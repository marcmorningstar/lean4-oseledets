#!/usr/bin/env python3
"""leancheck — warm Lean diagnostics via the real language server (`lake serve`), with a cold
`lake build` gate. The agent never sees JSON or the LSP protocol: it edits a `.lean` file and
either gets diagnostics for free (PostToolUse hook) or runs `leancheck <file>`.

The engine is `leanclient` (the maintained client `lean-lsp-mcp` is built on), driving one
persistent `lake serve`. `lake serve` owns import resolution, incremental within-file elaboration,
the diagnostics-finalization handshake, stale-import auto-rebuild, and process lifecycle, so this
file is thin plumbing.

WORKTREE-SAFE: the daemon socket key is derived from the (realpath'd) project root, so each
worktree/checkout gets its OWN `lake serve` bound to its own root; workers within one tree share it.

MATHLIB GUARD: if Mathlib's oleans are absent (so a build/serve would recompile Mathlib from source
— HOURS), every entry point ABORTS with a loud warning instead of silently starting the rebuild,
unless `LEANCHECK_ALLOW_MATHLIB_REBUILD=1`.

Modes
-----
  leancheck <file.lean>        warm diagnostics (NON-BLOCKING; a cold file warms in the background)
  leancheck --cold <file|mod>  authoritative `lake build` of the module (the QA gate)
  leancheck --warm [file]      start the daemon (with a file, also start warming it)
  leancheck --stop             stop the daemon (kills `lake serve` + its `lean --server` child)
  leancheck --check-mathlib    report whether Mathlib is built (exit 1 + warning if not)
  leancheck --daemon           (internal) the long-lived server host
  leancheck --selftest         offline unit tests of the pure logic

Config (env): LEANCHECK_ROOT [cwd], LEANCHECK_KEY [derived from root], LEANCHECK_MAXFILES [8],
              LEANCHECK_HOOK_LOG [/tmp/leancheck-hook.log], LEANCHECK_ALLOW_MATHLIB_REBUILD [unset].

Cross-file note: `lake serve` resolves imports from `.olean`, so a file's check reflects its OWN
current source but sees dependencies as last built — a changed dependency must be rebuilt to be
visible. The cold `lake build` + guarded AxiomAudit remain the source of truth.
"""
import sys, os, json, socket, subprocess, time, argparse, re, threading, hashlib

ROOT = os.path.realpath(os.environ.get("LEANCHECK_ROOT", os.getcwd()))
KEY = os.environ.get("LEANCHECK_KEY") or ("oseledets-" + hashlib.sha1(ROOT.encode()).hexdigest()[:8])
SOCK = os.path.join(os.environ.get("LEANCHECK_SOCKDIR", "/tmp"), f"leancheck-{KEY}.sock")
MAXFILES = int(os.environ.get("LEANCHECK_MAXFILES", "8"))
ALLOW_REBUILD = os.environ.get("LEANCHECK_ALLOW_MATHLIB_REBUILD") == "1"

# ---------------------------------------------------------------- Mathlib-rebuild guard

def mathlib_built(root):
    """True iff Mathlib's oleans are present, i.e. a `lake build`/`lake serve` will NOT recompile
    Mathlib from source (a multi-hour operation). Detects the missing-cache case: a fresh checkout,
    or a worktree without the prebuilt `.lake` cache (or its symlink)."""
    base = os.path.join(root, ".lake", "packages", "mathlib", ".lake", "build", "lib")
    for cand in ("lean/Mathlib/Init.olean", "Mathlib/Init.olean"):   # pinned-toolchain layout first
        if os.path.exists(os.path.join(base, cand)):
            return True
    if os.path.isdir(base):                                          # fallback: any Mathlib olean
        for _dp, _dn, fs in os.walk(base):
            if any(f.endswith(".olean") for f in fs):
                return True
    return False

MATHLIB_WARNING = (
    "================ ⚠️  SERIOUS WARNING: MATHLIB IS NOT BUILT ================\n"
    "Mathlib's compiled oleans are missing under .lake/packages/mathlib, so a `lake build` or\n"
    "`lake serve` here would COMPILE MATHLIB FROM SOURCE — HOURS of CPU, not a quick check.\n"
    "  * On a brand-new checkout this is expected: fetch the prebuilt cache first.\n"
    "  * In a WORKTREE it usually means the prebuilt `.lake` cache (or its symlink) is missing.\n"
    "leancheck ABORTED rather than silently start a multi-hour rebuild. Decide explicitly:\n"
    "  - cancel, fix the cache/symlink, and retry; OR\n"
    "  - accept the from-scratch rebuild by re-running with  LEANCHECK_ALLOW_MATHLIB_REBUILD=1\n"
    "==================================================================================")

def mathlib_guard():
    """Warning text if a from-scratch Mathlib rebuild is imminent and not opted into, else None."""
    if ALLOW_REBUILD or mathlib_built(ROOT):
        return None
    return MATHLIB_WARNING

# ---------------------------------------------------------------- pure logic (unit-tested)

SEVERITY = {1: "error", 2: "warning", 3: "info", 4: "hint"}

def format_diagnostics(relpath, diagnostics):
    """LSP diagnostics (list of {range,severity,message}) -> (compiler-style text, n_errors).
    LSP positions are 0-based; we emit 1-based line:col. Messages are first-line-only."""
    out, n_err = [], 0
    for d in diagnostics or []:
        start = (d.get("range") or {}).get("start") or {}
        line = start.get("line", 0) + 1
        col = start.get("character", 0) + 1
        sev = SEVERITY.get(d.get("severity", 1), "info")
        msg = (d.get("message", "") or "").strip().split("\n", 1)[0]
        if sev == "error":
            n_err += 1
        out.append(f"{relpath}:{line}:{col}: {sev}: {msg}")
    if not out:
        out.append("✓ no errors")
    return "\n".join(out), n_err

# ---------------------------------------------------------------- the language-server daemon

class Engine:
    """Owns one persistent `lake serve` (via leanclient) and warms cold files in the background so a
    check never blocks: the first open elaborates a file; until then a check returns "warming";
    afterwards re-checks are fast."""
    def __init__(self):
        from leanclient import LeanLSPClient            # imported lazily: only the daemon needs it
        self.client = LeanLSPClient(ROOT, initial_build=False, prevent_cache_get=True,
                                    max_opened_files=MAXFILES)
        self.clock = threading.Lock()                   # serialize all server access (one lake serve)
        self.slock = threading.Lock()                   # guards the state sets below
        self.ready = set()
        self.warming = set()

    def _warm(self, rel):
        try:
            with self.clock:
                self.client.get_diagnostics(rel)
        except Exception:
            pass
        with self.slock:
            self.warming.discard(rel); self.ready.add(rel)

    def check(self, rel):
        with self.slock:
            if rel not in self.ready:
                if rel in self.warming:
                    return f"leancheck: still warming {os.path.basename(rel)}; diagnostics shortly."
                self.warming.add(rel)
                threading.Thread(target=self._warm, args=(rel,), daemon=True).start()
                return (f"leancheck: warming {os.path.basename(rel)} in the Lean server (first open "
                        f"of a file takes a moment); diagnostics appear on your next edit. The cold "
                        f"`lake build` Stop gate remains authoritative.")
        with self.clock:
            res = self.client.get_diagnostics(rel)
        text, _ = format_diagnostics(rel, getattr(res, "diagnostics", []))
        return text

    def close(self):
        try:
            self.client.close()
        except Exception:
            pass

def daemon():
    import atexit, signal
    eng = Engine()
    atexit.register(eng.close)
    for s in (signal.SIGTERM, signal.SIGINT):
        signal.signal(s, lambda *_: (eng.close(), os._exit(0)))
    if os.path.exists(SOCK):
        os.remove(SOCK)
    srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM); srv.bind(SOCK); srv.listen(8)
    atexit.register(lambda: os.path.exists(SOCK) and os.remove(SOCK))
    while True:
        conn, _ = srv.accept()
        try:
            req = json.loads(_recv_all(conn) or "{}")
            if req.get("file") == "__stop__":
                conn.sendall(b"stopping"); conn.close()
                eng.close()
                if os.path.exists(SOCK):
                    os.remove(SOCK)
                os._exit(0)
            rel = os.path.relpath(os.path.abspath(req["file"]), ROOT)
            conn.sendall(eng.check(rel).encode())
        except Exception as e:
            conn.sendall(f"leancheck daemon error: {e}".encode())
        finally:
            conn.close()

# ---------------------------------------------------------------- client / CLI

def _recv_all(conn):
    chunks = []
    while True:
        b = conn.recv(65536)
        if not b:
            break
        chunks.append(b)
    return b"".join(chunks).decode()

def ensure_daemon():
    if os.path.exists(SOCK):
        return
    g = mathlib_guard()
    if g:
        raise SystemExit(g)                  # backstop: never start lake serve on an unbuilt tree
    subprocess.Popen([sys.executable, os.path.abspath(__file__), "--daemon"],
                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                     start_new_session=True, cwd=ROOT)
    for _ in range(600):
        if os.path.exists(SOCK):
            time.sleep(0.2); return
        time.sleep(0.1)
    raise SystemExit("leancheck: daemon did not come up")

def warm_check(path):
    g = mathlib_guard()
    if g:
        print(g); return 1
    ensure_daemon()
    c = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM); c.connect(SOCK)
    c.sendall(json.dumps({"file": os.path.abspath(path)}).encode()); c.shutdown(socket.SHUT_WR)
    out = _recv_all(c); c.close()
    print(out)
    return 1 if re.search(r": error:", out) else 0

def module_of(target):
    if not target.endswith(".lean"):
        return target
    return os.path.relpath(os.path.abspath(target), ROOT)[:-5].replace("/", ".")

def cold_check(target):
    g = mathlib_guard()
    if g:
        print(g); return 1
    r = subprocess.run(["lake", "build", module_of(target)], cwd=ROOT, capture_output=True, text=True)
    diags = [l for l in (r.stdout + r.stderr).split("\n") if re.search(r"error:|warning:", l)]
    print("\n".join(diags) if diags else "✓ cold build clean")
    return r.returncode

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("target", nargs="?")
    ap.add_argument("--cold", action="store_true")
    ap.add_argument("--warm", action="store_true")
    ap.add_argument("--stop", action="store_true")
    ap.add_argument("--daemon", action="store_true")
    ap.add_argument("--check-mathlib", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    if a.check_mathlib:
        if mathlib_built(ROOT):
            print("✓ Mathlib oleans present (a build/serve will NOT recompile Mathlib)"); return 0
        print(MATHLIB_WARNING); return 1
    if a.daemon:
        return daemon()
    if a.stop:
        if os.path.exists(SOCK):
            try:
                c = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM); c.connect(SOCK)
                c.sendall(b'{"file":"__stop__"}'); c.close()
            except Exception:
                pass
            if os.path.exists(SOCK):
                os.remove(SOCK)
        return 0
    if a.warm:
        g = mathlib_guard()
        if g:
            print(g); return 1
        ensure_daemon()
        if a.target:
            return warm_check(a.target)
        print("warm"); return 0
    if not a.target:
        ap.error("need a file/module (or a mode flag)")
    return cold_check(a.target) if a.cold else warm_check(a.target)

# ---------------------------------------------------------------- offline self-test

def selftest():
    import tempfile
    diags = [
        {"range": {"start": {"line": 158, "character": 0}}, "severity": 1,
         "message": "Not a definitional equality\n  detail"},
        {"range": {"start": {"line": 3, "character": 7}}, "severity": 2,
         "message": "declaration uses 'sorry'"},
    ]
    text, nerr = format_diagnostics("Oseledets/Continuous/Flow.lean", diags)
    assert nerr == 1, nerr
    assert "Flow.lean:159:1: error: Not a definitional equality" in text, text
    assert "detail" not in text, "first-line-only"
    assert "Flow.lean:4:8: warning: declaration uses 'sorry'" in text, text
    clean, n0 = format_diagnostics("T.lean", [])
    assert n0 == 0 and clean == "✓ no errors", clean
    # Mathlib guard: an empty dir reads as not-built (would rebuild) -> warning fires
    d = tempfile.mkdtemp()
    assert mathlib_built(d) is False, "empty tree must read as not-built"
    # Per-root key derivation is deterministic and path-sensitive (worktree-safe)
    k = lambda p: "oseledets-" + hashlib.sha1(p.encode()).hexdigest()[:8]
    assert k("/repo/a") != k("/repo/b"), "different roots must yield different daemon keys"
    assert k("/repo/a") == k("/repo/a"), "same root must yield the same key"
    print("leancheck selftest OK")
    return 0

if __name__ == "__main__":
    sys.exit(main() or 0)
