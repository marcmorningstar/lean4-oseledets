#!/usr/bin/env python3
"""PostToolUse hook: after an Edit/Write/MultiEdit of a Lean file under `Oseledets/`, run the warm
`leancheck` and return its compiler-style diagnostics to the agent as `additionalContext`. leancheck
is itself non-blocking (a cold file warms in the background and reports "warming") and owns the
per-project-root daemon key and the Mathlib-not-built guard — so this hook is just: filter, record
the touched module for the Stop cold-gate, run leancheck, surface its output. Logs to a /tmp debug
log for observability. `--selftest` runs offline unit tests."""
import sys, os, json, subprocess, time

DEBUG = os.environ.get("LEANCHECK_HOOK_LOG", "/tmp/leancheck-hook.log")

def is_target(tool, path):
    """True iff this is an edit of a Lean source file under an `Oseledets/` directory."""
    return (tool in ("Edit", "Write", "MultiEdit")
            and isinstance(path, str) and path.endswith(".lean")
            and os.sep + "Oseledets" + os.sep in path)

def hook_output(ctx):
    return {"hookSpecificOutput": {"hookEventName": "PostToolUse", "additionalContext": ctx}}

def dbg(msg):
    try:
        with open(DEBUG, "a", encoding="utf-8") as f:
            f.write(f"{time.strftime('%H:%M:%S')} [post-edit pid={os.getpid()}] {msg}\n")
    except Exception:
        pass

def main():
    try:
        d = json.load(sys.stdin)
    except Exception:
        return 0
    tool = d.get("tool_name")
    ti = d.get("tool_input") or {}
    path = ti.get("file_path") or ti.get("path") or ""
    if not is_target(tool, path):
        return 0
    proj = os.environ.get("CLAUDE_PROJECT_DIR", os.getcwd())
    leancheck = os.path.join(proj, ".claude", "leancheck", "leancheck.py")
    session = d.get("session_id", "default")
    env = dict(os.environ, LEANCHECK_ROOT=proj)        # leancheck derives the per-root key from this
    rel = os.path.relpath(os.path.abspath(path), proj)
    # record the touched module for the Stop cold-gate
    try:
        mod = rel[:-5].replace(os.sep, ".")
        touch = f"/tmp/leancheck-touched-{session}.txt"
        seen = set(open(touch).read().split()) if os.path.exists(touch) else set()
        seen.add(mod); open(touch, "w").write("\n".join(sorted(seen)))
    except Exception as e:
        dbg(f"touch-list error: {e}")
    t0 = time.time()
    try:
        r = subprocess.run([sys.executable, leancheck, path], env=env,
                           capture_output=True, text=True, timeout=80)
        report = (r.stdout or "").strip()
        dbg(f"{rel}: leancheck exit={r.returncode} bytes={len(report)} in {time.time()-t0:.2f}s")
    except Exception as e:
        dbg(f"{rel}: leancheck error: {e}")
        report = f"leancheck unavailable ({e}); rely on the cold build."
    if not report:
        return 0
    print(json.dumps(hook_output("leancheck — " + os.path.basename(path) + ":\n" + report)))
    return 0

def selftest():
    assert is_target("Edit", "/r/Oseledets/A.lean")
    assert is_target("Write", "/r/Oseledets/Continuous/A.lean")
    assert not is_target("Edit", "/r/Other/A.lean")
    assert not is_target("Edit", "/r/Oseledets/A.txt")
    assert not is_target("Read", "/r/Oseledets/A.lean")
    env = hook_output("hi")
    assert env["hookSpecificOutput"]["hookEventName"] == "PostToolUse"
    assert env["hookSpecificOutput"]["additionalContext"] == "hi"
    json.loads(json.dumps(env))
    print("post-edit-leancheck selftest OK")
    return 0

if __name__ == "__main__":
    if "--selftest" in sys.argv:
        sys.exit(selftest())
    sys.exit(main() or 0)
