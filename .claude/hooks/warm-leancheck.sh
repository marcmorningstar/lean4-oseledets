#!/usr/bin/env bash
# SessionStart hook: start the leancheck daemon (ONE `lake serve` per project root) in the
# background so the first edit's warm check is ready. leancheck itself derives the per-root socket
# key (worktree-safe), is idempotent (reuses a live daemon), and guards against an accidental
# from-scratch Mathlib rebuild — so this hook is just a detached, non-blocking trigger.
PROJ="${CLAUDE_PROJECT_DIR:-$PWD}"
LOG="${LEANCHECK_HOOK_LOG:-/tmp/leancheck-hook.log}"
echo "$(date +%H:%M:%S) [sessionstart pid=$$] warming leancheck daemon for $PROJ" >> "$LOG" 2>/dev/null
LEANCHECK_ROOT="$PROJ" nohup python3 "$PROJ/.claude/leancheck/leancheck.py" --warm >> "$LOG" 2>&1 &
exit 0
