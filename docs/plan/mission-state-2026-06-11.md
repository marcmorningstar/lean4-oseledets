# Autonomous mission state — paused on monthly spend limit (2026-06-11 ~16:30 UTC)

Mission (user mandate): (A) fix all findings of `docs/plan/style-review-2026-06-11.md`,
(B) add companion corollaries per `docs/plan/blueprints/companion-corollaries.md`,
(C) two-sided splitting theorem per `docs/plan/blueprints/two-sided-met.md` (phases P0–P8),
(D) final full QA (general + Mathlib-candidate). All subagents on model `fable`
(override agent-definition models). Commit per stage, Mathlib-style + Co-Authored-By
Claude Fable 5. Watchdog: hourly ScheduleWakeup while stages remain.

## Paused because

Workers began failing with "You've hit your monthly spend limit" (claude.ai/settings/usage).
User notified by push. Resume when the user raises the limit and says continue.

## State at pause

- **Stage A phase 1 (per-file mechanical fixes)**: workflow run `wf_f97bd688-d8b`
  (script under the session workflows dir) — 21/49 files `fixed-verified`
  (list in the workflow result; e.g. Cocycle/*, Ergodic/*, ExteriorNorm, Forward*,
  AssemblyChain, AssemblyTopGap, CapstoneTelescope, Fischer, Filtration,
  FiltrationAssemblyBridge). ~18 more files were edited but their workers died
  UNVERIFIED; ~10 untouched. 39 modified library files total in the working tree.
  A full `lake build` was started as the arbiter; commit verified-green work, fix or
  re-verify the rest at relaunch (resume the workflow with `resumeFromRunId`; verified
  agents return cached, failed ones re-run).
- **31 `#print axioms` declaration names** collected so far (see workflow result JSON,
  `axiomAuditDecls`) — destined for a central `#guard_msgs`-style axiom test file in
  Stage A phase 2; ~85 more remain in not-yet-processed files.
- **Stage B (corollaries)**: `Oseledets/Lyapunov/Corollaries.lean` written (~33 KB)
  + root import added; final typecheck pending (the running `lake build` covers it,
  since the root imports it). Worker's #print-axioms probe not yet run.
- **Stage C (two-sided)**: blueprint complete (`two-sided-met.md`, P0–P8, ~2.8k lines
  plan); implementation NOT started. Starts after Stage A phase 2 (which splits
  `Kingman.lean`, a P3 dependency).
- **Stage A phase 2 (NOT started)**: renames (22 hypothesis-slot names — list in the
  style review §naming), namespace consolidation (ExteriorNorm/Frames/Fischer/Weyl/
  ChainCore/Ruelle13 → Oseledets.* or proper Mathlib homes), fossil-route deletion
  (~2,400 lines, list in §architecture), splits of OseledetsLimit/Kingman/ExteriorNorm
  (>1500-line cap), maxHeartbeats policy, central axiom test + CI wiring, doc updates
  (CLAUDE.md/STATE.md still say the axiom audit "prints during the build").

## Resume protocol

1. `git status` + full `lake build` → commit green work if not yet committed
   (style cleanup and Corollaries as separate commits).
2. Resume `wf_f97bd688-d8b` (TaskStop any stale run first) to finish phase-1 files;
   instruct re-verification of the unverified-edited files.
3. Stage B verification: `lake env lean` on Corollaries.lean + axiom probe; commit.
4. Stage A phase 2 (serial orchestration), commit; then Stage C P0–P8; then Stage D.
