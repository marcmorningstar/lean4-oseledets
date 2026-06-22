# Oseledets Frontier Campaign — Orchestration Plan (2026-06-22)

**Role:** CEO/orchestrator. I delegate + observe; agents write Lean in warm `lwt` worktrees.
**Goal:** resolve the 4 open GitHub issues (#8, #9, #10, #11) — the research-level BLOCKED leaves.

## The 4 walls (one+ sorry leaf each, in the unlinted `Frontier.Issue*` staging lib)

| Issue | Leaf(s) | Domain | A priori |
|---|---|---|---|
| #8 Yamamoto | `Frontier/Issue1/Yamamoto.lean:128` `yamamoto_singularValues_tendsto` | matrix analysis (cfc, polar, Jordan–Chevalley) | most tractable |
| #9 mfderiv | `Frontier/Issue2/DerivativeCocycleManifold.lean:325`, `Existence.lean:153` | manifold + measurable selection | hard |
| #10 Pesin | `Frontier/Issue4Pesin/ManeLowerBound.lean:124` `sumPosExp_le_ksEntropy_of_SRB` | smooth ergodic / Pesin | hardest ("multi-year") |
| #11 Arsenin–Kunugui | `Frontier/Issue6/ArseninKunugui.lean:240,271` (+ downstream `CastaingSelection.lean:479`, `MeasurableGraphToProjector.lean:405`) | descriptive set theory | hard |

## Infra (validated 2026-06-22)
- `gh` absent → use GitHub REST API with token from VS Code credential helper (cached `/tmp/.ghtok`). Repo: `marcmorningstar/lean4-oseledets`.
- leancheck plugin installed (`claude plugin install leancheck@lean-tools`); `lwt` works.
- Warm worktree smoke test: built `Frontier.Issue1.Yamamoto` (3037 jobs, 160s) with **NO Mathlib rebuild** — warm cache confirmed.
- Subagents may run `lwt` (only bare `git` is blocked by `block-subagent-git.sh`); leancheck PostToolUse hook auto-appends a build report after each subagent edit.
- 32 cores, ~25 GB free RAM → up to 15 lean agents authorized by user; stagger heavy cold builds (RAM-bound, ~0.5 GB/daemon + 2–4 GB/build).
- Resource monitor: `reports/infra/resmon.sh` (background) → `reports/infra/resources.log`.

## Invariants (from CLAUDE.md — never violate)
1. Warm checker mandatory for every Lean worker (own `lwt` worktree).
2. Workers NEVER run git; orchestrator does all merges/commits/pushes + authoritative cold builds.
3. Never `sorry`, never axiomatize in the imported (`Oseledets`) build. Partial work stays in `Frontier.Issue*` until sorry-free.
4. Headline theorems keep `#print axioms = [propext, Classical.choice, Quot.sound]`.
5. Migrate `Frontier.Issue*` → `Oseledets/` only when fully sorry-free.

## Phases
- **A — Recon** (workflow `oseledets-recon`, 4 agents): feasibility + literature + sub-lemma decomposition per issue. Reports → `docs/research/frontier/issue*/FEASIBILITY-*.md`.
- **B — Implementation** (super-workflow, up to 15 agents): per wall, multiple INDEPENDENT lean-worker attempts (distinct strategies from recon) in warm worktrees = tournament; keep the best branch per file. Pipeline: implement → mathematician QA verify.
- **C — Integration** (orchestrator): merge winning branches, authoritative cold `lake build` + axiom audit, migrate sorry-free chains to `Oseledets/`, commit+push at milestones.
- **D — Final QA** (workflow): adversarial audit (no hidden sorry/axiom, statements faithful), then update GitHub issues + write final report.

## Token policy
Burn tokens on parallel independent attempts at hard walls (diversity → success), NOT on brute-forcing a known multi-year wall (#10) — there the deliverable is the sharpest possible decomposition + roadmap. Multiple QA passes throughout. Commit+push at every milestone.

## Honest expectation
Some leaves may yield genuine closure (#8 best candidate); others realistically yield partial decomposition + literature-cited roadmap. Every leaf gets a real attempt. Report outcomes faithfully.
