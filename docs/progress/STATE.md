# Oseledets MET formalization — living state

> Single source of truth for resuming this project. Fresh agent: read this file top
> to bottom, then `docs/research/understanding.md` (the math + the L0–L7 lemma
> ladder), `docs/research/target-and-milestones.md` (target + milestones M0–M13),
> and `docs/plan/` (decision record + phased plan). Charter: `PROMPT.md`.

_Last updated: 2026-06-04 (autonomous run; user away → self-approving checkpoints,
recorded in `docs/plan/decision-record.md`)._

## Target (one line)

`sorry`-free Lean 4 + Mathlib formalization of the **one-sided Oseledets MET in
filtration form** (milestone **M10** / layer **L6.1**): for an ergodic m.p.
`T : X → X` on a probability space and measurable `A : X → GL(d,ℝ)` with
`log⁺‖A‖, log⁺‖A⁻¹‖ ∈ L¹`, there exist `λ₁ > ⋯ > λ_k` and an a.e. `A`-equivariant
measurable flag with `lim (1/n) log‖A⁽ⁿ⁾(x)v‖ = λᵢ` on each stratum. Signature sketch:
`docs/research/target-and-milestones.md §a`.

## Current phase

**Research + plan COMPLETE. Next: green build → Phase 0 (skeleton).**

## What is done

- ✅ Environment: toolchain `v4.30.0-rc2`, Mathlib pinned `34f7a6cd…`. Confirmed the
  cache gotcha (`mathlib4.blob.core.windows.net` DNS-blocked → `cache get` stalls,
  0 oleans; GitHub reachable). Building Mathlib **from source**.
- 🔄 **Build from source still running** (background; `tail -f build.log`). At last
  check `[~1800/2463]` modules. NOT yet green. Resume rule: just re-run `lake build`
  (incremental), never `cache get`.
- ✅ **Research phase** (dynamic workflow, 10 agents): sources scraped to
  `docs/research/sources/` (HTML sources OK; PDF scrapes failed — firecrawl can't
  extract PDFs — see `sources/SCRAPE-LOG.md`; math is captured in the digests),
  digests in `docs/research/digests/`, Mathlib API survey in
  `docs/research/mathlib-survey/`, synthesis in `docs/research/understanding.md` +
  `docs/research/target-and-milestones.md`.
- ✅ **Target + route decided and self-approved** (`docs/plan/decision-record.md`):
  target M10; **Route B** (maximal ergodic ineq → pointwise Birkhoff → Kingman →
  Furstenberg–Kesten → induction). Conventions pinned (cocycle order, scoped L2 op
  norm, `det ≠ 0` for GL, `log⁺`, Kingman in `EReal`).
- ✅ **Implementation plan** (`docs/plan/implementation-plan.md`): module layout under
  `Oseledets/{Ergodic,Cocycle,Lyapunov}/…`, 12 phases (P0 skeleton → P11 assemble
  target), the hard-gate definition (green build + fewer sorrys + no new axioms +
  independent checker sign-off + one commit per phase).
- ✅ Substrate spot-verified on disk: `Real.posLog`, `Matrix.l2_opNorm_mul` & scope
  `Matrix.Norms.L2Operator`, `Ergodic.ae_eq_const_of_ae_eq_comp_ae`,
  `MeasurableSpace.invariants` (the invariant σ-algebra), `birkhoffAverage`,
  `condExp`/`setIntegral_condExp`, `LinearMap.singularValues`, `Flag`,
  `Subadditive.tendsto_lim`. Pointwise Birkhoff confirmed ABSENT (only L² mean
  ergodic theorem exists).

## Key facts driving the plan

- **The whole dependency tower is absent from Mathlib**: maximal ergodic inequality,
  pointwise Birkhoff, Kingman, Furstenberg–Kesten, cocycles, Lyapunov exponents,
  Oseledets filtration, measurable structure on subspaces/flags. This is a large,
  multi-session formalization. Pointwise Birkhoff (L1) and Kingman (L2) are the two
  big novel sub-projects; each is an independently valuable Mathlib contribution.
- Progress is **monotone and committed per phase**; honest `sorry`/axiom status is
  always tracked here.

## What is next (in order)

1. ⏳ Finish green build.
2. ⏳ **Phase 0 — skeleton**: write target + all milestone statements as `sorry`
   theorems in the planned layout, conventions pinned, target proof citing
   milestones; `lake build` green; checker sign-off; commit.
3. ⏳ Phase 1 (cocycle infra), Phase 2 (condExp∘MP), Phase 3 (ultrametric LA) — all
   self-contained, closeable. Then push Phase 4 (maximal ergodic ineq) and Phase 5
   (pointwise Birkhoff). Phases 6–11 advance as far as possible; statements locked.

## Open `sorry`s

None yet (skeleton not written).

## Decisions / rationale log

- Self-approving the two human checkpoints (target, plan) — user away, authorized.
  Full rationale: `docs/plan/decision-record.md`.
- Building Mathlib from source (cache blocked).
- Target = one-sided filtration MET (M10), Route B. Conventions pinned (see above).

## Resumption notes

- Background build task id (this run): `bktw3v502`; log `build.log`.
- Research workflow run id (this run): `wf_53384be8-54f` (completed).
- Git on `main`. Baseline `2bead01`. Commit per QA-passed phase.
