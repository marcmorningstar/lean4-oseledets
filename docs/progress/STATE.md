# Oseledets MET formalization — living state

> Single source of truth for resuming this project. Fresh agent: read this file top
> to bottom, then `docs/research/understanding.md` (the math + the L0–L7 lemma
> ladder), `docs/research/target-and-milestones.md` (target + milestones M0–M13),
> and `docs/plan/` (decision record + phased plan + api-notes). Charter: `PROMPT.md`.

_Last updated: 2026-06-05 (autonomous run; user away → self-approving checkpoints,
recorded in `docs/plan/decision-record.md`)._

## Target (one line)

`sorry`-free Lean 4 + Mathlib formalization of the **one-sided Oseledets MET in
filtration form** (milestone **M10** / layer **L6.1**), stated in Lean as
`Oseledets.oseledets_filtration` in `Oseledets/MultiplicativeErgodic.lean`.

## Current phase

**Phase 0 (skeleton) — COMPLETE (QA-passed).** Build green from source; the target
theorem + the major milestone theorems are stated and typecheck, all proofs are intended
`sorry`. Independent 3-agent checker review: **PASS** on all dimensions, zero blocking
issues (see `docs/progress/qa/phase0-skeleton.md`). **Next: Phase 1 (cocycle infra).**

## What is done

- ✅ **Green build from source** (cache host DNS-blocked, as documented — never run
  `lake exe cache get`; just `lake build`, incremental). Full Mathlib closure for our
  imports is compiled and cached.
- ✅ Research dossier + Mathlib survey + self-approved target/route/plan (committed in
  `d3922ae` on branch `met-formalization`).
- ✅ **Phase 0 skeleton written and compiling green.** 7 modules under `Oseledets/`:
  - `Cocycle/Basic.lean` — `cocycle` def (newest factor left) + `cocycle_zero/_succ/_one`
    (proved), `cocycle_add` (identity, `sorry`), `IntegrableLogNorm` predicate,
    `measurable_cocycle` (`sorry`); also the project-wide `instMeasurableSpaceMatrix`
    (Pi/Borel measurable structure on matrices — not in Mathlib).
  - `Cocycle/FurstenbergKesten.lean` — `furstenbergKesten_top`, `_bot` (`sorry`, M5).
  - `Ergodic/MaximalErgodic.lean` — `setIntegral_birkhoffSum_pos_nonneg` (`sorry`, M1).
  - `Ergodic/Birkhoff.lean` — `condExp_invariants_comp` (M2), `tendsto_birkhoffAverage_ae`
    (M3), `tendsto_birkhoffAverage_ae_integral` (ergodic) — all `sorry`.
  - `Ergodic/Kingman.lean` — `IsSubadditiveCocycle` predicate, `tendsto_kingman`,
    `tendsto_kingman_ergodic` (`sorry`, M4).
  - `Lyapunov/MeasurableSubspace.lean` — `orthProjMatrix`, `MeasurableSubspace` (M7 infra).
  - `MultiplicativeErgodic.lean` — `oseledets_filtration` (the TARGET, `sorry`, M10).
- ✅ Gate checks: `lake build` exit 0 (only `sorry` warnings); **no custom `axiom`
  declarations**; `#print axioms oseledets_filtration` = `[propext, sorryAx,
  Classical.choice, Quot.sound]` (only standard axioms + the intended `sorryAx` gaps).

## Open `sorry`s (11 — all intended skeleton gaps; the implementation backlog)

| Decl | File | Milestone |
|---|---|---|
| `cocycle_add` | Cocycle/Basic | M5-infra (cocycle identity) |
| `measurable_cocycle` | Cocycle/Basic | M5-infra |
| `setIntegral_birkhoffSum_pos_nonneg` | Ergodic/MaximalErgodic | M1 |
| `condExp_invariants_comp` | Ergodic/Birkhoff | M2 |
| `tendsto_birkhoffAverage_ae` | Ergodic/Birkhoff | M3 |
| `tendsto_birkhoffAverage_ae_integral` | Ergodic/Birkhoff | M3 (ergodic) |
| `tendsto_kingman` | Ergodic/Kingman | M4 |
| `tendsto_kingman_ergodic` | Ergodic/Kingman | M4 (ergodic) |
| `furstenbergKesten_top` | Cocycle/FurstenbergKesten | M5 |
| `furstenbergKesten_bot` | Cocycle/FurstenbergKesten | M5 |
| `oseledets_filtration` | MultiplicativeErgodic | M10 (TARGET) |

Not yet in the skeleton (deferred to their implementation phases): the Lyapunov layer
L4.x (growth function `λ̄`, ultrametric algebra, the limsup flag), L5.x (limsup→lim
induction), and measurability of the exponents/filtration (M7 proper). The target is
stated and `sorry`; these intermediate lemmas are added when their phase begins.

## What is next (in order)

1. ✅ Phase-0 QA passed → commit the skeleton (this commit).
2. ⏳ Phase 1 — cocycle infra: prove `cocycle_add`, `measurable_cocycle` + supporting
   posLog/integrability lemmas (self-contained; closeable).
3. ⏳ Phase 2 — `condExp_invariants_comp` (M2, self-contained).
4. ⏳ Phase 3 — ultrametric linear algebra (L4.3, pure LA; add module).
5. ⏳ Phase 4 — maximal ergodic inequality (M1); Phase 5 — pointwise Birkhoff (M3).
   Then Kingman (M4), Furstenberg–Kesten (M5), the Lyapunov layers, and assembly.

## Conventions (pinned — see decision-record.md / api-notes.md)

Cocycle newest-factor-left; scoped L2 operator norm `Matrix.Norms.L2Operator`; vectors
`EuclideanSpace ℝ (Fin d)` acted on via `Matrix.toEuclideanCLM`; GL encoded as
`det ≠ 0`; `log⁺ = Real.posLog`; Kingman to be generalized to `EReal` later;
subspace measurability via `orthProjMatrix`/`MeasurableSubspace`.

## Resumption notes

- Branch `met-formalization`; baseline `2bead01`; research/plan commit `d3922ae`.
- Build is incremental: `lake build`. Never `lake exe cache get` (DNS-blocked, stalls).
- Per-file builds are slow (~150s, heavy import-closure load); a single whole-library
  `lake build` shares the environment and is the efficient inner loop.
- One commit per QA-passed phase, Mathlib-style message + `Co-Authored-By` line.
