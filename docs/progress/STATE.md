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

**M3 = pointwise Birkhoff ergodic theorem — COMPLETE.** `tendsto_birkhoffAverage_ae`
(now `[IsFiniteMeasure μ]`, see correction note) and the ergodic corollary
`tendsto_birkhoffAverage_ae_integral` proved sorry-free (~20 helper lemmas: a
Borel–Cantelli orbital tail estimate `n⁻¹·g(Tⁿx)→0`, the maximal-inequality core
`measure_setOf_lt_limsup_eq_zero`, the limsup/liminf sandwich around `μ[g|I]`, and the
ergodic a.e.-constant reduction to `∫ g`). Build green; axioms clean; open `sorry`s 7 → 5.

> **Statement correction (M3).** The Phase-0 skeleton stated `tendsto_birkhoffAverage_ae`
> with NO finiteness hypothesis — which is *false* in general (infinite measure, non-σ-finite
> trim ⇒ `μ[g|I]=0` but averages need not →0). Corrected to require `[IsFiniteMeasure μ]`,
> the true/standard statement. The MET target assumes `[IsProbabilityMeasure μ]` (⊂ finite),
> so the corrected lemma is fully usable downstream — no MET-relevant content lost.

Prior: P0 skeleton (QA-passed); P1 cocycle infra; P2 condExp∘MP (M2); P3 = M1 maximal
ergodic inequality (the keystone).

**M4 (Kingman) — ATTEMPTED, interrupted by a worker session limit; baseline reverted to
green.** A lean-worker built genuine Katznelson–Weiss scaffolding but did not finish; its
partial attempt is preserved at `docs/plan/wip/m4-kingman-attempt.md`. `Kingman.lean` was
reverted to the green skeleton (the two milestone `sorry` stubs). **Key insight for the
next attempt:** `IsSubadditiveCocycle` does not force `g 0 = 0`, but subadditivity at
`(0,0)` gives `g 0 ≥ 0` — so the "`gₙ ≤ birkhoffSum (g 1) n`" domination needs either a
`g 0 = 0` field added to the predicate (true for `log‖A⁽ⁿ⁾‖`) or to be stated for `n ≥ 1`.
Also add `[IsFiniteMeasure μ]` to `tendsto_kingman` (as for M3 Birkhoff; the worker did).

**Next: resume M4 (Kingman)** from `docs/plan/blueprints/m4-kingman.md` + the WIP, then M5
(Furstenberg–Kesten, blueprint `m5-furstenberg-kesten.md`), the Lyapunov layers
(`lyapunov-to-target.md`), and assembly into the target.

## What is done

- ✅ **Green build from source** (cache host DNS-blocked, as documented — never run
  `lake exe cache get`; just `lake build`, incremental). Full Mathlib closure for our
  imports is compiled and cached.
- ✅ Research dossier + Mathlib survey + self-approved target/route/plan (committed in
  `d3922ae` on branch `met-formalization`).
- ✅ **Phase 0 skeleton written and compiling green.** 7 modules under `Oseledets/`:
  - `Cocycle/Basic.lean` — `cocycle` def (newest factor left) + `cocycle_zero/_succ/_one`,
    **`cocycle_add` (identity) and `measurable_cocycle` PROVED (Phase 1)**,
    `IntegrableLogNorm` predicate; the project-wide `instMeasurableSpaceMatrix`
    (Pi/Borel measurable structure on matrices) and `instMeasurableMul₂Matrix`
    (matrix multiplication measurable — added in Phase 1), neither in Mathlib.
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

## Open `sorry`s (5 — all intended planned gaps; the implementation backlog)

_Closed so far: `cocycle_add`, `measurable_cocycle` (P1); `condExp_invariants_comp` (P2,
M2); `setIntegral_birkhoffSum_pos_nonneg` (P3, M1); `tendsto_birkhoffAverage_ae` +
`tendsto_birkhoffAverage_ae_integral` (M3). `Cocycle/Basic`, `Ergodic/MaximalErgodic`,
`Ergodic/Birkhoff` are all sorry-free._

| Decl | File | Milestone |
|---|---|---|
| `tendsto_kingman` | Ergodic/Kingman | M4 (now unlocked via Katznelson–Weiss from M1) |
| `tendsto_kingman_ergodic` | Ergodic/Kingman | M4 (ergodic) |
| `furstenbergKesten_top` | Cocycle/FurstenbergKesten | M5 |
| `furstenbergKesten_bot` | Cocycle/FurstenbergKesten | M5 |
| `oseledets_filtration` | MultiplicativeErgodic | M10 (TARGET) |

Not yet in the skeleton (deferred to their implementation phases): the Lyapunov layer
L4.x (growth function `λ̄`, ultrametric algebra, the limsup flag), L5.x (limsup→lim
induction), and measurability of the exponents/filtration (M7 proper). The target is
stated and `sorry`; these intermediate lemmas are added when their phase begins.

## What is next (in order)

1. ✅ Phase 0 (skeleton) committed `4ed4225`; blueprints `5b64baa`.
2. ✅ Phase 1 (cocycle infra) — `cocycle_add`, `measurable_cocycle` proved (`c23b73e`).
3. ✅ Phase 2 (M2) — `condExp_invariants_comp` proved (`4e5feec`).
4. ✅ Phase 3 (M1, keystone) — `setIntegral_birkhoffSum_pos_nonneg` proved (`bbf2ba2`).
5. ✅ M3 (pointwise Birkhoff) — `tendsto_birkhoffAverage_ae [IsFiniteMeasure]` + ergodic
   corollary proved (statement corrected; see note above).
6. ⏳ **M4 (Kingman)** — next; unlocked via Katznelson–Weiss (from M1, `m4-kingman.md`).
   Prove `tendsto_kingman` + `tendsto_kingman_ergodic`. Work the private lemmas under
   `[IsFiniteMeasure μ]`; fix the EReal/−∞ convention.
7. ⏳ Then M5 (Furstenberg–Kesten, `Cocycle/FurstenbergKesten.lean`), the Lyapunov layers
   (growth fn, ultrametric, flag, measurability, limsup→lim), and assembly into the target.

**Proof blueprints** for the three hard theorems (M1/M3/M4) are in
`docs/plan/blueprints/` — exact Mathlib lemma maps + auxiliary lemmas + pitfalls.

**Routing insight (from the blueprints) — M1 is the keystone.** The maximal ergodic
inequality (M1) unlocks BOTH:
- M3 (pointwise Birkhoff) = M1 + M2, and
- M4 (Kingman) via the **Katznelson–Weiss** route (M1 + truncation/stopping argument),
  which the `m4-kingman.md` blueprint recommends over Steele (Steele needs M3 first and
  a bespoke greedy-partition lemma with no Mathlib support).
So after M2, **prove M1 next** — it is the single highest-leverage unlock. Prove the
Kingman private lemmas under `[IsFiniteMeasure μ]` (the MET only uses probability
measures); fix the EReal/−∞ convention before M4 (`m4-kingman.md §1`).

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
