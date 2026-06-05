# QA sign-off — M3 (pointwise Birkhoff ergodic theorem)

_Date: 2026-06-05. Independent checker (fresh context, did not write the code) +
orchestrator statement correction._

## Verdict: PASS — committable (zero blocking issues)

## Statement correction (recorded)

The Phase-0 skeleton stated `tendsto_birkhoffAverage_ae` with **no finiteness
hypothesis**, which is mathematically **false** in general: for an infinite measure where
the trim of `μ` to `invariants T` is not σ-finite, `μ[g | invariants T] = 0` (degenerate
`condExp`) while the Birkhoff averages need not converge to `0`. The implementing worker
correctly proved the substantive theorem under `[IsFiniteMeasure μ]` and flagged the bare
statement as unprovable; the orchestrator then **corrected** the public statement to
require `[IsFiniteMeasure μ]` (the true, standard pointwise Birkhoff theorem) and removed
the duplicate, so there is one source of truth and no `sorry`.

The independent checker confirmed this correction is **sound and non-weakening**: the MET
target assumes `[IsProbabilityMeasure μ]` (⊂ finite), so the corrected lemma applies
directly downstream (and is consumed that way by the ergodic corollary). No MET-relevant
content is lost.

## Hard-gate items (independently confirmed)

- `lake build` exit 0; only the 5 intended `sorry`s remain (MultiplicativeErgodic×1,
  Kingman×2, FurstenbergKesten×2) — none in Birkhoff or MaximalErgodic.
- `#print axioms` of both `tendsto_birkhoffAverage_ae` and
  `tendsto_birkhoffAverage_ae_integral` = `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`); no custom `axiom` declarations.
- No hidden `sorry` in Birkhoff.

## Faithfulness + soundness

- `tendsto_birkhoffAverage_ae [IsFiniteMeasure μ]`: conclusion byte-identical to the
  skeleton (full a.e. `Tendsto … (𝓝 (μ[g|invariants T]))`); only the finiteness
  hypothesis was added. Faithful individual ergodic theorem.
- `tendsto_birkhoffAverage_ae_integral`: statement unchanged; faithful ergodic Birkhoff
  (averages → `∫ g`); genuinely derived from the a.e. theorem via ergodic a.e.-constancy.
- ~20 private helpers sound & non-vacuous (the Borel–Cantelli tail estimate
  `ae_tendsto_orbit_div_atTop_zero`, the maximal-inequality core
  `measure_setOf_lt_limsup_eq_zero`, the limsup/liminf sandwich, `condExp_invariants_comp_self`).
  Mathlib-style; docstrings; targeted imports (no `import Mathlib`).
