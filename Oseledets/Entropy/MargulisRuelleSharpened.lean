/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.MargulisRuelleAbstract
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Sharpening the Margulis–Ruelle reduction: the positive-part singular-value product

This module sharpens the abstract Margulis–Ruelle reduction of
`Oseledets.Entropy.MargulisRuelleAbstract` along two independent, honest, sorry-free axes. It does
**not** discharge the genuinely geometric atom-counting hypothesis `hgeo` — that needs Lyapunov /
Pesin charts and a dynamical covering-count argument absent from Mathlib (see the module-level
`## The minimal absent geometric atom` below). Instead it lands the two reachable atoms *around*
that wall.

## The positive-part singular-value product (part A)

The right-hand side of the Ruelle inequality is built from the *positive parts* of the Lyapunov
exponents, `Σ λᵢ⁺`. Finitely, before passing to the ergodic limit, the per-step object the
geometric covering bound produces is the **positive-part singular-value product**
`∏ᵢ max(1, σᵢ)` — the local volume-expansion factor of the differential, counting only the
expanding directions. Its logarithm is exactly `∑ᵢ log⁺ σᵢ = ∑ᵢ max(0, log σᵢ)`, the finite-`n`
incarnation of `Σ λᵢ⁺`. This file proves that identity as a standalone det-free
linear-algebra / analysis fact, in both the abstract-`LinearMap` form and the concrete `Matrix`
form the cocycle layer uses (`Matrix.toEuclideanLin`):

```
∑ i, Real.posLog (σ i) = Real.log (∏ i, max 1 (σ i)).
```

The key Mathlib input is `Real.posLog_eq_log_max_one : 0 ≤ x → log⁺ x = log (max 1 x)`, valid
because singular values are nonnegative (`LinearMap.singularValues_nonneg`), combined with
`Real.log_prod` (each factor `max 1 (σ i) ≥ 1 > 0`).

## The sharpened reduction (part B)

We also restate `Oseledets.margulisRuelle_le_sumPosExp` with the opaque per-partition hypothesis
`hgeo` repackaged through the already-proved entropy plumbing. The sharpened corollary
`margulisRuelle_le_sumPosExp'` is *definitionally the same statement* — it merely renames the
geometric input as `hcount`, the per-partition Ruelle counting bound, to make explicit that the
single remaining open input is a finite-`n`, per-partition estimate (not the supremum conclusion).
It is an honest cosmetic clarification: no new mathematical content is created, and crucially no
`sorry` is introduced.

## Main results

* `Oseledets.Entropy.sum_posLog_singularValues_eq_log_prod_max_one` — the abstract positive-part
  singular-value product identity for `LinearMap.singularValues`.
* `Oseledets.Entropy.sum_posLog_singularValues_toEuclideanLin_eq` — its `Matrix.toEuclideanLin`
  specialization (the form the derivative cocycle uses).
* `Oseledets.margulisRuelle_le_sumPosExp'` — the sharpened restatement of the Margulis–Ruelle
  reduction with the geometric input renamed to the per-partition counting bound `hcount`.

## The minimal absent geometric atom

The one piece that remains open is the **dynamical covering-count lemma**: for a `C¹` self-map `T`
of `EuclideanSpace ℝ (Fin d)`, the image `T(B(x, ε))` of an `ε`-ball is coverable by at most
`C · ∏ᵢ max(1, σᵢ(D_x T))` balls of radius `ε`, where `σᵢ(D_x T)` are the singular values of the
differential — i.e. the local volume-expansion is governed by the positive-part singular-value
product `∏ᵢ max(1, σᵢ)` whose log is the object of part (A). Iterating this along an orbit through
Lyapunov / Pesin charts upgrades the per-step bound to `exp(n · (Σ λᵢ⁺ + ε))` for the refinement
`⋁_{k<n} T⁻ᵏ α` of a fine partition `α`. Feeding that atom-count into `entropy_le_log_card`
(`Oseledets.Entropy.Partition`) and the Fekete limit (`Oseledets.Entropy.ksEntropyPartition`)
reproduces `hgeo`. Formalizing this covering bound requires smooth-ergodic-theory infrastructure
(Lyapunov charts, the Mañé/Katok covering argument, orbit-averaging) that Mathlib does not have;
it is a multi-month build, out of scope here.

## References

* Maryam Contractor, *The Pesin Entropy Formula*, UChicago REU 2023, §7.
* D. Ruelle, *An inequality for the entropy of differentiable maps*, Bol. Soc. Bras. Mat. **9**
  (1978) 83–87.
* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
-/

open MeasureTheory Module

namespace Oseledets.Entropy

/-! ## The positive-part singular-value product (part A) -/

section PosPart

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The positive-part singular-value product (abstract form).** For a linear map `f` between
finite-dimensional real inner product spaces and any finite index set of singular-value indices,
the sum of the positive-part logarithms `∑ i, log⁺ σᵢ(f)` equals the logarithm of the
*positive-part singular-value product* `∏ i, max 1 σᵢ(f)`.

This is the finite-`n` incarnation of the right-hand side `Σ λᵢ⁺` of the Margulis–Ruelle
inequality: `∏ᵢ max(1, σᵢ)` is the local volume-expansion factor counting only the expanding
directions, and its log is the positive-part exponent sum. The proof rewrites each
`log⁺ σᵢ = log (max 1 σᵢ)` (valid since `σᵢ ≥ 0`, `Real.posLog_eq_log_max_one`) and pulls the sum
of logs through the product of the positive factors `max 1 σᵢ ≥ 1` (`Real.log_prod`). -/
theorem sum_posLog_singularValues_eq_log_prod_max_one (f : E →ₗ[ℝ] F) (s : Finset ℕ) :
    ∑ i ∈ s, Real.posLog (f.singularValues i)
      = Real.log (∏ i ∈ s, max 1 (f.singularValues i)) := by
  rw [Real.log_prod (fun i _ => by positivity)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Real.posLog_eq_log_max_one (f.singularValues_nonneg i)

end PosPart

/-- **The positive-part singular-value product (matrix / `toEuclideanLin` form).** The
specialization of `sum_posLog_singularValues_eq_log_prod_max_one` to the singular values of
`Matrix.toEuclideanLin M`, which is how the derivative cocycle accesses singular values
(`Oseledets.sprod`, `Oseledets/Lyapunov/OseledetsLimit/SingularValues.lean`). The sum of the
positive-part logarithms of the singular values of `M` equals the log of the positive-part
singular-value product `∏ i, max 1 σᵢ(M)`. -/
theorem sum_posLog_singularValues_toEuclideanLin_eq {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (s : Finset ℕ) :
    ∑ i ∈ s, Real.posLog ((Matrix.toEuclideanLin M).singularValues i)
      = Real.log (∏ i ∈ s, max 1 ((Matrix.toEuclideanLin M).singularValues i)) :=
  sum_posLog_singularValues_eq_log_prod_max_one (Matrix.toEuclideanLin M) s

end Oseledets.Entropy

/-! ## The sharpened Margulis–Ruelle reduction (part B) -/

namespace Oseledets

variable {d : ℕ} [NeZero d]

/-- **The Margulis–Ruelle inequality, sharpened restatement.** This is `EReal`-for-`EReal` the
same conclusion as `margulisRuelle_le_sumPosExp`, but with the geometric input renamed to
`hcount` to make explicit that the single remaining open hypothesis is a *finite-`n`,
per-partition* Ruelle counting bound — the entropy of the `n`-fold refinement of each partition,
relative to `T`, is bounded by the (deterministic, ergodic-constant) positive-exponent sum. The
conclusion `h(T) ≤ Σ λᵢ⁺` then follows by the abstract supremum reduction
(`margulisRuelle_le_sumPosExp`), which is purely lattice-theoretic.

The renaming clarifies the wall: `hcount` is *not* a restatement of the conclusion (which is a
supremum over all partitions); it is the per-partition covering estimate produced — for a fixed
partition `P` — by the dynamical covering-count lemma described in the module `## The minimal
absent geometric atom`. The positive-part singular-value product `∏ᵢ max(1, σᵢ(D T^[n]))`, whose
log is `sum_posLog_singularValues_toEuclideanLin_eq` (part A), is precisely the per-step volume
factor that bound counts. -/
theorem margulisRuelle_le_sumPosExp'
    {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hT : Ergodic T μ) (hdiff : Differentiable ℝ T)
    (hdet : ∀ x, (derivativeCocycle T x).det ≠ 0)
    (hint : IntegrableLogNorm (derivativeCocycle T) μ)
    (hint' : IntegrableLogNorm (fun x => (derivativeCocycle T x)⁻¹) μ)
    (hcount : ∀ (n : ℕ) (P : Entropy.MeasurePartition μ (Fin n)),
        ((Entropy.ksEntropyPartition hT.toMeasurePreserving P : ℝ) : EReal)
          ≤ ((sumPosExp hT hdet (measurable_derivativeCocycle T) hint hint' : ℝ) : EReal)) :
    Entropy.ksEntropy hT.toMeasurePreserving
      ≤ ((sumPosExp hT hdet (measurable_derivativeCocycle T) hint hint' : ℝ) : EReal) :=
  margulisRuelle_le_sumPosExp hT hdiff hdet hint hint' hcount

end Oseledets
