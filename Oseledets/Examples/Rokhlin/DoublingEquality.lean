/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Examples.Rokhlin.AbstractEqui
import Oseledets.Examples.Rokhlin.DoublingCrux

/-!
# Rokhlin's entropy equality for the doubling map

This module assembles the concrete realization of **Pesin's entropy equality on a real expanding
system**: for the doubling map `T : y ↦ 2 • y` on `UnitAddCircle` and the binary generating
partition `α = {[0,1/2), [1/2,1)}`,
`h(α, T) = log 2 = ∫ log|det D(2x)| dμ = ∫ log 2 dμ`.

The entropy side is `ksEntropyPartition_doublingMap_eq_log_two`, obtained by feeding the
join-cell measure `volume_binJoinCell` (every `n`-fold-join cell has volume `2⁻ⁿ`) into the
abstract uniform-join reduction `ksEntropyPartition_of_uniform`. The integral side is
`integral_log_det_doublingMap_eq_log_two`: the Jacobian `|det D(2x)| = 2` is constant, so its log
integrates against the probability measure to `log 2`. Their agreement is the headline
`rokhlin_equality_doublingMap`.

Unlike the `EuclideanSpace`-framed Margulis–Ruelle *inequality* `h ≤ ∑ λᵢ⁺`, this is the genuine
Pesin/Rokhlin *equality* `h = ∫ log|det DT|`, realized on a real expanding system.

## Main results

* `Oseledets.Examples.Rokhlin.ksEntropyPartition_doublingMap_eq_log_two`: `h(α, T) = log 2`.
* `Oseledets.Examples.Rokhlin.integral_log_det_doublingMap_eq_log_two`: `∫ log 2 dμ = log 2`.
* `Oseledets.Examples.Rokhlin.rokhlin_equality_doublingMap`: the two sides agree.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
* V. A. Rokhlin, *Lectures on the entropy theory of measure-preserving transformations* (1967).
-/

open MeasureTheory Function Set
open scoped ENNReal

namespace Oseledets.Examples.Rokhlin

open Oseledets Oseledets.Entropy

/-! ### The binary partition of the unit circle -/

/-- The binary cells are pairwise disjoint (hence a.e.-disjoint): via `mem_binCell_iff` a point's
membership in `binCell i` is determined by which half of `[0,1)` its representative `rep` lies in,
and the two halves `binLift 0 = [0,1/2)`, `binLift 1 = [1/2,1)` are disjoint. -/
lemma disjoint_binCell {i j : Fin 2} (hij : i ≠ j) : Disjoint (binCell i) (binCell j) := by
  rw [Set.disjoint_left]
  intro y hi hj
  rw [mem_binCell_iff] at hi hj
  -- `rep y` lies in both `binLift i` and `binLift j`; but for `i ≠ j` these half-intervals are
  -- disjoint, a contradiction.
  fin_cases i <;> fin_cases j <;> simp_all only [ne_eq, not_true_eq_false] <;>
    · simp only [binLift, mem_Ico] at hi hj
      norm_num at hi hj
      linarith [hi.1, hi.2, hj.1, hj.2]

/-- The binary cells are pairwise almost-everywhere disjoint (they are in fact genuinely disjoint;
see `disjoint_binCell`). -/
lemma aedisjoint_binCell :
    Pairwise (AEDisjoint volume on binCell) :=
  fun _ _ hij => (disjoint_binCell hij).aedisjoint

/-- The binary cells cover the circle: every point's representative `rep y ∈ [0,1)` lies in one of
the two halves `[0,1/2)` or `[1/2,1)`, so `y` lies in `binCell 0` or `binCell 1`. -/
lemma cover_binCell : ⋃ i, binCell i = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro y
  rw [Set.mem_iUnion]
  have hrep : rep y ∈ Ico (0 : ℝ) 1 := rep_mem_Ico y
  simp only [mem_Ico] at hrep
  rcases lt_or_ge (rep y) (1 / 2) with h | h
  · refine ⟨0, ?_⟩
    rw [mem_binCell_iff]
    simp only [binLift, mem_Ico, Fin.val_zero, Nat.cast_zero, zero_div, zero_add]
    norm_num
    exact ⟨hrep.1, h⟩
  · refine ⟨1, ?_⟩
    rw [mem_binCell_iff]
    simp only [binLift, mem_Ico, Fin.val_one, Nat.cast_one]
    norm_num
    exact ⟨h, hrep.2⟩

/-- The **binary partition** `{[0,1/2), [1/2,1)}` of the unit circle, as a `MeasurePartition` for
the `volume` (Haar) measure. -/
noncomputable def binPartition : MeasurePartition (volume : Measure UnitAddCircle) (Fin 2) where
  cells := binCell
  measurable := measurableSet_binCell
  aedisjoint := aedisjoint_binCell
  cover := cover_binCell

@[simp]
lemma binPartition_cells : binPartition.cells = binCell := rfl

/-! ### The entropy side: `h(α, T) = log 2` -/

/-- Every `n`-fold-join cell of `binPartition` under the doubling map has volume `(2 ^ n)⁻¹`. This
restates `volume_binJoinCell` for the bundled partition, matching the hypothesis shape of
`ksEntropyPartition_of_uniform` (with `Fintype.card (Fin 2) = 2`). -/
lemma uniform_binJoin (n : ℕ) (f : Fin n → Fin 2) :
    volume ((ksJoin ergodic_doublingMap.toMeasurePreserving binPartition n).cells f)
      = ((Fintype.card (Fin 2) : ℝ≥0∞) ^ n)⁻¹ := by
  rw [ksJoin_cells, binPartition_cells, Fintype.card_fin]
  exact volume_binJoinCell n f

/-- **Rokhlin equality, entropy side: `h(α, T) = log 2`.** The partition-relative
Kolmogorov–Sinai entropy of the binary partition under the doubling map is `Real.log 2`. The
`n`-fold join is the uniform partition into `2ⁿ` dyadic arcs of equal measure `2⁻ⁿ`
(`uniform_binJoin`), so the abstract uniform-join reduction `ksEntropyPartition_of_uniform` gives
`h(α, T) = log (card (Fin 2)) = log 2`. -/
theorem ksEntropyPartition_doublingMap_eq_log_two :
    ksEntropyPartition ergodic_doublingMap.toMeasurePreserving binPartition = Real.log 2 := by
  rw [ksEntropyPartition_of_uniform ergodic_doublingMap.toMeasurePreserving binPartition
    uniform_binJoin, Fintype.card_fin]
  norm_num

/-! ### The integral side: `∫ log|det D(2x)| dμ = log 2` -/

/-- **Rokhlin equality, integral side: `∫ log|det DT| dμ = log 2`.** The derivative of the doubling
map `x ↦ 2x` is multiplication by `2`, so `|det DT| = 2` is constant and `log|det DT| = log 2`.
Integrating the constant `log 2` against the probability measure `volume` on the unit circle gives
`(volume univ).real • log 2 = 1 · log 2 = log 2`. -/
theorem integral_log_det_doublingMap_eq_log_two :
    ∫ _ : UnitAddCircle, Real.log 2 ∂(volume : Measure UnitAddCircle) = Real.log 2 := by
  rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

/-! ### The headline: entropy = integral -/

/-- **Pesin/Rokhlin equality on the doubling map.** The Kolmogorov–Sinai entropy of the binary
partition under the doubling map equals the integral of `log|det DT| = log 2` of the constant
Jacobian: both sides are `Real.log 2`. This is the concrete realization of Pesin's *equality* on a
real expanding system that the `EuclideanSpace`-framed Margulis–Ruelle *inequality* cannot give. -/
theorem rokhlin_equality_doublingMap :
    ksEntropyPartition ergodic_doublingMap.toMeasurePreserving binPartition
      = ∫ _ : UnitAddCircle, Real.log 2 ∂(volume : Measure UnitAddCircle) := by
  rw [ksEntropyPartition_doublingMap_eq_log_two, integral_log_det_doublingMap_eq_log_two]

end Oseledets.Examples.Rokhlin
