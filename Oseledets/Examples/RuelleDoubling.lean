/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Examples.Elementary
import Oseledets.Lyapunov.Extensions.ExponentSums
import Oseledets.Entropy.Ruelle.Crude

/-!
# A non-vacuous instance of the Margulis–Ruelle inequality: the doubling map

The abstract Margulis–Ruelle inequality `h(T) ≤ ∑ λᵢ⁺` (`Oseledets.margulisRuelle_le_sumPosExp`,
`Oseledets.margulisRuelle_sharp`) isolates the genuinely geometric content as an explicit
atom-counting hypothesis and proves everything around it. This module **instantiates that content
concretely** on the classical worked example for which the inequality is a sharp, *non-trivial*
equality: the **doubling map** `T : y ↦ 2 • y` on the unit circle (`Oseledets.doublingMap`,
`Oseledets/Examples/Elementary.lean`).

For the doubling map both sides of the inequality equal `log 2`:

* the **right-hand side** — the sum of the strictly positive Lyapunov exponents of the (constant)
  derivative cocycle, generator `M = !![2]` — is `log 2` (the single exponent is `log 2 > 0`); and
* the **left-hand side** — the Kolmogorov–Sinai entropy — is `log 2` as well, by the binary
  generating partition (the topological-entropy / variational content).

So `h(T) ≤ ∑ λᵢ⁺` reads `log 2 ≤ log 2`: a *non-vacuous* instance, in contrast to a trivial
isometry where it would be `0 ≤ 0`.

## What is discharged here, and what stays an honest input

* **The right-hand side is computed unconditionally.** `Oseledets.doublingMap_sumPosExp_eq_log_two`
  proves `sumPosExp = log 2` for the doubling-map constant cocycle, with *every* spectrum hypothesis
  (invertibility, measurability, the two log-integrability conditions) discharged from the
  constant-cocycle API (`const_det_ne_zero`, `const_measurable`, `const_integrableLogNorm`,
  `const_integrableLogNorm_inv`). It reuses the proven single exponent
  `Oseledets.doublingMap_topExponent_eq_log_two` (`= log 2`). This is the genuine positive-exponent
  *sum* side of Margulis–Ruelle, fully sorry-free.

* **The per-partition Ruelle inequality is instantiated at the sharp rate `log 2`.**
  `Oseledets.doublingMap_ksEntropyPartition_le_sumPosExp` specializes the unconditional arithmetic
  backbone `Oseledets.Entropy.ksEntropyPartition_le_of_atomCount_growth` to the doubling map at the
  exponential rate `R = log 2`, and then *identifies that rate with the computed positive-exponent
  sum*: from the honest atom-count growth `atomCount ≤ C · 2ⁿ` of a partition's `n`-refinement, the
  partition entropy `h(α, T)` is bounded by `sumPosExp = log 2`. The rate here is not an assumed
  abstract constant — it is the actual Lyapunov datum `log 2`, so this is a *sharp, named* instance.

The atom-count growth at rate `log 2` is the genuine geometric input (the doubling map is exactly
`2`-to-`1`, so the `n`-refinement of a partition into intervals has `≈ 2ⁿ` non-empty atoms); it has
exactly the status it carries in `Oseledets.Entropy.Ruelle.Crude` and
`Oseledets.margulisRuelle_sharp` (the Mañé/Katok count), here with the *rate pinned to the true
exponent*. The remaining bridge to a
fully unconditional `h(T) ≤ log 2` over **all** partitions is the Kolmogorov–Sinai theorem
`h(T) = h(α, T)` for a generating partition (Le Maître's notes, Thm. 5), multi-month-scale ergodic
infrastructure not present in Mathlib, hence deliberately left as the named input.

## Main results

* `Oseledets.doublingMap_sumPosExp_eq_log_two` — the positive-exponent sum of the doubling-map
  constant cocycle is `log 2` (unconditional, all hypotheses discharged).
* `Oseledets.doublingMap_ksEntropyPartition_le_sumPosExp` — the **non-vacuous Ruelle inequality**
  `h(α, T) ≤ ∑ λᵢ⁺ = log 2` for the doubling map, from the honest atom-count growth at the sharp
  rate `log 2`.

## References

* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
* Maryam Contractor, *The Pesin Entropy Formula*, UChicago REU 2023, §7.
* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §2 (Thm. 5).
-/

open MeasureTheory Filter Topology

namespace Oseledets

/-! ## The positive-exponent sum of the doubling-map cocycle is `log 2` -/

/-- The single Lyapunov exponent of the doubling-map constant cocycle (generator `M = !![2]`,
indexed by `Fin (Fintype.card (Fin 1)) = Fin 1`) is `log 2`.

This is `Oseledets.doublingMap_topExponent_eq_log_two` read off the only spectrum index: the top
exponent `exponents … ⟨0, _⟩` *is* the single exponent, and a subsingleton index forces every index
to that value. -/
theorem doublingMap_exponents_eq_log_two
    (i : Fin (Fintype.card (Fin 1))) :
    exponents ergodic_doublingMap (const_det_ne_zero doublingGen_det_ne_zero)
        (const_measurable doublingGen) (const_integrableLogNorm doublingGen)
        (const_integrableLogNorm_inv doublingGen) i
      = Real.log 2 := by
  -- `exponents_const` evaluates the spectrum at the (only) sorted index to `log` of the eigenvalue.
  have key := exponents_const ergodic_doublingMap doublingGen_transpose doublingGen_det_ne_zero
    (i : Fin (Fintype.card (Fin 1)))
  rw [eigenvalues₀_absMatrix_of_posSemidef doublingGen_posSemidef, doublingGen_eigenvalue] at key
  -- The reindexing `⟨(i : ℕ), …⟩ : Fin 1` is the index `i` itself.
  rwa [show (⟨(i : ℕ), lt_of_lt_of_eq i.isLt (Fintype.card_fin 1)⟩ : Fin 1) = i from
    Fin.ext rfl] at key

/-- **Doubling map: the sum of the strictly positive Lyapunov exponents is `log 2`.**

The right-hand side of the Margulis–Ruelle inequality for the doubling-map constant cocycle
(generator `M = !![2]`) is `log 2`: the spectrum has a single exponent `log 2 > 0`, so the
positive-exponent sum is that one term. **Every** hypothesis (invertibility, measurability, and the
two log-integrability conditions) is discharged from the constant-cocycle API, so this
computation is unconditional. -/
theorem doublingMap_sumPosExp_eq_log_two :
    sumPosExp ergodic_doublingMap (const_det_ne_zero doublingGen_det_ne_zero)
        (const_measurable doublingGen) (const_integrableLogNorm doublingGen)
        (const_integrableLogNorm_inv doublingGen)
      = Real.log 2 := by
  classical
  -- Abbreviate the exponent function; every entry is `log 2 > 0`, so the positive filter is all of
  -- `Finset.univ`, and the sum over the single index `Fin 1` is `log 2`.
  rw [sumPosExp]
  have hval : ∀ i, exponents ergodic_doublingMap (const_det_ne_zero doublingGen_det_ne_zero)
      (const_measurable doublingGen) (const_integrableLogNorm doublingGen)
      (const_integrableLogNorm_inv doublingGen) i = Real.log 2 :=
    doublingMap_exponents_eq_log_two
  have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- The positive-exponent filter is the full `Finset.univ` (every exponent is `log 2 > 0`).
  have hfilter : (Finset.univ.filter fun i =>
      0 < exponents ergodic_doublingMap (const_det_ne_zero doublingGen_det_ne_zero)
        (const_measurable doublingGen) (const_integrableLogNorm doublingGen)
        (const_integrableLogNorm_inv doublingGen) i) = (Finset.univ : Finset (Fin 1)) := by
    refine Finset.filter_true_of_mem (fun i _ => ?_)
    rw [hval i]; exact hpos
  rw [hfilter, Finset.sum_congr rfl (fun i _ => hval i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, one_smul]

/-! ## The non-vacuous per-partition Ruelle inequality for the doubling map -/

/-- **The non-vacuous Margulis–Ruelle inequality for the doubling map.**

For any finite measurable partition `P` of the unit circle whose `n`-fold refinement
`⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P` under the doubling map has eventually at most `C · 2ⁿ` non-empty atoms
(`hgrow`, with `C ≥ 1`), the Kolmogorov–Sinai partition entropy is bounded by the sum of the
strictly positive Lyapunov exponents of the (constant) derivative cocycle:

`h(α, T) ≤ ∑ λᵢ⁺ = log 2`.

This is a **sharp, non-vacuous** instance of the Margulis–Ruelle inequality: the right-hand side is
the *computed* exponent sum `log 2` (`doublingMap_sumPosExp_eq_log_two`), not an abstract constant,
and for the binary generating partition equality `h(α, T) = log 2` holds, so the bound is attained.

The atom-count growth `hgrow` is the genuine geometric input — the doubling map is exactly
`2`-to-`1`, so a partition into intervals refines under `T^[n]` into `≈ 2ⁿ` atoms — pinned here to
the **sharp**
rate `log 2 = ∑ λᵢ⁺` (note `2ⁿ = exp(n · log 2)`). The reduction itself is the unconditional
arithmetic backbone `Oseledets.Entropy.ksEntropyPartition_le_of_atomCount_growth`. -/
theorem doublingMap_ksEntropyPartition_le_sumPosExp {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : Entropy.MeasurePartition (volume : Measure UnitAddCircle) ι) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ᶠ n : ℕ in atTop,
      (Entropy.atomCount ergodic_doublingMap.toMeasurePreserving P n : ℝ)
        ≤ C * Real.exp (n * Real.log 2)) :
    Entropy.ksEntropyPartition ergodic_doublingMap.toMeasurePreserving P
      ≤ sumPosExp ergodic_doublingMap (const_det_ne_zero doublingGen_det_ne_zero)
          (const_measurable doublingGen) (const_integrableLogNorm doublingGen)
          (const_integrableLogNorm_inv doublingGen) := by
  rw [doublingMap_sumPosExp_eq_log_two]
  exact Entropy.ksEntropyPartition_le_of_atomCount_growth
    ergodic_doublingMap.toMeasurePreserving P hC hgrow

end Oseledets
