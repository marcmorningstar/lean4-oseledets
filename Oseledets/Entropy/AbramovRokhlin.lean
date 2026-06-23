/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.FactorEntropy
import Oseledets.Entropy.CondKSEntropySystem

/-!
# The Abramov–Rokhlin addition formula (issue #13)

For a factor map `π : (α, T, μ) → (β, S, ν)` of measure-preserving systems, the **Abramov–Rokhlin
addition formula** decomposes the Kolmogorov–Sinai entropy of the total system as the entropy of
the factor plus the *relative* (fibrewise) entropy conditioned on the factor σ-algebra:

`h(T) = h(S) + h(T | comap π 𝓑_Y)`.

This file assembles the formula from the proved ingredient stack. The assembly threads three
inputs through pure `EReal` algebra:

1. the **factor-relative entropy invariance** `h(π⁻¹R, T) = h(R, S)`
   (`Oseledets.Entropy.factor_relative_eq`), proved sorry-free in `FactorEntropy`;
2. the two **generator reductions** `h(T) = h(P, T)` and `h(S) = h(R, S)`, and the
   **relative-generator reduction** `h(T | 𝒜) = h(P, T | 𝒜)` — supplied hypotheses, exactly the
   supplied-generator interface of `Oseledets.Entropy.Generator`;
3. the **partition-level Abramov–Rokhlin identity** (B6a)
   `h(P, T) = h(π⁻¹R, T) + h(P, T | comap π 𝓑_Y)`,
   for a generating `P` refining the pulled-back partition `π⁻¹R`.

Item (3) is the analytic heart: it follows from the finite conditional chain rule per `n`, divided
by `n` and passed to the limit, where the conditioning σ-algebra `σ(⋁_{k<n} T⁻ᵏπ⁻¹R)` increases to
the fixed `comap π 𝓑_Y` and a martingale/σ-convergence step (Lévy upward, `tendsto_ae_condExp`)
replaces it by the limit. The present file takes (3) as a **named hypothesis**
`hBA : ksEntropyPartition hT P = ksEntropyPartition hT (R.pulledBack hπ.measurePreserving)
    + condKsEntropyPartition hm hT hinv P`,
so the headline `abramov_rokhlin` is **sorry-free modulo that one supplied identity** — all of (1),
(2) and the `EReal` assembly are honestly discharged.

## Main results

* `Oseledets.Entropy.abramov_rokhlin`: the addition formula
  `h(T) = h(S) + h(T | comap π 𝓑_Y)`, under the factor map, the generator/relative-generator
  reductions, and the supplied partition-level identity (B6a).

## References

* L. M. Abramov, V. A. Rokhlin, *The entropy of a skew product of measure-preserving
  transformations*, Vestnik Leningrad Univ. **17** (1962).
* Peter Walters, *An Introduction to Ergodic Theory*, GTM **79**, Springer (1982), Ch. 4.
-/

open MeasureTheory Function

namespace Oseledets.Entropy

variable {α β : Type*} {n m : ℕ}
variable [mα : MeasurableSpace α] [mβ : MeasurableSpace β] [StandardBorelSpace α]

/-- **The Abramov–Rokhlin addition formula** for a factor map `π : (α, T, μ) → (β, S, ν)`:
`h(T) = h(S) + h(T | comap π 𝓑_Y)`,
where `comap π 𝓑_Y = MeasurableSpace.comap π mβ` is the factor (invariant) sub-σ-algebra of the
source pulled back from the target.

The formula is assembled from:

* `hfac : IsFactorMap π T S μ ν` — the factor map, supplying that `π` is measure preserving, the
  forward-invariance of `comap π mβ` (`hinv`, via `IsFactorMap.invariant_comap`), and the
  inclusion `comap π mβ ≤ mα` (`hm`, via `IsFactorMap.measurable_comap_le`);
* `hredT : h(T) = h(P, T)` and `hredS : h(S) = h(R, S)` — the two generator reductions for the
  total and factor systems (supplied-generator interface);
* `hredRel : h(T | comap π mβ) = h(P, T | comap π mβ)` — the relative-generator reduction;
* `hBA` — the partition-level Abramov–Rokhlin identity (B6a), the one supplied analytic input
  `h(P, T) = h(π⁻¹R, T) + h(P, T | comap π mβ)`.

Given these, the proof is pure `EReal` algebra: rewrite `h(T)` by `hredT`, expand the
partition-level identity `hBA`, identify `h(π⁻¹R, T) = h(R, S)` via `factor_relative_eq`, fold the
factor side back to `h(S)` via `hredS`, and the relative side to `h(T | comap π mβ)` via
`hredRel`. -/
theorem abramov_rokhlin
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T : α → α} {S : β → β} {π : α → β}
    (hfac : IsFactorMap π T S μ ν)
    (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S ν ν)
    (P : MeasurePartition μ (Fin n)) (R : MeasurePartition ν (Fin m))
    (hm : MeasurableSpace.comap π mβ ≤ mα)
    (hinv : MeasurableSpace.comap T (MeasurableSpace.comap π mβ) ≤ MeasurableSpace.comap π mβ)
    (hredT : ksEntropy hT = ((ksEntropyPartition hT P : ℝ) : EReal))
    (hredS : ksEntropy hS = ((ksEntropyPartition hS R : ℝ) : EReal))
    (hredRel : condKsEntropy hm hT hinv
        = ((condKsEntropyPartition hm hT hinv P : ℝ) : EReal))
    (hBA : ksEntropyPartition hT P
        = ksEntropyPartition hT (R.pulledBack hfac.1)
          + condKsEntropyPartition hm hT hinv P) :
    ksEntropy hT = ksEntropy hS + condKsEntropy hm hT hinv := by
  -- Factor-relative invariance: `h(π⁻¹R, T) = h(R, S)`.
  have hfre : ksEntropyPartition hT (R.pulledBack hfac.1) = ksEntropyPartition hS R :=
    factor_relative_eq hT hS hfac.1 hfac.2.2 R
  -- Pure `EReal` assembly: combine the two real coercions on the right via `EReal.coe_add`.
  rw [hredT, hredS, hredRel, hBA, hfre, EReal.coe_add]

end Oseledets.Entropy
