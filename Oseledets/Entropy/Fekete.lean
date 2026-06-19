/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.Subadditive
import Oseledets.Entropy.Subadditive2

/-!
# Pullback partitions and the iterated-join entropy sequence

This file continues the measure-theoretic foundation for Kolmogorov–Sinai entropy started in
`Oseledets.Entropy.Partition`, `Oseledets.Entropy.Join`, `Oseledets.Entropy.Subadditive`, and
`Oseledets.Entropy.Subadditive2`. It builds the dynamical refinements that feed the Fekete limit
defining the entropy `h(α, T)` of a measure-preserving transformation `T` relative to a finite
measurable partition `α`.

Following the Le Maître notes on the Kolmogorov–Sinai theorem, the **iterated join**
`⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α` is the common refinement obtained by repeatedly pulling `α` back along `T`. We
realize it by the recursion `P 0 = α`, `P (n+1) = α ∨ T⁻¹(P n)`, where the **pullback partition**
`T⁻¹ β = (T⁻¹ Bⱼ)` of a measurable partition `β` along a measure-preserving `T` is again a
measurable partition (its cells are measurable, pairwise almost-everywhere disjoint, and cover the
space, all because `T` is measurable and the preimage of a covering a.e.-disjoint family has the
same properties). The associated **entropy sequence** `entropySeq α T n = H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α)` is
nonnegative, and grows at most one `H(α)` per step:

`H(⋁ₖ₌₀ⁿ T⁻ᵏ α) ≤ H(α) + H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α)`,

which is the join subadditivity `entropy_join_le` combined with the `T`-invariance
`entropy_comp_preimage`. Iterating gives the linear bound `entropySeq α T n ≤ (n + 1) • H(α)`, so
the sequence is bounded above by a linear function — the boundedness half of the Fekete hypothesis.

## Main definitions

* `Oseledets.Entropy.MeasurePartition.pullback`: the partition `T⁻¹ β` whose cells are the
  preimages `T⁻¹ Bⱼ`, for a measure-preserving `T`.
* `Oseledets.Entropy.iteratedJoinPartition`: the `n`-fold refinement `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α`, a
  measurable partition for each `n`.
* `Oseledets.Entropy.entropySeq`: the real sequence `n ↦ H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α)`.

## Main results

* `Oseledets.Entropy.entropy_pullback`: the pullback partition has the same entropy as the
  original, `H(T⁻¹ β) = H(β)`.
* `Oseledets.Entropy.entropySeq_nonneg`: the entropy sequence is nonnegative.
* `Oseledets.Entropy.entropySeq_succ_le`: the per-step bound
  `entropySeq α T (n+1) ≤ H(α) + entropySeq α T n`.
* `Oseledets.Entropy.entropySeq_le_nsmul`: the linear upper bound
  `entropySeq α T n ≤ (n + 1) • H(α)`.

## Implementation notes

The full Fekete packaging — exhibiting `entropySeq α T` as a `Subadditive` sequence (so that
`Subadditive.tendsto_lim` produces the Kolmogorov–Sinai entropy `h(α, T)`) — requires the exact
common-refinement identity `⋁ₖ₌₀ⁿ⁺ᵐ⁻¹ T⁻ᵏ α = (⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α) ∨ T⁻ⁿ(⋁ₖ₌₀ᵐ⁻¹ T⁻ᵏ α)` as an
equality of refinements *up to reindexing of cells*. With the recursion used here the two sides
carry different (nested-product) index types, and matching them is a substantial reindexing
argument that is deferred; only the per-step inequality (hence the linear upper bound) is
established here, which is the boundedness half of the Fekete hypothesis. The strict
subadditivity `entropySeq (n+m) ≤ entropySeq n + entropySeq m` and the limit `h(α, T)` are left
for future work.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Function

namespace Oseledets.Entropy

variable {α : Type*} {ι : Type*} [MeasurableSpace α]

/-- The **pullback partition** `T⁻¹ β` of a finite measurable partition `β = P` along a
measure-preserving transformation `T : α → α`: the partition whose cell at index `i` is the
preimage `T⁻¹ (P.cells i)`. Each cell is measurable (preimage of a measurable set under the
measurable `T`); the family is pairwise almost-everywhere disjoint (the preimage of an
a.e.-disjoint pair is a.e. disjoint, since `T` preserves measures); and the cells cover the space
(the preimage of the cover `⋃ i, P.cells i = univ` is `univ`). -/
noncomputable def MeasurePartition.pullback [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) : MeasurePartition μ ι where
  cells := fun i => T ⁻¹' P.cells i
  measurable := fun i => (P.measurable i).preimage hT.measurable
  aedisjoint := by
    intro i j hij
    simp only [onFun, AEDisjoint, ← Set.preimage_inter]
    rw [hT.measure_preimage ((P.measurable i).inter (P.measurable j)).nullMeasurableSet]
    exact P.aedisjoint hij
  cover := by rw [← Set.preimage_iUnion, P.cover, Set.preimage_univ]

@[simp]
lemma MeasurePartition.pullback_cells [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    (P.pullback hT).cells = fun i => T ⁻¹' P.cells i := rfl

/-- **`T`-invariance of partition entropy.** The pullback partition `T⁻¹ β` along a
measure-preserving `T` has the same Shannon entropy as `β`, since `T` preserves the measure of
each cell. This is `entropy_comp_preimage` specialized to the cells of a partition. -/
lemma entropy_pullback [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    entropy μ (P.pullback hT).cells = entropy μ P.cells := by
  rw [MeasurePartition.pullback_cells]
  exact entropy_comp_preimage hT P.cells (fun i => (P.measurable i).nullMeasurableSet)

/-- The nested-product index type of `iteratedJoinPartition`: `ι` for `n = 0`, and `ι × (index n)`
for `n + 1`, matching the recursion `P (n+1) = α ∨ T⁻¹(P n)` whose join is indexed by the product
of the two factors' index types. -/
def iteratedJoinIndex (ι : Type*) : ℕ → Type _
  | 0 => ι
  | n + 1 => ι × iteratedJoinIndex ι n

instance iteratedJoinIndex.instFintype [Fintype ι] : (n : ℕ) → Fintype (iteratedJoinIndex ι n)
  | 0 => inferInstanceAs (Fintype ι)
  | n + 1 => @instFintypeProd _ _ _ (iteratedJoinIndex.instFintype n)

/-- The **iterated join** `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α`, defined by the recursion `P 0 = α`,
`P (n+1) = α ∨ T⁻¹(P n)`: a finite measurable partition for each `n`, indexed by a nested product
of copies of `ι`. Refining `α` by its `T`-pullbacks `n` times records, for a `μ`-random point, the
cells of `α` it visits along the first `n` steps of the orbit under `T`. -/
noncomputable def iteratedJoinPartition [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    (n : ℕ) → MeasurePartition μ (iteratedJoinIndex ι n)
  | 0 => P
  | n + 1 => P.join ((iteratedJoinPartition hT P n).pullback hT)

/-- The **entropy sequence** `n ↦ H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α)` of the iterated join. Its Fekete limit is the
Kolmogorov–Sinai entropy `h(α, T)` of `T` relative to `α`; here we record only that it is
nonnegative and grows at most `H(α)` per step. -/
noncomputable def entropySeq [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) : ℝ :=
  entropy μ (iteratedJoinPartition hT P n).cells

@[simp]
lemma entropySeq_zero [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    entropySeq hT P 0 = entropy μ P.cells := rfl

/-- The Shannon entropy of the iterated join is nonnegative for a probability measure. -/
lemma entropySeq_nonneg [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    0 ≤ entropySeq hT P n :=
  entropy_nonneg μ _

/-- **Per-step subadditivity of the iterated-join entropy.** Refining by one more `T`-pullback
adds at most `H(α)` to the entropy:
`H(⋁ₖ₌₀ⁿ T⁻ᵏ α) ≤ H(α) + H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α)`. This is the join subadditivity `entropy_join_le`
applied to `α` and the pulled-back iterate, together with the `T`-invariance `entropy_pullback`
identifying the second summand. -/
lemma entropySeq_succ_le [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    entropySeq hT P (n + 1) ≤ entropy μ P.cells + entropySeq hT P n := by
  have hle := entropy_join_le P ((iteratedJoinPartition hT P n).pullback hT)
  rw [entropy_pullback] at hle
  exact hle

/-- **Linear upper bound on the iterated-join entropy.** Iterating the per-step bound from the
base value `entropySeq α T 0 = H(α)`, the entropy of the `n`-fold refinement is at most `n + 1`
times the entropy of `α`:
`H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α) ≤ (n + 1) • H(α)`. In particular the entropy sequence grows at most linearly,
the boundedness half of the Fekete hypothesis. -/
lemma entropySeq_le_nsmul [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    entropySeq hT P n ≤ (n + 1) • entropy μ P.cells := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc entropySeq hT P (n + 1)
        ≤ entropy μ P.cells + entropySeq hT P n := entropySeq_succ_le hT P n
      _ ≤ entropy μ P.cells + (n + 1) • entropy μ P.cells := by gcongr
      _ = (n + 1 + 1) • entropy μ P.cells := by rw [succ_nsmul]; ring

end Oseledets.Entropy
