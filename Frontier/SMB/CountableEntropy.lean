/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Shannon entropy of a countable measurable partition

This is **node 1** of the Shannon–McMillan–Breiman (SMB) formalization: the *static*
countable-partition Shannon-entropy API. Mathlib has only topological entropy and the
function `Real.negMulLog`; it has no measure-theoretic partition entropy. The project's existing
entropy (`Oseledets/Entropy/`) is `[Fintype ι]`-only. SMB needs the **countable** partition `P`
(its atom at `x` shrinks along the dynamical refinement `⋁ₖ T⁻ᵏ P`), so we need a countable-index
Shannon entropy that composes with joins, pullbacks and iterated joins.

## Value type: `ℝ≥0∞`

A countable partition can have **infinite** Shannon entropy (e.g. `μ(Aᵢ) ∝ 1/(i log²i)` gives a
divergent `∑ -p log p`), so the real-valued `tsum` — which silently returns `0` on a non-summable
family — is mathematically *wrong* here. We therefore land the entropy in `ℝ≥0∞` via
`ENNReal.ofReal (negMulLog (μ Aᵢ).toReal)`. Each summand is `≥ 0` because on a probability measure
`(μ Aᵢ).toReal ∈ [0,1]` and `negMulLog` is nonnegative there, so the `ℝ≥0∞`-valued `tsum` is
*always* well-defined and equals `+∞` exactly when the real series diverges. This is the textbook
convention `H(P) ∈ [0, ∞]`. It also makes the join/pullback/Fekete algebra clean: `ℝ≥0∞`-tsum is
unconditionally additive (`ENNReal.tsum_add`), Fubini-commutes (`ENNReal.tsum_prod`,
`ENNReal.tsum_comm`), and is monotone termwise (`ENNReal.tsum_le_tsum`) with **no** summability
side goals — exactly what subadditivity under joins needs.

## Main definitions

* `Frontier.SMB.CountablePartition`: a `[Countable ι]`-indexed family of measurable cells that are
  pairwise almost-everywhere disjoint and almost-everywhere cover the space. Designed to compose:
  the join `P ⊔ Q` is indexed by `ι × κ` with cells `Aᵢ ∩ Bⱼ`, and the pullback `T⁻¹ P` along a
  measurable map keeps the index type.
* `Frontier.SMB.entropy μ s`: the Shannon entropy `∑' i, ofReal (negMulLog (μ (s i)).toReal)`
  of a countable family of cells, valued in `ℝ≥0∞`.
* `Frontier.SMB.CountablePartition.join`: the common refinement `P ⊔ Q`.
* `Frontier.SMB.CountablePartition.comap`: the pullback `f⁻¹ P` along a measurable `f`.

## Main results

* `Frontier.SMB.entropy_nonneg`: `0 ≤ entropy μ s` (trivial in `ℝ≥0∞`, kept for the interface).
* `Frontier.SMB.entropy_le_log_card`: for a finite index, `entropy ≤ ofReal (log card)` (Jensen).
* `Frontier.SMB.CountablePartition.tsum_measure_eq_one`: the cells' measures sum to `1`.
* `Frontier.SMB.entropy_join_le`: **subadditivity** `entropy (P ⊔ Q) ≤ entropy P + entropy Q`.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
* Walters, *An Introduction to Ergodic Theory*, ch. 4.
-/

open MeasureTheory Function
open scoped ENNReal

namespace Frontier.SMB

variable {α : Type*} {ι κ : Type*} [MeasurableSpace α]

/-! ### The countable Shannon entropy -/

/-- The Shannon entropy `∑' i, ofReal (negMulLog (μ (s i)).toReal)` of a countable family of cells
`s : ι → Set α`, valued in `ℝ≥0∞`. For a genuine partition this is `- ∑ᵢ μ(sᵢ) log μ(sᵢ) ∈ [0,∞]`,
the average information gained by learning which cell a random point lies in. The `ℝ≥0∞` value
makes a possibly-infinite entropy well-defined and the join/Fubini algebra summability-free. -/
noncomputable def entropy (μ : Measure α) (s : ι → Set α) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (Real.negMulLog (μ (s i)).toReal)

lemma entropy_def (μ : Measure α) (s : ι → Set α) :
    entropy μ s = ∑' i, ENNReal.ofReal (Real.negMulLog (μ (s i)).toReal) := rfl

/-- The countable Shannon entropy is nonnegative — automatic in `ℝ≥0∞`, recorded for the
interface and to mirror the finite-index API. -/
lemma entropy_nonneg (μ : Measure α) (s : ι → Set α) : 0 ≤ entropy μ s := zero_le'

/-! ### Countable measurable partitions -/

/-- A **countable measurable partition** of a measure space `(α, μ)`: a `[Countable ι]`-indexed
family of measurable cells that are pairwise almost-everywhere disjoint and almost-everywhere cover
the whole space (`μ (⋃ i, cells i)ᶜ = 0`). The a.e. cover (rather than an on-the-nose cover) is the
right notion: it is preserved by pullback along a measure-preserving map and by joins, and it is all
the entropy/SMB arguments use. -/
structure CountablePartition (μ : Measure α) (ι : Type*) [Countable ι] where
  /-- The cells of the partition. -/
  cells : ι → Set α
  /-- Each cell is measurable. -/
  measurable : ∀ i, MeasurableSet (cells i)
  /-- The cells are pairwise almost-everywhere disjoint. -/
  aedisjoint : Pairwise (AEDisjoint μ on cells)
  /-- The cells almost-everywhere cover the whole space. -/
  ae_cover : μ (⋃ i, cells i)ᶜ = 0

variable [Countable ι] [Countable κ]

/-- The `μ`-measure of the almost-cover `⋃ i, cells i` of a countable partition is the whole mass.
From `μ (⋃ cells)ᶜ = 0`. -/
lemma CountablePartition.measure_iUnion {μ : Measure α} [IsProbabilityMeasure μ]
    (P : CountablePartition μ ι) : μ (⋃ i, P.cells i) = 1 := by
  have h : μ (⋃ i, P.cells i) + μ (⋃ i, P.cells i)ᶜ = μ Set.univ := by
    rw [measure_add_measure_compl
      (MeasurableSet.iUnion P.measurable)]
  rw [P.ae_cover, add_zero, measure_univ] at h
  exact h

/-- The `μ`-measures of the cells of a countable measurable partition of a probability space sum to
the total mass `1`. The cells are null-measurable and pairwise almost-everywhere disjoint, so the
countable additivity `measure_iUnion₀` applies, and the a.e.-cover pins the union mass to `1`. -/
lemma CountablePartition.tsum_measure_eq_one {μ : Measure α} [IsProbabilityMeasure μ]
    (P : CountablePartition μ ι) :
    ∑' i, μ (P.cells i) = 1 := by
  rw [← measure_iUnion₀ P.aedisjoint (fun i => (P.measurable i).nullMeasurableSet),
    P.measure_iUnion]

/-! ### Finite-index bound (Jensen) -/

omit [Countable ι] [Countable κ] in
/-- On a finite index type the `ℝ≥0∞`-valued entropy is the `ofReal` of the ordinary finite Shannon
sum, since the cells' summands are nonnegative and `ofReal` is additive over finite sums. -/
lemma entropy_eq_ofReal_sum [Fintype ι] (μ : Measure α) [IsProbabilityMeasure μ] (s : ι → Set α) :
    entropy μ s = ENNReal.ofReal (∑ i, Real.negMulLog (μ (s i)).toReal) := by
  rw [entropy_def, tsum_fintype, ENNReal.ofReal_sum_of_nonneg]
  intro i _
  refine Real.negMulLog_nonneg ENNReal.toReal_nonneg ?_
  have h := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := s i))
  rwa [ENNReal.toReal_one] at h

omit [Countable ι] [Countable κ] in
/-- **Maximal-entropy bound.** A finite family of `k` cells whose `μ`-measures sum to `1` (in
particular a partition of a probability space into `k` nonempty cells) has Shannon entropy at most
`log k`. This is Jensen's inequality for the concave `negMulLog` with equal weights, lifted to
`ℝ≥0∞`. -/
lemma entropy_le_log_card [Fintype ι] [Nonempty ι] (μ : Measure α) [IsProbabilityMeasure μ]
    (s : ι → Set α) (hsum : ∑ i, (μ (s i)).toReal = 1) :
    entropy μ s ≤ ENNReal.ofReal (Real.log (Fintype.card ι)) := by
  rw [entropy_eq_ofReal_sum]
  refine ENNReal.ofReal_le_ofReal ?_
  -- The real-valued Jensen bound, reproved inline (cf. `Oseledets.Entropy.entropy_le_log_card`).
  set k : ℝ := (Fintype.card ι : ℝ) with hk
  have hk_pos : 0 < k := by rw [hk]; exact_mod_cast Fintype.card_pos
  have hk_ne : k ≠ 0 := ne_of_gt hk_pos
  have hjensen :
      (∑ i, k⁻¹ • Real.negMulLog (μ (s i)).toReal) ≤
        Real.negMulLog (∑ i, k⁻¹ • (μ (s i)).toReal) := by
    refine Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
      (fun i _ => le_of_lt (inv_pos.mpr hk_pos)) ?_
      (fun i _ => Set.mem_Ici.mpr ENNReal.toReal_nonneg)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hk, mul_inv_cancel₀ hk_ne]
  have hLHS : (∑ i, k⁻¹ • Real.negMulLog (μ (s i)).toReal)
      = k⁻¹ * ∑ i, Real.negMulLog (μ (s i)).toReal := by
    rw [Finset.mul_sum]; simp only [smul_eq_mul]
  have harg : (∑ i, k⁻¹ • (μ (s i)).toReal) = k⁻¹ := by
    simp only [smul_eq_mul, ← Finset.mul_sum, hsum, mul_one]
  have hRHS : Real.negMulLog (∑ i, k⁻¹ • (μ (s i)).toReal) = k⁻¹ * Real.log k := by
    rw [harg, Real.negMulLog, Real.log_inv]; ring
  rw [hLHS, hRHS] at hjensen
  have hcancel := le_of_mul_le_mul_left hjensen (inv_pos.mpr hk_pos)
  rwa [hk] at hcancel

/-! ### Joins (common refinement) -/

/-- The cell family `(i, j) ↦ s i ∩ t j` underlying the join (common refinement) `P ⊔ Q` of two
families of cells. Indexed by `ι × κ`, keeping every index pair (null cells allowed). -/
def joinCells (s : ι → Set α) (t : κ → Set α) : ι × κ → Set α := fun p => s p.1 ∩ t p.2

omit [MeasurableSpace α] [Countable ι] [Countable κ] in
@[simp]
lemma joinCells_apply (s : ι → Set α) (t : κ → Set α) (p : ι × κ) :
    joinCells s t p = s p.1 ∩ t p.2 := rfl

/-- The **join** (common refinement) `P ⊔ Q` of two countable measurable partitions: the
`ι × κ`-indexed partition whose cell at `(i, j)` is `Aᵢ ∩ Bⱼ`. Measurability is closure under
intersection; a.e.-disjointness follows because distinct pairs differ in some coordinate, and the
a.e.-cover is `(⋃ Aᵢ) ∩ (⋃ Bⱼ)`, whose complement is contained in the union of the two null
complements. -/
noncomputable def CountablePartition.join {μ : Measure α} (P : CountablePartition μ ι)
    (Q : CountablePartition μ κ) : CountablePartition μ (ι × κ) where
  cells := joinCells P.cells Q.cells
  measurable p := (P.measurable p.1).inter (Q.measurable p.2)
  aedisjoint := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hne
    simp only [Function.onFun, joinCells]
    rcases eq_or_ne i i' with rfl | hi
    · have hj : j ≠ j' := fun h => hne (by rw [h])
      exact AEDisjoint.mono (Q.aedisjoint hj) Set.inter_subset_right Set.inter_subset_right
    · exact AEDisjoint.mono (P.aedisjoint hi) Set.inter_subset_left Set.inter_subset_left
  ae_cover := by
    have hunion : (⋃ p : ι × κ, joinCells P.cells Q.cells p)
        = (⋃ i, P.cells i) ∩ (⋃ j, Q.cells j) := by
      ext x
      simp only [joinCells, Set.mem_iUnion, Set.mem_inter_iff, Prod.exists]
      constructor
      · rintro ⟨i, j, hi, hj⟩; exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩; exact ⟨i, j, hi, hj⟩
    rw [hunion, Set.compl_inter]
    refine measure_union_null P.ae_cover Q.ae_cover

@[simp]
lemma CountablePartition.join_cells {μ : Measure α} (P : CountablePartition μ ι)
    (Q : CountablePartition μ κ) :
    (P.join Q).cells = joinCells P.cells Q.cells := rfl

/-! ### Pullback along a measurable map -/

/-- The **pullback** `f⁻¹ P` of a countable measurable partition along a measurable, measure-
preserving map `f : α → α` (e.g. the dynamics `T` of the cocycle). Same index type, cells
`f⁻¹(Aᵢ)`. Measure preservation (`MeasurePreserving f μ μ`) is what carries a.e.-disjointness and the
a.e.-cover through the preimage; it also makes each pullback cell's measure equal to the original,
which is the pullback-invariance of entropy used in the Fekete/KS step. -/
noncomputable def CountablePartition.comap {μ : Measure α} {f : α → α}
    (hf : MeasurePreserving f μ μ) (P : CountablePartition μ ι) : CountablePartition μ ι where
  cells i := f ⁻¹' P.cells i
  measurable i := hf.measurable (P.measurable i)
  aedisjoint := by
    intro i j hne
    have heq : f ⁻¹' P.cells i ∩ f ⁻¹' P.cells j = f ⁻¹' (P.cells i ∩ P.cells j) :=
      (Set.preimage_inter).symm
    have hpre : μ (f ⁻¹' (P.cells i ∩ P.cells j)) = μ (P.cells i ∩ P.cells j) :=
      hf.measure_preimage ((P.measurable i).inter (P.measurable j)).nullMeasurableSet
    have hdisj : μ (P.cells i ∩ P.cells j) = 0 := P.aedisjoint hne
    show μ (f ⁻¹' P.cells i ∩ f ⁻¹' P.cells j) = 0
    rw [heq, hpre, hdisj]
  ae_cover := by
    have hpre : (⋃ i, f ⁻¹' P.cells i)ᶜ = f ⁻¹' (⋃ i, P.cells i)ᶜ := by
      rw [← Set.preimage_iUnion, ← Set.preimage_compl]
    rw [hpre, hf.measure_preimage (MeasurableSet.iUnion P.measurable).compl.nullMeasurableSet,
      P.ae_cover]

@[simp]
lemma CountablePartition.comap_cells {μ : Measure α} {f : α → α} (hf : MeasurePreserving f μ μ)
    (P : CountablePartition μ ι) (i : ι) : (P.comap hf).cells i = f ⁻¹' P.cells i := rfl

omit [Countable ι] [Countable κ] in
/-- **Pullback-invariance of entropy.** The entropy of the pullback `f⁻¹ P` along a measure-
preserving map equals the entropy of `P`, because each pullback cell has the same `μ`-measure as the
original cell (`μ (f⁻¹ Aᵢ) = μ Aᵢ`). This is the invariance that makes the Kolmogorov–Sinai Fekete
sequence `H(⋁ₖ T⁻ᵏ P)` subadditive (`H(⋁_{k<n+m}) ≤ H(⋁_{k<n}) + H(Tⁿ-pullback of ⋁_{k<m})`). -/
lemma entropy_comap {μ : Measure α} {f : α → α} (hf : MeasurePreserving f μ μ)
    (s : ι → Set α) (hs : ∀ i, MeasurableSet (s i)) :
    entropy μ (fun i => f ⁻¹' s i) = entropy μ s := by
  rw [entropy_def, entropy_def]
  refine tsum_congr fun i => ?_
  rw [hf.measure_preimage (hs i).nullMeasurableSet]

/-! ### Marginal identities (toward subadditivity) -/

/-- **Partial row-marginal bound.** For a countable measurable partition `Q` and a measurable set
`A`, the partial sum over any finite set of column indices `Sj` of the cell measures `μ (A ∩ Bⱼ)` is
at most `μ A`: the sets `A ∩ Bⱼ` are pairwise a.e.-disjoint subsets of `A`. (The full sum over all
`j` equals `μ A`; this is the truncated version used in the finite-restriction route to
subadditivity.) -/
lemma CountablePartition.sum_inter_le {μ : Measure α} (Q : CountablePartition μ κ) {A : Set α}
    (hA : MeasurableSet A) (Sj : Finset κ) :
    ∑ j ∈ Sj, μ (A ∩ Q.cells j) ≤ μ A := by
  rw [← measure_biUnion_finset₀ (s := Sj) (f := fun j => A ∩ Q.cells j)
    (fun i _ j _ hij =>
      AEDisjoint.mono (Q.aedisjoint hij) Set.inter_subset_right Set.inter_subset_right)
    (fun j _ => (hA.inter (Q.measurable j)).nullMeasurableSet)]
  exact measure_mono (Set.iUnion₂_subset fun j _ => Set.inter_subset_left)

/-- **Full row-marginal identity.** For a countable measurable partition `Q` of a probability space
and a measurable set `A`, the measure of `A` is the (countable) sum of the measures of its
intersections with the cells of `Q`: `μ A = ∑'ⱼ μ (A ∩ Bⱼ)`. The sets `A ∩ Bⱼ` cover `A` up to the
null complement of `⋃ Bⱼ`, are pairwise a.e.-disjoint, and are null-measurable. -/
lemma CountablePartition.measure_eq_tsum_inter {μ : Measure α} [IsProbabilityMeasure μ]
    (Q : CountablePartition μ κ) {A : Set α} (hA : MeasurableSet A) :
    μ A = ∑' j, μ (A ∩ Q.cells j) := by
  have hadd : μ (⋃ j, A ∩ Q.cells j) = ∑' j, μ (A ∩ Q.cells j) :=
    measure_iUnion₀
      (fun i j hij =>
        AEDisjoint.mono (Q.aedisjoint hij) Set.inter_subset_right Set.inter_subset_right)
      (fun j => (hA.inter (Q.measurable j)).nullMeasurableSet)
  rw [← hadd, ← Set.inter_iUnion]
  -- `A = A ∩ (⋃ⱼ Bⱼ)`, since the missing part `A ∩ (⋃ⱼ Bⱼ)ᶜ ⊆ (⋃ⱼ Bⱼ)ᶜ` is null.
  set U : Set α := ⋃ j, Q.cells j with hU
  refine le_antisymm ?_ (measure_mono Set.inter_subset_left)
  have hsub : A ⊆ (A ∩ U) ∪ Uᶜ := by
    intro x hx
    by_cases h : x ∈ U
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h
  calc μ A ≤ μ ((A ∩ U) ∪ Uᶜ) := measure_mono hsub
    _ ≤ μ (A ∩ U) + μ Uᶜ := measure_union_le _ _
    _ = μ (A ∩ U) := by rw [Q.ae_cover, add_zero]

/-! ### Subadditivity under joins (the node-2 boundary)

The key nontrivial property `H(P ⊔ Q) ≤ H(P) + H(Q)` is stated here but **left as the first task of
node 2** (its proof is genuinely larger than the rest of node 1). The honest route is the
**conditional-entropy chain rule**:

* `H(P ⊔ Q) = H(P) + ∑'ᵢ μ(Aᵢ) · H(Q | Aᵢ)` where `H(Q | Aᵢ) = ∑'ⱼ negMulLog(μ(Aᵢ∩Bⱼ)/μ(Aᵢ))` is
  the conditional entropy of `Q` given the cell `Aᵢ`. This is the per-row expansion via
  `Real.negMulLog_mul`: `negMulLog(μ(Aᵢ)·r) = r·negMulLog(μ Aᵢ) + μ(Aᵢ)·negMulLog(r)` with
  `r = μ(Aᵢ∩Bⱼ)/μ(Aᵢ)`, summed over `j` using the marginal identity `measure_eq_tsum_inter`
  (`∑'ⱼ μ(Aᵢ∩Bⱼ) = μ(Aᵢ)`, so `∑'ⱼ r = 1`).
* `∑'ᵢ μ(Aᵢ) · H(Q | Aᵢ) ≤ H(Q)` by **concavity of `negMulLog`** (`concaveOn_negMulLog`): the
  conditional distributions `j ↦ μ(Aᵢ∩Bⱼ)/μ(Aᵢ)` average (with weights `μ(Aᵢ)`) to the marginal
  `j ↦ μ(Bⱼ)`, and `negMulLog` is concave, so the weighted average of the conditional entropies is
  at most the entropy of the average distribution `= H(Q)`. This step needs a **Jensen inequality
  for `tsum`** (an infinite-index version of `ConcaveOn.le_map_sum`), which Mathlib does **not**
  currently have — building it (or the equivalent log-sum inequality for countable families) is the
  substance of node 2.

A finite-restriction / sup-of-finite-sums route does **not** work here: the partial Gibbs bound over
a product finset `Sᵢ × Sⱼ` carries a slack `(∑_{Sᵢ}μ Aᵢ)(∑_{Sⱼ}μ Bⱼ) − ∑ μ(Aᵢ∩Bⱼ)` that is only
zero in the full limit, so it cannot be discharged term-by-term against the fixed bound
`H(P) + H(Q)`. (It *does* work for `entropy_le_log_card`, which is a single Jensen, not a difference.)
-/

set_option linter.unusedVariables false in
/-- **Subadditivity of Shannon entropy under joins** (the node-2 headline). For two countable
measurable partitions `P` and `Q` of a probability space, `H(P ⊔ Q) ≤ H(P) + H(Q)`.

Stated here; proved in node 2 via the conditional-entropy chain rule plus a `tsum`-Jensen step (see
the module note above). This `sorry` is the **explicit boundary between node 1 and node 2**, not a
gap in a node-1 deliverable. -/
theorem entropy_join_le {μ : Measure α} [IsProbabilityMeasure μ] (P : CountablePartition μ ι)
    (Q : CountablePartition μ κ) :
    entropy μ (P.join Q).cells ≤ entropy μ P.cells + entropy μ Q.cells := by
  sorry -- BLOCKED: node 2. Needs conditional-entropy chain rule + Jensen-for-`tsum`
        -- (Mathlib lacks an infinite-index `ConcaveOn.le_map_sum`). See module note above.

end Frontier.SMB
