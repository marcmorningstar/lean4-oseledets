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

/-! ### Countable Jensen for `negMulLog` (the analytic core of subadditivity)

Subadditivity `H(P ⊔ Q) ≤ H(P) + H(Q)` is the conditional-entropy chain rule
`H(P ⊔ Q) = H(P) + ∑'ᵢ μ(Aᵢ)·H(Q|Aᵢ)` together with `∑'ᵢ μ(Aᵢ)·H(Q|Aᵢ) ≤ H(Q)`, which is a
**Jensen inequality for the concave `negMulLog` over a countable convex combination**. Mathlib has
only the *finite* Jensen `ConcaveOn.le_map_sum`; the countable version below is proved directly from
the supporting-line (tangent) bound `negMulLog p ≤ negMulLog q + (-log q - 1)(p - q)`, summed against
the weights — the linear term cancels because the weights sum to `1` and the points average to `q`.
This avoids any convexity-via-limit machinery. -/

/-- **Supporting-line (tangent) bound** for the concave `negMulLog` at a point `q > 0`:
`negMulLog p ≤ negMulLog q + (-log q - 1)·(p - q)` for every `p ≥ 0`. Proved directly from
`Real.log_le_sub_one_of_pos` (`log t ≤ t - 1`), no convexity API. -/
lemma negMulLog_le_tangent {q : ℝ} (hq : 0 < q) {p : ℝ} (hp : 0 ≤ p) :
    Real.negMulLog p ≤ Real.negMulLog q + (-Real.log q - 1) * (p - q) := by
  rcases eq_or_lt_of_le hp with rfl | hp'
  · simp only [Real.negMulLog_zero]
    have h : Real.negMulLog q + (-Real.log q - 1) * (0 - q) = q := by
      simp only [Real.negMulLog]; ring
    rw [h]; exact le_of_lt hq
  · have hlog : Real.log (q / p) ≤ q / p - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (ne_of_gt hq) (ne_of_gt hp')] at hlog
    have hmul : p * (Real.log q - Real.log p) ≤ p * (q / p - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hp')
    have hpdiv : p * (q / p - 1) = q - p := by field_simp
    rw [hpdiv] at hmul
    simp only [Real.negMulLog]
    nlinarith [hmul]

/-- **Countable Jensen / log-sum inequality for `negMulLog`.** For a probability weight vector
`w` (`w i ≥ 0`, `∑' w = 1`) and points `p i ∈ [0,1]`, the weighted average of `negMulLog (p i)` is at
most `negMulLog` of the weighted average `q = ∑' wᵢ pᵢ`. This is concave Jensen for a (possibly)
countably-infinite convex combination, the analytic core of entropy subadditivity. The proof sums
the supporting-line bound `negMulLog_le_tangent` against `w`: the linear term cancels since
`∑' w = 1` and `∑' w·p = q`. (No `[Countable ι]` is needed — summability comes from the hypotheses.) -/
lemma negMulLog_tsum_le {ι : Type*} (w p : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hwsum : ∑' i, w i = 1) :
    (∑' i, w i * Real.negMulLog (p i)) ≤ Real.negMulLog (∑' i, w i * p i) := by
  -- `w` is summable: otherwise `∑' w = 0 ≠ 1`.
  have hsw : Summable w := by
    by_contra h
    rw [tsum_eq_zero_of_not_summable h] at hwsum
    exact one_ne_zero hwsum.symm
  -- `w·p` summable, by comparison `0 ≤ w·p ≤ w`.
  have hswp : Summable (fun i => w i * p i) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hw i) (hp0 i))
      (fun i => by nlinarith [hw i, hp0 i, hp1 i]) hsw
  -- `w·negMulLog p` summable, by comparison `0 ≤ w·negMulLog p ≤ w` (negMulLog p ≤ 1 - p ≤ 1).
  have hsnml : Summable (fun i => w i * Real.negMulLog (p i)) :=
    Summable.of_nonneg_of_le
      (fun i => mul_nonneg (hw i) (Real.negMulLog_nonneg (hp0 i) (hp1 i)))
      (fun i => by
        have h1 : Real.negMulLog (p i) ≤ 1 - p i := Real.negMulLog_le_one_sub_self (hp0 i)
        nlinarith [hw i, hp0 i, hp1 i, h1])
      hsw
  set q : ℝ := ∑' i, w i * p i with hq_def
  have hq0 : 0 ≤ q := tsum_nonneg (fun i => mul_nonneg (hw i) (hp0 i))
  rcases eq_or_lt_of_le hq0 with hq_eq | hq_pos
  · -- `q = 0`: every `w i · p i = 0`, so every `w i · negMulLog (p i) = 0`; LHS = 0 = negMulLog 0.
    rw [← hq_eq, Real.negMulLog_zero]
    have hterms : ∀ i, w i * p i = 0 := by
      intro i
      refine le_antisymm ?_ (mul_nonneg (hw i) (hp0 i))
      have hle : w i * p i ≤ q := by
        rw [hq_def]; exact hswp.le_tsum i (fun j _ => mul_nonneg (hw j) (hp0 j))
      rwa [← hq_eq] at hle
    have hzero : ∀ i, w i * Real.negMulLog (p i) = 0 := by
      intro i
      rcases mul_eq_zero.mp (hterms i) with hwi | hpi
      · rw [hwi, zero_mul]
      · rw [hpi, Real.negMulLog_zero, mul_zero]
    rw [tsum_congr hzero, tsum_zero]
  · -- `q > 0`: supporting-line bound summed against `w`.
    have htangent : ∀ i, w i * Real.negMulLog (p i)
        ≤ w i * (Real.negMulLog q + (-Real.log q - 1) * (p i - q)) :=
      fun i => mul_le_mul_of_nonneg_left (negMulLog_le_tangent hq_pos (hp0 i)) (hw i)
    -- The supporting-line family as a linear combination of the summable `w` and `w·p`.
    have hrw : (fun i => w i * (Real.negMulLog q + (-Real.log q - 1) * (p i - q)))
        = (fun i => Real.negMulLog q * w i
            + ((-Real.log q - 1) * (w i * p i) - (-Real.log q - 1) * q * w i)) := by
      funext i; ring
    have hsRHS : Summable (fun i => w i * (Real.negMulLog q + (-Real.log q - 1) * (p i - q))) := by
      rw [hrw]; exact (hsw.mul_left _).add ((hswp.mul_left _).sub (hsw.mul_left _))
    calc ∑' i, w i * Real.negMulLog (p i)
        ≤ ∑' i, w i * (Real.negMulLog q + (-Real.log q - 1) * (p i - q)) :=
          hsnml.tsum_le_tsum htangent hsRHS
      _ = Real.negMulLog q := by
          rw [hrw,
            (hsw.mul_left _).tsum_add ((hswp.mul_left _).sub (hsw.mul_left _)),
            (hswp.mul_left _).tsum_sub (hsw.mul_left _),
            hsw.tsum_mul_left (Real.negMulLog q),
            hswp.tsum_mul_left (-Real.log q - 1),
            hsw.tsum_mul_left ((-Real.log q - 1) * q), hwsum, ← hq_def]
          ring

/-! ### Subadditivity under joins

`H(P ⊔ Q) ≤ H(P) + H(Q)`. The whole argument lives in `ℝ≥0∞` (no finiteness assumption on the
entropies). Writing `aᵢ = (μ Aᵢ).toReal`, `bⱼ = (μ Bⱼ).toReal`, `cᵢⱼ = (μ (Aᵢ ∩ Bⱼ)).toReal` and
the conditional density `rᵢⱼ = cᵢⱼ / aᵢ` (with `aᵢ · rᵢⱼ = cᵢⱼ` even when `aᵢ = 0`, since then
`cᵢⱼ = 0`), the per-cell chain rule `Real.negMulLog_mul` gives
`negMulLog cᵢⱼ = rᵢⱼ·negMulLog aᵢ + aᵢ·negMulLog rᵢⱼ`, so
`H(P ⊔ Q) = ∑'ᵢⱼ ofReal(rᵢⱼ·negMulLog aᵢ) + ∑'ᵢⱼ ofReal(aᵢ·negMulLog rᵢⱼ)`. The first double sum
is `H(P)` (each row sums to `negMulLog aᵢ` because `∑'ⱼ rᵢⱼ = 1`); the second is bounded by `H(Q)`
column-by-column through `negMulLog_tsum_le` (weights `aᵢ`, points `rᵢⱼ`, average `bⱼ`). -/

/-- **Subadditivity of Shannon entropy under joins.** For two countable measurable partitions `P`
and `Q` of a probability space, `H(P ⊔ Q) ≤ H(P) + H(Q)`. Proved via the conditional-entropy chain
rule (`Real.negMulLog_mul`) and the countable Jensen inequality `negMulLog_tsum_le`. -/
theorem entropy_join_le {μ : Measure α} [IsProbabilityMeasure μ] (P : CountablePartition μ ι)
    (Q : CountablePartition μ κ) :
    entropy μ (P.join Q).cells ≤ entropy μ P.cells + entropy μ Q.cells := by
  classical
  -- Abbreviations for the cell measures (as reals) and the conditional densities.
  set a : ι → ℝ := fun i => (μ (P.cells i)).toReal with ha_def
  set b : κ → ℝ := fun j => (μ (Q.cells j)).toReal with hb_def
  set c : ι → κ → ℝ := fun i j => (μ (P.cells i ∩ Q.cells j)).toReal with hc_def
  set r : ι → κ → ℝ := fun i j => c i j / a i with hr_def
  -- Basic bounds.
  have ha_nonneg : ∀ i, 0 ≤ a i := fun i => ENNReal.toReal_nonneg
  have ha_le_one : ∀ i, a i ≤ 1 := fun i => by
    have h : (μ (P.cells i)).toReal ≤ (1 : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := P.cells i))
    rwa [ENNReal.toReal_one] at h
  have hb_nonneg : ∀ j, 0 ≤ b j := fun j => ENNReal.toReal_nonneg
  have hc_nonneg : ∀ i j, 0 ≤ c i j := fun i j => ENNReal.toReal_nonneg
  -- `cᵢⱼ ≤ aᵢ`, since `Aᵢ ∩ Bⱼ ⊆ Aᵢ`.
  have hc_le_a : ∀ i j, c i j ≤ a i := fun i j =>
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono Set.inter_subset_left)
  -- The key identity `aᵢ · rᵢⱼ = cᵢⱼ`, valid even at `aᵢ = 0` (then `cᵢⱼ = 0`).
  have har : ∀ i j, a i * r i j = c i j := by
    intro i j
    rcases eq_or_lt_of_le (ha_nonneg i) with hai | hai
    · have hcij : c i j = 0 := le_antisymm (hai ▸ hc_le_a i j) (hc_nonneg i j)
      simp only [hr_def, ← hai, zero_mul, hcij]
    · simp only [hr_def]
      rw [mul_div_cancel₀ _ (ne_of_gt hai)]
  have hr_nonneg : ∀ i j, 0 ≤ r i j := fun i j => div_nonneg (hc_nonneg i j) (ha_nonneg i)
  have hr_le_one : ∀ i j, r i j ≤ 1 := by
    intro i j
    rcases eq_or_lt_of_le (ha_nonneg i) with hai | hai
    · simp only [hr_def, ← hai, div_zero]; exact zero_le_one
    · rw [hr_def, div_le_one hai]; exact hc_le_a i j
  -- Row marginal: `∑'ⱼ cᵢⱼ = aᵢ`, from `measure_eq_tsum_inter`.
  have hrow : ∀ i, ∑' j, c i j = a i := by
    intro i
    have hmeas : μ (P.cells i) = ∑' j, μ (P.cells i ∩ Q.cells j) :=
      Q.measure_eq_tsum_inter (P.measurable i)
    have hne : ∀ j, μ (P.cells i ∩ Q.cells j) ≠ ∞ := fun j => measure_ne_top μ _
    calc ∑' j, c i j = ∑' j, (μ (P.cells i ∩ Q.cells j)).toReal := rfl
      _ = (∑' j, μ (P.cells i ∩ Q.cells j)).toReal := (ENNReal.tsum_toReal_eq hne).symm
      _ = (μ (P.cells i)).toReal := by rw [← hmeas]
      _ = a i := rfl
  -- Column marginal: `∑'ᵢ cᵢⱼ = bⱼ`.
  have hcol : ∀ j, ∑' i, c i j = b j := by
    intro j
    have hmeas : μ (Q.cells j) = ∑' i, μ (Q.cells j ∩ P.cells i) :=
      P.measure_eq_tsum_inter (Q.measurable j)
    have hne : ∀ i, μ (Q.cells j ∩ P.cells i) ≠ ∞ := fun i => measure_ne_top μ _
    have hcomm : ∀ i, μ (Q.cells j ∩ P.cells i) = μ (P.cells i ∩ Q.cells j) := fun i => by
      rw [Set.inter_comm]
    calc ∑' i, c i j = ∑' i, (μ (P.cells i ∩ Q.cells j)).toReal := rfl
      _ = ∑' i, (μ (Q.cells j ∩ P.cells i)).toReal := by simp_rw [hcomm]
      _ = (∑' i, μ (Q.cells j ∩ P.cells i)).toReal := (ENNReal.tsum_toReal_eq hne).symm
      _ = (μ (Q.cells j)).toReal := by rw [← hmeas]
      _ = b j := rfl
  -- Weights `a` sum to `1`.
  have hsum_a : ∑' i, a i = 1 := by
    have h := P.tsum_measure_eq_one
    have hne : ∀ i, μ (P.cells i) ≠ ∞ := fun i => measure_ne_top μ _
    calc ∑' i, a i = ∑' i, (μ (P.cells i)).toReal := rfl
      _ = (∑' i, μ (P.cells i)).toReal := (ENNReal.tsum_toReal_eq hne).symm
      _ = (1 : ℝ≥0∞).toReal := by rw [h]
      _ = 1 := ENNReal.toReal_one
  -- `c i ·` summable (its `ℝ≥0∞`-tsum is `μ Aᵢ ≠ ⊤`), hence `r i ·` summable.
  have hcsum : ∀ i, Summable (fun j => c i j) := by
    intro i
    have hfin : ∑' j, μ (P.cells i ∩ Q.cells j) ≠ ∞ := by
      rw [← Q.measure_eq_tsum_inter (P.measurable i)]; exact measure_ne_top μ _
    exact ENNReal.summable_toReal hfin
  have hsr : ∀ i, Summable (fun j => r i j) := fun i => (hcsum i).div_const (a i)
  -- Each summand is nonnegative, so the `ℝ≥0∞` rewrites are clean.
  -- === The chain-rule decomposition of the join entropy ===
  -- `H(P ⊔ Q) = ∑'ᵢⱼ ofReal(negMulLog cᵢⱼ)`.
  have hjoin_eq : entropy μ (P.join Q).cells
      = ∑' p : ι × κ, ENNReal.ofReal (Real.negMulLog (c p.1 p.2)) := by
    rw [entropy_def]
    refine tsum_congr fun p => ?_
    simp only [CountablePartition.join_cells, joinCells_apply, hc_def]
  -- Per-cell chain rule in `ℝ≥0∞`.
  have hchain : ∀ i j, ENNReal.ofReal (Real.negMulLog (c i j))
      = ENNReal.ofReal (r i j * Real.negMulLog (a i))
        + ENNReal.ofReal (a i * Real.negMulLog (r i j)) := by
    intro i j
    have hmul : Real.negMulLog (c i j)
        = r i j * Real.negMulLog (a i) + a i * Real.negMulLog (r i j) := by
      rw [← har i j, Real.negMulLog_mul]
    rw [hmul, ENNReal.ofReal_add]
    · exact mul_nonneg (hr_nonneg i j) (Real.negMulLog_nonneg (ha_nonneg i) (ha_le_one i))
    · exact mul_nonneg (ha_nonneg i) (Real.negMulLog_nonneg (hr_nonneg i j) (hr_le_one i j))
  -- `a` is summable (`∑' a = 1`).
  have hsa : Summable a := by
    by_contra h
    rw [tsum_eq_zero_of_not_summable h] at hsum_a
    exact one_ne_zero hsum_a.symm
  -- === Term `T1`: the first double sum reconstructs `H(P)`. ===
  -- For each row `i`, `∑'ⱼ ofReal(rᵢⱼ·negMulLog aᵢ) = ofReal(negMulLog aᵢ)` (since `∑'ⱼ rᵢⱼ = 1`).
  have hT1row : ∀ i, (∑' j, ENNReal.ofReal (r i j * Real.negMulLog (a i)))
      = ENNReal.ofReal (Real.negMulLog (a i)) := by
    intro i
    rcases eq_or_lt_of_le (ha_nonneg i) with hai | hai
    · -- `aᵢ = 0`: both sides are `0`.
      have hnml0 : Real.negMulLog (a i) = 0 := by rw [← hai, Real.negMulLog_zero]
      simp only [hnml0, mul_zero, ENNReal.ofReal_zero, tsum_zero]
    · -- `aᵢ > 0`: factor out the constant and use `∑'ⱼ rᵢⱼ = 1`.
      have hrsum : ∑' j, r i j = 1 := by
        have hrmul : ∀ j, r i j = c i j * (a i)⁻¹ := fun j => by
          simp only [hr_def, div_eq_mul_inv]
        rw [tsum_congr hrmul, (hcsum i).tsum_mul_right, hrow i, mul_inv_cancel₀ (ne_of_gt hai)]
      calc (∑' j, ENNReal.ofReal (r i j * Real.negMulLog (a i)))
          = ∑' j, ENNReal.ofReal (r i j) * ENNReal.ofReal (Real.negMulLog (a i)) := by
            refine tsum_congr fun j => ?_
            rw [ENNReal.ofReal_mul (hr_nonneg i j)]
        _ = (∑' j, ENNReal.ofReal (r i j)) * ENNReal.ofReal (Real.negMulLog (a i)) :=
            ENNReal.tsum_mul_right
        _ = ENNReal.ofReal (∑' j, r i j) * ENNReal.ofReal (Real.negMulLog (a i)) := by
            rw [ENNReal.ofReal_tsum_of_nonneg (fun j => hr_nonneg i j) (hsr i)]
        _ = ENNReal.ofReal (Real.negMulLog (a i)) := by
            rw [hrsum, ENNReal.ofReal_one, one_mul]
  -- === Term `T2`: the second double sum is bounded by `H(Q)` column-by-column. ===
  -- For each column `j`, `∑'ᵢ ofReal(aᵢ·negMulLog rᵢⱼ) ≤ ofReal(negMulLog bⱼ)` (countable Jensen).
  have hT2col : ∀ j, (∑' i, ENNReal.ofReal (a i * Real.negMulLog (r i j)))
      ≤ ENNReal.ofReal (Real.negMulLog (b j)) := by
    intro j
    -- Summability of `i ↦ aᵢ·negMulLog rᵢⱼ` by comparison `0 ≤ · ≤ aᵢ`.
    have hsum_col : Summable (fun i => a i * Real.negMulLog (r i j)) :=
      Summable.of_nonneg_of_le
        (fun i => mul_nonneg (ha_nonneg i) (Real.negMulLog_nonneg (hr_nonneg i j) (hr_le_one i j)))
        (fun i => by
          have h1 : Real.negMulLog (r i j) ≤ 1 - r i j := Real.negMulLog_le_one_sub_self (hr_nonneg i j)
          nlinarith [ha_nonneg i, hr_nonneg i j, hr_le_one i j, h1])
        hsa
    -- The average `∑'ᵢ aᵢ·rᵢⱼ = ∑'ᵢ cᵢⱼ = bⱼ`.
    have havg : ∑' i, a i * r i j = b j := by
      rw [tsum_congr (fun i => har i j), hcol j]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun i => mul_nonneg (ha_nonneg i) (Real.negMulLog_nonneg (hr_nonneg i j) (hr_le_one i j)))
      hsum_col]
    refine ENNReal.ofReal_le_ofReal ?_
    have hjensen := negMulLog_tsum_le a (fun i => r i j) ha_nonneg
      (fun i => hr_nonneg i j) (fun i => hr_le_one i j) hsum_a
    rwa [havg] at hjensen
  -- The first double sum reconstructs `H(P)` (sum the per-row identity over `i`).
  have hT1 : (∑' p : ι × κ, ENNReal.ofReal (r p.1 p.2 * Real.negMulLog (a p.1)))
      = entropy μ P.cells := by
    rw [ENNReal.tsum_prod (f := fun i j => ENNReal.ofReal (r i j * Real.negMulLog (a i))),
      entropy_def]
    exact tsum_congr hT1row
  -- The second double sum is bounded by `H(Q)` (sum the per-column bound over `j`).
  have hT2 : (∑' p : ι × κ, ENNReal.ofReal (a p.1 * Real.negMulLog (r p.1 p.2)))
      ≤ entropy μ Q.cells := by
    rw [ENNReal.tsum_prod (f := fun i j => ENNReal.ofReal (a i * Real.negMulLog (r i j))),
      ENNReal.tsum_comm, entropy_def]
    exact ENNReal.tsum_le_tsum hT2col
  -- === Assemble. ===
  rw [hjoin_eq]
  calc (∑' p : ι × κ, ENNReal.ofReal (Real.negMulLog (c p.1 p.2)))
      = ∑' p : ι × κ, (ENNReal.ofReal (r p.1 p.2 * Real.negMulLog (a p.1))
          + ENNReal.ofReal (a p.1 * Real.negMulLog (r p.1 p.2))) :=
        tsum_congr fun p => hchain p.1 p.2
    _ = (∑' p : ι × κ, ENNReal.ofReal (r p.1 p.2 * Real.negMulLog (a p.1)))
          + ∑' p : ι × κ, ENNReal.ofReal (a p.1 * Real.negMulLog (r p.1 p.2)) :=
        ENNReal.tsum_add
    _ ≤ entropy μ P.cells + entropy μ Q.cells := by
        rw [hT1]; exact add_le_add le_rfl hT2

end Frontier.SMB
