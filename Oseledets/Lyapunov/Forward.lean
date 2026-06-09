import Oseledets.Lyapunov.OseledetsLimit
import Oseledets.Lyapunov.Filtration
import Oseledets.Lyapunov.Measurable

/-!
# Forward exact growth and the measurable Oseledets filtration (L10–L13)

This module assembles the endgame of the one-sided Oseledets MET, connecting the analytic
core (the Oseledets limit `Λ = lim ((A⁽ⁿ⁾)ᵀA⁽ⁿ⁾)^{1/2n}` of `OseledetsLimit.lean`, its
band-projector convergence, and the limsup flag of `Filtration.lean`) to the target
`oseledets_filtration`.

The mathematical content of this module is the **per-vector exact growth limit**
`(1/n) log‖A⁽ⁿ⁾(x) v‖ → λᵢ` for `v` in the stratum `Vᵢ \ Vᵢ₊₁`:

* **Lower bound** `liminf ≥ λᵢ` — clean: the Gram quadratic-form band bound
  `⟪gramₙ v, v⟫ ≥ c^{2n} ‖Pᶜₙ v‖²` (`inner_cfc_ge_band`), the band-projector convergence
  `Pᶜₙ v → Pᶜ_∞ v ≠ 0`, and taking the threshold `c ↑ e^{λᵢ}`.
* **Upper bound** `limsup ≤ λᵢ` — the crux: an Abel summation over nested band projectors,
  each band's leakage `‖Pᶜₘₙ v‖` decaying at its straddling-gap rate (the band-projector
  *tail rate* lemma), paired against the block's singular-value growth.

Together they upgrade the limsup flag's `lambdaBar = λᵢ` (`lambdaBar_eq_on_stratum`) to a genuine
limit, identify the Λ-spectral filtration with `lambdaSublevel` a.e. (so it inherits strict
antitonicity and `A`-equivariance), and—with the deterministic exponents from
`exists_lam_tendsto_singularValue` and the CFC measurability of `Measurable.lean`—discharge the
target.
-/

open MeasureTheory Filter Topology
open scoped Matrix Matrix.Norms.L2Operator

namespace Oseledets

variable {d : ℕ}

/-! ## Distinct descending exponent enumeration

The deterministic singular-value exponents `lam : ℕ → ℝ` (from `exists_lam_tendsto_singularValue`)
are antitone on `[0, d)`; their distinct values, enumerated **descending**, are the `k` Lyapunov
exponents `λ₀ > ⋯ > λ_{k-1}` handed to the target. This mirrors `Filtration.specList`. -/

/-- The finite set of distinct exponent values on `[0, d)`. -/
noncomputable def distinctExp (lam : ℕ → ℝ) (d : ℕ) : Finset ℝ := (Finset.range d).image lam

/-- The number of distinct exponents. -/
noncomputable def numExp (lam : ℕ → ℝ) (d : ℕ) : ℕ := (distinctExp lam d).card

/-- The descending enumeration of the distinct exponents (index `0` = largest). -/
noncomputable def expEnum (lam : ℕ → ℝ) (d : ℕ) : Fin (numExp lam d) → ℝ :=
  fun i => (distinctExp lam d).orderEmbOfFin rfl i.rev

theorem expEnum_strictAnti (lam : ℕ → ℝ) (d : ℕ) : StrictAnti (expEnum lam d) :=
  fun _ _ hij => (distinctExp lam d).orderEmbOfFin rfl |>.strictMono (Fin.rev_lt_rev.mpr hij)

theorem expEnum_mem (lam : ℕ → ℝ) (d : ℕ) (i : Fin (numExp lam d)) :
    expEnum lam d i ∈ distinctExp lam d :=
  (distinctExp lam d).orderEmbOfFin_mem rfl i.rev

/-- Membership: `r` is an enumerated value iff `r = lam j` for some `j < d`. -/
theorem mem_distinctExp (lam : ℕ → ℝ) (d : ℕ) {r : ℝ} :
    r ∈ distinctExp lam d ↔ ∃ j : ℕ, j < d ∧ lam j = r := by
  rw [distinctExp, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hjr⟩; exact ⟨j, Finset.mem_range.mp hj, hjr⟩
  · rintro ⟨j, hj, hjr⟩; exact ⟨j, Finset.mem_range.mpr hj, hjr⟩

/-- Every exponent `lam j` (`j < d`) is one of the enumerated distinct values. -/
theorem exists_expEnum_eq (lam : ℕ → ℝ) {d : ℕ} {j : ℕ} (hj : j < d) :
    ∃ i : Fin (numExp lam d), expEnum lam d i = lam j := by
  have hr : lam j ∈ distinctExp lam d := (mem_distinctExp lam d).mpr ⟨j, hj, rfl⟩
  have hrange : lam j ∈ Set.range ⇑((distinctExp lam d).orderEmbOfFin (rfl : _ = numExp lam d)) := by
    rw [Finset.range_orderEmbOfFin]; exact hr
  obtain ⟨k, hk⟩ := hrange
  exact ⟨k.rev, by simpa [expEnum] using hk⟩

/-- Every enumerated value is realized by some `lam j`. -/
theorem expEnum_eq_lam (lam : ℕ → ℝ) (d : ℕ) (i : Fin (numExp lam d)) :
    ∃ j : ℕ, j < d ∧ expEnum lam d i = lam j := by
  obtain ⟨j, hj, hjr⟩ := (mem_distinctExp lam d).mp (expEnum_mem lam d i)
  exact ⟨j, hj, hjr.symm⟩

theorem numExp_pos (lam : ℕ → ℝ) {d : ℕ} (hd : 0 < d) : 0 < numExp lam d := by
  rw [numExp, Finset.card_pos]; exact ⟨lam 0, (mem_distinctExp lam d).mpr ⟨0, hd, rfl⟩⟩

theorem numExp_le (lam : ℕ → ℝ) (d : ℕ) : numExp lam d ≤ d := by
  rw [numExp, distinctExp]
  calc ((Finset.range d).image lam).card ≤ (Finset.range d).card := Finset.card_image_le
    _ = d := Finset.card_range d

/-! ## The Gram quadratic-form band bound (lower-bound foundation)

For a self-adjoint `Q` and a `0/1` band indicator `χ = 𝟙_{(c,∞)}`, a continuous shape `f ≥ 0` with
`f ≥ a` above `c` controls the band projection: `a · ‖(cfc χ Q) v‖² ≤ ⟪(cfc f Q) v, v⟫`. Applied
with `Q = qpow`, `f = (·)^{2n}` (so `cfc f Q = gram`) and `a = c^{2n}` it gives the per-vector
lower bound `c^{2n} ‖Pᶜₙ v‖² ≤ ‖A⁽ⁿ⁾ v‖²`. -/

section QuadForm
open scoped InnerProductSpace
open ComplexOrder

/-- The norm identity `‖toEuclideanLin M v‖² = ⟪toEuclideanLin (Mᵀ * M) v, v⟫` (generic real
matrix; the cocycle specialization is `norm_sq_cocycle_apply_eq_inner_gram`). -/
theorem norm_sq_toEuclideanLin_eq_inner_gram
    (M : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    ‖Matrix.toEuclideanLin M v‖ ^ 2 = ⟪Matrix.toEuclideanLin (Mᵀ * M) v, v⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq]
  have hadj : ⟪Matrix.toEuclideanLin M v, Matrix.toEuclideanLin M v⟫_ℝ
      = ⟪((Matrix.toEuclideanLin M).adjoint ∘ₗ (Matrix.toEuclideanLin M)) v, v⟫_ℝ := by
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  rw [hadj]
  congr 1
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  simp only [LinearMap.comp_apply, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]

/-- **Gram quadratic-form band bound.** For self-adjoint `Q`, a `0/1` band indicator
`χ = 𝟙_{(c,∞)}`, and a continuous `f ≥ 0` on the spectrum with `a ≤ f t` whenever `c < t`:
`a · ‖(cfc χ Q) v‖² ≤ ⟪(cfc f Q) v, v⟫`. The band projector is a self-adjoint idempotent
(`‖Pv‖² = ⟪Pv,v⟫`); the gap `cfc (f − a·χ) Q` is `PosSemidef` since `f − a·χ ≥ 0` on the
spectrum. -/
theorem inner_cfc_ge_band [NeZero d]
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsSelfAdjoint Q)
    (c a : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (_root_.spectrum ℝ Q))
    (hfnn : ∀ t ∈ _root_.spectrum ℝ Q, 0 ≤ f t)
    (hfband : ∀ t ∈ _root_.spectrum ℝ Q, c < t → a ≤ f t)
    (v : EuclideanSpace ℝ (Fin d)) :
    a * ‖Matrix.toEuclideanLin (cfc (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ)) Q) v‖ ^ 2
      ≤ inner ℝ (Matrix.toEuclideanLin (cfc f Q) v) v := by
  classical
  set χ : ℝ → ℝ := Set.indicator (Set.Ioi c) (1 : ℝ → ℝ) with hχ
  have hspecfin : (_root_.spectrum ℝ Q).Finite := Matrix.finite_real_spectrum (A := Q)
  have hcontχ : ContinuousOn χ (_root_.spectrum ℝ Q) := hspecfin.continuousOn _
  have hPsa : IsSelfAdjoint (cfc χ Q) := cfc_predicate χ Q
  have hPherm : (cfc χ Q).IsHermitian := Matrix.isHermitian_iff_isSelfAdjoint.mpr hPsa
  have hidem : (_root_.spectrum ℝ Q).EqOn (fun t => χ t * χ t) χ := by
    intro t _
    by_cases ht : t ∈ Set.Ioi c
    · simp [hχ, Set.indicator_of_mem ht]
    · simp [hχ, Set.indicator_of_notMem ht]
  have hPidem : cfc χ Q * cfc χ Q = cfc χ Q := by
    rw [← cfc_mul χ χ Q hcontχ hcontχ, cfc_congr hidem]
  have hPtranspose : (cfc χ Q)ᵀ = cfc χ Q := by
    have h := hPherm
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hstep1 : ‖Matrix.toEuclideanLin (cfc χ Q) v‖ ^ 2
      = ⟪Matrix.toEuclideanLin (cfc χ Q) v, v⟫_ℝ := by
    rw [norm_sq_toEuclideanLin_eq_inner_gram, hPtranspose, hPidem]
  set g : ℝ → ℝ := fun t => f t - a * χ t with hg
  have hgnn : ∀ t ∈ _root_.spectrum ℝ Q, 0 ≤ g t := by
    intro t ht
    by_cases hc : c < t
    · have h1 : χ t = 1 := by simp [hχ, Set.indicator_of_mem (Set.mem_Ioi.mpr hc)]
      rw [hg]; simp only [h1, mul_one]; linarith [hfband t ht hc]
    · have h0 : χ t = 0 := by
        rw [hχ, Set.indicator_of_notMem]; rw [Set.mem_Ioi]; exact hc
      rw [hg]; simp only [h0, mul_zero, sub_zero]; exact hfnn t ht
  have hgsplit : cfc g Q = cfc f Q - a • cfc χ Q := by
    have hca : ContinuousOn (fun t => a * χ t) (_root_.spectrum ℝ Q) := (continuousOn_const).mul hcontχ
    rw [hg, cfc_sub f (fun t => a * χ t) Q hf hca, cfc_const_mul a χ Q hcontχ]
  have hgcont : ContinuousOn g (_root_.spectrum ℝ Q) := hf.sub ((continuousOn_const).mul hcontχ)
  have hgsa : IsSelfAdjoint (cfc g Q) := cfc_predicate g Q
  have hgherm : (cfc g Q).IsHermitian := Matrix.isHermitian_iff_isSelfAdjoint.mpr hgsa
  have hgPSD : (cfc g Q).PosSemidef := by
    rw [Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg]
    refine ⟨hgherm, ?_⟩
    rw [cfc_map_spectrum g Q hQ hgcont]
    rintro _ ⟨t, ht, rfl⟩
    exact hgnn t ht
  have hinner_dot : ⟪Matrix.toEuclideanLin (cfc g Q) v, v⟫_ℝ
      = star (v : Fin d → ℝ) ⬝ᵥ ((cfc g Q) *ᵥ (v : Fin d → ℝ)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply]
    simp only [star_trivial]
  have hPSDnn : (0 : ℝ) ≤ ⟪Matrix.toEuclideanLin (cfc g Q) v, v⟫_ℝ := by
    rw [hinner_dot]; exact hgPSD.dotProduct_mulVec_nonneg _
  have hsplit_inner : ⟪Matrix.toEuclideanLin (cfc g Q) v, v⟫_ℝ
      = ⟪Matrix.toEuclideanLin (cfc f Q) v, v⟫_ℝ
        - a * ⟪Matrix.toEuclideanLin (cfc χ Q) v, v⟫_ℝ := by
    rw [hgsplit, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      inner_sub_left, real_inner_smul_left]
  rw [show inner ℝ (Matrix.toEuclideanLin (cfc f Q) v) v
      = ⟪Matrix.toEuclideanLin (cfc f Q) v, v⟫_ℝ from rfl, hstep1]
  have hfin : (0 : ℝ) ≤ ⟪Matrix.toEuclideanLin (cfc f Q) v, v⟫_ℝ
      - a * ⟪Matrix.toEuclideanLin (cfc χ Q) v, v⟫_ℝ := by
    rw [← hsplit_inner]; exact hPSDnn
  linarith

end QuadForm

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

end Oseledets
