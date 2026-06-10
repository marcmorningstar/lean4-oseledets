import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# M5 (reverse side of Ruelle's Lemma 1.4) — deterministic entry bound

`entry_reverse_bound_of_orthogonal`: for an orthogonal matrix `S` (here `S * Sᵀ = 1`)
whose entries obey the *graded forward* bound `|S a b| ≤ c · exp(-(max (g b - g a) 0))`,
every entry obeys the *reverse* bound at the full pairwise rate:

    |S i j| ≤ (d-1)! · c^(d-1) · exp(-(g i - g j)).

The argument is Ruelle's cofactor expansion: `S⁻¹ = Sᵀ`, entries of `S⁻¹` are
(`det S`)-scaled cofactors with `|det S| = 1`, and each surviving Leibniz term of the
cofactor minor pays exactly the level imbalance `g i - g j` by telescoping.
-/

open scoped BigOperators Matrix
open Equiv

noncomputable section

namespace Ruelle13

/-- A bare-handed Leibniz bound on `|det M|`: it is at most the number of permutations
`σ` with `nonzero ∏` times the worst per-permutation product bound.  Here we directly bound
`|det M| ≤ ∑_σ ∏_k |M (σ k) k|`. -/
lemma abs_det_le_sum_abs_prod {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    |M.det| ≤ ∑ σ : Equiv.Perm (Fin d), ∏ k, |M (σ k) k| := by
  rw [Matrix.det_apply']
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro σ _
  rw [abs_mul, ← Finset.abs_prod]
  have : |(((Equiv.Perm.sign σ : ℤ)) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  rw [this, one_mul]

/-- The number of permutations `σ` of `Fin d` with `σ j = i` is at most `(d-1)!`.
Injection into `Perm {x // x ≠ j}` via the swap that pulls `i` back to `j`. -/
lemma card_filter_apply_eq_le {d : ℕ} (i j : Fin d) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin d) => σ j = i)).card
      ≤ (d - 1).factorial := by
  classical
  -- `Fintype.card {x : Fin d // x ≠ j} = d - 1`.
  have hcard : Fintype.card {x : Fin d // x ≠ j} = d - 1 := by
    rw [Fintype.card_subtype_compl]
    simp
  -- Injection target: `Perm {x // x ≠ j}`.
  have hpres : ∀ (σ : Equiv.Perm (Fin d)), σ j = i →
      ∀ x, (Equiv.swap i j * σ) x ≠ j ↔ x ≠ j := by
    intro σ hσ x
    have hfix : (Equiv.swap i j * σ) j = j := by
      simp only [Equiv.Perm.mul_apply, hσ]
      exact Equiv.swap_apply_left i j
    constructor
    · intro hx hxj
      apply hx
      rw [hxj, hfix]
    · intro hx hxj
      apply hx
      exact (Equiv.injective _) (by rw [hxj, hfix])
  have htarget : (d - 1).factorial
      = (Finset.univ : Finset (Equiv.Perm {x : Fin d // x ≠ j})).card := by
    rw [Finset.card_univ, Fintype.card_perm, hcard]
  rw [htarget]
  apply Finset.card_le_card_of_injOn
    (f := fun σ => if h : σ j = i then (Equiv.swap i j * σ).subtypePerm (hpres σ h)
      else 1)
  · intro σ _; exact Finset.mem_univ _
  · intro σ hσ τ hτ hστ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hσ hτ
    simp only [dif_pos hσ, dif_pos hτ] at hστ
    -- Equal subtypePerms ⟹ swap*σ = swap*τ on `{x≠j}`; both fix j ⟹ equal everywhere.
    have key : ∀ x : Fin d, (Equiv.swap i j * σ) x = (Equiv.swap i j * τ) x := by
      intro x
      by_cases hx : x = j
      · subst hx
        simp only [Equiv.Perm.mul_apply, hσ, hτ, Equiv.swap_apply_left]
      · have := congrArg (fun p => (p ⟨x, hx⟩ : Fin d)) hστ
        simpa only [Equiv.Perm.subtypePerm_apply] using this
    have : Equiv.swap i j * σ = Equiv.swap i j * τ := Equiv.ext key
    exact mul_left_cancel this

/-- The telescoping level identity: for a permutation `σ` of `Fin d` with `σ j = i`,
`∑_{k ≠ j} (g k - g (σ k)) = g i - g j`. -/
lemma sum_level_telescope {d : ℕ} (g : Fin d → ℝ) (σ : Equiv.Perm (Fin d))
    (i j : Fin d) (hσ : σ j = i) :
    ∑ k ∈ Finset.univ.erase j, (g k - g (σ k)) = g i - g j := by
  classical
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ k ∈ Finset.univ.erase j, g k = (∑ k, g k) - g j := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
  have h2 : ∑ k ∈ Finset.univ.erase j, g (σ k) = (∑ k, g k) - g i := by
    have hreindex : ∑ k, g (σ k) = ∑ k, g k := Equiv.sum_comp σ g
    have hh : ∑ k ∈ Finset.univ.erase j, g (σ k)
        = (∑ k, g (σ k)) - g (σ j) := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
    rw [hh, hreindex, hσ]
  rw [h1, h2]; ring

/-- Per-permutation product bound.  For a permutation `σ` of `Fin d` with `σ j = i`, the product of
the `(d-1)` entry-magnitudes off the `j`-column, bounded by the graded forward bound, is at most
`c^(d-1) · exp(-(g i - g j))`. -/
lemma prod_entry_bound {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hfwd : ∀ a b : Fin d, |S a b| ≤ c * Real.exp (-(max (g b - g a) 0)))
    (σ : Equiv.Perm (Fin d)) (i j : Fin d) (hσ : σ j = i) :
    ∏ k ∈ Finset.univ.erase j, |S (σ k) k|
      ≤ c ^ (d - 1) * Real.exp (-(g i - g j)) := by
  classical
  have hcard : (Finset.univ.erase j).card = d - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  -- Step 1: termwise bound by the forward estimate.
  have hstep1 : ∏ k ∈ Finset.univ.erase j, |S (σ k) k|
      ≤ ∏ k ∈ Finset.univ.erase j, c * Real.exp (-(max (g k - g (σ k)) 0)) := by
    apply Finset.prod_le_prod
    · intro k _; exact abs_nonneg _
    · intro k _; exact hfwd (σ k) k
  -- Step 2: factor the product.
  have hstep2 : ∏ k ∈ Finset.univ.erase j, c * Real.exp (-(max (g k - g (σ k)) 0))
      = c ^ (d - 1) * Real.exp (-(∑ k ∈ Finset.univ.erase j, max (g k - g (σ k)) 0)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
    congr 1
    rw [← Real.exp_sum, ← Finset.sum_neg_distrib, Finset.sum_neg_distrib]
  -- Step 3: drop the `max` (each `max(x,0) ≥ x`, so `-∑max ≤ -∑x`).
  have hsum_ge : ∑ k ∈ Finset.univ.erase j, (g k - g (σ k))
      ≤ ∑ k ∈ Finset.univ.erase j, max (g k - g (σ k)) 0 :=
    Finset.sum_le_sum (fun k _ => le_max_left _ _)
  have hstep3 : Real.exp (-(∑ k ∈ Finset.univ.erase j, max (g k - g (σ k)) 0))
      ≤ Real.exp (-(g i - g j)) := by
    rw [Real.exp_le_exp]
    rw [← sum_level_telescope g σ i j hσ]
    linarith
  calc ∏ k ∈ Finset.univ.erase j, |S (σ k) k|
      ≤ ∏ k ∈ Finset.univ.erase j, c * Real.exp (-(max (g k - g (σ k)) 0)) := hstep1
    _ = c ^ (d - 1) * Real.exp (-(∑ k ∈ Finset.univ.erase j, max (g k - g (σ k)) 0)) := hstep2
    _ ≤ c ^ (d - 1) * Real.exp (-(g i - g j)) := by
        apply mul_le_mul_of_nonneg_left hstep3 (by positivity)

/-- **Reverse-side entry bound (Ruelle Lemma 1.4, reverse half).**

Let `S` be an orthogonal matrix (`S * Sᵀ = 1`) whose entries obey the *graded forward* bound
`|S a b| ≤ c · exp(-(max (g b - g a) 0))` (entries where the level `g` increases are exponentially
small).  Then every entry obeys the *reverse* bound at the full pairwise rate:

    |S i j| ≤ (d-1)! · c^(d-1) · exp(-(g i - g j)).

Proof: `S⁻¹ = Sᵀ`, so `S i j` is a `(det S)`-scaled cofactor with `|det S| = 1`; expanding the
cofactor minor by the Leibniz formula, every surviving permutation term pays exactly the level
imbalance `g i - g j` (telescoping), and there are at most `(d-1)!` of them. -/
theorem entry_reverse_bound_of_orthogonal {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S * Sᵀ = 1) (g : Fin d → ℝ) (c : ℝ) (hc : 1 ≤ c)
    (hfwd : ∀ a b : Fin d, |S a b| ≤ c * Real.exp (-(max (g b - g a) 0))) :
    ∀ i j : Fin d, |S i j| ≤ (d - 1).factorial * c ^ (d - 1) * Real.exp (-(g i - g j)) := by
  classical
  intro i j
  have hc0 : (0:ℝ) ≤ c := le_trans zero_le_one hc
  -- `det S = ±1`.
  have hdet : S.det = 1 ∨ S.det = -1 := by
    have h2 : S.det ^ 2 = 1 := by
      have := congrArg Matrix.det hS
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
      nlinarith [this]
    have hfac : (S.det - 1) * (S.det + 1) = 0 := by nlinarith [h2]
    rcases mul_eq_zero.1 hfac with h | h
    · left; linarith
    · right; linarith
  -- `S i j = (S⁻¹) j i = Ring.inverse (det S) * adjugate S j i`.
  have hinv : S⁻¹ = Sᵀ := Matrix.inv_eq_right_inv hS
  have hentry : S i j = Ring.inverse S.det * Matrix.adjugate S j i := by
    have : (S⁻¹) j i = Ring.inverse S.det * Matrix.adjugate S j i := by
      rw [Matrix.inv_def]; simp [Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
    rw [hinv] at this
    simpa [Matrix.transpose_apply] using this
  -- `|S i j| = |adjugate S j i|` (since `|Ring.inverse (det S)| = 1`).
  have habs : |S i j| = |Matrix.adjugate S j i| := by
    rw [hentry, abs_mul]
    have hri : |Ring.inverse S.det| = 1 := by
      rcases hdet with h | h <;>
        simp [h, Ring.inverse_one, show Ring.inverse (-1 : ℝ) = -1 from by
          rw [Ring.inverse_eq_inv']; norm_num]
    rw [hri, one_mul]
  -- `adjugate S j i = det (S.updateRow i (Pi.single j 1))`.
  rw [habs, Matrix.adjugate_apply]
  set M : Matrix (Fin d) (Fin d) ℝ := S.updateRow i (Pi.single j 1) with hMdef
  -- Leibniz bound.
  refine (abs_det_le_sum_abs_prod M).trans ?_
  -- Each term: nonzero only when `σ j = i`; then `= ∏_{k≠j}|S(σk)k| ≤ B`.
  set B : ℝ := c ^ (d - 1) * Real.exp (-(g i - g j)) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  -- termwise: `∏_k |M (σ k) k| ≤ if σ j = i then B else 0`.
  have hterm : ∀ σ : Equiv.Perm (Fin d),
      ∏ k, |M (σ k) k| ≤ (if σ j = i then B else 0) := by
    intro σ
    by_cases hσ : σ j = i
    · rw [if_pos hσ]
      -- The factor at `k = j` is `|Pi.single j 1 j| = 1`; pull it out, leaving the erase-j product.
      have hsplit : ∏ k, |M (σ k) k|
          = |M (σ j) j| * ∏ k ∈ Finset.univ.erase j, |M (σ k) k| := by
        rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ j)]; ring
      have hMjj : |M (σ j) j| = 1 := by
        rw [hMdef, hσ, Matrix.updateRow_self]; simp
      have hrest : ∏ k ∈ Finset.univ.erase j, |M (σ k) k|
          = ∏ k ∈ Finset.univ.erase j, |S (σ k) k| := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [Finset.mem_erase] at hk
        have hσk : σ k ≠ i := by
          intro h; exact hk.1 (σ.injective (h.trans hσ.symm))
        rw [hMdef, Matrix.updateRow_ne hσk]
      rw [hsplit, hMjj, one_mul, hrest]
      exact prod_entry_bound S g c hc0 hfwd σ i j hσ
    · rw [if_neg hσ]
      -- The factor at `k = σ⁻¹ i` is `|Pi.single j 1 (σ⁻¹ i)| = 0` since `σ⁻¹ i ≠ j`.
      have hki : σ⁻¹ i ≠ j := by
        intro h; apply hσ; rw [← h]; simp
      have hself : σ (σ⁻¹ i) = i := by
        simp
      have : |M (σ (σ⁻¹ i)) (σ⁻¹ i)| = 0 := by
        rw [hself, hMdef, Matrix.updateRow_self, Pi.single_eq_of_ne hki, abs_zero]
      calc ∏ k, |M (σ k) k|
          ≤ ∏ k, |M (σ k) k| := le_refl _
        _ = 0 := by
            rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ (σ⁻¹ i)), this, mul_zero]
  -- Sum the termwise bound; the `ite` sum collapses to `card(filter)·B`.
  refine (Finset.sum_le_sum (fun σ _ => hterm σ)).trans ?_
  rw [← Finset.sum_filter (fun σ : Equiv.Perm (Fin d) => σ j = i) (fun _ => B)]
  -- `∑_{σ ∈ filter} B = card • B ≤ (d-1)! • B = (d-1)!·c^(d-1)·exp(...)`.
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcardle := card_filter_apply_eq_le i j
  calc ((Finset.univ.filter (fun σ : Equiv.Perm (Fin d) => σ j = i)).card : ℝ) * B
      ≤ ((d - 1).factorial : ℝ) * B := by
        apply mul_le_mul_of_nonneg_right _ hB0
        exact_mod_cast hcardle
    _ = (d - 1).factorial * c ^ (d - 1) * Real.exp (-(g i - g j)) := by rw [hBdef]; ring

#print axioms entry_reverse_bound_of_orthogonal

end Ruelle13
