/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.ExteriorNorm.Basic

/-!
# Singular-value submultiplicativity, Plücker coordinates and the eigenvalue ceiling

Building on the exterior-power operator-norm engine and the compound matrix, this module proves the
submultiplicativity of the product of the top-`k` singular values, the Rayleigh / sin-Θ
off-diagonal estimates, and the Plücker bridge giving the top eigenpair and second-eigenvalue
ceiling of the compound of a gapped symmetric map in compound-matrix coordinates.

## Main results

* `Oseledets.ExteriorNorm.prod_singularValues_comp_le` —
  `∏_{i<k} σᵢ(g ∘ f) ≤ (∏_{i<k} σᵢ(g)) · (∏_{i<k} σᵢ(f))`, the input to the Oseledets
  singular-value exponents via Kingman's subadditive ergodic theorem.
* `Oseledets.ExteriorNorm.plucker_eigenpair_ceiling_standard` — for a symmetric map with an
  eigenvalue gap, the top eigenpair and second-eigenvalue ceiling of the compound, in
  compound-matrix coordinates (the Plücker bridge).
* `Oseledets.ExteriorNorm.norm_offdiag_residual_compound_le`,
  `Oseledets.ExteriorNorm.perturbed_compound_gram_ceiling` — the off-diagonal numerator bound and
  the `ν`-ceiling feeding the band-projector increment estimate.
-/

open Module InnerProductSpace
open scoped Matrix.Norms.L2Operator Matrix

noncomputable section

namespace Oseledets.ExteriorNorm

/-! ## Submultiplicativity of the product of singular values -/

section Crux

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- **Submultiplicativity of the product of the top-`k` singular values**, assembled from the
submultiplicativity engine and the singular-value bridge:
`∏_{i<k} σᵢ(g ∘ f) ≤ (∏_{i<k} σᵢ(g)) · (∏_{i<k} σᵢ(f))`. -/
theorem prod_singularValues_comp_le (k : ℕ) (f : E →ₗ[ℝ] F) (g : F →ₗ[ℝ] G) :
    ∏ i ∈ Finset.range k, (g ∘ₗ f).singularValues i
      ≤ (∏ i ∈ Finset.range k, g.singularValues i)
        * ∏ i ∈ Finset.range k, f.singularValues i := by
  rw [← exteriorOpNorm_hodge_eq_prod_singularValues k (g ∘ₗ f),
      ← exteriorOpNorm_hodge_eq_prod_singularValues k g,
      ← exteriorOpNorm_hodge_eq_prod_singularValues k f]
  exact exteriorOpNorm_comp_le k (hodgeTrivialization k) (hodgeTrivialization k)
    (hodgeTrivialization k) f g

end Crux

/-! ## The rank-1 exterior Rayleigh-deficit bound

The band-projector increment reduces to a rank-1 dominant-eigenvector `sin Θ` estimate
(`sin_sq_le_rayleigh_deficit_div_gap` in `Oseledets.Lyapunov.OseledetsLimit`). This section
provides the deficit-side pieces feeding that core: the per-vector compound operator-norm step
(Lemma 1), the Rayleigh quotient identity and top-eigenvalue ceiling `μ₀ = ‖compound‖²`
(Lemma 2), and the assembled deficit bound `μ₀ − ⟨C_n v', v'⟩ ≤ (1 − 1/κ²)·μ₀` (Lemma 3),
with `κ = ‖compound B‖·‖(compound B)⁻¹‖` the compound condition number. -/

section Rayleigh

variable {d : ℕ}

/-- Per-vector L2 operator-norm bound for `toEuclideanLin`: `‖toEuclideanLin N w‖ ≤ ‖N‖·‖w‖`.
Routed through the bundled continuous-linear-map `toEuclideanCLM`, whose operator norm is the L2
matrix norm `‖N‖` by `Matrix.l2_opNorm_toEuclideanCLM`. -/
theorem norm_toEuclideanLin_apply_le (N : Matrix (Fin d) (Fin d) ℝ)
    (w : EuclideanSpace ℝ (Fin d)) :
    ‖Matrix.toEuclideanLin N w‖ ≤ ‖N‖ * ‖w‖ := by
  have hc : (Matrix.toEuclideanLin N w) = Matrix.toEuclideanCLM (𝕜 := ℝ) N w := by
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]; rfl
  rw [hc]
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) N w‖
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) N‖ * ‖w‖ := (Matrix.toEuclideanCLM (𝕜 := ℝ) N).le_opNorm w
    _ = ‖N‖ * ‖w‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM]

/-- The `k`-th compound of the identity matrix is the identity. Via the compound bridge
`conjExteriorMap_eq_toEuclideanLin_compound`, since `⋀^k id = id` (`exteriorPower.map_id`). -/
theorem compoundMatrix_one (k : ℕ) :
    compoundMatrix k (1 : Matrix (Fin d) (Fin d) ℝ) = 1 := by
  apply (Matrix.toEuclideanLin (n := Fin _) (m := Fin _)).injective
  rw [← conjExteriorMap_eq_toEuclideanLin_compound]
  have h1 : Matrix.toEuclideanLin (1 : Matrix (Fin d) (Fin d) ℝ) = LinearMap.id := by
    ext v i; simp
  rw [h1]
  unfold conjExteriorMap
  rw [exteriorPower.map_id]
  have h2 : Matrix.toEuclideanLin
      (1 : Matrix (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d)))))
        (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d))))) ℝ) = LinearMap.id := by
    ext v i; simp
  rw [h2]
  ext x; simp

/-- For invertible `B`, `compound k B⁻¹` is a right inverse of `compound k B`
(`compoundMatrix_mul` + `compoundMatrix_one`). -/
theorem compoundMatrix_mul_inv (k : ℕ) {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.det ≠ 0) :
    compoundMatrix k B * compoundMatrix k B⁻¹ = 1 := by
  rw [← compoundMatrix_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit hB), compoundMatrix_one]

/-- For invertible `B`, `compound k B⁻¹` is a left inverse of `compound k B`. -/
theorem compoundMatrix_inv_mul (k : ℕ) {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.det ≠ 0) :
    compoundMatrix k B⁻¹ * compoundMatrix k B = 1 := by
  rw [← compoundMatrix_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hB), compoundMatrix_one]

/-- The compound factorisation `compound M = (compound B)⁻¹ · compound(B · M)`, for invertible
`B`. Used in Lemma 3 to lower-bound `‖compound M‖` by `‖compound(B·M)‖`. -/
theorem compoundMatrix_eq_inv_mul (k : ℕ) {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.det ≠ 0)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    compoundMatrix k M = compoundMatrix k B⁻¹ * compoundMatrix k (B * M) := by
  rw [← compoundMatrix_mul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit hB),
    Matrix.one_mul]

/-- **The rank-1 lower bound `μ̃₀ ≥ cM²/cBi²`.** For invertible `B`, the
squared compound operator norm of the perturbed cocycle step `B · M` (= the top eigenvalue `μ̃₀` of
`Cₙ₊₁ = adjoint Gₙ₊₁ ∘ₗ Gₙ₊₁`) is bounded below by `cM²/cBi²`, where `cM = ‖compound k M‖` and
`cBi = ‖compound k B⁻¹‖`. Route: `compound k M = compound k B⁻¹ · compound k (B·M)` gives
`cM ≤ cBi·‖compound(B·M)‖`, hence `‖compound(B·M)‖ ≥ cM/cBi`; squaring yields the bound. -/
theorem norm_sq_compound_mul_ge (k : ℕ) {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.det ≠ 0)
    (M : Matrix (Fin d) (Fin d) ℝ) (hcBipos : 0 < ‖compoundMatrix k B⁻¹‖) :
    ‖compoundMatrix k M‖ ^ 2 / ‖compoundMatrix k B⁻¹‖ ^ 2
      ≤ ‖compoundMatrix k (B * M)‖ ^ 2 := by
  -- `cM ≤ cBi · ‖compound(B·M)‖` from the compound factorisation + submultiplicativity.
  have hstep : ‖compoundMatrix k M‖
      ≤ ‖compoundMatrix k B⁻¹‖ * ‖compoundMatrix k (B * M)‖ := by
    conv_lhs => rw [compoundMatrix_eq_inv_mul k hB M]
    exact Matrix.l2_opNorm_mul _ _
  rw [div_le_iff₀ (by positivity)]
  have hcMnn : 0 ≤ ‖compoundMatrix k M‖ := norm_nonneg _
  nlinarith [hstep, hcMnn, norm_nonneg (compoundMatrix k (B * M)), hcBipos]

set_option maxHeartbeats 800000 in -- heavy elaboration; exceeds the default budget
-- The `⋀^k`-finrank-indexed `EuclideanSpace` statement is expensive to elaborate.
/-- **Lemma 1 — the rank-1 per-vector step.** The squared norm of the compound of a product,
applied to `w`, is dominated by `‖compound B‖²` times the squared norm of the `M`-compound at `w`:
`‖compound(B·M) w‖² ≤ ‖compound B‖²·‖compound M w‖²`. This relates the Rayleigh quotients of the
compound Gram operators `C_{n+1}` (from `B·M`) and `C_n` (from `M`). Via
`toEuclideanLin_compoundMatrix_mul` + the per-vector operator-norm step. -/
theorem rayleigh_compound_mul_le (k : ℕ) (B M : Matrix (Fin d) (Fin d) ℝ)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d)))))) :
    ‖Matrix.toEuclideanLin (compoundMatrix k (B * M)) w‖ ^ 2
      ≤ ‖compoundMatrix k B‖ ^ 2
        * ‖Matrix.toEuclideanLin (compoundMatrix k M) w‖ ^ 2 := by
  rw [toEuclideanLin_compoundMatrix_mul, LinearMap.comp_apply]
  set a := ‖Matrix.toEuclideanLin (compoundMatrix k M) w‖ with ha
  set b := ‖compoundMatrix k B‖ with hb
  have h : ‖Matrix.toEuclideanLin (compoundMatrix k B)
      (Matrix.toEuclideanLin (compoundMatrix k M) w)‖ ≤ b * a :=
    norm_toEuclideanLin_apply_le _ _
  have han : 0 ≤ a := norm_nonneg _
  have hbn : 0 ≤ b := norm_nonneg _
  calc ‖Matrix.toEuclideanLin (compoundMatrix k B)
        (Matrix.toEuclideanLin (compoundMatrix k M) w)‖ ^ 2
      ≤ (b * a) ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _) h
    _ = b ^ 2 * a ^ 2 := by ring

/-- **Lemma 2 (Rayleigh identity).** The Rayleigh quotient of the compound Gram operator
`C_n = adjoint(compound M) ∘ₗ compound M` at `w` equals `‖compound M w‖²`. -/
theorem rayleigh_compound_eq_norm_sq (k : ℕ) (M : Matrix (Fin d) (Fin d) ℝ)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d)))))) :
    (inner ℝ ((LinearMap.adjoint (Matrix.toEuclideanLin (compoundMatrix k M)) ∘ₗ
        Matrix.toEuclideanLin (compoundMatrix k M)) w) w : ℝ)
      = ‖Matrix.toEuclideanLin (compoundMatrix k M) w‖ ^ 2 := by
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]

/-- **Lemma 2 (top-eigenvalue ceiling).** The Rayleigh quotient of the compound Gram operator is
bounded by `‖compound M‖²·‖w‖²`; equivalently the top eigenvalue `μ₀` of
`C_n = adjoint(compound M) ∘ₗ compound M` is `‖compound M‖²` (the squared operator norm of the
compound = top eigenvalue of `AᵀA`). -/
theorem rayleigh_compound_le (k : ℕ) (M : Matrix (Fin d) (Fin d) ℝ)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d)))))) :
    (inner ℝ ((LinearMap.adjoint (Matrix.toEuclideanLin (compoundMatrix k M)) ∘ₗ
        Matrix.toEuclideanLin (compoundMatrix k M)) w) w : ℝ)
      ≤ ‖compoundMatrix k M‖ ^ 2 * ‖w‖ ^ 2 := by
  rw [rayleigh_compound_eq_norm_sq]
  have h := norm_toEuclideanLin_apply_le (compoundMatrix k M) w
  have hn := norm_nonneg (Matrix.toEuclideanLin (compoundMatrix k M) w)
  nlinarith [h, norm_nonneg (compoundMatrix k M), norm_nonneg w]

/-- Pure-real algebraic kernel of the deficit bound: from `BM ≤ CB·r` and `mu ≤ CBi·BM` (with all
nonnegative) one gets `mu² − r² ≤ (1 − 1/(CB·CBi)²)·mu²`. -/
theorem rayleigh_deficit_kernel {BM CB r CBi mu : ℝ}
    (hCBn : 0 ≤ CB) (hCBin : 0 ≤ CBi) (hmun : 0 ≤ mu)
    (hstep1 : BM ≤ CB * r) (hstep2 : mu ≤ CBi * BM) :
    mu ^ 2 - r ^ 2 ≤ (1 - 1 / (CB * CBi) ^ 2) * mu ^ 2 := by
  by_cases hκ : CB * CBi = 0
  · have h0 : (CB * CBi) ^ 2 = 0 := by rw [hκ]; ring
    rw [h0]; simp only [div_zero, sub_zero, one_mul]
    nlinarith [sq_nonneg r]
  · have hκpos : 0 < CB * CBi := lt_of_le_of_ne (by positivity) (Ne.symm hκ)
    have hchain : mu ≤ (CB * CBi) * r := by
      calc mu ≤ CBi * BM := hstep2
        _ ≤ CBi * (CB * r) := by nlinarith [hstep1, hCBin]
        _ = (CB * CBi) * r := by ring
    have hrlb : mu / (CB * CBi) ≤ r := by rw [div_le_iff₀ hκpos]; linarith
    have hr2 : (mu / (CB * CBi)) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by positivity) hrlb 2
    rw [div_pow] at hr2
    have heq : mu ^ 2 - mu ^ 2 / (CB * CBi) ^ 2 = (1 - 1 / (CB * CBi) ^ 2) * mu ^ 2 := by ring
    linarith [hr2, heq.ge, heq.le]

set_option maxHeartbeats 1600000 in -- heavy elaboration; exceeds the default budget
-- The `⋀^k`-finrank-indexed `EuclideanSpace` statement is expensive to elaborate.
/-- **Lemma 3 — the rank-1 exterior Rayleigh-deficit bound.**
For invertible `B` and a unit vector `v'` that achieves the operator norm of the compound
`compound (B·M)` (so `‖compound(B·M) v'‖ = ‖compound(B·M)‖`, i.e. `v'` is a top right-singular
vector / dominant eigenvector of `C_{n+1}`), the Rayleigh deficit of the operator
`C_n = adjoint(compound M) ∘ₗ compound M` at `v'` against its top value `μ₀ = ‖compound M‖²`
obeys `μ₀ − ⟨C_n v', v'⟩ ≤ (1 − 1/κ²)·μ₀` with `κ = ‖compound B‖·‖(compound B)⁻¹‖`.

This is the deficit-side input to `sin_sq_le_rayleigh_deficit_div_gap` (with
`ε := μ₀ − ⟨C_n v', v'⟩`, `μ₀ := ‖compound M‖²`). The `v'`-achieves-the-op-norm hypothesis encodes
that `v'` is the top eigenvector of `C_{n+1}`; its existence is the caller's responsibility. -/
theorem rayleigh_deficit_le (k : ℕ) {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.det ≠ 0)
    (M : Matrix (Fin d) (Fin d) ℝ)
    {v' : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d)))))}
    (htop : ‖Matrix.toEuclideanLin (compoundMatrix k (B * M)) v'‖ = ‖compoundMatrix k (B * M)‖) :
    ‖compoundMatrix k M‖ ^ 2
        - (inner ℝ ((LinearMap.adjoint (Matrix.toEuclideanLin (compoundMatrix k M)) ∘ₗ
            Matrix.toEuclideanLin (compoundMatrix k M)) v') v' : ℝ)
      ≤ (1 - 1 / (‖compoundMatrix k B‖ * ‖compoundMatrix k B⁻¹‖) ^ 2)
          * ‖compoundMatrix k M‖ ^ 2 := by
  rw [rayleigh_compound_eq_norm_sq]
  -- (1) `v'` achieves the op-norm of `compound(B·M)`, then the per-vector step:
  --     `‖compound(B·M)‖ ≤ ‖compound B‖·‖compound M v'‖`.
  have hstep1 : ‖compoundMatrix k (B * M)‖
      ≤ ‖compoundMatrix k B‖ * ‖Matrix.toEuclideanLin (compoundMatrix k M) v'‖ := by
    rw [← htop, toEuclideanLin_compoundMatrix_mul, LinearMap.comp_apply]
    exact norm_toEuclideanLin_apply_le _ _
  -- (2) `‖compound M‖ ≤ ‖(compound B)⁻¹‖·‖compound(B·M)‖` from the compound factorisation.
  have hstep2 : ‖compoundMatrix k M‖
      ≤ ‖compoundMatrix k B⁻¹‖ * ‖compoundMatrix k (B * M)‖ := by
    conv_lhs => rw [compoundMatrix_eq_inv_mul k hB M]
    exact Matrix.l2_opNorm_mul _ _
  exact rayleigh_deficit_kernel (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hstep1 hstep2

end Rayleigh

/-! ## The off-diagonal residual estimate and the perturbed Gram ceiling

The refined Davis–Kahan sin-Θ estimate in **off-diagonal/residual form**
(`offdiag_sin_le_residual_div_gap` in `Oseledets.Lyapunov.OseledetsLimit`) needs two
cocycle-specific inputs:

* the **off-diagonal residual numerator** `‖Cₙ₊₁ v₀ − ⟪Cₙ₊₁ v₀, v₀⟫ v₀‖ ≤ τ₀ τ₁ ‖H‖²`, where
  `Cₙ₊₁ = adjoint G' ∘ₗ G'`, `G' = H ∘ₗ G`, and `v₀` is the top eigenvector of
  `Cₙ = adjoint G ∘ₗ G` (`offdiag_residual_norm_le`);
* the **`ν`-ceiling** `∀ z ⊥ v₀, ⟪Cₙ₊₁ z, z⟫ ≤ (μ₁ ‖H‖²) ‖z‖²` transported from the `Cₙ`-ceiling
  `∀ z ⊥ v₀, ⟪Cₙ z, z⟫ ≤ μ₁ ‖z‖²` (`perturbed_gram_ceiling`).

Both are abstract operator facts (no compound/exterior structure); the cocycle specialisation in
standard coordinates (where `G = toEuclideanLin (compoundMatrix k ·)`) follows by
`toEuclideanLin_compoundMatrix_mul` (functoriality `G' = H ∘ₗ G`) and the per-vector operator-norm
bound `norm_toEuclideanLin_apply_le`. These pieces feed the band-projector increment bound
together with the back-transport `norm_proj_sub_le_wedge`. -/

section OffDiag

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

open scoped RealInnerProductSpace

omit [FiniteDimensional ℝ E] in
/-- **The off-diagonal residual is orthogonal to `v₀`.** For a unit `v₀`, the residual
`C v₀ − ⟪C v₀, v₀⟫ v₀ = (I − P) C v₀` is orthogonal to `v₀`. -/
theorem residual_orthogonal {C : E →ₗ[ℝ] E} {v₀ : E} (hv₀ : ‖v₀‖ = 1) :
    (inner ℝ (C v₀ - (inner ℝ (C v₀) v₀ : ℝ) • v₀) v₀ : ℝ) = 0 := by
  have hv₀v₀ : (inner ℝ v₀ v₀ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hv₀]; norm_num
  rw [inner_sub_left, real_inner_smul_left, hv₀v₀, mul_one, sub_self]

/-- **Rayleigh of the Gram operator is the squared norm:** `⟪(adjoint G ∘ₗ G) v, v⟫ = ‖G v‖²`
(abstract form; `rayleigh_compound_eq_norm_sq` is the compound-matrix specialisation). -/
theorem gram_rayleigh_eq_norm_sq (G : E →ₗ[ℝ] F) (v : E) :
    (inner ℝ ((LinearMap.adjoint G ∘ₗ G) v) v : ℝ) = ‖G v‖ ^ 2 := by
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]

/-- **The off-diagonal inner product reduction:**
`⟪(adjoint G' ∘ₗ G') v₀, z⟫ = ⟪G' v₀, G' z⟫`
(plain adjoint move; for `z ⊥ v₀` this is the off-diagonal block of `Cₙ₊₁`). -/
theorem offdiag_inner_eq (G' : E →ₗ[ℝ] F) (v₀ z : E) :
    (inner ℝ ((LinearMap.adjoint G' ∘ₗ G') v₀) z : ℝ) = inner ℝ (G' v₀) (G' z) := by
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]

/-- **The off-diagonal residual norm estimate.**
For the perturbed Gram operator `Cₙ₊₁ = adjoint G' ∘ₗ G'` with `G' = H ∘ₗ G` (functoriality) and
`v₀` the top unit eigenvector of `Cₙ = adjoint G ∘ₗ G`, the off-diagonal residual
`Cₙ₊₁ v₀ − ⟪Cₙ₊₁ v₀, v₀⟫ v₀` has norm at most `τ₀ · τ₁ · ‖H‖²`, where `τ₀ = ‖G v₀‖` (the top
singular value of `G`) and `τ₁` is the second-singular-value ceiling on `v₀^⊥`
(`hperp : ∀ z ⊥ v₀, ‖z‖ ≤ 1 → ‖G z‖ ≤ τ₁`).

Proof: the residual `res ⊥ v₀`; `‖res‖² = ⟪res, res⟫ = ⟪Cₙ₊₁ v₀, res⟫` (since `res ⊥ v₀`)
`= ⟪H G v₀, H G res⟫ ≤ ‖H‖²‖G v₀‖‖G res‖ ≤ ‖H‖² τ₀ τ₁ ‖res‖` by Cauchy–Schwarz, the per-vector
operator-norm bound on `H`, `htop`, and `hperp` applied to the unit normalisation of `res`. Dividing
by `‖res‖` gives the bound. -/
theorem offdiag_residual_norm_le
    {G : E →ₗ[ℝ] F} {H : F →ₗ[ℝ] F} {G' : E →ₗ[ℝ] F}
    (hcomp : G' = H ∘ₗ G)
    {v₀ : E} {τ₀ τ₁ nH : ℝ} (hτ₀ : 0 ≤ τ₀) (hτ₁ : 0 ≤ τ₁) (hnH : 0 ≤ nH) (hv₀ : ‖v₀‖ = 1)
    (htop : ‖G v₀‖ = τ₀)
    (hH : ∀ y, ‖H y‖ ≤ nH * ‖y‖)
    (hperp : ∀ z : E, (inner ℝ z v₀ : ℝ) = 0 → ‖z‖ ≤ 1 → ‖G z‖ ≤ τ₁) :
    ‖(LinearMap.adjoint G' ∘ₗ G') v₀ - (inner ℝ ((LinearMap.adjoint G' ∘ₗ G') v₀) v₀ : ℝ) • v₀‖
      ≤ τ₀ * τ₁ * nH ^ 2 := by
  set C := LinearMap.adjoint G' ∘ₗ G' with hC
  set res := C v₀ - (inner ℝ (C v₀) v₀ : ℝ) • v₀ with hres
  have hresperp : (inner ℝ res v₀ : ℝ) = 0 := residual_orthogonal hv₀
  -- key inner bound: for z ⊥ v₀, ⟪res, z⟫ ≤ τ₀τ₁nH² ‖z‖
  have hkey : ∀ z : E, (inner ℝ z v₀ : ℝ) = 0 →
      (inner ℝ res z : ℝ) ≤ τ₀ * τ₁ * nH ^ 2 * ‖z‖ := by
    intro z hz
    have hrz : (inner ℝ res z : ℝ) = inner ℝ (C v₀) z := by
      rw [hres, inner_sub_left, real_inner_smul_left,
        show (inner ℝ v₀ z : ℝ) = inner ℝ z v₀ from real_inner_comm z v₀, hz, mul_zero, sub_zero]
    rw [hrz, hC, offdiag_inner_eq, hcomp]
    simp only [LinearMap.comp_apply]
    rcases eq_or_lt_of_le (norm_nonneg z) with hz0 | hzpos
    · have : z = 0 := by rw [← norm_eq_zero]; exact hz0.symm
      subst this; simp
    · have hznorm : ‖z‖ ≠ 0 := ne_of_gt hzpos
      have hzu : ‖(‖z‖⁻¹ : ℝ) • z‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_mul_cancel₀ hznorm]
      have hzuperp : (inner ℝ ((‖z‖⁻¹ : ℝ) • z) v₀ : ℝ) = 0 := by
        rw [real_inner_smul_left, hz, mul_zero]
      have hGzu : ‖G ((‖z‖⁻¹ : ℝ) • z)‖ ≤ τ₁ := hperp _ hzuperp hzu
      have hGz : ‖G z‖ ≤ τ₁ * ‖z‖ := by
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hGzu
        rw [inv_mul_le_iff₀ hzpos] at hGzu
        linarith [hGzu]
      calc (inner ℝ (H (G v₀)) (H (G z)) : ℝ)
          ≤ ‖H (G v₀)‖ * ‖H (G z)‖ := real_inner_le_norm _ _
        _ ≤ (nH * ‖G v₀‖) * (nH * ‖G z‖) := by
            apply mul_le_mul (hH _) (hH _) (norm_nonneg _); positivity
        _ ≤ (nH * τ₀) * (nH * (τ₁ * ‖z‖)) := by rw [htop]; gcongr
        _ = τ₀ * τ₁ * nH ^ 2 * ‖z‖ := by ring
  rcases eq_or_lt_of_le (norm_nonneg res) with hr0 | hrpos
  · rw [hres] at hr0 ⊢; rw [← hr0]; positivity
  · have hself : (inner ℝ res res : ℝ) = ‖res‖ ^ 2 := real_inner_self_eq_norm_sq res
    have hb := hkey res hresperp
    rw [hself] at hb
    have hmul : ‖res‖ * ‖res‖ ≤ (τ₀ * τ₁ * nH ^ 2) * ‖res‖ := by nlinarith [hb]
    exact le_of_mul_le_mul_right hmul hrpos

/-- **The `ν`-ceiling for the perturbed Gram operator.**
From a Rayleigh ceiling `∀ z ⊥ v₀, ⟪Cₙ z, z⟫ ≤ μ₁ ‖z‖²` on the unperturbed Gram operator
`Cₙ = adjoint G ∘ₗ G`, the perturbed operator `Cₙ₊₁ = adjoint G' ∘ₗ G'` with `G' = H ∘ₗ G` obeys
the amplified ceiling `∀ z ⊥ v₀, ⟪Cₙ₊₁ z, z⟫ ≤ (μ₁ ‖H‖²) ‖z‖²`. Proof: `⟪Cₙ₊₁ z, z⟫ = ‖H G z‖²
≤ ‖H‖² ‖G z‖² = ‖H‖² ⟪Cₙ z, z⟫ ≤ ‖H‖² μ₁ ‖z‖²`. This supplies the `ν := μ₁ ‖H‖²` ceiling consumed
by `offdiag_sin_le_residual_div_gap`. -/
theorem perturbed_gram_ceiling
    {G : E →ₗ[ℝ] F} {H : F →ₗ[ℝ] F} {G' : E →ₗ[ℝ] F}
    (hcomp : G' = H ∘ₗ G)
    {v₀ : E} {μ₁ nH : ℝ}
    (hH : ∀ y, ‖H y‖ ≤ nH * ‖y‖)
    (hceil : ∀ z : E, (inner ℝ z v₀ : ℝ) = 0 →
      (inner ℝ ((LinearMap.adjoint G ∘ₗ G) z) z : ℝ) ≤ μ₁ * ‖z‖ ^ 2) :
    ∀ z : E, (inner ℝ z v₀ : ℝ) = 0 →
      (inner ℝ ((LinearMap.adjoint G' ∘ₗ G') z) z : ℝ) ≤ (μ₁ * nH ^ 2) * ‖z‖ ^ 2 := by
  intro z hz
  rw [gram_rayleigh_eq_norm_sq, hcomp, LinearMap.comp_apply]
  have h1 : ‖H (G z)‖ ^ 2 ≤ nH ^ 2 * ‖G z‖ ^ 2 := by
    have := hH (G z); nlinarith [this, norm_nonneg (G z), norm_nonneg (H (G z))]
  have h2 : ‖G z‖ ^ 2 = (inner ℝ ((LinearMap.adjoint G ∘ₗ G) z) z : ℝ) :=
    (gram_rayleigh_eq_norm_sq G z).symm
  have h3 : (inner ℝ ((LinearMap.adjoint G ∘ₗ G) z) z : ℝ) ≤ μ₁ * ‖z‖ ^ 2 := hceil z hz
  calc ‖H (G z)‖ ^ 2 ≤ nH ^ 2 * ‖G z‖ ^ 2 := h1
    _ = nH ^ 2 * (inner ℝ ((LinearMap.adjoint G ∘ₗ G) z) z : ℝ) := by rw [h2]
    _ ≤ nH ^ 2 * (μ₁ * ‖z‖ ^ 2) := by apply mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (μ₁ * nH ^ 2) * ‖z‖ ^ 2 := by ring

end OffDiag

/-! ### The cocycle specialisation in compound-matrix coordinates

Specialising `offdiag_residual_norm_le` / `perturbed_gram_ceiling` to the cocycle Gram operators
`Cₙ = adjoint Gₙ ∘ₗ Gₙ`, `Gₙ = toEuclideanLin (compoundMatrix k Mₙ)`, with the one-step left factor
`B = A(Tⁿx)` (so `Mₙ₊₁ = B · Mₙ` and `Gₙ₊₁ = (compound B) ∘ Gₙ` by
`toEuclideanLin_compoundMatrix_mul`). The SVD ceiling `hperp` of the abstract lemma is discharged
from a `μ₁`-ceiling on `Cₙ` via `rayleigh_compound_eq_norm_sq`:
`‖Gₙ z‖² = ⟪Cₙ z, z⟫ ≤ μ₁ ‖z‖² ≤ μ₁` for `‖z‖ ≤ 1`, hence `‖Gₙ z‖ ≤ √μ₁ =: τ₁`. -/

section CompoundOffDiag

variable {d : ℕ}

open scoped RealInnerProductSpace

/-- **The off-diagonal residual estimate for the compound Gram operators.**
With `Gₙ = toEuclideanLin (compoundMatrix k M)`, `Cₙ = adjoint Gₙ ∘ₗ Gₙ`, the one-step left factor
`B`, and `Cₙ₊₁ = adjoint Gₙ₊₁ ∘ₗ Gₙ₊₁` for `Gₙ₊₁ = toEuclideanLin (compoundMatrix k (B * M))`: if
`v₀` is a unit vector achieving the compound operator norm `‖Gₙ v₀‖ = ‖compoundMatrix k M‖ = τ₀`
(the top right-singular vector of `Gₙ`, i.e. the top eigenvector of `Cₙ`) with a `μ₁`-Rayleigh
ceiling on `v₀^⊥`, then the off-diagonal residual obeys
`‖Cₙ₊₁ v₀ − ⟪Cₙ₊₁ v₀, v₀⟫ v₀‖ ≤ ‖compoundMatrix k M‖ · √μ₁ · ‖compoundMatrix k B‖²`.
(`τ₀ = ‖compoundMatrix k M‖`, `τ₁ = √μ₁`, `‖H‖ = ‖compoundMatrix k B‖`.) -/
theorem norm_offdiag_residual_compound_le (k : ℕ) (B M : Matrix (Fin d) (Fin d) ℝ)
    {v₀ : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d)))))}
    {μ₁ : ℝ} (hμ₁ : 0 ≤ μ₁) (hv₀ : ‖v₀‖ = 1)
    (htop : ‖Matrix.toEuclideanLin (compoundMatrix k M) v₀‖ = ‖compoundMatrix k M‖)
    (hceil : ∀ z, (inner ℝ z v₀ : ℝ) = 0 →
      (inner ℝ ((LinearMap.adjoint (Matrix.toEuclideanLin (compoundMatrix k M)) ∘ₗ
          Matrix.toEuclideanLin (compoundMatrix k M)) z) z : ℝ) ≤ μ₁ * ‖z‖ ^ 2) :
    ‖(LinearMap.adjoint (Matrix.toEuclideanLin (compoundMatrix k (B * M))) ∘ₗ
          Matrix.toEuclideanLin (compoundMatrix k (B * M))) v₀
        - (inner ℝ ((LinearMap.adjoint (Matrix.toEuclideanLin (compoundMatrix k (B * M))) ∘ₗ
            Matrix.toEuclideanLin (compoundMatrix k (B * M))) v₀) v₀ : ℝ) • v₀‖
      ≤ ‖compoundMatrix k M‖ * Real.sqrt μ₁ * ‖compoundMatrix k B‖ ^ 2 := by
  -- discharge `hperp`: `‖Gₙ z‖ ≤ √μ₁` for `z ⊥ v₀`, `‖z‖ ≤ 1`.
  have hperp : ∀ z, (inner ℝ z v₀ : ℝ) = 0 → ‖z‖ ≤ 1 →
      ‖Matrix.toEuclideanLin (compoundMatrix k M) z‖ ≤ Real.sqrt μ₁ := by
    intro z hz hzn
    have hsq : ‖Matrix.toEuclideanLin (compoundMatrix k M) z‖ ^ 2 ≤ μ₁ := by
      rw [← rayleigh_compound_eq_norm_sq k M z]
      calc (inner ℝ ((LinearMap.adjoint (Matrix.toEuclideanLin (compoundMatrix k M)) ∘ₗ
              Matrix.toEuclideanLin (compoundMatrix k M)) z) z : ℝ)
          ≤ μ₁ * ‖z‖ ^ 2 := hceil z hz
        _ ≤ μ₁ * 1 ^ 2 := by gcongr
        _ = μ₁ := by ring
    have hnn := norm_nonneg (Matrix.toEuclideanLin (compoundMatrix k M) z)
    calc ‖Matrix.toEuclideanLin (compoundMatrix k M) z‖
        = Real.sqrt (‖Matrix.toEuclideanLin (compoundMatrix k M) z‖ ^ 2) :=
          (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt μ₁ := Real.sqrt_le_sqrt hsq
  -- apply the abstract residual estimate with the functoriality `G' = H ∘ₗ G`.
  exact offdiag_residual_norm_le
    (G := Matrix.toEuclideanLin (compoundMatrix k M))
    (H := Matrix.toEuclideanLin (compoundMatrix k B))
    (G' := Matrix.toEuclideanLin (compoundMatrix k (B * M)))
    (toEuclideanLin_compoundMatrix_mul k B M)
    (norm_nonneg _) (Real.sqrt_nonneg _) (norm_nonneg _) hv₀ htop
    (fun y => norm_toEuclideanLin_apply_le (compoundMatrix k B) y)
    hperp

/-- **The `ν`-ceiling for the perturbed compound Gram operator.**
From a `μ₁`-Rayleigh ceiling on `Cₙ = adjoint Gₙ ∘ₗ Gₙ` over `v₀^⊥`, the perturbed compound Gram
operator `Cₙ₊₁ = adjoint Gₙ₊₁ ∘ₗ Gₙ₊₁` (with `Gₙ₊₁ = toEuclideanLin (compoundMatrix k (B * M))`)
obeys the amplified ceiling `∀ z ⊥ v₀, ⟪Cₙ₊₁ z, z⟫ ≤ (μ₁ ‖compoundMatrix k B‖²) ‖z‖²`. This is the
`ν := μ₁ ‖H‖²` ceiling consumed by `offdiag_sin_le_residual_div_gap`. -/
theorem perturbed_compound_gram_ceiling (k : ℕ) (B M : Matrix (Fin d) (Fin d) ℝ)
    {v₀ : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d)))))}
    {μ₁ : ℝ}
    (hceil : ∀ z, (inner ℝ z v₀ : ℝ) = 0 →
      (inner ℝ ((LinearMap.adjoint (Matrix.toEuclideanLin (compoundMatrix k M)) ∘ₗ
          Matrix.toEuclideanLin (compoundMatrix k M)) z) z : ℝ) ≤ μ₁ * ‖z‖ ^ 2) :
    ∀ z, (inner ℝ z v₀ : ℝ) = 0 →
      (inner ℝ ((LinearMap.adjoint (Matrix.toEuclideanLin (compoundMatrix k (B * M))) ∘ₗ
          Matrix.toEuclideanLin (compoundMatrix k (B * M))) z) z : ℝ)
        ≤ (μ₁ * ‖compoundMatrix k B‖ ^ 2) * ‖z‖ ^ 2 :=
  perturbed_gram_ceiling
    (G := Matrix.toEuclideanLin (compoundMatrix k M))
    (H := Matrix.toEuclideanLin (compoundMatrix k B))
    (G' := Matrix.toEuclideanLin (compoundMatrix k (B * M)))
    (toEuclideanLin_compoundMatrix_mul k B M)
    (fun y => norm_toEuclideanLin_apply_le (compoundMatrix k B) y)
    hceil

end CompoundOffDiag

/-! ## The Plücker bridge

For a symmetric PD map `f` with orthonormal eigenbasis `u` and eigenvalues `lam`, the compound
`⋀^k f`, conjugated through the eigenbasis wedge trivialization `onbTriv u`, is a **diagonal**
Euclidean operator: it scales `basisFun i` by the subset product `∏_{a ∈ Sᵢ} lam a`. The top set
`{0,…,k-1}` (maximal by `prod_le_prod_top` for antitone weights) gives the top eigenvector
`v₀ = basisFun i₀` with eigenvalue `μ₀`, and every other weight is `≤ μ₁` (the second-eigenvalue
ceiling). The bridge is completed by the det-Gram identity for the Plücker (wedge) inner
product. -/

section Plucker

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open scoped Classical in
/-- **The conjugated compound is diagonal in the eigenbasis.** For a symmetric `f` with orthonormal
eigenbasis `u` and eigenvalues `lam`, conjugating `⋀^k f` through the eigenbasis wedge
trivialization `onbTriv u` yields a diagonal Euclidean operator: `basisFun i ↦ (∏_{a ∈ Sᵢ} lam a) •
basisFun i`, where `Sᵢ = (wIndexEquiv u k).symm i`. -/
private lemma conjExteriorMap_onbTriv_diag {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : E →ₗ[ℝ] E) (u : OrthonormalBasis ι ℝ E) (lam : ι → ℝ)
    (hf : ∀ i, f (u i) = lam i • u i) (k : ℕ)
    (i : Fin (Module.finrank ℝ (⋀[ℝ]^k E))) :
    conjExteriorMap k (onbTriv u k) (onbTriv u k) f (EuclideanSpace.basisFun _ ℝ i)
      = (∏ a ∈ ((wIndexEquiv u k).symm i : Set.powersetCard ι k).val, lam a)
          • EuclideanSpace.basisFun _ ℝ i := by
  classical
  -- `conjExteriorMap ... (basisFun i) = onbTriv u (⋀^k f (wedge u_{Sᵢ}))`.
  rw [conjExteriorMap]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [show (onbTriv u k).symm (EuclideanSpace.basisFun (Fin (Module.finrank ℝ (⋀[ℝ]^k E))) ℝ i)
      = (u.toBasis.exteriorPower k) ((wIndexEquiv u k).symm i) by
    rw [LinearEquiv.symm_apply_eq]; exact (onbTriv_wedge_eq_basisFun u k i).symm]
  rw [map_exteriorPower_wedgeBasis_eq f u lam hf k, map_smul, onbTriv_wedge_eq_basisFun]

open scoped Classical in
/-- **The Plücker (wedge) inner product is the cross-Gram determinant.** For two families
`v, w : Fin k → E`, the L2 inner product of their Hodge-trivialized wedges equals the determinant
of the cross-Gram matrix `⟪v j, w i⟫`. With orthonormal frames this is the wedge-sine identity
`⟪w_E, w_E'⟫ = det(UᵀV)` feeding the Frobenius back-transport `norm_proj_sub_le_wedge`. -/
theorem inner_hodgeTrivialization_ιMulti (k : ℕ) (v w : Fin k → E) :
    (inner ℝ (hodgeTrivialization k (exteriorPower.ιMulti ℝ k v))
        (hodgeTrivialization k (exteriorPower.ιMulti ℝ k w)) : ℝ)
      = (Matrix.of fun i j => (inner ℝ (v j) (w i) : ℝ)).det := by
  classical
  -- the Hodge trivialization is the standard o.n.-basis wedge trivialization.
  have hStd : hodgeTrivialization (E := E) k = onbTriv (stdOrthonormalBasis ℝ E) k := by
    unfold hodgeTrivialization onbTriv wedgeBasis wedgeIndexEquiv wIndexEquiv
    rfl
  rw [hStd, inner_onbTriv, hodgeForm_ιMulti]

/-- The `j`-th column of a `d×k` matrix, viewed as a vector in `EuclideanSpace ℝ (Fin d)`. The
columns of the band-projector frames `U_top` (`bandProjector_indicator_eq_frame`) are the
orthonormal top-block eigenvectors; their wedge is the Plücker top eigenvector. -/
def colE {d k : ℕ} (U : Matrix (Fin d) (Fin k) ℝ) (j : Fin k) :
    EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm (fun a => U a j)

/-- The L2 inner product of two matrix columns (as Euclidean vectors) is the cross-Gram entry
`(Uᵀ V) i j = ∑ₐ Uₐᵢ Vₐⱼ`. -/
theorem inner_colE {d k : ℕ} (U V : Matrix (Fin d) (Fin k) ℝ) (i j : Fin k) :
    (inner ℝ (colE U i) (colE V j) : ℝ) = (Uᵀ * V) i j := by
  rw [colE, colE, PiLp.inner_apply, Matrix.mul_apply]
  simp only [RCLike.inner_apply, conj_trivial, EuclideanSpace.equiv, Matrix.transpose_apply]
  exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)

/-- **The Plücker frame ↔ wedge determinant bridge (matrix form).** For two `d×k`
column-frames `U`, `V`, the determinant of the cross-Gram `Uᵀ V` equals the L2 inner product of the
Hodge-trivialized wedges of their columns. This is the `hdet : det(UᵀV) = ⟪vt, v₀⟫` plumbing fact
consumed by `Oseledets.norm_bandProjector_succ_sub_le`, with `v₀ = wedge of U-columns` (the Plücker
top eigenvector of `Cₙ`) and `vt = wedge of V-columns` (the perturbed top eigenvector of `Cₙ₊₁`).
Since the band-projector frames `U_top` have orthonormal eigenvector columns
(`bandProjector_indicator_eq_frame`) which are the same eigenbasis the Plücker eigenpair
(`plucker_eigenpair_ceiling_standard`, applied with `u = eigenvectorBasis`) is built from, the
two wedges are exactly these Hodge-trivialized column wedges, and this identity supplies `hdet`. -/
theorem det_transpose_mul_eq_inner_hodge {d k : ℕ} (U V : Matrix (Fin d) (Fin k) ℝ) :
    (Uᵀ * V).det
      = (inner ℝ
          (hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k
            (exteriorPower.ιMulti ℝ k (fun j => colE V j)))
          (hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k
            (exteriorPower.ιMulti ℝ k (fun i => colE U i))) : ℝ) := by
  rw [inner_hodgeTrivialization_ιMulti k (fun j => colE V j) (fun i => colE U i)]
  have hmat : Uᵀ * V
      = Matrix.of (fun i j => (inner ℝ (colE V j) (colE U i) : ℝ)) := by
    ext i j
    rw [Matrix.of_apply, inner_colE, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl
      (fun a _ => by rw [Matrix.transpose_apply, Matrix.transpose_apply]; ring)
  rw [hmat]

/-! ### Abstract diagonal Euclidean operators: eigenpair and second-eigenvalue ceiling -/

/-- A Euclidean operator diagonal in the standard basis (with real weights) is symmetric. -/
private lemma diag_isSymmetric {N : ℕ}
    (g : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) (c : Fin N → ℝ)
    (hg : ∀ i, g (EuclideanSpace.basisFun (Fin N) ℝ i)
      = c i • EuclideanSpace.basisFun (Fin N) ℝ i) :
    g.IsSymmetric := by
  -- check symmetry on the standard basis, then extend bilinearly.
  have hbasis : ∀ i j, (inner ℝ (g (EuclideanSpace.basisFun (Fin N) ℝ i))
      (EuclideanSpace.basisFun (Fin N) ℝ j) : ℝ)
      = inner ℝ (EuclideanSpace.basisFun (Fin N) ℝ i)
          (g (EuclideanSpace.basisFun (Fin N) ℝ j)) := by
    intro i j
    rw [hg i, hg j, inner_smul_left, inner_smul_right,
      (EuclideanSpace.basisFun (Fin N) ℝ).inner_eq_ite i j]
    simp only [RCLike.conj_to_real]
    by_cases h : i = j <;> simp [h]
  intro x y
  have hx := (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr x
  have hy := (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr y
  rw [← hx, ← hy]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, EuclideanSpace.basisFun_repr]
  apply Finset.sum_congr rfl; intro i _
  congr 1
  apply Finset.sum_congr rfl; intro j _
  rw [hbasis j i]

/-- A Euclidean operator `g` diagonal in the standard basis with weights `c`
(`g (basisFun i) = c i • basisFun i`) has `basisFun i₀` as an eigenvector with eigenvalue `c i₀`. -/
private lemma diag_apply_basisFun_eigenpair {N : ℕ}
    (g : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) (c : Fin N → ℝ)
    (hg : ∀ i, g (EuclideanSpace.basisFun (Fin N) ℝ i) = c i • EuclideanSpace.basisFun (Fin N) ℝ i)
    (i₀ : Fin N) :
    g (EuclideanSpace.basisFun (Fin N) ℝ i₀) = c i₀ • EuclideanSpace.basisFun (Fin N) ℝ i₀ :=
  hg i₀

/-- For a diagonal Euclidean operator `g` with weights `c`, the Rayleigh
quotient on a vector `w` orthogonal to `basisFun i₀` is bounded by `μ₁ ‖w‖²`, provided every weight
off the top index `i₀` is `≤ μ₁` (and `0 ≤ μ₁`). -/
private lemma diag_rayleigh_ceiling {N : ℕ}
    (g : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) (c : Fin N → ℝ)
    (hg : ∀ i, g (EuclideanSpace.basisFun (Fin N) ℝ i) = c i • EuclideanSpace.basisFun (Fin N) ℝ i)
    {μ₁ : ℝ} (i₀ : Fin N) (hcap : ∀ i, i ≠ i₀ → c i ≤ μ₁) (_hμpos : 0 ≤ μ₁)
    (w : EuclideanSpace ℝ (Fin N))
    (hw : (inner ℝ w (EuclideanSpace.basisFun (Fin N) ℝ i₀) : ℝ) = 0) :
    (inner ℝ (g w) w : ℝ) ≤ μ₁ * ‖w‖ ^ 2 := by
  -- expand `w` in the standard basis; the Rayleigh quotient is the weighted sum `∑ cᵢ (wᵢ)²`.
  have hwi₀ : w i₀ = 0 := by
    have := hw
    rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right] at this
    simpa using this
  have hexp : w = ∑ i, (w i) • EuclideanSpace.basisFun (Fin N) ℝ i := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr w]
    simp only [EuclideanSpace.basisFun_repr]
  have hgw : g w = ∑ i, (w i) • (c i • EuclideanSpace.basisFun (Fin N) ℝ i) := by
    conv_lhs => rw [hexp]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, hg i]
  -- `⟪g w, w⟫ = ∑ cᵢ (wᵢ)²`.
  have hray : (inner ℝ (g w) w : ℝ) = ∑ i, c i * (w i) ^ 2 := by
    rw [hgw, sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_smul_left, inner_smul_left, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left, map_one, one_mul]
    simp only [RCLike.conj_to_real]
    ring
  -- `‖w‖² = ∑ (wᵢ)²`.
  have hnorm : ‖w‖ ^ 2 = ∑ i, (w i) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp only [RCLike.inner_apply, conj_trivial]; ring
  rw [hray, hnorm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i = i₀
  · subst hi; rw [hwi₀]; simp
  · rw [mul_comm (c i), mul_comm μ₁]
    exact mul_le_mul_of_nonneg_left (hcap i hi) (sq_nonneg _)

/-! ### The Plücker eigenpair and second-eigenvalue ceiling -/

open scoped Classical in
/-- **The Plücker bridge for a symmetric map.** Let `f` be symmetric with orthonormal
eigenbasis `u : OrthonormalBasis (Fin n)` and antitone nonnegative eigenvalues
`lam : ℕ → ℝ` (`f (u i) = lam i • u i`). At a genuine gap `lam k < lam (k-1)` (with `1 ≤ k ≤ n`),
the conjugated compound `C = ⋀^k f` (through the eigenbasis wedge trivialization `onbTriv u`) is a
**symmetric operator** with:

* **top eigenpair:** `C v₀ = μ₀ • v₀`, where `v₀ = basisFun i₀` is the Plücker image of the
  top-`k` eigenframe and `μ₀ = ∏_{i<k} lam i`;
* **second-eigenvalue ceiling:** `∀ w ⊥ v₀, ⟪C w, w⟫ ≤ μ₁ ‖w‖²` with
  `μ₁ = (∏_{i<k-1} lam i)·lam k`;
* **the gap:** `μ₁ < μ₀`.

This lands in exactly the shape consumed by `sin_sq_le_rayleigh_deficit_div_gap` (`hC`, `hv₀`,
`hev`, `hgap`, `hμ₁`). -/
theorem plucker_eigenpair_ceiling {n : ℕ} (f : E →ₗ[ℝ] E)
    (u : OrthonormalBasis (Fin n) ℝ E) (lam : ℕ → ℝ) (hanti : Antitone lam)
    (hpos : ∀ i, 0 ≤ lam i) (hf : ∀ i, f (u i) = lam (i : ℕ) • u i)
    {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hgap : lam k < lam (k - 1)) :
    ∃ i₀ : Fin (Module.finrank ℝ (⋀[ℝ]^k E)),
      (conjExteriorMap k (onbTriv u k) (onbTriv u k) f).IsSymmetric
      ∧ conjExteriorMap k (onbTriv u k) (onbTriv u k) f
          (EuclideanSpace.basisFun _ ℝ i₀)
        = (∏ i ∈ Finset.range k, lam i) • EuclideanSpace.basisFun _ ℝ i₀
      ∧ ((∏ i ∈ Finset.range (k-1), lam i) * lam k) < (∏ i ∈ Finset.range k, lam i)
      ∧ ∀ w : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k E))),
          (inner ℝ w (EuclideanSpace.basisFun _ ℝ i₀) : ℝ) = 0 →
          (inner ℝ ((conjExteriorMap k (onbTriv u k) (onbTriv u k) f) w) w : ℝ)
            ≤ ((∏ i ∈ Finset.range (k-1), lam i) * lam k) * ‖w‖ ^ 2 := by
  classical
  set N := Module.finrank ℝ (⋀[ℝ]^k E) with hN
  set C := conjExteriorMap k (onbTriv u k) (onbTriv u k) f with hC
  -- the diagonal weight `c i = ∏_{a ∈ Sᵢ} lam a`.
  set c : Fin N → ℝ := fun i =>
    ∏ a ∈ ((wIndexEquiv u k).symm i : Set.powersetCard (Fin n) k).val, lam (a : ℕ) with hcdef
  -- the diagonalization: `C (basisFun i) = c i • basisFun i`.
  have hCdiag : ∀ i, C (EuclideanSpace.basisFun (Fin N) ℝ i)
      = c i • EuclideanSpace.basisFun (Fin N) ℝ i := by
    intro i
    rw [hC, conjExteriorMap_onbTriv_diag f u (fun j => lam (j : ℕ)) hf k]
  -- the top prefix embedding/set and its index `i₀`.
  set topEmb : Fin k ↪o Fin n :=
    { toFun := fun i => ⟨i, lt_of_lt_of_le i.2 hkn⟩
      inj' := fun i j h => Fin.ext (by simpa using congrArg Fin.val h)
      map_rel_iff' := Iff.rfl } with htopEmb
  set topSet : Set.powersetCard (Fin n) k := Set.powersetCard.ofFinEmbEquiv topEmb with htopSet
  set i₀ : Fin N := wIndexEquiv u k topSet with hi₀def
  have hS₀ : (wIndexEquiv u k).symm i₀ = topSet := by rw [hi₀def, Equiv.symm_apply_apply]
  have htopval : ∀ i : Fin k, (topEmb i : Fin n).val = (i : ℕ) := fun _ => rfl
  -- `∏_{a ∈ topSet} g a = ∏_{j} g (topEmb j)` for any `g`.
  have htopprod : ∀ g : Fin n → ℝ, ∏ a ∈ topSet.val, g a = ∏ j, g (topEmb j) := by
    intro g
    have hval : topSet.val = Finset.univ.image (topEmb) := by
      ext x
      rw [Finset.mem_image,
        show x ∈ topSet.val ↔ x ∈ topSet from Iff.rfl, htopSet,
        Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range, Set.mem_range]
      constructor
      · rintro ⟨j, hj⟩; exact ⟨j, Finset.mem_univ _, hj⟩
      · rintro ⟨j, _, hj⟩; exact ⟨j, hj⟩
    rw [hval, Finset.prod_image (fun x _ y _ h => topEmb.injective h)]
  -- the top weight `c i₀ = ∏_{i<k} lam i = μ₀`.
  set μ₀ : ℝ := ∏ i ∈ Finset.range k, lam i with hμ₀
  set μ₁ : ℝ := (∏ i ∈ Finset.range (k-1), lam i) * lam k with hμ₁
  have hci₀ : c i₀ = μ₀ := by
    rw [hcdef]; simp only
    rw [hS₀, htopprod (fun a => lam (a : ℕ)), hμ₀, Finset.prod_range fun i => lam i]
    exact Finset.prod_congr rfl (fun j _ => by simp only [htopval])
  -- maximality: `c i ≤ μ₀` for all i.
  have hmax : ∀ i, c i ≤ μ₀ := by
    intro i
    rw [hcdef]; simp only
    rw [hμ₀, Finset.prod_range fun j => lam j]
    have hconv : ∏ a ∈ ((wIndexEquiv u k).symm i : Set.powersetCard (Fin n) k).val, lam (a : ℕ)
        = ∏ a ∈ ((wIndexEquiv u k).symm i : Set.powersetCard (Fin n) k).val,
            (fun b : Fin n => lam (b : ℕ)) a := rfl
    rw [hconv]
    refine le_trans (prod_le_prod_top (fun b : Fin n => lam (b : ℕ)) ?_ ?_
      ((wIndexEquiv u k).symm i) topEmb htopval) ?_
    · exact fun a b hab => hanti (by exact_mod_cast (Fin.le_def.mp hab))
    · exact fun a => hpos _
    · exact le_of_eq (Finset.prod_congr rfl (fun j _ => by simp only [htopval]))
  -- second-largest: `c i ≤ μ₁` for `i ≠ i₀`.
  have hsecond : ∀ i, i ≠ i₀ → c i ≤ μ₁ := by
    intro i hi
    rw [hcdef]; simp only
    -- the enumeration of `Sᵢ` and the non-top fact.
    set S := ((wIndexEquiv u k).symm i : Set.powersetCard (Fin n) k) with hS
    set e := Set.powersetCard.ofFinEmbEquiv.symm S with he
    have hSne : S ≠ topSet := by
      intro h
      apply hi
      rw [hi₀def, ← h, hS, Equiv.apply_symm_apply]
    -- `∏_{a∈S} lam a = ∏_j lam (e j)`.
    have hprodeq : ∏ a ∈ (S : Finset (Fin n)), lam (a : ℕ) = ∏ j, lam (e j : ℕ) := by
      rw [he]; exact (prod_ofFinEmbEquiv_symm (fun a : Fin n => lam (a : ℕ)) S).symm
    rw [hprodeq]
    -- non-top: the images differ.
    have himgS : (S : Finset (Fin n)) = Finset.univ.image (fun j : Fin k => e j) := by
      have himg : (S : Finset (Fin n))
          = Finset.univ.image (Set.powersetCard.ofFinEmbEquiv.symm S) := by
        rw [Set.powersetCard.ofFinEmbEquiv_symm_apply, Finset.image_orderEmbOfFin_univ]
      rw [himg, he]
    have htopImg : topSet.val = Finset.univ.image topEmb := by
      have hval : topSet.val = Finset.univ.image (topEmb) := by
        ext x
        rw [Finset.mem_image,
          show x ∈ topSet.val ↔ x ∈ topSet from Iff.rfl, htopSet,
          Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range, Set.mem_range]
        constructor
        · rintro ⟨j, hj⟩; exact ⟨j, Finset.mem_univ _, hj⟩
        · rintro ⟨j, _, hj⟩; exact ⟨j, hj⟩
      exact hval
    have hImgNe : (Finset.univ.image (fun j : Fin k => e j) : Finset (Fin n))
        ≠ Finset.univ.image (fun i : Fin k => (⟨i, lt_of_lt_of_le i.2 hkn⟩ : Fin n)) := by
      intro h
      apply hSne
      apply Subtype.ext
      rw [show (S : Finset (Fin n)) = S.val from rfl, show topSet.val = topSet.val from rfl,
        himgS, htopImg, h]
      rfl
    -- top element of `S` is `≥ k`.
    have htopge : k ≤ (e ⟨k-1, by omega⟩ : ℕ) := top_elem_ge hk1 hkn e hImgNe
    -- specialize the product bound with `m = k-1`, i.e. `k = m+1`.
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k-1, by omega⟩
    rw [hμ₁, Nat.add_sub_cancel]
    have hbound := prod_le_second_aux (n := n) m lam hanti hpos e (by simpa using htopge)
    exact hbound
  -- assemble.
  refine ⟨i₀, diag_isSymmetric C c hCdiag, ?_, ?_, ?_⟩
  · rw [hCdiag i₀, hci₀]
  · have hpre_pos : 0 < ∏ i ∈ Finset.range (k-1), lam i := by
      apply Finset.prod_pos
      intro j hj
      rw [Finset.mem_range] at hj
      -- `lam j ≥ lam (k-1) > lam k ≥ 0`, since `j ≤ k-1` and `lam` antitone.
      have hjle : lam (k-1) ≤ lam j := hanti (by omega)
      exact lt_of_lt_of_le (lt_of_le_of_lt (hpos k) hgap) hjle
    change μ₁ < μ₀
    calc μ₁ = (∏ i ∈ Finset.range (k-1), lam i) * lam k := rfl
      _ < (∏ i ∈ Finset.range (k-1), lam i) * lam (k-1) := mul_lt_mul_of_pos_left hgap hpre_pos
      _ = μ₀ := by
          rw [hμ₀]
          obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hk1
          rw [Nat.add_comm 1 p, Nat.add_sub_cancel, Finset.prod_range_succ]
  · intro w hw
    refine diag_rayleigh_ceiling C c hCdiag i₀ hsecond ?_ w hw
    rw [hμ₁]
    have hprefix : 0 ≤ ∏ i ∈ Finset.range (k-1), lam i := Finset.prod_nonneg (fun _ _ => hpos _)
    exact mul_nonneg hprefix (hpos k)

open scoped Classical in
/-- **Witness-exposing Plücker bridge (eigenbasis coords).** Same as `plucker_eigenpair_ceiling`,
but with the top eigenvector index `i₀` produced *explicitly* as `wIndexEquiv u k topSet` (where
`topSet` is the top-`k` prefix subset), and with the extra identity pinning the standard basis
vector `basisFun i₀` to the explicit Hodge-trivialized wedge
`onbTriv u k (e_{u₀} ∧ ⋯ ∧ e_{u_{k-1}})` of the top-`k` eigenframe. This is the variant
`plucker_eigenpair_ceiling_standard'` transports to standard coordinates to expose the
band-projector frame wedge. -/
theorem plucker_eigenpair_ceiling' {n : ℕ} (f : E →ₗ[ℝ] E)
    (u : OrthonormalBasis (Fin n) ℝ E) (lam : ℕ → ℝ) (hanti : Antitone lam)
    (hpos : ∀ i, 0 ≤ lam i) (hf : ∀ i, f (u i) = lam (i : ℕ) • u i)
    {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hgap : lam k < lam (k - 1)) :
    ∃ i₀ : Fin (Module.finrank ℝ (⋀[ℝ]^k E)),
      EuclideanSpace.basisFun _ ℝ i₀
          = onbTriv u k (exteriorPower.ιMulti ℝ k
              (fun j : Fin k => u ⟨j, lt_of_lt_of_le j.2 hkn⟩))
      ∧ conjExteriorMap k (onbTriv u k) (onbTriv u k) f
          (EuclideanSpace.basisFun _ ℝ i₀)
        = (∏ i ∈ Finset.range k, lam i) • EuclideanSpace.basisFun _ ℝ i₀
      ∧ ((∏ i ∈ Finset.range (k-1), lam i) * lam k) < (∏ i ∈ Finset.range k, lam i)
      ∧ ∀ w : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k E))),
          (inner ℝ w (EuclideanSpace.basisFun _ ℝ i₀) : ℝ) = 0 →
          (inner ℝ ((conjExteriorMap k (onbTriv u k) (onbTriv u k) f) w) w : ℝ)
            ≤ ((∏ i ∈ Finset.range (k-1), lam i) * lam k) * ‖w‖ ^ 2 := by
  classical
  set N := Module.finrank ℝ (⋀[ℝ]^k E) with hN
  set C := conjExteriorMap k (onbTriv u k) (onbTriv u k) f with hC
  set c : Fin N → ℝ := fun i =>
    ∏ a ∈ ((wIndexEquiv u k).symm i : Set.powersetCard (Fin n) k).val, lam (a : ℕ) with hcdef
  have hCdiag : ∀ i, C (EuclideanSpace.basisFun (Fin N) ℝ i)
      = c i • EuclideanSpace.basisFun (Fin N) ℝ i := by
    intro i
    rw [hC, conjExteriorMap_onbTriv_diag f u (fun j => lam (j : ℕ)) hf k]
  set topEmb : Fin k ↪o Fin n :=
    { toFun := fun i => ⟨i, lt_of_lt_of_le i.2 hkn⟩
      inj' := fun i j h => Fin.ext (by simpa using congrArg Fin.val h)
      map_rel_iff' := Iff.rfl } with htopEmb
  set topSet : Set.powersetCard (Fin n) k := Set.powersetCard.ofFinEmbEquiv topEmb with htopSet
  set i₀ : Fin N := wIndexEquiv u k topSet with hi₀def
  have hS₀ : (wIndexEquiv u k).symm i₀ = topSet := by rw [hi₀def, Equiv.symm_apply_apply]
  have htopval : ∀ i : Fin k, (topEmb i : Fin n).val = (i : ℕ) := fun _ => rfl
  have htopprod : ∀ g : Fin n → ℝ, ∏ a ∈ topSet.val, g a = ∏ j, g (topEmb j) := by
    intro g
    have hval : topSet.val = Finset.univ.image (topEmb) := by
      ext x
      rw [Finset.mem_image,
        show x ∈ topSet.val ↔ x ∈ topSet from Iff.rfl, htopSet,
        Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range, Set.mem_range]
      constructor
      · rintro ⟨j, hj⟩; exact ⟨j, Finset.mem_univ _, hj⟩
      · rintro ⟨j, _, hj⟩; exact ⟨j, hj⟩
    rw [hval, Finset.prod_image (fun x _ y _ h => topEmb.injective h)]
  set μ₀ : ℝ := ∏ i ∈ Finset.range k, lam i with hμ₀
  set μ₁ : ℝ := (∏ i ∈ Finset.range (k-1), lam i) * lam k with hμ₁
  have hci₀ : c i₀ = μ₀ := by
    rw [hcdef]; simp only
    rw [hS₀, htopprod (fun a => lam (a : ℕ)), hμ₀, Finset.prod_range fun i => lam i]
    exact Finset.prod_congr rfl (fun j _ => by simp only [htopval])
  have hmax : ∀ i, c i ≤ μ₀ := by
    intro i
    rw [hcdef]; simp only
    rw [hμ₀, Finset.prod_range fun j => lam j]
    have hconv : ∏ a ∈ ((wIndexEquiv u k).symm i : Set.powersetCard (Fin n) k).val, lam (a : ℕ)
        = ∏ a ∈ ((wIndexEquiv u k).symm i : Set.powersetCard (Fin n) k).val,
            (fun b : Fin n => lam (b : ℕ)) a := rfl
    rw [hconv]
    refine le_trans (prod_le_prod_top (fun b : Fin n => lam (b : ℕ)) ?_ ?_
      ((wIndexEquiv u k).symm i) topEmb htopval) ?_
    · exact fun a b hab => hanti (by exact_mod_cast (Fin.le_def.mp hab))
    · exact fun a => hpos _
    · exact le_of_eq (Finset.prod_congr rfl (fun j _ => by simp only [htopval]))
  have hsecond : ∀ i, i ≠ i₀ → c i ≤ μ₁ := by
    intro i hi
    rw [hcdef]; simp only
    set S := ((wIndexEquiv u k).symm i : Set.powersetCard (Fin n) k) with hS
    set e := Set.powersetCard.ofFinEmbEquiv.symm S with he
    have hSne : S ≠ topSet := by
      intro h
      apply hi
      rw [hi₀def, ← h, hS, Equiv.apply_symm_apply]
    have hprodeq : ∏ a ∈ (S : Finset (Fin n)), lam (a : ℕ) = ∏ j, lam (e j : ℕ) := by
      rw [he]; exact (prod_ofFinEmbEquiv_symm (fun a : Fin n => lam (a : ℕ)) S).symm
    rw [hprodeq]
    have himgS : (S : Finset (Fin n)) = Finset.univ.image (fun j : Fin k => e j) := by
      have himg : (S : Finset (Fin n))
          = Finset.univ.image (Set.powersetCard.ofFinEmbEquiv.symm S) := by
        rw [Set.powersetCard.ofFinEmbEquiv_symm_apply, Finset.image_orderEmbOfFin_univ]
      rw [himg, he]
    have htopImg : topSet.val = Finset.univ.image topEmb := by
      have hval : topSet.val = Finset.univ.image (topEmb) := by
        ext x
        rw [Finset.mem_image,
          show x ∈ topSet.val ↔ x ∈ topSet from Iff.rfl, htopSet,
          Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range, Set.mem_range]
        constructor
        · rintro ⟨j, hj⟩; exact ⟨j, Finset.mem_univ _, hj⟩
        · rintro ⟨j, _, hj⟩; exact ⟨j, hj⟩
      exact hval
    have hImgNe : (Finset.univ.image (fun j : Fin k => e j) : Finset (Fin n))
        ≠ Finset.univ.image (fun i : Fin k => (⟨i, lt_of_lt_of_le i.2 hkn⟩ : Fin n)) := by
      intro h
      apply hSne
      apply Subtype.ext
      rw [show (S : Finset (Fin n)) = S.val from rfl, show topSet.val = topSet.val from rfl,
        himgS, htopImg, h]
      rfl
    have htopge : k ≤ (e ⟨k-1, by omega⟩ : ℕ) := top_elem_ge hk1 hkn e hImgNe
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k-1, by omega⟩
    rw [hμ₁, Nat.add_sub_cancel]
    have hbound := prod_le_second_aux (n := n) m lam hanti hpos e (by simpa using htopge)
    exact hbound
  refine ⟨i₀, ?_, ?_, ?_, ?_⟩
  · -- `basisFun i₀ = onbTriv u k (wedge of top-k eigenframe)`.
    have hwedge : (u.toBasis.exteriorPower k) topSet
        = exteriorPower.ιMulti ℝ k (fun j : Fin k => u ⟨j, lt_of_lt_of_le j.2 hkn⟩) := by
      rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
      have hsymm : Set.powersetCard.ofFinEmbEquiv.symm topSet = topEmb := by
        rw [htopSet, Equiv.symm_apply_apply]
      rw [show (⇑u.toBasis ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm topSet))
          = fun j : Fin k => u ⟨j, lt_of_lt_of_le j.2 hkn⟩ by
        funext j
        rw [Function.comp_apply, hsymm, OrthonormalBasis.coe_toBasis]
        rfl]
    rw [← onbTriv_wedge_eq_basisFun u k i₀, hS₀, hwedge]
  · rw [hCdiag i₀, hci₀]
  · have hpre_pos : 0 < ∏ i ∈ Finset.range (k-1), lam i := by
      apply Finset.prod_pos
      intro j hj
      rw [Finset.mem_range] at hj
      have hjle : lam (k-1) ≤ lam j := hanti (by omega)
      exact lt_of_lt_of_le (lt_of_le_of_lt (hpos k) hgap) hjle
    change μ₁ < μ₀
    calc μ₁ = (∏ i ∈ Finset.range (k-1), lam i) * lam k := rfl
      _ < (∏ i ∈ Finset.range (k-1), lam i) * lam (k-1) := mul_lt_mul_of_pos_left hgap hpre_pos
      _ = μ₀ := by
          rw [hμ₀]
          obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hk1
          rw [Nat.add_comm 1 p, Nat.add_sub_cancel, Finset.prod_range_succ]
  · intro w hw
    refine diag_rayleigh_ceiling C c hCdiag i₀ hsecond ?_ w hw
    rw [hμ₁]
    have hprefix : 0 ≤ ∏ i ∈ Finset.range (k-1), lam i := Finset.prod_nonneg (fun _ _ => hpos _)
    exact mul_nonneg hprefix (hpos k)

/-! ### The reconciliation bridge: transporting the Plücker eigenpair into standard coordinates

`plucker_eigenpair_ceiling` produces the top eigenpair and second-eigenvalue ceiling of the
conjugated compound `conjExteriorMap k (onbTriv u) (onbTriv u) f` in the **eigenbasis** wedge
trivialization (`u` = an orthonormal eigenbasis of the symmetric `f`). The Rayleigh-deficit input
`rayleigh_deficit_le` lives in the **standard** trivialization, where the conjugated compound is
`toEuclideanLin (compoundMatrix k ·)` (the compound matrix). These are the *same* abstract operator
`⋀^k f` viewed through two isometric o.n.-basis wedge trivializations, hence unitarily equivalent by
the orthogonal change-of-coordinates `onbChange`. Since an isometry preserves the inner product, the
Rayleigh quotient is trivialization-independent; this lets `sin_sq_le_rayleigh_deficit_div_gap` be
applied in eigenbasis coordinates with the deficit supplied from standard coordinates. -/

section Reconciliation

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open scoped Classical in
/-- **Conjugation of `conjExteriorMap` under change of o.n.-wedge trivialization.** For the *same*
endomorphism `f`, the conjugated compounds in two o.n.-basis wedge trivializations `onbTriv b`,
`onbTriv b'` are related by the L2 isometry `W = onbChange b b' k`:
`conjExteriorMap (onbTriv b') f = W ∘ conjExteriorMap (onbTriv b) f ∘ W⁻¹`. -/
private lemma conjExteriorMap_onbChange_conj {ιE ιE' : Type*}
    [Fintype ιE] [LinearOrder ιE] [Fintype ιE'] [LinearOrder ιE']
    (b : OrthonormalBasis ιE ℝ E) (b' : OrthonormalBasis ιE' ℝ E) (k : ℕ) (f : E →ₗ[ℝ] E)
    (p : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k E)))) :
    conjExteriorMap k (onbTriv b' k) (onbTriv b' k) f p
      = onbChange b b' k (conjExteriorMap k (onbTriv b k) (onbTriv b k) f
          ((onbChange b b' k).symm p)) := by
  change conjExteriorMap k (onbTriv b' k) (onbTriv b' k) f p
      = onbTriv b' k ((onbTriv b k).symm (conjExteriorMap k (onbTriv b k) (onbTriv b k) f
          (onbTriv b k ((onbTriv b' k).symm p))))
  simp only [conjExteriorMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

open scoped Classical in
/-- **Rayleigh-quotient transport.** Because `W = onbChange b b' k` is an L2 isometry and
`conjExteriorMap (onbTriv b') f = W ∘ conjExteriorMap (onbTriv b) f ∘ W⁻¹`, the Rayleigh quotient
of the standard-trivialization compound at `y` equals that of the eigenbasis-trivialization compound
at `W y`. (Here `b` is the standard, `b'` the eigenbasis.) -/
private lemma rayleigh_onbChange_eq {ιE ιE' : Type*}
    [Fintype ιE] [LinearOrder ιE] [Fintype ιE'] [LinearOrder ιE']
    (b : OrthonormalBasis ιE ℝ E) (b' : OrthonormalBasis ιE' ℝ E) (k : ℕ) (f : E →ₗ[ℝ] E)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k E)))) :
    (inner ℝ (conjExteriorMap k (onbTriv b k) (onbTriv b k) f y) y : ℝ)
      = (inner ℝ (conjExteriorMap k (onbTriv b' k) (onbTriv b' k) f (onbChange b b' k y))
          (onbChange b b' k y) : ℝ) := by
  rw [conjExteriorMap_onbChange_conj b b' k f (onbChange b b' k y),
    LinearIsometryEquiv.symm_apply_apply,
    (onbChange b b' k).inner_map_map]

open scoped Classical in
/-- **Transport of a top-eigenpair + second-eigenvalue ceiling across the change of o.n.-wedge
trivialization.** Given the top eigenpair (`hev`) and the `μ₁`-ceiling on the orthogonal complement
(`hceil`) of the conjugated compound in the `b'`-trivialization (`b'` = the eigenbasis), the same
data transports — via the orthogonal `W = onbChange b b' k` — to the `b`-trivialization (`b` = the
standard basis): the eigenvector is `v₀ = W⁻¹ (basisFun i₀)`, the eigenvalue/gap are unchanged, and
the Rayleigh ceiling holds verbatim on `v₀ᗮ`. This is the abstract (matrix-free) reconciliation core
that feeds `sin_sq_le_rayleigh_deficit_div_gap` once `conjExteriorMap (onbTriv b) f` is identified
with the standard compound. -/
lemma eigenpair_ceiling_transport {ιE ιE' : Type*}
    [Fintype ιE] [LinearOrder ιE] [Fintype ιE'] [LinearOrder ιE']
    (b : OrthonormalBasis ιE ℝ E) (b' : OrthonormalBasis ιE' ℝ E) (k : ℕ) (f : E →ₗ[ℝ] E)
    (i₀ : Fin (Module.finrank ℝ (⋀[ℝ]^k E))) (μ₀ μ₁ : ℝ)
    (hev : conjExteriorMap k (onbTriv b' k) (onbTriv b' k) f
        (EuclideanSpace.basisFun _ ℝ i₀) = μ₀ • EuclideanSpace.basisFun _ ℝ i₀)
    (hceil : ∀ w : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k E))),
        (inner ℝ w (EuclideanSpace.basisFun _ ℝ i₀) : ℝ) = 0 →
        (inner ℝ (conjExteriorMap k (onbTriv b' k) (onbTriv b' k) f w) w : ℝ) ≤ μ₁ * ‖w‖ ^ 2) :
    ‖(onbChange b b' k).symm (EuclideanSpace.basisFun _ ℝ i₀)‖ = 1
    ∧ conjExteriorMap k (onbTriv b k) (onbTriv b k) f
        ((onbChange b b' k).symm (EuclideanSpace.basisFun _ ℝ i₀))
        = μ₀ • (onbChange b b' k).symm (EuclideanSpace.basisFun _ ℝ i₀)
    ∧ ∀ w : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k E))),
        (inner ℝ w ((onbChange b b' k).symm (EuclideanSpace.basisFun _ ℝ i₀)) : ℝ) = 0 →
        (inner ℝ (conjExteriorMap k (onbTriv b k) (onbTriv b k) f w) w : ℝ) ≤ μ₁ * ‖w‖ ^ 2 := by
  set W := onbChange b b' k with hW
  set e₀ := EuclideanSpace.basisFun (Fin (Module.finrank ℝ (⋀[ℝ]^k E))) ℝ i₀ with he₀
  -- conjugation `C_b p = W⁻¹ (C_{b'} (W p))`.
  have hconj : ∀ p, conjExteriorMap k (onbTriv b k) (onbTriv b k) f p
      = W.symm (conjExteriorMap k (onbTriv b' k) (onbTriv b' k) f (W p)) := by
    intro p
    rw [hW]
    have hb := conjExteriorMap_onbChange_conj b b' k f (onbChange b b' k p)
    rw [LinearIsometryEquiv.symm_apply_apply] at hb
    rw [hb, LinearIsometryEquiv.symm_apply_apply]
  have hWv₀ : W (W.symm e₀) = e₀ := LinearIsometryEquiv.apply_symm_apply W e₀
  refine ⟨?_, ?_, ?_⟩
  · rw [LinearIsometryEquiv.norm_map, he₀, EuclideanSpace.basisFun_apply,
      PiLp.norm_single, norm_one]
  · rw [hconj (W.symm e₀), hWv₀, hev, map_smul]
  · intro w hw
    rw [hconj w]
    have hWperp : (inner ℝ (W w) e₀ : ℝ) = 0 := by
      rw [← hWv₀, W.inner_map_map]; exact hw
    have hR : (inner ℝ (W.symm (conjExteriorMap k (onbTriv b' k) (onbTriv b' k) f (W w))) w : ℝ)
        = (inner ℝ (conjExteriorMap k (onbTriv b' k) (onbTriv b' k) f (W w)) (W w) : ℝ) := by
      rw [← W.inner_map_map (W.symm _) w, LinearIsometryEquiv.apply_symm_apply]
    rw [hR]
    have hc := hceil (W w) hWperp
    rwa [W.norm_map] at hc

end Reconciliation

/-! ### The Plücker eigenpair in standard (compound-matrix) coordinates

The matrix-level packaging `plucker_eigenpair_ceiling_standard` transports
`plucker_eigenpair_ceiling` through the orthogonal change-of-trivialization `onbChange`
(via `eigenpair_ceiling_transport`) into the **standard** wedge trivialization
`onbTriv (EuclideanSpace.basisFun (Fin d) ℝ)`, where the compound bridge
`conjExteriorMap_eq_toEuclideanLin_compound` identifies the conjugated compound of
`toEuclideanLin Q` with `toEuclideanLin (compoundMatrix k Q)` — exactly the operator consumed by
the off-diagonal residual lemmas `norm_offdiag_residual_compound_le` /
`perturbed_compound_gram_ceiling`.

A single declaration combining plucker ∘ transport ∘ matrix-identification times out even at
`maxHeartbeats 1600000`. The fix is to *split* the heavy matrix-identification step into an
isolated scoped lemma (`conjExteriorMap_basisFun_toEuclideanLin_eq_compound` below — a thin alias
of the compound bridge, kept separate so its `⋀^k` finrank elaboration cost is contained) and to
keep the transport/assembly in its own scoped declaration. -/

section StandardCoords

variable {d : ℕ}

set_option maxHeartbeats 800000 in -- heavy elaboration; exceeds the default budget
-- The `⋀^k`-finrank-indexed `EuclideanSpace` statement is expensive to elaborate.
/-- **(A) — the isolated matrix-identification step.** Through the standard orthonormal-wedge
trivialization (`onbTriv (EuclideanSpace.basisFun (Fin d) ℝ)`), the conjugated compound of
`toEuclideanLin M` is `toEuclideanLin (compoundMatrix k M)`. This is a thin re-export of
`conjExteriorMap_eq_toEuclideanLin_compound`, isolated in its own scoped declaration so
that the (heavy) `⋀^k` finrank-indexed elaboration is paid here exactly once, keeping the
assembled `plucker_eigenpair_ceiling_standard` under budget. -/
theorem conjExteriorMap_basisFun_toEuclideanLin_eq_compound
    (k : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) :
    conjExteriorMap k (onbTriv (EuclideanSpace.basisFun (Fin d) ℝ) k)
        (onbTriv (EuclideanSpace.basisFun (Fin d) ℝ) k) (Matrix.toEuclideanLin M)
      = Matrix.toEuclideanLin (compoundMatrix k M) :=
  conjExteriorMap_eq_toEuclideanLin_compound k M

set_option maxHeartbeats 1200000 in -- heavy elaboration; exceeds the default budget
-- The `⋀^k`-finrank-indexed `EuclideanSpace` statement is expensive to elaborate.
/-- **(B) — `plucker_eigenpair_ceiling_standard`.** The Plücker eigenpair + second-eigenvalue
ceiling in *standard* compound-matrix coordinates. For a symmetric PSD `f = toEuclideanLin Q` with
orthonormal eigenbasis `u` and antitone nonnegative eigenvalues `lam`, at a genuine gap
`lam k < lam (k-1)`, the operator `toEuclideanLin (compoundMatrix k Q)` (`= ⋀^k Q` in the standard
trivialization) has:

* **top eigenpair:** a unit vector `v₀` with `toEuclideanLin (compoundMatrix k Q) v₀ = μ₀ • v₀`,
  `μ₀ = ∏_{i<k} lam i`;
* **the gap:** `μ₁ < μ₀` with `μ₁ = (∏_{i<k-1} lam i)·lam k`;
* **second-eigenvalue ceiling:** `∀ w ⊥ v₀, ⟪(toEuclideanLin (compoundMatrix k Q)) w, w⟫ ≤ μ₁‖w‖²`.

Assembled from `plucker_eigenpair_ceiling` (eigenbasis-wedge coords) → `eigenpair_ceiling_transport`
(`onbChange` to standard `basisFun` coords) → `conjExteriorMap_basisFun_toEuclideanLin_eq_compound`
(matrix identification, isolated in (A)). This is the top spectral data of `Cₙ = ⋀^k Qₙ` that
`norm_offdiag_residual_compound_le` / `perturbed_compound_gram_ceiling` consume. -/
theorem plucker_eigenpair_ceiling_standard {n : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (u : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin d)))
    (lam : ℕ → ℝ) (hanti : Antitone lam) (hpos : ∀ i, 0 ≤ lam i)
    (hf : ∀ i, Matrix.toEuclideanLin Q (u i) = lam (i : ℕ) • u i)
    {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hgap : lam k < lam (k - 1)) :
    ∃ v₀ : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d))))),
      ‖v₀‖ = 1
      ∧ Matrix.toEuclideanLin (compoundMatrix k Q) v₀
          = (∏ i ∈ Finset.range k, lam i) • v₀
      ∧ ((∏ i ∈ Finset.range (k-1), lam i) * lam k) < (∏ i ∈ Finset.range k, lam i)
      ∧ ∀ w : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d))))),
          (inner ℝ w v₀ : ℝ) = 0 →
          (inner ℝ (Matrix.toEuclideanLin (compoundMatrix k Q) w) w : ℝ)
            ≤ ((∏ i ∈ Finset.range (k-1), lam i) * lam k) * ‖w‖ ^ 2 := by
  classical
  -- eigenbasis-coords Plücker data (top eigenpair + ceiling).
  obtain ⟨i₀, _hsym, hev, hgapμ, hceil⟩ :=
    plucker_eigenpair_ceiling (Matrix.toEuclideanLin Q) u lam hanti hpos hf hk1 hkn hgap
  -- transport to standard (`basisFun`) wedge coordinates via the orthogonal `onbChange`.
  obtain ⟨hv₀norm, hv₀ev, hv₀ceil⟩ :=
    eigenpair_ceiling_transport (EuclideanSpace.basisFun (Fin d) ℝ) u k
      (Matrix.toEuclideanLin Q) i₀ _ _ hev hceil
  -- the transported eigenvector, named once.
  refine ⟨(onbChange (EuclideanSpace.basisFun (Fin d) ℝ) u k).symm
      (EuclideanSpace.basisFun _ ℝ i₀), hv₀norm, ?_, hgapμ, ?_⟩
  · -- identify the standard-coords conjugated compound with the compound matrix (step (A)).
    rw [← conjExteriorMap_basisFun_toEuclideanLin_eq_compound k Q]
    exact hv₀ev
  · intro w hw
    rw [← conjExteriorMap_basisFun_toEuclideanLin_eq_compound k Q]
    exact hv₀ceil w hw

/-- The inverse of the change-of-trivialization isometry: `(onbChange b b').symm` sends `q` to
`onbTriv b ((onbTriv b').symm q)`. -/
private lemma onbChange_symm_apply {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ιE ιE' : Type*} [Fintype ιE] [LinearOrder ιE] [Fintype ιE'] [LinearOrder ιE']
    (b : OrthonormalBasis ιE ℝ E) (b' : OrthonormalBasis ιE' ℝ E) (k : ℕ)
    (q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k E)))) :
    (onbChange b b' k).symm q = onbTriv b k ((onbTriv b' k).symm q) := by
  classical
  apply (onbChange b b' k).injective
  rw [LinearIsometryEquiv.apply_symm_apply, onbChange_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

set_option maxHeartbeats 1600000 in -- heavy elaboration; exceeds the default budget
-- The `⋀^k`-finrank-indexed `EuclideanSpace` statement is expensive to elaborate.
/-- **(B') — witness-exposing `plucker_eigenpair_ceiling_standard`.** Same spectral data as
`plucker_eigenpair_ceiling_standard`, but with the top eigenvector produced *explicitly* as the
standard-trivialization wedge `w₀ = onbTriv basisFun k (e_{u₀} ∧ ⋯ ∧ e_{u_{k-1}})` of the top-`k`
eigenframe of `u` — exactly the Plücker top eigenvector that the band-projector frame wedge equals.
This is the variant whose witness can be plugged into `det_transpose_mul_eq_inner_onbTriv` to
discharge the `hdet` hypothesis of `Oseledets.norm_bandProjector_succ_sub_le`. -/
theorem plucker_eigenpair_ceiling_standard' {n : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (u : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin d)))
    (lam : ℕ → ℝ) (hanti : Antitone lam) (hpos : ∀ i, 0 ≤ lam i)
    (hf : ∀ i, Matrix.toEuclideanLin Q (u i) = lam (i : ℕ) • u i)
    {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hgap : lam k < lam (k - 1)) :
    (‖onbTriv (EuclideanSpace.basisFun (Fin d) ℝ) k
        (exteriorPower.ιMulti ℝ k (fun j : Fin k => u ⟨j, lt_of_lt_of_le j.2 hkn⟩))‖ = 1)
    ∧ Matrix.toEuclideanLin (compoundMatrix k Q)
        (onbTriv (EuclideanSpace.basisFun (Fin d) ℝ) k
          (exteriorPower.ιMulti ℝ k (fun j : Fin k => u ⟨j, lt_of_lt_of_le j.2 hkn⟩)))
        = (∏ i ∈ Finset.range k, lam i)
          • onbTriv (EuclideanSpace.basisFun (Fin d) ℝ) k
              (exteriorPower.ιMulti ℝ k (fun j : Fin k => u ⟨j, lt_of_lt_of_le j.2 hkn⟩))
    ∧ ((∏ i ∈ Finset.range (k-1), lam i) * lam k) < (∏ i ∈ Finset.range k, lam i)
    ∧ ∀ w : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d))))),
        (inner ℝ w (onbTriv (EuclideanSpace.basisFun (Fin d) ℝ) k
            (exteriorPower.ιMulti ℝ k (fun j : Fin k => u ⟨j, lt_of_lt_of_le j.2 hkn⟩))) : ℝ) = 0 →
        (inner ℝ (Matrix.toEuclideanLin (compoundMatrix k Q) w) w : ℝ)
          ≤ ((∏ i ∈ Finset.range (k-1), lam i) * lam k) * ‖w‖ ^ 2 := by
  classical
  -- eigenbasis-coords data with the EXPLICIT top index and its wedge characterization.
  obtain ⟨i₀, hbasis, hev, hgapμ, hceil⟩ :=
    plucker_eigenpair_ceiling' (Matrix.toEuclideanLin Q) u lam hanti hpos hf hk1 hkn hgap
  -- transport to standard (`basisFun`) wedge coordinates.
  obtain ⟨hv₀norm, hv₀ev, hv₀ceil⟩ :=
    eigenpair_ceiling_transport (EuclideanSpace.basisFun (Fin d) ℝ) u k
      (Matrix.toEuclideanLin Q) i₀ _ _ hev hceil
  -- the transported witness equals the explicit standard wedge `w₀`.
  set w₀ := onbTriv (EuclideanSpace.basisFun (Fin d) ℝ) k
      (exteriorPower.ιMulti ℝ k (fun j : Fin k => u ⟨j, lt_of_lt_of_le j.2 hkn⟩)) with hw₀
  have hwit : (onbChange (EuclideanSpace.basisFun (Fin d) ℝ) u k).symm
      (EuclideanSpace.basisFun _ ℝ i₀) = w₀ := by
    rw [onbChange_symm_apply, hbasis, LinearEquiv.symm_apply_apply, hw₀]
  rw [hwit] at hv₀norm hv₀ev hv₀ceil
  refine ⟨hv₀norm, ?_, hgapμ, ?_⟩
  · rw [← conjExteriorMap_basisFun_toEuclideanLin_eq_compound k Q]; exact hv₀ev
  · intro w hw
    rw [← conjExteriorMap_basisFun_toEuclideanLin_eq_compound k Q]
    exact hv₀ceil w hw

/-- **(C) — the Plücker frame ↔ wedge determinant bridge through the *standard* trivialization.**
The `hdet` plumbing fact for `Oseledets.norm_bandProjector_succ_sub_le`, expressed through the same
trivialization `onbTriv basisFun` in which `plucker_eigenpair_ceiling_standard'` produces its top
eigenvectors: `det(UᵀV) = ⟪onbTriv basisFun (⋀ V-cols), onbTriv basisFun (⋀ U-cols)⟫`. Together with
`plucker_eigenpair_ceiling_standard'` (whose `v₀`/`vt` ARE these column wedges), this discharges the
`hdet` hypothesis with `v₀ = U-column wedge`, `vt = V-column wedge`. -/
theorem det_transpose_mul_eq_inner_onbTriv {k : ℕ} (U V : Matrix (Fin d) (Fin k) ℝ) :
    (Uᵀ * V).det
      = (inner ℝ
          (onbTriv (EuclideanSpace.basisFun (Fin d) ℝ) k
            (exteriorPower.ιMulti ℝ k (fun j => colE V j)))
          (onbTriv (EuclideanSpace.basisFun (Fin d) ℝ) k
            (exteriorPower.ιMulti ℝ k (fun i => colE U i))) : ℝ) := by
  classical
  rw [inner_onbTriv, hodgeForm_ιMulti]
  have hmat : Uᵀ * V
      = Matrix.of (fun i j => (inner ℝ (colE V j) (colE U i) : ℝ)) := by
    ext i j
    rw [Matrix.of_apply, inner_colE, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl
      (fun a _ => by rw [Matrix.transpose_apply, Matrix.transpose_apply]; ring)
  rw [hmat]

end StandardCoords

end Plucker
end Oseledets.ExteriorNorm

end
