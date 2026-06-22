/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Oseledets.Cocycle.Basic

/-!
# The fixed framing algebra `E ≃ₐ Matrix` of an inner-product model fibre

For a finite-dimensional real inner-product space `E`, conjugating endomorphisms of `E` by a fixed
orthonormal frame `E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E))` and identifying
`EuclideanSpace`-endomorphisms with matrices (`Matrix.toEuclideanCLM`) packages a **globally
constant** algebra equivalence
`frameAlg E : (E →L[ℝ] E) ≃ₐ[ℝ] Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ`.

This is the algebraic heart of the bundle-to-matrix reduction of the manifold Oseledets MET: because
it is an algebra equivalence it sends `1 ↦ 1` and products to products, turning a product of model-
fibre endomorphisms (the framed tangent cocycle) into a matrix cocycle without side conditions; it
preserves the L2 operator norm (the framing is an isometry), so the matrix integrability hypotheses
are exactly the genuine `log⁺‖·‖` ones; and it is continuous and (entrywise) measurable, so a
measurable model-fibre cocycle becomes a measurable matrix cocycle.

This file isolates the framing algebra so that both the canonical-derivative headline
(`Frontier/Issue2/DerivativeCocycleManifold.lean`) and the unconditional framed-cocycle MET
(`Frontier/Issue2/UnconditionalMET.lean`) can share it without colliding over the `mfderivHom`
definition that their respective measurability imports each introduce.

## Main definitions

* `Frontier.Issue2.modelDim E` — `finrank ℝ E`, the matrix side.
* `Frontier.Issue2.frameEquiv E` / `frameCLE E` — the fixed orthonormal framing (isometry / CLE).
* `Frontier.Issue2.frameAlg E` — the framing algebra equivalence `(E →L[ℝ] E) ≃ₐ Matrix`.

## Main results

* `Frontier.Issue2.norm_frameAlg` — the framing preserves the L2 operator norm.
* `Frontier.Issue2.continuous_frameAlg` / `measurable_frameAlg` — continuity / measurability.
-/

open scoped Matrix.Norms.L2Operator

namespace Frontier.Issue2

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable (E) in
/-- The model dimension: `finrank ℝ E`. The tangent spaces of `M` are all (definitionally) `E`, so
this is the fibre dimension of the tangent bundle, and the side of the cocycle matrices. -/
abbrev modelDim : ℕ := Module.finrank ℝ E

variable (E) in
/-- The **fixed framing** of the model fibre: a linear isometry
`E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E))`, obtained from an arbitrary chosen orthonormal
basis (`stdOrthonormalBasis`). Conjugating a tangent-space endomorphism by this isometry turns it
into an endomorphism of `EuclideanSpace`, hence (via `Matrix.toEuclideanCLM`) into a matrix.

Crucially this framing is **globally constant** — it does not depend on the base point `x` — because
Mathlib models every tangent space `TangentSpace I x` on the *same* fixed space `E`. This is exactly
the measurable bundle trivialisation required by the manifold MET, here in its simplest (constant)
incarnation. -/
def frameEquiv : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (modelDim E)) :=
  (stdOrthonormalBasis ℝ E).repr

variable (E) in
/-- The framing as a *continuous linear equivalence* `E ≃L[ℝ] EuclideanSpace ℝ (Fin (modelDim E))`,
the underlying CLE of `frameEquiv`. Conjugating endomorphisms of `E` by `frameCLE` lands in
endomorphisms of `EuclideanSpace`. -/
def frameCLE : E ≃L[ℝ] EuclideanSpace ℝ (Fin (modelDim E)) :=
  (frameEquiv E).toContinuousLinearEquiv

@[simp] theorem frameCLE_apply (v : E) : frameCLE E v = frameEquiv E v := rfl

@[simp] theorem frameCLE_symm_apply (w : EuclideanSpace ℝ (Fin (modelDim E))) :
    (frameCLE E).symm w = (frameEquiv E).symm w := rfl

theorem norm_frameCLE (v : E) : ‖frameCLE E v‖ = ‖v‖ := (frameEquiv E).norm_map v

theorem norm_frameCLE_symm (w : EuclideanSpace ℝ (Fin (modelDim E))) :
    ‖(frameCLE E).symm w‖ = ‖w‖ := (frameEquiv E).symm.norm_map w

variable (E) in
/-- The **framing algebra isomorphism**: conjugation by `frameCLE` followed by `toEuclideanCLM.symm`,
packaged as an algebra equivalence
`(E →L[ℝ] E) ≃ₐ[ℝ] Matrix (Fin (modelDim E)) (Fin (modelDim E)) ℝ`.

Because it is an algebra equivalence it sends `1 ↦ 1` and products to products; this is precisely
what turns the *bundle* cocycle (a product of endomorphisms along the orbit) into a *matrix* cocycle
without any side conditions. It is the algebraic heart of the bundle-to-matrix reduction. (Continuity,
needed only for the measurability of the matrix generator, is recorded separately in
`continuous_frameAlg`.) -/
def frameAlg : (E →L[ℝ] E) ≃ₐ[ℝ] Matrix (Fin (modelDim E)) (Fin (modelDim E)) ℝ :=
  (frameCLE E).conjContinuousAlgEquiv.toAlgEquiv.trans
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin (modelDim E))).symm.toAlgEquiv

@[simp] theorem frameAlg_apply (L : E →L[ℝ] E) :
    frameAlg E L =
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin (modelDim E))).symm
        ((frameCLE E).conjContinuousAlgEquiv L) :=
  rfl

/-- The framing `frameAlg E` is continuous: it is `toEuclideanCLM.symm ∘ conjugation-by-frameCLE`,
where conjugation is continuous and `toEuclideanCLM.symm` is an `ℝ`-linear map between
finite-dimensional spaces (hence continuous). Used for the measurability of the matrix generator. -/
theorem continuous_frameAlg : Continuous (frameAlg E) := by
  have h1 : Continuous (frameCLE E).conjContinuousAlgEquiv :=
    (frameCLE E).conjContinuousAlgEquiv.continuous
  -- `toEuclideanCLM.symm` as an `ℝ`-linear map between finite-dimensional spaces is continuous
  have h2 : Continuous
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin (modelDim E))).symm.toAlgEquiv.toLinearMap :=
    LinearMap.continuous_of_finiteDimensional _
  exact h2.comp h1

/-- The image of an endomorphism `L : E →L[ℝ] E` under the conjugation `frameCLE ∘L L ∘L frameCLE⁻¹`
acts on `EuclideanSpace` with the same operator norm as `L`: `frameCLE` and its inverse are
isometries (the underlying maps of the `LinearIsometryEquiv` `frameEquiv`), so conjugation by them
preserves the operator norm (`opNorm_comp_le` both ways with `norm_map`). -/
theorem norm_conj_frameCLE (L : E →L[ℝ] E) :
    ‖(frameCLE E).conjContinuousAlgEquiv L‖ = ‖L‖ := by
  rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply]
  -- the underlying maps of `frameCLE`, `frameCLE.symm` are isometries
  have hfwd : ∀ v : E, ‖(frameCLE E) v‖ = ‖v‖ := norm_frameCLE
  have hinv : ∀ w : EuclideanSpace ℝ (Fin (modelDim E)), ‖(frameCLE E).symm w‖ = ‖w‖ :=
    norm_frameCLE_symm
  refine le_antisymm ?_ ?_
  · -- ‖e ∘L L ∘L e⁻¹‖ ≤ ‖L‖
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) fun w => ?_
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearEquiv.coe_coe]
    calc ‖(frameCLE E) (L ((frameCLE E).symm w))‖
        = ‖L ((frameCLE E).symm w)‖ := hfwd _
      _ ≤ ‖L‖ * ‖(frameCLE E).symm w‖ := L.le_opNorm _
      _ = ‖L‖ * ‖w‖ := by rw [hinv]
  · -- ‖L‖ ≤ ‖e ∘L L ∘L e⁻¹‖, via the reverse conjugation
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    have key : L v = (frameCLE E).symm ((frameCLE E).conjContinuousAlgEquiv L ((frameCLE E) v)) := by
      simp [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply]
    rw [key, hinv, ← hfwd v]
    exact ((frameCLE E).conjContinuousAlgEquiv L).le_opNorm _

/-- The framing preserves the L2 operator norm: a matrix `frameAlg E L` has the same norm as the
endomorphism `L` of `E`. Both `frameCLE` (an isometry) and `toEuclideanCLM` are norm-preserving. -/
theorem norm_frameAlg (L : E →L[ℝ] E) : ‖frameAlg E L‖ = ‖L‖ := by
  rw [frameAlg_apply, ← Matrix.l2_opNorm_toEuclideanCLM, StarAlgEquiv.apply_symm_apply]
  exact norm_conj_frameCLE L

/-- The framing `frameAlg E` is measurable into the entrywise (Pi) measurable structure on matrices:
each matrix entry `(frameAlg E L) i j` is a continuous (`ℝ`-linear, finite-dimensional) function of
`L`, hence measurable. (We argue entrywise because the matrix carries the Pi measurable structure,
which is not registered as the Borel σ-algebra of its norm topology, so `Continuous.measurable` does
not apply directly.) -/
theorem measurable_frameAlg : Measurable (frameAlg E) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  -- the `(i, j)` entry map `L ↦ (frameAlg E L) i j` is continuous (norm topology), hence measurable
  have hcont : Continuous fun L : E →L[ℝ] E => frameAlg E L i j :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_frameAlg)
  exact hcont.measurable

end

end Frontier.Issue2
