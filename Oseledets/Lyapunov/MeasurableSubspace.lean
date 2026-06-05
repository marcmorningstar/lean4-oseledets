import Oseledets.Cocycle.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Measurable families of subspaces

Mathlib has no measurable structure on `Submodule`/`Module.Grassmannian`/`Flag`, so we
introduce the project's working notion of a measurably-varying subspace.

A subspace `K ≤ EuclideanSpace ℝ (Fin d)` is encoded by the **matrix of its orthogonal
projection** `orthProjMatrix K`, and a subspace-valued map `V : X → Submodule …` is
declared `MeasurableSubspace` when `x ↦ orthProjMatrix (V x)` is measurable (matrices
carry the Pi/Borel measurable structure, `Oseledets.instMeasurableSpaceMatrix`).

This is layer `L4.5` / milestone `M7` of the plan; the lemmas relating this notion to
spans, sums, and selections are stated in the measurability phase.
-/

open scoped Matrix.Norms.L2Operator

namespace Oseledets

/-- The matrix of the orthogonal projection of `EuclideanSpace ℝ (Fin d)` onto `K`.
A subspace is determined by this matrix, which lives in a space with a measurable
structure, so it is the vehicle for "measurably-varying subspace". -/
noncomputable def orthProjMatrix {d : ℕ} (K : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    Matrix (Fin d) (Fin d) ℝ :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).symm K.starProjection

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-- A family of subspaces `V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))` depends
**measurably** on `x` iff its orthogonal-projection matrix does. -/
def MeasurableSubspace (V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))) : Prop :=
  Measurable fun x => orthProjMatrix (V x)

end Oseledets
