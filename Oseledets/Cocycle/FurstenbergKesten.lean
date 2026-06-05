import Oseledets.Cocycle.Basic
import Oseledets.Ergodic.Kingman
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The Furstenberg–Kesten theorem (extremal Lyapunov exponents)

Applying Kingman's theorem to `gₙ = log‖A⁽ⁿ⁾‖` (a subadditive cocycle by
submultiplicativity of the operator norm) yields the **top Lyapunov exponent**
`λ₁ = lim (1/n) log‖A⁽ⁿ⁾(x)‖`; applying it to the conorm / inverse cocycle yields the
**bottom exponent** `λ_k = lim (1/n) log m(A⁽ⁿ⁾(x))`. These are the extremal cases of
the Oseledets spectrum (layer `L3` / milestone `M5`), and the first genuine
proof-of-concept landing on top of Kingman.

Statements carry `sorry`; proved in the Furstenberg–Kesten phase.
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X} {d : ℕ}

/-- **Furstenberg–Kesten, top exponent.** For an ergodic measure-preserving `T` and a
measurable cocycle generator with `log⁺‖A‖ ∈ L¹`, the normalized log operator norm of
the cocycle converges `μ`-a.e. to a constant `λ₁` (the top Lyapunov exponent). -/
theorem furstenbergKesten_top
    [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) :
    ∃ lam : ℝ, ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖) atTop (𝓝 lam) := by
  sorry

/-- **Furstenberg–Kesten, bottom exponent.** With the additional `log⁺‖A⁻¹‖ ∈ L¹`
hypothesis (so the cocycle is in `GL`), the normalized log norm of the inverse cocycle
converges `μ`-a.e. to a constant; equivalently the bottom Lyapunov exponent
`λ_k = -lim (1/n) log‖A⁽ⁿ⁾(x)⁻¹‖` exists and is finite. -/
theorem furstenbergKesten_bot
    [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∃ lam : ℝ, ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖(cocycle A T n x)⁻¹‖) atTop (𝓝 lam) := by
  sorry

end Oseledets
