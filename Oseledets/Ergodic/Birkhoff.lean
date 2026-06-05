import Oseledets.Ergodic.MaximalErgodic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Invariants
import Mathlib.Dynamics.Ergodic.Ergodic

/-!
# The pointwise (Birkhoff) ergodic theorem

The individual/pointwise ergodic theorem (layer `L1.3` / milestone `M3`) — `a.e.`
convergence of the Birkhoff averages to the conditional expectation onto the invariant
σ-algebra — is **absent** from Mathlib (only the L² von Neumann *mean* ergodic theorem
exists). It is the bottom gate of the whole development.

This file also states the supporting commutation lemma `M2` (`condExp` commutes with a
measure-preserving composition) and the ergodic corollary (the limit is the space
average `∫ g dμ`).

All statements carry `sorry`; proved in the Birkhoff phase (from the maximal ergodic
inequality `M1` and the `condExp` substrate).
-/

open MeasureTheory Filter Topology

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-- **`condExp` commutes with a measure-preserving composition** (layer `L1.2` / `M2`):
`μ[g ∘ T | invariants T] =ᵐ[μ] (μ[g | invariants T]) ∘ T`. -/
theorem condExp_invariants_comp
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : X → ℝ} (hg : Integrable g μ) :
    μ[g ∘ T | MeasurableSpace.invariants T] =ᵐ[μ]
      (μ[g | MeasurableSpace.invariants T]) ∘ T := by
  sorry

/-- **Pointwise (Birkhoff) ergodic theorem** (layer `L1.3` / `M3`): for a
measure-preserving `T` and integrable `g`, the Birkhoff averages converge `μ`-a.e. to
the conditional expectation of `g` onto the σ-algebra of `T`-invariant sets. -/
theorem tendsto_birkhoffAverage_ae
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T g n x) atTop
      (𝓝 ((μ[g | MeasurableSpace.invariants T]) x)) := by
  sorry

/-- **Birkhoff ergodic theorem, ergodic case**: when `T` is ergodic for a probability
measure, the Birkhoff averages converge `μ`-a.e. to the space average `∫ g dμ`. -/
theorem tendsto_birkhoffAverage_ae_integral
    [IsProbabilityMeasure μ] (hT : Ergodic T μ) {g : X → ℝ} (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T g n x) atTop (𝓝 (∫ y, g y ∂μ)) := by
  sorry

end Oseledets
