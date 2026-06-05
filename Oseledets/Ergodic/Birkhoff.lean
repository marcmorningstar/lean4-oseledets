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

/-- Set-integral invariance under a measure-preserving map: if `s` is a measurable
`T`-invariant set (`T ⁻¹' s = s`), then integrating `h ∘ T` over `s` equals integrating
`h` over `s`. -/
private theorem setIntegral_comp_of_invariants
    (hT : MeasurePreserving T μ μ) {h : X → ℝ} (hh : AEStronglyMeasurable h μ)
    {s : Set X} (hs : MeasurableSet s) (hsinv : T ⁻¹' s = s) :
    ∫ x in s, (h ∘ T) x ∂μ = ∫ x in s, h x ∂μ := by
  have hmap : Measure.map T μ = μ := hT.map_eq
  have hhmap : AEStronglyMeasurable h (Measure.map T μ) := by rw [hmap]; exact hh
  -- `∫_s (h ∘ T) ∂μ = ∫_{T⁻¹'s} h(T·) ∂μ = ∫_s h ∂(map T μ) = ∫_s h ∂μ`.
  calc ∫ x in s, (h ∘ T) x ∂μ
      = ∫ x in T ⁻¹' s, h (T x) ∂μ := by rw [hsinv]; rfl
    _ = ∫ y in s, h y ∂(Measure.map T μ) := (setIntegral_map hs hhmap hT.aemeasurable).symm
    _ = ∫ y in s, h y ∂μ := by rw [hmap]

/-- **`condExp` commutes with a measure-preserving composition** (layer `L1.2` / `M2`):
`μ[g ∘ T | invariants T] =ᵐ[μ] (μ[g | invariants T]) ∘ T`. -/
theorem condExp_invariants_comp
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : X → ℝ} (hg : Integrable g μ) :
    μ[g ∘ T | MeasurableSpace.invariants T] =ᵐ[μ]
      (μ[g | MeasurableSpace.invariants T]) ∘ T := by
  have hI : MeasurableSpace.invariants T ≤ ‹MeasurableSpace X› := MeasurableSpace.invariants_le T
  -- It suffices to prove the symmetric statement `(μ[g | I]) ∘ T =ᵐ μ[g ∘ T | I]`.
  symm
  by_cases hσ : SigmaFinite (μ.trim hI)
  · -- The substantive σ-finite branch: use uniqueness of `condExp`.
    -- `T` is `(I, I)`-measurable, as `T` semiconjugates itself.
    have hTI : @Measurable _ _ (MeasurableSpace.invariants T) (MeasurableSpace.invariants T) T :=
      MeasurableSpace.measurable_invariants_of_semiconj hTm (fun _ => rfl)
    refine ae_eq_condExp_of_forall_setIntegral_eq (f := g ∘ T)
      (g := (μ[g | MeasurableSpace.invariants T]) ∘ T) hI
      (hT.integrable_comp_of_integrable hg) (fun s _ _ => ?_) (fun s hs _ => ?_) ?_
    · -- `(μ[g | I]) ∘ T` is integrable, hence integrable on `s`.
      exact (hT.integrable_comp_of_integrable integrable_condExp).integrableOn
    · -- The set-integral identity, the heart of the proof.
      obtain ⟨hsm, hsinv⟩ := (MeasurableSpace.measurableSet_invariants).1 hs
      calc ∫ x in s, ((μ[g | MeasurableSpace.invariants T]) ∘ T) x ∂μ
          = ∫ x in s, (μ[g | MeasurableSpace.invariants T]) x ∂μ :=
            setIntegral_comp_of_invariants hT
              (stronglyMeasurable_condExp.mono hI).aestronglyMeasurable hsm hsinv
        _ = ∫ x in s, g x ∂μ := setIntegral_condExp hI hg hs
        _ = ∫ x in s, (g ∘ T) x ∂μ :=
            (setIntegral_comp_of_invariants hT hg.aestronglyMeasurable hsm hsinv).symm
    · -- `(μ[g | I]) ∘ T` is `I`-strongly-measurable.
      exact (stronglyMeasurable_condExp.comp_measurable hTI).aestronglyMeasurable
  · -- Degenerate branch: both sides reduce to `0`.
    rw [condExp_of_not_sigmaFinite hI hσ, condExp_of_not_sigmaFinite hI hσ]
    rfl

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
