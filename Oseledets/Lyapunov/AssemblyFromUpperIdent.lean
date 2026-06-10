import Oseledets.Lyapunov.AssemblyFromUpper
import Oseledets.Lyapunov.SpectrumResiduals

/-!
# Assembly from the upper bound, via the spectral-identification residual

Identical to the committed `Oseledets.oseledets_filtration_of_upper`, except the defective
band-projector residual `hband` is replaced by the sound `hident` residual, and the `hlb`
sub-step is routed through `hlb_of_slowflag_ident` (fed `hident` and the `hslowflag` already
computed earlier in the proof) instead of `hlb_of_bandProjector`.
-/

open MeasureTheory Filter Topology Matrix
open scoped Matrix Matrix.Norms.L2Operator

namespace Oseledets

set_option linter.unusedSectionVars false

variable {X : Type*} [MeasurableSpace X] {d : ℕ} [NeZero d]

/-- **Oseledets filtration theorem, composer variant via the sound `hident` route.**

Same as `oseledets_filtration_of_upper` but with the unsatisfiable band-projector residual
`hband` swapped for the sound spectral-identification residual `hident`, consumed by
`hlb_of_slowflag_ident`. -/
theorem oseledets_filtration_of_upper'
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ) (hTmeas : Measurable T)
    {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    -- The FIXED spectral-upper-bound node delivered by the parallel worker (verbatim shape).
    (hupper : ∀ᵐ x ∂μ, ∀ t : ℝ, ∀ v ∈ Vslow A T (Real.exp t) x, v ≠ 0 →
      Filter.limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) Filter.atTop ≤ t)
    -- Residual 1: the reverse slow-flag inclusion (slow growth ⟹ in Λ-slow-space).
    (hslowrev : ∀ᵐ x ∂μ, ∀ t : ℝ, lambdaSublevel A T x t ≤ Vslow A T (Real.exp t) x)
    -- Residual 2: spectrum upper Finset inclusion (every realized exponent is deterministic).
    (hub_spec : ∀ lam0 : ℕ → ℝ,
      (∀ i : ℕ, i < d → ∀ᵐ x ∂μ, Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i))
        atTop (𝓝 (lam0 i))) →
      ∀ᵐ x ∂μ, spectrum A T x ⊆ distinctExp lam0 d)
    -- Residual 3: spectrum lower Finset inclusion (every deterministic exponent is attained).
    (hlb_spec : ∀ lam0 : ℕ → ℝ,
      (∀ i : ℕ, i < d → ∀ᵐ x ∂μ, Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i))
        atTop (𝓝 (lam0 i))) →
      ∀ᵐ x ∂μ, distinctExp lam0 d ⊆ spectrum A T x)
    -- Residual 4 (SOUND route): the spectral-identification band-projector datum.
    (hident : ∀ᵐ x ∂μ, ∀ c : ℝ, 0 < c → (∀ i : Fin d, Real.exp (lamSing A T x (i : ℕ)) ≠ c) →
      Filter.Tendsto (fun n : ℕ => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)
        Filter.atTop (𝓝 (cfc (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ)) (lambdaHat A T x)))) :
    ∃ (k : ℕ) (lam : Fin k → ℝ)
      (V : Fin (k + 1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))),
      StrictAnti lam ∧
      (∀ i, MeasurableSubspace fun x => V i x) ∧
      ∀ᵐ x ∂μ,
        V 0 x = ⊤ ∧ V (Fin.last k) x = ⊥ ∧
        (∀ i : Fin k, V i.succ x < V i.castSucc x) ∧
        (∀ i : Fin (k + 1),
          Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap (V i x) = V i (T x)) ∧
        (∀ i : Fin k, ∀ v ∈ (V i.castSucc x : Set (EuclideanSpace ℝ (Fin d))),
            v ∉ V i.succ x →
            Tendsto
              (fun n : ℕ => (n : ℝ)⁻¹ *
                Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖)
              atTop (𝓝 (lam i))) := by
  classical
  -- The deterministic singular-value exponents.
  obtain ⟨lam0, _hmono, hlam0⟩ :=
    exists_lam_tendsto_singularValue hT hA hAmeas hint hint'
  -- `hspec` from the two residual spectrum inclusions.
  have hspec := hspec_standing hT A hA hAmeas hint hint' lam0
    (hub_spec lam0 hlam0) (hlb_spec lam0 hlam0)
  -- `hslowflag` from `hupper` and the reverse inclusion.
  have hslowflag := hslowflag_of_upper hT hA hAmeas hint hint' hupper hslowrev
  -- `hgrowth` from upper (`Vflag`) + lower (sound `hident` route) + boundedness (FK).
  have hbdd := hbdd_of_fk hT A hA hAmeas hint hint'
  have hub := hub_of_growthFunction hT hA hAmeas hint hint'
  have hlb := hlb_of_slowflag_ident hT hA hAmeas hint hint' hident hslowflag
  have hgrowth := hgrowth_of_upper_lower A hub hlb hbdd
  -- Assemble through the committed capstone.
  exact oseledets_filtration_of_slowflag hT A hA hAmeas hTmeas hint hint' lam0
    hspec hslowflag hgrowth

/-! ## Axiom audit -/

#print axioms oseledets_filtration_of_upper'

end Oseledets
