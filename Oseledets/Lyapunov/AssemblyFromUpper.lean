import Oseledets.Lyapunov.SlowFlagBridge
import Oseledets.Lyapunov.SpectrumConstancy
import Oseledets.Lyapunov.ForwardLowerWiring

/-!
# M5 — the FINAL COMPOSER for the Oseledets filtration theorem

This file composes all committed assets into the headline Oseledets filtration theorem
`oseledets_filtration_of_upper`, deriving everything from the single fixed analytic node
`hupper` (the per-vector spectral upper bound, delivered verbatim by the parallel worker) together
with a *minimized* set of precisely-typed residual hypotheses that capture exactly the deep
Λ-spectral identification (L7d / L11) which is genuinely not yet committed in the repository.

## Strategy

The committed capstone `Oseledets.oseledets_filtration_of_slowflag` consumes three a.e. interfaces:
`hspec`, `hslowflag`, and `hgrowth`.  We discharge each as far as the committed assets and `hupper`
allow, isolating the irreducible uncommitted content into named residual hypotheses.

* **`hslowflag`** (`Vslow (exp t) = lambdaSublevel t`).  The forward inclusion
  `Vslow (exp t) ⊆ lambdaSublevel t` is *derived from `hupper`* (a slow Λ-vector grows slowly, hence
  lies in the growth-sublevel) — `vslow_subset_lambdaSublevel_of_upper` below.  The reverse inclusion
  is the genuinely uncommitted Λ-spectral direction, taken as the typed residual `hslowrev`.

* **`hgrowth`** via `Oseledets.hgrowth_of_upper_lower`.  The upper half `hub` is *derived from
  `hupper`* through the slow-flag identification (`hub_of_upper` below).  The lower bound `hlb` and
  the boundedness `hbdd` come from the committed `Oseledets.hbdd_of_fk` (unconditional) and the
  band-projector lower-bound layer; the band-projector convergence datum is the typed residual
  `hband`.

* **`hspec`** via `Oseledets.hspec_standing` (the two Finset inclusions).  Both inclusions are the
  deep spectral identification of the deterministic exponent set; they are taken as the typed
  residuals `hub_spec` / `hlb_spec`.

## Residual hypotheses (the irreducible uncommitted Λ-spectral identification)

Beyond `hupper` the composition needs exactly the following, all precisely typed:

* `hslowrev` — reverse inclusion `lambdaSublevel t ⊆ Vslow (exp t)` a.e. (the slow-growth ⟹ in
  Λ-slow-space direction);
* `hband` — band-projector convergence with nonzero fast component on each stratum (the L7d
  `Vflag`-to-band identification feeding the committed liminf lower bound);
* `hub_spec`, `hlb_spec` — the two Finset spectrum inclusions (`spectrum ⊆/⊇ distinctExp lam0 d`).

Each is the minimal cleanly-typed shape of a single uncommitted spectral fact; none is derivable from
the committed assets plus `hupper` alone (they require the spectral structure of the Oseledets limit
operator `Λ`, whose projector-range/growth identification is the parallel L7d work).
-/

open MeasureTheory Filter Topology Matrix
open scoped Matrix Matrix.Norms.L2Operator

namespace Oseledets

set_option linter.unusedSectionVars false

variable {X : Type*} [MeasurableSpace X] {d : ℕ} [NeZero d]

/-! ## Forward inclusion of `hslowflag` from `hupper` -/

/-- **`Vslow (exp t) ⊆ lambdaSublevel t` from `hupper`.**  A nonzero vector in the Λ-slow band at
level `e^t` has, by `hupper`, `limsup (1/n) log‖A⁽ⁿ⁾ v‖ ≤ t`; that `limsup` *is* `lambdaBar A T x v`
(`limsup_log_norm_cocycle_eq_lambdaBar`), so `lambdaBar A T x v ≤ t`, i.e. `v ∈ lambdaSublevel t`.
The zero vector lies in every submodule.  Requires only the `IsUltrametricGrowth` good set (to use
the sublevel membership criterion `mem_lambdaSublevel`). -/
theorem vslow_subset_lambdaSublevel_of_upper
    {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X} {x : X}
    (hx : IsUltrametricGrowth (lambdaBar A T x))
    (hupperx : ∀ t : ℝ, ∀ v ∈ Vslow A T (Real.exp t) x, v ≠ 0 →
      limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ t) :
    ∀ t : ℝ, Vslow A T (Real.exp t) x ≤ lambdaSublevel A T x t := by
  intro t v hv
  rw [mem_lambdaSublevel hx]
  by_cases hv0 : v = 0
  · exact Or.inl hv0
  · refine Or.inr ?_
    have := hupperx t v hv hv0
    rwa [limsup_log_norm_cocycle_eq_lambdaBar] at this

/-! ## The `hgrowth` upper half from `Vflag` membership

The upper half `hub` of `Oseledets.hgrowth_of_upper_lower` is, in fact, *unconditional* given the
`IsUltrametricGrowth` good set: a vector in the stratum `Vflag i.castSucc \ Vflag i.succ` has
`lambdaBar = specList i` exactly (`lambdaBar_eq_on_stratum`), and that `lambdaBar` is the `limsup`
(`limsup_log_norm_cocycle_eq_lambdaBar`).  So `limsup ≤ specList i` holds (with equality) and `hub`
needs no separate analytic input. -/

/-- **`hub` from `Vflag` membership (a.e.).**  On the `IsUltrametricGrowth` good set the per-stratum
`limsup` equals the exact exponent `specList i`, so in particular `limsup ≤ specList i` — the upper
half consumed by `Oseledets.hgrowth_of_upper_lower`. -/
theorem hub_of_growthFunction
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∀ᵐ x ∂μ, ∀ i : Fin (specCard A T x),
      ∀ v ∈ (Vflag A T x i.castSucc : Set (EuclideanSpace ℝ (Fin d))),
        v ∉ Vflag A T x i.succ →
        limsup (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ specList A T x i := by
  filter_upwards [isUltrametricGrowth_lambdaBar hT hA hAmeas hint hint'] with x hx i v hv hvnot
  rw [limsup_log_norm_cocycle_eq_lambdaBar]
  exact le_of_eq (lambdaBar_eq_on_stratum hx i hv hvnot)

/-! ## Assembling `hslowflag` from the forward (`hupper`) and reverse inclusions -/

/-- **`hslowflag` from `hupper` and the reverse inclusion.**  Combines the forward inclusion
`Vslow (exp t) ⊆ lambdaSublevel t` (derived from `hupper` via
`vslow_subset_lambdaSublevel_of_upper`) with the uncommitted reverse inclusion `hslowrev`
(`lambdaSublevel t ⊆ Vslow (exp t)`) into the per-point identification
`Vslow (exp t) = lambdaSublevel t` consumed by `oseledets_filtration_of_slowflag`. -/
theorem hslowflag_of_upper
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (hupper : ∀ᵐ x ∂μ, ∀ t : ℝ, ∀ v ∈ Vslow A T (Real.exp t) x, v ≠ 0 →
      limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ t)
    (hslowrev : ∀ᵐ x ∂μ, ∀ t : ℝ, lambdaSublevel A T x t ≤ Vslow A T (Real.exp t) x) :
    ∀ᵐ x ∂μ, ∀ t : ℝ, Vslow A T (Real.exp t) x = lambdaSublevel A T x t := by
  filter_upwards [isUltrametricGrowth_lambdaBar hT hA hAmeas hint hint', hupper, hslowrev]
    with x hx hupperx hrevx
  intro t
  exact le_antisymm (vslow_subset_lambdaSublevel_of_upper hx (hupperx) t) (hrevx t)

/-! ## The capstone composition -/

/-- **Oseledets filtration theorem, composed from the spectral upper bound `hupper`.**

The complete Oseledets measurable-filtration conclusion, assembled from the committed capstone
`oseledets_filtration_of_slowflag` and the parallel worker's per-vector spectral upper bound
`hupper`.  The deterministic exponent data `lam0` is taken from the committed
`exists_lam_tendsto_singularValue`.  The three a.e. interfaces are discharged as follows:

* `hslowflag` — forward inclusion derived from `hupper` (`hslowflag_of_upper`), reverse inclusion the
  residual `hslowrev`;
* `hgrowth` — `hub` derived from `Vflag` membership (`hub_of_growthFunction`), `hbdd` from the
  committed `hbdd_of_fk`, `hlb` from the committed `hlb_of_bandProjector` fed the residual band datum
  `hband`;
* `hspec` — the committed `hspec_standing` fed the two residual Finset spectrum inclusions
  `hub_spec` / `hlb_spec`.

The residual hypotheses `hslowrev`, `hband`, `hub_spec`, `hlb_spec` are exactly the irreducible
uncommitted Λ-spectral identification content (L7d / L11); see the module docstring. -/
theorem oseledets_filtration_of_upper
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
    -- Residual 4: the band-projector convergence datum feeding the committed liminf lower bound.
    (hband : ∀ᵐ x ∂μ, ∀ i : Fin (specCard A T x),
      ∀ v ∈ (Vflag A T x i.castSucc : Set (EuclideanSpace ℝ (Fin d))),
        v ∉ Vflag A T x i.succ →
        ∃ P : Matrix (Fin d) (Fin d) ℝ,
          Tendsto (fun n => bandProjector A T
            (Set.indicator (Set.Ioi (Real.exp (specList A T x i))) 1) n x) atTop (𝓝 P) ∧
          Matrix.toEuclideanLin P v ≠ 0) :
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
  -- `hgrowth` from upper (`Vflag`) + lower (band) + boundedness (FK).
  have hbdd := hbdd_of_fk hT A hA hAmeas hint hint'
  have hub := hub_of_growthFunction hT hA hAmeas hint hint'
  have hlb := hlb_of_bandProjector A hA hband hbdd
  have hgrowth := hgrowth_of_upper_lower A hub hlb hbdd
  -- Assemble through the committed capstone.
  exact oseledets_filtration_of_slowflag hT A hA hAmeas hTmeas hint hint' lam0
    hspec hslowflag hgrowth

/-! ## Axiom audit -/

#print axioms vslow_subset_lambdaSublevel_of_upper
#print axioms hub_of_growthFunction
#print axioms hslowflag_of_upper
#print axioms oseledets_filtration_of_upper

end Oseledets
