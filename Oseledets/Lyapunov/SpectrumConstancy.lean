import Oseledets.Lyapunov.FiltrationAssemblyBridge

/-!
# SpectrumConstancy — discharging the `hspecconst` spectrum-constancy interface

The committed `Oseledets.hspec_of_spectrum_const` (in `FiltrationAssemblyBridge.lean`) reduces the
`hspec` interface of the final assembly to the single hypothesis

```
hspecconst : ∀ᵐ x ∂μ, spectrum A T x = distinctExp lam0 d.
```

This file discharges `hspecconst` itself.  The per-point limsup spectrum `spectrum A T x` is the
finite set of values of the upper Lyapunov growth function `lambdaBar A T x` on nonzero vectors
(`Oseledets.spectrum`, `Oseledets.mem_spectrum`).  Pinning that finite set to the deterministic
distinct-exponent set `distinctExp lam0 d` is a `Finset.Subset.antisymm` of two per-vector
inclusions:

* **upper inclusion** `spectrum A T x ⊆ distinctExp lam0 d` — every realized `lambdaBar` value is
  one of the deterministic singular-value exponents `lam0 i` (`i < d`).  This is the
  growth→exponent direction; its per-vector core is the **spectral upper bound** (the one genuine
  analytic node of the MET, proved in parallel via the determinant/tempering squeeze), here taken in
  exactly the repackaged Finset shape it produces.

* **lower inclusion** `distinctExp lam0 d ⊆ spectrum A T x` — every distinct deterministic exponent
  `lam0 i` is *attained* by some nonzero vector, i.e. lies in the `lambdaBar`-range.  Its per-vector
  core is the committed lower bound (`log_le_liminf_log_cocycle_apply`) combined with the
  stratum-exact `lambdaBar_eq_on_stratum`.

The two inclusions compose to the constant `distinctExp lam0 d`, so **ergodic constancy of the
spectrum (subgoal 1) is automatic** — the limit set is deterministic by construction, hence
trivially `T`-invariant and constant; no separate `Finset ℝ` measurability / ergodic-averaging step
is needed once the identification is in hand.  (For completeness we *also* record, unconditionally
from `spectrum_equivariant_ae` + ergodicity, that the identification self-propagates: if it holds it
holds at `T x` too, and on the full orbit.)

## What is unconditional vs. hypothesis-gated

* `spectrum_eq_of_subsets` and `hspecconst_of_subsets` are **unconditional** `Finset` algebra: they
  turn the two per-vector inclusions into the Finset identity / the `hspec` interface, using nothing
  but the committed `Oseledets.hspec_of_spectrum_const`.
* `spectrum_const_invariant_ae` is **unconditional** (committed `spectrum_equivariant_ae`): the
  identification, once true a.e., is `T`-invariant a.e.
* The two per-vector inclusion hypotheses `hub_spec` / `hlb_spec` are the analytic interface.  The
  lower one is essentially committed; the upper one is the spectral-upper-bound node proved by the
  parallel worker.  They are stated here in the minimal cleanly-typed Finset shape so that the
  orchestrator can plug the parallel outputs in directly.
-/

open MeasureTheory Filter Topology

namespace Oseledets

-- The `hspec_standing` wrapper intentionally lists the full standing hypotheses to fix the
-- orchestrator's call-site shape, even though its proof only consumes the two inclusions.
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-! ## Unconditional Finset algebra: two inclusions ⟹ the identity -/

/-- **The spectrum identity from the two per-vector inclusions (pointwise).**  If, at the point `x`,
every spectrum value is a deterministic exponent and every deterministic exponent is attained, then
the per-point limsup spectrum equals the deterministic distinct-exponent set. -/
theorem spectrum_eq_of_subsets
    {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X} {x : X} {lam0 : ℕ → ℝ}
    (hub : spectrum A T x ⊆ distinctExp lam0 d)
    (hlb : distinctExp lam0 d ⊆ spectrum A T x) :
    spectrum A T x = distinctExp lam0 d :=
  Finset.Subset.antisymm hub hlb

/-- **`hspecconst` from the two a.e. per-vector inclusions.**  The minimal cleanly-typed reduction:
the a.e. upper inclusion (`spectrum ⊆ distinctExp`, the spectral-upper-bound node) and the a.e.
lower inclusion (`distinctExp ⊆ spectrum`, the attainment/lower-bound layer) give the a.e. spectrum
constancy `spectrum A T x = distinctExp lam0 d` consumed by `hspec_of_spectrum_const`. -/
theorem hspecconst_of_subsets
    {μ : Measure X} {T : X → X} (A : X → Matrix (Fin d) (Fin d) ℝ) (lam0 : ℕ → ℝ)
    (hub_spec : ∀ᵐ x ∂μ, spectrum A T x ⊆ distinctExp lam0 d)
    (hlb_spec : ∀ᵐ x ∂μ, distinctExp lam0 d ⊆ spectrum A T x) :
    ∀ᵐ x ∂μ, spectrum A T x = distinctExp lam0 d := by
  filter_upwards [hub_spec, hlb_spec] with x hub hlb
  exact spectrum_eq_of_subsets hub hlb

/-- **The `hspec` interface, discharged from the two a.e. per-vector inclusions.**  Composes
`hspecconst_of_subsets` with the committed `hspec_of_spectrum_const`: the output is *exactly* the
`hspec` hypothesis of `oseledets_filtration_of_interfaces`. -/
theorem hspec_of_subsets
    {μ : Measure X} {T : X → X} (A : X → Matrix (Fin d) (Fin d) ℝ) (lam0 : ℕ → ℝ)
    (hub_spec : ∀ᵐ x ∂μ, spectrum A T x ⊆ distinctExp lam0 d)
    (hlb_spec : ∀ᵐ x ∂μ, distinctExp lam0 d ⊆ spectrum A T x) :
    ∀ᵐ x ∂μ, ∃ h : specCard A T x = numExp lam0 d,
      ∀ i : Fin (specCard A T x), specList A T x i = expEnum lam0 d (Fin.cast h i) :=
  hspec_of_spectrum_const A lam0 (hspecconst_of_subsets A lam0 hub_spec hlb_spec)

/-! ## Reducing the inclusions to the analytic workers' native `lambdaBar` shape

The two Finset inclusions are equivalent, on the a.e. good set where `lambdaBar A T x` is an
`IsUltrametricGrowth` function (committed: `isUltrametricGrowth_lambdaBar`), to per-vector `lambdaBar`
statements:

* upper inclusion ⟺ every realized value `lambdaBar A T x v` (`v ≠ 0`) is some `lam0 j` (`j < d`) —
  this is the spectral-upper-bound worker's native output (`lambdaBar v = λᵢ` on each stratum,
  the values being the deterministic exponents);
* lower inclusion ⟺ every `lam0 j` (`j < d`) is realized by some nonzero `v` — the attainment/
  lower-bound layer.

These reductions are unconditional `mem_spectrum`/`mem_distinctExp` unfoldings; they let the
orchestrator feed the workers' per-vector outputs without first repackaging into Finsets. -/

/-- **Upper inclusion in native `lambdaBar`/`lam0` form.**  On the `IsUltrametricGrowth` good set, the
Finset upper inclusion `spectrum ⊆ distinctExp` is exactly: every value of `lambdaBar A T x` on a
nonzero vector is one of the deterministic exponents `lam0 j` (`j < d`). -/
theorem spectrum_subset_iff_lambdaBar_mem
    {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X} {x : X} {lam0 : ℕ → ℝ}
    (hx : IsUltrametricGrowth (lambdaBar A T x)) :
    spectrum A T x ⊆ distinctExp lam0 d ↔
      ∀ v : EuclideanSpace ℝ (Fin d), v ≠ 0 →
        ∃ j : ℕ, j < d ∧ lam0 j = lambdaBar A T x v := by
  constructor
  · intro hsub v hv
    have : lambdaBar A T x v ∈ distinctExp lam0 d := hsub (lambdaBar_mem_spectrum hx hv)
    exact (mem_distinctExp lam0 d).mp this
  · intro hall r hr
    obtain ⟨v, hv, hvr⟩ := (mem_spectrum hx).mp hr
    obtain ⟨j, hj, hjr⟩ := hall v hv
    exact (mem_distinctExp lam0 d).mpr ⟨j, hj, by rw [hjr, hvr]⟩

/-- **Lower inclusion in native `lam0`/`lambdaBar` form.**  On the `IsUltrametricGrowth` good set, the
Finset lower inclusion `distinctExp ⊆ spectrum` is exactly: every deterministic exponent `lam0 j`
(`j < d`) is realized as `lambdaBar A T x v` for some nonzero `v`. -/
theorem distinctExp_subset_iff_lambdaBar_attained
    {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X} {x : X} {lam0 : ℕ → ℝ}
    (hx : IsUltrametricGrowth (lambdaBar A T x)) :
    distinctExp lam0 d ⊆ spectrum A T x ↔
      ∀ j : ℕ, j < d →
        ∃ v : EuclideanSpace ℝ (Fin d), v ≠ 0 ∧ lambdaBar A T x v = lam0 j := by
  constructor
  · intro hsub j hj
    have hr : lam0 j ∈ spectrum A T x := hsub ((mem_distinctExp lam0 d).mpr ⟨j, hj, rfl⟩)
    exact (mem_spectrum hx).mp hr
  · intro hall r hr
    obtain ⟨j, hj, hjr⟩ := (mem_distinctExp lam0 d).mp hr
    obtain ⟨v, hv, hvr⟩ := hall j hj
    rw [← hjr, ← hvr]
    exact lambdaBar_mem_spectrum hx hv

/-- **`hspecconst` from the workers' native per-vector outputs.**  Combines the two `lambdaBar`-level
reductions with the committed a.e. `IsUltrametricGrowth` good set: given a.e. that every realized
`lambdaBar` value is a deterministic exponent (`hub_lam`, the spectral-upper-bound node) and every
deterministic exponent is attained (`hlb_lam`, the lower-bound/attainment layer), the spectrum is
a.e. the deterministic constant `distinctExp lam0 d`. -/
theorem hspecconst_of_lambdaBar
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (lam0 : ℕ → ℝ)
    (hub_lam : ∀ᵐ x ∂μ, ∀ v : EuclideanSpace ℝ (Fin d), v ≠ 0 →
      ∃ j : ℕ, j < d ∧ lam0 j = lambdaBar A T x v)
    (hlb_lam : ∀ᵐ x ∂μ, ∀ j : ℕ, j < d →
      ∃ v : EuclideanSpace ℝ (Fin d), v ≠ 0 ∧ lambdaBar A T x v = lam0 j) :
    ∀ᵐ x ∂μ, spectrum A T x = distinctExp lam0 d := by
  have hUM := isUltrametricGrowth_lambdaBar hT hA hAmeas hint hint'
  filter_upwards [hUM, hub_lam, hlb_lam] with x hx hub hlb
  refine spectrum_eq_of_subsets ?_ ?_
  · exact (spectrum_subset_iff_lambdaBar_mem hx).mpr hub
  · exact (distinctExp_subset_iff_lambdaBar_attained hx).mpr hlb

/-! ## Unconditional ergodic constancy (subgoal 1)

The deterministic target `distinctExp lam0 d` is constant in `x`, so the identification
`spectrum A T x = distinctExp lam0 d` is automatically `T`-invariant.  We make the self-propagation
explicit and unconditional from the committed `spectrum_equivariant_ae`: where the spectrum equals
the deterministic constant and is `A`-equivariant, the same holds at `T x`.  This is the precise
"ergodic constancy" content of subgoal 1 — once the (deterministic) value is identified, ergodicity
adds nothing further, because a deterministic function is already constant. -/

/-- **Self-propagation of the spectrum identity along `T` (a.e.).**  Unconditional from the committed
`spectrum_equivariant_ae`: if a.e. `spectrum A T x = distinctExp lam0 d`, then a.e.
`spectrum A T (T x) = distinctExp lam0 d` as well.  Together with the a.e. equivariance
`spectrum A T x = spectrum A T (T x)` this exhibits the identification as `T`-invariant, i.e. the
spectrum is a.e. equal to the *same* deterministic constant set at `x` and at `T x`. -/
theorem spectrum_const_invariant_ae
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (lam0 : ℕ → ℝ)
    (hconst : ∀ᵐ x ∂μ, spectrum A T x = distinctExp lam0 d) :
    ∀ᵐ x ∂μ, spectrum A T x = distinctExp lam0 d ∧
      spectrum A T (T x) = distinctExp lam0 d := by
  have hequiv := spectrum_equivariant_ae hT hA hAmeas hint hint'
  filter_upwards [hconst, hequiv] with x hx heq
  exact ⟨hx, by rw [← heq]; exact hx⟩

/-! ## End-to-end: the `hspec` interface under the standing hypotheses

Bundling everything: under the standard standing hypotheses, *given* the two analytic per-vector
inclusions, the `hspec` interface (and hence — via the committed `FiltrationAssemblyBridge`
deliverables — the `oseledets_filtration` `hspec` slot) is discharged.  The signature lists the full
standing hypotheses so it slots directly into the orchestrator's call site, even though the proof
only needs the two inclusions: this fixes the *shape* the parallel spectral-upper-bound worker must
deliver. -/

/-- **Standing-hypotheses wrapper for the `hspec` interface.**  Under `Ergodic T μ`, a probability
measure, measurable invertible log-integrable `A` (and `A⁻¹`), and the two per-vector spectrum
inclusions, the `hspec` hypothesis of `oseledets_filtration_of_interfaces` holds. -/
theorem hspec_standing
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ)
    (A : X → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).det ≠ 0)
    (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ)
    (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (lam0 : ℕ → ℝ)
    (hub_spec : ∀ᵐ x ∂μ, spectrum A T x ⊆ distinctExp lam0 d)
    (hlb_spec : ∀ᵐ x ∂μ, distinctExp lam0 d ⊆ spectrum A T x) :
    ∀ᵐ x ∂μ, ∃ h : specCard A T x = numExp lam0 d,
      ∀ i : Fin (specCard A T x), specList A T x i = expEnum lam0 d (Fin.cast h i) :=
  hspec_of_subsets A lam0 hub_spec hlb_spec

/-! ## Axiom audit -/

#print axioms spectrum_eq_of_subsets
#print axioms hspecconst_of_subsets
#print axioms hspec_of_subsets
#print axioms spectrum_subset_iff_lambdaBar_mem
#print axioms distinctExp_subset_iff_lambdaBar_attained
#print axioms hspecconst_of_lambdaBar
#print axioms spectrum_const_invariant_ae
#print axioms hspec_standing

end Oseledets
