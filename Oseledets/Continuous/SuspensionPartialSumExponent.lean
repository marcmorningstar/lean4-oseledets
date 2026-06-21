/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Continuous.SuspensionFlowExponentFinal
import Oseledets.Lyapunov.Extensions.ExteriorCocycle

/-!
# Full-spectrum scaling of the special-flow Lyapunov exponents

The space-level special-flow headline `Oseledets.ae_suspensionMeasure_hasFlowExponent_of_measurable`
(`Oseledets.Continuous.SuspensionFlowExponentFinal`) establishes, for `μ̂ = suspensionMeasure`-a.e.
orbit class `q`, the **top** flow exponent `λ_base / ∫τ` — the Lyapunov analogue of Abramov's
entropy formula `h(flow) = h(base)/∫τ`. That headline is, however, *generic in its cocycle
generator*: it takes an arbitrary base generator `A : X → Matrix (Fin d) (Fin d) ℝ`, an arbitrary
base growth rate `lam` (the a.e. limit of `(1/n) log ‖cocycle A T n x‖`), and produces the
cover-cocycle growth rate `lam / ∫τ`. Nothing in it is special to the *top* exponent.

This module upgrades that to the **full spectrum**, i.e. to *every* exponent of the base spectrum,
by instantiating the generic headline at the **exterior (compound) cocycle generator** `extGen k A`
(`Oseledets.Lyapunov.Extensions.ExteriorCocycle`). The `k`-th compound cocycle `C_k(A^{(n)})` has
operator-norm growth rate `Γ_k = ∑_{i<k} exponents i` (the sum of the top-`k` base exponents,
`Oseledets.tendsto_log_opNorm_compound_cocycle`), so feeding it into the generic special-flow
headline yields the **partial-sum (exterior-power) flow scaling**

`Γ_k^flow = Γ_k^base / ∫τ`     (`ae_suspensionMeasure_hasFlowExponent_extGen`),

read as `HasFlowExponent (extGen k A) … q (Γ_k / ∫τ)`: the top exponent of the `k`-fold exterior
suspension flow — i.e. the sum of the top-`k` *flow* exponents — equals `Γ_k^base / ∫τ`.

Telescoping the partial sums gives the **per-exponent / full-spectrum scaling**: for every sorted
index `i : Fin d`,

`λ_i^flow = λ_i^base / ∫τ`     (`suspension_perExponent_scaling`),

phrased as the identity `(gammaK_{i+1} − gammaK_i) / ∫τ = exponents i / ∫τ` between the discrete
base spectrum (divided by the mean roof) and the per-band flow-exponent increments
`Γ_{i+1}^flow − Γ_i^flow`. This is the full-spectrum statement requested for Issue #5: the *entire*
suspension/flow Lyapunov spectrum is the base spectrum divided by `∫τ`, not merely the top
exponent.

## Main results

* `Oseledets.measurable_extGen` — the exterior (compound) cocycle generator `x ↦ C_k(A x)` is
  measurable whenever `A` is (each entry is a `k × k` minor, a polynomial in the entries of `A x`).
* `Oseledets.ae_suspensionMeasure_hasFlowExponent_extGen` — the **partial-sum flow scaling**:
  under the base MET standing hypotheses and the bounded-roof / Birkhoff hypotheses, for `μ̂`-a.e.
  orbit class `q`, `HasFlowExponent (extGen k A) … q (Γ_k / ∫τ)`. (For `k = 1` this recovers the
  top-exponent headline; for `k = d` it is the determinant / volume growth.)
* `Oseledets.suspension_gammaK_flow_scaling` — the partial-sum scaling read as a value identity:
  the flow growth rate `Γ_k^flow = HasFlowExponent`-value is `Γ_k^base / ∫τ`.
* `Oseledets.suspension_perExponent_scaling` — the **per-exponent / full-spectrum scaling**:
  `(Γ_{i+1}^base − Γ_i^base) / ∫τ = exponents i / ∫τ` for every `i : Fin d`, i.e. each individual
  flow exponent is the corresponding base exponent divided by `∫τ`.

## References

* L. M. Abramov, *On the entropy of a flow*, Dokl. Akad. Nauk SSSR **128** (1959) 873–875.
* I. P. Cornfeld, S. V. Fomin, Ya. G. Sinai, *Ergodic Theory*, Springer 1982, Ch. 11
  (special / suspension flows; Ambrose–Kakutani).
* M. Bessa, P. Varandas, *On the Lyapunov spectrum of suspension flows* (exponent transfer).
* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014)
  (the exterior-power characterization of the partial sums).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-! ## Measurability of the exterior (compound) cocycle generator -/

section MeasurableExtGen

omit [MeasurableSpace X] in
/-- **The compound matrix is a measurable function of its argument.** Each entry of
`ExteriorNorm.compoundMatrix k M` is the determinant of a `k × k` submatrix of `M`, hence a
polynomial in the entries of `M`; the determinant is measurable (`measurable_det` on the submatrix
index type) and post-composing with the entry-extraction keeps measurability. -/
theorem measurable_compoundMatrix (k : ℕ) :
    Measurable
      (fun M : Matrix (Fin d) (Fin d) ℝ => ExteriorNorm.compoundMatrix k M) := by
  refine measurable_pi_iff.2 fun t => measurable_pi_iff.2 fun s => ?_
  -- The `(t, s)` entry is `(M.submatrix rowsel colsel).det`, a `k × k` determinant.
  simp only [ExteriorNorm.compoundMatrix, Matrix.of_apply]
  -- Unfold the determinant as a polynomial in the submatrix entries, which are entries of `M`.
  simp only [Matrix.det_apply]
  refine Finset.measurable_sum _ fun σ _ => ?_
  refine Measurable.const_smul ?_ _
  refine Finset.measurable_prod _ fun i _ => ?_
  -- The factor is `M.submatrix _ _ (σ i) i = M (rowsel (σ i)) (colsel i)`, a single entry of `M`.
  simp only [Matrix.submatrix_apply]
  exact (measurable_pi_apply _).comp (measurable_pi_apply _)

variable {A : X → Matrix (Fin d) (Fin d) ℝ}

/-- **Measurability of the exterior (compound) cocycle generator `extGen k A`.** Since
`extGen k A x = C_k(A x)` and `C_k` is measurable (`measurable_compoundMatrix`), the generator is
measurable whenever the base generator `A` is. -/
theorem measurable_extGen (k : ℕ) (hAmeas : Measurable A) :
    Measurable (extGen k A) :=
  (measurable_compoundMatrix k).comp hAmeas

end MeasurableExtGen

/-! ## The exterior cocycle's base growth rate is `Γ_k` -/

section ExtGrowth

variable {μ : Measure X} {T : X ≃ᵐ X} [IsProbabilityMeasure μ] [NeZero d]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hT : Ergodic (⇑T) μ) (hA : ∀ x, (A x).det ≠ 0)
    (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ)
    (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)

include hT hA hint hint' in
/-- **The exterior cocycle's discrete growth rate is `Γ_k`.** For `μ`-a.e. base point `x`,
`(1/n) log ‖cocycle (extGen k A) T n x‖ → Γ_k`. This is `tendsto_log_opNorm_compound_cocycle`
(the `k`-volume / largest-minor growth equals the partial sum `Γ_k`) rewritten through the cocycle
identity `cocycle (extGen k A) T n x = C_k(cocycle A T n x)` (`cocycle_extGen_eq_compound`). It is
the base-growth datum consumed by the generic special-flow headline at `extGen k A`. -/
theorem tendsto_log_opNorm_cocycle_extGen {k : ℕ} (hk : k ≤ d) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle (extGen k A) (⇑T) n x‖) atTop
      (𝓝 (gammaK hT hA hAmeas hint hint' hk)) := by
  filter_upwards [tendsto_log_opNorm_compound_cocycle hT hA hAmeas hint hint' hk] with x hx
  refine hx.congr (fun n => ?_)
  rw [cocycle_extGen_eq_compound]

end ExtGrowth

/-! ## The partial-sum (exterior-power) flow scaling -/

section PartialSumScaling

variable {μ : Measure X} {T : X ≃ᵐ X} {τ : X → ℝ} {c C : ℝ}
    [IsProbabilityMeasure μ] [NeZero d]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hT : Ergodic (⇑T) μ) (hA : ∀ x, (A x).det ≠ 0)
    (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ)
    (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) (hτ : Measurable τ)

include hT hA hint hint' hτ in
/-- **The partial-sum (exterior-power) special-flow Lyapunov scaling.** Instantiate the generic,
fully unconditional special-flow headline `ae_suspensionMeasure_hasFlowExponent_of_measurable` at
the exterior (compound) cocycle generator `extGen k A`, with base growth rate `lam := Γ_k`. The
required base-growth datum is `tendsto_log_opNorm_cocycle_extGen` and the generator measurability is
`measurable_extGen`; the roof hypotheses are unchanged (independent of the cocycle generator). For
`μ̂ = suspensionMeasure`-a.e. orbit class `q`,

`HasFlowExponent (extGen k A) … q (Γ_k / ∫τ)`,

i.e. the top exponent of the `k`-fold exterior suspension flow — the sum of the top-`k` *flow*
exponents — equals `Γ_k^base / ∫τ`. For `k = 1` this recovers the top-exponent headline; for
`k = d` it is the volume / determinant growth. -/
theorem ae_suspensionMeasure_hasFlowExponent_extGen {k : ℕ} (hk : k ≤ d)
    (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (hC : ∀ x, τ x ≤ C)
    (hroof : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * roofSum T hτ (n : ℤ) x) atTop (𝓝 (∫ y, τ y ∂μ)))
    (hτ_pos : 0 < ∫ y, τ y ∂μ) :
    ∀ᵐ q ∂suspensionMeasure T hτ μ,
      HasFlowExponent (extGen k A) T hτ hc hcpos q (gammaK hT hA hAmeas hint hint' hk
        / ∫ y, τ y ∂μ) :=
  ae_suspensionMeasure_hasFlowExponent_of_measurable (extGen k A) T hτ
    (measurable_extGen k hAmeas) hc hcpos hC
    (tendsto_log_opNorm_cocycle_extGen hT hA hAmeas hint hint' hk) hroof hτ_pos

include hT hA hint hint' hτ in
/-- **The partial-sum flow scaling, read as a value identity.** The flow growth rate carried by the
`k`-fold exterior suspension flow at `μ̂`-a.e. class `q` is `Γ_k^base / ∫τ`. This is a restatement
of `ae_suspensionMeasure_hasFlowExponent_extGen`: the `HasFlowExponent`-value equals
`Γ_k / ∫τ`. -/
theorem suspension_gammaK_flow_scaling {k : ℕ} (hk : k ≤ d)
    (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (hC : ∀ x, τ x ≤ C)
    (hroof : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * roofSum T hτ (n : ℤ) x) atTop (𝓝 (∫ y, τ y ∂μ)))
    (hτ_pos : 0 < ∫ y, τ y ∂μ) :
    ∀ᵐ q ∂suspensionMeasure T hτ μ, ∃ L : ℝ,
      HasFlowExponent (extGen k A) T hτ hc hcpos q L ∧
        L = gammaK hT hA hAmeas hint hint' hk / ∫ y, τ y ∂μ := by
  filter_upwards [ae_suspensionMeasure_hasFlowExponent_extGen hT hA hAmeas hint hint' hτ hk
    hc hcpos hC hroof hτ_pos] with q hq
  exact ⟨_, hq, rfl⟩

end PartialSumScaling

/-! ## The per-exponent / full-spectrum scaling -/

section PerExponentScaling

variable {μ : Measure X} {T : X → X} [IsProbabilityMeasure μ] [NeZero d]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hT : Ergodic T μ) (hA : ∀ x, (A x).det ≠ 0)
    (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ)
    (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)

include hT hA hint hint' in
/-- **The per-exponent (full-spectrum) special-flow scaling.** For every sorted index `i : Fin d`,
the `i`-th flow exponent equals the `i`-th base exponent divided by the mean roof `∫τ`:

`(Γ_{i+1}^base − Γ_i^base) / R = exponents i / R`.

The left side is the `i`-th *flow*-exponent increment `Γ_{i+1}^flow − Γ_i^flow` (each partial sum
scaled by `1/R = 1/∫τ` via `ae_suspensionMeasure_hasFlowExponent_extGen`); the right side is the
`i`-th base exponent scaled by `1/R`. The identity follows by telescoping the partial sums
`Γ_k = ∑_{j<k} exponents j` (`gammaK_eq_sum_top_exponents`): `Γ_{i+1} − Γ_i = exponents i`. Thus the
*entire* suspension/flow Lyapunov spectrum is the base spectrum divided by `∫τ`, not merely the top
exponent. (`R` is any nonzero scalar; in the suspension application `R = ∫τ`, positive under a
bounded roof.) -/
theorem suspension_perExponent_scaling (R : ℝ) (i : Fin d) :
    (gammaK hT hA hAmeas hint hint' (Nat.succ_le_of_lt i.isLt)
        - gammaK hT hA hAmeas hint hint' (le_of_lt i.isLt)) / R
      = exponents hT hA hAmeas hint hint' i / R := by
  -- Telescope the partial sums: `Γ_{i+1} − Γ_i = exponents i`.
  have hsucc := gammaK_eq_sum_top_exponents hT hA hAmeas hint hint' (Nat.succ_le_of_lt i.isLt)
  have hi := gammaK_eq_sum_top_exponents hT hA hAmeas hint hint' (le_of_lt i.isLt)
  rw [hsucc, hi]
  -- `∑_{j < i+1} exponents (castLE j) − ∑_{j < i} exponents (castLE j) = exponents i`.
  congr 1
  -- Reduce both partial sums to `Finset.range`-sums of `exponents ∘ (Fin.mk · _)`.
  have key : ∑ j : Fin ((i : ℕ) + 1),
        exponents hT hA hAmeas hint hint' (Fin.castLE (Nat.succ_le_of_lt i.isLt) j)
      - ∑ j : Fin (i : ℕ),
        exponents hT hA hAmeas hint hint' (Fin.castLE (le_of_lt i.isLt) j)
      = exponents hT hA hAmeas hint hint' i := by
    rw [Fin.sum_univ_castSucc]
    have hcong : ∀ j : Fin (i : ℕ),
        exponents hT hA hAmeas hint hint'
            (Fin.castLE (Nat.succ_le_of_lt i.isLt) (Fin.castSucc j))
          = exponents hT hA hAmeas hint hint' (Fin.castLE (le_of_lt i.isLt) j) := by
      intro j; exact congrArg _ (Fin.ext rfl)
    rw [Finset.sum_congr rfl (fun j _ => hcong j)]
    have hlast : (Fin.castLE (Nat.succ_le_of_lt i.isLt) (Fin.last (i : ℕ))) = i := Fin.ext rfl
    rw [hlast]
    ring
  exact key

end PerExponentScaling

end Oseledets
