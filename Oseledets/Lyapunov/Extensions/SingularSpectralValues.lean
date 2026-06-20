/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.Extensions.SingularExponentGenLog
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# The genuine per-direction singular Lyapunov exponent `λ_k^gen` (`EReal`-valued, antitone)

For a **possibly-singular** matrix cocycle generator `A : X → Matrix (Fin d) (Fin d) ℝ` — no
`det A ≠ 0`, no inverse integrability — this module builds the **genuine** (`−∞`-aware)
per-direction forward singular Lyapunov exponent and proves it is **antitone in the direction
index**, the gap
datum that the intermediate filtration needs in order to choose its cut thresholds.

The `log⁺` per-direction exponent of
`Oseledets/Lyapunov/Extensions/SingularPerDirectionExponent.lean`
(`Oseledets.singularDirExponent`) is **NOT** antitone — the positive-part clamp `log⁺` resets the
cumulative volume to `0` once it turns non-positive, so its increments jump back up (see that
module's docstring for the explicit `λ^gen = (1, −½, −½, −½)` counterexample). The antitone ordering
lives on the **genuine** logarithm. We capture it here with the `−∞`-valued `ENNReal.log` of the
`k`-th singular value `σ_k(A⁽ⁿ⁾)` (zero-indexed, so `σ_0 ≥ σ_1 ≥ …`):

`λ_k^gen(x) = limsup_n ((1/n : EReal) · log σ_k(A⁽ⁿ⁾ x))`,

with `log 0 = ⊥` (the collapse `−∞` exponent). Because the singular values are antitone in `k`
(`LinearMap.singularValues_antitone`) and `ENNReal.log` is monotone (`ENNReal.log_monotone`), the
per-direction exponents are **deterministically antitone** — `λ_{k+1}^gen(x) ≤ λ_k^gen(x)` for
**every** `x`, with no invertibility, integrability, or ergodicity hypothesis. This is exactly the
property the `log⁺` packaging lacks and the reason the genuine `log` is used.

## Main definitions

* `Oseledets.singularSpectralValue` — the genuine per-direction forward singular exponent
  `λ_k^gen`, the `EReal`-valued `limsup` of `(1/n) log σ_k(A⁽ⁿ⁾)` (with `log 0 = ⊥`). It can equal
  `⊥` on the collapse / kernel stratum.

## Main results

* `Oseledets.singularSpectralValue_antitone` — **the headline**: `λ_k^gen` is antitone in `k` for
  **every** `x` (deterministic), since the singular values are antitone and `ENNReal.log` is
  monotone.
* `Oseledets.singularSpectralValue_le_genLog_sub` / `Oseledets.singularSpectralValue_succ_telescope`
  — the telescoping tie to the cumulative genuine-`log` exponent
  `Oseledets.forwardSingularExponentLog`: where the top-`k` volume is positive, the per-direction
  exponent is the cumulative increment `γ_{k+1}^log − γ_k^log`.

## Implementation notes

* The `−∞`-aware `ENNReal.log : ℝ≥0∞ → EReal` (`log 0 = ⊥`, `log` monotone) is the right logarithm
  here: with the plain `Real.log` (where `Real.log 0 = 0` by convention) the per-direction exponents
  would **not** be antitone, because a collapsed singular value `σ = 0` would read as `log 0 = 0`
  rather than the genuine `−∞`. So the antitone ordering is genuinely an `ENNReal.log` phenomenon.
* Everything in the antitone core is **deterministic** (holds for every `x`); no `det A ≠ 0`, no
  `log⁺‖A⁻¹‖ ∈ L¹`, no ergodicity. The invertible analogues (`Oseledets.exponents` in
  `Oseledets/Lyapunov/Extensions/Spectrum.lean`, with their `det ≠ 0` and inverse-integrability
  hypotheses) are deliberately **not** reused.

## References

* A. Quas, *Multiplicative Ergodic Theorems and Applications* (Theorem 2, §3.1; SVD + exterior
  algebra + Kingman, Raghunathan's method).
* M. S. Raghunathan, *A proof of Oseledec's multiplicative ergodic theorem*,
  Israel J. Math. **32** (1979), 356–362.
* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {T : X → X} {d : ℕ}

/-- **The genuine per-direction forward singular exponent `λ_k^gen`** of a possibly-singular
cocycle generator, as an `EReal`-valued `limsup` built from the `−∞`-aware logarithm
`ENNReal.log`:

`λ_k^gen(x) = limsup_n ((1/n : EReal) · log σ_k(A⁽ⁿ⁾ x))`,

where `σ_k(A⁽ⁿ⁾) = (toEuclideanLin (cocycle A T n x)).singularValues k` is the `k`-th singular value
(zero-indexed, non-increasing) and `log = ENNReal.log` (so a collapsed singular value `σ_k = 0`
reads as the genuine `⊥ = −∞`, not the `Real.log 0 = 0` junk). Unlike the `log⁺` per-direction
exponent `Oseledets.singularDirExponent`, this genuine version is **antitone** in `k`. -/
noncomputable def singularSpectralValue (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (k : ℕ) (x : X) : EReal :=
  Filter.limsup
    (fun n : ℕ => ((n : ℝ)⁻¹ : EReal) *
      ENNReal.log (ENNReal.ofReal
        ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k))) atTop

omit [MeasurableSpace X] in
/-- **The headline: `λ_k^gen` is antitone in `k`, deterministically.** For **every** `x` (no
invertibility, no integrability, no ergodicity), `λ_{k+1}^gen(x) ≤ λ_k^gen(x)`. The singular
values are antitone in the index (`LinearMap.singularValues_antitone`), `ENNReal.ofReal` is
monotone, and the `−∞`-aware logarithm `ENNReal.log` is monotone (`ENNReal.log_monotone`), so each
term `(1/n) log σ_{k+1} ≤ (1/n) log σ_k` (the factor `(n : ℝ)⁻¹ ≥ 0`); the `EReal`-`limsup` is
monotone, giving the bound. This is precisely the antitone ordering the `log⁺` packaging
(`Oseledets.singularDirExponent`) lacks, and the gap datum the cut-threshold layer needs. -/
theorem singularSpectralValue_antitone (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) :
    Antitone fun k => singularSpectralValue A T k x := by
  intro k l hkl
  refine Filter.limsup_le_limsup (Filter.Eventually.of_forall fun n => ?_)
  -- `σ_l ≤ σ_k` (singular values antitone), so `ofReal σ_l ≤ ofReal σ_k`, so `log ≤ log`.
  have hσ : (Matrix.toEuclideanLin (cocycle A T n x)).singularValues l
      ≤ (Matrix.toEuclideanLin (cocycle A T n x)).singularValues k :=
    (Matrix.toEuclideanLin (cocycle A T n x)).singularValues_antitone hkl
  have hlog : ENNReal.log (ENNReal.ofReal
        ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues l))
      ≤ ENNReal.log (ENNReal.ofReal
        ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k)) :=
    ENNReal.log_monotone (ENNReal.ofReal_le_ofReal hσ)
  exact mul_le_mul_of_nonneg_left hlog (by positivity)

/-! ### Telescoping tie to the cumulative genuine-`log` volume and measurability -/

omit [MeasurableSpace X] in
/-- **The genuine `−∞`-aware log of the `k`-th singular value is a measurable telescoping
difference of cumulative log-volumes.** For **every** `n` and `x`,

`log σ_k(A⁽ⁿ⁾) = log (ofReal sprod_{k+1}) − log (ofReal sprod_k)` (in `EReal`, `log = ENNReal.log`).

When `sprod_k > 0`, the factorization `sprod_{k+1} = sprod_k · σ_k` (`Finset.prod_range_succ`) and
the unconditional additivity `ENNReal.log_mul_add` give
`log (ofReal sprod_{k+1}) = log (ofReal sprod_k) + log σ_k`, and the (finite) `log (ofReal sprod_k)`
cancels (`EReal.add_sub_cancel_left`). When `sprod_k = 0`, antitonicity of the singular values
forces `σ_k = 0`, so the left side is `⊥`, while the right side is `⊥ − ⊥ = ⊥` (`EReal.bot_sub`),
so the identity holds there too. This expresses the per-direction term through the **measurable**
`sprod` (`Oseledets.measurable_sprod`), sidestepping the absence of a direct singular-value
measurability lemma. -/
theorem log_singularValue_eq_sub_sprod (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (k n : ℕ) (x : X) :
    ENNReal.log (ENNReal.ofReal
        ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k))
      = ENNReal.log (ENNReal.ofReal (sprod A T (k + 1) n x))
        - ENNReal.log (ENNReal.ofReal (sprod A T k n x)) := by
  set σ : ℝ := (Matrix.toEuclideanLin (cocycle A T n x)).singularValues k with hσdef
  have hσ_nonneg : 0 ≤ σ := (Matrix.toEuclideanLin (cocycle A T n x)).singularValues_nonneg k
  have hfac : sprod A T (k + 1) n x = sprod A T k n x * σ := by
    rw [sprod, sprod, Finset.prod_range_succ]
  rcases eq_or_lt_of_le (sprod_nonneg A k n x) with hzero | hpos
  · -- collapse: `sprod_k = 0` forces `σ_k = 0`, both sides are `⊥`.
    have hσ0 : σ = 0 := by
      by_contra hne
      have hσpos : 0 < σ := lt_of_le_of_ne hσ_nonneg (Ne.symm hne)
      have hspos : 0 < sprod A T k n x := by
        rw [sprod]
        refine Finset.prod_pos fun i hi => ?_
        exact lt_of_lt_of_le hσpos
          ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues_antitone
            (Nat.le_of_lt_succ (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))))
      exact absurd hzero.symm (ne_of_gt hspos)
    have hsk0 : sprod A T k n x = 0 := hzero.symm
    have hsk1 : sprod A T (k + 1) n x = 0 := by rw [hfac, hσ0, mul_zero]
    rw [hσ0, hsk0, hsk1]
    simp only [ENNReal.ofReal_zero, ENNReal.log_zero, EReal.bot_sub]
  · -- positive regime: factorize, use additivity of `log`, cancel the finite cumulative term.
    have hsprodk_pos : 0 < sprod A T k n x := hpos
    have hofRealmul : ENNReal.ofReal (sprod A T (k + 1) n x)
        = ENNReal.ofReal (sprod A T k n x) * ENNReal.ofReal σ := by
      rw [hfac, ENNReal.ofReal_mul (le_of_lt hsprodk_pos)]
    rw [hofRealmul, ENNReal.log_mul_add,
      ENNReal.log_ofReal_of_pos hsprodk_pos, EReal.add_sub_cancel_left]

/-- **The per-direction exponent `λ_k^gen` is measurable.** Via the telescoping identity
`log σ_k = log (ofReal sprod_{k+1}) − log (ofReal sprod_k)`
(`Oseledets.log_singularValue_eq_sub_sprod`), each defining term is the scalar multiple of a
measurable `EReal`-difference: `sprod` is measurable (`Oseledets.measurable_sprod`, `[NeZero d]`),
`ENNReal.ofReal` is measurable (`ENNReal.measurable_ofReal`), `ENNReal.log` is measurable
(`ENNReal.measurable_log`), and `EReal` subtraction/scalar multiplication preserve measurability.
The `ℕ`-`limsup` of measurable `EReal`-valued functions is measurable (`Measurable.limsup`). -/
theorem measurable_singularSpectralValue [NeZero d] {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hAmeas : Measurable A) (hTmeas : Measurable T) (k : ℕ) :
    Measurable (singularSpectralValue A T k) := by
  refine Measurable.limsup (fun n => ?_)
  have hsprodsucc : Measurable fun x =>
      ENNReal.log (ENNReal.ofReal (sprod A T (k + 1) n x)) :=
    ENNReal.measurable_log.comp
      (ENNReal.measurable_ofReal.comp (measurable_sprod hAmeas hTmeas (k + 1) n))
  have hsprodk : Measurable fun x =>
      ENNReal.log (ENNReal.ofReal (sprod A T k n x)) :=
    ENNReal.measurable_log.comp
      (ENNReal.measurable_ofReal.comp (measurable_sprod hAmeas hTmeas k n))
  have hneg : Measurable fun x =>
      -ENNReal.log (ENNReal.ofReal (sprod A T k n x)) :=
    (continuous_neg.measurable).comp hsprodk
  have hsub : Measurable fun x =>
      ENNReal.log (ENNReal.ofReal (sprod A T (k + 1) n x))
        + -ENNReal.log (ENNReal.ofReal (sprod A T k n x)) := hsprodsucc.add hneg
  have hfun : (fun x =>
      ENNReal.log (ENNReal.ofReal
        ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k)))
      = fun x => ENNReal.log (ENNReal.ofReal (sprod A T (k + 1) n x))
          + -ENNReal.log (ENNReal.ofReal (sprod A T k n x)) := by
    funext x
    rw [log_singularValue_eq_sub_sprod, sub_eq_add_neg]
  have hlogσ : Measurable fun x =>
      ENNReal.log (ENNReal.ofReal
        ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k)) := by
    rw [hfun]; exact hsub
  exact (measurable_const.mul hlogσ)

omit [MeasurableSpace X] in
/-- **Each term of `λ_k^gen` is bounded above by `(1/n) log⁺‖A⁽ⁿ⁾‖`.** Deterministically, for every
`n` and `x`, `(1/n) · log σ_k(A⁽ⁿ⁾) ≤ ((1/n) log⁺‖A⁽ⁿ⁾‖ : EReal)`. If `σ_k = 0` the left side is
`⊥`; otherwise `σ_k ≤ ‖A⁽ⁿ⁾‖` (`Oseledets.sigma_le_opNorm`) gives
`log σ_k ≤ log ‖A⁽ⁿ⁾‖ ≤ log⁺‖A⁽ⁿ⁾‖`, and the factor `(n : ℝ)⁻¹ ≥ 0` preserves the bound. -/
theorem singularSpectralValue_term_le_posLogNorm (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (k n : ℕ) (x : X) :
    ((n : ℝ)⁻¹ : EReal) * ENNReal.log (ENNReal.ofReal
        ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k))
      ≤ (((n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖ : ℝ) : EReal) := by
  set σ : ℝ := (Matrix.toEuclideanLin (cocycle A T n x)).singularValues k with hσdef
  have hσ_nonneg : 0 ≤ σ := (Matrix.toEuclideanLin (cocycle A T n x)).singularValues_nonneg k
  have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  rcases eq_or_lt_of_le hσ_nonneg with hzero | hpos
  · -- `σ_k = 0`: left side is `(1/n) · ⊥ ≤ RHS` (handle `n = 0`, where `(1/n)⁻¹ = 0`, separately).
    have hlog0 : ENNReal.log (ENNReal.ofReal σ) = ⊥ := by
      rw [← hzero]; simp
    rw [hlog0]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hpos_inv : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.2 hnR
      have heq : ((n : ℝ)⁻¹ : EReal) * ⊥ = ⊥ :=
        EReal.mul_bot_of_pos (EReal.coe_pos.2 hpos_inv)
      rw [heq]; exact bot_le
  · -- `σ_k > 0`: `log σ_k ≤ log⁺‖A⁽ⁿ⁾‖`, then scale by `(1/n) ≥ 0`.
    have hlogeq : ENNReal.log (ENNReal.ofReal σ) = ((Real.log σ : ℝ) : EReal) := by
      rw [ENNReal.log_ofReal_of_pos hpos]
    have hlogle : Real.log σ ≤ Real.posLog ‖cocycle A T n x‖ :=
      (Real.log_le_log hpos (sigma_le_opNorm _ k)).trans
        (le_max_right _ _)
    calc ((n : ℝ)⁻¹ : EReal) * ENNReal.log (ENNReal.ofReal σ)
        = (((n : ℝ)⁻¹ * Real.log σ : ℝ) : EReal) := by rw [hlogeq]; norm_cast
      _ ≤ (((n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖ : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_left hlogle hninv)

/-- **`λ_k^gen < ⊤` `μ`-a.e.** (the genuine per-direction exponent is a.e. finite above). For an
ergodic measure-preserving `T` and a possibly-singular generator with `log⁺‖A‖ ∈ L¹`, each defining
term is `≤ (1/n) log⁺‖A⁽ⁿ⁾‖` (`Oseledets.singularSpectralValue_term_le_posLogNorm`), and the latter
converges `μ`-a.e. to the finite forward top value `λ₁⁺` (`Oseledets.tendsto_top_posLogNorm`). So
the `EReal`-`limsup` defining `λ_k^gen` is `≤ (λ₁⁺ : EReal) < ⊤`. (The lower side can reach `⊥` on
the
collapse stratum, so no a.e. `⊥ < λ_k^gen` companion is claimed — that is the whole point of the
genuine `−∞`-aware exponent.) -/
theorem ae_singularSpectralValue_lt_top {μ : Measure X} [IsProbabilityMeasure μ] [NeZero d]
    (hT : Ergodic T μ) {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (k : ℕ) :
    ∀ᵐ x ∂μ, singularSpectralValue A T k x < ⊤ := by
  obtain ⟨lam, hlam⟩ := tendsto_top_posLogNorm hT hAmeas hint
  filter_upwards [hlam] with x hx
  have hxE : Tendsto
      (fun n : ℕ => (((n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖ : ℝ) : EReal)) atTop
      (𝓝 (lam : EReal)) := (continuous_coe_real_ereal.tendsto _).comp hx
  have hle : singularSpectralValue A T k x ≤ (lam : EReal) := by
    rw [← hxE.limsup_eq]
    refine Filter.limsup_le_limsup (Filter.Eventually.of_forall fun n => ?_)
    exact singularSpectralValue_term_le_posLogNorm A T k n x
  exact lt_of_le_of_lt hle (EReal.coe_lt_top lam)

/-! ### Cut thresholds between consecutive distinct finite exponents

The intermediate singular filtration is built by feeding the Gram-sublevel projector
`Oseledets.cocycleSublevelEuclid` a **squared-singular-value** threshold `t` strictly between the
growth rates of two consecutive distinct exponents. A singular direction with per-direction exponent
`λ` has singular value `σ ≈ e^{nλ}`, hence Gram eigenvalue `σ² ≈ e^{2nλ}`. So to separate the
exponent `λ_{j+1}` (below) from `λ_j` (above) the threshold must satisfy
`e^{2 λ_{j+1}} < t_j < e^{2 λ_j}`. This section constructs such thresholds from the **a.e.-constant
distinct finite exponent vector** (the strictly-antitone list of distinct values), which is the gap
datum the cut layer consumes. It is pure real analysis (`Real.exp` strict monotone +
`exists_between`), with no cocycle, measure, or invertibility hypothesis. -/

/-- **A cut threshold strictly between two consecutive distinct exponents.** Given finite exponents
`a < b` (so `b` is the larger, "faster" exponent), there is a squared-singular-value threshold `t`
with `Real.exp (2 * a) < t < Real.exp (2 * b)`: the Gram-eigenvalue scale strictly separates the two
growth rates. Obtained from strict monotonicity of `Real.exp` and density of `ℝ`
(`exists_between`). -/
theorem exists_cutThreshold {a b : ℝ} (hab : a < b) :
    ∃ t : ℝ, Real.exp (2 * a) < t ∧ t < Real.exp (2 * b) := by
  have hlt : Real.exp (2 * a) < Real.exp (2 * b) :=
    Real.exp_lt_exp.2 (by linarith)
  exact exists_between hlt

/-- **The full ladder of cut thresholds for a strictly-antitone finite exponent vector.** Given the
distinct exponents `lam : Fin (r + 1) → ℝ` sorted strictly decreasingly (largest first; `lam` is
the a.e.-constant list of distinct **finite** singular exponents, kernel/`−∞` directions excluded),
there is a threshold vector `t : Fin r → ℝ` placing, for each consecutive pair, a
squared-singular-value
cut strictly between the two growth rates:

`Real.exp (2 · lam (j+1)) < t j < Real.exp (2 · lam j)`.

These are exactly the thresholds to feed `Oseledets.cocycleSublevelEuclid` so that its `≤ t_j`
Gram-sublevel space captures the directions with exponent `≤ lam (j+1)` (the slow part below the
`j`-th gap). Built by choosing each cut independently with `Oseledets.exists_cutThreshold` on the
strict gap `lam (j.succ) < lam (j.castSucc)`. No measure-theoretic or invertibility hypothesis. -/
theorem exists_cutThresholds {r : ℕ} (lam : Fin (r + 1) → ℝ) (hlam : StrictAnti lam) :
    ∃ t : Fin r → ℝ, ∀ j : Fin r,
      Real.exp (2 * lam j.succ) < t j ∧ t j < Real.exp (2 * lam j.castSucc) := by
  choose t ht using fun j : Fin r =>
    exists_cutThreshold (a := lam j.succ) (b := lam j.castSucc)
      (hlam (by simp [Fin.castSucc_lt_succ_iff]))
  exact ⟨t, ht⟩

end Oseledets
