import Oseledets.Ergodic.MaximalErgodic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Invariants
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# The pointwise (Birkhoff) ergodic theorem

The individual/pointwise ergodic theorem (layer `L1.3` / milestone `M3`) — `a.e.`
convergence of the Birkhoff averages to the conditional expectation onto the invariant
σ-algebra — is **absent** from Mathlib (only the L² von Neumann *mean* ergodic theorem
exists). It is the bottom gate of the whole development.

This file also states the supporting commutation lemma `M2` (`condExp` commutes with a
measure-preserving composition) and the ergodic corollary (the limit is the space
average `∫ g dμ`).

## Status

* `condExp_invariants_comp` (`M2`) — **proved**.
* `tendsto_birkhoffAverage_ae` (`M3`) — **proved** for `[IsFiniteMeasure μ]` (the regime
  in which the statement holds): the genuine pointwise Birkhoff theorem, via the maximal
  ergodic inequality `M1`, a Borel–Cantelli tail estimate, and the `condExp` substrate.
  The finiteness hypothesis is necessary (see the theorem docstring); the Oseledets MET
  uses this only for probability measures.
* `tendsto_birkhoffAverage_ae_integral` (ergodic corollary, probability measure) —
  **proved**.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

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

/-! ### The tail estimate `n⁻¹ · g (T^[n] x) → 0` a.e.

For an integrable `g` and a measure-preserving `T`, the orbital values `g (T^[n] x)`
grow slower than linearly, almost everywhere. This is the analytic input that makes the
Birkhoff `limsup`/`liminf` `T`-invariant. The proof is a Borel–Cantelli argument: for a
fixed threshold `δ > 0` the series `∑ₙ μ {x | (n+1)·δ ≤ |g x|}` is finite (its terms
integrate the pointwise count, bounded by `|g|/δ`), and measure-preservation transfers
this to `g ∘ T^[n]`. -/

omit [MeasurableSpace X] in
/-- Pointwise bound for the count of thresholds crossed: for `0 ≤ a` and `0 < δ`,
`∑'ₙ {x | (n+1)·δ ≤ a}.indicator 1 ≤ a / δ` (as an `ℝ≥0∞`-valued tsum over `n`). The sum
counts the integers `n` with `(n+1)·δ ≤ a`, which is at most `a / δ`. -/
private theorem tsum_indicator_threshold_le {δ : ℝ} (hδ : 0 < δ) (a : ℝ) (ha : 0 ≤ a) :
    ∑' n : ℕ, (if ((n : ℝ) + 1) * δ ≤ a then (1 : ℝ≥0∞) else 0) ≤ ENNReal.ofReal (a / δ) := by
  -- Every contributing `n` satisfies `n + 1 ≤ a / δ`, hence lies in `range ⌊a/δ⌋₊`.
  have hdiv : 0 ≤ a / δ := div_nonneg ha hδ.le
  have hsupp : (Function.support fun n : ℕ => (if ((n : ℝ) + 1) * δ ≤ a then (1 : ℝ≥0∞) else 0))
      ⊆ Finset.range ⌊a / δ⌋₊ := by
    intro n hn
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
      not_not] at hn
    rw [Finset.coe_range, Set.mem_Iio]
    have hnδ : ((n : ℝ) + 1) ≤ a / δ := by rw [le_div_iff₀ hδ]; linarith [hn]
    have : n + 1 ≤ ⌊a / δ⌋₊ := Nat.le_floor (by push_cast; linarith)
    omega
  rw [tsum_eq_sum (s := Finset.range ⌊a / δ⌋₊) (fun n hn => by
    by_contra hne
    exact hn (hsupp (by simpa [Function.mem_support] using hne)))]
  calc ∑ n ∈ Finset.range ⌊a / δ⌋₊,
          (if ((n : ℝ) + 1) * δ ≤ a then (1 : ℝ≥0∞) else 0)
      ≤ ∑ _n ∈ Finset.range ⌊a / δ⌋₊, (1 : ℝ≥0∞) := by
        apply Finset.sum_le_sum; intro n _; split <;> simp
    _ = (⌊a / δ⌋₊ : ℝ≥0∞) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    _ ≤ ENNReal.ofReal (a / δ) := by
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (Nat.floor_le hdiv)

/-- For an integrable `g`, the threshold series `∑ₙ μ {x | (n+1)·δ ≤ |g x|}` is finite:
summing the pointwise count bound `tsum_indicator_threshold_le` against `μ` (Tonelli)
gives `∑ₙ μ{(n+1)δ ≤ |g|} ≤ (1/δ)·∫⁻ |g| < ∞`. -/
private theorem tsum_measure_threshold_ne_top {δ : ℝ} (hδ : 0 < δ) {g : X → ℝ}
    (hg : Integrable g μ) :
    (∑' n : ℕ, μ {x | ((n : ℝ) + 1) * δ ≤ |g x|}) ≠ ∞ := by
  have hgm : AEStronglyMeasurable g μ := hg.1
  have hgabs : AEMeasurable (fun x => |g x|) μ :=
    _root_.continuous_abs.measurable.comp_aemeasurable hg.aemeasurable
  -- Each threshold set is null-measurable.
  have hmeas : ∀ n : ℕ, NullMeasurableSet {x | ((n : ℝ) + 1) * δ ≤ |g x|} μ := fun n =>
    nullMeasurableSet_le measurable_const.aemeasurable hgabs
  -- `μ s = ∫⁻ indicator`, and Tonelli swaps the sum with the integral.
  -- The indicator of each threshold set, written pointwise as an `if`.
  have hind : ∀ n : ℕ, (fun x => (if ((n : ℝ) + 1) * δ ≤ |g x| then (1 : ℝ≥0∞) else 0))
      = {x | ((n : ℝ) + 1) * δ ≤ |g x|}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    intro n
    funext x
    simp only [Set.indicator, Set.mem_setOf_eq]
  have hae : ∀ n : ℕ, AEMeasurable
      (fun x => (if ((n : ℝ) + 1) * δ ≤ |g x| then (1 : ℝ≥0∞) else 0)) μ := by
    intro n
    rw [hind n]
    exact (aemeasurable_const).indicator₀ (hmeas n)
  have hterm : ∀ n : ℕ, μ {x | ((n : ℝ) + 1) * δ ≤ |g x|}
      = ∫⁻ x, (if ((n : ℝ) + 1) * δ ≤ |g x| then (1 : ℝ≥0∞) else 0) ∂μ := by
    intro n
    rw [hind n, lintegral_indicator_const₀ (hmeas n), one_mul]
  have key : (∑' n : ℕ, μ {x | ((n : ℝ) + 1) * δ ≤ |g x|})
      = ∫⁻ x, ∑' n : ℕ, (if ((n : ℝ) + 1) * δ ≤ |g x| then (1 : ℝ≥0∞) else 0) ∂μ := by
    rw [lintegral_tsum hae]
    exact tsum_congr hterm
  rw [key]
  -- Bound the inner tsum pointwise by `|g x| / δ`, then by `(1/δ)·∫⁻ |g|`.
  have hbound : ∫⁻ x, ∑' n : ℕ, (if ((n : ℝ) + 1) * δ ≤ |g x| then (1 : ℝ≥0∞) else 0) ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (|g x| / δ) ∂μ := by
    apply lintegral_mono
    intro x
    exact tsum_indicator_threshold_le hδ (|g x|) (abs_nonneg _)
  refine ne_top_of_le_ne_top ?_ hbound
  -- `∫⁻ |g|/δ = (1/δ) ∫⁻ |g| < ∞` since `g` is integrable.
  have hglt : ∫⁻ x, ENNReal.ofReal (|g x|) ∂μ ≠ ∞ := by
    have hfin := hg.2
    rw [hasFiniteIntegral_iff_norm] at hfin
    simp only [Real.norm_eq_abs] at hfin
    exact hfin.ne
  have heq : ∀ x, ENNReal.ofReal (|g x| / δ) = ENNReal.ofReal δ⁻¹ * ENNReal.ofReal (|g x|) := by
    intro x
    rw [div_eq_inv_mul, ENNReal.ofReal_mul (by positivity)]
  simp_rw [heq]
  rw [lintegral_const_mul'' _ hgabs.ennreal_ofReal]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hglt

/-- For integrable `g` and measure-preserving `T`, the orbital tail `n⁻¹ · g (T^[n] x)`
tends to `0` almost everywhere. Proved by Borel–Cantelli: for each threshold `δ = 1/(k+1)`
the series `∑ₙ μ {x | (n+1)δ ≤ |g (T^[n] x)|}` is finite (measure-preservation transfers
`tsum_measure_threshold_ne_top`), so a.e. only finitely many `n` cross the threshold. -/
private theorem ae_tendsto_orbit_div_atTop_zero
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * g (T^[n] x)) atTop (𝓝 0) := by
  -- For each `k`, a.e. `x` eventually has `|g (T^[n] x)| < (n+1)/(k+1)`.
  set δ : ℕ → ℝ := fun k => (k + 1 : ℝ)⁻¹ with hδdef
  have hδpos : ∀ k, 0 < δ k := fun k => by positivity
  have hbc : ∀ k : ℕ, ∀ᵐ x ∂μ,
      ∀ᶠ n : ℕ in atTop, ¬ (((n : ℝ) + 1) * δ k ≤ |g (T^[n] x)|) := by
    intro k
    -- The threshold sets for the shifted orbit, transferred by measure-preservation.
    have hsummable : (∑' n : ℕ, μ {x | ((n : ℝ) + 1) * δ k ≤ |g (T^[n] x)|}) ≠ ∞ := by
      have htrans : ∀ n : ℕ, μ {x | ((n : ℝ) + 1) * δ k ≤ |g (T^[n] x)|}
          = μ {x | ((n : ℝ) + 1) * δ k ≤ |g x|} := by
        intro n
        have hmp : MeasurePreserving (T^[n]) μ μ := hT.iterate n
        have hms : NullMeasurableSet {x | ((n : ℝ) + 1) * δ k ≤ |g x|} μ :=
          nullMeasurableSet_le measurable_const.aemeasurable
            (_root_.continuous_abs.measurable.comp_aemeasurable hg.aemeasurable)
        have := hmp.measure_preimage (s := {x | ((n : ℝ) + 1) * δ k ≤ |g x|}) hms
        rw [← this]; rfl
      rw [show (fun n : ℕ => μ {x | ((n : ℝ) + 1) * δ k ≤ |g (T^[n] x)|})
          = (fun n : ℕ => μ {x | ((n : ℝ) + 1) * δ k ≤ |g x|}) from funext htrans]
      exact tsum_measure_threshold_ne_top (hδpos k) hg
    exact ae_eventually_notMem hsummable
  -- Collect over all `k`.
  rw [← ae_all_iff] at hbc
  filter_upwards [hbc] with x hx
  -- From the threshold bounds, the tail tends to `0`.
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Choose `k` with `2/(k+1) < ε`.
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / ε)
  have hkε : 2 / ((k : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hk
    nlinarith [hk]
  -- Beyond the threshold index for this `k`, and for `n ≥ 1`, the orbital tail is small.
  obtain ⟨N, hN⟩ := (hx k).exists_forall_of_atTop
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  -- `|g (T^[n] x)| < (n+1)·δ k = (n+1)/(k+1)`.
  have hbound : |g (T^[n] x)| < ((n : ℝ) + 1) * δ k := lt_of_not_ge (hN n hnN)
  rw [Real.dist_eq, sub_zero, abs_mul, abs_inv, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ))]
  -- `|n⁻¹| · |g(T^n x)| < n⁻¹·(n+1)/(k+1) ≤ 2/(k+1) < ε`.
  rw [hδdef] at hbound
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hbound' : |g (T^[n] x)| < ((n : ℝ) + 1) * ((k : ℝ) + 1)⁻¹ := by
    simpa using hbound
  have hcalc : (n : ℝ)⁻¹ * |g (T^[n] x)| < 2 / ((k : ℝ) + 1) := by
    rw [inv_mul_lt_iff₀ hnpos]
    have hb : |g (T^[n] x)| < ((n : ℝ) + 1) * ((k : ℝ) + 1)⁻¹ := hbound'
    rw [div_eq_mul_inv]
    -- `(n+1)/(k+1) ≤ n · 2 / (k+1)` because `n+1 ≤ 2n`.
    have hstep : ((n : ℝ) + 1) * ((k : ℝ) + 1)⁻¹ ≤ (n : ℝ) * (2 * ((k : ℝ) + 1)⁻¹) := by
      have hinv : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
      nlinarith [hn1', hinv]
    linarith [hb, hstep]
  linarith [hcalc, hkε]

/-! ### Almost-everywhere `T`-invariance facts -/

/-- If `h ∘ T =ᵐ[μ] h` then a.e. `h` is constant along the whole forward orbit:
`∀ j, h (T^[j] x) = h x`. Each step transfers `h ∘ T =ᵐ h` along the
measure-preserving iterate `T^[j]`, and a countable family of a.e. statements holds a.e. -/
private theorem ae_forall_orbit_eq (hT : MeasurePreserving T μ μ) {h : X → ℝ}
    (hh : h ∘ T =ᵐ[μ] h) : ∀ᵐ x ∂μ, ∀ j : ℕ, h (T^[j] x) = h x := by
  -- For each `j`, `h (T^[j] x) = h x` a.e. (induction on `j`).
  have hstep : ∀ j : ℕ, (fun x => h (T^[j] x)) =ᵐ[μ] h := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        -- `h (T^[j+1] x) = h (T^[j] (T x))`; use `T`-invariance on the orbit.
        have h1 : (fun x => h (T^[j] (T x))) =ᵐ[μ] (fun x => h (T x)) :=
          (hT.quasiMeasurePreserving).ae_eq_comp ih
        have h2 : (fun x => h (T x)) =ᵐ[μ] h := hh
        refine (Filter.EventuallyEq.trans ?_ (h1.trans h2))
        filter_upwards with x
        rw [Function.iterate_succ_apply]
  exact ae_all_iff.2 (fun j => hstep j)

/-- If `h ∘ T =ᵐ[μ] h` then a.e. `birkhoffSum T h n x = n • h x`. -/
private theorem birkhoffSum_ae_eq_nsmul (hT : MeasurePreserving T μ μ) {h : X → ℝ}
    (hh : h ∘ T =ᵐ[μ] h) (n : ℕ) :
    (fun x => birkhoffSum T h n x) =ᵐ[μ] fun x => (n : ℝ) • h x := by
  filter_upwards [ae_forall_orbit_eq hT hh] with x hx
  simp only [birkhoffSum, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _ => hx j), Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The conditional expectations of `g ∘ T` and of `g` onto the invariant σ-algebra
coincide a.e.: both have the same set-integrals over `I`-measurable (= measurable
invariant) sets, by `setIntegral_comp_of_invariants`, so uniqueness of `condExp` applies. -/
private theorem condExp_comp_invariants_eq [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) :
    μ[g ∘ T | MeasurableSpace.invariants T] =ᵐ[μ] μ[g | MeasurableSpace.invariants T] := by
  have hI : MeasurableSpace.invariants T ≤ ‹MeasurableSpace X› := MeasurableSpace.invariants_le T
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (f := g ∘ T)
    (g := μ[g | MeasurableSpace.invariants T]) hI
    (hT.integrable_comp_of_integrable hg) (fun s _ _ => integrable_condExp.integrableOn)
    (fun s hs _ => ?_) stronglyMeasurable_condExp.aestronglyMeasurable
  obtain ⟨hsm, hsinv⟩ := (MeasurableSpace.measurableSet_invariants).1 hs
  rw [setIntegral_condExp hI hg hs]
  exact (setIntegral_comp_of_invariants hT hg.aestronglyMeasurable hsm hsinv).symm

/-- The conditional expectation `μ[g | invariants T]` is a.e. `T`-invariant:
`(μ[g | invariants T]) ∘ T =ᵐ[μ] μ[g | invariants T]`. Combines
`condExp_invariants_comp` with `condExp_comp_invariants_eq`. -/
private theorem condExp_invariants_comp_self [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : X → ℝ} (hg : Integrable g μ) :
    (μ[g | MeasurableSpace.invariants T]) ∘ T =ᵐ[μ] μ[g | MeasurableSpace.invariants T] :=
  ((condExp_invariants_comp hT hTm hg).symm.trans (condExp_comp_invariants_eq hT hg))

/-! ### Maximal-set algebra and `birkhoffAverage` -/

omit [MeasurableSpace X] in
/-- `birkhoffSum` of a constant function is `n • c`. -/
private theorem birkhoffSum_const (c : ℝ) (n : ℕ) (x : X) :
    birkhoffSum T (fun _ => c) n x = (n : ℝ) * c := by
  rw [birkhoffSum_of_comp_eq (φ := fun _ => c) rfl n]
  simp [nsmul_eq_mul]

omit [MeasurableSpace X] in
/-- For `n ≥ 1`, having a positive Birkhoff sum of `g - c` is the same as the Birkhoff
average of `g` exceeding `c`: `0 < birkhoffSum T (g - c) (n+1) x ↔ c < birkhoffAverage ℝ T g (n+1) x`. -/
private theorem birkhoffSum_sub_const_pos_iff (c : ℝ) {g : X → ℝ} (n : ℕ) (x : X) :
    0 < birkhoffSum T (fun y => g y - c) (n + 1) x ↔
      c < birkhoffAverage ℝ T g (n + 1) x := by
  have hsub : (fun y => g y - c) = g - (fun _ => c) := by funext y; rfl
  rw [hsub, birkhoffSum_sub, birkhoffSum_const]
  rw [birkhoffAverage, smul_eq_mul]
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  rw [lt_inv_mul_iff₀ hpos]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-- The maximal-set form of the maximal ergodic inequality: for integrable `g` and
`c : ℝ`, `c · μ B ≤ ∫_B g` over the maximal set `B = {x | ∃ n, c < birkhoffAverage ℝ T g (n+1) x}`.
Apply `setIntegral_birkhoffSum_pos_nonneg` to `g - c` and rewrite the set and integrand. -/
private theorem mul_measure_le_setIntegral_maximal [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) (c : ℝ) :
    c * (μ {x | ∃ n : ℕ, c < birkhoffAverage ℝ T g (n + 1) x}).toReal
      ≤ ∫ x in {x | ∃ n : ℕ, c < birkhoffAverage ℝ T g (n + 1) x}, g x ∂μ := by
  set B : Set X := {x | ∃ n : ℕ, c < birkhoffAverage ℝ T g (n + 1) x} with hBdef
  -- The M1 set for `g - c` equals `B`.
  have hset : {x | ∃ n : ℕ, 0 < birkhoffSum T (fun y => g y - c) (n + 1) x} = B := by
    ext x
    simp only [Set.mem_setOf_eq, hBdef]
    exact exists_congr (fun n => birkhoffSum_sub_const_pos_iff c n x)
  have hgc : Integrable (fun y => g y - c) μ := hg.sub (integrable_const c)
  have hM1 := setIntegral_birkhoffSum_pos_nonneg hT hgc
  rw [hset] at hM1
  -- `∫_B (g - c) = ∫_B g - c·μB` (`setIntegral_const` needs no measurability of `B`).
  have hsplit : ∫ x in B, (g x - c) ∂μ = (∫ x in B, g x ∂μ) - c * (μ B).toReal := by
    rw [integral_sub hg.integrableOn (integrable_const c).integrableOn, setIntegral_const]
    simp only [Measure.real, smul_eq_mul, mul_comm]
  have : (0 : ℝ) ≤ (∫ x in B, g x ∂μ) - c * (μ B).toReal := by
    rw [← hsplit]; exact hM1
  linarith

/-- The maximal-set measure decays: `(natural) k · μ Bₖ ≤ ∫ |g|`, where
`Bₖ = {x | ∃ n, (k:ℝ) < birkhoffAverage ℝ T g (n+1) x}`. -/
private theorem natCast_mul_measure_maximal_le [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) (k : ℕ) :
    (k : ℝ) * (μ {x | ∃ n : ℕ, (k : ℝ) < birkhoffAverage ℝ T g (n + 1) x}).toReal
      ≤ ∫ x, |g x| ∂μ := by
  set B : Set X := {x | ∃ n : ℕ, (k : ℝ) < birkhoffAverage ℝ T g (n + 1) x} with hBdef
  calc (k : ℝ) * (μ B).toReal
      ≤ ∫ x in B, g x ∂μ := mul_measure_le_setIntegral_maximal hT hg k
    _ ≤ ∫ x in B, |g x| ∂μ :=
        setIntegral_mono hg.integrableOn hg.abs.integrableOn (fun x => le_abs_self _)
    _ ≤ ∫ x, |g x| ∂μ :=
        setIntegral_le_integral hg.abs (Eventually.of_forall (fun x => abs_nonneg _))

/-- Almost every orbit has Birkhoff averages bounded above: the exceptional set where
`birkhoffAverage ℝ T g (·+1) x` is unbounded above is contained in `⋂ₖ Bₖ`, whose measure
is `≤ ∫|g| / k → 0`. -/
private theorem ae_bddAbove_birkhoffAverage [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, BddAbove (Set.range (fun n : ℕ => birkhoffAverage ℝ T g (n + 1) x)) := by
  set B : ℕ → Set X := fun k => {x | ∃ n : ℕ, (k : ℝ) < birkhoffAverage ℝ T g (n + 1) x} with hBdef
  set C : ℝ := ∫ x, |g x| ∂μ with hCdef
  have hCnn : 0 ≤ C := integral_nonneg (fun x => abs_nonneg _)
  -- `(μ Bₖ).toReal ≤ C / k`.
  have hμBk : ∀ k : ℕ, 0 < k → (μ (B k)).toReal ≤ C / k := by
    intro k hk
    have := natCast_mul_measure_maximal_le hT hg k
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    rw [le_div_iff₀ hkpos, mul_comm]
    exact this
  -- The intersection has measure zero.
  have hmeasInter : μ (⋂ k, B k) = 0 := by
    have hle : ∀ k : ℕ, 0 < k → (μ (⋂ k, B k)).toReal ≤ C / k := by
      intro k hk
      refine le_trans ?_ (hμBk k hk)
      apply ENNReal.toReal_mono (measure_ne_top μ _)
      exact measure_mono (Set.iInter_subset _ k)
    -- `C/k → 0`, and `(μ⋂).toReal ≤ C/k` eventually, so `(μ⋂).toReal ≤ 0`.
    have hCk : Tendsto (fun k : ℕ => C / k) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have ht0 : (μ (⋂ k, B k)).toReal ≤ 0 :=
      ge_of_tendsto hCk (eventually_atTop.2 ⟨1, fun k hk => hle k hk⟩)
    have : (μ (⋂ k, B k)).toReal = 0 := le_antisymm ht0 ENNReal.toReal_nonneg
    exact (ENNReal.toReal_eq_zero_iff _).1 this |>.resolve_right (measure_ne_top μ _)
  -- Off the intersection, the range is bounded above.
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hmeasInter
  simp only [Set.mem_setOf_eq] at hx
  rw [Set.mem_iInter]
  intro k
  simp only [hBdef, Set.mem_setOf_eq]
  by_contra hcon
  rw [not_exists] at hcon
  simp only [not_lt] at hcon
  exact hx ⟨(k : ℝ), fun y hy => by
    obtain ⟨n, rfl⟩ := hy
    exact hcon n⟩

/-! ### A real-analysis helper: `limsup` is insensitive to a vanishing perturbation -/

/-- If two bounded real sequences differ by a sequence tending to `0`, their `limsup`s
(along `atTop`) coincide. Bound `u ≤ v + δ` eventually and use `limsup_add_const`. -/
private theorem limsup_eq_of_sub_tendsto_zero {u v : ℕ → ℝ}
    (hau : BddAbove (Set.range u)) (hbu : BddBelow (Set.range u))
    (hav : BddAbove (Set.range v)) (hbv : BddBelow (Set.range v))
    (h : Tendsto (fun n => u n - v n) atTop (𝓝 0)) :
    Filter.limsup u atTop = Filter.limsup v atTop := by
  have bau : IsBoundedUnder (· ≤ ·) atTop u := hau.isBoundedUnder_of_range
  have bbu : IsBoundedUnder (· ≥ ·) atTop u := hbu.isBoundedUnder_of_range
  have bav : IsBoundedUnder (· ≤ ·) atTop v := hav.isBoundedUnder_of_range
  have bbv : IsBoundedUnder (· ≥ ·) atTop v := hbv.isBoundedUnder_of_range
  have cou : IsCoboundedUnder (· ≤ ·) atTop u := bbu.isCoboundedUnder_le
  have cov : IsCoboundedUnder (· ≤ ·) atTop v := bbv.isCoboundedUnder_le
  -- One direction (then apply symmetrically).
  have key : ∀ (a b : ℕ → ℝ), BddBelow (Set.range a) →
      IsBoundedUnder (· ≤ ·) atTop b → IsCoboundedUnder (· ≤ ·) atTop b →
      Tendsto (fun n => a n - b n) atTop (𝓝 0) →
      Filter.limsup a atTop ≤ Filter.limsup b atTop := by
    intro a b hba bab cob hab
    have coa : IsCoboundedUnder (· ≤ ·) atTop a :=
      hba.isBoundedUnder_of_range.isCoboundedUnder_le
    have hle : ∀ δ : ℝ, 0 < δ → Filter.limsup a atTop ≤ Filter.limsup b atTop + δ := by
      intro δ hδ
      have heq : Filter.limsup (fun n => b n + δ) atTop = Filter.limsup b atTop + δ :=
        limsup_add_const atTop b δ bab cob
      rw [← heq]
      have hbab' : IsBoundedUnder (· ≤ ·) atTop (fun n => b n + δ) := by
        obtain ⟨M, hM⟩ := bab
        refine ⟨M + δ, ?_⟩
        simp only [eventually_map] at hM ⊢
        filter_upwards [hM] with n hn
        exact by linarith
      refine Filter.limsup_le_limsup ?_ coa hbab'
      -- eventually `a n ≤ b n + δ`, since `a n - b n → 0`.
      have hev : ∀ᶠ n in atTop, a n - b n < δ := by
        obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hab) δ hδ
        filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hN n hn⟩] with n hn
        rw [Real.dist_eq, sub_zero] at hn
        exact (abs_lt.1 hn).2
      filter_upwards [hev] with n hn
      show a n ≤ b n + δ
      linarith
    -- Let δ ↓ 0.
    by_contra hcon
    rw [not_le] at hcon
    have := hle ((Filter.limsup a atTop - Filter.limsup b atTop) / 2) (by linarith)
    linarith
  apply le_antisymm
  · exact key u v hbu bav cov h
  · refine key v u hbv bau cou ?_
    have heq2 : (fun n => v n - u n) = (fun n => -(u n - v n)) := by funext n; ring
    rw [heq2]
    simpa using h.neg

/-- Almost every orbit has Birkhoff averages bounded below (apply `ae_bddAbove` to `-g`). -/
private theorem ae_bddBelow_birkhoffAverage [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, BddBelow (Set.range (fun n : ℕ => birkhoffAverage ℝ T g (n + 1) x)) := by
  filter_upwards [ae_bddAbove_birkhoffAverage hT hg.neg] with x hx
  -- `birkhoffAverage T (-g) = -birkhoffAverage T g`, so bounded above becomes bounded below.
  obtain ⟨M, hM⟩ := hx
  refine ⟨-M, ?_⟩
  rintro y ⟨n, rfl⟩
  have hbnd := hM (Set.mem_range_self n)
  have heq : birkhoffAverage ℝ T (-g) (n + 1) x = -birkhoffAverage ℝ T g (n + 1) x := by
    rw [birkhoffAverage_neg]; rfl
  rw [heq] at hbnd
  linarith [hbnd]

/-! ### `limsup` of the Birkhoff averages is a.e. `T`-invariant -/

/-- The pointwise `limsup` of the Birkhoff averages `x ↦ limsup_n (birkhoffAverage ℝ T g n x)`
is a.e. `T`-invariant. Uses the cocycle identity `A_n(g)(Tx) - A_n(g)(x) = n⁻¹(g(Tⁿx) - g x)`
together with the orbital tail estimate `ae_tendsto_orbit_div_atTop_zero` and a.e.
boundedness, via `limsup_eq_of_sub_tendsto_zero`. -/
private theorem limsup_birkhoffAverage_comp_ae [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) :
    (fun x => Filter.limsup (fun n => birkhoffAverage ℝ T g n x) atTop) ∘ T
      =ᵐ[μ] fun x => Filter.limsup (fun n => birkhoffAverage ℝ T g n x) atTop := by
  have hbddA := ae_bddAbove_birkhoffAverage hT hg
  have hbddB := ae_bddBelow_birkhoffAverage hT hg
  have htail := ae_tendsto_orbit_div_atTop_zero hT hg
  -- The same boundedness facts along the shifted orbit `T x`.
  have hbddAT := hT.quasiMeasurePreserving.tendsto_ae hbddA
  have hbddBT := hT.quasiMeasurePreserving.tendsto_ae hbddB
  filter_upwards [hbddA, hbddB, htail, hbddAT, hbddBT] with x hbA hbB htl hbAT hbBT
  show Filter.limsup (fun n => birkhoffAverage ℝ T g n (T x)) atTop
      = Filter.limsup (fun n => birkhoffAverage ℝ T g n x) atTop
  -- Reduce to limsup of the shifted (n+1) sequences.
  rw [← limsup_nat_add (fun n => birkhoffAverage ℝ T g n (T x)) 1,
    ← limsup_nat_add (fun n => birkhoffAverage ℝ T g n x) 1]
  apply limsup_eq_of_sub_tendsto_zero hbAT hbBT hbA hbB
  -- The difference of the two (n+1) sequences tends to `0`.
  have hdiff : (fun n : ℕ => birkhoffAverage ℝ T g (n + 1) (T x)
      - birkhoffAverage ℝ T g (n + 1) x)
      = fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ • (g (T^[n + 1] x) - g x) := by
    funext n
    exact birkhoffAverage_apply_sub_birkhoffAverage T g (n + 1) x
  rw [hdiff]
  -- `((n+1))⁻¹ (g(T^{n+1} x) - g x) → 0`.
  have h1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ * g (T^[n + 1] x)) atTop (𝓝 0) :=
    htl.comp (tendsto_add_atTop_nat 1)
  have hinv0 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have h2 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ * g x) atTop (𝓝 0) := by
    simpa using hinv0.mul_const (g x)
  have hsub := h1.sub h2
  rw [sub_zero] at hsub
  refine hsub.congr (fun n => ?_)
  rw [smul_eq_mul, mul_sub]

/-! ### The core one-sided bound `limsup ≤ μ[g | I]` -/

/-- **Core maximal-inequality step.** For `ε > 0`, the invariant superlevel set where the
`limsup` of the Birkhoff averages strictly exceeds `μ[g | I] + ε` is null.

The set `E = {x | L x + ε < Ls x}` (with `L = μ[g|I]`, `Ls = limsup A_·(g)`) is a.e.
`T`-invariant, so a.e. equal to a genuinely invariant `I`-measurable set `E'`
(`exists_preimage_eq_of_preimage_ae`). Applying the maximal ergodic inequality to
`φ = E'.indicator (g - L - ε)` and showing the maximal set equals `E'`, one gets
`0 ≤ ∫_{E'} (g - L - ε) = -ε · μ E'` (using `∫_{E'} g = ∫_{E'} L`), forcing `μ E' = 0`. -/
private theorem measure_setOf_lt_limsup_eq_zero [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) {ε : ℝ} (hε : 0 < ε) :
    μ {x | (μ[g | MeasurableSpace.invariants T]) x + ε
      < Filter.limsup (fun n => birkhoffAverage ℝ T g n x) atTop} = 0 := by
  classical
  have hTm : Measurable T := hT.measurable
  have hI : MeasurableSpace.invariants T ≤ ‹MeasurableSpace X› := MeasurableSpace.invariants_le T
  set L : X → ℝ := μ[g | MeasurableSpace.invariants T] with hLdef
  set Ls : X → ℝ := fun x => Filter.limsup (fun n => birkhoffAverage ℝ T g n x) atTop with hLsdef
  set E : Set X := {x | L x + ε < Ls x} with hEdef
  -- Invariance facts.
  have hLinv : L ∘ T =ᵐ[μ] L := condExp_invariants_comp_self hT hTm hg
  have hLsinv : Ls ∘ T =ᵐ[μ] Ls := limsup_birkhoffAverage_comp_ae hT hg
  -- `L` is `StronglyMeasurable[I]` hence measurable.
  have hLmeas : Measurable L := (stronglyMeasurable_condExp.mono hI).measurable
  -- `Ls` is a.e. measurable: it agrees a.e. with the limsup of measurable representatives.
  set g₀ : X → ℝ := hg.1.mk with hg₀def
  have hg₀m : Measurable g₀ := hg.1.measurable_mk
  have hgg₀ : g =ᵐ[μ] g₀ := hg.1.ae_eq_mk
  set Ls₀ : X → ℝ := fun x => Filter.limsup (fun n => birkhoffAverage ℝ T g₀ n x) atTop with hLs₀def
  have hLs₀m : Measurable Ls₀ := by
    have hfm : ∀ n : ℕ, Measurable (fun x => birkhoffAverage ℝ T g₀ n x) := by
      intro n
      simp only [birkhoffAverage, smul_eq_mul]
      exact (measurable_birkhoffSum hTm hg₀m n).const_mul _
    exact Measurable.limsup hfm
  have hLseq : Ls =ᵐ[μ] Ls₀ := by
    -- The birkhoff sums of `g` and `g₀` agree a.e. for all `n` simultaneously.
    have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, birkhoffSum T g n x = birkhoffSum T g₀ n x :=
      ae_all_iff.2 (fun n => birkhoffSum_congr_ae hT hgg₀ n)
    filter_upwards [hall] with x hx
    simp only [hLsdef, hLs₀def, birkhoffAverage]
    congr 1; funext n; rw [hx n]
  have hLsaem : AEMeasurable Ls μ := ⟨Ls₀, hLs₀m, hLseq⟩
  -- `E` is null-measurable.
  have hEnull : NullMeasurableSet E μ :=
    nullMeasurableSet_lt (hLmeas.aemeasurable.add_const ε) hLsaem
  -- `E` is a.e. `T`-invariant.
  have hEinv : T ⁻¹' E =ᵐ[μ] E := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [hLinv, hLsinv] with x hLx hLsx
    simp only [Function.comp] at hLx hLsx
    simp only [Set.mem_preimage, hEdef, Set.mem_setOf_eq, hLx, hLsx]
  -- Extract a genuinely invariant `I`-measurable set `E'` with `E' =ᵐ E`.
  obtain ⟨E', hE'm, hE'eq, hE'inv⟩ :=
    hT.quasiMeasurePreserving.exists_preimage_eq_of_preimage_ae hEnull hEinv
  have hE'I : MeasurableSet[MeasurableSpace.invariants T] E' :=
    MeasurableSpace.measurableSet_invariants.2 ⟨hE'm, hE'inv⟩
  -- Orbit stays in/out of `E'`: `T^[k] x ∈ E' ↔ x ∈ E'`.
  have horbit : ∀ (k : ℕ) (x : X), (T^[k] x ∈ E') ↔ (x ∈ E') := by
    intro k x
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        have : T (T^[k] x) ∈ E' ↔ T^[k] x ∈ E' := by
          rw [← Set.mem_preimage, hE'inv]
        rw [this, ih]
  -- The localized function `φ`.
  set φ : X → ℝ := E'.indicator (fun y => g y - L y - ε) with hφdef
  have hφint : Integrable φ μ :=
    ((hg.sub integrable_condExp).sub (integrable_const ε)).indicator hE'm
  -- Maximal ergodic inequality on `φ`.
  have hM1 := setIntegral_birkhoffSum_pos_nonneg hT hφint
  set Bφ : Set X := {x | ∃ n : ℕ, 0 < birkhoffSum T φ (n + 1) x} with hBφdef
  -- For `x ∈ E'`, the partial sums of `φ` are `S_{n+1}(g) - (n+1)(L x + ε)` (a.e.).
  have hSφ : ∀ᵐ x ∂μ, ∀ n : ℕ, x ∈ E' →
      birkhoffSum T φ (n + 1) x
        = birkhoffSum T g (n + 1) x - ((n : ℝ) + 1) * (L x + ε) := by
    filter_upwards [ae_forall_orbit_eq hT hLinv] with x hx n hxE'
    -- On the orbit, `φ (T^[k] x) = g (T^[k] x) - L x - ε`.
    have hval : ∀ k : ℕ, φ (T^[k] x) = g (T^[k] x) - L x - ε := by
      intro k
      have hmem : T^[k] x ∈ E' := (horbit k x).2 hxE'
      simp only [hφdef, Set.indicator_of_mem hmem, hx k]
    have hbs : birkhoffSum T φ (n + 1) x
        = ∑ k ∈ Finset.range (n + 1), (g (T^[k] x) - L x - ε) := by
      simp only [birkhoffSum]
      exact Finset.sum_congr rfl (fun k _ => hval k)
    rw [hbs]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      Finset.sum_const, Finset.card_range]
    simp only [birkhoffSum, nsmul_eq_mul]
    push_cast
    ring
  -- `Bφ =ᵐ E'`.
  have hBφE' : Bφ =ᵐ[μ] E' := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [hSφ, hE'eq, hLseq, ae_bddBelow_birkhoffAverage hT hg]
      with x hSφx hE'x hLsx hbb
    constructor
    · -- `Bφ ⊆ E'` (genuine): off `E'`, all partial sums vanish.
      intro hxB
      by_contra hxE'
      simp only [hBφdef, Set.mem_setOf_eq] at hxB
      obtain ⟨n, hn⟩ := hxB
      have hzero : birkhoffSum T φ (n + 1) x = 0 := by
        simp only [birkhoffSum]
        refine Finset.sum_eq_zero (fun k _ => ?_)
        have hmem : T^[k] x ∉ E' := fun h => hxE' ((horbit k x).1 h)
        simp only [hφdef, Set.indicator_of_notMem hmem]
      rw [hzero] at hn; exact lt_irrefl 0 hn
    · -- `E' ⊆ Bφ` (a.e.): `limsup > L + ε` gives a positive partial sum.
      intro hxE'
      have hxE : x ∈ E := Eq.mp hE'x hxE'
      have hlt : L x + ε < Ls x := hxE
      -- frequently, `A_{n}(g) x > L x + ε`; pick `n = m+1 ≥ 1`.
      have hcobdd : IsCoboundedUnder (· ≤ ·) atTop (fun n => birkhoffAverage ℝ T g n x) := by
        obtain ⟨m, hm⟩ := hbb
        refine IsBoundedUnder.isCoboundedUnder_le ⟨m, ?_⟩
        simp only [eventually_map]
        filter_upwards [eventually_ge_atTop 1] with n hn
        obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
        exact hm (Set.mem_range_self p)
      have hfreq : ∃ᶠ n in atTop, L x + ε < birkhoffAverage ℝ T g n x :=
        frequently_lt_of_lt_limsup hcobdd hlt
      obtain ⟨m, hm⟩ := (hfreq.and_eventually (eventually_ge_atTop 1)).exists
      obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
      have hmg : L x + ε < birkhoffAverage ℝ T g (p + 1) x := hm.1
      simp only [hBφdef, Set.mem_setOf_eq]
      refine ⟨p, ?_⟩
      rw [hSφx p hxE']
      -- `A_{p+1}(g) x > L x + ε ⟺ S_{p+1}(g) x > (p+1)(L x + ε)`.
      have hpos : (0 : ℝ) < (p : ℝ) + 1 := by positivity
      rw [birkhoffAverage, smul_eq_mul] at hmg
      have hcast : (((p + 1 : ℕ)) : ℝ) = (p : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hmg
      rw [lt_inv_mul_iff₀ hpos] at hmg
      nlinarith [hmg]
  -- Conclude: `0 ≤ ∫_{E'} (g - L - ε) = -ε · μ E'`, forcing `μ E' = 0`.
  rw [hBφdef] at hM1
  rw [show {x | ∃ n : ℕ, 0 < birkhoffSum T φ (n + 1) x} = Bφ from rfl] at hM1
  rw [setIntegral_congr_set hBφE'] at hM1
  -- `∫_{E'} φ = ∫_{E'} (g - L - ε)`.
  have hφE' : ∫ x in E', φ x ∂μ = ∫ x in E', (g x - L x - ε) ∂μ := by
    rw [hφdef, setIntegral_indicator hE'm, Set.inter_self]
  rw [hφE'] at hM1
  -- Split and use `∫_{E'} g = ∫_{E'} L`.
  have hcondExp : ∫ x in E', g x ∂μ = ∫ x in E', L x ∂μ :=
    (setIntegral_condExp hI hg hE'I).symm
  have hsplit : ∫ x in E', (g x - L x - ε) ∂μ = - (ε * (μ E').toReal) := by
    have h1 : ∫ x in E', (g x - L x - ε) ∂μ
        = (∫ x in E', (g x - L x) ∂μ) - ∫ x in E', ε ∂μ :=
      integral_sub ((hg.sub integrable_condExp).integrableOn) (integrable_const ε).integrableOn
    have h2 : ∫ x in E', (g x - L x) ∂μ = (∫ x in E', g x ∂μ) - ∫ x in E', L x ∂μ :=
      integral_sub hg.integrableOn integrable_condExp.integrableOn
    rw [h1, h2, hcondExp, sub_self, zero_sub, setIntegral_const]
    simp only [Measure.real, smul_eq_mul]
    ring
  rw [hsplit] at hM1
  -- `0 ≤ -ε μE'` with `ε > 0` ⟹ `μ E' = 0`.
  have hμE'real : (μ E').toReal = 0 := by
    have : ε * (μ E').toReal ≤ 0 := by linarith [hM1]
    nlinarith [ENNReal.toReal_nonneg (a := μ E'), this, hε]
  have hμE'zero : μ E' = 0 :=
    (ENNReal.toReal_eq_zero_iff _).1 hμE'real |>.resolve_right (measure_ne_top μ _)
  -- `μ E = μ E' = 0`.
  have : μ E' = μ E := measure_congr hE'eq
  rw [hEdef] at this
  rw [← this]
  exact hμE'zero

/-- A.e. `limsup` of the Birkhoff averages is `≤ μ[g | I]`: union the null superlevel sets
`{L + 1/(k+1) < Ls}` from `measure_setOf_lt_limsup_eq_zero` over `k`. -/
private theorem limsup_le_condExp_ae [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Filter.limsup (fun n => birkhoffAverage ℝ T g n x) atTop
      ≤ (μ[g | MeasurableSpace.invariants T]) x := by
  set L : X → ℝ := μ[g | MeasurableSpace.invariants T] with hLdef
  set Ls : X → ℝ := fun x => Filter.limsup (fun n => birkhoffAverage ℝ T g n x) atTop with hLsdef
  -- Each superlevel set `{L + 1/(k+1) < Ls}` is null.
  have hnull : ∀ k : ℕ, μ {x | L x + (1 / (k + 1) : ℝ) < Ls x} = 0 := fun k =>
    measure_setOf_lt_limsup_eq_zero hT hg (by positivity)
  -- The set where `Ls > L` is contained in their union, hence null.
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null hnull)
  simp only [Set.mem_setOf_eq, not_le] at hx
  rw [Set.mem_iUnion]
  -- `L x < Ls x` gives some `k` with `L x + 1/(k+1) < Ls x`.
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (Ls x - L x))
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  refine ⟨k, ?_⟩
  simp only [Set.mem_setOf_eq]
  have hdiff : (0 : ℝ) < Ls x - L x := by linarith
  rw [div_lt_iff₀ hdiff] at hk
  have : (1 / ((k : ℝ) + 1)) < Ls x - L x := by
    rw [div_lt_iff₀ hkpos]
    nlinarith [hk, hdiff]
  linarith

/-- A.e. `liminf` of the Birkhoff averages is `≥ μ[g | I]`: apply `limsup_le_condExp_ae`
to `-g`, using `birkhoffAverage_neg`, `condExp_neg`, and `limsup (-a) = -liminf a`. -/
private theorem condExp_le_liminf_ae [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, (μ[g | MeasurableSpace.invariants T]) x
      ≤ Filter.liminf (fun n => birkhoffAverage ℝ T g n x) atTop := by
  have hneg := limsup_le_condExp_ae hT hg.neg
  have hcondneg : μ[-g | MeasurableSpace.invariants T] =ᵐ[μ]
      -μ[g | MeasurableSpace.invariants T] := condExp_neg g _
  have hbb := ae_bddBelow_birkhoffAverage hT hg
  have hba := ae_bddAbove_birkhoffAverage hT hg
  filter_upwards [hneg, hcondneg, hbb, hba] with x hx hcn hbbx hbax
  -- `limsup A_·(-g) x = - liminf A_·(g) x`.
  have hbav : (fun n => birkhoffAverage ℝ T (-g) n x)
      = fun n => -birkhoffAverage ℝ T g n x := by
    funext n; rw [birkhoffAverage_neg]; rfl
  -- boundedness for the antitone-map lemma.
  have hbddAbove : IsBoundedUnder (· ≤ ·) atTop (fun n => birkhoffAverage ℝ T g n x) := by
    obtain ⟨M, hM⟩ := hbax
    refine ⟨M, ?_⟩
    simp only [eventually_map]
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    exact hM (Set.mem_range_self p)
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop (fun n => birkhoffAverage ℝ T g n x) :=
    hbddAbove.isCoboundedUnder_ge
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (fun n => birkhoffAverage ℝ T g n x) := by
    obtain ⟨m, hm⟩ := hbbx
    refine ⟨m, ?_⟩
    simp only [eventually_map]
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    exact hm (Set.mem_range_self p)
  have hanti : Antitone (fun y : ℝ => -y) := fun _ _ h => by simpa using h
  have hmap : -(Filter.liminf (fun n => birkhoffAverage ℝ T g n x) atTop)
      = Filter.limsup (fun n => birkhoffAverage ℝ T (-g) n x) atTop := by
    rw [hbav]
    have := hanti.map_liminf_of_continuousAt (fun n => birkhoffAverage ℝ T g n x)
      (continuousAt_neg) hcobdd hbdd
    simpa using this
  -- Now `limsup A_·(-g) x ≤ μ[-g|I] x = -L x`, so `-liminf ≤ -L`, i.e. `L ≤ liminf`.
  rw [hcn] at hx
  rw [← hmap] at hx
  simp only [Pi.neg_apply] at hx
  linarith

/-- **Pointwise (Birkhoff) ergodic theorem** (layer `L1.3` / `M3`): for a finite measure,
a measure-preserving `T`, and integrable `g`, the Birkhoff averages converge `μ`-a.e. to
the conditional expectation of `g` onto the σ-algebra of `T`-invariant sets. Sandwiches
the a.e. bounds `limsup ≤ μ[g|I]` and `μ[g|I] ≤ liminf` via
`tendsto_of_le_liminf_of_limsup_le`.

The `[IsFiniteMeasure μ]` hypothesis is necessary: without it (e.g. when the trim of `μ`
to `invariants T` is not σ-finite) `μ[g | invariants T] = 0` while the Birkhoff averages
need not converge to `0`. The Oseledets MET only ever uses this for probability measures,
where it applies directly. -/
theorem tendsto_birkhoffAverage_ae [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T g n x) atTop
      (𝓝 ((μ[g | MeasurableSpace.invariants T]) x)) := by
  filter_upwards [limsup_le_condExp_ae hT hg, condExp_le_liminf_ae hT hg,
    ae_bddAbove_birkhoffAverage hT hg, ae_bddBelow_birkhoffAverage hT hg]
    with x hsup hinf hba hbb
  -- Boundedness over `atTop` of the full sequence `n ↦ A_n(g) x`.
  have hbddAbove : IsBoundedUnder (· ≤ ·) atTop (fun n => birkhoffAverage ℝ T g n x) := by
    obtain ⟨M, hM⟩ := hba
    refine ⟨M, ?_⟩
    simp only [eventually_map]
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    exact hM (Set.mem_range_self p)
  have hbddBelow : IsBoundedUnder (· ≥ ·) atTop (fun n => birkhoffAverage ℝ T g n x) := by
    obtain ⟨m, hm⟩ := hbb
    refine ⟨m, ?_⟩
    simp only [eventually_map]
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    exact hm (Set.mem_range_self p)
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup hbddAbove hbddBelow

/-- **Birkhoff ergodic theorem, ergodic case**: when `T` is ergodic for a probability
measure, the Birkhoff averages converge `μ`-a.e. to the space average `∫ g dμ`. -/
theorem tendsto_birkhoffAverage_ae_integral
    [IsProbabilityMeasure μ] (hT : Ergodic T μ) {g : X → ℝ} (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T g n x) atTop (𝓝 (∫ y, g y ∂μ)) := by
  have hmp : MeasurePreserving T μ μ := hT.toMeasurePreserving
  have hI : MeasurableSpace.invariants T ≤ ‹MeasurableSpace X› := MeasurableSpace.invariants_le T
  -- The a.e. limit is `μ[g | I]`.
  have hbirk := tendsto_birkhoffAverage_ae hmp hg
  -- `μ[g | I]` is a.e. `T`-invariant, hence (ergodicity) a.e. constant.
  have hcomp : (μ[g | MeasurableSpace.invariants T]) ∘ T
      =ᵐ[μ] μ[g | MeasurableSpace.invariants T] :=
    condExp_invariants_comp_self hmp hT.measurable hg
  have haesm : AEStronglyMeasurable (μ[g | MeasurableSpace.invariants T]) μ :=
    (stronglyMeasurable_condExp.mono hI).aestronglyMeasurable
  obtain ⟨c, hc⟩ := hT.ae_eq_const_of_ae_eq_comp_ae
    (g := μ[g | MeasurableSpace.invariants T]) haesm hcomp
  -- The constant is `∫ g`, since `∫ μ[g|I] = ∫ g` and `∫ (const c) = c`.
  have hcval : c = ∫ y, g y ∂μ := by
    have h1 : ∫ x, (μ[g | MeasurableSpace.invariants T]) x ∂μ = ∫ y, g y ∂μ :=
      integral_condExp hI
    have h2 : ∫ x, (μ[g | MeasurableSpace.invariants T]) x ∂μ = ∫ _x, c ∂μ :=
      integral_congr_ae hc
    rw [h2, integral_const, probReal_univ, one_smul] at h1
    exact h1
  -- Rewrite the limit.
  filter_upwards [hbirk, hc] with x hx hcx
  rw [hcx, hcval] at hx
  exact hx

end Oseledets
