/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.Forward
import Oseledets.Lyapunov.OseledetsLimit

/-!
# Tempered angles and the spectral upper bound for slow vectors

Let `Pₙ = bandProjector A T (Set.indicator (Set.Ioi c) 1) n x` denote the projector onto the
fast Oseledets band at the cut `c = exp λᵢ` (the band of `qpow`-eigenvalues `> exp λᵢ`),
converging to a limit projector `Pinf`, and call a vector `v` *slow* when
`toEuclideanLin Pinf v = 0`. This file proves the spectral upper bound

    limsup_n (1/n)·log ‖toEuclideanLin (cocycle A T n x) v‖ ≤ λᵢ

for a slow vector `v`, without assuming the a-priori growth bound `lambdaBar A T x v ≤ λᵢ`.

## The tempering mechanism

On their own, the slow-growth upper bound and the slow–fast overlap leak are mutually
equivalent: `oⱼ ≤ g − λⱼ` and `g ≤ maxⱼ(λⱼ+oⱼ)` compose to the vacuous `g ≤ g`. The genuine
content needed to break this circle is that the slow–fast overlap decays at a strictly negative
exponential rate — the splitting is *tempered*. We obtain this rate without an a-priori
slow-growth assumption, from the qualitative convergence of the band projector together with
the quantitative per-step increment bound.

`Oseledets.limsup_inv_mul_log_norm_cocycle_apply_le` reduces the per-vector upper bound to a
per-spectral-index exponential envelope `henv j`:
`specTerm A n x v j = σⱼ(n)²·⟪v,uⱼ(n)⟫² ≤ exp(n(2λᵢ+ε))`. For a fast index (`λⱼ > λᵢ`), since
`σⱼ(n)² ~ exp(2nλⱼ)` blows up, the overlap `⟪v,uⱼ(n)⟫²` must decay at rate `2(λᵢ − λⱼ) < 0`.

The handle identity `Oseledets.inner_eq_inner_bandProjector_sub_limit` gives, for slow `v` and
a step-`n` fast eigenvector `uⱼ(n)` (so `Pₙ uⱼ = uⱼ`):

    ⟪v, uⱼ(n)⟫ = ⟪v, (Pₙ − Pinf) uⱼ(n)⟫,   so   |⟪v, uⱼ(n)⟫| ≤ ‖v‖ · ‖Pₙ − Pinf‖.

The rate of `⟪v, uⱼ⟫` is therefore controlled by the rate of the *projector tilt*
`‖Pₙ − Pinf‖`. The quantitative layer (`Oseledets.norm_bandProjector_succ_sub_le_cocycle`,
`Oseledets.tendsto_log_bCocycle_point`) gives the per-step bound `‖Pₙ₊₁ − Pₙ‖ ≤ b(n)` with
`(1/n) log b(n) → L < 0`, where `L = λₖ − λₖ₋₁` is the spectral gap at the cut. Mathlib's
`dist_le_tsum_of_dist_le_of_tendsto` then bounds the *tail*:

    ‖Pₙ − Pinf‖ ≤ ∑'_m b(n+m),

and the geometric tail inherits the rate: `limsup (1/n) log (∑'_m b(n+m)) ≤ L`. This is the
*tempered-angle bound*: the slow–fast angle is subexponential with a strictly negative log-rate
`L`, supplied by convergence plus a spectral gap, not by an assumed growth rate.

## Main results

1. `tsum_tail_le_geometric`, `limsup_log_tsum_tail_le` — the abstract tempering lemma: a
   sequence `b ≥ 0` with negative log-rate `(1/n)log b → L < 0` has its tail sums `∑'_m b(n+m)`
   decaying at the same rate, `limsup (1/n) log (tail) ≤ L`.
2. `eventually_norm_sub_tendsto_le_exp` — for any convergent sequence `f → a` in a complete
   normed space with tempered increments `‖f(n+1)−f n‖ ≤ b n`: the distance to the limit is
   subexponential, `∀ ε>0, ∀ᶠ n, ‖f n − a‖ ≤ exp(n(L+ε))` (zero-safe, no `log 0`).
3. `eventually_norm_bandProjector_sub_le_exp` — the band-projector tilt `‖Pₙ − Pinf‖` is
   tempered with the negative rate `L` (convergence plus the per-step increment bound, through
   (2)): the tempered angle between the step-`n` and limit fast bands.
4. `eventually_inner_sq_le_exp_of_tilt` — the slow–fast overlap envelope
   `⟪v, uⱼ(n)⟫² ≤ (‖v‖U)²·exp(2n(L+ε))` (handle identity + (3)); the negative overlap rate,
   with no slow-growth assumption on `v`.
5. `specTerm_envelope_of_tempered_overlap` — the per-index `specTerm` envelope `henv j`,
   `σⱼ(n)²⟪v,uⱼ⟫² ≤ exp(n(2λᵢ+ε))` (overlap × singular envelope), under the rate balance
   `λⱼ + L ≤ λᵢ`. Zero-safe.
6. `limsup_log_norm_cocycle_apply_le_of_tempered_envelopes` — the spectral upper bound
   `limsup (1/n)log‖A⁽ⁿ⁾v‖ ≤ λᵢ` from the per-index envelopes (via
   `Oseledets.limsup_inv_mul_log_norm_cocycle_apply_le`).
7. `specTerm_envelope_henv_of_convergence` — the per-index closure chaining (3)→(4)→(5): from
   band convergence, tempered increments, the singular-value limit, fast-band membership of
   `sortedGramEigenbasis`, and the rate balance, to the envelope `henv j`.

## The multi-gap condition

The per-index rate balance `λⱼ + L ≤ λᵢ` is the load-bearing condition. Here `L` is the gap
straddling the cut `c = exp λᵢ` (`L = λ_k − λ_{k−1}`, last-fast minus first-slow exponents).
For the nearest fast index `j = k−1` it holds with equality
(`λ_{k−1} + (λ_k − λ_{k−1}) = λ_k ≤ λᵢ`). For deeper fast indices (`λⱼ ≫ λᵢ`) the single
straddling gap `L` is insufficient (`λⱼ + L > λᵢ`): the multi-gap product of intermediate gap
ratios is not realized by a single-cut projector tilt. Closing every index needs either (a) the
tempered tilt applied at each intermediate cut and telescoped (a slow vector `v` is killed by
every higher-threshold limit projector by band nesting, `bandProjector_mul_of_le`, but each cut
supplies only its own one-step gap), or (b) an adapted (Lyapunov) norm in which the cocycle is
block-diagonal up to `exp(εn)` and the norm-equivalence constant absorbs the gap product
(itself tempered). The lemmas below close every index for which the per-index rate balance
holds — in particular the nearest gap, hence the first nontrivial slow stratum.
-/

open MeasureTheory Filter Topology
open scoped Matrix InnerProductSpace Matrix.Norms.L2Operator

namespace Oseledets.Tempering

/-! ## 1. The abstract tempering lemma: tail sums inherit the negative log-rate -/

/-- **Geometric tail bound.** If `b m ≤ exp(m·s)` for all `m ≥ N` and `s < 0` (so `exp s < 1`),
then for `n ≥ N` the tail `∑'_m b(n+m)` is summable and bounded by
`exp(n·s) / (1 − exp s)`. -/
theorem tsum_tail_le_geometric {b : ℕ → ℝ} {s : ℝ} {N : ℕ}
    (hbnn : ∀ m, 0 ≤ b m) (hs : s < 0)
    (hble : ∀ m, N ≤ m → b m ≤ Real.exp (m * s)) {n : ℕ} (hn : N ≤ n) :
    (∑' m, b (n + m)) ≤ Real.exp (n * s) / (1 - Real.exp s) := by
  have hes1 : Real.exp s < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]; exact Real.exp_lt_exp.mpr hs
  have hes0 : 0 < Real.exp s := Real.exp_pos s
  -- termwise: b (n+m) ≤ exp(n s) * (exp s)^m
  have hterm : ∀ m, b (n + m) ≤ Real.exp (n * s) * (Real.exp s) ^ m := by
    intro m
    have : b (n + m) ≤ Real.exp ((n + m : ℕ) * s) := hble (n + m) (by omega)
    refine this.trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast; ring
  -- the dominating geometric series is summable
  have hgeom : Summable (fun m => Real.exp (n * s) * (Real.exp s) ^ m) :=
    (summable_geometric_of_lt_one (le_of_lt hes0) hes1).mul_left _
  have hbsummable : Summable (fun m => b (n + m)) :=
    hgeom.of_nonneg_of_le (fun m => hbnn _) hterm
  calc (∑' m, b (n + m)) ≤ ∑' m, Real.exp (n * s) * (Real.exp s) ^ m :=
        hbsummable.tsum_le_tsum hterm hgeom
    _ = Real.exp (n * s) * (1 - Real.exp s)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (le_of_lt hes0) hes1]
    _ = Real.exp (n * s) / (1 - Real.exp s) := by rw [div_eq_mul_inv]

/-- **Tempering lemma (tail-rate form).** Let `b ≥ 0`, eventually positive, with
`(1/n)·log (b n) → L < 0` (the root-test hypothesis; `b` is summable and geometric-like). Then the
*tail sums* `T n := ∑'_m b(n+m)` obey

    limsup_n (1/n)·log (T n)  ≤  L.

The tail inherits the negative exponential rate `L` of `b` itself. This converts a.e.
convergence-with-gap (a per-step rate) into a uniform subexponential bound on the distance to
the limit. -/
theorem limsup_log_tsum_tail_le {b : ℕ → ℝ} {L : ℝ}
    (hbnn : ∀ n, 0 ≤ b n) (hbpos : ∀ᶠ n in atTop, 0 < b n) (hL : L < 0)
    (hlog : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (b n)) atTop (𝓝 L)) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (∑' m, b (n + m))) atTop ≤ L := by
  set g : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * Real.log (∑' m, b (n + m)) with hg
  -- it suffices to show `limsup g ≤ s` for every `s ∈ (L, 0)`; then `s → L⁺` gives `≤ L`.
  have hkey : ∀ s : ℝ, L < s → s < 0 → limsup g atTop ≤ s := by
    intro s hLs hs0
    -- per-term envelope `b m ≤ exp(m s)` eventually.
    have henv : ∀ᶠ m : ℕ in atTop, b m ≤ Real.exp (m * s) := by
      have hev := hlog.eventually (gt_mem_nhds (show L < s from hLs))
      filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm1
      rcases lt_or_ge 0 (b m) with hbp | hble0
      · have hlt : Real.log (b m) < (m : ℝ) * s := by
          have hmul := mul_lt_mul_of_pos_left hm hmpos
          rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hmpos), one_mul] at hmul
        calc b m = Real.exp (Real.log (b m)) := (Real.exp_log hbp).symm
          _ ≤ Real.exp ((m : ℝ) * s) := Real.exp_le_exp.mpr (le_of_lt hlt)
      · exact hble0.trans (Real.exp_nonneg _)
    obtain ⟨N, hN⟩ := eventually_atTop.mp henv
    obtain ⟨Np, hNp⟩ := eventually_atTop.mp hbpos
    have hctt : 0 < 1 - Real.exp s := by
      have : Real.exp s < 1 := by
        rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]; exact Real.exp_lt_exp.mpr hs0
      linarith
    set C := Real.log ((1 - Real.exp s)⁻¹) with hC
    -- eventual upper envelope on `g`: `g n ≤ s + (1/n)·C`.
    have htail : ∀ᶠ n : ℕ in atTop, g n ≤ s + (n : ℝ)⁻¹ * C := by
      filter_upwards [eventually_ge_atTop (max (max N Np) 1)] with n hn
      have hnN : N ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
      have hnNp : Np ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
      have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
      have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
      have hbound := tsum_tail_le_geometric hbnn hs0 hN hnN
      -- tail is positive: `b (n+0) > 0` and all terms ≥ 0.
      have hbn0 : 0 < b (n + 0) := by simpa using hNp n hnNp
      have hTpos : 0 < ∑' m, b (n + m) := by
        have hsummable : Summable (fun m => b (n + m)) := by
          have hgeom : Summable (fun m => Real.exp (n * s) * (Real.exp s) ^ m) :=
            (summable_geometric_of_lt_one (le_of_lt (Real.exp_pos s))
              (by rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm];
                  exact Real.exp_lt_exp.mpr hs0)).mul_left _
          refine hgeom.of_nonneg_of_le (fun m => hbnn _) (fun m => ?_)
          have : b (n + m) ≤ Real.exp ((n + m : ℕ) * s) := hN (n + m) (by omega)
          refine this.trans (le_of_eq ?_)
          rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
        refine lt_of_lt_of_le hbn0 (hsummable.le_tsum 0 (fun i _ => hbnn _))
      -- `log T n ≤ n s + C`.
      have hlogle : Real.log (∑' m, b (n + m)) ≤ (n : ℝ) * s + C := by
        have h1 : Real.log (∑' m, b (n + m))
            ≤ Real.log (Real.exp (n * s) / (1 - Real.exp s)) :=
          Real.log_le_log hTpos hbound
        rw [Real.log_div (Real.exp_ne_zero _) (ne_of_gt hctt), Real.log_exp] at h1
        rw [hC, Real.log_inv]; linarith [h1]
      calc g n = (n : ℝ)⁻¹ * Real.log (∑' m, b (n + m)) := rfl
        _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * s + C) := mul_le_mul_of_nonneg_left hlogle hninv
        _ = s + (n : ℝ)⁻¹ * C := by
            rw [mul_add, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hnpos), one_mul]
    -- the RHS `s + (1/n)·C` tends to `s`, so its limsup is `s`; dominate `g`.
    have hrhs_tend : Tendsto (fun n : ℕ => s + (n : ℝ)⁻¹ * C) atTop (𝓝 s) := by
      have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
        tendsto_natCast_atTop_atTop.inv_tendsto_atTop
      have := (tendsto_const_nhds (x := s)).add (hinv.mul_const C)
      simpa using this
    have hrhs_limsup : limsup (fun n : ℕ => s + (n : ℝ)⁻¹ * C) atTop = s := hrhs_tend.limsup_eq
    have hrhs_bdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => s + (n : ℝ)⁻¹ * C) :=
      hrhs_tend.isBoundedUnder_le
    -- `g` is bounded above (by the eventual envelope) and cobounded.
    have hg_bdd : IsBoundedUnder (· ≤ ·) atTop g := by
      obtain ⟨B, hB⟩ := hrhs_bdd
      rw [eventually_map] at hB
      refine ⟨B, ?_⟩
      rw [eventually_map]
      filter_upwards [htail, hB] with n h1 h2 using h1.trans h2
    -- `g` is bounded below: `g n = (1/n) log T(n) ≥ (1/n) log b(n) → L`, since `T(n) ≥ b(n)`.
    have hg_lb : ∀ᶠ n : ℕ in atTop, L - 1 ≤ g n := by
      have hblog_ev := hlog.eventually (eventually_gt_nhds (show L - 1 < L by linarith))
      filter_upwards [hblog_ev, eventually_ge_atTop (max (max N Np) 1)] with n hn hge
      have hnN : N ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hge
      have hnNp : Np ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hge
      have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hge
      have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
      have hbn0 : 0 < b (n + 0) := by simpa using hNp n hnNp
      -- `T(n) ≥ b(n+0) = b n`.
      have hsummable : Summable (fun m => b (n + m)) := by
        have hgeom : Summable (fun m => Real.exp (n * s) * (Real.exp s) ^ m) :=
          (summable_geometric_of_lt_one (le_of_lt (Real.exp_pos s))
            (by rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm];
                exact Real.exp_lt_exp.mpr hs0)).mul_left _
        refine hgeom.of_nonneg_of_le (fun m => hbnn _) (fun m => ?_)
        have : b (n + m) ≤ Real.exp ((n + m : ℕ) * s) := hN (n + m) (by omega)
        refine this.trans (le_of_eq ?_)
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
      have hTge : b n ≤ ∑' m, b (n + m) := by
        have := hsummable.le_tsum 0 (fun i _ => hbnn _)
        simpa using this
      have hbn0' : 0 < b n := by simpa using hbn0
      have hloge : Real.log (b n) ≤ Real.log (∑' m, b (n + m)) :=
        Real.log_le_log hbn0' hTge
      -- `g n = (1/n) log T(n) ≥ (1/n) log b(n) > L - 1`.
      have hgge : (n : ℝ)⁻¹ * Real.log (b n) ≤ g n :=
        mul_le_mul_of_nonneg_left hloge hninv
      have hblow : L - 1 < (n : ℝ)⁻¹ * Real.log (b n) := hn
      linarith
    have hg_cob : IsCoboundedUnder (· ≤ ·) atTop g :=
      (IsBoundedUnder.isCoboundedUnder_le ⟨L - 1, by
        rw [eventually_map]; exact hg_lb⟩)
    calc limsup g atTop ≤ limsup (fun n : ℕ => s + (n : ℝ)⁻¹ * C) atTop :=
          limsup_le_limsup htail hg_cob hrhs_bdd
      _ = s := hrhs_limsup
  -- `limsup g ≤ s` for all `s ∈ (L, 0)` ⟹ `limsup g ≤ L`.
  by_contra hcon
  rw [not_le] at hcon
  -- `L < limsup g`; pick `s` strictly between `L` and `min(0, limsup g)`.
  set m := min ((L + limsup g atTop) / 2) (L / 2) with hm
  have hLm : L < m := by
    rw [hm]; refine lt_min ?_ ?_ <;> linarith
  have hm0 : m < 0 := by
    rw [hm]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hmls : m < limsup g atTop := by
    rw [hm]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  exact absurd (hkey m hLm hm0) (not_le.mpr hmls)

/-! ## 2. Tempered distance-to-limit for a convergent sequence with tempered increments -/

/-- **Tempered distance-to-limit (exp-envelope form, general normed space).** Let `f : ℕ → F`
converge to `a` in a complete normed space, with increments eventually bounded by a tempered
sequence `b ≥ 0`: `∀ᶠ n, ‖f (n+1) − f n‖ ≤ b n`, `b` eventually positive,
`(1/n)·log (b n) → L < 0`. Then the distance to the limit decays subexponentially with the same
rate: for every `ε > 0`,

    ∀ᶠ n, ‖f n − a‖ ≤ exp (n · (L + ε)).

The proof bounds `‖f n − a‖ = dist (f n) a ≤ ∑'_m d(n+m)` (`dist_le_tsum_of_dist_le_of_tendsto`,
`d` = actual increments, summable by `summable_norm_of_logLimit_neg_of_le`), then dominates the
tail by a geometric `b`-tail (`tsum_tail_le_geometric`). This is the **tempered-angle
exp-envelope** used by the per-index leakage bound; it is zero-safe (`exp ≥ 0` even when
`f n = a`). -/
theorem eventually_norm_sub_tendsto_le_exp {F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    {f : ℕ → F} {a : F} {b : ℕ → ℝ} {L : ℝ}
    (hf : Tendsto f atTop (𝓝 a))
    (hbnn : ∀ n, 0 ≤ b n) (hbpos : ∀ᶠ n in atTop, 0 < b n) (hL : L < 0)
    (hlog : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (b n)) atTop (𝓝 L))
    (hstep : ∀ᶠ n in atTop, ‖f (n + 1) - f n‖ ≤ b n)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ‖f n - a‖ ≤ Real.exp ((n : ℝ) * (L + ε)) := by
  -- summability of the actual increments `d n = dist (f n) (f (n+1)) = ‖f(n+1) − f n‖`.
  have hincr_sum : Summable (fun n => ‖f (n + 1) - f n‖) :=
    summable_norm_of_logLimit_neg_of_le (fun n => f (n + 1) - f n) b hbnn hbpos hL hlog hstep
  set d : ℕ → ℝ := fun n => dist (f n) (f (n + 1)) with hd
  have hdeq : ∀ n, d n = ‖f (n + 1) - f n‖ := fun n => by
    change dist (f n) (f (n + 1)) = _; rw [dist_eq_norm, norm_sub_rev]
  have hdsum : Summable d := hincr_sum.congr (fun n => (hdeq n).symm)
  have hdnn : ∀ n, 0 ≤ d n := fun n => dist_nonneg
  -- distance-to-limit tail bound: `‖f n − a‖ = dist (f n) a ≤ ∑'_m d (n+m)`.
  have hdist : ∀ n, ‖f n - a‖ ≤ ∑' m, d (n + m) := by
    intro n
    have := dist_le_tsum_of_dist_le_of_tendsto d (fun k => le_of_eq (by rw [hd])) hdsum hf n
    rwa [dist_eq_norm] at this
  -- choose `s := L + ε/2 < 0` with `L < s < L + ε`.
  set s := L + ε / 2 with hs
  rcases le_or_gt 0 s with hs0 | hs0
  · -- if `s ≥ 0` (large ε), the envelope is trivial: `‖f n − a‖ ≤ d-tail` is bounded, and the RHS
    -- `exp(n(L+ε)) → ∞` dominates. We use the simpler bound `‖f n − a‖ → 0 ≤ exp(...)`.
    have hfa : Tendsto (fun n => ‖f n - a‖) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n => f n - a) atTop (𝓝 (a - a)) :=
        hf.sub (tendsto_const_nhds (x := a))
      rw [sub_self] at h0
      have := h0.norm
      simpa using this
    -- eventually `‖f n − a‖ ≤ 1 ≤ exp(n(L+ε))` once `n(L+ε) ≥ 0`.
    have hLε : 0 < L + ε := by linarith
    filter_upwards [hfa.eventually_le_const (show (0:ℝ) < 1 by norm_num)] with n hn
    have hexp1 : (1 : ℝ) ≤ Real.exp ((n : ℝ) * (L + ε)) :=
      Real.one_le_exp (by positivity)
    exact hn.trans hexp1
  · -- the geometric-tail route.
    have hLs : L < s := by rw [hs]; linarith
    have hsε : s < L + ε := by rw [hs]; linarith
    -- per-term envelope `d m ≤ exp(m s)` eventually (since `d m ≤ b m ≤ exp(m s)`).
    have henvb : ∀ᶠ m : ℕ in atTop, b m ≤ Real.exp (m * s) := by
      have hev := hlog.eventually (gt_mem_nhds (show L < s from hLs))
      filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm1
      rcases lt_or_ge 0 (b m) with hbp | hble0
      · have hlt : Real.log (b m) < (m : ℝ) * s := by
          have hmul := mul_lt_mul_of_pos_left hm hmpos
          rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hmpos), one_mul] at hmul
        calc b m = Real.exp (Real.log (b m)) := (Real.exp_log hbp).symm
          _ ≤ Real.exp ((m : ℝ) * s) := Real.exp_le_exp.mpr (le_of_lt hlt)
      · exact hble0.trans (Real.exp_nonneg _)
    obtain ⟨Nb, hNb⟩ := eventually_atTop.mp henvb
    obtain ⟨Ns, hNs⟩ := eventually_atTop.mp hstep
    set N := max Nb Ns with hNdef
    have hdle : ∀ m, N ≤ m → d m ≤ Real.exp (m * s) := by
      intro m hm
      have hmNs : Ns ≤ m := le_trans (le_max_right _ _) hm
      have hmNb : Nb ≤ m := le_trans (le_max_left _ _) hm
      rw [hdeq]; exact (hNs m hmNs).trans (hNb m hmNb)
    have hctt : 0 < 1 - Real.exp s := by
      have : Real.exp s < 1 := by
        rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]; exact Real.exp_lt_exp.mpr hs0
      linarith
    -- the subexponential constant `(1−exp s)⁻¹` is eventually dominated by `exp(n·ε/2)`.
    have hconst_dom : ∀ᶠ n : ℕ in atTop, (1 - Real.exp s)⁻¹ ≤ Real.exp ((n : ℝ) * (ε / 2)) := by
      have hgrow : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (ε / 2))) atTop atTop := by
        apply Real.tendsto_exp_atTop.comp
        apply Filter.Tendsto.atTop_mul_const (by linarith)
        exact tendsto_natCast_atTop_atTop
      exact hgrow.eventually_ge_atTop _
    -- the geometric tail bound for `d`, combined with the eventual constant domination.
    filter_upwards [eventually_ge_atTop (max N 1), hconst_dom] with n hn hcon
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have htailbound := tsum_tail_le_geometric hdnn hs0 hdle hnN
    have hub : ‖f n - a‖ ≤ Real.exp (n * s) / (1 - Real.exp s) := (hdist n).trans htailbound
    refine hub.trans ?_
    rw [div_le_iff₀ hctt]
    -- `exp(n s)·1 = exp(n s) ≤ exp(n(L+ε))·(1−exp s)`:
    -- `exp(n(L+ε))·(1−exp s) = exp(n(L+ε/2))·exp(nε/2)·(1−exp s)`
    --   `≥ exp(ns)·(1−exp s)⁻¹·(1−exp s) = exp(ns)`
    -- using `exp(nε/2) ≥ (1−exp s)⁻¹` and `s = L+ε/2`.
    have hsval : s = L + ε / 2 := hs
    have hsplit : (n : ℝ) * (L + ε) = (n : ℝ) * s + (n : ℝ) * (ε / 2) := by
      rw [hsval]; ring
    rw [hsplit, Real.exp_add]
    have hstep1 : (1 - Real.exp s) * (1 - Real.exp s)⁻¹ = 1 := by
      rw [mul_inv_cancel₀ (ne_of_gt hctt)]
    calc Real.exp ((n:ℝ) * s)
        = Real.exp ((n:ℝ) * s) * ((1 - Real.exp s) * (1 - Real.exp s)⁻¹) := by rw [hstep1, mul_one]
      _ = Real.exp ((n:ℝ) * s) * (1 - Real.exp s)⁻¹ * (1 - Real.exp s) := by ring
      _ ≤ Real.exp ((n:ℝ) * s) * Real.exp ((n:ℝ) * (ε/2)) * (1 - Real.exp s) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hctt)
          apply mul_le_mul_of_nonneg_left hcon (Real.exp_nonneg _)

/-! ## 3. The tempered tilt of the band projector

Instantiate the abstract tempered distance-to-limit at the Oseledets band projector
`Pₙ = bandProjector A T (indicator (Ioi c) 1) n x`, converging to `Pinf`, with the per-step
increment bound `‖Pₙ₊₁ − Pₙ‖ ≤ b n` and the negative root-test log-limit
`(1/n) log (b n) → L < 0` (`L = lamK − lamK1`, the spectral gap straddling the cut `c`). The
matrix space `Matrix (Fin d) (Fin d) ℝ` is a complete normed space, so the abstract lemma
applies verbatim. -/

open Oseledets in
/-- **Tempered band-projector tilt (exp-envelope).** At a point `x` where the band projector
`Pₙ = bandProjector A T (indicator (Ioi c) 1) n x` converges to `Pinf`, with per-step increments
bounded by a tempered `b` (negative root-test rate `L < 0`), the tilt is subexponential: for
every `ε > 0`, eventually `‖Pₙ − Pinf‖ ≤ exp(n(L+ε))`. This is the **tempered angle** between
the step-`n` and limit fast bands; the negative rate comes from convergence plus a spectral
gap. -/
theorem eventually_norm_bandProjector_sub_le_exp
    {X : Type*} [MeasurableSpace X] {d : ℕ}
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (c : ℝ) (x : X)
    {Pinf : Matrix (Fin d) (Fin d) ℝ} {b : ℕ → ℝ} {L : ℝ}
    (hP : Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) atTop (𝓝 Pinf))
    (hbnn : ∀ n, 0 ≤ b n) (hbpos : ∀ᶠ n in atTop, 0 < b n) (hL : L < 0)
    (hlog : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (b n)) atTop (𝓝 L))
    (hstep : ∀ᶠ n in atTop,
      ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
          - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖ ≤ b n)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) n x - Pinf‖
        ≤ Real.exp ((n : ℝ) * (L + ε)) :=
  eventually_norm_sub_tendsto_le_exp
    (f := fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)
    hP hbnn hbpos hL hlog hstep ε hε

/-! ## 4. The slow–fast overlap exp-envelope (handle identity + tempered tilt)

For a slow `v` (`toEuclideanLin Pinf v = 0`) and a step-`n` fast eigenvector `uⱼ(n)`
(`toEuclideanLin Pₙ uⱼ = uⱼ`), the handle identity
(`Oseledets.inner_eq_inner_bandProjector_sub_limit`) gives
`⟪v, uⱼ⟫ = ⟪v, (Pₙ − Pinf) uⱼ⟫`, whence `|⟪v, uⱼ⟫| ≤ ‖v‖ · ‖Pₙ − Pinf‖ · ‖uⱼ‖`. With the tempered
tilt `‖Pₙ − Pinf‖ ≤ exp(n(L+ε))`, the overlap squared is `⟪v, uⱼ⟫² ≤ ‖v‖²‖uⱼ‖² · exp(2n(L+ε))`:
the slow–fast overlap leaks at the strictly negative tempered rate `L`. -/

open Oseledets in
/-- **Slow–fast overlap exp-envelope.** For slow `v` and a step-`n` fast eigenvector `uⱼ(n)` of the
band (self-adjoint `Pₙ`, `Pₙ uⱼ = uⱼ`), with `‖uⱼ(n)‖ ≤ U` bounded, and the tempered tilt
`‖Pₙ − Pinf‖ ≤ exp(n(L+ε/2))`, the squared overlap obeys
`⟪v, uⱼ(n)⟫² ≤ (‖v‖·U)² · exp(2n(L+ε/2))`, eventually. The negative overlap rate is obtained
with no slow-growth assumption on `v`. -/
theorem eventually_inner_sq_le_exp_of_tilt
    {d : ℕ} [NeZero d]
    {Pn : ℕ → Matrix (Fin d) (Fin d) ℝ} {Pinf : Matrix (Fin d) (Fin d) ℝ}
    {v : EuclideanSpace ℝ (Fin d)} {uj : ℕ → EuclideanSpace ℝ (Fin d)} {U L ε : ℝ}
    (hPnsa : ∀ᶠ n in atTop, (Pn n)ᵀ = Pn n) (hPinfsa : Pinfᵀ = Pinf)
    (hslow : Matrix.toEuclideanLin Pinf v = 0)
    (hfast : ∀ᶠ n in atTop, Matrix.toEuclideanLin (Pn n) (uj n) = uj n)
    (hUbd : ∀ᶠ n in atTop, ‖uj n‖ ≤ U)
    (htilt : ∀ᶠ n in atTop, ‖Pn n - Pinf‖ ≤ Real.exp ((n : ℝ) * (L + ε))) :
    ∀ᶠ n : ℕ in atTop,
      (inner ℝ v (uj n) : ℝ) ^ 2 ≤ (‖v‖ * U) ^ 2 * Real.exp ((n : ℝ) * (2 * (L + ε))) := by
  filter_upwards [hPnsa, hfast, hUbd, htilt] with n hsa hf hU htn
  -- handle + Cauchy–Schwarz: |⟪v, uⱼ⟫| ≤ ‖v‖ · ‖(Pₙ − Pinf) uⱼ‖.
  have hhandle : |(inner ℝ v (uj n) : ℝ)| ≤ ‖v‖ * ‖Matrix.toEuclideanLin (Pn n - Pinf) (uj n)‖ :=
    Oseledets.abs_inner_le_norm_mul_bandProjector_tilt hsa hPinfsa hslow hf
  -- ‖(Pₙ − Pinf) uⱼ‖ ≤ ‖Pₙ − Pinf‖ · ‖uⱼ‖.
  have hopbd : ‖Matrix.toEuclideanLin (Pn n - Pinf) (uj n)‖ ≤ ‖Pn n - Pinf‖ * ‖uj n‖ := by
    have hle := (Matrix.toEuclideanCLM (𝕜 := ℝ) (Pn n - Pinf)).le_opNorm (uj n)
    have heq : (Matrix.toEuclideanCLM (𝕜 := ℝ) (Pn n - Pinf)) (uj n)
        = Matrix.toEuclideanLin (Pn n - Pinf) (uj n) := by
      rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]; rfl
    rw [heq] at hle
    have hnormeq : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Pn n - Pinf)‖ = ‖Pn n - Pinf‖ := rfl
    rwa [hnormeq] at hle
  have hUnn : 0 ≤ U := le_trans (norm_nonneg _) hU
  have hvnn : 0 ≤ ‖v‖ := norm_nonneg _
  -- combine: |⟪v, uⱼ⟫| ≤ ‖v‖ · ‖Pₙ − Pinf‖ · ‖uⱼ‖ ≤ ‖v‖ · U · exp(n(L+ε)).
  have hchain : |(inner ℝ v (uj n) : ℝ)| ≤ ‖v‖ * U * Real.exp ((n : ℝ) * (L + ε)) := by
    calc |(inner ℝ v (uj n) : ℝ)|
        ≤ ‖v‖ * ‖Matrix.toEuclideanLin (Pn n - Pinf) (uj n)‖ := hhandle
      _ ≤ ‖v‖ * (‖Pn n - Pinf‖ * ‖uj n‖) := by
          apply mul_le_mul_of_nonneg_left hopbd hvnn
      _ ≤ ‖v‖ * (Real.exp ((n : ℝ) * (L + ε)) * U) := by
          apply mul_le_mul_of_nonneg_left _ hvnn
          exact mul_le_mul htn hU (norm_nonneg _) (Real.exp_nonneg _)
      _ = ‖v‖ * U * Real.exp ((n : ℝ) * (L + ε)) := by ring
  -- square both sides.
  have habs_sq : (inner ℝ v (uj n) : ℝ) ^ 2 = |(inner ℝ v (uj n) : ℝ)| ^ 2 := (sq_abs _).symm
  rw [habs_sq]
  have hrhs_nn : 0 ≤ ‖v‖ * U * Real.exp ((n : ℝ) * (L + ε)) := by positivity
  calc |(inner ℝ v (uj n) : ℝ)| ^ 2
      ≤ (‖v‖ * U * Real.exp ((n : ℝ) * (L + ε))) ^ 2 := by
        apply pow_le_pow_left₀ (abs_nonneg _) hchain
    _ = (‖v‖ * U) ^ 2 * Real.exp ((n : ℝ) * (2 * (L + ε))) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        rw [show ((2 : ℕ) : ℝ) * ((n : ℝ) * (L + ε)) = (n : ℝ) * (2 * (L + ε)) by push_cast; ring]

/-! ## 5. The per-index spectral envelope `henv j` for a fast index (zero-safe, no logs of zero)

Multiply the tempered overlap exp-envelope (step 4) by the singular-value exp-envelope
(`Oseledets.eventually_sq_singularValue_le_exp`) to obtain the per-index `specTerm` envelope
`specTermⱼ(n) = σⱼ(n)²·⟪v,uⱼ(n)⟫² ≤ exp(n(2λᵢ+ε))` directly. This is the `henv j` hypothesis of
`Oseledets.limsup_inv_mul_log_norm_cocycle_apply_le`. Working with exp-envelopes throughout is
zero-safe: when `⟪v,uⱼ⟫ = 0`, `specTermⱼ = 0 ≤ exp(...)` holds trivially (no `log 0` arises).

The rate condition is `λⱼ + L ≤ λᵢ`, where `L` is the tempered (straddling-gap) overlap rate
for the band projector at the cut. At the nearest fast index this holds with equality
(`λⱼ = λ_{k-1}`, `L = λ_k − λ_{k-1}`, `λⱼ + L = λ_k ≤ λᵢ`); see the multi-gap discussion in the
module docstring. -/

open Oseledets in
/-- **Per-index spectral envelope from the tempered overlap (fast index).** Given the singular
exponent limit `(1/n) log σⱼ(n) → λⱼ` with `σⱼ(n) > 0`, and the tempered overlap exp-envelope
`⟪v,uⱼ(n)⟫² ≤ C·exp(2n(L+ε'))` for every `ε' > 0` (the output of step 4 with
`uⱼ = sortedGramEigenbasis`, `C = (‖v‖·U)²`), and the rate balance `λⱼ + L ≤ λᵢ`, the per-index
`specTerm` envelope holds: for every `ε > 0`, eventually `specTermⱼ(n) ≤ exp(n(2λᵢ+ε))`. This is
exactly `henv j` of `limsup_inv_mul_log_norm_cocycle_apply_le`. Zero-safe. -/
theorem specTerm_envelope_of_tempered_overlap
    {X : Type*} [MeasurableSpace X] {d : ℕ} [NeZero d] {T : X → X}
    {A : X → Matrix (Fin d) (Fin d) ℝ} {x : X} {v : EuclideanSpace ℝ (Fin d)}
    {lami lamj L C : ℝ} (j : Fin (Fintype.card (Fin d)))
    (hσpos : ∀ n : ℕ, 1 ≤ n → 0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues j)
    (hσ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues j)) atTop (𝓝 lamj))
    (hCnn : 0 ≤ C)
    (hov : ∀ ε' > 0, ∀ᶠ n : ℕ in atTop,
      (inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2
        ≤ C * Real.exp ((n : ℝ) * (2 * (L + ε'))))
    (hrate : lamj + L ≤ lami) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      specTerm T A n x v j ≤ Real.exp ((n : ℝ) * (2 * lami + ε)) := by
  intro ε hε
  -- pick a small `δ`; split `ε` between the singular and overlap factors and the constant `C`.
  -- singular factor: σⱼ² ≤ exp(n(2λⱼ + ε/4)).
  have hσenv := Oseledets.eventually_sq_singularValue_le_exp (T := T) j hσpos hσ (ε/4) (by linarith)
  -- overlap factor: ⟪v,uⱼ⟫² ≤ C·exp(2n(L + ε/8)).
  have hovenv := hov (ε/8) (by linarith)
  -- constant `C` is eventually dominated by exp(n·ε/8).
  have hCdom : ∀ᶠ n : ℕ in atTop, C ≤ Real.exp ((n : ℝ) * (ε/8)) := by
    rcases eq_or_lt_of_le hCnn with hC0 | hCpos
    · filter_upwards with n; rw [← hC0]; exact Real.exp_nonneg _
    · have hgrow : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (ε/8))) atTop atTop := by
        apply Real.tendsto_exp_atTop.comp
        exact Filter.Tendsto.atTop_mul_const (by linarith) tendsto_natCast_atTop_atTop
      exact hgrow.eventually_ge_atTop C
  filter_upwards [hσenv, hovenv, hCdom] with n hσn hovn hCn
  rw [specTerm]
  -- multiply: σⱼ²·⟪v,uⱼ⟫² ≤ exp(n(2λⱼ+ε/4)) · C·exp(2n(L+ε/8)).
  have hnn1 : (0 : ℝ) ≤ (Matrix.toEuclideanLin (cocycle A T n x)).singularValues j ^ 2 := by
    positivity
  have hnn2 : (0 : ℝ) ≤ (inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2 := by positivity
  have hCexp : C * Real.exp ((n : ℝ) * (2 * (L + ε/8)))
      ≤ Real.exp ((n : ℝ) * (ε/8)) * Real.exp ((n : ℝ) * (2 * (L + ε/8))) :=
    mul_le_mul_of_nonneg_right hCn (Real.exp_nonneg _)
  calc (Matrix.toEuclideanLin (cocycle A T n x)).singularValues j ^ 2
          * (inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2
      ≤ Real.exp ((n : ℝ) * (2 * lamj + ε/4)) * (C * Real.exp ((n : ℝ) * (2 * (L + ε/8)))) :=
        mul_le_mul hσn hovn hnn2 (Real.exp_nonneg _)
    _ ≤ Real.exp ((n : ℝ) * (2 * lamj + ε/4))
          * (Real.exp ((n : ℝ) * (ε/8)) * Real.exp ((n : ℝ) * (2 * (L + ε/8)))) :=
        mul_le_mul_of_nonneg_left hCexp (Real.exp_nonneg _)
    _ = Real.exp ((n : ℝ) * (2 * lamj + ε/4) + ((n : ℝ) * (ε/8) + (n : ℝ) * (2 * (L + ε/8)))) := by
        rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp ((n : ℝ) * (2 * lami + ε)) := by
        apply Real.exp_le_exp.mpr
        have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
        nlinarith [hrate, hnn]

/-! ## 6. The spectral upper bound for a Λ-slow vector

Assembling the per-index envelopes into the per-vector growth upper bound, via
`Oseledets.limsup_inv_mul_log_norm_cocycle_apply_le`. The per-index inputs are exactly
`specTerm_envelope_of_tempered_overlap` for each spectral index `j`: each carries its own
tempered overlap rate `Lⱼ ≤ 0` (from the tempered angle of the band projector at the
appropriate cut) and the rate balance `λⱼ + Lⱼ ≤ λᵢ`. The conclusion is the spectral upper
bound

    limsup_n (1/n)·log ‖A⁽ⁿ⁾ v‖  ≤  λᵢ,

with no assumption of slow growth (`lambdaBar v ≤ λᵢ`) — the overlap rates come from
convergence plus a spectral gap (tempering), not from an assumed growth rate. -/

open Oseledets in
/-- **Spectral upper bound for a Λ-slow vector.** Given, for every spectral index `j`, the
per-index tempered `specTerm` envelope `henv j` (the output of
`specTerm_envelope_of_tempered_overlap`), plus eventual positivity of `‖A⁽ⁿ⁾ v‖` and the
cobounded side-condition, the per-vector growth `limsup` is bounded by `λᵢ`; the per-index
envelopes are supplied by the tempered angle, with no slow-growth assumption. -/
theorem limsup_log_norm_cocycle_apply_le_of_tempered_envelopes
    {X : Type*} [MeasurableSpace X] {d : ℕ} [NeZero d] {T : X → X}
    (A : X → Matrix (Fin d) (Fin d) ℝ) (x : X) (v : EuclideanSpace ℝ (Fin d)) (lami : ℝ)
    (henv : ∀ j : Fin (Fintype.card (Fin d)), ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop, specTerm T A n x v j ≤ Real.exp ((n : ℝ) * (2 * lami + ε)))
    (hpos : ∀ᶠ n : ℕ in atTop, 0 < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)
    (hcobdd : IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ lami :=
  Oseledets.limsup_inv_mul_log_norm_cocycle_apply_le (T := T) A x v lami henv hpos hcobdd

/-! ## 7. The per-index closure: from convergence plus gap to `henv j`

This single lemma chains steps 3 → 4 → 5: it takes as input, at a point `x`, the band-projector
convergence, the tempered per-step increment bound, the singular-value limit, the fast-band
membership of `uⱼ = sortedGramEigenbasis`, and the rate balance, and produces the per-index
`specTerm` envelope `henv j`. No slow-growth assumption on `v` is used — the overlap rate is
the tempered angle, supplied by convergence plus a spectral gap. -/

open Oseledets in
/-- **Per-index closure (tempering chain).** For a Λ-slow `v` (`toEuclideanLin Pinf v = 0`) at a
point `x` where the band projector at cut `c` converges to `Pinf` with tempered increments
(`hbnn`/`hbpos`/`hL`/`hlog`/`hstep`), and where `uⱼ(n) = sortedGramEigenbasis A T n x j` is a
unit step-`n` fast eigenvector (`hunit`/`hfast`), with singular limit `(1/n) log σⱼ(n) → λⱼ`
(`hσpos`/`hσ`) and the rate balance `λⱼ + L ≤ λᵢ`, the per-index `specTerm` envelope `henv j`
holds. No slow-growth assumption on `v` is required. -/
theorem specTerm_envelope_henv_of_convergence
    {X : Type*} [MeasurableSpace X] {d : ℕ} [NeZero d] {T : X → X}
    (A : X → Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (x : X) (j : Fin (Fintype.card (Fin d)))
    {v : EuclideanSpace ℝ (Fin d)} {Pinf : Matrix (Fin d) (Fin d) ℝ}
    {b : ℕ → ℝ} {L lami lamj : ℝ}
    (hP : Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) atTop (𝓝 Pinf))
    (hbnn : ∀ n, 0 ≤ b n) (hbpos : ∀ᶠ n in atTop, 0 < b n) (hL : L < 0)
    (hlog : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (b n)) atTop (𝓝 L))
    (hstep : ∀ᶠ n in atTop,
      ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
          - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖ ≤ b n)
    (hPinfsa : Pinfᵀ = Pinf)
    (hslow : Matrix.toEuclideanLin Pinf v = 0)
    (hbandsa : ∀ᶠ n in atTop,
      (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)ᵀ
        = bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)
    (hfast : ∀ᶠ n in atTop,
      Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)
          (sortedGramEigenbasis A T n x j)
        = sortedGramEigenbasis A T n x j)
    (hunit : ∀ᶠ n in atTop, ‖sortedGramEigenbasis A T n x j‖ ≤ 1)
    (hσpos : ∀ n : ℕ, 1 ≤ n → 0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues j)
    (hσ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues j)) atTop (𝓝 lamj))
    (hrate : lamj + L ≤ lami) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      specTerm T A n x v j ≤ Real.exp ((n : ℝ) * (2 * lami + ε)) := by
  -- overlap exp-envelope for every `ε' > 0` (steps 3 + 4 with `U = 1`):
  have hov : ∀ ε' > 0, ∀ᶠ n : ℕ in atTop,
      (inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2
        ≤ (‖v‖ * 1) ^ 2 * Real.exp ((n : ℝ) * (2 * (L + ε'))) := by
    intro ε' hε'
    -- step 3: tempered band-projector tilt `‖Pₙ − Pinf‖ ≤ exp(n(L+ε'))`.
    have htilt :=
      eventually_norm_bandProjector_sub_le_exp A T c x hP hbnn hbpos hL hlog hstep ε' hε'
    -- step 4: overlap squared envelope (with `Pn n = bandProjector …`).
    exact eventually_inner_sq_le_exp_of_tilt
      (Pn := fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) (Pinf := Pinf)
      (v := v) (uj := fun n => sortedGramEigenbasis A T n x j) (U := 1)
      hbandsa hPinfsa hslow hfast hunit htilt
  -- step 5: per-index `specTerm` envelope, with `C = (‖v‖ * 1)²`.
  exact specTerm_envelope_of_tempered_overlap (T := T) (A := A) (x := x) (v := v) j
    hσpos hσ (by positivity) hov hrate

end Oseledets.Tempering
