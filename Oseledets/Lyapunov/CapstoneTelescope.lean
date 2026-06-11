/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.ForwardOverlap
import Oseledets.Lyapunov.ForwardTempering
import Oseledets.Lyapunov.ForwardV

/-!
# Per-vector growth bounds from telescoped overlap rates

For the matrix cocycle `A⁽ⁿ⁾ = cocycle A T n x` of a map `T : X → X`, this file assembles the
per-vector spectral upper bound

`limsup (1/n) · log ‖A⁽ⁿ⁾ v‖ ≤ λᵢ`

from per-spectral-index data: the singular-value limits `(1/n) · log σⱼ(n) → λⱼ`, an
overlap-rate bound `limsup (1/n) · log |⟪v, uⱼ(n)⟫| ≤ rⱼ` against the sorted Gram eigenbasis
`uⱼ(n)` (the conclusion of the multiplicative telescope
`Oseledets.telescope_overlap_limsup_le`), and the rate balance `λⱼ + rⱼ ≤ λᵢ`.  This is the
shape consumed for a vector `v` in the slow space `Vslow A T (Real.exp t) x` with `λᵢ = t`.

The file also records a quantitative obstruction explaining why the overlap rates must be
telescoped through every adjacent spectral gap.  A single-cut estimate routes the overlap
against every fast direction through the operator norm `‖Pₙ − P∞‖` of a band-projector
difference at one cut `c = exp λᵢ`; the available decay rate is then the nearest gap
`L = λ_near − λᵢ` straddling the cut, and the balance `λⱼ + L ≤ λᵢ` fails for every band
strictly above the nearest fast one (`single_cut_rate_balance_fails`).  Composing single-cut
tilt estimates at every adjacent gap between the band of `j` and the slow space yields the
pairwise rate `λᵢ − λⱼ` instead, which does satisfy the balance.

## Main results

* `single_cut_rate_balance_fails`, `single_cut_envelope_exponent_exceeds_target`: the
  obstruction lemmas — for `λᵢ < λ_near < λⱼ` and `L = λ_near − λᵢ`, the single-cut rate
  balance `λⱼ + L ≤ λᵢ` is strictly violated.
* `limsup_log_sq_le_two_mul`: the bridge from the absolute-value overlap rate to the squared
  form, `limsup (1/n) · log (aₙ²) ≤ 2L` from `limsup (1/n) · log |aₙ| ≤ L`.
* `capstone_upper_of_overlap_rates`: the per-vector upper bound from squared overlap rates,
  via `Oseledets.specTerm_envelope_of_rate` and
  `Oseledets.limsup_inv_mul_log_norm_cocycle_apply_le`.
* `capstone_upper_of_telescope_outputs`: the end-to-end form, consuming the absolute-value
  overlap rates produced by `Oseledets.telescope_overlap_limsup_le`.

## References

* D. Ruelle, *Ergodic theory of differentiable dynamical systems*,
  Publ. Math. IHÉS **50** (1979), 27–58.
-/

open MeasureTheory Filter Topology
open scoped Matrix InnerProductSpace

namespace Oseledets.CapstoneTelescope

/-! ## The single-cut obstruction

A single-cut tempering estimate produces the per-index rate balance `λⱼ + L ≤ λᵢ`, where
`L = λ_near − λᵢ` is the band-projector tilt rate at the cut `c = exp λᵢ` (the nearest gap
straddling the cut: `λ_near` is the smallest fast exponent, strictly above `λᵢ`).  For any
band `j` strictly above the nearest fast band (`λⱼ > λ_near`) the balance is violated.  The
two lemmas below make this quantitative. -/

/-- **The single-cut rate balance fails above the nearest fast band.**  With `L = λ_near − λᵢ`
the nearest straddling-gap tilt rate (`λᵢ < λ_near`), and a fast band `j` strictly above the
nearest one (`λ_near < λⱼ`), the per-index balance `λⱼ + L ≤ λᵢ` required by
`specTerm_envelope_of_tempered_overlap` is violated: `λⱼ + L > λᵢ`.  Hence a single-cut
estimate through the operator-norm tilt rate (`eventually_inner_sq_le_exp_of_tilt`) cannot
close the bands above the nearest gap. -/
theorem single_cut_rate_balance_fails {lami lamNear lamj : ℝ}
    (hcut : lami < lamNear) (habove : lamNear < lamj) :
    lami < lamj + (lamNear - lami) := by
  -- λⱼ + (λ_near − λᵢ) > λ_near + (λ_near − λᵢ) > λ_near > λᵢ ⇒ in particular > λᵢ.
  nlinarith [hcut, habove]

/-- **The single-cut envelope rate strictly exceeds the target.**  The exponent a single-cut
estimate can certify for `specTermⱼ` is `2·(λⱼ + L)` with `L = λ_near − λᵢ`; for `j` above the
nearest fast band this strictly exceeds the target exponent `2·λᵢ`.  So no `ε`-envelope at the
target rate is available from a single cut — the obstruction is strict, not borderline. -/
theorem single_cut_envelope_exponent_exceeds_target {lami lamNear lamj : ℝ}
    (hcut : lami < lamNear) (habove : lamNear < lamj) :
    2 * lami < 2 * (lamj + (lamNear - lami)) := by
  nlinarith [hcut, habove]

/-! ## The per-vector upper bound from per-index overlap rates

The limsup conclusion `limsup (1/n) log ‖A⁽ⁿ⁾ v‖ ≤ λᵢ` is assembled at a point `x` and
vector `v` from the following data, per spectral index `j`:

* `hσpos j`, `hσ j` — the singular-value limit `(1/n) log σⱼ(n) → λⱼ`;
* `hbal j` — the per-index **pairwise** rate balance `λⱼ + rⱼ ≤ λᵢ`, with `rⱼ` the overlap
  rate;
* `hov_rate j` — the per-index overlap-rate bound `limsup (1/n) log ⟪v,uⱼ(n)⟫² ≤ 2 rⱼ` (the
  output of the telescope `telescope_overlap_limsup_le`);
* `hovbdd j` — the overlap-log boundedness side condition.

The assembly goes through `specTerm_envelope_of_rate` and
`limsup_inv_mul_log_norm_cocycle_apply_le`. -/

open Oseledets in
/-- **The per-vector upper bound from per-index pairwise overlap rates.**  Given, for each
spectral index `j`, the singular-value limit, the pairwise rate balance `λⱼ + rⱼ ≤ λᵢ`, the
overlap-rate bound (`limsup (1/n) log ⟪v,uⱼ⟫² ≤ 2 rⱼ`, the telescope output) and its
boundedness, plus eventual positivity and coboundedness of `‖A⁽ⁿ⁾ v‖`, the per-vector growth
`limsup` is `≤ λᵢ`.  This is the exact shape consumed for a slow vector with top exponent
`λᵢ = t`. -/
theorem capstone_upper_of_overlap_rates
    {X : Type*} [MeasurableSpace X] {d : ℕ} [NeZero d] {T : X → X}
    (A : X → Matrix (Fin d) (Fin d) ℝ) (x : X) (v : EuclideanSpace ℝ (Fin d)) (lami : ℝ)
    (lamj rj : Fin (Fintype.card (Fin d)) → ℝ)
    (hσpos : ∀ j : Fin (Fintype.card (Fin d)), ∀ n : ℕ, 1 ≤ n →
      0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues j)
    (hσ : ∀ j : Fin (Fintype.card (Fin d)), Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues j)) atTop (𝓝 (lamj j)))
    (hovbdd : ∀ j : Fin (Fintype.card (Fin d)), IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2)))
    (hov_rate : ∀ j : Fin (Fintype.card (Fin d)), limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2)) atTop ≤ 2 * rj j)
    (hbal : ∀ j : Fin (Fintype.card (Fin d)), lamj j + rj j ≤ lami)
    (hpos : ∀ᶠ n : ℕ in atTop, 0 < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)
    (hcobdd : IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ lami := by
  -- the per-index `specTerm` envelope, from `specTerm_envelope_of_rate`:
  have henv : ∀ j : Fin (Fintype.card (Fin d)), ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop, specTerm T A n x v j ≤ Real.exp ((n : ℝ) * (2 * lami + ε)) := by
    intro j
    exact Oseledets.specTerm_envelope_of_rate (T := T) (A := A) (x := x) (v := v) j
      (hσpos j) (hσ j) (hovbdd j) (hov_rate j) (hbal j)
  -- assemble via the conditional upper bound:
  exact Oseledets.limsup_inv_mul_log_norm_cocycle_apply_le (T := T) A x v lami henv hpos hcobdd

/-! ## The squared overlap rate from the absolute-value form

`telescope_overlap_limsup_le` concludes `limsup (1/n) log |⟪v,uⱼ(n)⟫| ≤ rate`, while
`capstone_upper_of_overlap_rates` consumes the squared form
`limsup (1/n) log ⟪v,uⱼ(n)⟫² ≤ 2·rate`.  The bridge is `log (a²) = 2 log |a|`, proved in the
`≤` direction for `limsup`s below. -/

/-- **Squared-overlap limsup `≤ 2 ×` abs-overlap limsup.**  For `a : ℕ → ℝ` eventually
nonzero, with the squared-log sequence cobounded above and the abs-log sequence bounded
above, `limsup (1/n) log (a n ^ 2) ≤ 2 · L` whenever `limsup (1/n) log |a n| ≤ L`.  Via
`log (a²) = 2 log|a|` pointwise and the `<`-form `limsup_le_iff` (avoiding the absent real
`limsup_const_mul`). -/
theorem limsup_log_sq_le_two_mul {a : ℕ → ℝ} {L : ℝ} (ha : ∀ᶠ n in atTop, a n ≠ 0)
    (hcob : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (a n ^ 2)))
    (hbdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ * Real.log |a n|))
    (hL : limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log |a n|) atTop ≤ L) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (a n ^ 2)) atTop ≤ 2 * L := by
  set f : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * Real.log |a n| with hfdef
  set g : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * Real.log (a n ^ 2) with hgdef
  set h2 : ℕ → ℝ := fun n => 2 * f n with hh2def
  -- pointwise (eventually): g n = 2 · f n.
  have hcongr : g =ᶠ[atTop] h2 := by
    filter_upwards [ha] with n hn
    have hlog : Real.log (a n ^ 2) = 2 * Real.log |a n| := by
      rw [show a n ^ 2 = |a n| ^ 2 by rw [sq_abs], Real.log_pow]; push_cast; ring
    change (n : ℝ)⁻¹ * Real.log (a n ^ 2) = 2 * ((n : ℝ)⁻¹ * Real.log |a n|)
    rw [hlog]; ring
  -- transport coboundedness of `g` across the eventual equality to `h2`.
  have hcob2 : IsCoboundedUnder (· ≤ ·) atTop h2 := by
    obtain ⟨c, hc⟩ := hcob
    refine ⟨c, fun w hw => hc w ?_⟩
    have : ∀ᶠ k in atTop, g k ≤ w := by
      filter_upwards [(hw : ∀ᶠ k in atTop, h2 k ≤ w), hcongr] with k hk heq
      rw [heq]; exact hk
    exact this
  -- bounded above: from `f` bounded above by `B`, `2 f` bounded above by `2B`.
  have hbdd2 : IsBoundedUnder (· ≤ ·) atTop h2 := by
    obtain ⟨B, hB⟩ := hbdd
    refine ⟨2 * B, ?_⟩
    rw [Filter.eventually_map] at hB ⊢
    filter_upwards [hB] with n hn
    exact mul_le_mul_of_nonneg_left hn (by norm_num)
  rw [limsup_congr hcongr, limsup_le_iff hcob2 hbdd2]
  intro y hy
  -- y > 2L ⇒ y/2 > L ⇒ eventually f < y/2 ⇒ eventually 2 f < y.
  have hyL : L < y / 2 := by linarith
  have hflt : limsup f atTop < y / 2 := lt_of_le_of_lt hL hyL
  have hev := eventually_lt_of_limsup_lt hflt hbdd
  filter_upwards [hev] with n hn
  change h2 n < y
  change 2 * f n < y
  linarith [hn]

open Oseledets in
/-- **The squared overlap rate from the telescope output.**  If the abs-overlap limsup is
`≤ rⱼ` (the conclusion of `telescope_overlap_limsup_le` with `rate = rⱼ`), the overlap is
eventually nonzero, and the boundedness side conditions hold, then the squared-overlap limsup
is `≤ 2 rⱼ` — exactly the `hov_rate` hypothesis of `capstone_upper_of_overlap_rates`. -/
theorem hov_rate_of_telescope_output
    {X : Type*} [MeasurableSpace X] {d : ℕ} [NeZero d] {T : X → X}
    {A : X → Matrix (Fin d) (Fin d) ℝ} {x : X} {v : EuclideanSpace ℝ (Fin d)}
    (j : Fin (Fintype.card (Fin d))) {rj : ℝ}
    (hnz : ∀ᶠ n in atTop, (inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ≠ 0)
    (hcob : IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2)))
    (hbdd : IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log |(inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ)|))
    (htele : limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log |(inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ)|) atTop ≤ rj) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2)) atTop ≤ 2 * rj :=
  limsup_log_sq_le_two_mul hnz hcob hbdd htele

/-! ## The end-to-end composition

Composing `hov_rate_of_telescope_output` into `capstone_upper_of_overlap_rates`: given, per
spectral index `j`, the singular-value limit and the abs-overlap limsup bound
`limsup (1/n) log |⟪v,uⱼ⟫| ≤ rⱼ` (the conclusion of `Oseledets.telescope_overlap_limsup_le`),
plus the rate balance `λⱼ + rⱼ ≤ λᵢ` and the routine side conditions, the per-vector upper
bound `limsup (1/n) log ‖A⁽ⁿ⁾ v‖ ≤ λᵢ` follows. -/

open Oseledets in
/-- **The per-vector upper bound from per-index telescope outputs.**  Feeds the per-index
abs-overlap limsup `htele j` (the output of `telescope_overlap_limsup_le`) through
`hov_rate_of_telescope_output` to obtain the squared form, then through
`capstone_upper_of_overlap_rates` to the per-vector upper bound. -/
theorem capstone_upper_of_telescope_outputs
    {X : Type*} [MeasurableSpace X] {d : ℕ} [NeZero d] {T : X → X}
    (A : X → Matrix (Fin d) (Fin d) ℝ) (x : X) (v : EuclideanSpace ℝ (Fin d)) (lami : ℝ)
    (lamj rj : Fin (Fintype.card (Fin d)) → ℝ)
    (hσpos : ∀ j : Fin (Fintype.card (Fin d)), ∀ n : ℕ, 1 ≤ n →
      0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues j)
    (hσ : ∀ j : Fin (Fintype.card (Fin d)), Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues j)) atTop (𝓝 (lamj j)))
    (hnz : ∀ j : Fin (Fintype.card (Fin d)), ∀ᶠ n in atTop,
      (inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ≠ 0)
    (hcobSq : ∀ j : Fin (Fintype.card (Fin d)), IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2)))
    (hbddSq : ∀ j : Fin (Fintype.card (Fin d)), IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2)))
    (hbddAbs : ∀ j : Fin (Fintype.card (Fin d)), IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log |(inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ)|))
    (htele : ∀ j : Fin (Fintype.card (Fin d)), limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log |(inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ)|) atTop ≤ rj j)
    (hbal : ∀ j : Fin (Fintype.card (Fin d)), lamj j + rj j ≤ lami)
    (hpos : ∀ᶠ n : ℕ in atTop, 0 < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)
    (hcobdd : IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ lami := by
  -- the per-index squared-overlap rate from the telescope output `htele j`:
  have hov_rate : ∀ j : Fin (Fintype.card (Fin d)), limsup (fun n : ℕ => (n : ℝ)⁻¹ *
      Real.log ((inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2)) atTop ≤ 2 * rj j :=
    fun j => hov_rate_of_telescope_output j (hnz j) (hcobSq j) (hbddAbs j) (htele j)
  -- assemble from the per-index squared-overlap rates:
  exact capstone_upper_of_overlap_rates A x v lami lamj rj
    hσpos hσ hbddSq hov_rate hbal hpos hcobdd

end Oseledets.CapstoneTelescope
