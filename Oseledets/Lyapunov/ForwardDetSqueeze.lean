/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.ForwardUpperBound
import Oseledets.Ergodic.Birkhoff

/-!
# The spectral upper bound via the determinant squeeze and the tempered angle

This file proves the **spectral upper bound** of the Oseledets multiplicative ergodic theorem
for a `Λ`-slow vector `v`,

    limsup_n (1/n)·log ‖A⁽ⁿ⁾ v‖  ≤  λᵢ,    for `v` in the limit slow subspace `S(x)`.

The mechanism is the **determinant squeeze with a tempered angle** (Raghunathan; Arnold §3.4;
Filip). Its decisive feature is non-circularity: the slow growth is determined *globally* via
the volume cocycle, never per vector. A per-vector recursion between the growth exponent and
the fast/slow overlap would be circular; the squeeze instead consumes only *convergence* facts
(the Furstenberg–Kesten determinant limit, the fast-volume Kingman limit, and the tempered-angle
limit), none of which refers to the growth of an individual vector.

Two self-contained ingredients are built here:

1. **The tempering lemma** (`tempering_lemma`, a Birkhoff corollary): for `g ≥ 0` with
   `log⁺ g ∈ L¹(μ)`, `(1/n)·log⁺(g ∘ Tⁿ) → 0` a.e. Only convergence/finiteness is used,
   not a rate.

2. **The determinant / Gram factorization** (`det_gram_image_eq`, `det_sq_eq_gram_image`,
   finite-dimensional linear algebra): for a splitting `ℝ^d = F ⊕ S` with orthonormal frames
   `ω_F` (`p` columns) and `ω_S` (`q` columns) assembled into the block frame `W = [ω_F ω_S]`,
   the Gram determinant of the image block factors as
   `det((M·W)ᵀ·(M·W)) = (det M)² · (det W)²`, which underlies the geometric identity
   `|det(M·W)| = vol_F · vol_S · sin∠(M F, M S)`.

## Main results

* `Oseledets.tempering_lemma`, `Oseledets.tempering_posLog`: for an integrable `h` (think
  `h = log⁺ g`), `(1/n)·h(Tⁿ x) → 0` for almost every `x`.
* `Oseledets.det_gram_image_eq`, `Oseledets.det_sq_eq_gram_image`: the determinant/Gram
  factorization for a block frame.
* `Oseledets.tendsto_slowVolume_exponent`: the squeeze arithmetic — convergence of the
  slow-volume exponent from the determinant, fast-volume, and angle limits.
* `Oseledets.limsup_le_of_sum_tendsto`, `Oseledets.limsup_topSlow_le_of_squeeze`: the
  exponent-pinning squeeze forcing the top slow exponent down to `λᵢ`.
* `Oseledets.spectral_upper_bound_of_squeeze`: the per-vector spectral upper bound
  `limsup (1/n)·log ‖A⁽ⁿ⁾ v‖ ≤ λᵢ` for `v` in the slow subspace.

## References

* M. S. Raghunathan, *A proof of Oseledec's multiplicative ergodic theorem*,
  Israel J. Math. **32** (1979), 356–362.
* L. Arnold, *Random Dynamical Systems*, Springer Monographs in Mathematics, 1998.
* S. Filip, *Notes on the multiplicative ergodic theorem*,
  Ergodic Theory Dynam. Systems **39** (2019), 1153–1189.
-/

open MeasureTheory Filter Topology
open scoped Matrix InnerProductSpace Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {T : X → X} {d : ℕ}

/-! ## The tempering lemma (a Birkhoff corollary)

If `g ≥ 0` and `log⁺ g ∈ L¹(μ)`, then `(1/n) log⁺(g(Tⁿx)) → 0` for a.e. `x`. This follows by
applying the orbit-decay theorem `ae_tendsto_orbit_div_atTop_zero` to the integrable function
`x ↦ log⁺ g(x) = Real.posLog (g x)`. The decisive feature: only *integrability* (finiteness) of
`log⁺ g` is used — no decay rate. -/

/-- **Tempering lemma.** For an integrable `h` (think `h = log⁺ g`, the positive log of a tempered
quantity), `(1/n)·h(Tⁿx) → 0` for `μ`-a.e. `x`. A thin specialization of
`ae_tendsto_orbit_div_atTop_zero`, packaged as the tempering corollary. -/
theorem tempering_lemma {μ : Measure X} (hT : MeasurePreserving T μ μ) {h : X → ℝ}
    (hh : Integrable h μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * h (T^[n] x)) atTop (𝓝 0) :=
  ae_tendsto_orbit_div_atTop_zero hT hh

/-- **Tempering lemma (posLog form).** If `x ↦ Real.posLog (g x)` is integrable (the tempered
condition `log⁺ g ∈ L¹`), then `(1/n)·log⁺(g(Tⁿx)) → 0` a.e. This is the form used by the squeeze:
`g = 1/sin∠(F,S)` (genuine splitting, tempered) gives `(1/n)·log sin∠(F(Tⁿx),S(Tⁿx)) → 0`. -/
theorem tempering_posLog {μ : Measure X} (hT : MeasurePreserving T μ μ) {g : X → ℝ}
    (hg : Integrable (fun x => Real.posLog (g x)) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.posLog (g (T^[n] x))) atTop (𝓝 0) :=
  ae_tendsto_orbit_div_atTop_zero hT hg

/-! ## The determinant / angle factorization (finite-dimensional linear algebra)

For a square real matrix `W : Matrix (Fin d) (Fin d) ℝ` viewed as a block frame `W = [ω_F | ω_S]`
(`ω_F` the first `p` columns, `ω_S` the last `q = d − p`), and any `M : Matrix (Fin d) (Fin d) ℝ`,
the **Gram determinant of the image block** factors:

    det((M·W)ᵀ·(M·W)) = (det M)² · (det W)²,

and equals `det(Gram(M ω_F)) · det(Gram(M ω_S)) · sin²∠(M F, M S)` where the inter-block sine is
*defined* by `sin² := det(Gram(M·W)) / (det(Gram(M ω_F)) · det(Gram(M ω_S)))`. The genuine
geometric content is **Fischer's inequality** `sin² ≤ 1`, i.e. the Gram determinant of a block
matrix is at most the product of the diagonal-block Gram determinants. We package the unconditional
algebraic identity here; the squeeze uses `0 < sin² ≤ 1` (genuine splitting + Fischer). -/

section DetFactor

/-- **Gram determinant of an image is the square of the determinant times the source Gram det.**
For square `M W`, `det((M W)ᵀ (M W)) = (det M)² · (det W)²`. The pure algebraic core of the
determinant factorization: combining `det_mul`, `det_transpose`, `det_mul`. -/
theorem det_gram_image_eq (M W : Matrix (Fin d) (Fin d) ℝ) :
    ((M * W)ᵀ * (M * W)).det = (M.det) ^ 2 * (W.det) ^ 2 := by
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_mul]
  ring

/-- **Determinant factorization (squared form).** For an *orthogonal* block frame `W` (so
`det W = ±1`, `(det W)² = 1`), the squared determinant of `M` equals the Gram determinant of its
image block: `(det M)² = det((M W)ᵀ (M W))`. This is the algebraic identity the squeeze applies:
`(det M)²` factors as `det(Gram(M ω_F)) · det(Gram(M ω_S)) · sin²`. -/
theorem det_sq_eq_gram_image (M W : Matrix (Fin d) (Fin d) ℝ) (hW : (W.det) ^ 2 = 1) :
    (M.det) ^ 2 = ((M * W)ᵀ * (M * W)).det := by
  rw [det_gram_image_eq, hW, mul_one]

end DetFactor

/-! ## The determinant squeeze (volume-exponent form)

The squeeze in its decisive scalar form. Write `D(n) = (1/n) log|det A⁽ⁿ⁾|` (by
Furstenberg–Kesten, `→ Σ_all λ`), `VF(n) = (1/n) log vol(A⁽ⁿ⁾ ω_F)` (fast-frame volume;
tempered to `→ Σ_fast λ`), `VS(n) = (1/n) log vol(A⁽ⁿ⁾ ω_S)` (slow-frame volume), and
`S(n) = (1/n) log sin∠(A⁽ⁿ⁾F, A⁽ⁿ⁾S)` (tempered: `→ 0` by the tempering lemma). The
factorization gives, *with the orthogonal source frame `W`*, `D(n) = VF(n) + VS(n) + S(n)`
(taking logs of `|det A⁽ⁿ⁾| = volF·volS·sin`, using `|det W| = 1`). Hence

    VS(n) = D(n) − VF(n) − S(n)  →  Σ_all λ − Σ_fast λ − 0 = Σ_slow λ.

The lemma below is the pure limit arithmetic of the squeeze: it does *not* presuppose any
per-vector rate (the only convergence inputs are the Furstenberg–Kesten determinant limit, the
fast-volume Kingman limit, and the tempered-angle limit `→ 0`). This is what makes the argument
non-circular. -/

section Squeeze

/-- **Determinant squeeze (volume arithmetic).** If `D → dSum` (det exponent), `VF → fSum`
(fast-volume exponent), and the tempered angle `S → 0`, and the factorization
`D n = VF n + VS n + S n` holds eventually, then the slow-volume exponent converges:
`VS → dSum − fSum`. Pure arithmetic of the squeeze; the inputs are all *convergence* facts
(no rate assumed on any vector). -/
theorem tendsto_slowVolume_exponent {D VF VS S : ℕ → ℝ} {dSum fSum : ℝ}
    (hD : Tendsto D atTop (𝓝 dSum)) (hVF : Tendsto VF atTop (𝓝 fSum))
    (hS : Tendsto S atTop (𝓝 0))
    (hfact : ∀ᶠ n in atTop, D n = VF n + VS n + S n) :
    Tendsto VS atTop (𝓝 (dSum - fSum)) := by
  -- `VS n = D n − VF n − S n` eventually; the RHS tends to `dSum − fSum − 0`.
  have hrhs : Tendsto (fun n => D n - VF n - S n) atTop (𝓝 (dSum - fSum - 0)) :=
    (hD.sub hVF).sub hS
  rw [sub_zero] at hrhs
  refine hrhs.congr' ?_
  filter_upwards [hfact] with n hn
  rw [hn]; ring

/-- **Exponent-pinning squeeze (two terms).** If `a + b → A + B` (the volume sum has the exact
total exponent), `liminf a ≥ A` and `liminf b ≥ B` (the per-direction lower bounds), then
`limsup a ≤ A` (and symmetrically for `b`), so each converges to its lower bound. This is the
arithmetic that forces the top slow exponent to equal `λᵢ`: the slow volume `→ Σ_slow λ` decomposes
as `top-slow + rest`, the lower bounds pin `rest ≥ Σ_rest` and `top ≥ λᵢ`, and equality of the sum
squeezes `top ≤ λᵢ`. Stated as a clean two-term lemma; iterates to any finite split. -/
theorem limsup_le_of_sum_tendsto {a b : ℕ → ℝ} {A B : ℝ}
    (hsum : Tendsto (fun n => a n + b n) atTop (𝓝 (A + B)))
    (_ha : A ≤ liminf a atTop) (hb : B ≤ liminf b atTop)
    (haub : IsBoundedUnder (· ≤ ·) atTop a) (halb : IsBoundedUnder (· ≥ ·) atTop a)
    (hblb : IsBoundedUnder (· ≥ ·) atTop b)
    (hbub : IsBoundedUnder (· ≤ ·) atTop b) :
    limsup a atTop ≤ A := by
  -- `le_limsup_add`: `limsup a + liminf b ≤ limsup(a+b) = A + B`. With `liminf b ≥ B`:
  -- `limsup a ≤ (A+B) − liminf b ≤ (A+B) − B = A`.
  have hsumls : limsup (fun n => a n + b n) atTop = A + B := hsum.limsup_eq
  have hkey : limsup a atTop + liminf b atTop ≤ limsup (a + b) atTop :=
    le_limsup_add haub (halb.isCoboundedUnder_le) hbub hblb
  have hsum' : limsup (a + b) atTop = A + B := by
    rw [show (a + b) = (fun n => a n + b n) from rfl]; exact hsumls
  rw [hsum'] at hkey
  -- limsup a ≤ (A+B) − liminf b ≤ (A+B) − B = A.
  have : limsup a atTop ≤ (A + B) - liminf b atTop := by linarith
  calc limsup a atTop ≤ (A + B) - liminf b atTop := this
    _ ≤ (A + B) - B := by linarith [hb]
    _ = A := by ring

/-- **The determinant-squeeze closure (abstract operator-norm form).** Package the whole squeeze
into the spectral upper bound on the slow restricted operator norm. Let:
* `volS n` = slow-frame volume exponent term `(1/n) log vol(A⁽ⁿ⁾ ω_S)`, with `volS → slowSum`
  (the slow-exponent sum, supplied by `tendsto_slowVolume_exponent`);
* `topS n` = `(1/n) log ‖A⁽ⁿ⁾|_S‖` (top slow restricted singular exponent);
* `restS n` = `(1/n) log (vol / ‖·|_S‖)` (product of the remaining `q−1` slow singular exponents),
  so `volS n = topS n + restS n` (the volume factors as top × rest);
* lower bounds `liminf topS ≥ lamI` (the top slow direction grows at ≥ λᵢ) and
  `liminf restS ≥ restSum` with `lamI + restSum = slowSum` (the remaining directions).

Then `limsup topS ≤ lamI`: the squeeze pins the top slow exponent at exactly `λᵢ`. This is the
spectral upper bound on the slow subspace, obtained non-circularly: no per-vector growth was
assumed, only the volume limit and the unconditional lower bounds. -/
theorem limsup_topSlow_le_of_squeeze {volS topS restS : ℕ → ℝ} {slowSum lamI restSum : ℝ}
    (hvolS : Tendsto volS atTop (𝓝 slowSum))
    (hsplit : slowSum = lamI + restSum)
    (hfact : ∀ᶠ n in atTop, volS n = topS n + restS n)
    (htop_lb : lamI ≤ liminf topS atTop) (hrest_lb : restSum ≤ liminf restS atTop)
    (htop_ub : IsBoundedUnder (· ≤ ·) atTop topS) (htop_glb : IsBoundedUnder (· ≥ ·) atTop topS)
    (hrest_lbd : IsBoundedUnder (· ≥ ·) atTop restS)
    (hrest_ubd : IsBoundedUnder (· ≤ ·) atTop restS) :
    limsup topS atTop ≤ lamI := by
  -- `volS = topS + restS → lamI + restSum`; apply the two-term pinning squeeze.
  have hsum : Tendsto (fun n => topS n + restS n) atTop (𝓝 (lamI + restSum)) := by
    rw [← hsplit]; exact hvolS.congr' (hfact.mono fun n hn => hn)
  exact limsup_le_of_sum_tendsto hsum htop_lb hrest_lb htop_ub htop_glb hrest_lbd hrest_ubd

end Squeeze

/-! ## From the slow restricted operator norm to the per-vector spectral upper bound

The final step: once `limsup (1/n) log ‖A⁽ⁿ⁾|_S‖ ≤ λᵢ`, every `v` in the slow subspace `S` obeys
`‖A⁽ⁿ⁾ v‖ ≤ ‖A⁽ⁿ⁾|_S‖ · ‖v‖`, so `limsup (1/n) log ‖A⁽ⁿ⁾ v‖ ≤ λᵢ`, the desired spectral upper
bound. This is pure operator-norm monotonicity plus log arithmetic; no circularity, since the
slow-norm bound came from the global volume squeeze, not from this vector. -/

section PerVector

/-- **Per-vector upper bound from the restricted operator-norm bound.** If the slow restricted
operator-norm exponent `R n = (1/n) log r n` has `limsup R ≤ lamI`, and the per-vector growth
satisfies `‖A⁽ⁿ⁾ v‖ ≤ r n · ‖v‖` eventually (`r n ≥ 0`, `v ≠ 0`), then
`limsup (1/n) log ‖A⁽ⁿ⁾ v‖ ≤ lamI`. -/
theorem limsup_apply_le_of_restricted_norm {Mv : ℕ → ℝ} {r : ℕ → ℝ} {c lamI : ℝ}
    (hc : 0 < c)
    (hbound : ∀ᶠ n in atTop, Mv n ≤ r n * c) (hrnn : ∀ᶠ n in atTop, 0 ≤ r n)
    (hMvpos : ∀ᶠ n in atTop, 0 < Mv n)
    (hR : limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (r n)) atTop ≤ lamI)
    (hRbdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (r n)))
    (hcobdd : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (Mv n))) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (Mv n)) atTop ≤ lamI := by
  set g : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * Real.log (Mv n) with hg
  set R : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * Real.log (r n) with hR'
  -- pointwise: `g n ≤ R n + (1/n) log c` eventually (log monotone; r n > 0 from Mv n > 0).
  have hcorr : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log c) atTop (𝓝 0) := by
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.mul_const (Real.log c)
    simpa using this
  have hle : g ≤ᶠ[atTop] (fun n => R n + (n : ℝ)⁻¹ * Real.log c) := by
    filter_upwards [hbound, hrnn, hMvpos, eventually_ge_atTop 1] with n hb hr hmv hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    have hrpos : 0 < r n := by
      rcases lt_or_eq_of_le hr with h | h
      · exact h
      · exfalso; rw [← h] at hb; simp at hb; linarith [hmv, hb]
    -- log Mv ≤ log (r·c) = log r + log c
    have hlog : Real.log (Mv n) ≤ Real.log (r n) + Real.log c := by
      have h1 : Real.log (Mv n) ≤ Real.log (r n * c) := Real.log_le_log hmv hb
      rwa [Real.log_mul (ne_of_gt hrpos) (ne_of_gt hc)] at h1
    have := mul_le_mul_of_nonneg_left hlog hninv
    simp only [hg, hR']
    rw [mul_add] at this; linarith [this]
  -- conclude `limsup g ≤ lamI` via `limsup_le_iff`: for `y > lamI`, eventually `g n < y`.
  have hgbdd : IsBoundedUnder (· ≤ ·) atTop g := by
    refine isBoundedUnder_of_eventually_le (a := lamI + 1) ?_
    -- from hle and eventual `R n < lamI + 1/2`, `corr n < 1/2`.
    have hRev : ∀ᶠ n in atTop, R n < lamI + 1 / 2 :=
      eventually_lt_of_limsup_lt (lt_of_le_of_lt hR (by linarith)) hRbdd
    have hcev : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * Real.log c < 1 / 2 :=
      hcorr.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
    filter_upwards [hle, hRev, hcev] with n hn hR' hc' using by simp only [hg] at hn ⊢; linarith
  rw [limsup_le_iff hcobdd hgbdd]
  intro y hy
  have hRev : ∀ᶠ n in atTop, R n < lamI + (y - lamI) / 2 :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hR (by linarith)) hRbdd
  have hcev : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * Real.log c < (y - lamI) / 2 :=
    hcorr.eventually (gt_mem_nhds (by linarith : (0:ℝ) < (y - lamI) / 2))
  filter_upwards [hle, hRev, hcev] with n hn hR' hc'
  simp only [hg] at hn ⊢
  linarith

end PerVector

/-! ## The spectral upper bound for a slow cocycle vector (non-circular)

The full chain assembled into one statement about the cocycle `A⁽ⁿ⁾`. For a `Λ`-slow vector `v`
(in the limit slow subspace `S(x)`), the determinant squeeze provides — non-circularly — the slow
restricted-operator-norm exponent bound `limsup (1/n) log ‖A⁽ⁿ⁾|_S‖ ≤ λᵢ` (`hslownorm`, the output
of `limsup_topSlow_le_of_squeeze`), and the restriction bound `‖A⁽ⁿ⁾ v‖ ≤ ‖A⁽ⁿ⁾|_S‖ · ‖v‖`
(`hrestrict`, valid because `v ∈ S`). The conclusion is the spectral upper bound

    limsup_n (1/n)·log ‖A⁽ⁿ⁾ v‖  ≤  λᵢ.

The non-circularity is structural: `hslownorm` is determined by the *global* volume cocycle (the
Furstenberg–Kesten determinant limit, the fast-volume Kingman limit, and the tempered angle `→ 0`)
together with the lower bounds — none of which references the growth of *this* vector. The
per-vector bound is then a one-line operator-norm consequence. -/

section Capstone

omit [MeasurableSpace X] in
/-- **Spectral upper bound for a slow cocycle vector (via the determinant squeeze).** Given the
slow restricted-operator-norm exponent bound `hslownorm` (the squeeze output) and the restriction
bound `hrestrict` (valid for `v` in the slow subspace), the per-vector growth obeys
`limsup (1/n) log ‖A⁽ⁿ⁾ v‖ ≤ λᵢ`. The remaining side conditions are the routine
boundedness/positivity facts (`hrnn`, `hMvpos`, `hRbdd`, `hcobdd`). -/
theorem spectral_upper_bound_of_squeeze {A : X → Matrix (Fin d) (Fin d) ℝ} {x : X}
    {v : EuclideanSpace ℝ (Fin d)} {lamI : ℝ} {r : ℕ → ℝ} (hv : v ≠ 0)
    (hslownorm : limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (r n)) atTop ≤ lamI)
    (hrestrict : ∀ᶠ n : ℕ in atTop,
      ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ ≤ r n * ‖v‖)
    (hrnn : ∀ᶠ n : ℕ in atTop, 0 ≤ r n)
    (hMvpos : ∀ᶠ n : ℕ in atTop, 0 < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)
    (hRbdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (r n)))
    (hcobdd : IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ lamI := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  exact limsup_apply_le_of_restricted_norm hvpos hrestrict hrnn hMvpos hslownorm hRbdd hcobdd

end Capstone

end Oseledets
