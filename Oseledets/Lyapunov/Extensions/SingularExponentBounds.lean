/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.Extensions.SingularExponent

/-!
# Tie-in bounds for the forward singular exponent `γ_k`

This module connects the cumulative forward singular exponent
`Oseledets.forwardSingularExponent` (the `EReal`-valued `γ_k` of
`Oseledets/Lyapunov/Extensions/SingularExponent.lean`) to the top-singular-value growth that
underlies it. The cumulative exponent `γ_k = limsup_n (1/n) log⁺ sprod_k` is built from the
top-`k` singular-value product `sprod_k = ∏_{i<k} σᵢ(A⁽ⁿ⁾)`. Each singular value is bounded by
the L2 operator norm `‖A⁽ⁿ⁾‖` (`Oseledets.sigma_le_opNorm`), so `sprod_k ≤ ‖A⁽ⁿ⁾‖^k`, and
`log⁺` of a `k`-th power scales by `k` (`Real.posLog_pow`). Passing to the `EReal`-`limsup` and
pulling out the (finite, non-negative) constant `k`
(`EReal.limsup_const_mul_of_nonneg_of_ne_top`) gives the **deterministic** linear-in-`k` bound

`γ_k(x) ≤ (k : EReal) · limsup_n ((1/n) log⁺‖A⁽ⁿ⁾(x)‖ : EReal)`.

This is the `EReal` `log⁺`-norm-growth ceiling on the cumulative singular exponent, with no
ergodicity, integrability, or invertibility hypothesis. It says the top-`k` volume exponent can
grow at most `k` times as fast as the top operator-norm exponent — the singular-cocycle
counterpart of `γ_k ≤ k λ₁`.

## Main results

* `Oseledets.forwardPosLogNormLimsup` — the `EReal` `limsup` of the normalized `log⁺`-operator
  norms `(1/n) log⁺‖A⁽ⁿ⁾(x)‖`; the `k = 1` ceiling for `γ_k`.
* `Oseledets.forwardSingularExponent_le_natCast_mul` — the deterministic bound
  `γ_k(x) ≤ (k : EReal) · forwardPosLogNormLimsup A T x` for every `x`.

## Implementation notes

* Everything here is **deterministic** (holds for every `x`, no measure-theoretic hypothesis):
  the bound is a pure consequence of the singular-value/operator-norm inequality and the scaling
  of `log⁺` under powers. The constant `k` is pulled out of the `EReal`-`limsup` via
  `EReal.limsup_const_mul_of_nonneg_of_ne_top`, valid because `(k : EReal)` is non-negative and
  finite.
* The right-hand `limsup` is taken over the `log⁺`-operator norms (the *convergent* quantity); it
  is **not** `γ_1`. Identifying it with `γ_1` would require `sprod_1 = ‖A⁽ⁿ⁾‖`, i.e. the top
  singular value equals the operator norm — that identity is not available here, so the ceiling
  is stated through the operator-norm `limsup` directly.

## References

* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {T : X → X} {d : ℕ}

/-- **The forward `log⁺`-operator-norm `limsup`.** The `EReal`-valued
`limsup_n ((1/n) log⁺‖A⁽ⁿ⁾(x)‖ : EReal)`, the top operator-norm growth ceiling that bounds the
cumulative forward singular exponent `γ_k` (see `forwardSingularExponent_le_natCast_mul`). On the
`μ`-a.e. convergence set (`tendsto_top_posLogNorm`) it is the forward top value `λ₁⁺`. -/
noncomputable def forwardPosLogNormLimsup (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (x : X) : EReal :=
  Filter.limsup
    (fun n : ℕ => (((n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖ : ℝ) : EReal)) atTop

omit [MeasurableSpace X] in
/-- **Deterministic linear-in-`k` ceiling for `γ_k`.** For every `x`,

`γ_k(x) ≤ (k : EReal) · limsup_n ((1/n) log⁺‖A⁽ⁿ⁾(x)‖ : EReal)`.

Each top-`k` singular-value product satisfies `sprod_k ≤ ‖A⁽ⁿ⁾‖^k` (every singular value is
`≤ ‖A⁽ⁿ⁾‖`, `Oseledets.sigma_le_opNorm`), so `log⁺ sprod_k ≤ log⁺(‖A⁽ⁿ⁾‖^k) = k · log⁺‖A⁽ⁿ⁾‖`
(`Real.posLog_pow`). Multiplying by `(n : ℝ)⁻¹ ≥ 0` and passing to the `EReal`-`limsup`
(monotone), the constant `k` is pulled out by `EReal.limsup_const_mul_of_nonneg_of_ne_top`. No
ergodicity, integrability, or invertibility is used. -/
theorem forwardSingularExponent_le_natCast_mul (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (k : ℕ) (x : X) :
    forwardSingularExponent A T k x ≤ (k : EReal) * forwardPosLogNormLimsup A T x := by
  -- Termwise real bound: `(1/n) log⁺ sprod_k ≤ k · ((1/n) log⁺‖A⁽ⁿ⁾‖)`.
  have hterm : ∀ n : ℕ,
      (((n : ℝ)⁻¹ * Real.posLog (sprod A T k n x) : ℝ) : EReal)
        ≤ (((k : ℝ) * ((n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖) : ℝ) : EReal) := by
    intro n
    refine EReal.coe_le_coe_iff.2 ?_
    -- `sprod_k ≤ ‖A⁽ⁿ⁾‖^k`.
    have hle : sprod A T k n x ≤ ‖cocycle A T n x‖ ^ k := by
      rw [sprod]
      calc ∏ i ∈ Finset.range k,
            (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i
          ≤ ∏ _i ∈ Finset.range k, ‖cocycle A T n x‖ :=
            Finset.prod_le_prod
              (fun i _ => (Matrix.toEuclideanLin (cocycle A T n x)).singularValues_nonneg i)
              (fun i _ => sigma_le_opNorm _ i)
        _ = ‖cocycle A T n x‖ ^ k := by rw [Finset.prod_const, Finset.card_range]
    -- `log⁺ sprod_k ≤ k · log⁺‖A⁽ⁿ⁾‖`.
    have hposLog : Real.posLog (sprod A T k n x)
        ≤ (k : ℝ) * Real.posLog ‖cocycle A T n x‖ := by
      calc Real.posLog (sprod A T k n x)
          ≤ Real.posLog (‖cocycle A T n x‖ ^ k) :=
            Real.posLog_le_posLog (sprod_nonneg A k n x) hle
        _ = (k : ℝ) * Real.posLog ‖cocycle A T n x‖ := Real.posLog_pow k _
    -- Multiply by `(n : ℝ)⁻¹ ≥ 0` and rearrange.
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left hposLog (by positivity)
  -- Pass to the `EReal`-`limsup` and pull out the constant `k`.
  calc forwardSingularExponent A T k x
      ≤ Filter.limsup
          (fun n : ℕ => (((k : ℝ) * ((n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖) : ℝ) : EReal))
          atTop :=
        Filter.limsup_le_limsup (Filter.Eventually.of_forall hterm)
    _ = Filter.limsup
          (fun n : ℕ => ((k : ℝ) : EReal)
            * (((n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖ : ℝ) : EReal)) atTop := by
        refine Filter.limsup_congr (Filter.Eventually.of_forall fun n => ?_)
        rw [EReal.coe_mul]
    _ = ((k : ℝ) : EReal) * forwardPosLogNormLimsup A T x :=
        EReal.limsup_const_mul_of_nonneg_of_ne_top (by positivity) (EReal.coe_ne_top _)
    _ = (k : EReal) * forwardPosLogNormLimsup A T x := by rw [EReal.coe_natCast]

end Oseledets
