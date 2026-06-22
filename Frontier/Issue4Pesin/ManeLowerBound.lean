/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Frontier.Issue4Pesin.SRBData

/-!
# Pesin's entropy formula, part 2: Mañé's lower bound `∑ λ_i⁺ ≤ h_μ(T)`

This module decomposes the **hard reverse inequality** of Pesin's formula,
`∑_i λ_i⁺ ≤ h_μ(T)` (equivalently `∫ χ dμ ≤ h_μ(T)` with `χ = ∑ λ_i⁺`), for an SRB measure,
following Mañé's proof (Contractor *The Pesin Entropy Formula*, §7, Theorem 7.15 and Proposition
7.7). Each genuinely missing piece of Pesin / Ledrappier–Young theory is a single, precisely
documented `BLOCKED` leaf; the abstract scaffolding around them is recorded so the decomposition is
auditable.

## The Mañé proof, top-down

The reverse inequality is assembled from two layers (Contractor §7):

1. **Mañé's abstract entropy lower bound (Proposition 7.7).** If `ν` is a (not necessarily
   invariant) measure absolutely continuous w.r.t. the invariant `μ`, then
   `h_μ(g) ≥ ∫ h_ν(g, ρ, x) dμ`, where `h_ν(g, ρ, x)` is the *local `ν`-entropy* along the
   `ρ(x)`-balls — the exponential shrink-rate of `ν` of the `n`-step dynamical refinement of the
   ball `B_{ρ(x)}(x)`. This is a measure-theoretic / entropy statement (no manifold structure),
   but it rests on the Shannon–McMillan–Breiman theorem and a covering argument absent from
   Mathlib's entropy API. Packaged as `mane_entropy_lower_bound` (BLOCKED leaf).

2. **The unstable-Jacobian local-entropy estimate (7.17/7.18).** The geometric heart: for `μ`-a.e.
   `x`, the local `ν`-entropy is bounded below by the unstable Jacobian rate,
   `h_ν(g, ρ, x) ≥ N(χ(x) − ε)`. This is where the **SRB property** enters: taking `ν` = leaf
   (Lebesgue) volume on unstable manifolds, absolute continuity of `μ`'s conditional measures
   (`SRBProperty`) makes `ν ≪ μ` usable in step 1, and the volume of the image of an unstable disk
   under `g^n` grows like `exp(n · χ)` (the unstable Jacobian, `UnstableJacobianRate`), forcing the
   `ν`-measure of the `n`-refinement to shrink at rate `χ`. Packaged as
   `local_entropy_ge_unstable_jacobian` (BLOCKED leaf), built on the dispersion-`c` graph-transform
   lemmas (Contractor 7.9, 7.11, 7.14) and the unstable-Jacobian volume bound.

Combining 1 and 2 and integrating gives `h_μ(g) ≥ ∫ χ dμ` for the iterate `g = f^N`; dividing by
`N` (`h_μ(f^N) = N · h_μ(f)`, the entropy power rule) and letting `ε → 0` gives
`h_μ(f) ≥ ∫ χ dμ = sumPosExp`.

## Main results

* `Frontier.Issue4Pesin.sumPosExp_le_ksEntropy_of_SRB` — the reverse inequality
  `(sumPosExp : EReal) ≤ h_μ(T)` for an SRB measure, assembled top-down from the two BLOCKED
  geometric leaves above.

## Status

Both leaves (`mane_entropy_lower_bound`, `local_entropy_ge_unstable_jacobian`) are genuine
Mathlib-scale gaps (Pesin theory, the unstable foliation, Shannon–McMillan–Breiman + Brin–Katok
local entropy). They are stated and used; the geometric content is `BLOCKED`. The capstone
`sumPosExp_le_ksEntropy_of_SRB` chains them, so the *route* is fully auditable and the only `sorry`s
are at the two named leaves.

## References

* Maryam Contractor, *The Pesin Entropy Formula*, UChicago REU 2023, §7 (Proposition 7.7,
  Theorem 7.15, Lemmas 7.9/7.11/7.14).
* R. Mañé, *A proof of Pesin's formula*, Ergodic Theory Dynam. Systems **1** (1981) 95–102.
* F. Ledrappier, J.-M. Strelcyn, *A proof of the estimation from below in Pesin's entropy formula*,
  Ergodic Theory Dynam. Systems **2** (1982) 203–219.
-/

open MeasureTheory Filter Topology

namespace Frontier.Issue4Pesin

variable {d : ℕ} [NeZero d]

section AnalyticCore

/-- **The Radon–Nikodym density-rate vanishing (reusable analytic core of Mañé's Prop. 7.7,
step 3 — the `1/n · log(μ(Pₙ)/ν(Pₙ)) → 0` claim).**

In Mañé's proof of the abstract entropy lower bound (Contractor Prop. 7.7), the only non-trivial
analytic input is that the log-density ratio of the two measures along the dynamical refinement
`Pₙ` of a partition decays at sub-exponential rate:
`(1/n) · log(μ(Pₙ(x)) / ν(Pₙ(x))) → 0` a.e.

The measure ratio `r n := μ(Pₙ)/ν(Pₙ)` is a martingale (conditional density) that converges a.e. to
a **finite, strictly positive** limit `k(x)` by Lévy's upward theorem
(`MeasureTheory.Integrable.tendsto_ae_condExp`); since `k(x) ≠ 0`, the logarithm `log (r n)`
converges to the finite value `log (k x)`, and dividing a convergent sequence by `n → ∞` sends it
to `0`. This lemma isolates *that last, purely real-analytic step*, fully `sorry`-free: it is the
implication "`rₙ → k` with `k > 0` ⟹ `(1/n)·log rₙ → 0`", which is exactly what the martingale
limit feeds into. It is reusable for any sub-exponential-rate argument of this shape (e.g. the
Shannon–McMillan–Breiman density step, Brin–Katok local entropy).

This is the genuinely reachable piece L1b of the feasibility decomposition, landed sorry-free. -/
theorem rate_log_div_tendsto_zero_of_tendsto_pos
    {r : ℕ → ℝ} {k : ℝ} (hk : 0 < k) (hr : Tendsto r atTop (𝓝 k)) :
    Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (r n)) atTop (𝓝 0) := by
  -- `log ∘ r → log k`, a finite limit, because `r → k` and `log` is continuous at `k > 0`.
  have hlog : Tendsto (fun n : ℕ => Real.log (r n)) atTop (𝓝 (Real.log k)) :=
    (Real.continuousAt_log (ne_of_gt hk)).tendsto.comp hr
  -- `1/n → 0`.
  have hinv : Tendsto (fun n : ℕ => (1 / (n : ℝ))) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  -- Product of a null sequence with a convergent (hence eventually bounded) sequence is null.
  have hmul : Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (r n)) atTop (𝓝 (0 * Real.log k)) :=
    hinv.mul hlog
  simpa using hmul

end AnalyticCore

section LowerBound

variable {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : Ergodic T μ)
    (hdet : ∀ x, (Oseledets.derivativeCocycle T x).det ≠ 0)
    (hint : Oseledets.IntegrableLogNorm (Oseledets.derivativeCocycle T) μ)
    (hint' : Oseledets.IntegrableLogNorm (fun x => (Oseledets.derivativeCocycle T x)⁻¹) μ)

/-- **The local `ν`-entropy `h_ν(T, ρ, x)` of Mañé's proof (Contractor §7).**

For the reference measure `ν` (leaf / Lebesgue volume on unstable manifolds, related to `μ` by the
SRB property) and the radius function `ρ`, this is the exponential shrink-rate of `ν` of the
`n`-step dynamical refinement `Sₙ(T, ρ, x)` of the ball `B_{ρ(x)}(x)`:
`h_ν(T, ρ, x) := limsup_n  -(1/n) · log ν(Sₙ(T, ρ, x))`.

It is the quantity bounded below in Layer 1 (`manePropLowerBound`, Prop. 7.7) and from above by the
unstable Jacobian rate in Layer 2 (`localEntropy_ge_unstableJacobian`, (7.17)/(7.18)).

It is introduced here as an **opaque** real-valued function (a black box supplied by the Pesin /
local-entropy theory that is absent from Mathlib): the dynamical refinement `Sₙ`, the radius `ρ`,
and the leaf measure `ν` are not yet formalizable, so `localNuEntropy` carries no exploitable
content. The two layers below state precisely the inequalities Mañé proves about it; the present
opacity is the honest record that its construction is the BLOCKED geometric gap. -/
opaque localNuEntropy
    {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : Ergodic T μ)
    (hdet : ∀ x, (Oseledets.derivativeCocycle T x).det ≠ 0)
    (hint : Oseledets.IntegrableLogNorm (Oseledets.derivativeCocycle T) μ)
    (hint' : Oseledets.IntegrableLogNorm (fun x => (Oseledets.derivativeCocycle T x)⁻¹) μ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ

/-- **Layer 1 — Mañé's abstract entropy lower bound (Contractor Proposition 7.7).**

If `ν` is a (not necessarily invariant) measure absolutely continuous with respect to the invariant
`μ` (`hSRB` provides this via the SRB absolute-continuity of `μ`'s conditional measures on unstable
manifolds), then the metric entropy of the system dominates the integral of the local `ν`-entropy:
`h_μ(T) ≥ ∫ h_ν(T, ρ, x) dμ`, and the local-entropy integrand is integrable.

Concretely (with `h_ν = localNuEntropy …`):
`Integrable (localNuEntropy …)` and `(∫ x, localNuEntropy … x ∂μ : EReal) ≤ ksEntropy hT`.

**Proof structure (Mañé, Contractor §7, partition-free route).**
1. **Lemma 7.5/7.6**: from `log ρ ∈ L¹`, build a *countable* partition `P` with `H(P) < ∞` and
   `diam P(x) ≤ ρ(x)` a.e.
2. **Shannon–McMillan–Breiman** (Contractor Thm 2.14) + the KS definition:
   `h_μ(T) ≥ h_μ(P, T) = ∫ limₙ (1/n)·[−log μ(Pₙ(x))] dμ`.
3. Split `(1/n) log μ(Pₙ) = (1/n) log ν(Pₙ) + (1/n) log(μ(Pₙ)/ν(Pₙ))`; the **second term → 0 a.e.**
   by the Radon–Nikodym / Lévy-upward martingale limit — the reusable analytic core
   `rate_log_div_tendsto_zero_of_tendsto_pos` above isolates exactly this step.
4. Hence `limₙ (1/n)·[−log μ(Pₙ)] = limₙ (1/n)·[−log ν(Pₙ)] ≥ h_ν(T, ρ, x)` (since the refinement
   `Sₙ ⊂ Pₙ` up to the `ρ`-ball containment).

`BLOCKED`: this layer is pure measure / entropy theory — **no manifold, no Pesin splitting, no
foliation** — but it needs (i) a *countable*-partition Kolmogorov–Sinai entropy API (Mathlib and
this project have only finite partitions), and (ii) the **Shannon–McMillan–Breiman theorem**
(absent from Mathlib). The one genuinely analytic substep (the density-rate limit, L1b) is provided
sorry-free by `rate_log_div_tendsto_zero_of_tendsto_pos`. -/
theorem manePropLowerBound
    {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hSRB : SRBProperty T μ) :
    Integrable (localNuEntropy hT hdet hint hint') μ ∧
      ((∫ x, localNuEntropy hT hdet hint hint' x ∂μ : ℝ) : EReal)
        ≤ Oseledets.Entropy.ksEntropy hT.toMeasurePreserving := by
  -- The SRB absolute continuity is what makes `ν ≪ μ` usable in Prop. 7.7; it is named but its
  -- geometric content is the BLOCKED gap. The `χ` argument records that this layer feeds the same
  -- integrand that Layer 2 bounds below.
  let _ := hSRB.acConditionalUnstable
  let _ := χ
  sorry

/-- **Layer 2 — the unstable-Jacobian local-entropy estimate (Contractor Theorem 7.15,
eqns (7.17)/(7.18)).**

For `μ`-a.e. `x`, the local `ν`-entropy is bounded **below** by the unstable-Jacobian rate `χ(x)`:
`χ(x) ≤ h_ν(T, ρ, x)`  a.e.  (with `χ = ∑_i λ_i⁺` the positive-exponent sum, `hχ`).

**Proof structure (Mañé, Contractor §7, the geometric heart).**
* Pesin block `K` (`μ(K) > 0`) carrying a measurable continuous splitting `Eˢ(x) ⊕ Eᵘ(x)` (§5, §7).
* **Birkhoff ergodic theorem** to control the first-return time `N(x)` to `K` and the orbit fraction
  outside `K` (`#{j < n : Tʲx ∉ K} ≤ 2n√ε`). *(This project owns a real Birkhoff pointwise theorem,
  `Oseledets.tendsto_birkhoffAverage_ae`, absent from Mathlib.)*
* **Graph-transform Lemmas 7.9/7.11/7.14**: dispersion-`c` `(Eˢ, Eᵘ)`-graphs map to graphs under
  `Tⁿ` (needs `C^{1+α}` Hölder control `‖DTⁿ_x − DTⁿ_y‖ ≤ Cⁿ‖x−y‖ᵗ`).
* **Fubini on the unstable disk** + the unstable-Jacobian lower bound
  `log|det DTⁿ|_{T_zΛₙ(y)}| ≥ ∑_{j∈Fₙ} log|det DT|Eᵘ| − εn − …` give (7.18):
  `h_ν(T, ρ, x) ≥ N(χ(x) − O(√ε))`.

`BLOCKED`: this is the genuine multi-year Pesin / Ledrappier–Young wall — the measurable
`Eˢ ⊕ Eᵘ` splitting on a positive-measure Pesin block, the stable/unstable manifold theorem, the
unstable foliation and **its absolute continuity** (the SRB bridge), leaf disintegration, and the
unstable-disk volume growth. None of these exist in Mathlib. The hypotheses `hSRB`, `hχ` name
exactly the data this layer consumes. -/
theorem localEntropy_ge_unstableJacobian
    {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hSRB : SRBProperty T μ)
    (hχ : UnstableJacobianRate hT hdet hint hint' χ) :
    ∀ᵐ x ∂μ, χ x ≤ localNuEntropy hT hdet hint hint' x := by
  let _ := hSRB.acConditionalUnstable
  let _ := hχ
  sorry

/-- **Mañé's abstract entropy lower bound (Contractor Proposition 7.7), composed with the
unstable-Jacobian local-entropy estimate (Contractor (7.17)/(7.18)): the reverse inequality.**

For an SRB measure (`hSRB`), with `χ` the unstable-Jacobian integrand identified with the
positive-exponent sum (`hχ : UnstableJacobianRate …`), the positive-exponent sum is bounded above
by the Kolmogorov–Sinai entropy of the system:
`(sumPosExp : EReal) ≤ h_μ(T)`.

This is the reverse direction of Pesin's formula. Its proof is Mañé's two-layer argument:

* (Layer 1, Proposition 7.7) `h_μ(T) ≥ ∫ h_ν(T, ρ, x) dμ` for `ν ≪ μ` the leaf volume — uses
  Brin–Katok / Shannon–McMillan–Breiman local entropy, absent from Mathlib.
* (Layer 2, (7.17)/(7.18)) `h_ν(T, ρ, x) ≥ χ(x)` a.e. — uses the dispersion-`c` graph transform
  (7.9/7.11/7.14), the unstable-Jacobian volume growth `vol(g^n(unstable disk)) ≈ exp(n·χ)`, and
  the SRB absolute continuity (`hSRB`) to transfer the leaf-volume shrink rate to `μ`.

Integrating: `h_μ(T) ≥ ∫ χ dμ = sumPosExp` (a probability measure integrates the a.e.-constant `χ`
to `sumPosExp`).

`BLOCKED`: both layers are Mathlib-scale Pesin / Ledrappier–Young infrastructure (local entropy
theory; the measurable `Eˢ ⊕ Eᵘ` splitting and its unstable foliation; absolute continuity of the
foliation / conditional measures). The hypotheses `hSRB`, `hχ` name precisely the data those layers
consume; the geometric derivation is the documented gap. -/
theorem sumPosExp_le_ksEntropy_of_SRB
    {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hSRB : SRBProperty T μ)
    (hχ : UnstableJacobianRate hT hdet hint hint' χ) :
    ((Oseledets.sumPosExp hT hdet (Oseledets.measurable_derivativeCocycle T) hint hint' : ℝ)
        : EReal)
      ≤ Oseledets.Entropy.ksEntropy hT.toMeasurePreserving := by
  -- The route (sorry-free plumbing chaining the two BLOCKED layers):
  --   `sumPosExp = ∫ χ dμ ≤ ∫ h_ν(T,ρ,·) dμ ≤ h_μ(T)`.
  -- The first `=` is L0 (a.e.-constant integrand over a probability measure); the middle `≤` is
  -- integral-monotonicity of Layer 2's pointwise bound `χ ≤ h_ν` a.e.; the final `≤` is Layer 1
  -- (Mañé's Prop. 7.7). Only the two layers carry `sorry`; the assembly here is honest.
  --
  -- Layer 2: `χ ≤ h_ν` a.e.
  have hL2 : ∀ᵐ x ∂μ, χ x ≤ localNuEntropy hT hdet hint hint' x :=
    localEntropy_ge_unstableJacobian hT hdet hint hint' hSRB hχ
  -- Layer 1: `h_ν` integrable and `∫ h_ν ≤ h_μ(T)`.
  obtain ⟨hLint, hL1⟩ := manePropLowerBound (χ := χ) hT hdet hint hint' hSRB
  -- L0: `χ` is a.e. the constant `sumPosExp`, hence integrable, with `∫ χ = sumPosExp`.
  have hχsymm : (fun _ : EuclideanSpace ℝ (Fin d) => Oseledets.sumPosExp hT hdet
      (Oseledets.measurable_derivativeCocycle T) hint hint') =ᵐ[μ] χ := by
    filter_upwards [hχ] with x hx using hx.symm
  have hχint : Integrable χ μ :=
    (integrable_const (Oseledets.sumPosExp hT hdet
      (Oseledets.measurable_derivativeCocycle T) hint hint')).congr hχsymm
  have hχint_eq : (∫ x, χ x ∂μ)
      = Oseledets.sumPosExp hT hdet (Oseledets.measurable_derivativeCocycle T) hint hint' := by
    rw [integral_congr_ae hχ, integral_const, probReal_univ, one_smul]
  -- Middle step (L3 plumbing): integral-monotonicity of the a.e. bound `χ ≤ h_ν`.
  have hmid : (∫ x, χ x ∂μ) ≤ ∫ x, localNuEntropy hT hdet hint hint' x ∂μ :=
    integral_mono_ae hχint hLint hL2
  -- Chain: `(sumPosExp : EReal) = (∫ χ) ≤ (∫ h_ν) ≤ h_μ(T)`.
  calc ((Oseledets.sumPosExp hT hdet
          (Oseledets.measurable_derivativeCocycle T) hint hint' : ℝ) : EReal)
      = ((∫ x, χ x ∂μ : ℝ) : EReal) := by rw [hχint_eq]
    _ ≤ ((∫ x, localNuEntropy hT hdet hint hint' x ∂μ : ℝ) : EReal) := by
        exact_mod_cast EReal.coe_le_coe_iff.mpr hmid
    _ ≤ Oseledets.Entropy.ksEntropy hT.toMeasurePreserving := hL1

end LowerBound

end Frontier.Issue4Pesin
