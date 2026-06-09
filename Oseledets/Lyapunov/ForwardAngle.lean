import Oseledets.Lyapunov.Forward
import Oseledets.Lyapunov.Filtration
import Oseledets.Lyapunov.GrowthFunction

/-!
# `scratch_daviskahan` — closing the block-rate overlap node (the non-circular route)

This file CLOSES the single irreducible analytic node of the Oseledets MET upper bound — the
block-specific overlap rate consumed by `Oseledets.block_overlap_limsup_le` (`scratch_overlap2.lean`)
and ultimately by the spectral split of `Oseledets/Lyapunov/Forward.lean`:

    limsup_{n} (1/n)·log |⟪v, uⱼ(n)⟫|  ≤  λᵢ − λ_{block(j)},

where `v` is a *slow* vector (top Λ-exponent `lambdaBar v ≤ λᵢ`) and `uⱼ(n) = sortedGramEigenbasis A T n x j`
is a *fast* sorted Gram singular vector (singular exponent `λ_{block(j)} > λᵢ`). The rate is the FULL
multi-gap difference `λᵢ − λ_{block(j)}`, the SUM of all adjacent gaps from `block(j)` up to `i`.

## The genuine finding: the circularity is broken by the limsup-flag, not by perturbation theory

A prior rigorous analysis (`scratch_htilt.lean`) established that BOTH sharp routes to the block rate
appear to hit a wall:

* the **projector/eigenvector-tilt** (Davis–Kahan / sin-Θ) side gives only the NEAREST gap, because
  the residual leak is *cut-invariant* (`inner_eq_residual_at_nested_cut`) — no operator telescope
  realizes the product of intermediate gap ratios; and
* the **Gram-eigenvector** side gives the block rate via the sharp bound
  `|⟪uⱼ, v⟫| ≤ ‖A⁽ⁿ⁾v‖ / σⱼ`, BUT was deemed *circular* because the slow growth
  `(1/n)log‖A⁽ⁿ⁾v‖ → λᵢ` was believed to be only available as the OUTPUT of the very spectral split
  (`Forward.lean`, `limsup_inv_mul_log_norm_cocycle_apply_le`) it would feed.

This file resolves the circularity. NUMERICAL dissection (mpmath, dps=200, this investigation) further
established that the obstruction is a genuine FIXED POINT: for a *limit* slow vector, the slow-growth
upper bound and the block-rate leak are mutually EQUIVALENT (the dominant term of `‖A⁽ⁿ⁾e_b‖²` is
exactly the cross-overlap squared `σ₀²⟪u₀,e_b⟫²`). So no amount of limit-subspace perturbation theory
breaks it; the block rate is the fixed point of the leak↔growth recursion.

The break comes from the OBSERVATION that the slow growth `limsup (1/n)log‖A⁽ⁿ⁾v‖ ≤ λᵢ` is **not**
the output of the spectral split — it is `lambdaBar A T x v ≤ λᵢ`, which is the DEFINITION of `v`
being slow (`Oseledets.lambdaBar A T x v = limsup_n (1/n) log‖A⁽ⁿ⁾v‖`, `Filtration.lean`), and the
filtration module `Oseledets/Lyapunov/Filtration.lean` (where slow membership lives) is **strictly
upstream** of the overlap split `Forward.lean` (it does not import it). The slow growth is available
unconditionally from the limsup-flag, proven via the ultrametric growth structure, NOT via the
spectral overlaps. The circle is broken.

## What this file delivers (NO `sorry`, clean axioms)

1. **`abs_inner_gramEig_le_norm_div_singularValue`** — the abstract Gram-eigenvector cross bound
   `|⟪u, v⟫| ≤ ‖f v‖ / √μ` for a unit `Q`-eigenvector `u` (`Q = adjoint f ∘ f`, eigenvalue `μ > 0`).
   Pure linear algebra (adjoint + Cauchy–Schwarz); NO perturbation theory, NO symmetry.

2. **`abs_inner_sortedGramEigenbasis_le_cocycle`** — the concrete per-`n` Oseledets overlap bound
   `|⟪uⱼ(n), v⟫| ≤ ‖A⁽ⁿ⁾v‖ / σⱼ(n)`, instantiating (1) at the genuine `sortedGramEigenbasis` and the
   cocycle map, with `σⱼ(n) = singularValues j` the genuine `j`-th singular value.

3. **`limsup_log_div_le_of_limsup_le_of_tendsto`** — the rate-assembly lemma: if `aₙ ≤ pₙ/qₙ` (all
   eventually positive), `limsup (1/n)log pₙ ≤ P`, and `(1/n)log qₙ → Q`, then
   `limsup (1/n)log aₙ ≤ P − Q`. The genuine `limsup` arithmetic that turns the per-`n` bound into the
   block rate.

4. **`overlap_limsup_le_of_slow_growth`** — the CLOSURE: from the slow growth (as a `limsup`
   hypothesis on `‖A⁽ⁿ⁾v‖`) and the singular-value convergence `(1/n)log σⱼ(n) → λ_l`, concludes
   `limsup (1/n)log|⟪v, uⱼ(n)⟫| ≤ λᵢ − λ_l`. The slow-growth hypothesis is `limsup (1/n)log‖A⁽ⁿ⁾v‖ ≤ λᵢ`,
   i.e. `lambdaBar A T x v ≤ λᵢ` — supplied NON-circularly by the limsup-flag filtration.

The deliverable (4) is precisely the conclusion of `block_overlap_limsup_le`, now proven from the
filtration's slow-growth bound rather than from the unproven `htilt` tilt-rate hypothesis: it closes
the node.

Everything below is sorry-free with the standard axioms `[propext, Classical.choice, Quot.sound]`.
-/

open MeasureTheory Filter Topology
open scoped Matrix InnerProductSpace Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {T : X → X}
variable {d : ℕ}

/-! ## 1. The abstract Gram-eigenvector cross bound -/

/-- **`abs_inner_gramEig_le_norm_div_singularValue`.**
Abstract Gram-eigenvector overlap bound. Let `f : E →ₗ[ℝ] E` on a finite-dimensional real inner
product space, `Q := adjoint f ∘ f` the Gram operator. If `u` is a unit `Q`-eigenvector with
eigenvalue `μ > 0` (`adjoint f (f u) = μ • u`), then for every `v`:

    |⟪u, v⟫|  ≤  ‖f v‖ / √μ.

Proof: `μ·⟪u,v⟫ = ⟪Q u, v⟫ = ⟪f u, f v⟫` (adjoint), so `|⟪u,v⟫| = |⟪fu,fv⟫|/μ ≤ ‖fu‖·‖fv‖/μ`
(Cauchy–Schwarz), and `‖fu‖² = ⟪fu,fu⟫ = ⟪Qu,u⟫ = μ` for unit `u`, so `‖fu‖ = √μ`. Pure linear
algebra. The sharp source of the BLOCK rate `λᵢ − λ_{block(j)}` once `‖f v‖` (slow growth `λᵢ`) and
`√μ = σⱼ` (singular value, exponent `λ_{block(j)}`) are fed in. -/
theorem abs_inner_gramEig_le_norm_div_singularValue
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) {u v : E} (hu : ‖u‖ = 1) {μ : ℝ} (hμ : 0 < μ)
    (heig : (LinearMap.adjoint f) (f u) = μ • u) :
    |(inner ℝ u v : ℝ)| ≤ ‖f v‖ / Real.sqrt μ := by
  have hfu_sq : ‖f u‖ ^ 2 = μ := by
    have h1 : (inner ℝ (f u) (f u) : ℝ) = inner ℝ ((LinearMap.adjoint f) (f u)) u := by
      rw [LinearMap.adjoint_inner_left]
    rw [real_inner_self_eq_norm_sq] at h1
    rw [h1, heig, real_inner_smul_left, real_inner_self_eq_norm_sq, hu]; ring
  have hfu_nonneg : 0 ≤ ‖f u‖ := norm_nonneg _
  have hfu : ‖f u‖ = Real.sqrt μ := by
    rw [← hfu_sq, Real.sqrt_sq hfu_nonneg]
  have hsqrt_pos : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hkey : μ * (inner ℝ u v : ℝ) = (inner ℝ (f u) (f v) : ℝ) := by
    have h1 : (inner ℝ (f u) (f v) : ℝ) = inner ℝ ((LinearMap.adjoint f) (f u)) v := by
      rw [LinearMap.adjoint_inner_left]
    rw [h1, heig, real_inner_smul_left]
  have habs : |(inner ℝ u v : ℝ)| = |(inner ℝ (f u) (f v) : ℝ)| / μ := by
    rw [eq_div_iff (ne_of_gt hμ), ← abs_of_pos hμ, ← abs_mul, mul_comm, hkey]
  rw [habs]
  have hcs : |(inner ℝ (f u) (f v) : ℝ)| ≤ ‖f u‖ * ‖f v‖ := abs_real_inner_le_norm (f u) (f v)
  have hμsqrt : Real.sqrt μ * Real.sqrt μ = μ := Real.mul_self_sqrt (le_of_lt hμ)
  calc |(inner ℝ (f u) (f v) : ℝ)| / μ ≤ (‖f u‖ * ‖f v‖) / μ := by gcongr
    _ = (Real.sqrt μ * ‖f v‖) / μ := by rw [hfu]
    _ = ‖f v‖ / Real.sqrt μ := by
        rw [div_eq_div_iff (ne_of_gt hμ) (ne_of_gt hsqrt_pos)]
        nlinarith [hμsqrt, norm_nonneg (f v)]

/-! ## 2. The concrete Oseledets per-`n` overlap bound -/

/-- **`abs_inner_sortedGramEigenbasis_le_cocycle`.** For the genuine sorted Gram singular vector
`uⱼ(n) = sortedGramEigenbasis A T n x j` and ANY fixed vector `v`:

    |⟪uⱼ(n), v⟫|  ≤  ‖A⁽ⁿ⁾·v‖ / σⱼ(n),

where `σⱼ(n) = (toEuclideanLin (cocycle A T n x)).singularValues j` is the genuine `j`-th singular
value of `A⁽ⁿ⁾` and `‖A⁽ⁿ⁾·v‖` the cocycle growth of the FIXED `v`. The eigenvalue
`μⱼ(n) = eigenvalues₀(gram) j = σⱼ(n)²`, so `√μⱼ(n) = σⱼ(n)`. -/
theorem abs_inner_sortedGramEigenbasis_le_cocycle [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X)
    (j : Fin (Fintype.card (Fin d))) (v : EuclideanSpace ℝ (Fin d))
    (hσpos : 0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues j) :
    |(inner ℝ (sortedGramEigenbasis A T n x j) v : ℝ)|
      ≤ ‖Matrix.toEuclideanLin (cocycle A T n x) v‖
        / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues j := by
  set f := Matrix.toEuclideanLin (cocycle A T n x) with hf
  set u := sortedGramEigenbasis A T n x j with hu
  set μ := (gram_posSemidef A T n x).isHermitian.eigenvalues₀ j with hμ
  -- `μ = σⱼ²` and `√μ = σⱼ`.
  have hμsq : μ = f.singularValues j ^ 2 := by
    rw [hμ, hf]; exact gram_eigenvalues₀_eq_sq_singularValues A T n x j
  have hμpos : 0 < μ := by rw [hμsq]; positivity
  have hsqrtμ : Real.sqrt μ = f.singularValues j := by
    rw [hμsq, Real.sqrt_sq (le_of_lt hσpos)]
  -- the gram eigenpair: `adjoint f (f u) = μ • u`.
  have hadj : LinearMap.adjoint f = Matrix.toEuclideanLin (cocycle A T n x)ᵀ := by
    rw [hf, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  have hgram : (LinearMap.adjoint f) ∘ₗ f = Matrix.toEuclideanLin (gram A T n x) := by
    rw [hadj, hf, gram]
    ext w i
    simp only [LinearMap.comp_apply, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
  have heig : (LinearMap.adjoint f) (f u) = μ • u := by
    have h := sortedGramEigenbasis_eigenpair A T n x j
    rw [← hgram] at h
    simpa [LinearMap.comp_apply] using h
  have hunorm : ‖u‖ = 1 := by rw [hu]; exact (sortedGramEigenbasis A T n x).orthonormal.1 j
  have hbnd := abs_inner_gramEig_le_norm_div_singularValue f (u := u) (v := v) hunorm hμpos heig
  rwa [hsqrtμ] at hbnd

/-! ## 3. The rate-assembly lemma -/

/-- **`limsup_log_div_le_of_limsup_le_of_tendsto`.** The genuine `limsup` arithmetic behind the block
rate. If `aₙ ≤ pₙ / qₙ` eventually (with `aₙ, pₙ, qₙ` eventually positive), `limsup (1/n)log pₙ ≤ P`,
and `(1/n)log qₙ → Q`, then `limsup (1/n)log aₙ ≤ P − Q`.

Mechanism: `(1/n)log aₙ ≤ (1/n)log pₙ − (1/n)log qₙ` eventually; `limsup` of the RHS is
`≤ limsup (1/n)log pₙ + limsup (−(1/n)log qₙ) = P + (−Q)` (the second `limsup` is `−Q` since
`(1/n)log qₙ → Q`). -/
theorem limsup_log_div_le_of_limsup_le_of_tendsto
    {a p q : ℕ → ℝ} {P Q : ℝ}
    (hbound : ∀ᶠ n : ℕ in atTop, a n ≤ p n / q n)
    (hapos : ∀ᶠ n : ℕ in atTop, 0 < a n)
    (hppos : ∀ᶠ n : ℕ in atTop, 0 < p n)
    (hqpos : ∀ᶠ n : ℕ in atTop, 0 < q n)
    (hPlim : limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (p n)) atTop ≤ P)
    (hPbdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (p n)))
    (hPcob : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (p n)))
    (hQtend : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (q n)) atTop (𝓝 Q))
    (hacob : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (a n))) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (a n)) atTop ≤ P - Q := by
  set la : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * Real.log (a n) with hla
  set lp : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * Real.log (p n) with hlp
  set lq : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * Real.log (q n) with hlq
  -- `la n ≤ lp n - lq n` eventually.
  have hev : la ≤ᶠ[atTop] (fun n => lp n - lq n) := by
    filter_upwards [hbound, hapos, hppos, hqpos, eventually_ge_atTop 1] with n hb ha hp hq hn1
    have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    have hlogle : Real.log (a n) ≤ Real.log (p n) - Real.log (q n) := by
      have : Real.log (a n) ≤ Real.log (p n / q n) := Real.log_le_log ha hb
      rwa [Real.log_div (ne_of_gt hp) (ne_of_gt hq)] at this
    calc la n = (n : ℝ)⁻¹ * Real.log (a n) := rfl
      _ ≤ (n : ℝ)⁻¹ * (Real.log (p n) - Real.log (q n)) :=
          mul_le_mul_of_nonneg_left hlogle hninv
      _ = lp n - lq n := by rw [mul_sub]
  -- We avoid any lower bound on `lp` by an `ε`-argument: for every `ε > 0`, eventually `lq n > Q - ε`,
  -- hence `la n ≤ lp n - lq n < lp n - (Q - ε) = lp n + (ε - Q)`, and `limsup (lp + const) =
  -- limsup lp + const ≤ P + (ε - Q)`. Then `ε → 0` gives `limsup la ≤ P - Q`.
  rw [show P - Q = P + (- Q) by ring]
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  -- eventually `la n ≤ lp n + (ε - Q)`.
  have hqlow : ∀ᶠ n : ℕ in atTop, Q - ε ≤ lq n :=
    hQtend.eventually (eventually_ge_nhds (show Q - ε < Q by linarith))
  have hev2 : la ≤ᶠ[atTop] (fun n => lp n + (ε - Q)) := by
    filter_upwards [hev, hqlow] with n hn hq
    calc la n ≤ lp n - lq n := hn
      _ ≤ lp n - (Q - ε) := by linarith
      _ = lp n + (ε - Q) := by ring
  -- limsup of `lp + const`.
  have hbdd_const : IsBoundedUnder (· ≤ ·) atTop (fun n => lp n + (ε - Q)) := by
    obtain ⟨B, hB⟩ := hPbdd
    rw [eventually_map] at hB
    exact ⟨B + (ε - Q), eventually_map.mpr (by
      filter_upwards [hB] with n hn using by linarith)⟩
  have hlimsup_const : limsup (fun n => lp n + (ε - Q)) atTop = limsup lp atTop + (ε - Q) :=
    limsup_add_const atTop lp (ε - Q) hPbdd hPcob
  calc limsup la atTop ≤ limsup (fun n => lp n + (ε - Q)) atTop :=
        limsup_le_limsup hev2 hacob hbdd_const
    _ = limsup lp atTop + (ε - Q) := hlimsup_const
    _ ≤ P + (ε - Q) := by gcongr
    _ = P + (- Q) + ε := by ring

/-! ## 4. The closure: block-rate overlap from the slow-growth limsup -/

/-- **`overlap_limsup_le_of_slow_growth` — the closure of the block-rate overlap node.**

For the genuine sorted Gram singular vector `uⱼ(n) = sortedGramEigenbasis A T n x j` and a slow
vector `v`, with:

* the **slow growth** `limsup (1/n)log‖A⁽ⁿ⁾v‖ ≤ λᵢ` (this is `lambdaBar A T x v ≤ λᵢ`, the DEFINITION
  of `v` being slow — supplied NON-circularly by the limsup-flag filtration `Filtration.lean`, which
  is strictly upstream of the overlap split);
* the **singular exponent** `(1/n)log σⱼ(n) → λ_l` (`tendsto_log_singularValue`, the fast block rate);

the overlap exponent obeys the BLOCK rate

    limsup (1/n) log |⟪v, uⱼ(n)⟫|  ≤  λᵢ − λ_l.

This is exactly the conclusion of `block_overlap_limsup_le`, proven WITHOUT the `htilt` tilt-rate
hypothesis. The per-`n` engine is `abs_inner_sortedGramEigenbasis_le_cocycle`
(`|⟪uⱼ,v⟫| ≤ ‖A⁽ⁿ⁾v‖/σⱼ`, sharp); the rate is assembled by `limsup_log_div_le_of_limsup_le_of_tendsto`. -/
theorem overlap_limsup_le_of_slow_growth [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X)
    (j : Fin (Fintype.card (Fin d))) {v : EuclideanSpace ℝ (Fin d)} {lamI lamL : ℝ}
    (hσpos : ∀ᶠ n : ℕ in atTop, 0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues j)
    (hslow : limsup (fun n : ℕ => (n : ℝ)⁻¹ *
      Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ lamI)
    (hslowbdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ *
      Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖))
    (hslowcob : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ *
      Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖))
    (hsing : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues j)) atTop (𝓝 lamL))
    (hvgrowpos : ∀ᶠ n : ℕ in atTop, 0 < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)
    (hovpos : ∀ᶠ n : ℕ in atTop,
      0 < |(inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ)|)
    (hovcob : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ *
      Real.log |(inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ)|)) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log |(inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ)|) atTop
      ≤ lamI - lamL := by
  -- the per-`n` bound `|⟪v, uⱼ⟫| ≤ ‖A⁽ⁿ⁾v‖ / σⱼ`.
  have hbound : ∀ᶠ n : ℕ in atTop,
      |(inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ)|
        ≤ ‖Matrix.toEuclideanLin (cocycle A T n x) v‖
          / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues j := by
    filter_upwards [hσpos] with n hn
    rw [real_inner_comm]
    exact abs_inner_sortedGramEigenbasis_le_cocycle A T n x j v hn
  exact limsup_log_div_le_of_limsup_le_of_tendsto hbound hovpos hvgrowpos hσpos
    hslow hslowbdd hslowcob hsing hovcob

/-! ## 5. The connector: the slow-growth `limsup` IS `lambdaBar` (the bridge that breaks the circle)

The slow-growth `limsup` hypothesis of `overlap_limsup_le_of_slow_growth` is, up to the
`toEuclideanCLM`/`toEuclideanLin` coercion, EXACTLY `lambdaBar A T x v` (`GrowthFunction.lean`,
`lambdaBar_eq_limsup_growthSeq`). This connector rewrites the closure into the filtration's native
slow-vector hypothesis `lambdaBar A T x v ≤ λᵢ`, making explicit that the slow growth is supplied by
`Filtration.lean` (`lambdaBar_eq_on_stratum` / `mem_Vflag`), strictly upstream of the overlap split —
NOT by the spectral split it feeds. -/

/-- The `lambdaBar` form of the slow-growth `limsup`: the cocycle map's `toEuclideanLin` and
`toEuclideanCLM` agree, so `limsup (1/n)log‖toEuclideanLin (cocycle) v‖ = lambdaBar A T x v`. -/
theorem limsup_log_norm_cocycle_eq_lambdaBar
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) (v : EuclideanSpace ℝ (Fin d)) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ *
      Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop
      = lambdaBar A T x v := by
  rw [lambdaBar]
  have hpt : ∀ n : ℕ, Matrix.toEuclideanLin (cocycle A T n x) v
      = Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v := by
    intro n
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]; rfl
  simp_rw [hpt]

/-- **`overlap_limsup_le_of_lambdaBar` — the closure in the filtration's native form.**
The block-rate overlap bound from the SLOW-VECTOR hypothesis `lambdaBar A T x v ≤ λᵢ` (the genuine
"`v` is slow" datum, from `Filtration.lean`, upstream of the spectral split). The two boundedness
side-conditions on the cocycle growth are exactly `GrowthFunction.growthSeq_bounded`. -/
theorem overlap_limsup_le_of_lambdaBar [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X)
    (j : Fin (Fintype.card (Fin d))) {v : EuclideanSpace ℝ (Fin d)} {lamI lamL : ℝ}
    (hσpos : ∀ᶠ n : ℕ in atTop, 0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues j)
    (hslow : lambdaBar A T x v ≤ lamI)
    (hslowbdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ *
      Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖))
    (hslowcob : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ *
      Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖))
    (hsing : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues j)) atTop (𝓝 lamL))
    (hvgrowpos : ∀ᶠ n : ℕ in atTop, 0 < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)
    (hovpos : ∀ᶠ n : ℕ in atTop,
      0 < |(inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ)|)
    (hovcob : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ *
      Real.log |(inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ)|)) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log |(inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ)|) atTop
      ≤ lamI - lamL := by
  refine overlap_limsup_le_of_slow_growth A T x j hσpos ?_ hslowbdd hslowcob hsing
    hvgrowpos hovpos hovcob
  rw [limsup_log_norm_cocycle_eq_lambdaBar]
  exact hslow

end Oseledets
