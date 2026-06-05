# Target theorem and milestone ladder — Oseledets MET

Companion to `understanding.md`. Recommends the concrete theorem to formalize, the
proof route, the ordered milestone ladder from Mathlib's current API to the target,
the key risks, and the Mathlib gaps that must be built. Mathlib status claims are
spot-verified against the pinned source under `.lake/packages/mathlib/Mathlib`
(toolchain `v4.30.0-rc2`).

---

## (a) Recommended target theorem

**The one-sided Oseledets MET in filtration form, for a real matrix cocycle over an
ergodic measure-preserving system.** This is the faithful *core* of the Oseledets
theorem: it produces the genuine Lyapunov exponents `λ₁ > ⋯ > λ_k` and the
`T`-equivariant measurable Oseledets filtration, with the honest forward limit
`(1/n) log‖A⁽ⁿ⁾v‖ → λᵢ` on each stratum. It is unmistakably "the Oseledets theorem"
(not a triviality), yet it avoids the parts (invertibility, backward cocycle,
splitting) that add the most work without changing the essential content.

### Informal statement

> Let `(X,μ)` be a probability space, `T : X → X` ergodic measure-preserving, and
> `A : X → GL(d,ℝ)` measurable with `log⁺‖A‖, log⁺‖A⁻¹‖ ∈ L¹(μ)`. Then there are
> reals `λ₁ > ⋯ > λ_k` and, for `μ`-a.e. `x`, a strictly decreasing flag of
> subspaces `ℝᵈ = V¹ₓ ⊋ ⋯ ⊋ V_kₓ ⊋ {0}`, depending measurably on `x` and
> `A`-equivariant (`A(x)·Vⁱₓ = Vⁱ_{Tx}`), such that for all `v ∈ Vⁱₓ ∖ V^{i+1}ₓ`,
> `lim_{n→∞} (1/n) log‖A⁽ⁿ⁾(x)·v‖ = λᵢ`.

### Lean 4 signature sketch (real types; not yet type-checked)

> **Superseded by the implemented statement.** The sketch below uses `Fin d → ℝ`,
> `Matrix.toLin'`, and `*ᵥ` (which carry the L∞/sup norm). The actual formalized target
> `Oseledets.oseledets_filtration` (in `Oseledets/MultiplicativeErgodic.lean`) instead
> uses `EuclideanSpace ℝ (Fin d)` with the matrix action `Matrix.toEuclideanCLM` and the
> **L2** operator norm — so that the operator norm is submultiplicative and the
> spectral/singular-value API applies (see `docs/plan/api-notes.md`). The Lyapunov
> exponents are norm-independent, so the two are mathematically equivalent; the
> `EuclideanSpace` framing is the one that compiles and is used downstream.

```lean
open scoped Matrix.Norms.L2Operator  -- fix the L2 operator norm on Matrix

variable {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
  [MeasureTheory.IsProbabilityMeasure μ]
variable {d : ℕ} {T : X → X}

/-- Iterated cocycle: `cocycle A T n x = A (T^[n-1] x) * ⋯ * A x`. -/
noncomputable def cocycle (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) :
    ℕ → X → Matrix (Fin d) (Fin d) ℝ
  | 0,     _ => 1
  | (n+1), x => cocycle A T n (T x) * A x   -- newest factor on the left

theorem oseledets_filtration
    (hT : Ergodic T μ)
    (A : X → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).det ≠ 0)                       -- A x ∈ GL(d, ℝ)
    (hAmeas : Measurable A)
    (hint  : MeasureTheory.Integrable (fun x => Real.posLog ‖A x‖) μ)
    (hint' : MeasureTheory.Integrable (fun x => Real.posLog ‖(A x)⁻¹‖) μ) :
    ∃ (k : ℕ) (lam : Fin k → ℝ)            -- distinct Lyapunov exponents, descending
      (V : Fin (k+1) → X → Submodule ℝ (Fin d → ℝ)),
      StrictAnti lam ∧
      (∀ᵐ x ∂μ,
        -- a flag  ⊤ = V 0 ⊋ V 1 ⊋ ⋯ ⊋ V k = ⊥
        V 0 x = ⊤ ∧ V (Fin.last k) x = ⊥ ∧
        (∀ i : Fin k, V i.succ x < V i.castSucc x) ∧
        -- A-equivariance of each level
        (∀ i, (V i x).map (Matrix.toLin' (A x)) = V i (T x)) ∧
        -- genuine exponential growth on each stratum
        (∀ i : Fin k, ∀ v ∈ (V i.castSucc x : Set (Fin d → ℝ)),
            v ∉ V i.succ x →
            Filter.Tendsto
              (fun n => (n : ℝ)⁻¹ * Real.log ‖cocycle A T n x *ᵥ v‖)
              Filter.atTop (nhds (lam i)))) ∧
      -- measurability of the level maps
      (∀ i, Measurable (fun x => V i x))
```

(The exact packaging — `Submodule` vs `Flag`, `Fin k`-indexing, how measurability
of subspace-valued maps is phrased — is to be pinned in `Oseledets/` and is itself
part of milestone work; the sketch shows the real types and the load-bearing
conclusions. Note `‖A x‖` uses the scoped L2 operator norm; `*ᵥ` is matrix–vector
product; `Matrix.toLin'` gives the linear map for equivariance.)

### Rationale (mergeable, provable, faithful)

- **Faithful.** It is the genuine one-sided Oseledets/Furstenberg–Oseledets theorem
  (Filip Thm 2.2.6, Bochi Thm 2, Zhu Thm 5.1): all distinct exponents, the
  equivariant measurable filtration, and the *honest* limit (not merely limsup) on
  each layer. Furstenberg–Kesten (top/bottom only) would be too weak to be called
  "Oseledets"; the splitting is a strict refinement we defer.
- **Provable on current Mathlib + the planned builds.** It needs only the one-sided
  hypotheses and avoids inverting `T`. Its entire dependency chain (pointwise
  Birkhoff → Kingman → Furstenberg–Kesten → limsup flag → limsup→lim induction) is
  classical, self-contained, and rests on Mathlib substrate that demonstrably
  exists (measure-preserving/ergodic API, condExp, Fekete, `posLog`, L2 matrix norm,
  singular values, spectral theorem). No NPC geometry, no symmetric spaces.
- **Mergeable into Mathlib.** The intermediate results (pointwise Birkhoff, Kingman,
  Furstenberg–Kesten) are individually high-value, long-requested Mathlib targets
  with clean statements; building them in Mathlib style makes the whole stack
  upstreamable. The statement uses standard Mathlib idioms (`Ergodic`, `Integrable`,
  `Submodule`, `Filter.Tendsto`, `posLog`, scoped matrix norm).
- **Right scope.** Large enough to be the real theorem, small enough to have a
  credible sorry-free path. The two-sided splitting, exterior-power multiplicities,
  and non-ergodic decomposition are listed as future milestones, not the target.

---

## (b) Proof route (and why)

**Route B — classical: pointwise Birkhoff → Kingman → Furstenberg–Kesten →
induction-on-dimension peeling.** Chosen because it has the lightest *credible*
dependency footprint given what Mathlib actually has:

- Both candidate routes (B and Filip's induction-on-the-projective-bundle, "Route
  A") require building the **pointwise Birkhoff ergodic theorem**, which is absent
  (only the mean/von Neumann theorem exists). So that cost is unavoidable and shared.
- Route A's distinctive machinery — *fibered* Krylov–Bogoliubov + Krein–Milman +
  extreme-point-ergodicity + measurable subbundles, on the projective bundle with a
  custom weak-* topology — is a bespoke functional-analysis gadget with essentially
  nothing packaged in Mathlib.
- Route B's distinctive dependency, **Kingman**, has a single classical proof
  (Steele 1989) resting on *only* pointwise Birkhoff + elementary partition
  combinatorics, is independently valuable/upstreamable, and yields
  Furstenberg–Kesten (the clean first milestone) almost immediately.
- We use exterior powers / singular values / spectral theorem only where Mathlib
  already supports them (to identify multiplicities and as the two-sided cross-check),
  **not** as the existence engine — so we avoid building the complete
  Grassmannian-with-`|sinθ|`-metric and the eigenspace-Cauchy estimate that the pure
  Ruelle route would demand.

Reject Karlsson–Margulis (NPC geometry) and Filip's geometric/Noncommutative route
(symmetric spaces, Kaimanovich regularity): both require building large theories
with little reuse for a single theorem.

---

## (c) Alternative target framings considered, and why rejected

1. **Full two-sided Oseledets splitting `ℝᵈ = ⊕ Eⁱ` (invertible `T`, two-sided
   limit, angle decay).** *The "complete" theorem.* **Rejected as the initial
   target:** strictly larger — it requires the inverse cocycle, the backward
   filtration, and subexponential-angle-decay estimates *on top of* the entire
   one-sided proof. It reuses the one-sided theorem as a black box, so it is the
   natural *next* milestone, not the first. Listed in §(d) and as Layer 7 of
   `understanding.md`.

2. **Furstenberg–Kesten only (top and bottom Lyapunov exponents, no subspaces).**
   `lim (1/n) log‖A⁽ⁿ⁾‖ = λ₁` a.e. **Rejected as the target (kept as a milestone):**
   it is a genuine, valuable theorem and the cleanest first real result, but it is
   *not* "the Oseledets theorem" — it resolves only the two extremal exponents and
   provides no filtration/spectrum. It is milestone M5 below, the proof of concept,
   not the deliverable.

3. **Classical singular-value form `Λ(x) = lim (A⁽ⁿ⁾*A⁽ⁿ⁾)^{1/2n}` (Ruelle/Oseledets
   original), exponents = log-eigenvalues of `Λ`.** **Rejected as the target:** it
   front-loads the hardest analysis Mathlib does not yet support — convergence of
   `(A⁽ⁿ⁾*A⁽ⁿ⁾)^{1/2n}` in operator norm, a full ordered SVD, and the
   eigenspace-Cauchy/Grassmannian-completeness estimate. The eigenspaces of `Λ` are
   moreover *not* the equivariant Oseledets subspaces, so this form is less directly
   "the" theorem. Useful as a conceptual cross-check, not the primary statement.

4. **(Considered, rejected immediately) `GL(d,ℝ)`-cocycle phrased via
   `ContinuousLinearMap`/abstract bundle instead of `Matrix (Fin d) (Fin d) ℝ`.**
   The `LinearMap`/inner-product-space framing has the richest singular-value API,
   but `Matrix (Fin d) (Fin d) ℝ` is the most concrete, measurable-by-default
   (`Matrix m n α ≃ m → n → α`, Pi Borel structure), Mathlib-idiomatic, and
   matches the digests' uniform `A : X → GL(d,ℝ)` framing. We use the matrix
   framing for the statement and bridge to `LinearMap`/`EuclideanSpace` internally
   where the spectral API is needed.

---

## (d) Milestone ladder (ordered; each strictly builds on the previous)

Status: **exists-in-mathlib** (reuse) or **to-build**. IDs match
`milestone_ladder` in the structured output and the Lx labels in `understanding.md`.

| ID | Milestone | Status | Depends on |
|---|---|---|---|
| **M0** | Substrate: `Ergodic`/`MeasurePreserving`, `condExp` + `invariants`, `birkhoffSum`, Fekete `Subadditive.tendsto_lim`, `Real.posLog`, `Matrix.l2_opNorm_mul`, `GL`/`det`, `LinearMap.singularValues`, spectral theorem, `CFC.sqrt`, `exteriorPower.map`, `Flag` | **exists** | — |
| **M1** | Maximal ergodic inequality (Hopf/Garsia) | **to-build** | M0 |
| **M2** | `condExp` commutes with measure-preserving composition: `μ[g∘T \| invariants T] =ᵐ μ[g\|invariants T]∘T` | **to-build** | M0 |
| **M3** | **Pointwise (Birkhoff) ergodic theorem**: a.e. convergence of `birkhoffAverage` to `condExp` onto `invariants T`; constant under `Ergodic` | **to-build** | M1, M2 |
| **M4** | Subadditive-cocycle machinery + **Kingman subadditive ergodic theorem** (Steele proof: partition lemma, reduce-to-nonpositive, invariance, greedy covering) | **to-build** | M3, Fekete (M0) |
| **M5** | Linear-cocycle infrastructure (`cocycle`, identity, integrability predicate, measurability) + **Furstenberg–Kesten** top & bottom exponents | **to-build** | M4, M0 |
| **M6** | limsup growth function `λ̄(x,v)`: finiteness, ultrametric algebra (≤ d values), the **limsup flag** `Vⁱ = {v : λ̄ ≤ λᵢ}` + equivariance | **to-build** | M5 |
| **M7** | Measurability of `k`, `λᵢ`, `x ↦ Vⁱₓ` (measurable-subspace / selection layer) | **to-build** | M6 |
| **M8** | Tempering corollary of Birkhoff (`(1/n)φ(Tⁿx)→0`) + extremes-on-a-subbundle-are-limits (Bochi L11) | **to-build** | M3, M5, M6 |
| **M9** | Tempered block-triangular estimate + peel-one-exponent + induction ⇒ genuine forward `lim` on each stratum (limsup→lim) | **to-build** | M8 |
| **M10** | **TARGET: one-sided MET (filtration)** — assemble flag (M6) + measurability (M7) + genuine limit (M9) | **to-build** | M6, M7, M9 |
| **M11** | *(future)* Exterior-power exponent calculus: `‖⋀ᵏA‖ = ∏σᵢ`, multiplicities and full Lyapunov spectrum (inner product/norm on `⋀ᵏ`) | **to-build** | M5, M10, M0 |
| **M12** | *(future)* **Two-sided Oseledets splitting**: backward filtration (`T⁻¹`), subexponential angle decay, intersect ⇒ `⊕Eⁱ` with two-sided limit | **to-build** | M10 |
| **M13** | *(future)* Non-ergodic version via ergodic decomposition (exponents as `T`-invariant functions) | **to-build** | M10 |

**M5 is the recommended proof-of-concept checkpoint** (Furstenberg–Kesten end to
end), **M10 is the target deliverable**, M11–M13 are the faithful generalizations.

---

## (e) Key risks and concrete Mathlib gaps to build

### The two large, gating sub-projects

- **GAP — Pointwise Birkhoff ergodic theorem (M3) is ABSENT.** Verified: only the
  *mean* von Neumann theorem exists
  (`Mathlib/Analysis/InnerProductSpace/MeanErgodic.lean`), and the **maximal ergodic
  inequality / Hopf / Garsia lemma is ABSENT** (zero hits) — that is its usual gate.
  This is on the critical path for *every* route and must be built first (M1→M3).
  This is the foundational risk: if it is harder than estimated, everything slips.
  Mitigation: it is a well-understood classical result; the conditional-expectation
  substrate it needs (`condExp`, tower, `setIntegral_condExp`, `invariants`) all
  exists.

- **GAP — Kingman subadditive ergodic theorem (M4) is ABSENT.** Only Fekete's
  deterministic `Subadditive.tendsto_lim` (over `ℝ`, needs `BddBelow`) exists. This
  is the analytic engine of the MET. Largest single build after Birkhoff. **Highest
  technical risk: the greedy-covering length bound (Steele Step 4 / L2.5)** — fiddly
  consecutive-block partition index-bookkeeping; expect it to dominate the Kingman
  effort.

### Concrete smaller gaps that must be built

- **GAP — `condExp` vs measure-preserving composition (M2) is ABSENT.** No lemma
  `μ[g∘T | invariants T] =ᵐ μ[g | invariants T]∘T`. (`ContinuousLinearMap.comp_condExp_comm`
  exists but is unrelated.) Build from `setIntegral_condExp` + `MeasurePreserving`.
- **GAP — measurable structure on subspaces / flags (M7).** `Flag`
  (`LinearAlgebra/Basis/Flag.lean`) and `Module.Grassmannian`
  (`RingTheory/Grassmannian.lean`, AG quotient convention) exist but carry **no
  Borel/measurable structure**, and measurable selection of subspace-valued maps is
  not packaged. Must build a measurable-subspace layer (subspace ↦ orthogonal
  projection / Grassmannian metric; measurable orthonormal frames via
  `gramSchmidt`). Moderate infrastructure risk; pervasive (used in M6, M7, M8).
- **GAP — Furstenberg–Kesten, Lyapunov exponents, the cocycle notion, Oseledets**
  (M5, M6, M10): ABSENT entirely (zero hits). The whole MET-specific vocabulary is
  new and must be defined (cocycle `A⁽ⁿ⁾`, integrability predicate, `λ̄`, exponents,
  filtration). Low math risk, real engineering volume.
- **GAP (future) — inner product / norm on exterior powers (M11).** `exteriorPower`
  is purely algebraic; **zero references in `Analysis/`/`Topology/`**. The
  Gram-determinant inner product, the `NormedAddCommGroup`/`InnerProductSpace`
  instance on `⋀ᵏE`, and `‖⋀ᵏA‖ = ∏σᵢ` must be built. Only needed for multiplicities
  (M11), not for the target M10.
- **GAP (future) — ordered matrix SVD / polar decomposition.** `LinearMap.singularValues`
  + `CFC.sqrt` + `IsHermitian.eigenvalues` exist; a named `A = UΣVᴴ` and a
  matrix-level `Matrix.singularValues` with `‖A‖ = σ₀` do not. Largely bypassable by
  working with `√(AᵀA)` directly.

### Statement/convention risks (decide once, early)

- **EReal vs ℝ and `−∞`.** Kingman's limit and `λ̄` can be `−∞`. Decide at M4 whether
  to work in `EReal` throughout or carry the `inf_n (1/n)∫gₙ > −∞` proviso to stay in
  `ℝ`. Under our `log⁺‖A⁻¹‖ ∈ L¹` hypothesis the bottom exponent is finite, so `ℝ`
  with the proviso is viable for the target — but Kingman itself, to be Mathlib-worthy
  and reusable, should be stated in `EReal`. This choice propagates through every
  statement; fix it before M4.
- **Conventions to pin once (per the digests):** decreasing `λ₁ > ⋯ > λ_k`; flag
  inclusion direction (`V¹ ⊋ ⋯ ⊋ V_k`); cocycle factor order (newest on the left,
  `A⁽ⁿ⁾(x) = A(Tⁿ⁻¹x)⋯A(x)` — matches `birkhoffSum`'s `f^[k]` indexing); `log⁺`
  meaning (`max(0, log)`, = `Real.posLog`); co-norm `m(L) = ‖L⁻¹‖⁻¹` for the bottom
  exponent.
- **Norm choice.** `Matrix` norm instances are *scoped*, not default. Fix the L2
  operator norm project-wide (`open scoped Matrix.Norms.L2Operator`) to get
  submultiplicativity (`l2_opNorm_mul`) and the C*-identity, and avoid instance
  clashes with the entrywise sup norm.
- **`GL` encoding.** Encode `A x ∈ GL(d,ℝ)` as `(A x).det ≠ 0` on `Matrix (Fin d)
  (Fin d) ℝ` rather than `GL (Fin d) ℝ`, to keep `A` a plain matrix-valued
  measurable function and reuse the L2 norm directly; provide a bridge to
  `Matrix.GeneralLinearGroup` where group structure is needed (inverse cocycle).
