# Oseledets L7c — de-risking scout: route decision + sub-lemma ladder

> Bounded scouting pass, 2026-06-07. De-risks **L7c**, the single irreducible hard node of the MET
> formalization: a.e. convergence of the self-adjoint matrix sequence `qpow A T n x = (Qₙ)^{1/(2n)}`
> (eigenvalues already converge by the committed `eigenvalues_qpow_tendsto`; the content is that the
> eigenSPACES / block spectral projectors converge, pinned by the growing spectral gaps). NOT an
> implementation; produces a verified route decision and a risk-tagged ladder. Compiled probes
> (all `lake env lean`, repo root): `scratch_l7c_cx_instances.lean` (compiled, reports expected
> synth failures), `scratch_l7c_projector.lean` (compiled, exit 0), `scratch_l7c_cstar_check.lean`
> (blocked by a missing cache `.olean`, source-confirmed only) — this scout — plus the pre-existing
> `scratch_l7_*.lean`.
> Refines `oseledets-l7-crux.md` §B.1/§C/§E. Corrects two stale claims (see §F surprises). Does not
> modify committed library files.

## A. Recommended route — VERDICT

**Route 1 (direct relative-gap projector-Cauchy bound, on PLAIN real matrices), built from scratch.**

The crux is to prove, for `μ`-a.e. `x`, that `qpow A T n x` is a Cauchy sequence in the
finite-dimensional matrix metric, hence converges (the committed `L7_statement`). The mechanism:

1. Group eigenvalue indices by **distinct** limit exponents `e^{λ₁} > … > e^{λ_p}` (the committed
   `specList`/`specCard` enumerate distinct exponents descending). NEVER per singular-value index —
   see §F.
2. For each gap `j` (between distinct `λⱼ > λⱼ₊₁`) pick a threshold `cⱼ` strictly between `e^{λⱼ}`
   and `e^{λⱼ₊₁}`. Let `Πₙ⁽ʲ⁾` be the orthogonal projector of `qpow_n` onto eigenvalues `> cⱼ`.
3. **The new infra (L7c):** `{Πₙ⁽ʲ⁾}ₙ` is Cauchy in operator norm, by a *relative-gap angle bound*
   on the top-`j` right-singular subspaces of consecutive iterates `Mₙ = A⁽ⁿ⁾`, `Mₙ₊₁ = A(Tⁿx)·Mₙ`.
4. `Matrix (Fin d) (Fin d) ℝ` is complete (`scratch_l7_cauchy.lean` D), so each `Πₙ⁽ʲ⁾ → P⁽ʲ⁾`;
   assemble `Λ := Σⱼ e^{λⱼ}·(P⁽ʲ⁾ − P⁽ʲ⁺¹⁾)` and show `qpow_n → Λ` from projector + eigenvalue limits.

**Why the projectors can be DEFINED with the bare real CFC (no isometric instance):** the cutoff
projector `Πₙ⁽ʲ⁾ = cfc χⱼ (qpow_n)` for a continuous cutoff `χⱼ` (1 above `cⱼ`, 0 below) equals, via
`cfc_congr` on the *finite* spectrum, the cfc of the exact 0/1 indicator — an idempotent self-adjoint
matrix = the orthogonal block projector. The bare `Matrix.IsHermitian.instContinuousFunctionalCalculus
ℝ` (FOUND) suffices for `cfc`, `cfc_congr`, `cfc_mul`, `cfc_predicate`; all of P1/P2/P3 below compiled
on PLAIN `Matrix _ _ ℝ` (`scratch_l7c_projector.lean`). The CFC explicit formula
`Matrix.IsHermitian.cfc f A = U · diag(f∘eigenvalues) · Uᴴ` makes the projector concrete.

### Why the other routes lose

- **Route 2 (continuous-cutoff CFC projector relying on continuity-in-operator / `Filter.Tendsto.cfc`):
  BLOCKED, and even its complexification escape is now refuted (§C, §F SURPRISE 1).** The
  operator-variable continuity lemmas (`continuousOn_cfc`, `Filter.Tendsto.cfc`,
  `lipschitzOnWith_cfc_fun`) live in the `RCLike` section and require
  `[IsometricContinuousFunctionalCalculus 𝕜 A IsSelfAdjoint]`, which needs `[CStarAlgebra A]`. This
  instance does NOT synthesize for plain `Matrix n n ℝ` (pinned, `scratch_l7_cfc_synth.lean`) **nor for
  `Matrix n n ℂ`** — `CStarAlgebra (Matrix n n ℂ)` FAILS to synthesize (compiled,
  `scratch_l7c_cx_instances.lean`). The proper `CStarAlgebra` lives only on the type-synonym wrapper
  `CStarMatrix n n ℂ` (Mathlib `CStarMatrix.lean:816`, `instCStarAlgebra`; isometric ℝ-CFC available
  there — `scratch_l7c_cstar_check.lean`). So Route 2 would require porting the entire committed
  `qpow`/`gram` construction off plain `Matrix ℝ` onto `CStarMatrix _ _ ℂ`, with real↔complex↔wrapper
  transfer lemmas — a major refactor. **And it would not even shrink the crux:** continuity-in-operator
  only TRANSFERS convergence; it cannot CREATE the convergence of `qpow_n` (it requires an
  already-convergent operator sequence as input). See §F SURPRISE 2.
- **Route 3 (Riesz/holomorphic contour projector `(1/2πi)∮(z−A)⁻¹dz`): REJECT.** Needs complexification
  (same wrapper problem) + contour integration of the resolvent over ℂ. Mathlib has `resolvent`/
  `resolventSet`/`isOpen_resolventSet` but no spectral-projection-by-contour, no `spectralProjection`,
  no Riesz functional calculus producing band projectors (grep: absent, §C). Heaviest route; the
  contour estimate is itself the same relative-gap content dressed in analytic machinery.
- **Route 4 (cheaper device): NONE found.** The projective-measure / growth-dichotomy proof (Filip
  notes Lemma 2.3.1; Chicago REU; = blueprint "Route I") avoids the matrix limit but needs the
  filtration measurable+equivariant first — relocating the dependency at comparable cost, and it does
  NOT discharge the committed `L7_statement` (which literally asserts `Tendsto (qpow…) (𝓝 (Λ x))`). A
  direct `qpow_n` Cauchy via "`‖log H_{n+1} − log H_n‖` summable" is FALSE (eigenvectors rotate; §F
  counterexample). No subadditive/monotone matrix trick yields `qpow_n` Cauchy without the gap content.

## B. Precise Lean statement(s) of the new infra to build (per distinct-λ)

The crux factors into one ABSTRACT self-adjoint lemma + one COCYCLE-specific gap input. State per
distinct exponent / per gap.

### B.1 The abstract gapped-projector-Cauchy lemma (the irreducible new infra)

```lean
open scoped Matrix.Norms.L2Operator in
/-- Abstract crux. A sequence of self-adjoint matrices whose spectrum splits, for `n` large, into a
top block `> c` and a bottom block `< c` with the projector increments summable, has a convergent
band projector. Stated for the cutoff CFC `Πₙ = cfc χ Hₙ` of a fixed continuous 0/1 cutoff `χ` at
`c`. -/
theorem cauchySeq_bandProjector
    {d : ℕ} (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (hH : ∀ n, IsSelfAdjoint (H n))
    (χ : ℝ → ℝ) (hχ : Continuous χ) (c : ℝ)
    -- eventually `c` lies in a spectral gap of `Hₙ`, with χ = the exact 0/1 indicator there:
    (hgap : ∀ᶠ n in atTop, (spectrum ℝ (H n)).EqOn χ (Set.indicator (Set.Ioi c) 1))
    -- the geometric (relative-gap) increment bound that makes the projectors Cauchy:
    (hsum : Summable (fun n => ‖cfc χ (H (n+1)) - cfc χ (H n)‖)) :
    CauchySeq (fun n => cfc χ (H n))
```
The real mathematical weight is `hsum`; this lemma is the *packaging* (Cauchy from summable
increments + completeness, via `cauchySeq_of_summable_dist` or `cauchySeq_finset` telescoping). LOW
once `hsum` is supplied.

### B.2 The relative-gap angle bound that DISCHARGES `hsum` (the genuine §3.3 content)

```lean
/-- The single-step angle bound. Let `Mₙ = A⁽ⁿ⁾x` and `Mₙ₊₁ = A(Tⁿx)·Mₙ`. The orthogonal projector
`Πₙ⁽ʲ⁾` onto the top-`j` right-singular subspace of `Mₙ` (= eigenspace of `Qₙ` for the top-`j`
eigenvalues) moves between `n` and `n+1` by at most the RELATIVE gap times the one-step distortion:
`‖Πₙ₊₁⁽ʲ⁾ − Πₙ⁽ʲ⁾‖ ≤ Cⱼ · ‖A(Tⁿx)‖ · ‖A(Tⁿx)⁻¹‖ · σⱼ₊₁(Mₙ)/σⱼ(Mₙ)`.
(`Cⱼ` an absolute constant; this is the multiplicative/relative Davis–Kahan sin-Θ bound for singular
subspaces under an invertible left perturbation.) -/
theorem norm_bandProjector_succ_sub_le
    {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (j : ℕ) (n : ℕ) (x : X) :
    ‖Πj A T (n+1) x - Πj A T n x‖
      ≤ Cj * ‖A (T^[n] x)‖ * ‖(A (T^[n] x))⁻¹‖
          * (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (j+1)
          / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues j
```
Combined with the committed scalar layer: `(1/n)·log(σⱼ₊₁/σⱼ) → λⱼ₊₁ − λⱼ < 0`
(`tendsto_log_singularValue`, two indices, distinct exponents) and the tempered one-step factor
`(1/n)·log(‖A(Tⁿx)‖‖A⁻¹‖) → 0` a.e. (Birkhoff / `IntegrableLogNorm`, already in the FK plumbing),
the RHS is eventually `≤ e^{−cn}`, hence `hsum` holds a.e. This is **the irreducible piece** and is
entirely absent from Mathlib (no Davis–Kahan, no sin-Θ, no singular-subspace perturbation; §C).

### B.3 Assembly (`L7c → L7d`)

```lean
/-- For a.e. `x`, `qpow A T n x` converges. -/
theorem cauchySeq_qpow {A} (hA : ∀ x, (A x).det ≠ 0) … :
    ∀ᵐ x ∂μ, CauchySeq (fun n => qpow A T n x)
-- assemble qpow_n = Σⱼ (eigenvalue on block j)·Πₙ⁽ʲ⁾ ; each Πₙ⁽ʲ⁾ Cauchy (B.1+B.2),
-- each block eigenvalue → e^{λⱼ} (committed eigenvalues_qpow_tendsto); products/sums of
-- Cauchy/convergent sequences are Cauchy.

theorem L7d {A} … : L7_statement μ T A   -- via cauchySeq_tendsto_of_complete (probe E)
```

## C. Mathlib API: found vs missing (independent verification, this scout)

**FOUND (compiled against, plain real matrices unless noted):**
- `Matrix.IsHermitian.instContinuousFunctionalCalculus ℝ (Matrix n n 𝕜) IsSelfAdjoint` — the BARE
  (non-isometric) CFC instance. Sufficient to DEFINE the projectors.
- `cfc_congr : (spectrum ℝ a).EqOn f g → cfc f a = cfc g a` (`…/Unital.lean:417`). Compiled, P1.
  This is the bridge continuous-cutoff → exact indicator on the finite matrix spectrum, and the same
  device the committed `measurable_cfc_eqOn_polynomial` uses.
- `cfc_mul`, `cfc_predicate` (idempotent + self-adjoint of the cutoff cfc = orthogonal projector).
  Compiled, P2a/P2b/P2c.
- `Matrix.IsHermitian.cfc` explicit triple-product formula `U · diag(f∘eigenvalues) · Uᴴ`
  (`HermitianFunctionalCalculus.lean:132`) + `cfc_eq`; `eigenvectorUnitary`, `spectral_theorem`,
  `eigenvalues₀`/`eigenvalues₀_antitone`, `spectrum_real_eq_range_eigenvalues` (`Matrix/Spectrum.lean`).
- `CompleteSpace (Matrix _ _ ℝ)`, `cauchySeq_tendsto_of_complete` (probes D/E). Compiled, P3.
- `Submodule.orthogonalProjection` (CLM), `orthogonalProjection_eq_sum_rankOne` (`PiL2.lean`) — to
  describe block projectors concretely if needed.
- `CStarAlgebra (CStarMatrix n n ℂ)` + isometric ℝ-CFC ON THE WRAPPER (`CStarMatrix.lean:816`) —
  available, but only for the wrapper type, not plain matrices (so not used by Route 1).
- Committed scalar layer: `tendsto_log_singularValue`, `sigma_le_opNorm`, `inv_opNorm_inv_le_sigma`,
  `singularValues_cocycle_pos`, `eigenvalues_qpow_tendsto`, `eigenvalues₀_qpow_eq`.

**MISSING (must be BUILT; upstreamable):**
- **M-2′ — singular-subspace / eigenprojection perturbation (Davis–Kahan / sin-Θ), RELATIVE form.**
  CONFIRMED ABSENT: no `davis`/`kahan`, no sin-Θ spectral object, no eigenvalue/eigenvector
  continuity, no subspace-angle-perturbation, no singular-subspace distance, no `spectralProjection`/
  Riesz contour projector (grep over all Mathlib). `Matrix/Gershgorin.lean` gives only eigenvalue
  *localization*, not projector perturbation. **This is the irreducible §3.3 gap = B.2.**
- **M-3 — the assembled gapped matrix-limit (`qpow_n → Λ`) = `cauchySeq_qpow` + `L7d`.** Absent;
  built from B.1+B.2.
- (Confirmed) **M-2 — operator-variable CFC continuity unusable on the committed type.** Both real and
  complex plain matrices lack `CStarAlgebra`/isometric CFC; only the `CStarMatrix` wrapper has it.

## D. Compiled micro-steps (this scout) vs UNVERIFIED

| Probe file | Claim | Status |
|---|---|---|
| `scratch_l7c_cx_instances.lean` | `CStarAlgebra (Matrix n n ℂ)` and isometric ℝ-CFC for `Matrix n n ℂ` FAIL to synthesize (SURPRISE 1) | **COMPILED — reports the two `synthInstanceFailed` (exit 1 expected; READ the output)** |
| `scratch_l7c_projector.lean` | P1 `cfc_congr`; P2a `cfc_predicate`; P2b `cfc_mul`; P2c idempotent cutoff ⇒ projector; P3 completeness — all on PLAIN `Matrix _ _ ℝ` (bare CFC) | **COMPILED (exit 0, only unused-var warnings)** |
| `scratch_l7c_cstar_check.lean` | The wrapper `CStarMatrix n n ℂ` has `CStarAlgebra` + isometric ℝ-CFC | **NOT compile-verified here** — `CStarMatrix.olean` absent from the local cache (no `lake exe cache get` per directive); claim is SOURCE-confirmed at `Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:816` (`instance instCStarAlgebra : CStarAlgebra (CStarMatrix n n A)`) but UNVERIFIED by compile |

**UNVERIFIED (asserted, not compiled — these ARE the L7c work):**
- B.2 the relative-gap single-step angle bound `norm_bandProjector_succ_sub_le`. No probe; this is the
  new theorem to prove. The numeric form of the constant `Cⱼ` and whether the bound is best stated via
  `‖Π‖`-difference vs `sin∠` is to be settled during implementation.
- B.1 `hsum`-from-scalar-layer (needs B.2 + the tempered one-step factor a.e.).
- B.3 assembly and `Λ` Hermitian-PD eigen-data.

## E. Risk-tagged sorry-free sub-lemma ladder (L7c → L7d)

Build inside `OseledetsLimit.lean` (or a new `OseledetsProjector.lean`). All on PLAIN
`Matrix (Fin d) (Fin d) ℝ`; bare CFC instance only.

| # | Lemma (abbrev.) | Risk | Effort | Notes |
|---|---|---|---|---|
| L7c.0 | `bandProjector A T j n x := cfc χⱼ (qpow_n)`; self-adjoint + idempotent on the good set (`cfc_predicate`,`cfc_mul`,`cfc_congr`) | **LOW (probe-backed)** | <0.5 sess | P1/P2 compiled |
| L7c.1 | `bandProjector = Πⱼ`(top-`j` eigenprojector of `Qₙ`): range/eigenvalue identification via explicit `IsHermitian.cfc` formula | MED | 1 sess | `eigenvectorUnitary`,`spectrum_real_eq_range_eigenvalues` |
| L7c.2 | one-step factor a.e.: `(1/n)·log(‖A(Tⁿx)‖‖A⁻¹‖) → 0` | LOW–MED | 0.5–1 sess | Birkhoff over `IntegrableLogNorm`; FK plumbing exists |
| L7c.3 | **relative-gap angle bound B.2 (`norm_bandProjector_succ_sub_le`)** | **HIGH (CRUX, NEW — M-2′)** | 4–8 sess | Davis–Kahan sin-Θ for singular subspaces, invertible-left perturbation; absent from Mathlib; the irreducible piece |
| L7c.4 | `hsum` a.e.: RHS of B.2 eventually `≤ e^{−cn}`, summable | MED | 1 sess | L7c.2 + L7c.3 + `tendsto_log_singularValue` (two indices) |
| L7c.5 | `cauchySeq_bandProjector` (B.1 packaging): Cauchy from summable increments + completeness | LOW–MED | 0.5–1 sess | `cauchySeq_of_summable_dist`/telescoping; probe D/E |
| L7d | `cauchySeq_qpow` ⇒ `L7_statement` (assemble blocks×eigenvalues; `cauchySeq_tendsto_of_complete`) | MED | 1–1.5 sess | needs L7c.1/4/5 + committed `eigenvalues_qpow_tendsto` |

**Critical path: L7c.3 → L7c.4 → L7c.5 → L7d.** The single irreducible new-infra node is **L7c.3**
(the relative-gap singular-subspace angle bound). Everything else is LOW/MED or probe-backed.
Net estimate for L7c→L7d: ~8–14 sessions, dominated by L7c.3.

## F. Counterexamples / pitfalls found

- **SURPRISE 1 (route-doc correction).** `oseledets-l7-crux.md` §F speculated the isometric ℝ-CFC fails
  for real matrices because of the "scoped L2 norm / missing real CStarAlgebra ℝ-structure". The
  sharper truth: the bundled **`CStarAlgebra` class is registered on NEITHER `Matrix n n ℝ` NOR
  `Matrix n n ℂ`** under the scoped L2 norm — only on the dedicated wrapper `CStarMatrix n n A`
  (`Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:816`). So complexification does NOT rescue Route 2
  on the committed type; one would have to refactor onto `CStarMatrix _ _ ℂ`. Compiled:
  `scratch_l7c_cx_instances.lean` (both fail), `scratch_l7c_cstar_check.lean` (wrapper succeeds).
- **SURPRISE 2 (architecture).** Even granting the isometric instance, `Filter.Tendsto.cfc` /
  `continuousOn_cfc` only TRANSFER convergence (input: a convergent operator sequence). They CANNOT
  produce the convergence of `qpow_n` — that is exactly the unknown. So no continuity-of-cfc lemma,
  however obtained, discharges the crux; the from-scratch relative-gap estimate (B.2) is unavoidable
  on every route. This re-confirms `oseledets-l7-crux.md`'s "M-2 unusable" verdict for a deeper reason
  than stated.
- **Eigenvector rotation under equal eigenvalues (the core counterexample).** Eigenvalue convergence
  of `qpow_n` does NOT imply matrix convergence: take `Hₙ = Rₙ diag(1,1) Rₙᵀ = I` — trivial — but with
  `diag(1, 1+1/n)` and `Rₙ` an angle-`θₙ` rotation that does not converge, the eigenVALUES converge
  (→1,1) while the top eigenVECTOR `Rₙe₁` need not. What forbids this in our setting is a GENUINE gap
  `e^{λⱼ} > e^{λⱼ₊₁}` (strict) plus the relative-gap bound B.2; with a real gap the top-`j`
  *eigenspace* is pinned. This is precisely why a naive "`‖log Hₙ₊₁ − log Hₙ‖` summable" claim is FALSE
  and why B.2 (not eigenvalue convergence) is the crux.
- **Per-distinct-λ, NEVER per-singular-value-index.** When a distinct exponent has multiplicity > 1,
  the individual eigenprojector inside the cluster is NOT Cauchy (eigenvectors rotate WITHIN the equal
  block); only the SUMMED block projector over a maximal gap-separated cluster is. State B.1/B.2/L7c
  per gap `cⱼ` between DISTINCT exponents (consistent with the committed `specList`/`specCard`). A
  per-index projector statement would be FALSE for multiplicity > 1.
- **Degenerate equal-exponent strata / `k>d`.** Across a non-gap (consecutive equal exponents) there is
  no threshold `cⱼ`; the ladder must skip to the next DISTINCT exponent. For the one-sided invertible
  cocycle (`det ≠ 0`), `Qₙ` is PD throughout, all `σᵢ > 0`, `e^{λᵢ} > 0`; no zero-eigenvalue
  degeneracy. The number of gaps is `specCard − 1`. Safe.
- **No counterexample to any committed statement.** The committed scalar/eigenvalue layer and
  `L7_statement` remain sound; the corrections are about the M-2/complexification route only.

## G. Crux L7c.3 — verified proof route (de-risking pass 2, 2026-06-07)

> Adversarial re-audit of §A/§B/§E, hunting the CHEAPEST correct route for the increment bound.
> Worked the inequality out on paper, verified its truth + direction + constant numerically (Python,
> thousands of random ill-conditioned cases), and COMPILED the load-bearing Lean facts in four new
> probes `scratch_l7c3_{index,rayleigh,assembly,sintheta}.lean` (all `lake env lean`, exit 0; read
> exit codes explicitly — the `lake env` wrapper masked a real error on one earlier run, exactly the
> §F hazard). Conclusions below SUPERSEDE the cost estimate in §E for node L7c.3.

### G.0 Index convention — CHECKED (and it bites)

Committed `cocycle A T (n+1) x = cocycle A T n (T x) * A x` (newest factor LEFT). The left-mult
recurrence the perturbation step needs, `Mₙ₊₁ = A(Tⁿx)·Mₙ`, is NOT definitional — it is
`cocycle_add A T 1 n` after `Nat.add_comm` + `cocycle_one`. COMPILED (`scratch_l7c3_index.lean`,
first `example`). So `B := A(T^[n] x)` is the one-step left factor; `κ(B) = ‖A(Tⁿx)‖·‖A(Tⁿx)⁻¹‖`.

### G.1 The increment bound is TRUE — with constant `C = 1`, ratio `σₖ/σₖ₋₁`, on `sin∠` (NOT `tan`)

Let `Pₙ⁽ᵏ⁾` be the orthogonal projector onto the top-`k` RIGHT-singular subspace of `Mₙ`
(= top-`k` eigenspace of `Qₙ = MₙᵀMₙ`; INDEPENDENT of the power `1/(2n)` — the band projector
`Πₙ⁽ʲ⁾ = cfc χⱼ Hₙ` equals exactly this `Pₙ⁽ᵏⱼ⁾`, the power only relabels eigenvalues). The cut index
`k = kⱼ` must sit at a genuine exponent gap `λ_{k-1} > λ_k`. Then, verified numerically over `d=5`,
all `k`, ill-conditioned `B` (50k+ trials, max ratio **0.52**):

```
‖Pₙ₊₁⁽ᵏ⁾ − Pₙ⁽ᵏ⁾‖  ≤  κ(A(Tⁿx)) · σₖ(Mₙ) / σₖ₋₁(Mₙ)        [C = 1]
```

This CONFIRMS §B.2 (the route doc's `Cⱼ·‖A‖‖A⁻¹‖·σⱼ₊₁/σⱼ`) with the explicit constant `1` and pins
the 0-indexed ratio as `σₖ/σₖ₋₁` (bottom-of-bottom-block over bottom-of-top-block at the cut).

SURPRISES / pitfalls found, each a real correctness constraint:
- **It is genuinely a `sin∠` bound, not `tan∠`.** The `tan` version blows up (max ratio 518 in the
  same experiment). So `‖Pₙ₊₁−Pₙ‖ = sin∠(Eₙ,Eₙ₊₁)` is the right LHS; any proof that produces a
  `tan`-shaped estimate is WRONG.
- **Naive triangle/quadratic-form juggling gives only the WEAK (≈1) bound, not `σₖ/σₖ₋₁`.** Worked it
  out: `‖Mₙu‖² = ‖Mₙ Pₙu‖² + ‖Mₙ(I−Pₙ)u‖²` (orthogonal eigenspaces of `Qₙ`) plus the lower bound
  `‖Mₙu‖ ≥ σₖ₋₁(Mₙ)/κ(B)` yields only `‖w‖² ≤ (σ₀²−(σₖ₋₁/κ)²)/(σ₀²−σₖ²)` — the `σ₀` ruins it. The
  sharp `σₖ/σₖ₋₁` constant is a genuine sin-Θ statement; there is no elementary triangle-inequality
  shortcut on the plain matrices. **The route doc's HIGH risk on L7c.3 stands.**
- **Cutting INSIDE a multiplicity block is FALSE.** With `σ₁ = σ₂` (cut at a non-gap), `‖Pₙ₊₁−Pₙ‖`
  reaches **1.0** (projector NOT Cauchy) and the RHS does not decay (`σₖ/σₖ₋₁ → 1`). Re-confirms
  "per DISTINCT exponent, never per index" as a hard correctness requirement, not style.

### G.2 The CHEAPEST correct route: exterior rank-1 Rayleigh-gap sin-Θ (NOT block Davis–Kahan)

VERDICT: **a full abstract Davis–Kahan / block sin-Θ theorem is NOT needed.** The exterior-power
machinery already committed (`compoundMatrix`, `prod_singularValues_eq_l2_opNorm_compound`,
`exteriorPower.map_comp` functoriality) collapses the block problem to a **rank-1 dominant-eigenvector
sin-Θ**, which has a fully ELEMENTARY (Parseval-only) proof. The reduction (numerically verified):

1. Top-`k` right-singular subspace of `Mₙ` ↔ (Plücker) the dominant eigenLINE of
   `Cₙ := (⋀^k Mₙ)ᵀ(⋀^k Mₙ) = ⋀^k Qₙ` on `⋀^k ℝᵈ ≅ ℝ^(d chok)`. Functoriality gives
   `⋀^k Mₙ₊₁ = (⋀^k B)(⋀^k Mₙ)`.
2. At a genuine gap `λ_{k-1} > λ_k`, the top two singular values of `⋀^k Mₙ` are
   `σ₀···σ_{k-1}` and `σ₀···σ_{k-2}σ_k`, ratio EXACTLY `σ_k/σ_{k-1}` (verified) — so the dominant
   eigenline of `Cₙ` is SIMPLE and gapped. A simple gapped top eigenline is the easiest sin-Θ case.
3. **Elementary rank-1 Rayleigh-gap lemma (the irreducible core, fully provable):** for self-adjoint
   `C` with top eigenvalue `μ₀`, second `≤ μ₁ < μ₀`, top unit eigenvector `v₀`, and ANY unit `v'`
   with `⟨C v', v'⟩ ≥ μ₀ − ε`, one has `sin²∠(v', v₀) ≤ ε/(μ₀ − μ₁)`. Proof = Pythagoras
   (`Submodule.norm_sq_eq_add_norm_sq_projection`, COMPILED) + the purely algebraic kernel
   `μ₀−ε ≤ μ₀c+b, b ≤ μ₁s, c+s=1 ⟹ s ≤ ε/(μ₀−μ₁)` (`nlinarith` after `c := 1−s`, COMPILED in
   `scratch_l7c3_sintheta.lean`). NO abstract Davis–Kahan, NO Riesz contour, NO operator-CFC
   continuity.
4. The Rayleigh deficit `ε = μ₀(Cₙ) − ⟨Cₙ v', v'⟩` for `v' =` dominant eigenvector of `Cₙ₊₁`
   is bounded by `(κ(⋀^k B)·σ_k/σ_{k-1})²` (verified, max ratio 0.18), via
   `⟨Cₙ v',v'⟩ = ‖⋀^k Mₙ v'‖² = ‖(⋀^kB)⁻¹ ⋀^k Mₙ₊₁ v'‖² ≥ ‖⋀^k Mₙ₊₁ v'‖²/‖⋀^kB‖² ≥ μ₀(Cₙ₊₁)/‖⋀^kB‖²`
   and `μ₀(Cₙ₊₁) ≥ μ₀(Cₙ)/‖(⋀^kB)⁻¹‖²`. Hence `sin∠ ≤ κ(⋀^kB)·σ_k/σ_{k-1}`.

Trade-off, stated honestly: the exterior route uses `κ(⋀^k B) = ‖⋀^kB‖‖(⋀^kB)⁻¹‖` (LOOSER than the
direct `κ(B)`), but `(1/n)log κ(⋀^kB)` is STILL tempered → 0 a.e. (it is `≤ k·log‖B‖ + k·log‖B⁻¹‖`
up to the committed `sigma_le_opNorm`/`prod_singularValues` sandwich), so summability is unaffected.
The WIN is that the irreducible analytic content shrinks from a block sin-Θ theorem (which Mathlib
lacks entirely and which would have to be built from scratch) to ONE scalar `nlinarith` kernel +
Pythagoras + the ALREADY-COMMITTED exterior bridge. This is strictly cheaper than building block
Davis–Kahan and is the recommended route.

Why NOT the direct (non-exterior) block route: it needs (i) the per-vector restricted-Rayleigh
bounds `v∈Eₙ ⟹ ‖Mₙv‖≥σₖ₋₁‖v‖` and `v∈Eₙ^⊥ ⟹ ‖Mₙv‖≤σₖ‖v‖` for the BLOCK (provable from the
eigenbasis but more bookkeeping), AND (ii) a genuine block sin-Θ assembly (multi-dimensional
principal angles). The exterior route replaces (ii) by the rank-1 lemma. Both need the eigenbasis
facts (COMPILED, `scratch_l7c3_rayleigh.lean`); only the exterior route avoids multi-dim sin-Θ.

### G.3 EXACT Lean statements (Mathlib-style, plain real matrices / inner product spaces)

```lean
-- G.3a  THE irreducible core (abstract, real inner product space). Bare IsSymmetric, NO CFC instance.
theorem sin_sq_le_rayleigh_deficit_div_gap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {C : E →ₗ[ℝ] E} (hC : C.IsSymmetric)
    {μ₀ μ₁ : ℝ} {v₀ : E} (hv₀ : ‖v₀‖ = 1) (hev : C v₀ = μ₀ • v₀)   -- top eigenpair
    (hgap : μ₁ < μ₀) (hμ₁ : ∀ w, ⟪w, v₀⟫_ℝ = 0 → ⟪C w, w⟫_ℝ ≤ μ₁ * ‖w‖^2)  -- second-eigval ceiling
    {v' : E} (hv' : ‖v'‖ = 1) {ε : ℝ} (hRay : μ₀ - ε ≤ ⟪C v', v'⟫_ℝ) :
    ‖v' - (⟪v', v₀⟫_ℝ) • v₀‖^2 ≤ ε / (μ₀ - μ₁)
-- proof: Pythagoras ‖v'‖²=‖proj‖²+‖perp‖² (Submodule.norm_sq_eq_add_norm_sq_projection on span{v₀});
--        ⟪C v',v'⟫ = μ₀·c + ⟪C perp,perp⟫ ≤ μ₀ c + μ₁ s; then the COMPILED nlinarith kernel.

-- G.3b  the one-step exterior Rayleigh-deficit bound (cocycle-specific; uses committed exterior API)
theorem rayleigh_deficit_le {d : ℕ} (M B : Matrix (Fin d) (Fin d) ℝ)
    (hB : B.det ≠ 0) (k : ℕ) (hk : k ≤ d) (hgap : 0 < σ (k-1) M - σ k M /-genuine gap-/) :
    -- μ₀(⋀^k M) − ⟨(⋀^k M)·v', v'⟩  ≤  (‖⋀^kB‖·‖(⋀^kB)⁻¹‖)² · (σₖ M / σₖ₋₁ M)² · μ₀(⋀^k M)
    sorry  -- via ‖compoundMatrix k (B*M)‖, prod_singularValues_eq_l2_opNorm_compound, compound mult.

-- G.3c  band-projector increment bound (= §B.2, now DERIVED from G.3a+G.3b)
theorem norm_bandProjector_succ_sub_le {d : ℕ}
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (j n : ℕ) (x : X) :
    ‖bandProjector A T j (n+1) x - bandProjector A T j n x‖
      ≤ ‖A (T^[n] x)‖^kⱼ * ‖(A (T^[n] x))⁻¹‖^kⱼ * (σ kⱼ (Mₙ) / σ (kⱼ-1) (Mₙ))   -- κ(⋀^kⱼ B)≤‖B‖^k‖B⁻¹‖^k

-- G.3d  packaging: Cauchy from summable increments  (COMPILED, scratch_l7c3_index.lean)
theorem cauchySeq_of_summable_succ_sub {E} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℕ → E) (hsum : Summable (fun n => ‖f (n+1) - f n‖)) : CauchySeq f

-- G.3e  geometric decay ⇒ summable  (COMPILED, scratch_l7c3_assembly.lean)
theorem summable_of_le_exp_neg (a : ℕ → ℝ) (han : ∀ n, 0 ≤ a n) {c : ℝ} (hc : 0 < c)
    (hbd : ∀ n, a n ≤ Real.exp (-c * n)) : Summable a
```

### G.4 The verified ladder (replaces the L7c.3 row of §E)

| # | Lemma | Risk | Effort | Probe / Mathlib |
|---|---|---|---|---|
| L7c.0 | `bandProjector := cfc χⱼ Hₙ`; self-adj + idempotent on good set | LOW (probe-backed §A) | <0.5 | `cfc_predicate/_mul/_congr` |
| L7c.1 | `bandProjector = Pₙ⁽ᵏⱼ⁾` (top-`kⱼ` eigenproj of `Qₙ`), power-independent | MED | 1 | `IsHermitian.cfc` formula; repo `orthProjMatrix` pattern |
| L7c.2 | tempered factor `(1/n)log(‖A(Tⁿx)‖‖A⁻¹‖) → 0` a.e. | **LOW (already proved)** | <0.5 | repo `ae_tendsto_orbit_div_atTop_zero` (Birkhoff.lean:187, currently `private`) |
| L7c.3a | rank-1 Rayleigh-gap sin-Θ core `sin_sq_le_rayleigh_deficit_div_gap` | **MED** (was HIGH) | 1–2 | **COMPILED kernel** `scratch_l7c3_sintheta.lean` (Pythagoras + nlinarith) |
| L7c.3b | exterior Rayleigh-deficit `rayleigh_deficit_le` (compound API) | **HIGH** | 2–3 | committed `prod_singularValues_eq_l2_opNorm_compound`, `exteriorPower.map_comp`; needs single-index `σⱼ(⋀^kB·X) ≤ ‖⋀^kB‖σⱼ(X)` (BUILD) |
| L7c.3c | assemble `norm_bandProjector_succ_sub_le` (G.3a∘G.3b + Plücker subspace↔eigenline) | **HIGH** | 1–2 | the subspace↔eigenline (Plücker) bridge is new infra |
| L7c.4 | `hsum` a.e. (geometric decay ⇒ summable) | LOW–MED | 0.5–1 | **COMPILED** `scratch_l7c3_{assembly,index}.lean` + `tendsto_log_singularValue` |
| L7c.5 | `cauchySeq_bandProjector` (Cauchy from summable incr.) | **LOW (COMPILED)** | <0.5 | `scratch_l7c3_index.lean` |
| L7d  | `cauchySeq_qpow ⇒ L7_statement` (assemble blocks×eigenvalues) | MED | 1–1.5 | `scratch_l7c3_assembly.lean` (smul-limit, completeness) + committed `eigenvalues_qpow_tendsto` |

Net L7c→L7d: **~7–11 sessions** (down from §E's 8–14), dominated now by L7c.3b+L7c.3c (the
exterior-deficit estimate + the Plücker subspace↔eigenline bridge), NOT by an abstract Davis–Kahan
theorem. The single-index exterior submultiplicativity `σⱼ(⋀^kB·X) ≤ ‖⋀^kB‖·σⱼ(X)` is a small new
lemma (Mathlib has only the product form `prod_singularValues_comp_le`; min-max is absent).

### G.5 What was COMPILED vs argued on paper (honest ledger)

| Probe | Claim | Status |
|---|---|---|
| `scratch_l7c3_index.lean` | (i) `Mₙ₊₁ = A(Tⁿx)·Mₙ` from committed cocycle; (ii) Cauchy ⇐ summable increments | **COMPILED exit 0** |
| `scratch_l7c3_rayleigh.lean` | eigenbasis `apply_eigenvectorBasis`, `eigenvalues_antitone`, `singularValues_antitone`, `sq_singularValues` — the restricted-Rayleigh ingredients | **COMPILED exit 0** |
| `scratch_l7c3_assembly.lean` | geometric-decay ⇒ summable; `Tendsto.smul` block assembly; `cauchySeq_tendsto_of_complete` | **COMPILED exit 0** |
| `scratch_l7c3_sintheta.lean` | Pythagoras `norm_sq_eq_add_norm_sq_projection`; **the algebraic kernel of the rank-1 sin-Θ bound** | **COMPILED exit 0** |

ARGUED ON PAPER + verified NUMERICALLY only (Python, not Lean):
- The increment bound `‖Pₙ₊₁−Pₙ‖ ≤ κ(B)σₖ/σₖ₋₁` with `C=1` (max ratio 0.52 over 50k+ trials).
- The exterior reduction: top-2 singular-value ratio of `⋀^k M` equals `σₖ/σₖ₋₁` (exact).
- The full chain `sin²∠ ≤ ε/g ≤ (κ(⋀^kB)·σₖ/σₖ₋₁)²` (max 0.18) and the rank-1 kernel `sin² ≤ ε/g`
  (tight, ratio 1.0).
- The `tan` form FAILS (518); cutting inside a multiplicity block FAILS (1.0). Both are correctness
  guards, not yet Lean-encoded.

These four numerically-verified inequalities are the L7c.3 work to formalize; the Lean *kernels* they
rest on are the four compiled probes above. No committed statement is contradicted.
