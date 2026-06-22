# Feasibility report — Issue #8: Yamamoto singular-value limit

**Leaf:** `Frontier/Issue1/Yamamoto.lean`, lemma `yamamoto_singularValues_tendsto` (`sorry` at ~line 128).
**Date:** 2026-06-22.
**Reference:** Soumyashant Nayak, *A stronger form of Yamamoto's theorem on singular values*,
arXiv:2303.01252 (the saved `refs/yamamoto-stronger.md`). The decisive results are
Proposition 3.2 (trace-moment identity), Proposition 3.3 (limit-point structure), Theorem 3.8
(convergence of `|Aⁿ|^{1/n}`) and Corollary 3.9 (= Yamamoto's theorem).

> NOTE on the saved ref's attribution line: the markdown header lists the author area incorrectly;
> the actual sole author of arXiv:2303.01252 is **Soumyashant Nayak** (ISI Bangalore). The CLAUDE
> orchestration text calls it "Dowla–Mukherjee et al." — that attribution is wrong; cite Nayak.

---

## 1. Precise Lean type of the leaf

```lean
theorem yamamoto_singularValues_tendsto (M : Matrix (Fin d) (Fin d) ℝ) (i : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (M ^ n)).singularValues i))
      atTop (𝓝 (Real.log ((eigenvalueModuli M).getD i 0)))
```

where (in the same file)

```lean
noncomputable def eigenvalueModuli (M : Matrix (Fin d) (Fin d) ℝ) : List ℝ :=
  (((M.map (algebraMap ℝ ℂ)).charpoly.roots).map (fun z => ‖z‖)).sort (· ≥ ·)
```

So `(eigenvalueModuli M).getD i 0` is the `i`-th (0-indexed) entry of the **non-increasingly sorted
multiset of complex-eigenvalue moduli** of `M`, padded with `0` past index `d-1`.

The singular value is `LinearMap.singularValues` of `Matrix.toEuclideanLin (M^n) : EuclideanSpace ℝ (Fin d) →ₗ EuclideanSpace ℝ (Fin d)`,
which Mathlib defines (`Mathlib/Analysis/InnerProductSpace/SingularValues.lean`) as the
finitely-supported sequence whose first `d` entries are `√(eigenvalue of (adjoint ∘ self))`, sorted
**antitone** (`LinearMap.singularValues_antitone`), zero-indexed.

**Subtle real-vs-complex point.** The goal is stated for a *real* matrix `M` but `eigenvalueModuli`
uses the complex eigenvalues of `M.map (algebraMap ℝ ℂ)`. The singular values, however, are
computed over `ℝ` via `toEuclideanLin (M^n)`. Because `σᵢ(M^n)² = eigenvalue of (M^n)ᵀ(M^n)`, and
`(M^n)ᵀ(M^n)` has the *same* real entries whether viewed over `ℝ` or `ℂ`, the real singular values of
`M^n` equal the complex singular values of `(M.map …)^n`. A small reconciliation lemma is needed
(see sub-lemma S0) but is routine: singular values are real-base-field-invariant.

This needs to hold **for all `i : ℕ`**, including `i ≥ d`. For `i ≥ d` the singular value is `0`
(`singularValues_of_finrank_le`) and `getD i 0 = 0`, so both sides are `Real.log 0 = 0` and the
sequence is constantly `0` — a trivial branch that must be handled explicitly (`Real.log 0 = 0` in
Mathlib's junk convention), giving `Tendsto … (𝓝 0)`.

---

## 2. Literature proof (Nayak, arXiv:2303.01252), reduced to what this leaf needs

The leaf needs only Corollary 3.9: `limₙ sⱼ(Aⁿ)^{1/n} = |λⱼ|(A)`. Taking `(1/n)·log` and
`log`-continuity converts the `n`-th-root statement to the additive form in the goal. The proof of
Cor 3.9 chains:

1. **Polar identity** `sⱼ(Aⁿ)^{1/n} = sⱼ(|Aⁿ|^{1/n})`, where `|T| := √(Tᴴ T)`. (Singular values of
   `T` = eigenvalues of `|T|`; `sⱼ(Hᵖ) = sⱼ(H)ᵖ` for PSD `H`, `p>0`.)
2. **Convergence** `H := limₙ |Aⁿ|^{1/n}` exists in the PSD cone (Theorem 3.8(i)).
3. **Singular-value continuity** `sⱼ(|Aⁿ|^{1/n}) → sⱼ(H)` (Lemma 2.4, Weyl perturbation).
4. **Spectral match** `sⱼ(H) = |λⱼ|(H) = |λⱼ|(A)` (Prop 3.3(iii): the multiset of eigenvalues of `H`
   equals the multiset of eigenvalue-moduli of `A`).

The convergence (step 2) is the deep part. Its skeleton (Thm 3.8(i)) is:

- **Lemma 3.1 / `Wₙ` trick.** Put `A` in upper-triangular (Schur) form by a unitary; set
  `Wₙ = diag(1,n,n²,…,n^{m-1})`. Then `Λₙ := WₙAWₙ⁻¹ → diag(λ₁,…,λ_m)` because the `(i,j)` entry is
  scaled by `n^{i-j}`, killing the strict-upper part.
- **Prop 3.2 (trace-moment identity).** For all `p∈[0,∞)`, `∑ᵢ|λᵢ|ᵖ = limₙ tr(|Aⁿ|^{p/n})`.
  - `≤`: Weyl's majorant theorem `∑|λᵢ|ᵖ ≤ tr(|A|ᵖ)` (Prop 2.5) applied to `Aⁿ` with `p/n`, plus
    the spectral mapping `|λᵢ(Aⁿ)| = |λᵢ|ⁿ`.
  - `≥`: via `Λₖ`: `tr(|Λₖ|ᵖ) → ∑|λᵢ|ᵖ`, the sub-multiplicative power-trace inequality
    (Cor 2.7: `tr(|Aⁿ|^{p/n}) ≤ tr(|A|ᵖ)`, from the generalized Hölder/Weyl-majorization Prop 2.6),
    and `Aⁿ = Wₖ⁻¹ΛₖⁿWₖ` with the conjugation bound `tr(|XBC|ᵖ) ≤ ‖X‖ᵖ‖C‖ᵖ tr(|B|ᵖ)`.
- **Prop 3.3.** `{|Aⁿ|^{1/n}}` is bounded (`‖|Aⁿ|^{1/n}‖ = ‖Aⁿ‖^{1/n} ≤ ‖A‖`), so by compactness
  has limit points, all PSD; each limit point `H` satisfies `tr(Hᵖ) = ∑|λᵢ|ᵖ` (from Prop 3.2 + trace
  continuity), hence `|λ|(H) = |λ|(A)` as multisets (moments determine the spectrum of a PSD matrix).
- **Prop 3.5–3.7 (uniqueness of the limit point).** Introduce `V(A,r) = {x : limsupₙ‖Aⁿx‖^{1/n} ≤ r}`,
  show it is a subspace, equals the span of eigenvectors of the *diagonalizable part* `D` of the
  **Jordan-Chevalley decomposition** `A = D+N` with `|λ| ≤ r`, and that every PSD limit point `H` has
  `V(H,r) = V(A,r)`; a PSD matrix is determined by its family `{V(H,r)}` (Lemma 3.6(ii)). Hence the
  limit point is unique ⇒ the sequence converges (Thm 3.8(i)).

**Crucial structural observation for formalization.** Cor 3.9 (and therefore this leaf) requires the
**full convergence** of `|Aⁿ|^{1/n}` (step 2), not merely the trace-moment identity. Convergence is
where the Jordan-Chevalley `A=D+N` and the `V(A,r)` machinery (Lemmas 3.5–3.7) enter. There is **no
shortcut** in Nayak that proves Cor 3.9 from Prop 3.2 alone; the trace moments pin down the spectrum
of *each* limit point but you still need limit-point uniqueness to get a single `H`.

**Alternative proof (Mathias, ref [7] in Nayak).** R. Mathias, *Two theorems on singular values and
eigenvalues* (or the proof reproduced in Horn–Johnson), proves Yamamoto's theorem **without**
constructing the limit matrix `H`, using the interlacing/majorization of singular values of
principal blocks under Schur triangularization and a sandwich. This route avoids Jordan-Chevalley
and PSD-cone limit-point uniqueness entirely and is a genuinely independent strategy (see §6).

---

## 3. What Mathlib already provides (exact names found)

Searched `.lake/packages/mathlib/Mathlib`. Useful existing infrastructure:

| Need | Mathlib lemma/def found | File |
|---|---|---|
| CFC instance for `Matrix n n ℂ` (Hermitian) | `Matrix.IsHermitian.instContinuousFunctionalCalculus`, `…instContinuousFunctionalCalculusIsClosedEmbedding`, `Matrix.IsHermitian.cfc`, `cfc_eq`, `charpoly_cfc_eq` | `Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean` |
| Polar part `|T|` and `√` of PSD matrix | `CFC.abs`, `CFC.abs_eq_cfc_norm`, `CFC.sqrt`, `CFC.sqrt_eq_cfc`, `CFC.sq_sqrt`, `CFC.sqrt_nonneg`, `Matrix.…inv_sqrt`, `det_sqrt`, `det_abs` | `Mathlib/Analysis/Matrix/Order.lean` |
| Fractional powers `Hᵖ`, `H^{p/n}`, `(Hᵖ)^q = H^{pq}` | `CFC.rpow`, `CFC.nnrpow`, `CFC.rpow_rpow`, `rpow_rpow_inv`, `rpow_natCast`, `sqrt_eq_rpow`, `cfc_rpow` | `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean` |
| Matrix is a C⋆-ring/-algebra (so CFC + rpow apply) | `Matrix.instCStarRing` (scoped `Matrix.Norms.L2Operator`), `CStarMatrix.instCStarAlgebra` | `Mathlib/Analysis/CStarAlgebra/Matrix.lean`, `.../CStarMatrix.lean` |
| Singular values, ordering, link to eigenvalues | `LinearMap.singularValues`, `singularValues_antitone`, `singularValues_nonneg`, `singularValues_fin`, `sq_singularValues_fin`, `singularValues_of_finrank_le`, `singularValues_of_lt`, `card_support_singularValues` | `Mathlib/Analysis/InnerProductSpace/SingularValues.lean` |
| Charpoly splits over ℂ, `d` roots with multiplicity | `IsAlgClosed.splits`, `Polynomial.splits_iff_card_roots`, `Matrix.charpoly_natDegree_eq_dim` (already used in `eigenvalueModuli_length`) | `…/Charpoly/Eigs.lean`, `…/Complex/Polynomial/Basic.lean` |
| PSD eigenvalues = nonneg, trace = ∑ eigenvalues | `Matrix.PosSemidef` API, `IsHermitian.trace_eq_sum_eigenvalues`, `…eigenvalues_nonneg`, `det_eq_prod_eigenvalues` | `Mathlib/LinearAlgebra/Matrix/PosDef.lean`, `…/Spectrum.lean` |
| Generalized-eigenspace decomposition over ℂ | `Module.End.iSup_genEigenspace_eq_top`, `iSup_maxGenEigenspace_eq_top`, `genEigenspace`, `maxGenEigenspace` | `Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean` |
| Semisimple/nilpotent uniqueness facts | `Module.End.eq_zero_of_isNilpotent_isSemisimple`, `IsFinitelySemisimple.genEigenspace_eq_eigenspace`, `apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil` | `Mathlib/LinearAlgebra/{Semisimple, Eigenspace/Semisimple}.lean` |
| Spectral-radius formula (the `i=0` case) | (search Mathlib `spectralRadius`, `…pow_norm`) — Gelfand formula exists in CStar theory | `Mathlib/Analysis/…/GelfandDuality`/`SpectralRadius` |
| `nᵏ`-th root → 1, generic limits | `Nat.tendsto_pow_atTop_atTop`, `tendsto_rpow_natCast…`, `Filter.Tendsto.comp` with `Real.continuous_log` on `(0,∞)` | core analysis |

### Confirmed GAPS in Mathlib (the hard part)

1. **No additive/multiplicative Jordan–Chevalley *existence* for a matrix/endomorphism over a
   perfect field.** Mathlib has the *raw material* (`iSup_maxGenEigenspace_eq_top`) and the
   Lie-algebra `ad`-version (`Mathlib/Algebra/Lie/AdjointAction/JordanChevalley.lean`:
   `ad_mem_adjoin_of_isSemisimple`), but **no** packaged theorem
   `∃ D N, A = D+N ∧ Commute D N ∧ D.IsSemisimple ∧ IsNilpotent N`. This must be built from
   `iSup_genEigenspace_eq_top` (define `D` as the operator acting by `λ` on each generalized
   eigenspace; `N := A - D`; commutation + nilpotence from the block structure). Medium-to-hard,
   genuinely missing infrastructure.
2. **No Schur unitary upper-triangularization** of a complex matrix
   (`∃ U unitary, UᴴAU upper-triangular`). Needed for Lemma 3.1 / the `Wₙ` collapse. Mathlib has
   `Mathlib/LinearAlgebra/Matrix/Block.lean` block-triangular tooling and `iSup_genEigenspace…` but
   no assembled Schur form. Hard (this is a real Mathlib-scale contribution on its own).
3. **No Weyl perturbation theorem** `|sⱼ(A) − sⱼ(B)| ≤ ‖A−B‖` (Bhatia VI.2.1) and no Weyl majorant
   theorem `∑φ(|λᵢ|) ≤ ∑φ(sᵢ)` (Bhatia II.3.6). Searched for `Weyl`/eigenvalue-continuity — absent.
   The singular-value-continuity Lemma 2.4 and the moment inequality Prop 2.5 both depend on these.
   Medium-hard.
4. **No "moments determine a PSD spectrum" lemma** (`∀p>0, ∑μᵢᵖ = ∑νᵢᵖ ⇒ multisets {μ}={ν}` for
   nonneg reals). Provable from Newton's identities / power-sum symmetric polynomials or from
   distinctness via Vandermonde, but not packaged. Medium.
5. **No "log of `n`-th-root limit" plumbing tying `LinearMap.singularValues` to a sorted
   eigenvalue-modulus list.** The bridge from `sⱼ(H)` (antitone Mathlib sequence) to
   `(eigenvalueModuli M).getD i 0` (a `Multiset.sort (·≥·)` of charpoly-root norms) is index
   bookkeeping that is fiddly but elementary. Medium.

---

## 4. Decomposition into sub-lemmas

| name | statement (informal) | mathlibSupport | difficulty |
|---|---|---|---|
| `S0_realComplex_singularValues` | `σᵢ(M^n)` over ℝ (`toEuclideanLin`) = `σᵢ((M.map ℂ)^n)` over ℂ; reconcile real goal with complex eigenvalues | partial (`singularValues_fin` + base-change of `AᴴA`) | medium |
| `S1_polar_singularValues` | for `T : Matrix d d ℂ`, `σⱼ(T) = eigenvalueₖ (CFC.sqrt (Tᴴ*T))`; and `σⱼ(T)^{1/n}=σⱼ(|T|^{1/n})` via `CFC.rpow` | partial (`CFC.abs/sqrt/rpow`, `singularValues_fin`) | medium |
| `S2_weyl_majorant` | `∑ᵢ|λᵢ(A)|ᵖ ≤ tr(|A|ᵖ)` (Prop 2.5) | absent (needs Weyl majorant Bhatia II.3.6) | hard |
| `S3_power_trace_subm` | `tr(|Aⁿ|^{p/n}) ≤ tr(|A|ᵖ)` (Cor 2.7 via generalized Hölder Prop 2.6) | absent (needs singular-value log-majorization `sⱼ(AB)≺sⱼ(A)sⱼ(B)`) | hard |
| `S4_schur_triangular` | `∃ U ∈ unitary, Uᴴ A U` upper-triangular over ℂ | absent | hard |
| `S5_Wn_collapse` | `Wₙ A Wₙ⁻¹ → diag(λ)` for upper-triangular `A`, `Wₙ=diag(1,…,n^{d-1})`; entrywise `n^{i-j}` scaling + `Tendsto` | partial (entrywise limits elementary; needs S4) | medium |
| `S6_trace_moment` | `∑ᵢ|λᵢ|ᵖ = limₙ tr(|Aⁿ|^{p/n})` (Prop 3.2) | absent (assembles S2,S3,S5) | hard |
| `S7_seq_bounded_PSD` | `{|Aⁿ|^{1/n}}` norm-bounded by `‖A‖`, limit points PSD (Prop 3.3(i)) | partial (`CFC.abs`, PSD cone closed, ball compact in finite dim) | medium |
| `S8_limitpoint_spectrum` | every limit point `H` has `tr(Hᵖ)=∑|λᵢ|ᵖ`, hence `|λ|(H)=|λ|(A)` (Prop 3.3(ii)(iii)) | partial (needs S6 + S-moments) | medium |
| `S_moments_det_spectrum` | nonneg reals with equal power-sums for all `p>0` ⇒ equal multisets | absent | medium |
| `S9_jordan_chevalley` | `∃ D N, A=D+N ∧ Commute D N ∧ D.IsSemisimple ∧ IsNilpotent N` over ℂ | absent (raw material `iSup_genEigenspace_eq_top` exists) | hard |
| `S10_V_subspace` | `V(A,r)={x:limsup‖Aⁿx‖^{1/n}≤r}` is a subspace ⊇ eigenvectors of `D` with `|λ|≤r` (Lem 3.5) | partial (needs S9, binomial `(D+N)ⁿ`, `Nat.choose` `n`-th root →1) | medium |
| `S11_V_psd` | for PSD `H`, `V(H,r)=ran(∑_{aᵢ≤r}Fᵢ)`, and `{V(H,r)}` determines `H` (Lem 3.6) | partial (spectral decomp of PSD via cfc) | medium |
| `S12_limit_unique` | `V(A,r)=V(H,r)` for every limit point `H` ⇒ unique limit point ⇒ `|Aⁿ|^{1/n}` converges (Prop 3.7, Thm 3.8(i)) | partial (assembles S8,S10,S11) | hard |
| `S13_singval_continuity` | `Hₙ→H` Hermitian ⇒ `σⱼ(Hₙ)→σⱼ(H)` (Lem 2.4, Weyl perturbation) | absent (needs `|sⱼ(A)−sⱼ(B)|≤‖A−B‖`) | hard |
| `S14_cor39` | `σⱼ(Aⁿ)^{1/n} → |λⱼ|(A)` (Cor 3.9): chain S1,S12,S13,S8 | — (assembly) | medium |
| `S15_log_repackage` | turn `n`-th-root convergence into `(1/n)log σ → log|λᵢ|`, handle `i≥d` & `σ=0`, match `eigenvalueModuli … getD i 0` ordering | partial (`Real.continuous_log`, antitone sort bookkeeping) | medium |

---

## 5. Honest assessment of size

This is **not** a one-PR leaf. Closing it sorry-free requires building, from scratch in Mathlib
style, **four** pieces of genuine matrix-analysis infrastructure that Mathlib lacks today:

- Schur unitary triangularization (S4),
- the multiplicative/additive Jordan–Chevalley decomposition of a matrix over ℂ (S9),
- Weyl's perturbation + majorant theorems / singular-value log-majorization (S2, S3, S13),
- the PSD-cone limit-point uniqueness argument (S10–S12).

Each of S4, S9, and the Weyl pair is independently a multi-hundred-line Mathlib contribution. The
glue (S0–S1, S5–S8, S14–S15) is medium difficulty but voluminous and relies on the above. A
realistic estimate is **several thousand lines** of new Lean across a dozen+ files, i.e. a
multi-month effort even for an expert, comparable in scale to the existing `Oseledets/` MET proof
itself. The `BLOCKED` annotation in the source is accurate and well-calibrated.

The Mathlib `CFC` story is genuinely good news: `CFC.abs`, `CFC.sqrt`, `CFC.rpow` over
`Matrix n n ℂ` already exist and remove what the docstring feared most ("Mathlib lacks fractional
Hermitian matrix powers"). That is **wrong/outdated** in the leaf's own comment — fractional powers
DO exist via `CFC.rpow`. The true blockers are Schur form, Jordan-Chevalley existence, and Weyl
perturbation/majorization, none of which CFC helps with.

---

## 6. Independent strategies for parallel implementation attempts

**Strategy A — Nayak route (PSD-cone convergence), full faithful port.**
Implement S0–S15 exactly as in arXiv:2303.01252. Heaviest, but the reference gives every step with
theorem numbers. Build order: CFC polar/rpow lemmas (S0,S1,S7) → Schur (S4) → trace-moment via Weyl
(S2,S3,S5,S6) → Jordan-Chevalley (S9) → `V(A,r)` uniqueness (S10–S12) → continuity (S13) →
assembly (S14,S15). Best if the goal is a reusable Mathlib-grade `|Aⁿ|^{1/n}` convergence theorem.

**Strategy B — Mathias route (block-interlacing), avoids Jordan-Chevalley and limit-point
uniqueness.** Port R. Mathias's proof (Nayak ref [7]; also in Horn–Johnson *Topics in Matrix
Analysis*, §3.3, or *Matrix Analysis* 2nd ed.). Uses only: Schur triangularization (S4), the
singular-value interlacing/majorization for principal leading blocks, and a direct sandwich
`|λⱼ| ≤ liminf σⱼ(Aⁿ)^{1/n} ≤ limsup σⱼ(Aⁿ)^{1/n} ≤ |λⱼ|`. This **eliminates S9, S10–S12, the whole
`V(A,r)` apparatus, and the moment-determines-spectrum lemma** — substantially smaller. Still needs
S4 and the block/majorization inequalities (S2/S3-flavored). Likely the **least total work** and the
recommended primary attempt. Independent proof skeleton, not a variation of A.

**Strategy C — Top-exponent + exterior-power induction (Lyapunov-style).**
Yamamoto for index `i` follows from `‖Λⁱ⁺¹(Aⁿ)‖^{1/n} → ∏_{k≤i}|λₖ|` (top singular value of the
`(i+1)`-fold exterior power) combined with `σ₀⋯σᵢ(Aⁿ) = ‖Λⁱ⁺¹(Aⁿ)‖`. The top case is the
spectral-radius / Gelfand formula `‖Bⁿ‖^{1/n} → ρ(B)` applied to `B = Λⁱ⁺¹(A)`, whose spectral
radius is `∏_{k≤i}|λₖ(A)|` (eigenvalues of exterior powers = products of `i+1` eigenvalues of `A`).
Telescoping the products recovers each `σᵢ`. This leverages Mathlib's existing Gelfand/spectral-
radius and any exterior-power machinery the `Oseledets/Lyapunov/Extensions/` wedge files already
built, and **sidesteps polar decomposition, Jordan-Chevalley, and Weyl perturbation** entirely —
the only analytic input is the scalar Gelfand formula. Risk: need `ρ(Λⁱ⁺¹ A) = ∏|λₖ|` (eigenvalues
of `⋀ᵏ` = `k`-products of eigenvalues; partial Mathlib support) and the singular-value/exterior-norm
identity `s₁⋯sᵢ = ‖⋀ⁱ‖` (the wedge growth lemmas in this repo may already supply it). **Most likely
to reuse existing repo infrastructure**; genuinely independent route.

**Strategy D — Direct trace-moment + Tonelli/Stolz on the sorted list (partial, weaker target).**
If full convergence proves intractable, prove only the *consequences this repo actually consumes*:
the trace-moment identity S6 plus continuity, giving `limₙ tr(|Aⁿ|^{p/n}) = ∑|λᵢ|ᵖ`, then extract
the sorted top value by the `Lemma 2.3` sandwich (`limₙ(∑tᵢaᵢⁿ)^{1/n}=max aᵢ`) at the level of the
*ordered* singular values via a majorization argument, recovering each `σᵢ` by peeling. This still
needs S4 + Weyl but **avoids Jordan-Chevalley/V(A,r)**; it is a middle ground between A and B.

Recommended parallel fan-out: **B (primary), C (high-reuse alternative), A (faithful fallback)**.

---

## 7. Key Mathlib lemmas to lean on (quick reference for implementers)

- `Matrix.IsHermitian.instContinuousFunctionalCalculus`, `Matrix.IsHermitian.cfc`, `cfc_eq`,
  `charpoly_cfc_eq` — CFC over `Matrix n n ℂ`.
- `CFC.abs`, `CFC.abs_eq_cfc_norm`, `CFC.sqrt`, `CFC.sqrt_eq_cfc`, `CFC.sq_sqrt`,
  `Matrix.…det_abs`, `det_sqrt` — polar part `|T|`.
- `CFC.rpow`, `CFC.nnrpow`, `CFC.rpow_rpow`, `rpow_rpow_inv`, `sqrt_eq_rpow`, `cfc_rpow` —
  fractional Hermitian powers `H^{p/n}`.
- `LinearMap.singularValues`, `singularValues_fin`, `sq_singularValues_fin`,
  `singularValues_antitone`, `singularValues_of_finrank_le`, `card_support_singularValues`.
- `IsAlgClosed.splits`, `Polynomial.splits_iff_card_roots`, `Matrix.charpoly_natDegree_eq_dim`
  (note this fork's **one-argument** `Polynomial.Splits`; import
  `Mathlib.Analysis.Complex.Polynomial.Basic` for `IsAlgClosed ℂ`).
- `Module.End.iSup_genEigenspace_eq_top`, `iSup_maxGenEigenspace_eq_top`,
  `Module.End.eq_zero_of_isNilpotent_isSemisimple` — raw material for building S9 (Jordan-Chevalley).
- `Matrix.PosSemidef` API, `IsHermitian.trace_eq_sum_eigenvalues`, `eigenvalues_nonneg`,
  `Matrix.instCStarRing` (scoped `Matrix.Norms.L2Operator`).
- `Real.continuous_log` (on `(0,∞)`), `Real.log_zero`, `Nat.tendsto_pow_atTop_atTop`,
  `tendsto_nhds_unique` — final repackaging into the `(1/n)·log` form.

---

## 8. Verdict

See structured `honestVerdict`.
