# Feasibility report — Issue #10, Pesin reverse inequality `∑λ⁺ ≤ h`

**Leaf:** `Frontier/Issue4Pesin/ManeLowerBound.lean` ~line 124,
`Frontier.Issue4Pesin.sumPosExp_le_ksEntropy_of_SRB` (single `sorry`).
**Date:** 2026-06-22. **Mode:** recon only (no `.lean` edits, no builds).
**Verdict (short):** research wall, but **honestly partially decomposable** — one genuine sub-piece
(Layer 1, Mañé Prop 7.7) is plausibly closeable now on top of existing project + Mathlib
infrastructure; the geometric Layer 2 is a multi-year Pesin/Ledrappier–Young wall.

---

## 1. Precise leaf type

```lean
theorem sumPosExp_le_ksEntropy_of_SRB
    {d : ℕ} [NeZero d]
    {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : Ergodic T μ)
    (hdet : ∀ x, (Oseledets.derivativeCocycle T x).det ≠ 0)
    (hint  : Oseledets.IntegrableLogNorm (Oseledets.derivativeCocycle T) μ)
    (hint' : Oseledets.IntegrableLogNorm (fun x => (Oseledets.derivativeCocycle T x)⁻¹) μ)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hSRB : SRBProperty T μ)
    (hχ   : UnstableJacobianRate hT hdet hint hint' χ) :
    ((Oseledets.sumPosExp hT hdet (Oseledets.measurable_derivativeCocycle T) hint hint' : ℝ) : EReal)
      ≤ Oseledets.Entropy.ksEntropy hT.toMeasurePreserving
```

i.e. `(sumPosExp : EReal) ≤ h_μ(T)`, the **reverse** of the proved Margulis–Ruelle inequality
`Oseledets.margulisRuelle_sharp` (`h_μ(T) ≤ sumPosExp`). `le_antisymm` of the two is Pesin's formula
(`PesinFormula.lean`, already wired sorry-free *modulo this single leaf*).

### What the skeleton already gives sorry-free (the hypotheses / interfaces)
- `Oseledets.sumPosExp …` — the deterministic constant `∑ λ_i⁺` (ExponentSums.lean), a plain `ℝ`.
- `Oseledets.Entropy.ksEntropy hT.toMeasurePreserving : EReal` — KS entropy as
  `⨆_{n} ⨆_{P : Fin n-partition} ksEntropyPartition`, the Fekete limit of finite-partition join
  entropies (KSEntropySystem.lean). **Defined only via finite partitions.**
- `UnstableJacobianRate hT … χ` (SRBData.lean) is **defined to be** `∀ᵐ x ∂μ, χ x = sumPosExp`. So
  `∫ χ dμ = sumPosExp` is already discharged in `pesin_entropy_formula` (the `hbridge` step). The
  *geometric* content (that this χ is the unstable-Jacobian rate) is folded into the interface, NOT
  proved. **Consequence:** the leaf's RHS reduces to `(sumPosExp : EReal) ≤ h_μ(T)` with no integral
  to manage — the integrand identity is assumed.
- `SRBProperty T μ` (SRBData.lean) is **opaque**: a `Prop`-structure with one field
  `acConditionalUnstable : True`. It is a genuine non-trivial hypothesis (cannot be discharged) but
  carries **no usable mathematical content** — there is nothing to destructure into an
  absolute-continuity statement. *This is the load-bearing honesty gap:* the proof cannot actually
  consume SRB-ness because the interface exposes nothing.

**Honest reading of the SRB-data hypotheses.** Of the data Mañé's proof consumes, NONE is present as
a usable interface: `hSRB.acConditionalUnstable : True` is a placeholder, and `hχ` is an a.e.-equality
to a constant (it gives `∫χ = sumPosExp`, not the per-orbit Jacobian growth `log|det Dgⁿ|Eᵘ| ≈ nχ`
that 7.15/(7.18) actually needs). So as currently typed, the leaf **cannot be honestly closed** by
consuming its own hypotheses — the geometric inputs are stubs. A truthful close requires either
(a) enriching `SRBProperty`/`UnstableJacobianRate` into real statements (then proving the geometry),
or (b) the cleanest realistic deliverable: **replace the one `sorry` by a small set of individually
stated, individually `sorry`-carrying sub-lemmas** matching the proof's true layers, so the wall is
sharply localized and auditable. (b) is what I recommend below.

---

## 2. The literature proof (Mañé), top-down, with precise citations

Primary source scraped in full: **M. Contractor, *The Pesin Entropy Formula*, UChicago REU 2023, §7**
(`https://math.uchicago.edu/~may/REU2023/REUPapers/Contractor.pdf`). This reproduces
**R. Mañé, *A proof of Pesin's formula*, ETDS 1 (1981) 95–102** — the *partition-free, stable-manifold-
free* proof (confirmed by Scholarpedia: Mañé's route is the "somewhat straightforward" one that
"avoids unstable foliations, their absolute continuity, leaf-subordinated partitions"). This matters:
**Mañé's proof needs much *less* Pesin machinery than Ledrappier–Young.** The cost is shifted onto a
clean general entropy lower bound (Prop 7.7) plus a graph-transform volume estimate (7.9–7.15).

### Layer 1 — abstract metric-entropy lower bound (Contractor **Prop 7.7**)
> Let `μ` be `g`-invariant, `ν ≪ μ` (not necessarily invariant). Then
> `h_μ(g) ≥ ∫_M h_ν(g, ρ, x) dμ`, where `h_ν(g,ρ,x) := limsup_n -1/n · log ν(Sₙ(g,ρ,x))` is the
> *local ν-entropy* of the dynamical refinement of the ρ(x)-ball.

**Proof skeleton (verbatim structure):**
1. Take the **countable** partition `P` of **Lemma 7.6**: `H(P) < ∞` and `diam P(x) ≤ ρ(x)` a.e.
   (built from `log ρ` integrable via the elementary **Lemma 7.5** summability estimate).
2. **Shannon–McMillan–Breiman (Contractor Thm 2.14)** + KS def (2.10):
   `h_μ(g) ≥ h_μ(P,g) = ∫ limₙ 1/n·[−log μ(Pₙ(x))] dμ` where `Pₙ = ⋁₀ⁿ⁻¹ g⁻ᵏP`.
3. Reduce to `limₙ 1/n[−log μ(Pₙ(x))] ≥ h_ν(g,ρ,x)` a.e. Split
   `1/n log μ(Pₙ) = 1/n log ν(Pₙ) + 1/n log(μ(Pₙ)/ν(Pₙ))`. The **second term → 0 a.e.** by the
   **Radon–Nikodym / martingale (Lévy upward) theorem** (Contractor Thm 2.7): `μ(Pₙ)/ν(Pₙ) → k`,
   a finite a.e. limit (the conditional density on `P_∞ = σ(⋃Pₙ)`), so `1/n log(·) → 0`.
4. Hence `limₙ 1/n[−log μ(Pₙ)] = limₙ 1/n[−log ν(Pₙ)] ≥ h_ν(g,ρ,x)` (last `≥` because `Sₙ ⊂ Pₙ`
   up to the ρ-ball containment, so `ν(Pₙ) ≤ ν(Sₙ)`-type comparison).

**This layer is pure measure/entropy theory — NO manifold, NO Pesin splitting, NO foliation.**

### Layer 2 — the unstable-Jacobian local-entropy estimate (Contractor **Thm 7.15**, eqns (7.17)/(7.18))
For `ν =` Lebesgue volume, for `μ`-a.e. `x`: `h_ν(g,ρ,x) ≥ N(χ(x) − ε)`. This is the geometry:
- Pesin block `K` (μ(K)>0) carrying a measurable continuous splitting `Eˢ(x)⊕Eᵘ(x)` (§5/§7).
- **Birkhoff ergodic theorem** to control the return-time function `N(x)` (first return to `K`) and
  the fraction of orbit outside `K` (`#{j<n : gʲx ∉ K} ≤ 2n√ε`). [Contractor cites Thm 3.6.]
- **Graph-transform Lemmas 7.9 / 7.11 / 7.14** (dispersion-`c` (Eˢ,Eᵘ)-graphs map to graphs under
  `gⁿ`; needs `‖Dgⁿ_x − Dgⁿ_y‖ ≤ Cⁿ‖x−y‖ᵗ`, i.e. **C^{1+α} / Hölder derivative**).
- **Fubini on the unstable disk** + bounded volume `D > vol(gⁿ(Λₙ(y)))` and the unstable-Jacobian
  lower bound `log|det Dgⁿ|_{T_zΛₙ(y)}| ≥ ∑_{j∈Fₙ} log|det Dg|Eᵘ| − εn − NC(n−#Fₙ)` give (7.18):
  `limsupₙ inf_y 1/n[−log ν(Λₙ(y))] ≥ N(χ(x) − ε − 4C√ε) − ε`.

### Capstone (Thm 7.15 → leaf)
Apply Prop 7.7 with `ν = Leb`; **this is exactly where SRB enters**: `ν ≪ μ` is used in Prop 7.7,
and to push the leaf-volume shrink rate back to `μ` one needs `μ`'s conditional measures on `Wᵘ`
absolutely continuous w.r.t. `ν` (the SRB property; Ledrappier–Strelcyn–Young §8 Thm 8.1). Integrate
`h_ν(g,ρ,·) ≥ χ − O(ε)`, let `ε→0`, divide by `N` via `h_μ(gᴺ)=N·h_μ(g)`. Result: `h_μ(g) ≥ ∫χ dμ`.

---

## 3. What EXISTS to help — exact lemma names

### In this project (reusable, sorry-free)
| Asset | Location | Role |
|---|---|---|
| `Oseledets.tendsto_birkhoffAverage_ae`, `…_ae_integral` | `Oseledets/Ergodic/Birkhoff.lean:813,839` | **Birkhoff pointwise ergodic theorem** — needed by Layer 2 (return-time/orbit-fraction control). Mathlib lacks this; project has it. |
| `Oseledets.ae_tendsto_orbit_div_atTop_zero` | `Birkhoff.lean:209` | orbital tail `gⁿ/n → 0` a.e. |
| `MaximalErgodic` lemmas | `Oseledets/Ergodic/MaximalErgodic.lean` | maximal ergodic inequality (Birkhoff engine). |
| `Oseledets.Ergodic.Kingman` (`ae_tendsto_cdiv`, `limsup_cdiv_le_comp`, …) | `Oseledets/Ergodic/Kingman/Core.lean:58,107,278` | subadditive a.e. convergence — the analytic core reused for any `1/n log(...)` limit. |
| `Oseledets.sumPosExp` and `exponents` (Oseledets/MET) | `Lyapunov/Extensions/ExponentSums.lean:74` | the constant `∑λ⁺`; the full MET spectrum. |
| `Oseledets.Entropy.ksEntropy`, `ksEntropyPartition`, `ksJoin`, `entropy`, `MeasurePartition` | `Oseledets/Entropy/*` | finite-partition KS-entropy API (the target's RHS). |
| `Oseledets.margulisRuelle_sharp` | `Entropy/Ruelle/MargulisRuelleSharp.lean` | the proved `≤` direction; same hypothesis shape — a template for the covering/atom-count machinery. |
| Suspension disintegration transfer (`ae_suspensionMeasure_of_ae_base`, …) | `Oseledets/Continuous/SuspensionDisintegration.lean` | demonstrates the project can drive Mathlib's kernel disintegration; a pattern, not the unstable-leaf disintegration. |

### In Mathlib (directly relevant)
| Lemma | Location | Role |
|---|---|---|
| `MeasureTheory.Integrable.tendsto_ae_condExp` | `Mathlib/Probability/Martingale/Convergence.lean:360` | **Lévy upward / L¹ martingale convergence** — the engine of the Prop 7.7 RN step `μ(Pₙ)/ν(Pₙ) → k` a.e. (the only non-trivial analytic input of Layer 1). |
| `MeasureTheory.tendsto_ae_condExp`, `Submartingale.ae_tendsto_limitProcess` | `…/Convergence.lean:426,209` | supporting martingale a.e. convergence. |
| `MeasureTheory.condExp` (`condExp` API), `Measure.rnDeriv`, `Measure.withDensity` | `Mathlib/MeasureTheory/Function/ConditionalExpectation/…`, `…/Decomposition/RadonNikodym.lean` | conditional expectation / Radon–Nikodym derivative for the density `k`. |
| `Measure.condKernel`, `Measure.IsCondKernel`, `…⊗ₘ… = ρ` | `Mathlib/Probability/Kernel/Disintegration/{Basic,StandardBorel,Unique}.lean` | **kernel disintegration** on standard Borel spaces — the abstract form of "conditional measures along a partition"; usable for the σ-algebra `P_∞`, but NOT for a measurable foliation. |
| `Real.negMulLog`, `Real.negMulLog_one`, entropy sums | `Mathlib/Analysis/SpecialFunctions/…` | the `−x log x` Shannon entropy primitives (project's `entropy` is built on these). |
| `MeasureTheory.MeasurePreserving`, `Ergodic`, `Ergodic.ae_eq_const_of_ae_eq_comp₀` | `Mathlib/Dynamics/Ergodic/{MeasurePreserving,Ergodic,Function}.lean` | invariance / ergodic a.e.-constancy. |

### What is **ABSENT** from Mathlib (the wall, confirmed by grep)
- **No Kolmogorov–Sinai entropy** (it lives only in this project, and only as a *finite*-partition
  sup). **No SMB theorem** (`grep ShannonMcMillan` → only the unrelated coding-theory KraftMcMillan).
  **No Brin–Katok**. **No Birkhoff *pointwise* ergodic theorem in Mathlib** (only algebraic
  `BirkhoffSum`/`birkhoffAverage`; the a.e. theorem exists *only in this project*).
- **No Pesin theory whatsoever**: `grep Pesin|Lyapunov|unstable|invariant.*manifold Mathlib/` → empty.
  No measurable `Eˢ⊕Eᵘ` splitting, no stable/unstable manifold theorem, no Lyapunov charts, no Pesin
  blocks, no absolute continuity of foliations / holonomy, no leaf disintegration, no leaf-volume
  growth. None of the Layer-2 inputs exist.

---

## 4. Decomposition into smallest sub-lemmas

| # | Sub-lemma (informal) | Mathlib support | Project support | Difficulty |
|---|---|---|---|---|
| L0 | `(sumPosExp : EReal) ≤ h_μ(T)` ⟸ `∫χ dμ ≤ h_μ(T)` and `∫χ = sumPosExp` (already a.e.-const). Pure plumbing. | n/a | exists (`hbridge` pattern in PesinFormula) | **easy** |
| L1a | **Lemma 7.5/7.6**: from `log ρ ∈ L¹` build a *countable* partition `P`, `H(P)<∞`, `diam P(x) ≤ ρ(x)` a.e. Requires a **countable**-partition entropy API. | absent (only finite partitions) | partial (`entropy` on finite cells; needs countable extension) | **hard** |
| L1b | **Prop 7.7 RN step**: `1/n·log(μ(Pₙ)/ν(Pₙ)) → 0` a.e. for `ν ≪ μ`. | **exists** (`Integrable.tendsto_ae_condExp`, `condExp`, `rnDeriv`) | Kingman/Birkhoff for the `1/n` scaling | **medium** |
| L1c | **SMB**: `h_μ(P,g) = ∫ limₙ 1/n[−log μ(Pₙ(x))] dμ` for the countable `P`. | absent | absent (KS-entropy is Fekete-of-finite-joins; need the pointwise SMB identity) | **research** |
| L1d | **Prop 7.7 assembly**: `h_μ(g) ≥ ∫ h_ν(g,ρ,·) dμ`, combining L1a–L1c + `h_μ(g) ≥ h_μ(P,g)` (a countable partition ≤ sup). | n/a | needs `ksEntropy ≥ countable-partition entropy` (extend `le_ksEntropy`) | **hard** |
| L2a | Pesin block `K`, μ(K)>0, with measurable continuous `Eˢ⊕Eᵘ` splitting + dispersion graphs (Def 7.8). | absent | absent | **research** |
| L2b | Graph transform 7.9/7.11/7.14: dispersion-`c` graphs persist under `gⁿ`; needs `C^{1+α}` Hölder `‖Dgⁿ_x−Dgⁿ_y‖≤Cⁿ‖x−y‖ᵗ`. | absent (have `fderiv`, `ContDiff`; no nonunif. estimate) | absent | **research** |
| L2c | Return-time `N(x)` to `K` well-defined and integrable; orbit-outside-`K` fraction `≤2n√ε` — **Birkhoff**. | absent (no pointwise ergodic) | **exists** (`tendsto_birkhoffAverage_ae`) | **medium** (given the splitting) |
| L2d | Unstable-disk Fubini + Jacobian bound (7.17)/(7.18): `h_ν(g,ρ,x) ≥ N(χ−O(ε))`, `ν=Leb`. | absent | absent | **research** |
| L2e | **SRB bridge**: transfer leaf-volume shrink rate to `μ` via a.c. conditional measures on `Wᵘ` (genuine `SRBProperty`). | kernel disintegration exists; **foliation disintegration absent** | absent | **research** |
| L3 | `h_μ(gᴺ) = N·h_μ(g)` (entropy power rule) + `ε→0` limit assembly. | absent | partial (subadditive/Fekete machinery present; power rule not stated) | **hard** |

**Closeable-now subset:** L0 (trivial), L1b (martingale step — real, self-contained), L2c (Birkhoff
return-time — given a splitting interface). Everything labelled *research* is the Pesin wall; L1a/L1c/
L1d/L3 are "Mathlib-scale but not Pesin" (a countable-partition KS-entropy + SMB development —
substantial but in principle mechanical ergodic theory).

---

## 5. Independent strategies for parallel implementation attempts

1. **Sharper-sorries refactor (recommended primary deliverable).** Do NOT attempt the wall. Replace
   the single `sorry` by the explicit chain `manePropLowerBound` (Layer 1) ∘
   `localEntropy_ge_unstableJacobian` (Layer 2), each its own `theorem … := sorry` with a precise
   type matching §2, plus the sorry-free assembly `L0`/`L3`-plumbing connecting them. Net effect:
   same honesty, but the wall is localized to ~5 individually-typed leaves (L1a, L1c, L1d-or-Prop7.7,
   L2-bundle, SRB-bridge) instead of one opaque blob — exactly the auditable roadmap the issue asks
   for. Low risk, high value; build stays green.

2. **Layer-1 partial close (martingale + countable-partition entropy).** Independently *prove*
   L1b (`1/n·log(μ(Pₙ)/ν(Pₙ)) → 0` via `Integrable.tendsto_ae_condExp`) as a standalone sorry-free
   lemma, and *build the countable-partition entropy API* (extend `MeasurePartition`/`entropy`/
   `le_ksEntropy` to countable index, L1a's `H(P)<∞`). This is genuine, Pesin-free Mathlib-scale work
   that chips real content off Layer 1 without touching the geometry. Leaves SMB (L1c) and the whole
   of Layer 2 as sorries — but converts ~2 of the decomposition rows to green.

3. **SMB as the keystone target.** Attempt the Shannon–McMillan–Breiman theorem itself
   (`h_μ(P,g) = ∫ limₙ 1/n[−log μ(Pₙ)] dμ`) on top of the project's Birkhoff/Kingman + Mathlib
   martingale convergence (the standard Algoet–Cover / Breiman proof routes through exactly these).
   SMB is reusable far beyond this issue and is the single largest non-Pesin gap; landing it
   sorry-free would unblock all of Layer 1. High effort, but it is *ordinary* ergodic theory, not
   nonuniform hyperbolicity — the realistic "hard but not research-wall" target.

4. **Layer-2 interface enrichment (geometry as named data).** Turn `SRBProperty` and
   `UnstableJacobianRate` from stubs into *faithful* `Prop`s (a measurable `Eᵘ : X → Subspace`,
   the orbit Jacobian growth `∀ᵐ x, Tendsto (1/n·log|det Dgⁿ|Eᵘ|) (𝓝 χ)`, and an
   absolute-continuity field stated via Mathlib `condKernel`/`rnDeriv`), then prove L2c (Birkhoff
   return-time) and the Jacobian-summation algebra *from those interfaces*, leaving only the
   existence of the splitting / its a.c. (L2a, L2b, L2d, L2e) as sorries. This makes the SRB
   hypothesis genuinely load-bearing (fixing the current `True`-field honesty gap) and closes the
   purely-combinatorial parts of Layer 2 — without proving any Pesin manifold theorem.

Strategies 1 and 4 are complementary refactors (do both); 2 and 3 are independent
content-landing attempts that can run in parallel.

---

## 6. Honest verdict

This is **not closeable now** as a sorry-free `∑λ⁺ ≤ h`. It is a genuine multi-component wall whose
**core is multi-year, Mathlib-scale Pesin / Ledrappier–Young theory**: a measurable `Eˢ⊕Eᵘ` splitting
on a positive-measure Pesin block, the stable/unstable manifold theorem, the unstable foliation and
**its absolute continuity**, leaf disintegration, and unstable-disk volume growth — *none of which
exists in Mathlib and none of which is short*. The Layer-2 geometry (L2a, L2b, L2d, L2e) is the real
research wall.

**But it is honestly partially decomposable, and the current leaf overstates its own honesty.** Two
findings matter. First, Mañé's proof (the one cited) is the partition-free / stable-manifold-free
route, so **Layer 1 (Prop 7.7) is pure ergodic/measure theory** and its one non-trivial analytic step
(the Radon–Nikodym density limit) is *directly serviced by Mathlib's martingale Lévy-upward theorem*
`Integrable.tendsto_ae_condExp` — that sub-piece (L1b) is plausibly closeable now. The remaining
Layer-1 pieces (a countable-partition KS-entropy API + the SMB theorem) are substantial but *ordinary*
ergodic theory, not nonuniform hyperbolicity, and the project already owns the hard analytic
prerequisites (a real **Birkhoff pointwise** theorem and **Kingman**, both absent from Mathlib).
Second — and this is the honesty flag — the leaf's own hypotheses are stubs: `SRBProperty` exposes
only `acConditionalUnstable : True`, and `UnstableJacobianRate` is merely `χ =ᵐ sumPosExp`, so the
proof *cannot actually consume SRB-ness or the Jacobian growth*. A truthful state of this leaf is
therefore a **sharper-sorry decomposition** (Strategy 1) plus **interface enrichment** (Strategy 4):
split the one `sorry` into the ~5 individually-typed leaves of §4, make the SRB/Jacobian interfaces
faithful, and land the genuinely reachable martingale (L1b) and Birkhoff-return-time (L2c) pieces.
That is the realistic deliverable; a full sorry-free close is years and a Pesin-theory library away.
