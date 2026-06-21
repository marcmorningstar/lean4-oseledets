# MET enhancements #1–#6 — branch state (2026-06-20)

> **Living state document** for the `issues/met-enhancements-1-6` branch (GitHub issues #1–#6),
> the counterpart to `STATE.md` (which records the completed main-branch MET). Records current
> target, what is done, what remains, and the next steps. Resumable from alone.

## ⚠️ Orchestration invariants for the goal loop (DO NOT FORGET — survives summarization)

1. **Warm Lean checker is MANDATORY for every Lean worker.** Each Lean-writing agent gets its OWN
   warm `lwt` worktree (`.claude/scripts/lwt add <branch>`, **never** `--no-warm`). Warm leancheck
   (`lake serve` daemon) = the iteration loop; cold-building after every edit is forbidden (too slow).
2. **One cold `lake build <Module>` per agent = the final authoritative gate**, not the inner loop.
3. **One worktree per agent, always** — isolated `.lake/build` ⇒ no `setup.json` race across trees.
4. **Parallel agents encouraged**; run in waves of ~6–8 concurrent warm worktrees (RAM is the binding
   constraint: ~0.5 GB/daemon + ~2–4 GB/coincident build; ~31 GB usable; 32 cores, CPU is not the cap).
5. **Never `sorry`, never axiomatize** (`warningAsError` ⇒ `sorry` fails the build). Partial work stays
   out of the build until it compiles. Every headline keeps a `#print axioms` audit = `[propext,
   Classical.choice, Quot.sound]`.
6. **Workers never run git**; the orchestrator does all merges/commits/pushes + authoritative builds.

Branch `issues/met-enhancements-1-6` @ `613b47a` (pushed, in sync with origin).
Worktrees i4/i5/i6 all synced to `613b47a`. Nothing running; tree clean.

## Headline state

- **62 new sorry-free modules**, **267 guarded axiom checks**, full `lake build` **green**
  (3099 jobs, zero warnings under `linter.mathlibStandardSet` + `warningAsError`).
- Every audited result depends on exactly `[propext, Classical.choice, Quot.sound]`.
- Built via 13 incremental grind rounds + **5 long autonomous campaigns** + earlier QA passes.

## ✅ CAMPAIGN COMPLETE (2026-06-21) — all six issues solved/formalized, full `lake build` GREEN (3140 jobs)

All of #1–#6 are landed in the linted, axiom-audited `Oseledets` library (`linter.mathlibStandardSet` +
`warningAsError`; every headline `#print axioms = [propext, Classical.choice, Quot.sound]`). Phase 2 went
beyond the Phase-1 walls: the Ruelle inequality geometric core and the singular measurable filtration were
**formalized** by building the missing Mathlib-scale infrastructure (top-down via the `Frontier` staging lib,
then migrated). Two independent QA layers (adversarial soundness audit + a 7-lens sweep) returned SOUND; the
7-lens findings (all quality, no correctness defects) were fixed. See `AuditReport.md` for the full accounting.

## Per-issue status

| # | Topic | Status |
|---|---|---|
| 1 | constant-cocycle exponents | **DONE** |
| 2 | derivative (tangent) cocycle | **DONE** |
| 3 | worked examples | **DONE** |
| 4 | Ruelle entropy inequality | **FORMALIZED** — `Oseledets.margulisRuelle_sharp : ksEntropy ≤ Σλᵢ⁺` (full Mañé covering pipeline; honest Riquelme-necessary distortion hyps) |
| 5 | suspension / special flow | **DONE** — fully unconditional space-level flow exponent (`hPmeas` discharged) |
| 6 | full singular forward filtration | **FORMALIZED** — `Oseledets.aemeasurable_orthProjMatrix_lambdaSublevel` (a.e. measurable singular filtration; new infra `AnalyticSet.nullMeasurableSet`) |

> The detailed Phase-1 narrative below records the *journey* (the wall characterization that motivated the
> eventual routes). The Phase-2 closure is summarized at the top and in `AuditReport.md`.

## ⟢ ACTIVE CAMPAIGN (2026-06-20, orchestrated) — grounded plans + Wave 1 in flight

A 3-planner adversarial planning workflow (grounded in frontier code + docs + firecrawl) graded each issue:

- **#5 — `closeable-this-campaign` (confidence HIGH).** Sole remaining gap `hPmeas` (measurability-in-`x`
  of the cover-cocycle convergence set over ℝ-atTop). Key insight: Mathlib has no uncountable-index
  convergence-set lemma, so reduce (deterministic per-`x` set-equality, valid under the bounded roof the
  headline already carries) to the **countable ℕ-indexed** discrete return-time convergence set, where
  `MeasureTheory.measurableSet_tendsto` applies. Planner **cold-built a scratch proof** of the core →
  de-risked. **Wave 1 builds 4 modules** (SuspensionReturnTimeMeasurable → SuspensionExponentSetEquiv →
  SuspensionExponentSetMeasurable → SuspensionFlowExponentFinal) removing `hPmeas` for `Measurable A`.
- **#6 — `substantial-progress` (confidence MEDIUM).** Two **independent det-free infra modules** are the
  committed win: `SingularSubspaceDist` (metric on subspaces via orth-projector difference + CauchySeq from
  summable increments) and `SingularPerDirectionExponent` (EReal per-direction exponent = increment of the
  cumulative `forwardSingularExponent`). The full intermediate flag `V_j` is a **genuine wall**: it needs a
  metric Grassmannian (ABSENT from Mathlib — its `Grassmannian.lean` is the AG functor-of-points) and a
  det-free slow-side gap-rate Cauchy estimate = re-deriving Ruelle Thm 1.6's filtration half without
  invertibility. **Wave 1 builds the 2 infra modules + scaffolds spectral values.**
- **#4 — `infrastructure-wall` (confidence HIGH, triple-confirmed).** Discharging `hgeo` needs Lyapunov
  charts + dynamical covering-count + positive-part singular-value product + orbit-averaging (Mathlib has ONE
  local atom: `Jacobian.addHaar_image_le_mul_of_det_lt`). Independently, **there is no concrete ergodic C¹
  self-map of `EuclideanSpace ℝ (Fin d)` with a probability measure** to even instantiate `hgeo` (repo
  examples live on `AddCircle`/constant cocycles; no n-torus, no hyperbolic-toral ergodicity in Mathlib).
  The abstract reduction `margulisRuelle_le_sumPosExp` is the **honest maximal result**. **Wave 1 = honest
  sharpening only** (positive-part product lemma + minimal atom-count restatement, sorry-free) + precise wall
  documentation. **Not axiomatized, not sorry'd** — that is the quality bar.

**Wave 1 (`wf_26cc6bcc-adb`): 4 parallel `lean-worker`s, one warm `lwt` worktree each.** Orchestrator
integrates green files → wires imports + `#print axioms` audit → authoritative cold `lake build` in the main
checkout → commit/push. Wall modules (#6 `V_j` Cauchy/equivariance, #4 `hgeo`) are a later adversarial wave,
gated hard on sorry-free; they land only if they genuinely compile.

### ✅ WAVE 1 LANDED (authoritative `lake build` green, 3106 jobs, axiom-audited)

7 new sorry-free modules, all `[propext, Classical.choice, Quot.sound]`:

- **#5 — CLOSED.** `Oseledets/Continuous/{SuspensionReturnTimeMeasurable, SuspensionExponentSetEquiv,
  SuspensionExponentSetMeasurable, SuspensionFlowExponentFinal}.lean`. `hPmeas` discharged via
  `measurableSet_coverCocycle_exponent` (ℝ-atTop → countable-ℕ return-time set-equality + `measurableSet_tendsto`)
  ⇒ `ae_suspensionMeasure_hasFlowExponent_of_measurable` / `_flowOrbit_of_measurable`: the space-level
  special-flow exponent `λ_base/∫τ` now needs only `Measurable A` (standard), **no convergence-set hypothesis**.
- **#6 — det-free infra LANDED.** `SingularSubspaceDist.lean` (`subspaceDist` = orth-projector-gap metric;
  `cauchySeq_of_summable_subspaceDist`, `exists_tendsto_orthProjMatrix_of_summable` — summable projector
  increments ⇒ Cauchy ⇒ limit is again an orth projector) + `SingularPerDirectionExponent.lean`
  (`singularDirExponent` EReal per-direction exponent = increment of cumulative `forwardSingularExponent`;
  measurable, a.e. finite-constant). **Worker correctly refused a spec'd theorem that is mathematically FALSE**
  (`singularDirExponent_antitone_ae`: log⁺-clamped cumulative is not antitone — concrete counterexample
  λ^gen=(1,−½,−½,−½)) rather than fake it; `SingularSpectralValues` honestly NOT landed (needs genuine per-σ
  exponents without invertibility). The intermediate flag `V_j` stays a genuine wall (no metric Grassmannian
  in Mathlib + det-free slow-side gap-rate Cauchy estimate = re-deriving Ruelle Thm 1.6 sans invertibility).
- **#4 — honest sharpening LANDED.** `Oseledets/Entropy/MargulisRuelleSharpened.lean`: the positive-part
  singular-value product identity `∑ posLog σᵢ = log ∏ max 1 σᵢ` (det-free, abstract + `toEuclideanLin` forms)
  + `margulisRuelle_le_sumPosExp'` (minimal atom-count restatement making the single open input a per-partition
  counting bound). **`hgeo` NOT axiomatized.** Minimal absent atom recorded for the issue writeup: the dynamical
  covering-count lemma (a C¹ map sends an ε-ball into ≤ C·∏ᵢ max(1,σᵢ(D_xT)) ε-balls, lifted along orbits
  through Lyapunov charts to exp(n(Σλᵢ⁺+ε))) — multi-month Mathlib-scale, correctly left as the open input.

### ✅ WAVE 2 LANDED + #6 WALL PRECISELY CHARACTERIZED (`lake build` green, 3110 jobs)

- **#6 genuine spectrum LANDED:** `Oseledets/Lyapunov/Extensions/SingularSpectralValues.lean` (green,
  sorry-free, axiom-clean). `singularSpectralValue` = the −∞-aware (ENNReal.log) genuine per-direction
  exponent whose increments ARE antitone — `singularSpectralValue_antitone` is **deterministic** (no
  det≠0/integrability/ergodicity), plus `measurable_singularSpectralValue`, `ae_singularSpectralValue_lt_top`,
  the telescoping bridge `log_singularValue_eq_sub_sprod` (holds even on the collapse set), and the
  cut-threshold ladder `exists_cutThresholds` (`exp(2λ_{j+1}) < t_j < exp(2λ_j)`, Gram scale) feeding
  `cocycleSublevelEuclid`.
- **#6 wall, now cold-build-characterized (two independent obstructions):**
  1. **a.e.-constancy of the genuine spectrum** (to extract the distinct-finite-values vector) is blocked via
     Kingman (needs bounded-below; genuine log σ_k → −∞ on collapse). Possible det-free route NOT yet tried:
     sub-invariance `g ≤ g∘T` + measure-preservation + integrability on the finite stratum ⇒ a.e.-invariance
     ⇒ ergodic a.e.-constant. (Subtle: integrability of the −∞-valued limsup.)
  2. **`V_j` limit existence**: the Track-B de-risk PROVED the feared small-σ leakage bound is a non-issue
     (slow projector = `1 − fast` by a cfc-complement identity ⇒ increments equal in norm, all green); the
     REAL wall is a **threshold-scale mismatch** — at a fixed raw-Gram threshold the sublevel family is
     provably NOT Cauchy. The Lyapunov-scale (qpow) fix reuses the existing band engine but needs qpow
     normalized convergence, which itself requires invertibility / a det-free normalized-convergence theory
     (the deep singular-MET obstruction; no metric-Grassmannian Cauchy theory in Mathlib).
  Net: the reachable det-free pieces (kernel stratum + subspace metric + per-direction infra + genuine
  spectrum) are LANDED; the full flag's two remaining atoms are genuine multi-session Mathlib-scale infra,
  the same class as #4's geometric wall. Track-B's reusable structural lemmas
  (`SingularSlowSpaceCauchyScratch`, sorry-free) are kept as the seed for any future flag-assembly wave.

### ✅ WAVE 3 LANDED — spectrum a.e.-constant + V_j structural reduction; wall pinned to ONE lemma

- **#6 spectrum a.e. CONSTANT (det-free) LANDED:** `SingularSpectrumConstant.lean` (green, sorry-free,
  axiom-clean). `ae_singularSpectralValue_eq_const`: for ergodic measure-preserving `T`, the genuine singular
  Lyapunov exponent is a.e. constant (value may be `⊥` on the kernel stratum). The Wave-2 Kingman obstruction
  is bypassed by **sub-invariance + a bounded-monotone transform** (no integrability needed). En route it
  builds genuine new Mathlib-grade infra: `singularValues_comp_le_opNorm` — the **Horn inequality**
  `σ_k(g∘f) ≤ σ_k(g)·‖f‖` (absent from Mathlib, via Courant–Fischer on the repo's `Weyl` machinery) — and
  `limsup_inv_succ_mul_add_le` (the unbounded-below `(n+1)⁻¹→n⁻¹` limsup reindexing).
- **#6 V_j STRUCTURAL REDUCTION (det-free) LANDED:** `SingularSlowSpace.lean` (green, sorry-free). Defines
  the slow-space step `vSlowSingularStep`, proves `measurableSubspace_vSlowSingularStep` + `_antitone`, and
  `tendsto_orthProjMatrix_vSlowSingularStep_of_tendsto_bandProjector`: the slow-space projector CONVERGES
  (⇒ `V_j` exists, measurable) **given** band-projector convergence — reducing the whole flag to one input.
- **#6 WALL pinned to ONE missing det-free lemma:** that input (`Summable ‖bandProj(n+1)−bandProj(n)‖`) is
  supplied unconditionally only by `exists_tendsto_bandProjector_cocycle`, which carries `det ≠ 0`; the det
  enters via a **lower bound on the perturbed top compound eigenvalue** (`norm_sq_compound_mul_ge`,
  Plucker.lean) using the compound **inverse**. The det-free RuelleCore engine supplies only the one-sided
  UPPER leakage envelope, never this lower (aperture/Davis–Kahan gap) bound. Candidate det-free route (genuine
  new math): turn the reverse SVD sandwich `orthogonal_block_mass_symm` into a two-sided aperture bound without
  `‖B⁻¹‖`. This is the fundamental non-invertible-MET obstruction.

### ✅ WAVE 4 LANDED — wall PROVED tight (counterexample); inverse isolated to one per-step scalar

Two independent mathematician angles both reached the same rigorous conclusion. `SingularBandConverge.lean`
(green, sorry-free, axiom-clean) removes `det≠0` from the ENTIRE band-projector increment bound except one
scalar: `numerator_div_gap_le_detfree` (det-free gap-denominator collapse, replacing the compound condition
number `κ=cB·cBi` by `cB/s`), `norm_bandProjector_succ_sub_le_detfree` (det-free per-step increment, consuming
only the residual `hμ₀lb : s²cM² ≤ μ̃₀`), and `tendsto_vSlowSingularStep_of_bandProjector_detfree`
(band-convergence ⇒ `V_j` convergence, unconditional). **The residual is one inequality**
`(R) ‖compound k (B·Mₙ)‖ ≥ s·‖compound k Mₙ‖` with `s` bounded below.

**PROVED (not just unmet):** the maximal det-free coefficient is `s = σ_min(compound k B) = 1/cBi` EXACTLY —
so the inverse is genuinely structural, not generic overkill. Explicit COUNTEREXAMPLE to the forward-bound
hope: `k=1, B=½I, M=I ⇒ μ̃₀=¼ < 1=cM²`. The expanding-top-k insight controls the TIME-AVERAGE
`(1/n)log‖Λᵏ cocycle‖ → λ₁+…+λₖ`, not the per-step ratio a single contracting step pushes below 1; and the
reverse SVD sandwich is mass-SYMMETRIC (no lower bound). So neither forward growth nor the reverse sandwich
removes the last inverse per-step. **The ONLY escape is an AMORTIZED (windowed, multi-step) det-free lower
mass envelope** — the genuine mathematical core of the non-invertible MET filtration (Ruelle Lemma 1.4 without
inverses), where the cut-above-kernel structure + ergodicity control the bad collapse set over a window. That
is Wave 5's target; the per-step route is now a closed, characterized wall.

### ✅ WAVE 5 LANDED — tempered-class V_j + the amortized route PROVED walled too

`SingularSlowSpaceUnconditional.lean` (green, sorry-free, axiom-clean):
- **Unconditional soft-analysis core** `tendsto_vSlowSingularStep_of_summable_increment`: ANY per-step band
  increment bound `b` with `(1/n)log b → L<0` ⇒ `V_j` converges to the explicit complement `1−Pfast` (no det,
  no tempering — pure root test + the landed structural reduction).
- **Tempered-class V_j** `tendsto_vSlowSingularStep_of_tempered`: `V_j` converges (measurable + antitone) on
  the tempered-non-degeneracy class `∀ᶠ n, σ_min(compound k A(Tⁿx)) ≥ exp(−εn)` — **strictly weaker than
  `det≠0`** (allows `σ_{k+1}=…=σ_d=0`), via the a.e.-constant spectrum for the strict gap.
- **The wall, PROVED as a sorry-free identity** `bandProjector_increment_eq_aperture`: the band increment
  EQUALS the aperture `‖VVᵀ−UUᵀ‖` between consecutive top-k right-singular frames — a between-step ROTATION
  governed by `cond(B)` (the inverse), NOT the within-step forward ratio `σ_{k+1}/σ_k`. So the forward-ratio
  crack is mathematically FALSE; the amortized/windowed variant inherits the same window-condition-number, also
  walled. The per-step AND amortized band routes are both closed.

**The ONLY remaining route to the unconditional general-singular `V_j` (Wave 6 target):** abandon the
Cauchy/aperture construction entirely and define `V_j := {v : lambdaBar A T x v ≤ c}` directly from the
pointwise forward exponent (det-free), then prove that sublevel set is a MEASURABLE subspace + antitone +
equivariant. The existing `vslow`/`measurableSubspace_vslow` (ForwardV.lean) is NOT reusable — it is built on
`lambdaHat = sanitized oseledetsLimit`, whose convergence needs invertibility (junk for singular). So the open
problem is precisely the **measurable selection of the limsup-sublevel subspace `{v : λ̄ ≤ c}` for singular
cocycles** — which the kernel stratum dodged via monotonicity (`eventualKer` = monotone ⨆), but the finite
strata are non-monotone. This is the classical non-invertible measurable-Oseledets-filtration problem (KRN
selection, absent from Mathlib). Wave 6 either cracks it via the CFC/spectral-projector technique or pins it.

### ✅ WAVE 6 LANDED — algebraic forward filtration + measurability wall PINNED from all routes

- **#6 algebraic forward filtration LANDED:** `SingularLambdaBarFiltration.lean` (green, sorry-free,
  axiom-clean). `lambdaBarSublevel` (the slow subspace `{v : λ̄ ≤ c}`, as an `IsUltrametricGrowth.sublevel`
  submodule), `lambdaBarSublevel_antitone`, `lambdaBarSublevel_equivariant`, `mem_lambdaBarSublevel_iff`, the
  floored non-Archimedean growth inequality `lambdaBar_add_le_max_zero`. The worker CORRECTED the spec (it was
  false as literally posed): for a singular cocycle the raw `{λ̄ ≤ c}∪{0}` is NOT a submodule for `c<0`
  (counterexample `A=diag(½,0)`: `log 0 = 0` junk makes two decaying vectors sum to a non-decaying one), so the
  honest construction floors growth at 0 and carries the minimal det-free finiteness hypothesis
  `HasFiniteTopGrowth` (a.e.-true by Furstenberg–Kesten).
- **#6 measurability reduction LANDED + wall PINNED:** `SingularLambdaBarMeasurable.lean` (green, sorry-free).
  `measurableSubspace_of_tendsto_orthProjMatrix` (general: measurable projector limit ⇒ measurable subspace) +
  `measurableSubspace_lambdaSublevel_of_tendsto` + `orthProjMatrix_vSlowSingularStep_tendsto_iff_bandProjector`
  prove `{v : λ̄ ≤ c}` is measurable GIVEN projector convergence — and that convergence is provably the SAME
  band/aperture limit walled by `bandProjector_increment_eq_aperture` (one rank-dropping step makes it O(1)).
  So the direct-exponent route does NOT escape; it reduces to the identical inverse wall. The two genuinely
  missing Mathlib facts are named: (1) continuity of sorted Hermitian eigenvalues/eigenvectors; (2) a
  normalized singular-Gram (qpow) limit at a gap cut (−∞-aware).

## ⊨ #6 — DEFINITIVE TERMINAL STATE (all reachable det-free content landed; one wall, characterized 3 ways)

**LANDED, sorry-free, axiom-clean** (the genuine singular forward MET content reachable in pinned Mathlib):
- Genuine singular Lyapunov **spectrum**: per-direction exponent (`singularSpectralValue`), deterministically
  ANTITONE, measurable, **a.e. CONSTANT** (`ae_singularSpectralValue_eq_const`), with cut-threshold ladder —
  plus the new **Horn inequality** `singularValues_comp_le_opNorm` (Mathlib-absent, built via Courant–Fischer).
- **Bottom (kernel) stratum**: `eventualKer` measurable + equivariant + measurable dimension (prior work).
- **Algebraic forward filtration**: `lambdaBarSublevel` submodule, antitone, equivariant, growth dichotomy.
- **Tempered-class measurable `V_j`**: converges/measurable/antitone on the tempered-non-degeneracy class
  (strictly weaker than `det≠0`); the whole flag reduced to ONE convergence input.
- Subspace metric + Cauchy machinery; det-free band-increment bound with the inverse isolated to one scalar.

**THE ONE WALL (genuine research frontier, characterized from all 3 independent constructions):** the
UNCONDITIONAL general-singular measurable flag needs a det-free lower bound on the per-step top-k compound
eigenvalue. PROVED tight (counterexample `B=½I`): the band increment EQUALS the between-step frame aperture =
`cond(B)` (the inverse); a single rank-dropping step (allowed when `det=0`) makes it O(1). The amortized and
the direct-exponent-sublevel routes both REDUCE to this same limit. Escaping it needs either KRN measurable
selection or a normalized singular-Gram convergence theory — both absent from Mathlib, genuinely multi-session
(the classical non-invertible measurable-Oseledets-filtration problem; cf. Froyland–Lloyd–Quas semi-invertible
MET, which assumes base invertibility for exactly this reason). NOTHING faked or axiomatized.

### #5 — suspension / special flow (substantially closed)
- **Space-level headline proved:** `ae_suspensionMeasure_hasFlowExponent` — for μ̂-a.e.
  `q ∈ SuspensionSpace`, the representative-free flow exponent `HasFlowExponent q (λ_base/∫τ)`.
- Chain: bounded-roof section exponent (all flow times) → disintegration (base-a.e. → μ̂-a.e.) →
  growth-rate orbit re-basing + limit transfer → `HasFlowExponent` well-defined on orbit classes →
  μ̂-a.e. value.
- **`hmeas` discharged** (`measurableSet_suspensionMk_image`: quotient image of a measurable set is
  measurable, via the countable ℤ-orbit saturation) → `ae_suspensionMeasure_hasFlowExponent_unconditional`,
  plus `_flowOrbit` (tied to the genuine `suspensionFlow` `MeasurePreservingFlow`).
- **REMAINING (reachable):** `hPmeas` — measurability in `x` of the base exponent SET
  `{x | log‖coverCocycle (x,0) t‖/t → L}`. Needs a `coverCocycle` measurability-in-`x` lemma
  (the "FlowCocycle keystone"). This is genuinely reachable: the convergence set of a jointly-measurable
  family is measurable (reduce `atTop` over ℝ to a countable cofinal ℚ-sequence). **Best next step for #5.**

### #6 — full singular forward filtration (bottom stratum closed)
- **Bottom (kernel) stratum DONE:** `measurableSubspace_eventualKer` — `x ↦ eventualKer A T x` is a
  `MeasurableSubspace`, via the CFC spectral-projector route (orth proj onto ker = ≤0 spectral projector
  of the Gram `MᵀM`, measurable via the repo's `measurable_spectralProjector`) + monotone star-projection
  limit. **Sidesteps Kuratowski–Ryll-Nardzewski (absent from Mathlib) entirely.** Plus measurable
  DIMENSION (`measurable_eventualKerDim`, with the new determinantal minor-rank lemma
  `le_rank_iff_exists_submatrix_det_ne_zero`) and algebraic equivariance.
- **Threshold generalization:** `measurableSubspace_cocycleSublevel` — same technique at arbitrary
  threshold `t` (per fixed `n`).
- **REMAINING (research-scale):** the intermediate slow spaces `V_j` of the full flag need (a) the
  positive-threshold n→∞ stabilization (the fixed-`t` sublevel family is non-monotone, so the kernel's
  monotone-limit does not transfer), and (b) pinning thresholds to actual singular-value/Lyapunov GAPS —
  which needs the Kingman/exterior-power exponent identification, not currently wired. Genuinely multi-step.

### #4 — Ruelle entropy inequality (abstract scaffolding done)
- **Abstract reduction proved:** `margulisRuelle_le_sumPosExp` — `ksEntropy ≤ sumPosExp`, CONDITIONAL on
  the genuine per-partition Ruelle counting hypothesis `hgeo` (`h(T,P) ≤ Σλᵢ⁺` for every finite
  partition; verified `ksEntropyPartition` is the dynamical Fekete entropy, so `hgeo` is satisfiable and
  NOT a disguised conclusion; the `iSup_le` packaging is legitimate scaffolding).
- Full abstract entropy stack present: KS entropy, Fekete limit `h(α,T)`, system entropy `h(T)=⨆_α`,
  subadditivity, refinement-monotonicity.
- **REMAINING (wall):** discharging `hgeo` unconditionally needs smooth-manifold ergodic theory absent
  from Mathlib (Riemannian volume, Jacobian/`det Df`, Lyapunov charts, the Mañé/Katok covering-counting
  argument). Multi-month; correctly left as an explicit hypothesis, never sorry'd or axiomatized.

## Pipeline / architecture changes made this session

1. **Long autonomous campaigns** replace one-module-per-workflow. A campaign = a sequence of modules,
   each drafted + **self-cold-built** (`lake build <Module>` compiles an *unwired* module by name,
   authoritative ~30–60 s) + adversarially verified, then a sole **integrator agent** wires all imports +
   `#print axioms` audit blocks and proves the full build green. The orchestrator only does `git
   merge`/`push`. Scout→build variant: an opening agent surveys infra and returns a structured module
   plan the workflow then builds. (Scripts under `.firecrawl/wf-*.js`.)
2. **Collision-free per-agent worktrees** (your request): `.claude/scripts/new-agent-worktree.sh` +
   `remove-agent-worktree.sh`. Symlinks the shared 5 GB Mathlib cache (`.lake/packages`) and gives each
   worktree a PRIVATE `.lake/build` copy (~263 M, ~17 s) → the `setup.json` race is structurally
   impossible. Verified: provision 17 s, single-module build with zero Mathlib rebuild, teardown 0.18 s.
   Reflink falls back to copy on overlayfs. Chosen over N=32 preallocation (lifecycle/lease complexity).

## Recommended next steps (prioritized)

1. **Multi-lens QA pass on the 62 new modules.** A read-only fan-out of distinct lenses
   (vacuity, hypothesis-necessity, soundness spot-check, style/lint/dup, naming/doc/reference accuracy,
   axiom/sorry integrity) + synthesis → triaged findings → fix. The lens design is specified above;
   the workflow script is not currently on disk (to be re-scripted when the pipeline work resumes).
2. **#5 `hPmeas` discharge** — build the `coverCocycle` measurability-in-`x` lemma and the
   measurable-convergence-set lemma → fully unconditional space-level flow exponent. Most reachable
   remaining headline piece.
3. **#6 intermediate flag (`V_j`)** — needs the exterior-power/Kingman exponent-to-gap bridge wired first;
   then the sublevel-projector technique extends. Multi-step but the measurability tooling is in place.
4. **#4 geometric bridge** — genuinely multi-month; would need a Mathlib-scale smooth-ergodic-theory
   build (Riemannian volume, Lyapunov charts). Out of one-shot reach; the abstract scaffolding already
   isolates exactly the one geometric atom.

## Pipeline-improvement notes (for your tuning)

- Agents self-cold-building single modules is the highest-leverage change — it caught real errors warm
  leancheck can't see on unwired files (`mul_nonsing_inv_cancel_right _ _ h` arg arity; `dotProduct` is
  root namespace; matrix-entry measurability needs the explicit `Matrix`-typed `hentry`). Keep it.
- Integrators occasionally hit `#guard_msgs` print-width line-wrap on long theorem names (the expected
  `/-- info: ... -/` must match the wrapped `[propext,\n Classical.choice,\n Quot.sound]`). They self-fix
  it, but a helper that emits the audit block in the correct wrap would save a round.
- Merge conflicts only ever occur in the two index files (`Oseledets.lean`, `test/AxiomAudit.lean`) at the
  append point — always a trivial union. A per-issue audit-section convention (stable anchors) would make
  these conflict-free.
- With per-agent worktrees now available, campaigns can give each module-draft its own tree and build in
  parallel (no within-worktree serialization needed) — a further speedup not yet adopted.
