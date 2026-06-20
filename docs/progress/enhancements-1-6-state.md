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

## Per-issue status

| # | Topic | Status |
|---|---|---|
| 1 | constant-cocycle exponents | **DONE** |
| 2 | derivative (tangent) cocycle | **DONE** |
| 3 | worked examples | **DONE** |
| 4 | Ruelle entropy inequality | abstract reduction **+ sharpening** done; geometric core = wall (documented) |
| 5 | suspension / special flow | **DONE** — fully unconditional space-level flow exponent (`hPmeas` discharged) |
| 6 | full singular forward filtration | bottom stratum **+ det-free subspace/per-direction infra** done; full flag = wall |

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
