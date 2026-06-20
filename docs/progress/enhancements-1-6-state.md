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
| 4 | Ruelle entropy inequality | abstract reduction done; geometric core = wall |
| 5 | suspension / special flow | space-level μ̂-a.e. exponent done; one measurability gap |
| 6 | full singular forward filtration | bottom stratum done; full flag = research-scale |

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
