# CONTINUATION STATE — Oseledets frontier issues #8–#11

**This file is the single self-contained handoff.** Attach a new session to it ("read
`reports/CONTINUATION-STATE.md` and continue") and everything needed is here: role, infra, invariants,
current residuals (file:line), measured priorities, the method that worked, and the exact next actions.
Last updated 2026-06-22 (#8 AND #9 closed unconditionally + migrated into the linted `Oseledets`
library; only #11 and #10 remain). #9's chart-regularity wall fell to a measurable fixed-chart frame.

---

## 1. Role & goal

You are the CEO/orchestrator of an autonomous Lean 4 + Mathlib formalization campaign on
`marcmorningstar/lean4-oseledets`. You **delegate** to parallel `lean-worker`/`mathematician` agents in
warm git worktrees and **observe from the top**; you personally do all git/merges/authoritative builds.

The core Oseledets MET is COMPLETE. The open work is 4 research-level strengthenings = `BLOCKED` `sorry`
leaves in the unlinted `Frontier.Issue*` staging lib (GitHub issues #8/#9/#10/#11). A prior campaign
drove each from an opaque sorry to a small, sharp, literature-attributed residual — all faithful, no
unsoundness, `lake build` green, axiom audit unchanged. **Goal of a continuation run: close residuals,
sorry-free.**

## 2. Current state (branch `campaign/issues-8-11`, draft PR #12)

Residual sorries (authoritative — from `lake build` warnings, not docstring greps):

| Issue | File:line | Status |
|---|---|---|
| **#8** | `Oseledets/Lyapunov/Extensions/Yamamoto.lean` | ✅ **CLOSED sorry-free + MIGRATED to the linted lib** (proof `bf92e09`; migration `654837e`+`e874e6d`). `compoundMatrix_charpoly_roots_eq` proved via new `Frontier/Issue1/Schur.lean` (ℂ-Schur, a correctly-attributed Apache-2.0 graft of `leanprover-community/physlib`'s `Mathematics/SchurTriangulation.lean`) + functorial Cauchy–Binet (`compoundAbstract_mul` via `exteriorPower.map_comp`) + triangular-minor det lemmas + diagonal→`powersetCard` bridge. Axiom audit clean on the target + `yamamoto_singularValues_tendsto`/`exponents_const_general`/`spectralRadius_compound_eq_prod_eigenvalueModuli`. **✅ MIGRATED to the linted `Oseledets/` library**: Schur delinted into the quarantined shim `Oseledets/Mathlib/SchurTriangulation.lean` (physlib attribution kept, `autoImplicit`→explicit per-section `variable`s — incl. a shared `universe u` for the `cond b m n` instances and a decl-level `{E}` on `SchurTriangulationAux.of`); Yamamoto at `Oseledets/Lyapunov/Extensions/Yamamoto.lean` (import re-pointed, lines wrapped, `push_neg`→`push Not`). Both imported from `Oseledets.lean`; 4 `#print axioms` guards in `test/AxiomAudit.lean` confirm `[propext, Classical.choice, Quot.sound]`. Full `lake build` green under `warningAsError`; `Frontier/Issue1` removed. **#8 fully done.** |
| **#9** | `Oseledets/Smooth/{FrameAlg,Framing,UnconditionalFraming,UnconditionalMET}.lean` | ✅ **CLOSED UNCONDITIONALLY + MIGRATED to the linted lib** (`356c731`+`2f1aa5b`+`081cd50`). The `LocallyConstantChartAt` hypothesis is **GONE**. Breakthrough: `MeasurableFraming` needs only the *conjugated generator* measurable, not the frame — so a **piecewise fixed-reference-chart** frame over a disjointified countable atlas makes `framedGenerator` equal the fixed-chart `fderivWithin(extChartAt b ∘ T ∘ (extChartAt a).symm)` (continuous, C¹), measurable on the countable Borel partition; the moving `chartAt` cancels algebraically, so NO chart regularity is needed. Delivered: `exists_measurableFraming_of_sigmaCompact` (no LCC) + the framed-cocycle MET `oseledets_filtration_framedTangentCocycle`/`exists_oseledets_filtration_framedTangentCocycle` (`hAmeas` discharged unconditionally). 3 `#print axioms` guards = the standard triple; `lake build` green under `warningAsError`. Superseded LCC chain (`LocallyConstantChartAt`/`MFDerivMeasurable`/`Existence`/canonical `DerivativeCocycleManifold`) removed; `Frontier/Issue2` deleted. **#9 fully done.** |
| **#10** | `Frontier/Issue4Pesin/ManeLowerBound.lean:177,208` | ⛔ **OPTIONAL EXTENSION, consumer-irrelevant (orphaned)** — recon 2026-06-22. The Pesin entropy formula, downstream of the completed MET; `import Frontier` in `Oseledets.lean` = 0, nothing consumes it. The EASY Margulis–Ruelle direction (`h ≤ Σλ⁺`) is ALREADY shipped sorry-free in the lib (`Oseledets.margulisRuelle_sharp`, `Oseledets.lean:154`). The 2 sorries are EXCLUSIVELY the hard SRB direction (`Σλ⁺ ≤ h`) AND rest on a VACUOUS hypothesis (`SRBProperty = {acConditionalUnstable : True}`) + `opaque localNuEntropy` — not honest lemmas; closing needs the full ~4–6-month foliation sub-library (9-node serial chain, no Mathlib precursors). No #9-style shortcut. DON'T grind; quarantine. |
| **#11** | `Frontier/Issue6/ArseninKunugui.lean:301` (+ `CastaingSelection.lean:479`, `MeasurableGraphToProjector.lean:405`) | ⛔ **OPTIONAL upstream enhancement, consumer-irrelevant (orphaned)** — recon 2026-06-22. The leaf `exists_borel_openSection_structure` (Srivastava 4.7.2) genuinely needs the missing coanalytic pointclass + reduction theorem 4.6.5 (no shortcut — analytic ⊉ Borel; "provably fails" CONFIRMED). BUT the MET never imports/needs the AK chain (`import Frontier` in `Oseledets.lean` = 0): the a.e. filtration is AK-free (`aemeasurable_orthProjMatrix_lambdaSublevel`) and the everywhere-Borel filtration `oseledets_filtration` produces is AK-free via explicit `measurable_slowProjector` (not graph projection). `measurableInfDist_of_measurableGraph` has no consumer. DON'T grind; Mathlib-upstream nicety only. |

Headline signatures faithful vs pre-campaign `origin/main` except the documented, approved additions:
#8 benign `[NeZero d]`. **#9 carries NO added hypothesis** — the earlier `[LocallyConstantChartAt H M]`
was superseded and removed (the result is now unconditional). No `axiom`/`native_decide`/`admit`/
`sorryAx`/`implemented_by` anywhere. **Lessons:** (1) a sharp-looking isolated `sorry` is not
automatically a *true* lemma — re-verify the *statement*; (2) a campaign "wall" may be an
over-constraint — #9 fell once we used a **measurable** fixed-chart frame instead of forcing the
moving-index map *continuous*. Re-examine each wall for an architectural shortcut before declaring it
Mathlib-scale (this directly cracked #9, rated "days–weeks Mathlib-scale", in one run).

## 3. Measured priority queue (from the dependency-DAG spike — critical-path depth × parallel width)

Ranked by **measured** effort (DAG reports `docs/research/frontier/issue{4,6}/DAG-*.md`, Mathlib
node-availability grep-verified + adversarially audited). Parallel-Claude wall-clock ≈ critical-path
depth × per-node design+prove time (breadth is absorbed by running many warm agents at once).

**#8 and #9 are both COMPLETE** — sorry-free, migrated into the linted upstreamable `Oseledets`
library, axiom-audited, and **closed on GitHub**. #8: proof `bf92e09`, migration `654837e`+`e874e6d`.
#9: **UNCONDITIONAL** (no `LocallyConstantChartAt`), `356c731`+`2f1aa5b`+`081cd50`. Remaining open work, ranked:

| Priority | Target | Parallel-Claude | Notes |
|---|---|---|---|
| **✅ DONE** | **#8 → `Oseledets/`** | done (`654837e`+`e874e6d`) | Migrated: Schur vendored as the quarantined `Oseledets/Mathlib/SchurTriangulation.lean` shim (delint-only — `autoImplicit`→explicit per-section `variable`s incl. a shared `universe u` for the `cond` instances + decl-level `{E}` on `.of`; `push_neg`→`push Not`), Yamamoto at `Oseledets/Lyapunov/Extensions/Yamamoto.lean`, 4 axiom guards added, `Frontier/Issue1` removed. `lake build` green under `warningAsError`. |
| **✅ DONE** | **#9 unconditional** | done (`356c731`+`2f1aa5b`+`081cd50`) | `LocallyConstantChartAt` was NOT needed: a piecewise fixed-reference-chart frame makes `framedGenerator` a fixed-chart `fderivWithin` (continuous C¹, measurable unconditionally), since `MeasurableFraming` requires only the *generator* measurable. Migrated to `Oseledets/Smooth/`, axiom-audited, closed. The over-constraint was forcing the moving-index map *continuous*; **measurable** suffices for the MET. |
| **N/A** | **#11** | DON'T grind | **Orphaned optional enhancement** (recon 2026-06-22). Real Mathlib gap (coanalytic reduction 4.6.5) for the leaf, but the MET is AK-free everywhere it needs measurable filtrations; no consumer. Leave quarantined; possibly upstream the sorry-free by-products (4.7.4 / proper-map wiring) to Mathlib. |
| **N/A** | **#10** | DON'T grind | **Orphaned optional extension** (Pesin formula; recon 2026-06-22). ~4–6 months, 9-node serial foliation chain, no shortcut. The easy Ruelle direction is already shipped (`margulisRuelle_sharp`); the residual SRB sorries rest on a vacuous `True` hypothesis + `opaque` target. Quarantine. |

**RUN OUTCOME (2026-06-22): all four frontier issues driven to their honest conclusion.**
**#8 + #9 CLOSED** — unconditionally, migrated into the linted upstreamable lib, axiom-audited, GitHub-closed.
**#10 + #11 RECLASSIFIED** by skeptical #9-style recons from "blocked dependency" to **consumer-irrelevant
optional strengthenings**: neither is imported or needed by the completed MET (`import Frontier` in
`Oseledets.lean` = 0), and neither has a #9-style shortcut — #11's leaf needs a genuinely missing Mathlib
chapter (coanalytic reduction 4.6.5), and #10's residual is the irreducible ~4–6-month SRB/foliation
direction sitting on a vacuous (`True`) hypothesis stub. **No further productive autonomous grinding
remains** — the achievable frontier is complete; #10/#11 are quarantined optional enhancements (left
open on GitHub with reclassification comments, not auto-closed). Future *optional* work only:
(a) upstream #11's sorry-free DST by-products to Mathlib; (b) the `N-L1-RN` ~1-session Pesin sub-win
(off critical path, doesn't move the headline); (c) when Mathlib gains its own Schur decomposition, drop
the `Oseledets/Mathlib/SchurTriangulation.lean` shim and re-point `Yamamoto`.

## 4. Infrastructure (all verified working)

- **`gh`** is installed + authenticated — use it for issues/PRs. (`gh pr edit` may hit a Projects-classic
  GraphQL bug → PATCH via REST API with a token from `git credential fill`, host github.com.) Refs #8–#11,
  don't auto-close.
- **Warm lean-worker:** `.claude/scripts/lwt add <branch>` → warm worktree under `/home/vscode` (Mathlib
  cache symlinked — NEVER let a build recompile Mathlib; the `ContMDiffMFDeriv` subtree IS cached, fine to
  import). Prereq: leancheck plugin installed (`claude plugin install leancheck@lean-tools`). Subagents may
  run `lwt` but are git-BLOCKED (`.claude/hooks/block-subagent-git.sh`); leancheck auto-reports after each
  worker edit. Pre-provision worktrees **serially** from the orchestrator (avoids a `git worktree add` race).
- **firecrawl** CLI preconfigured for literature (`firecrawl search/scrape/map`).
- **RAM ceiling:** ~6–8 concurrent warm builds safe (32 cores, ~25 GB free; user OKs up to 15 agents,
  stagger cold builds). Resource watchdog templates in `reports/infra/`.
- **Build gates:** `lake build Frontier.<Module>` (staging, sorry-OK) for iteration; `lake build`
  (default `Oseledets`+`AxiomAudit`+`Frontier` root, must stay green) as the library gate.

## 5. Invariants (never violate)

1. Every Lean worker gets its OWN warm `lwt` worktree.
2. **Workers never run git**; the orchestrator does all merges/commits/pushes + authoritative builds.
3. Never `sorry`/axiomatize in the imported `Oseledets` lib. Partial work stays in `Frontier.Issue*`.
4. **Migrate `Frontier.Issue*` → `Oseledets/` only when fully sorry-free**, then keep
   `#print axioms = [propext, Classical.choice, Quot.sound]`.
5. Don't weaken a headline to "close" it; honest added hypotheses are OK but must be documented + QA-checked.
6. Multiple adversarial QA passes; commit + push at every milestone; report progress to files + issues.

## 6. Method that worked (reuse it)

Background **Workflow** super-workflows in waves: `pipeline(implement → mathematician QA)`, with
`agentType:'lean-worker'` for impl and `agentType:'mathematician'` for adversarial QA, forced structured
schema output. **Tournament**: run 2–3 independent attempts per wall (distinct strategies), keep the best
branch (they touch the same file in separate worktrees → no conflict, you merge one). Integrate by copying
the winning (disjoint) files into the campaign branch, authoritative-build, commit, push. Tear down
worktrees + monitors at the end. The campaign ran recon → 3 implementation waves → a DAG spike; ~35 agents,
0 RAM alerts.

## 7. Pointers
- Narrative retrospective: `reports/CAMPAIGN-FINAL-REPORT.md`
- Per-wave detail: `reports/implementation/WAVE1-RESULTS.md` + workflow outputs
- Feasibility recon: `docs/research/frontier/issue*/FEASIBILITY-*.md`
- Measured DAGs: `docs/research/frontier/issue{4,6}/DAG-*.md`
- Memory: `memory/frontier-campaign-infra.md`, `memory/frontier-campaign-outcome.md`
