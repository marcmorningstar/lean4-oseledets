# Stage A — phase 2 plan (serial, riskier refactors)

Resumed 2026-06-15, worker model = Opus. Phase 1 (per-file mechanical cleanup) is
done file-by-file; phase 2 is the cross-file refactoring a Mathlib reviewer requires.
Execute SERIALLY, each step its own full `lake build` + axiom audit + commit. Verifier:
`lake env lean -DautoImplicit=false -Dlinter.mathlibStandardSet=true -Dlinter.unusedSectionVars=true -Dlinter.unusedVariables=true -Dlinter.style.longFile=1500 <FILE>`

## LESSON (do not repeat): workers must NEVER run git
A phase-1a worker ran `git reset` and wiped 6 other workers' edits (reflog
`reset: moving to HEAD`). All worker prompts now carry an absolute no-git rule; the
ORCHESTRATOR does all git. Keep this rule in every future worker prompt.

## Step 1 — Fossil deletion (SAFE; do first)
6 files unreachable from {MultiplicativeErgodic, Corollaries} (only the root aggregator
imports them), 2406 lines:
  CapstoneTelescope(259), Fischer(286), ForwardFrames(411), ForwardOverlap(485),
  ForwardSubcoboundary(332), ForwardTempering(633).
Action: `git rm` the 6, delete their `import` lines from `Oseledets.lean`, rebuild.
DECISION on Fischer: it is genuinely useful standalone math (Fischer determinant
inequality) but unused by the proof. Default = delete with the rest (clean candidate);
if keeping, re-home `namespace Fischer` → `Matrix.PosSemidef` and keep it reachable.
NOTE: also reconsider reachable-but-superseded modules per style-review §architecture
(AssemblyChain holds `oseledets_filtration_dim_zero` — relocate before any deletion;
ForwardGradedOverlap is imported by the sound ForwardGradedOverlapTopGap — keep).

## Step 2 — Giant-file splits (>1500-line longFile cap) + fix their warnings
- OseledetsLimit.lean (3668) — ALSO carries ~60 build warnings (50 unusedSectionVars,
  7 `toEuclideanLin_apply`→`toLpLin_apply`, 2 `tendsto_finset_sum`→`tendsto_finsetSum`,
  2 unused simp args, ring-does-nothing, unused vars). Split seams (style-review):
  singular-value/Gram infra (56-420), per-exponent limits (420-715), band-projector
  convergence (729-2178), unconditional convergence+assembly (2179-3322), named limit Λ
  + eigen-data (3322-3668). Keep `namespace LinearMap` extension lemmas (correct pattern).
- Kingman.lean (3412) — split into 4: cocycle/Fekete (1-340), Fatou/integrability
  (340-700), Derriennic maximal ineq + M-block (702-2980, splittable at ~1358),
  core+assembly (2981-3412). Headline names tendsto_kingman(_ergodic) — see Step 4.
- ExteriorNorm.lean (2711) — split at its headers: det-Gram/Hodge (231-771),
  compound/Plücker (772-2328), Davis–Kahan/Rayleigh (1353-1741), Weyl (2500-end). Re-home
  `namespace ExteriorNorm` and `namespace Weyl` here (→ Oseledets.* or exteriorPower/Matrix).
  Has 6 maxHeartbeats bumps needing comments.
Put split pieces under Oseledets/Lyapunov/<Dir>/ or Oseledets/Ergodic/Kingman/; update
Oseledets.lean imports + any downstream imports.

## Step 3 — Namespace re-homing (non-fossil, non-correct ones)
Correct, KEEP: LinearMap (OseledetsLimit), Matrix (Corollaries), IsUltrametricGrowth.
Re-home:
  Ruelle13   (ChainRecursion, RuelleCore, RuelleReverse; 6 ref files) → Oseledets.Ruelle (or fold into Oseledets)
  SVDData    (ChainRecursion, RuelleCore; 5 ref files)               → Oseledets.SVDChainData (descriptive)
  ChainCore  (TopGapEnvelope; 1 ref file)                            → Oseledets.* 
  ExteriorNorm / Weyl  → during the ExteriorNorm split (Step 2)
Each: rename `namespace X` + every `X.` reference across the ref files; rebuild.

## Step 4 — Declaration renames (style-review §naming; ~22 thm + ~8 def)
Public theorems named after hypothesis-slot/milestone → conclusion-descriptive:
  hub_of_growthFunction, hslowflag_of_upper (AssemblyFromUpper);
  hbridge_of_forward_graded (BridgeWiring);
  hgrowth_of_upper_lower, hspec_of_spectrum_const (FiltrationAssemblyBridge);
  hbdd_of_fk, hlb_of_bandProjector, hgrowth_of_fk_and_band (ForwardLowerWiring);
  hmeas'_V', hae_of_slowflag (SlowFlagBridge);
  hub_spec_of_slowflag, hlb_spec_of_slowflag, hlb_of_slowflag_ident (SpectrumResiduals);
  hspecconst_of_subsets, hspec_of_subsets, hspecconst_of_lambdaBar, hspec_standing (SpectrumConstancy);
  hov_rate_of_telescope_output (CapstoneTelescope — FOSSIL, moot);
  perStratum_step, perStratum_strongInduction (TopGapEnvelope);
  forward_graded_overlap' (ForwardGradedOverlapTopGap);
  tendsto_inv_mul_log_norm_cocycle_apply_of_S4 (Forward).
Def renames: Vflag→lyapunovFlag, Vslow→slowSubspace, Vassembled→assembledFlag,
  V'→slowFlag, Sprod→singularValuesProd, L7_statement→(inline/HasQpowLimit),
  spectrum→lyapunovSpectrum (Filtration; shadows Mathlib root `spectrum`).
Headline: tendsto_kingman→kingman-style descriptive (keep Kingman in docstring);
  furstenbergKesten_top/_bot→furstenbergKesten_norm/_norm_inv (_top misreads as ⊤).
Main theorem Oseledets.oseledets_filtration → exists_-prefixed / drop dup namespace? (defer; risky, widely referenced — decide in Step 4 carefully).
Each rename: update all references; rebuild. Do the LOW-blast-radius ones first.

## Step 5 — Central axiom-audit test + CI
Create `test/AxiomAudit.lean` (or `Oseledets/Test/`) listing `#print axioms` for the
public API (decl names collected by the phase-1 workers' removedAxiomDecls + the main
theorem + all 8 Corollaries results), guarded with `#guard_msgs`. Wire a CI job (and/or a
lint script running the verifier over all files) in `.github/workflows/`. Update CLAUDE.md
/ STATE.md (they still say the axiom audit "prints during the build").

## Step 6 — Stage A final QA gate
Run the verifier over ALL files → zero warnings everywhere; full `lake build` green;
axiom audit of target + corollaries = [propext, Classical.choice, Quot.sound]. Commit.
Then Stage C (two-sided, blueprint two-sided-met.md) and Stage D (final QA).
