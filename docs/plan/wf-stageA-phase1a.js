export const meta = {
  name: 'stageA-phase1a',
  description: 'Mathlib-style cleanup of the 11 unverified phase-1 Oseledets files (headers, #print axioms removal, linter-suppression fixes, line-wrapping, register scrub)',
  phases: [{ title: 'Cleanup', detail: 'one Opus lean-worker per file; each verifies linter-clean' }],
}

const HEADER = [
  '/-',
  'Copyright (c) 2026 Marcel Morgenstern. All rights reserved.',
  'Released under Apache 2.0 license as described in the file LICENSE.',
  'Authors: Marcel Morgenstern',
  '-/',
].join('\n')

const VERIFY = 'lake env lean -DautoImplicit=false -Dlinter.mathlibStandardSet=true -Dlinter.style.longFile=1500 <FILE>'

const GENERIC = `
You are cleaning ONE Lean 4 file of a Mathlib-style formalization of the Oseledets
multiplicative ergodic theorem, to make it Mathlib-merge-ready. Apply ONLY the mechanical /
editorial changes below to the given file. Hard rules:
  - Do NOT rename any theorem/def/structure/namespace.
  - Do NOT change any statement or any proof's mathematical content.
  - The ONLY proof-affecting edits allowed are: removing now-unneeded \`set_option linter ... false\`
    via \`omit\`/variable-tightening, and replacing a goal-restating \`show\` with \`change\` if the
    linter flags \`linter.style.show\`.
  - Keep the build green: the file must still elaborate with NO errors.

Changes to make:

1. COPYRIGHT HEADER — if the file does not already begin with the 4-line Mathlib copyright
   block, prepend exactly this as the very first 5 lines (then a newline, then the existing
   \`import\` lines unchanged):
${HEADER}

2. REMOVE \`#print axioms\` — delete every line matching \`#print axioms <name>\`. Also delete any
   now-purposeless \`/-! ## Axiom audit -/\` (or similar) section-header comment that existed only
   to introduce those commands. RECORD every deleted declaration name (the \`<name>\`) — you MUST
   return this list in \`removedAxiomDecls\`.

3. LINTER SUPPRESSIONS — remove every file-global (un-scoped) \`set_option linter.unusedSectionVars false\`,
   \`set_option linter.unusedVariables false\`, and \`set_option linter.deprecated false\`. Then fix the
   warnings they hid the Mathlib way: prefer \`omit [Inst]\` before the declarations that don't use a
   section variable/instance, or tighten \`variable\` blocks. If (and only if) a specific declaration
   genuinely needs a suppression, scope it as \`set_option linter.X false in\` immediately before THAT
   declaration with a one-line comment explaining why. Iterate with the verifier to zero
   unusedSectionVars / unusedVariables / deprecated warnings.

4. DEPRECATED API — if the verifier reports deprecations, rename to the suggested replacement
   (e.g. \`Matrix.toEuclideanLin_apply\`→\`Matrix.toLpLin_apply\`, \`tendsto_finset_sum\`→\`tendsto_finsetSum\`,
   \`EuclideanSpace.norm_single\`→\`PiLp.norm_single\`; for \`push_neg\`→\`push Not\` only if the verifier
   actually flags it). Re-verify the proof still closes.

5. LONG LINES — wrap every line >100 chars to ≤100, preserving meaning. Prose/docstrings: rewrap.
   Code: break at natural points (after \`→\`, \`,\`, binders, \`:=\`, before \`:= by\`) using Mathlib's
   4-space signature / 2-space proof continuation indentation.

6. maxHeartbeats — if any \`set_option maxHeartbeats N in\` lacks an explanatory comment, add a short
   one (same line or line above) saying why the bump is needed.

7. DOCSTRING / COMMENT REGISTER SCRUB — rewrite project-internal development-log language into
   neutral mathematical prose. Remove or replace: milestone/node codes (M5, L7c.3b, L13, "NODE 1",
   etc.), worker/agent narrative ("the parallel worker", "prove-wave workers", "scratch_*",
   "adversarial attack", "next worker", "delivered verbatim"), self-status banners ("ZERO sorry",
   "sorry-free", "PROVED", "no sorryAx"), and dangling repo-internal pointers (\`docs/...\`). KEEP all
   genuine mathematics, literature references (Ruelle 1979, Viana, Karlsson), and proof-narration
   comments. Do not delete \`/-! ## ... -/\` section headers — just reword them to describe the math.

8. MODULE DOCSTRING — if the file has no \`/-! ... -/\` module docstring after the imports, add a
   short one describing the file's mathematical content.

VERIFY (run repeatedly until clean):
  ${VERIFY}
Acceptable final output: ZERO lines containing \`warning:\` and a clean (error-free) elaboration.
(After step 2 there should be no \`depends on axioms:\` info lines either.)

Edit ONLY the one file named below. Return the structured result.
`

const SCHEMA = {
  type: 'object',
  additionalProperties: false,
  properties: {
    file: { type: 'string' },
    removedAxiomDecls: { type: 'array', items: { type: 'string' } },
    finalWarningCount: { type: 'integer' },
    elaborates: { type: 'boolean' },
    notes: { type: 'string' },
  },
  required: ['file', 'removedAxiomDecls', 'finalWarningCount', 'elaborates', 'notes'],
}

const FILES = [
  { f: 'Oseledets/Lyapunov/Ultrametric.lean',
    s: 'Likely only needs the copyright header (no #print axioms, no long lines, no suppressions detected). Verify clean.' },
  { f: 'Oseledets/MultiplicativeErgodic.lean',
    s: 'THE TARGET FILE — be conservative. ~80 lines. Needs: header; remove 1 `#print axioms Oseledets.oseledets_filtration`; scrub milestone codes (M10 / L6.1) and the two dangling pointers `docs/research/target-and-milestones.md` and `docs/progress/STATE.md` from the module docstring. Keep the (excellent) mathematical docstring of the main theorem intact.' },
  { f: 'Oseledets/Lyapunov/RuelleReverse.lean',
    s: 'header; remove 1 #print axioms; ~3 long lines. Leave the `Ruelle13` namespace name unchanged (renamed in a later phase).' },
  { f: 'Oseledets/Lyapunov/SlowFlagBridge.lean',
    s: 'header; remove 3 #print axioms; remove 1 file-global `linter.unusedSectionVars false` (fix via omit); ~5 long lines; register scrub.' },
  { f: 'Oseledets/Lyapunov/SpectralMeasurable.lean',
    s: 'header; file has NO module docstring — add a short one; remove 1 file-global `linter.unusedSectionVars false` (fix via omit); register scrub if any.' },
  { f: 'Oseledets/Lyapunov/SpectrumResiduals.lean',
    s: 'header; remove 3 #print axioms; remove 1 suppression; ~12 long lines; register scrub.' },
  { f: 'Oseledets/Lyapunov/SpectrumConstancy.lean',
    s: 'header; remove 8 #print axioms; remove 2 suppressions (unusedSectionVars + unusedVariables); ~12 long lines; register scrub.' },
  { f: 'Oseledets/Lyapunov/SpectralIdentification.lean',
    s: 'header; remove 3 #print axioms; remove 1 suppression; ~23 long lines; register scrub.' },
  { f: 'Oseledets/Lyapunov/ForwardGradedOverlapTopGap.lean',
    s: 'header; remove 11 #print axioms; remove 1 suppression; ~16 long lines; register scrub (the docstring discusses a "refuted hchain" route — keep that as legitimate mathematical context, just neutralize the development-log tone). Leave the primed theorem name forward_graded_overlap-prime unchanged (it is renamed in a later phase).' },
  { f: 'Oseledets/Lyapunov/RuelleCore.lean',
    s: 'header; remove 9 #print axioms; ~45 long lines; register scrub. Leave the `Ruelle13` namespace unchanged.' },
  { f: 'Oseledets/Lyapunov/TopGapEnvelope.lean',
    s: 'HEAVY (1460 lines). header; remove 14 #print axioms; remove 2 file-global suppressions (unusedSectionVars + unusedVariables) via omit; ~103 long lines; thorough register scrub (milestone codes in `## section` headers, "KEY INSIGHT N", "the 11 prove-wave workers", "ZERO sorry and ZERO sorryAx" banners). Private helper names like `htg*` may stay. Work methodically.' },
]

phase('Cleanup')
const results = await parallel(FILES.map(({ f, s }) => () =>
  agent(
    `${GENERIC}\n\n========== FILE TO CLEAN ==========\n${f}\n\nFile-specific notes: ${s}\n\nVerifier command for THIS file:\n  ${VERIFY.replace('<FILE>', f)}\n`,
    { label: `clean:${f.split('/').pop()}`, phase: 'Cleanup', model: 'opus', agentType: 'lean-worker', schema: SCHEMA },
  )
))

const ok = results.filter(Boolean)
log(`phase-1a done: ${ok.filter(r => r.elaborates && r.finalWarningCount === 0).length}/${FILES.length} clean`)
return {
  perFile: ok,
  allAxiomDecls: ok.flatMap(r => r.removedAxiomDecls || []),
  cleanCount: ok.filter(r => r.elaborates && r.finalWarningCount === 0).length,
  total: FILES.length,
}
