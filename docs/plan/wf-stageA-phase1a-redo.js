export const meta = {
  name: 'stageA-phase1a-redo',
  description: 'Redo the 6 phase-1a files whose edits were lost to a worker git-reset race (NO git allowed this time)',
  phases: [{ title: 'Redo', detail: 'one Opus lean-worker per file; NO git commands; verify linter-clean' }],
}

const HEADER = [
  '/-',
  'Copyright (c) 2026 Marcel Morgenstern. All rights reserved.',
  'Released under Apache 2.0 license as described in the file LICENSE.',
  'Authors: Marcel Morgenstern',
  '-/',
].join('\n')

const VERIFY = 'lake env lean -DautoImplicit=false -Dlinter.mathlibStandardSet=true -Dlinter.unusedSectionVars=true -Dlinter.unusedVariables=true -Dlinter.style.longFile=1500 <FILE>'

const NOGIT = `
!!! ABSOLUTE RULE — NEVER RUN GIT !!!
Do NOT run any git command whatsoever: no \`git add\`, \`git commit\`, \`git reset\`,
\`git checkout\`, \`git restore\`, \`git stash\`, \`git clean\`, \`git rm\`. A prior run was
corrupted because a worker ran \`git reset\` and wiped other workers' edits. You operate
only with the Edit/Write tools and \`lake env lean\` (read-only). The ORCHESTRATOR handles
ALL version control. If you think you need git, you do not — just edit the file and verify.
`

const GENERIC = `
You are cleaning ONE Lean 4 file of a Mathlib-style formalization of the Oseledets
multiplicative ergodic theorem, to make it Mathlib-merge-ready. Apply ONLY the mechanical /
editorial changes below to the given file. Hard rules:
  - Do NOT rename any theorem/def/structure/namespace.
  - Do NOT change any statement or any proof's mathematical content.
  - The ONLY proof-affecting edits allowed: removing an unneeded \`set_option linter ... false\`
    via \`omit\`/variable-tightening, and replacing a goal-restating \`show\` with \`change\` if the
    linter flags \`linter.style.show\`, and deprecated-API renames.
  - Keep the file elaborating with NO errors.

1. COPYRIGHT HEADER — if the file does not already begin with the 4-line Mathlib copyright
   block, prepend exactly this as the first 5 lines (then the existing \`import\` lines):
${HEADER}

2. REMOVE \`#print axioms\` — delete every \`#print axioms <name>\` line and any now-purposeless
   \`/-! ## Axiom audit -/\` header. RECORD every deleted declaration name in removedAxiomDecls.

3. LINTER SUPPRESSIONS — remove every file-global \`set_option linter.unusedSectionVars false\` /
   \`linter.unusedVariables false\` / \`linter.deprecated false\`. Fix the surfaced warnings the
   Mathlib way: \`omit [Inst]\` immediately BEFORE the declaration (omit must come before the
   declaration's docstring, NOT between docstring and declaration — that is a parse error), or
   tighten \`variable\` blocks. Scoped \`set_option ... in\` + comment only as a last resort.
   IMPORTANT: verify zero unusedSectionVars/unusedVariables warnings remain under BOTH the
   verifier below AND a plain elaboration — every theorem that does not use an instance/section
   variable needs its own omit.

4. DEPRECATED API — rename to the suggested replacement if the verifier reports a deprecation.

5. LONG LINES — wrap every line whose LENGTH IN UNICODE CODEPOINTS exceeds 100 (NOT bytes —
   a line full of λ, ←, ₀, ⋀ may be >100 bytes but <=100 codepoints and is fine). Trust the
   linter's longLine report, not a byte count. Wrap at natural points with Mathlib indentation.

6. maxHeartbeats — add a short explanatory comment to any \`set_option maxHeartbeats N in\` lacking one.

7. REGISTER SCRUB — reword development-log language in docstrings/comments (milestone codes M*/L*,
   "NODE", worker/agent narrative, "scratch", status banners "ZERO sorry"/"PROVED"/"sorry-free",
   dangling \`docs/...\` pointers) into neutral mathematical prose. Keep all genuine math and
   literature references. Reword (do not delete) \`/-! ## ... -/\` section headers.

8. MODULE DOCSTRING — if the file has none after the imports, add a short one.

VERIFY (repeat until clean):
  ${VERIFY}
Acceptable final output: ZERO lines containing \`warning:\`, error-free elaboration, and no
\`depends on axioms:\` info lines (since you removed the #print axioms).

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
    s: 'Likely only needs the copyright header (no axioms, no suppressions, no long lines). Verify clean.' },
  { f: 'Oseledets/MultiplicativeErgodic.lean',
    s: 'THE TARGET FILE — be conservative (~80 lines). header; remove 1 `#print axioms Oseledets.oseledets_filtration` + its `## Axiom audit` header; scrub milestone codes (M10/L6.1), the "fully proved" banner, and the dangling pointers docs/research/target-and-milestones.md and docs/progress/STATE.md from the module docstring. KEEP the main-theorem mathematical docstring intact.' },
  { f: 'Oseledets/Lyapunov/RuelleReverse.lean',
    s: 'header; remove 1 #print axioms; ~3 long lines; reword the dev-log module-docstring title. Leave the `Ruelle13` namespace unchanged.' },
  { f: 'Oseledets/Lyapunov/SlowFlagBridge.lean',
    s: 'header; remove 3 #print axioms; remove 1 file-global linter.unusedSectionVars false (fix via omit — only hae_of_slowflag needed `omit [NeZero d]` last time); ~5 long lines; register scrub.' },
  { f: 'Oseledets/Lyapunov/SpectralMeasurable.lean',
    s: 'header; file has NO module docstring — add one; remove 1 file-global linter.unusedSectionVars false (fix via omit [NeZero d] before tendsto_cfc_gApprox and measurable_spectralProjector; measurable_slowProjector keeps the instance); register scrub.' },
  { f: 'Oseledets/Lyapunov/RuelleCore.lean',
    s: 'header; remove 9 #print axioms; ~45 long lines; register scrub. Leave the `Ruelle13` namespace unchanged.' },
]

phase('Redo')
const results = await parallel(FILES.map(({ f, s }) => () =>
  agent(
    `${NOGIT}\n${GENERIC}\n\n========== FILE TO CLEAN ==========\n${f}\n\nFile-specific notes: ${s}\n\nVerifier command for THIS file:\n  ${VERIFY.replace('<FILE>', f)}\n${NOGIT}`,
    { label: `redo:${f.split('/').pop()}`, phase: 'Redo', model: 'opus', agentType: 'lean-worker', schema: SCHEMA },
  )
))

const ok = results.filter(Boolean)
log(`phase-1a-redo done: ${ok.filter(r => r.elaborates && r.finalWarningCount === 0).length}/${FILES.length} clean`)
return {
  perFile: ok,
  allAxiomDecls: ok.flatMap(r => r.removedAxiomDecls || []),
  cleanCount: ok.filter(r => r.elaborates && r.finalWarningCount === 0).length,
  total: FILES.length,
}
