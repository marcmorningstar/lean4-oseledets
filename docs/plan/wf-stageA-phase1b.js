export const meta = {
  name: 'stageA-phase1b',
  description: 'Mathlib-style line-wrapping + residual-warning cleanup of the 25 already-headed smaller Oseledets files',
  phases: [{ title: 'Wrap', detail: 'one Opus lean-worker per file; each verifies linter-clean' }],
}

const HEADER = [
  '/-',
  'Copyright (c) 2026 Marcel Morgenstern. All rights reserved.',
  'Released under Apache 2.0 license as described in the file LICENSE.',
  'Authors: Marcel Morgenstern',
  '-/',
].join('\n')

const VERIFY = 'lake env lean -DautoImplicit=false -Dlinter.mathlibStandardSet=true -Dlinter.unusedSectionVars=true -Dlinter.unusedVariables=true -Dlinter.style.longFile=1500 <FILE>'

const GENERIC = `
You are finishing the Mathlib-style cleanup of ONE Lean 4 file in a formalization of the
Oseledets multiplicative ergodic theorem. These files were already given copyright headers and
had their docstrings scrubbed; the MAIN remaining task is wrapping over-long lines, plus fixing
any residual linter warning the verifier reports. Hard rules:
  - Do NOT rename any theorem/def/structure/namespace.
  - Do NOT change any statement or proof's mathematical content.
  - The only proof-affecting edits allowed: \`show\`→\`change\` if \`linter.style.show\` fires;
    deprecated-API renames; \`ring\`→\`ring_nf\` where \`ring\` "does nothing"; removing an
    unneeded \`set_option linter ... false\` via \`omit\`/variable-tightening.
  - Keep the file elaborating with NO errors.

Do, in order, whatever the verifier still complains about:

1. LONG LINES — wrap every line >100 chars to <=100, preserving meaning. Prose/docstrings:
   rewrap. Code: break at natural points (after \`->\`, \`,\`, binders, \`:=\`, before \`:= by\`) with
   Mathlib 4-space (signature) / 2-space (proof) continuation indentation.
2. COPYRIGHT HEADER — if somehow missing, prepend exactly:
${HEADER}
3. DEPRECATED API — rename to the suggested replacement if the verifier reports a deprecation
   (\`Matrix.toEuclideanLin_apply\`->\`Matrix.toLpLin_apply\`, \`tendsto_finset_sum\`->\`tendsto_finsetSum\`,
   \`EuclideanSpace.norm_single\`->\`PiLp.norm_single\`, \`push_neg\`->\`push Not\` only if flagged).
4. LINTER SUPPRESSIONS — remove any file-global \`set_option linter.X false\`; fix the underlying
   warning via \`omit [Inst]\` / tighter \`variable\` blocks (scoped \`... in\` + comment only as a
   last resort).
5. maxHeartbeats — add a short explanatory comment to any \`set_option maxHeartbeats N in\` lacking one.
6. \`#print axioms\` — if any remain, delete them and report their decl names in removedAxiomDecls.
7. REGISTER — if any development-log language remains in docstrings/comments (milestone codes,
   "worker"/"DELIVERABLE"/"scratch", status banners, \`docs/...\` pointers), reword to neutral math prose.

VERIFY (repeat until clean):
  ${VERIFY}
Acceptable final output: ZERO lines containing \`warning:\`, error-free elaboration.

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
  { f: 'Oseledets/Lyapunov/ForwardUpperBound.lean', s: '~41 long lines.' },
  { f: 'Oseledets/Lyapunov/Forward.lean', s: '~35 long lines.' },
  { f: 'Oseledets/Lyapunov/GrowthFunction.lean', s: '~23 long lines.' },
  { f: 'Oseledets/Lyapunov/ForwardDetSqueeze.lean', s: '~22 long lines.' },
  { f: 'Oseledets/Ergodic/Birkhoff.lean', s: '~21 long lines.' },
  { f: 'Oseledets/Lyapunov/ChainRecursion.lean', s: '~20 long lines. Leave the Ruelle13 namespace name unchanged.' },
  { f: 'Oseledets/Lyapunov/ForwardGradedOverlap.lean', s: '~19 long lines.' },
  { f: 'Oseledets/Lyapunov/ForwardSqueezeData.lean', s: '~17 long lines.' },
  { f: 'Oseledets/Lyapunov/CapstoneWiring.lean', s: '~16 long lines.' },
  { f: 'Oseledets/Lyapunov/Measurable.lean', s: '~12 long lines.' },
  { f: 'Oseledets/Lyapunov/ForwardLowerWiring.lean', s: '~12 long lines. Check for a file-global `set_option linter.deprecated false` and remove it, fixing any real deprecation it hid.' },
  { f: 'Oseledets/Cocycle/FurstenbergKesten.lean', s: '~11 long lines.' },
  { f: 'Oseledets/Lyapunov/ForwardSqueezeCore.lean', s: '~10 long lines.' },
  { f: 'Oseledets/Lyapunov/ForwardAngle.lean', s: '~10 long lines.' },
  { f: 'Oseledets/Lyapunov/Filtration.lean', s: '~9 long lines.' },
  { f: 'Oseledets/Lyapunov/ForwardV.lean', s: '~8 long lines.' },
  { f: 'Oseledets/Lyapunov/AssemblyChain.lean', s: '~8 long lines.' },
  { f: 'Oseledets/Lyapunov/BridgeWiring.lean', s: '~7 long lines. Also: change the 2 `ring` calls that "do nothing" to `ring_nf`; add an explanatory comment to the maxHeartbeats bump.' },
  { f: 'Oseledets/Lyapunov/LimitEigenbasis.lean', s: '~6 long lines.' },
  { f: 'Oseledets/Lyapunov/AssemblyTopGap.lean', s: '~6 long lines.' },
  { f: 'Oseledets/Lyapunov/AssemblyFromUpper.lean', s: '~5 long lines.' },
  { f: 'Oseledets/Lyapunov/FiltrationAssemblyBridge.lean', s: '~4 long lines.' },
  { f: 'Oseledets/Lyapunov/Corollaries.lean', s: '~3 long lines.' },
  { f: 'Oseledets/Lyapunov/FiltrationAssembly.lean', s: '~2 long lines.' },
  { f: 'Oseledets/Lyapunov/AssemblyFromUpperIdent.lean', s: '~2 long lines.' },
]

phase('Wrap')
const results = await parallel(FILES.map(({ f, s }) => () =>
  agent(
    `${GENERIC}\n\n========== FILE TO CLEAN ==========\n${f}\n\nFile-specific notes: ${s}\n\nVerifier command for THIS file:\n  ${VERIFY.replace('<FILE>', f)}\n`,
    { label: `wrap:${f.split('/').pop()}`, phase: 'Wrap', model: 'opus', agentType: 'lean-worker', schema: SCHEMA },
  )
))

const ok = results.filter(Boolean)
log(`phase-1b done: ${ok.filter(r => r.elaborates && r.finalWarningCount === 0).length}/${FILES.length} clean`)
return {
  perFile: ok,
  allAxiomDecls: ok.flatMap(r => r.removedAxiomDecls || []),
  cleanCount: ok.filter(r => r.elaborates && r.finalWarningCount === 0).length,
  total: FILES.length,
}
