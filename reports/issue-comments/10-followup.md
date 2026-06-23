## Measured estimate — dependency-DAG spike (2026-06-22)

Following up: I mapped the full two-layer dependency DAG (cartographer + adversarial critic, node availability grep-verified) to put a measured number on the SRB reverse inequality. Report: `docs/research/frontier/issue4/DAG-PESIN-2026-06-22.md`.

**This one is genuinely large — and is a clean illustration of why parallelism doesn't rescue it.** Critical path: **depth 8, width 6.** Eight *design-novel* high-risk nodes in **series** (the Layer-2 Pesin chain):
`measurable Eˢ⊕Eᵘ splitting → Lyapunov charts → graph transform → unstable-manifold mfderiv → absolute continuity of Wᵘ → disintegration of μ along Wᵘ → SRB bridge → Thm 7.15`.

Parallel width 6 lets agents absorb the *off-path* Layer-1 work (Shannon–McMillan–Breiman, the countable-partition Kolmogorov–Sinai API) — but the serial Layer-2 chain is, per the critic, "essentially incompressible by width" (Amdahl's law on a deep critical path).

The two deepest nodes are exactly the historically hardest pieces of Ledrappier–Young:
- **Absolute continuity of the unstable foliation** — no Mathlib prior for foliations or holonomy absolute continuity.
- **Disintegration of μ along Wᵘ** — Mathlib's `condKernel` disintegrates along a standard-Borel *measurable map*, not along a measurable foliation (whose leaf partition isn't σ-finite).

| Clock | Estimate |
|---|---|
| Parallel warm-worktree campaigns | **~4–6 months** (staged sub-projects) |
| Human / Mathlib-PR cadence | ~3–6 years |

Also flagged by the audit: the `≤` half (`Oseledets.margulisRuelle_sharp`) carries an honest `hgeo` non-compactness atom-count hypothesis, so even the "done" direction isn't unconditional on non-compact spaces. The realistic path is to stand up SMB + a countable-partition entropy API first (mostly parallelizable), then attack the serial foliation chain as a dedicated sequence of campaigns.
