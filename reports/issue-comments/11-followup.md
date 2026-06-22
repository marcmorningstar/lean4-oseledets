## Measured estimate — dependency-DAG spike (2026-06-22)

Following up the progress note: I mapped the residual's full dependency DAG (cartographer + adversarial critic, every node's Mathlib availability verified by grep) to replace the "multi-year" framing with a measured one. Report: `docs/research/frontier/issue6/DAG-AK-2026-06-22.md`.

**Key finding: this is near-term, not a multi-year wall — for what the project actually needs.** The full Effros-hyperspace / Π¹₁-boundedness / transfinite-derivative §5.12 tower genuinely is absent from Mathlib (that much of "multi-year" was true), **but the repo already routes around it** — the everywhere-Borel target is collapsed to the single sorry `measurableSet_image_fst_of_subset_compact_box` (Srivastava 4.7.2) at `ArseninKunugui.lean:297`, with the σ-compact-cover leaf eliminated via the sorry-free Euclidean ball-slab.

**Residual critical path: depth 3, width 1** (essentially serial):
`4.6.5 generalized reduction → 4.7.1 structure theorem → 4.7.2 open-section structure`.

The adversarial critic caught two over-pessimistic claims in the first pass: Mathlib **already has** the countable-family separation engine (`MeasurablySeparable.iUnion` and `measurablySeparable_range_of_disjoint` in `Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`), and **no** named coanalytic-pointclass abstraction is actually needed — Srivastava's proofs of 4.6.5/4.7.1/4.7.2 never instantiate one. The real remaining work is the generalized first-separation (4.6.2) tree-induction plus two structure lemmas built on the existing `MeasurablySeparable` API.

| Clock | Estimate |
|---|---|
| Parallel warm-worktree campaigns | **~1–2.5 weeks** |
| Human / Mathlib-PR cadence | ~6–10 weeks (1–2 PRs) |

Dominant remaining risk: the 4.6.2 induction needs the empty-interior/tree step that `MeasurablySeparable.iUnion` does not directly give. Reclassifying this from "research-wall" into the near-term closure queue alongside #8/#9.
