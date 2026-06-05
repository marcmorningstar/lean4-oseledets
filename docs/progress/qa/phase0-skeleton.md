# QA sign-off — Phase 0 (skeleton)

_Date: 2026-06-05. Independent review by a 3-agent verification workflow (fresh
context, did not write the code), per the charter's per-phase hard gate._

## Verdict: PASS (all three dimensions, zero blocking issues)

| Dimension | Reviewer | Verdict |
|---|---|---|
| Mathematical faithfulness of the statements | `mathematician` agent | **PASS** |
| Lean/Mathlib hygiene + independent build & axiom re-verification | reviewer | **PASS** |
| Plan conformance + completeness critic | reviewer | **PASS** |

## Hard-gate items, independently re-verified

- `lake build` green, exit 0, only the 11 intended `sorry` warnings; no other
  warnings/lint (no unused vars/imports, no deprecations).
- `#print axioms oseledets_filtration` = `[propext, sorryAx, Classical.choice,
  Quot.sound]` — only standard axioms + `sorryAx` (the intended gaps). The fully-defined
  infra layer (`MeasurableSubspace`, `orthProjMatrix`, `instMeasurableSpaceMatrix`) has
  **no** `sorryAx` — genuinely sorry-free.
- No custom `axiom` declarations; no `import Mathlib` catch-all; no `set_option`/`nolint`.
- All 18 declarations namespaced under `Oseledets`; docstring discipline followed.

The faithfulness reviewer additionally **machine-proved `cocycle_add` sorry-free** to
confirm the stated cocycle identity is the true one, checked the `IsSubadditiveCocycle`
direction against `gₙ = log‖A⁽ⁿ⁾‖`, verified the target's equivariance direction, flag
indexing, `StrictAnti` exponents, and that there is **no triviality escape** (`k = 0`
forces `⊤ = ⊥`, impossible for `d ≥ 1`).

## Non-blocking findings (tracked; addressed or deferred)

- **Fixed now:** `tendsto_kingman_ergodic` docstring softened to match the statement
  (a.e.-constant, with the Fekete-infimum identity noted as deferred). Added a note to
  `docs/research/target-and-milestones.md §a` that the implemented `EuclideanSpace` +
  `toEuclideanCLM` framing supersedes the older `Fin d → ℝ`/`toLin'`/`*ᵥ` sketch.
- **Deferred (future cleanup / upstream prep):**
  - Rename `Oseledets.instMeasurableSpaceMatrix` → `Matrix.instMeasurableSpace` and
    consider a scoped instance to avoid an upstream diamond with any future Mathlib
    matrix `MeasurableSpace`.
  - `furstenbergKesten_bot` exposes `lam = -λ_k`; add a wrapper making `λ_k = -lam`
    explicit when the proof lands (docstring already states the sign relation).
  - `condExp_invariants_comp` takes a redundant `hTm : Measurable T` (bundled in
    `MeasurePreserving`); revisit when filling the proof.
- **Deferred by design (not in this skeleton):** the Lyapunov layer L4.x (growth
  function `λ̄`, ultrametric algebra, the limsup flag), L5.x (limsup→lim induction), and
  measurability-of-exponents M7-proper are added as named statements when their
  implementation phases begin. Plan files `Ergodic/CondExpComp.lean` and
  `Ergodic/Subadditive.lean` were merged into `Birkhoff.lean` / `Kingman.lean`
  (consolidation, one source of truth — no duplication).
