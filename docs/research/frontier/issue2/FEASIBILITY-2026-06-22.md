# Issue #2 — Measurability of the manifold derivative cocycle: feasibility & decomposition

**Date:** 2026-06-22
**Scope:** two BLOCKED `sorry` leaves
- `Frontier/Issue2/DerivativeCocycleManifold.lean:325` — `measurable_bundleDerivativeCocycle`
- `Frontier/Issue2/Existence.lean:153` — `exists_measurableFraming_of_sigmaCompact`

**Verdict (one line):** `partial-decomposition`, but with a genuinely closeable *core* if one
restricts to **boundaryless** models and equips `M` with a **Borel** σ-algebra. The single hard
analytic fact (`x ↦ mfderiv I I T x` is Borel measurable) is reachable in Mathlib **today** via the
chart-local route below, with no from-source rebuild and no appeal to the uncached
`ContMDiffMFDeriv` continuity machinery. The `Existence.lean` framing leaf is strictly easier than
its docstring claims (the frame is globally constant and the per-block input is measurability, not
continuity). Confidence is moderate, not high: there are 3–4 non-trivial Mathlib gluing lemmas to
assemble, and one real hypothesis-strength decision (boundaryless) the author must accept.

---

## 1. Precise Lean types of the two leaves

### Leaf A — the wall

```lean
theorem measurable_bundleDerivativeCocycle
    [MeasurableSpace M] [BorelSpace M] {T : M → M}
    (hT : MDifferentiable I I T) :
    Measurable (bundleDerivativeCocycle I T)
```
where `bundleDerivativeCocycle I T x : E →L[ℝ] E` is **definitionally** `mfderiv I I T x`
(`bundleDerivativeCocycle_apply` is `rfl`; the codomain `E →L[ℝ] E` carries its Borel σ-algebra from
the operator-norm topology). Ambient hypotheses in scope at this declaration:
`[NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]`, `H` a topological space,
`I : ModelWithCorners ℝ E H`, `M` a `ChartedSpace H M` with `[IsManifold I 1 M]`.

**So the leaf is exactly:** `Measurable (fun x : M => mfderiv I I T x)` for the Borel σ-algebra of
`M`, mapping into the Borel σ-algebra of `E →L[ℝ] E`. The framing reductions downstream
(`measurable_frameAlg`, `measurable_derivativeCocycleManifold`) are already sorry-free, so this is
the only obligation.

### Leaf B — existence of a measurable framing

```lean
theorem exists_measurableFraming_of_sigmaCompact
    [SigmaCompactSpace M] [SecondCountableTopology H]
    {T : M → M} (hT : MDifferentiable I I T) :
    Nonempty (MeasurableFraming I T)
```
`MeasurableFraming I T` (Framing.lean) bundles `frame : (x : M) → TangentSpace I x ≃L[ℝ] E` together
with `Measurable (fun x => frame (T x) ∘L mfderiv I I T x ∘L (frame x).symm)`. Ambient:
`[NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]`,
`[MeasurableSpace M] [BorelSpace M]`, `[IsManifold I 1 M]`.

**Key structural observation the author already exploited (DerivativeCocycleManifold.lean) but the
`Existence.lean` docstring under-uses:** Mathlib's `TangentSpace I x` is *definitionally* the model
`E` for every `x`. Hence one may take `frame x := ContinuousLinearEquiv.refl ℝ E` (the constant
identity frame) and the `MeasurableFraming` obligation collapses to *exactly Leaf A*:
`Measurable (fun x => mfderiv I I T x)`. There is **no honest per-point bundle trivialization to
build** — the disjointified-atlas / `Trivialization.continuousLinearEquivAt` story in the
`Existence.lean` docstring is a red herring for this Mathlib tangent-bundle model. So **Leaf B
reduces to Leaf A** and should not be attacked independently.

---

## 2. The chart-local structure of `mfderiv` (Mathlib internals, verified)

From `Mathlib/Geometry/Manifold/MFDeriv/Defs.lean:334`:
```lean
def mfderiv (f : M → M') (x : M) : TangentSpace I x →L[𝕜] TangentSpace I' (f x) :=
  if MDifferentiableAt I I' f x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f) (range I) ((extChartAt I x) x) :)
  else 0
```
The chart is taken **at the moving point `x` itself**, so this expression is not directly a
measurable function of `x` (the chart varies). The fix is the *fixed-base-point* coordinate
representation `inTangentCoordinates`, which conjugates by coordinate changes
(`Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean:519`, `:531`):
```lean
def inTangentCoordinates (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') : N → N → E →L[𝕜] E' :=
  fun x₀ x => inCoordinates E (TangentSpace I) E' (TangentSpace I') (f x₀) (f x) (g x₀) (g x) (ϕ x)
-- inTangentCoordinates I I' f g ϕ x₀ x =
--   tangentCoordChange I' (g x) (g x₀) (g x) ∘L ϕ x ∘L tangentCoordChange I (f x₀) (f x) (f x)
```
with `tangentCoordChange I x y z = fderivWithin 𝕜 (extChartAt I y ∘ (extChartAt I x).symm) (range I)
(extChartAt I x z)` (`Tangent.lean:143,146`), and crucially
`continuousOn_tangentCoordChange : ContinuousOn (tangentCoordChange I x y)
((extChartAt I x).source ∩ (extChartAt I y).source)` (`Tangent.lean:171`).

**The boundaryless simplification (decisive).** If `I` is `ModelWithCorners.Boundaryless`
(`IsManifold/Basic.lean:593`, `range_eq_univ`), then `range I = univ`, so inside a single chart
`mfderiv` is `fderivWithin ℝ _ univ = fderiv ℝ _` of the Euclidean map `writtenInExtChartAt`. And
`measurable_fderiv` (`Analysis/Calculus/FDeriv/Measurable.lean:380`) is **unconditional** — it needs
**no** differentiability hypothesis (it maps non-differentiability points to `0`, exactly matching
`mfderiv`'s `else 0` branch). This removes the only deep analytic obstacle: over each chart we get a
genuinely Borel-measurable Euclidean derivative for free, with no smoothness beyond what
`writtenInExtChartAt` already is.

For models **with** boundary the analogue would need a `measurable_fderivWithin … (range I)` lemma,
which does **not** exist in Mathlib (only `aemeasurable_fderivWithin`, `Jacobian.lean:689`, which is
ae-only, Lebesgue-only, and assumes pointwise differentiability). So the honest recommendation is to
add `[I.Boundaryless]` to both leaves (manifolds without corners; this is the standard MET setting
and matches the dynamical-systems literature).

---

## 3. The literature proof (Filip §2.2.2; standard measurable-trivialization)

S. Filip, *Notes on the Multiplicative Ergodic Theorem*, arXiv:1710.10694v1, §2.2.2 (verified in the
saved scrape `docs/research/frontier/issue6/filip-notes-met.md`):

> "[A vector bundle] is defined by gluing the pieces `U_α × ℝⁿ` using the identifications
> `(ω,v) ∼ (ω, φ_{α,β} v)`. The sets `U_α` can be measurable or open. Similarly the gluing maps can
> be measurable, continuous, smooth, depending on the qualities of Ω. **Any vector bundle can be
> measurably trivialized, i.e. it is measurably isomorphic to `Ω × ℝⁿ`.**"

The constructive proof, specialised to the tangent cocycle of a self-map `T` of a manifold:

1. **Countable atlas.** A σ-compact manifold with `SecondCountableTopology H` is second-countable
   (Mathlib: `ChartedSpace.secondCountable_of_sigmaCompact`) and admits a countable family of points
   `(xₖ)` with `⋃ₖ (chartAt H xₖ).source = univ` (Mathlib:
   `countable_cover_nhds_of_sigmaCompact`, used inside `secondCountable_of_sigmaCompact`,
   `ChartedSpace.lean:236`).
2. **Disjointify** to a countable **Borel partition** `Pₖ := disjointed (chartSource ∘ enumerate) k`,
   each `Pₖ ⊆ (chartAt H xₖ).source`, `⋃ Pₖ = univ`, each `Pₖ` measurable (chart sources are open,
   hence Borel; `Set.disjointed`, `iUnion_disjointed`).
3. **Local representative.** On `Pₖ` the derivative `x ↦ mfderiv I I T x`, *read in the fixed chart
   at `xₖ` (source) and at `T xₖ` (target)*, is `inTangentCoordinates I I T (fun x => x) (mfderiv …)`,
   which equals the Euclidean `fderiv` of `writtenInExtChartAt` conjugated by two `tangentCoordChange`
   factors (§2). The conjugating factors are continuous on the chart overlap, the Euclidean factor is
   measurable by `measurable_fderiv` — so the local representative is measurable on `Pₖ`.
4. **Glue** the local measurable representatives across the countable Borel partition. (Filip: "the
   sets `U_α` can be measurable"; the resulting global trivialization is measurable.) In the Mathlib
   tangent-bundle model this gluing *is* `measurable_of_measurable_on_countable_cover` — already
   proved sorry-free in `Existence.lean:78` via `Set.liftCover` / `measurable_liftCover`.

Cross-references for the same construction at theorem-number granularity: Arnold, *Random Dynamical
Systems* (1998), §3.4 (measurable invariant bundles) and §4.2 (MET on bundles); Viana, *Lectures on
Lyapunov Exponents* (CSAM 145, 2014), §4.1 (the tangent cocycle as a measurable matrix cocycle after
a measurable frame). None of these formalize the measurability — it is treated as routine, which is
precisely why Mathlib has no lemma.

---

## 4. What EXISTS in Mathlib (exact names found)

| Need | Mathlib lemma | File:line | Status |
|---|---|---|---|
| Euclidean derivative measurable, no hyp | `measurable_fderiv` | `Analysis/Calculus/FDeriv/Measurable.lean:380` | exact, `@[fun_prop]` |
| set of differentiability points Borel | `measurableSet_of_differentiableAt` | `…/Measurable.lean:374` | exact |
| chart-local mfderiv unfolding | `mfderiv` def (`if … fderivWithin (writtenInExtChartAt) (range I) …`) | `MFDeriv/Defs.lean:334` | exact |
| fixed-base coordinate rep | `inTangentCoordinates`, `inTangentCoordinates_eq`, `inTangentCoordinates_eq_mfderiv_comp` | `VectorBundle/Tangent.lean:519,531`; `MFDeriv/Tangent.lean:75` | exact |
| coordinate-change factor | `tangentCoordChange`, `tangentCoordChange_def` | `VectorBundle/Tangent.lean:143,146` | exact |
| coord-change continuous on overlap | `continuousOn_tangentCoordChange` | `VectorBundle/Tangent.lean:171` | exact |
| boundaryless ⇒ range = univ | `ModelWithCorners.range_eq_univ` | `IsManifold/Basic.lean:598` | exact |
| range I closed (for-corners fallback) | `ModelWithCorners.isClosed_range` | `IsManifold/Basic.lean:403` | exact |
| second-countable from σ-compact | `ChartedSpace.secondCountable_of_sigmaCompact` | `ChartedSpace.lean:234` | exact |
| countable chart-source cover | `countable_cover_nhds_of_sigmaCompact` (inside the above) | `ChartedSpace.lean:236` | exact |
| glue measurable on countable cover | `measurable_of_measurable_on_countable_cover` | **already in repo** `Existence.lean:78` | sorry-free |
| disjointify open cover to Borel partition | `Set.disjointed`, `iUnion_disjointed`, `MeasurableSet.disjointed` | Mathlib core | exact |
| ContinuousOn ⇒ measurable on a Borel set | `ContinuousOn.aemeasurable` / restrict + `Measurable.comp` of continuous | `IntegrableOn.lean:712`; `BorelSpace/Basic.lean` | partial (need genuine, not ae — see §6) |
| chart-coord *continuity* of mfderiv (C² route) | `ContMDiffAt.mfderiv_const` | `ContMDiffMFDeriv.lean:242` | exact but **uncached import**, and needs `CMDiffAt n f` with `n ≥ 1` for `m=0`, i.e. **C²** for a strictly-positive `m`; for `m = 0` it needs `n ≥ 1` = C¹ but yields only `ContMDiffAt` ⇒ continuity, which is *more* than we need |

**Two things Mathlib does NOT have (confirmed by grep + firecrawl):**
- No `Measurable (fun x => mfderiv I I T x)` and no `Measurable (tangentMap …)`.
- No `measurable_fderivWithin … (range I)` for a non-`univ` set (only `aemeasurable_fderivWithin`).

---

## 5. Decomposition into smallest sub-lemmas

Assume `[I.Boundaryless] [MeasurableSpace M] [BorelSpace M]` and second-countable `H` /
σ-compact `M`. Target: `Measurable (fun x : M => mfderiv I I T x)`.

| # | Sub-lemma (informal type) | mathlibSupport | difficulty |
|---|---|---|---|
| L1 | `range I = univ` ⇒ on the source of `chartAt H x₀`, `mfderiv I I T x` (read at base `x₀`) `=` `tangentCoordChange I' (T x) (T x₀) (T x) ∘L fderiv ℝ (writtenInExtChartAt I I x T applied via charts) ∘L tangentCoordChange I x₀ x x`. Concretely the specialization of `inTangentCoordinates_eq_mfderiv_comp` with `range I = univ`. | partial (pieces exist; the exact `mfderiv = inTangentCoordinates id T (mfderiv) x₀` identity on the chart needs assembling) | medium |
| L2 | `Measurable (fun x => fderiv ℝ (E-side composite) (extChartAt I x₀ x))` on `(chartAt H x₀).source`: pull `measurable_fderiv` back through the continuous `extChartAt I x₀`. | exists (`measurable_fderiv` + `continuousOn` of extChartAt) | easy–medium |
| L3 | `Measurable` (restricted to the overlap) of each `tangentCoordChange` factor `x ↦ tangentCoordChange I a b x`: it is `ContinuousOn` the overlap (`continuousOn_tangentCoordChange`); restrict to a Borel subset ⇒ measurable. | partial (`ContinuousOn` ⇒ `Measurable` on a Borel set needs the standard `restrict`/`measurable_of_continuousOn` bridge; ae-version exists, genuine version assembled from `ContinuousOn` + open/Borel set) | medium |
| L4 | The composite/`comp` and `clm_apply` of measurable `E →L[ℝ] E`-valued maps is measurable: `ContinuousLinearMap.measurable_comp` / `.measurable_apply` and continuity of `(∘L)`. | exists (`ContinuousLinearMap.measurable_comp`, `measurable_apply`, continuity of composition on `E →L[ℝ] E`) | easy |
| L5 | Per-chart conclusion: `Measurable ((Pₖ).restrict (fun x => mfderiv I I T x))` from L1–L4 (the conjugated representative equals `mfderiv` on `Pₖ` because the inner coordinate changes telescope to identity on the chart — `inTangentCoordinates` is `mfderiv` itself when base = moving chart). | partial (telescoping identity; analogous to repo's `framedCocycle_eq`) | medium |
| L6 | Countable Borel partition `Pₖ` of `M` from the countable atlas + `disjointed`. | exists (`secondCountable_of_sigmaCompact`, `countable_cover_nhds_of_sigmaCompact`, `Set.disjointed`, `MeasurableSet.disjointed`) | easy |
| L7 | Glue: `Measurable (fun x => mfderiv I I T x)` from L5+L6. | exists (`measurable_of_measurable_on_countable_cover`, **already in repo**) | easy |
| L8 | (Leaf B only) `MeasurableFraming I T` from L1–L7 using the **constant identity frame** `frame x := .refl ℝ E`; the framed generator is then `= mfderiv` up to `rfl`. | exists (`MeasurableFraming.of_measurablePartitionFrame`, repo; or direct) | easy |

The genuine intellectual content is **L1 + L5** (identify `mfderiv` on a chart with a measurable
Euclidean derivative conjugated by measurable coordinate changes) and **L3** (a clean
`ContinuousOn ⇒ Measurable on Borel set` bridge for the coordinate-change factors). Everything else
is plumbing or already in the repo.

---

## 6. The honest residual risks

1. **Boundary.** Without `[I.Boundaryless]`, L1/L2 break: `mfderiv` is `fderivWithin _ (range I)` and
   Mathlib has no measurable-`fderivWithin`-over-a-set lemma. Proving one (`measurableSet`-of-
   differentiable-within-at over `range I`, then a Borel selection of the derivative) is a real
   Mathlib-scale addition (the `Measurable.lean` file only does it for the full space and for
   `Ici`/`Ioi` one-sided sets). **Recommendation: add `[I.Boundaryless]`.** This is honest and
   standard; the corner case is out of scope for a first formalization of the manifold MET.

2. **`ContinuousOn ⇒ Measurable` genuinely (not ae).** L3 needs that a function continuous on an open
   (or Borel) set `U`, extended arbitrarily off `U`, has a *measurable* restriction to `U`. Mathlib
   has `ContinuousOn.aemeasurable` (`IntegrableOn.lean:712`) — ae only — and
   `ContinuousOn.measurable_piecewise` (`BorelSpace/Basic.lean:508`). The clean statement
   `ContinuousOn f s → MeasurableSet s → Measurable (s.restrict f)` is derivable
   (`continuousOn_iff_continuous_restrict` + `Continuous.measurable` on the subtype with its Borel
   structure, then push forward), but is a small lemma that must be written. Low risk, non-zero work.

3. **The telescoping identity L5.** Showing the conjugated representative equals `mfderiv` *on the
   chart block* is the manifold analogue of the repo's own sorry-free `framedCocycle_eq` /
   `inTangentCoordinates_eq_mfderiv_comp`. It is fiddly `rfl`/`simp` chart algebra (coordinate
   changes at `base = moving chart` collapse to the identity via `tangentCoordChange_self`). Medium
   effort, but a known pattern; the author has already done the harder telescoping in Framing.lean.

4. **Codomain Borel structure.** `E →L[ℝ] E` must carry `[MeasurableSpace] [BorelSpace]` from its
   norm topology; `measurable_fderiv` already lands there, and the repo's `measurable_frameAlg`
   shows the downstream entrywise reduction works. No risk.

---

## 7. Recommended independent strategies (for parallel attempts)

**Strategy α — boundaryless chart-glue, the canonical route (recommended primary).**
Add `[I.Boundaryless]`. Prove L1–L7 exactly as decomposed. Core uses `measurable_fderiv` (no
smoothness, no C²), `inTangentCoordinates_eq_mfderiv_comp`, `continuousOn_tangentCoordChange`, the
σ-compact countable atlas, and the repo's `measurable_of_measurable_on_countable_cover`. No uncached
import; no `ContMDiffMFDeriv`. This is the highest-probability close and the one the issue's own
"plan" describes — but the report's correction is that the Euclidean factor is *free*
(`measurable_fderiv`), so the only real work is L1/L3/L5.

**Strategy β — constant-frame collapse of Leaf B, then α.**
Recognize that with Mathlib's definitional `TangentSpace I x = E`, `frame x := ContinuousLinearEquiv.refl ℝ E`
turns `MeasurableFraming I T`'s obligation into Leaf A verbatim. Prove `exists_measurableFraming_of_sigmaCompact`
*directly* from Leaf A (no disjointified-trivialization construction at all), and prove Leaf A by α.
This discharges **both** leaves from one analytic core and deletes the `Existence.lean` docstring's
(unnecessary) `Trivialization.continuousLinearEquivAt` plan. Independent of α only in *packaging*;
worth a separate agent because it may reveal that Leaf B needs *strictly less* than Leaf A if one is
willing to use a non-identity measurable frame.

**Strategy γ — C² route via `ContMDiffAt.mfderiv_const` (continuity ⇒ measurability).**
Strengthen `hT` from `MDifferentiable` to `ContMDiff I I 2 T` (or `[IsManifold I 2 M]` + `ContMDiff …`).
Then `ContMDiffAt.mfderiv_const` (`ContMDiffMFDeriv.lean:242`, `m = 0`, `n = 2`) gives that
`x ↦ inTangentCoordinates I I id T (mfderiv I I T) x₀ x` is *continuous* near each `x₀`; continuity on
a chart neighbourhood ⇒ measurability on a Borel block ⇒ glue with the repo lemma. **Cost:** the
`ContMDiffMFDeriv` import chain is not in the precompiled cache here (multi-hour from-source rebuild
per the module docstrings) and the hypothesis jumps to C². **Use only if α's L1/L5 chart algebra
proves intractable** — γ trades a from-source build + stronger hypothesis for avoiding the manual
telescoping. Genuinely independent proof route.

**Strategy δ — measurable selection / Borel-isomorphism abstraction (research fallback).**
Phrase the tangent bundle as a standard-Borel vector bundle and invoke a Kuratowski–Ryll-Nardzewski /
measurable-selection trivialization (the literature's actual mechanism). Mathlib has measurable
selection (`MeasurableSet.exists_measurable_proj`, KRN in `MeasureTheory/MeasurableSpace`), but **no**
standard-Borel vector-bundle API, so this would require building that scaffolding first. High effort,
low near-term payoff; list it for completeness as the "if α–γ all stall" route. Not recommended as a
first parallel attempt.

---

## 8. Honest verdict

This is **not** a multi-year wall, and it is **not** a free one-liner. With the two corrections this
report surfaces — (i) `measurable_fderiv` is *unconditional*, so the Euclidean derivative is
measurable with no smoothness, and (ii) the definitional `TangentSpace I x = E` lets Leaf B reuse a
**constant** frame so it collapses into Leaf A — the honest core is a single Borel-measurability
theorem `Measurable (fun x => mfderiv I I T x)` provable in current Mathlib by chart-local gluing.
The realistic cost is on the order of **150–350 lines** of new Lean: one `ContinuousOn ⇒ Measurable
on a Borel set` helper (L3), the chart-local `inTangentCoordinates`-to-`mfderiv` telescoping identity
(L1/L5, patterned on the repo's existing `framedCocycle_eq`), and assembly through the repo's
already-proved `measurable_of_measurable_on_countable_cover`. The one non-negotiable concession is
adding `[I.Boundaryless]` (no Mathlib `measurable_fderivWithin` over `range I` exists); this is
standard and honest for an MET formalization. The residual risk is in the chart-algebra `simp`/`rfl`
telescoping (fiddly but a known pattern here) and in confirming the codomain Borel structure threads
cleanly — both medium, neither a research wall. I would put **~70%** on a competent Lean agent
closing both leaves sorry-free within a focused effort under Strategy α/β, conditional on accepting
`[I.Boundaryless]`; **~40%** without that concession (then Strategy γ's C² route or a new
`measurable_fderivWithin` lemma becomes load-bearing, and γ additionally pays a multi-hour
from-source rebuild for the `ContMDiffMFDeriv` import that is uncached in this environment). It is a
**partial decomposition that is genuinely closeable**, not a wall — provided the boundaryless
hypothesis is allowed.
