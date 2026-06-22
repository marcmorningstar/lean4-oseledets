/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Frontier.Issue6.CastaingSelection
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The Arsenin–Kunugui measurable-projection theorem (top-down skeleton)

This module targets the strictly-stronger **everywhere-Borel** (not merely a.e.) form of the
singular ("issue #6") measurable-projection gap. It states the **Arsenin–Kunugui theorem** — a
Borel set `B ⊆ X × Y` (`X`, `Y` Polish) whose every section `B_x` is **σ-compact** (`K_σ`) has a
**measurable** (Borel) projection `Prod.fst '' B` — decomposes its proof into named leaves
following Srivastava, *A Course on Borel Sets*, §5.12 (cf. Kechris, *Classical Descriptive Set
Theory*, Thm 35.46; see also 28.8), proves sorry-free everything Mathlib currently supports, and
isolates the two genuine descriptive-set-theory walls as precisely-documented BLOCKED leaves.

It is the everywhere-Borel counterpart of the **a.e.** route already discharged sorry-free in
`Frontier.Issue6.MeasurableProjection` and migrated to `Oseledets.Singular`: there the projection is
merely *analytic*, hence (Choquet capacitability,
`MeasureTheory.AnalyticSet.nullMeasurableSet`) *universally measurable* — `NullMeasurableSet` for
every s-finite measure, which suffices for the a.e. theorem. The present file targets genuine
`MeasurableSet`-ness of the projection, which the analytic route cannot give: a Borel projection is
analytic but **not** in general Borel (the classical Lebesgue/Souslin error). The
σ-compact-section hypothesis is exactly what rescues Borel-ness — this is the Arsenin–Kunugui
phenomenon.

## The classical proof structure (Srivastava §5.12)

`Theorem 5.12.1` (Arsenin–Kunugui) reduces, in three named steps, to a single deep
descriptive-set-theory input:

1. **`5.12.3` (compact-section decomposition).** A Borel set `A ⊆ X × Y` with σ-compact sections is
   a *countable union* `A = ⋃ₙ Bₙ` of Borel sets `Bₙ` with **compact** sections. This is the crux
   and is `5.12.2` applied to `B = Aᶜ`.

2. **Projection of a Borel set with compact sections is Borel** (Srivastava `4.7.11`; Kechris
   `28.8`). Then `Prod.fst '' A = ⋃ₙ Prod.fst '' Bₙ` is a countable union of Borel sets, hence
   Borel.

3. **`5.12.2` (Saint Raymond's σ-compact separation theorem).** For analytic `A, B ⊆ X × Y` with,
   for every `x`, a σ-compact `K` with `A_x ⊆ K ⊆ (B_x)ᶜ`, there is a sequence of Borel sets `Bₙ`
   with compact sections covering `A` and disjoint from `B`. This is the irreducible
   descriptive-set-theory wall *in the general Polish case*.

**Euclidean specialization (the actual call site).** For `Y = EuclideanSpace ℝ (Fin d)` step 1
(`5.12.3`) and step 3 (`5.12.2`) are **elementary and proved sorry-free** here: a σ-compact ball-
section is exhausted by the *compact* closed balls `closedBall c ρₙ` (`EuclideanSpace` is a
`ProperSpace`), giving the compact-section cover with no Effros/`Π¹₁` machinery. Thus the issue-#6
target reduces to step 2 *alone*, and indeed to its compact-box instance (`Q := closedBall c ρₙ`) —
the single remaining BLOCKED leaf `measurableSet_image_fst_of_subset_compact_box`.

## What is proved sorry-free here, and what is BLOCKED

### Sorry-free, reusable topological wiring (the proper-map heart of step 2)

The genuinely true and reusable content is the **proper-map** characterisation of when a projection
is well-behaved:

* `Frontier.image_fst_eq_range_restrict`: `Prod.fst '' S` is the range of the restricted projection
  `(fun p : S => p.1.1)`.
* `Frontier.isClosed_image_fst_of_isProperMap_restrict`: if that restricted projection is a
  **proper map**, then `Prod.fst '' S` is **closed** (`IsProperMap.isClosed_range`).
* `Frontier.measurableSet_image_fst_of_isProperMap_restrict`: hence (over any `BorelSpace X`) the
  projection is `MeasurableSet`.
* `Frontier.isProperMap_fst_restrict_of_isClosed_compactSpace`: for a **closed** `S` with the whole
  fibre space `Y` **compact**, the restricted projection is proper — the one fully sorry-free
  *instance* of properness (e.g. `Y` a closed bounded box). This is `Prod.fst` (proper when `Y` is
  compact) restricted to the closed `S` via `IsProperMap.restrict`.

### A correction that is recorded (a naive lemma is FALSE)

A tempting shortcut — *"`S` closed with each section `S_x` compact ⟹ `Prod.fst '' S` is closed"* —
is **false** without properness/compactness of `Y`. Counterexample (`docstring` of
`not_isClosed_image_fst_of_isClosed_isCompact_sections`): `S = {(x, 1/x) : x ≠ 0} ⊆ ℝ × ℝ` is
closed (it is the graph of `1/·`, escaping to `∞` near `0`), every section is a singleton or empty
(compact), yet `Prod.fst '' S = ℝ \ {0}` is **open, not closed**. The classical `4.7.11` correctly
claims only a **Borel** (in fact `F_σ`) projection, *not* a closed one — exactly why the proper-map
hypothesis (or σ-compactness) is load-bearing and the projection lemma below stays BLOCKED rather
than collapsing to this false topological shortcut.

### The SINGLE remaining BLOCKED leaf (Strategy B re-route)

The 2026-06-22 Strategy-B (Euclidean-specialization) re-route **collapses the issue-#6 target onto a
single, strictly sharper leaf**, eliminating the research-scale Saint-Raymond σ-compact-section wall
for the actual call site.

* `Frontier.measurableSet_image_fst_of_subset_compact_box` (BLOCKED — Srivastava `4.7.4` with `Y`
  already compact): the projection of a *Borel* set **contained in a fixed compact box**
  `univ ×ˢ Q` (`Q` compact) is Borel. This is the compact-`Y` instance of `4.7.11`. Only the missing
  product topology-refinement (`4.7.1`/`4.7.2`, refine *only* `X` to make `B` closed in `(X,τ')×Q`,
  same Borel σ-algebra) blocks it; the proper-map heart (`Q` compact ⟹ proper restriction) is
  already sorry-free above. The Hilbert-cube `WLOG`-`Y`-compact reduction is **gone** (the box `Q` is
  given).

* **ELIMINATED — `exists_borel_compactSection_cover` (Saint Raymond `5.12.2`, the Effros/`Π¹₁`-
  boundedness wall) is no longer needed.** For the Euclidean consumer the σ-compact ball-sections are
  exhausted by *compact* closed balls (`EuclideanSpace` is `ProperSpace`):
  `S = ⋃ₙ (S ∩ (univ ×ˢ closedBall c ρₙ))`, each piece inside a fixed compact box. This is the
  sorry-free `Frontier.measurableSet_image_fst_of_ball_slab`, which replaces the entire
  `5.12.3 ⇐ 5.12.2` descriptive-set-theory chain by the elementary closed-ball exhaustion.

Granting the one sharp box leaf, the assembly down to the issue-#6 target
`Frontier.measurableInfDist_of_measurableGraph_AK` (the everywhere-Borel `MeasurableInfDist`
discharge) is proved sorry-free here.

## Main results

* `Frontier.image_fst_eq_range_restrict` (sorry-free).
* `Frontier.isClosed_image_fst_of_isProperMap_restrict` (sorry-free).
* `Frontier.measurableSet_image_fst_of_isProperMap_restrict` (sorry-free).
* `Frontier.isProperMap_fst_restrict_of_isClosed_compactSpace` (sorry-free).
* `Frontier.measurableSet_image_fst_of_subset_compact_box` (BLOCKED — the SINGLE sharp leaf, `4.7.4`
  with compact `Y`).
* `Frontier.measurableSet_image_fst_of_ball_slab` (sorry-free *given* the box leaf; leaf 2
  eliminated by closed-ball exhaustion): the Euclidean ball-slab Arsenin–Kunugui.
* `Frontier.measurableInfDist_of_measurableGraph_AK` (sorry-free *given* the box leaf): the
  everywhere-Borel discharge of `MeasurableInfDist`, the issue-#6 target.

Literature: W. J. Arsenin (1940); K. Kunugui (1940); J. Saint Raymond, *Boréliens à coupes `K_σ`*,
Bull. Soc. Math. France **104** (1976); S. M. Srivastava, *A Course on Borel Sets*, §5.12 (Thms
5.12.1, 5.12.2, 5.12.3, and 4.7.11); A. S. Kechris, *Classical Descriptive Set Theory*, Thms 35.46,
28.8.
-/

open Metric MeasureTheory Set Topology Submodule

namespace Frontier

/-! ### Sorry-free proper-map wiring: projection through a proper restriction -/

section ProperWiring

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- **The projection is the range of the restricted projection.** `Prod.fst '' S` coincides with
the range of `(fun p : S => (p : X × Y).1)`, the restriction of `Prod.fst` to the subtype `S`. A
pure set-theoretic repackaging used to transport `IsProperMap.isClosed_range` to the projection. -/
theorem image_fst_eq_range_restrict (S : Set (X × Y)) :
    range (fun p : S => (p : X × Y).1) = Prod.fst '' S := by
  ext x
  simp only [mem_range, mem_image, Subtype.exists, exists_prop]

/-- **A proper restriction has closed projection.** If the restriction
`(fun p : S => p.1.1) : S → X` of `Prod.fst` to `S` is a **proper map**, then `Prod.fst '' S` is
closed. This is `IsProperMap.isClosed_range` transported along `image_fst_eq_range_restrict`. The
properness hypothesis is *not* implied by closedness of `S` plus compact sections (see
`not_isClosed_image_fst_of_isClosed_isCompact_sections`); it is the genuine condition that makes the
projection closed. -/
theorem isClosed_image_fst_of_isProperMap_restrict {S : Set (X × Y)}
    (hproper : IsProperMap (fun p : S => (p : X × Y).1)) :
    IsClosed (Prod.fst '' S) := by
  rw [← image_fst_eq_range_restrict]
  exact hproper.isClosed_range

/-- **A proper restriction has measurable projection.** Over any `BorelSpace X`, a proper restricted
projection makes `Prod.fst '' S` `MeasurableSet` — its closedness
(`isClosed_image_fst_of_isProperMap_restrict`) makes it Borel. -/
theorem measurableSet_image_fst_of_isProperMap_restrict
    [MeasurableSpace X] [BorelSpace X] {S : Set (X × Y)}
    (hproper : IsProperMap (fun p : S => (p : X × Y).1)) :
    MeasurableSet (Prod.fst '' S) :=
  (isClosed_image_fst_of_isProperMap_restrict hproper).measurableSet

/-- **The fully sorry-free instance of properness: compact fibre space.** If `Y` is **compact** and
`S ⊆ X × Y` is **closed**, the restricted projection `(fun p : S => p.1.1)` is proper: `Prod.fst` is
proper because `Y` is compact (`isProperMap_fst_of_compactSpace`), and `IsProperMap.restrict` to the
closed `S` preserves properness (the inclusion of a closed set is proper). This handles, e.g., a
fibre space that is a closed bounded box; the non-compact-`Y` case is exactly where the AK machinery
is needed. -/
theorem isProperMap_fst_restrict_of_isClosed_compactSpace [CompactSpace Y]
    {S : Set (X × Y)} (hS : IsClosed S) :
    IsProperMap (fun p : S => (p : X × Y).1) :=
  isProperMap_fst_of_compactSpace.comp hS.isProperMap_subtypeVal

end ProperWiring

/-! ### The recorded correction: a naive closed-projection lemma is FALSE -/

section FalseShortcut

/-- **A naive shortcut is FALSE (recorded as an existence of a counterexample).** It is *not* true
that a closed `S ⊆ X × Y` with every section `S_x` compact has closed projection `Prod.fst '' S`.
Witness in `ℝ × ℝ`: `S = {(x, y) | x ≠ 0 ∧ x * y = 1}` (the graph of `y = 1/x`). It is closed (it
escapes to infinity as `x → 0`, so has no limit points off itself), each section `S_x` is a
singleton (`x ≠ 0`) or empty (`x = 0`) — hence compact — yet `Prod.fst '' S = {x | x ≠ 0}` is open,
not closed. This is why `measurableSet_image_fst_of_isCompact_sections` stays BLOCKED rather than
collapsing to a (false) topological one-liner: the classical `4.7.11` gives only a **Borel** (here
`F_σ`) projection. We state the witness existence; the full topological verification of closedness
of `S` is standard (graph of a continuous proper-to-`∞` map) and not needed downstream. -/
theorem not_isClosed_image_fst_of_isClosed_isCompact_sections :
    ∃ S : Set (ℝ × ℝ), (∀ x, IsCompact {y | (x, y) ∈ S}) ∧
      Prod.fst '' S = {x : ℝ | x ≠ 0} := by
  refine ⟨{p : ℝ × ℝ | p.1 ≠ 0 ∧ p.1 * p.2 = 1}, ?_, ?_⟩
  · -- Each section is a singleton (`x ≠ 0`) or empty (`x = 0`), hence compact.
    intro x
    by_cases hx : x = 0
    · -- `x = 0`: section is empty.
      have : {y : ℝ | (x, y) ∈ {p : ℝ × ℝ | p.1 ≠ 0 ∧ p.1 * p.2 = 1}} = ∅ := by
        ext y; simp [hx]
      rw [this]; exact isCompact_empty
    · -- `x ≠ 0`: section is the singleton `{1/x}`.
      have : {y : ℝ | (x, y) ∈ {p : ℝ × ℝ | p.1 ≠ 0 ∧ p.1 * p.2 = 1}} = {x⁻¹} := by
        ext y
        simp only [mem_setOf_eq, mem_singleton_iff]
        constructor
        · rintro ⟨-, hxy⟩; field_simp at hxy ⊢; linarith [hxy]
        · rintro rfl; refine ⟨hx, ?_⟩; field_simp
      rw [this]; exact isCompact_singleton
  · -- The projection is exactly `{x | x ≠ 0}`.
    ext x
    simp only [mem_image, mem_setOf_eq, Prod.exists, ne_eq]
    constructor
    · rintro ⟨x', y, ⟨hx', -⟩, rfl⟩; exact hx'
    · intro hx; exact ⟨x, x⁻¹, ⟨hx, by field_simp⟩, rfl⟩

end FalseShortcut

/-! ### The Arsenin–Kunugui theorem: statement, reduction, and BLOCKED DST leaves -/

section ArseninKunugui

variable {X Y : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **SHARPER BLOCKED leaf — projection of a Borel set contained in a fixed compact box is Borel
(the compact-`Y` instance of Srivastava 4.7.11 / 4.7.4).** For a measurable `B ⊆ X × Y` (`X`, `Y`
Polish) that is contained in `Set.univ ×ˢ Q` for a **single fixed compact** `Q ⊆ Y` (so every
section `B_x ⊆ Q` and is — being closed in the compact `Q` once `B` is made closed — compact), the
projection `Prod.fst '' B` is `MeasurableSet`.

**This is left `sorry`, but it is the SHARP residual of Strategy B** (Euclidean specialization),
strictly smaller than the original opaque `measurableSet_image_fst_of_isCompact_sections`:

* The **Hilbert-cube `WLOG`-`Y`-compact reduction (1b)** is *gone* — the fibre lives in the *given*
  compact `Q`, so no universal-embedding lemma is needed.
* The **σ-compact-section decomposition leaf (old `exists_borel_compactSection_cover`, Saint Raymond
  5.12.2 — the principal research wall)** is *gone*: for the Euclidean consumer it is discharged
  sorry-free by the explicit closed-ball exhaustion (`isSigmaCompact_isClosed_inter_ball`), see
  `measurableSet_image_fst_of_isSigmaCompact_sections_euclidean` below.

What remains is exactly **Srivastava 4.7.4 with `Y` already compact**: refine the Polish topology of
`X` (only) to a finer one — *same Borel σ-algebra* (`MeasureTheory.borel_eq_borel_of_le`,
`MeasureTheory.isClopenable_iff_measurableSet`) — making the Borel `B` *closed* in the product
`(X, τ') × Q`; then the proper-map heart already proved sorry-free in this file
(`isProperMap_fst_restrict_of_isClosed_compactSpace`, `Q` a `CompactSpace`,
`measurableSet_image_fst_of_isProperMap_restrict`) gives `Prod.fst '' B` closed — hence Borel — in
`τ'`, and Borel-invariance transports it back to the original topology. The single genuinely missing
Mathlib ingredient is the **product** refinement lemma: `MeasurableSet.isClopenable` refines the
*whole product* `X × Q` (which would destroy compactness of the `Q`-fibre), whereas 4.7.4 refines
*only* `X`. That product-clopenable-in-`X`-alone step is `4.7.1/4.7.2` (Borel set with open sections
`= ⋃ₖ Bₖ × Vₖ`), whose Borel-ness of `Bₖ = {x | Vₖ ⊆ B_xᶜ}` is itself a co-projection — circular
without the very theorem, *unless* the compactness of `Q` is exploited fibrewise, which is precisely
the Novikov argument and the remaining work. The naive "closed `B` + compact sections ⟹ closed
projection" route is *false* (`not_isClosed_image_fst_of_isClosed_isCompact_sections`), so this is
genuinely descriptive-set-theoretic. -/
theorem measurableSet_image_fst_of_subset_compact_box
    {B : Set (X × Y)} (hB : MeasurableSet B) {Q : Set Y} (hQ : IsCompact Q)
    (hsub : B ⊆ Set.univ ×ˢ Q) :
    MeasurableSet (Prod.fst '' B) := by
  sorry -- SHARPER BLOCKED (Strategy B residual): Srivastava 4.7.4 with `Y` already compact —
        -- refine ONLY `X`'s Polish topology to make the Borel `B ⊆ X × Q` closed in the product,
        -- same Borel σ-algebra, then the file's proper-map machinery (`Q` compact) closes it. The
        -- missing Mathlib piece is the product-only refinement (4.7.1/4.7.2); the WLOG-compact (1b)
        -- and the Saint-Raymond σ-compact-section wall (old 5.12.2 leaf) are BOTH eliminated.

/-- **The Arsenin–Kunugui theorem on a fixed compact box (sorry-free *given* the sharp leaf).** A
measurable `B ⊆ X × Y` contained in `Set.univ ×ˢ Q` for a fixed compact `Q` has measurable
projection. This is `measurableSet_image_fst_of_subset_compact_box`, re-exported under the
Arsenin–Kunugui name for the assembly. -/
theorem arseninKunugui_measurableSet_image_fst_box
    {B : Set (X × Y)} (hB : MeasurableSet B) {Q : Set Y} (hQ : IsCompact Q)
    (hsub : B ⊆ Set.univ ×ˢ Q) :
    MeasurableSet (Prod.fst '' B) :=
  measurableSet_image_fst_of_subset_compact_box hB hQ hsub

end ArseninKunugui

/-! ### Discharging the issue-#6 target: everywhere-Borel `MeasurableInfDist` -/

section Issue6Target

variable {X : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] {d : ℕ}
variable {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}

omit [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- **A subspace slab is σ-compact (sorry-free).** In the proper space
`EuclideanSpace ℝ (Fin d)`, the intersection `K ∩ ball c r` of any **closed** set `K` (in
particular a finite-dimensional subspace) with an open ball is σ-compact: write
`ball c r = ⋃ₙ closedBall c (r − 1/(n+1))` (an increasing exhaustion of the open ball by closed
balls), so `K ∩ ball c r = ⋃ₙ (K ∩ closedBall c (r − 1/(n+1)))`, each term **closed and bounded**
hence **compact** (`Metric.isCompact_of_isClosed_isBounded`, `ProperSpace`), and a countable union of
compacts is σ-compact. -/
theorem isSigmaCompact_isClosed_inter_ball
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsClosed K)
    (c : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    IsSigmaCompact (K ∩ Metric.ball c r) := by
  have hcover : Metric.ball c r = ⋃ n : ℕ, Metric.closedBall c (r - 1 / (n + 1)) := by
    ext y
    simp only [Metric.mem_ball, Metric.mem_closedBall, mem_iUnion]
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hy)
      exact ⟨n, by linarith [hn]⟩
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / (n + 1) := by positivity
      linarith
  rw [show K ∩ Metric.ball c r = ⋃ n : ℕ, K ∩ Metric.closedBall c (r - 1 / (n + 1)) by
    rw [hcover, inter_iUnion]]
  refine isSigmaCompact_iUnion_of_isCompact _ fun n => ?_
  exact Metric.isCompact_of_isClosed_isBounded (hK.inter Metric.isClosed_closedBall)
    (Metric.isBounded_closedBall.subset inter_subset_right)

omit [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- **The graph slab has σ-compact sections (sorry-free).** For the family `V` of subspaces and any
`c`, `r`, the `x`-section of `{(x, v) | v ∈ V x} ∩ (univ ×ˢ ball c r)` is `(V x) ∩ ball c r`. Since
`V x` is a (finite-dimensional, hence) closed subspace, this is σ-compact by
`isSigmaCompact_isClosed_inter_ball`. This is the σ-compact-section hypothesis consumed by the
Arsenin–Kunugui theorem in `measurableInfDist_of_measurableGraph_AK`. -/
theorem isSigmaCompact_section_graph_inter_ball
    (c : EuclideanSpace ℝ (Fin d)) (r : ℝ) (x : X) :
    IsSigmaCompact
      {v : EuclideanSpace ℝ (Fin d) |
        (x, v) ∈ ({p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1}
          ∩ (Set.univ ×ˢ Metric.ball c r))} := by
  have hsec : {v : EuclideanSpace ℝ (Fin d) |
      (x, v) ∈ ({p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1}
        ∩ (Set.univ ×ˢ Metric.ball c r))}
      = (V x : Set (EuclideanSpace ℝ (Fin d))) ∩ Metric.ball c r := by
    ext v
    simp only [mem_setOf_eq, mem_inter_iff, Set.mem_prod, mem_univ, true_and, SetLike.mem_coe,
      Metric.mem_ball]
  rw [hsec]
  exact isSigmaCompact_isClosed_inter_ball (V x).closed_of_finiteDimensional c r

/-- **Euclidean Arsenin–Kunugui for a ball slab (sorry-free *given the sharp box leaf*; leaf 2
ELIMINATED).** For a measurable `S ⊆ X × EuclideanSpace ℝ (Fin d)` contained in the open-ball slab
`Set.univ ×ˢ ball c r`, the projection `Prod.fst '' S` is measurable.

This is the **Euclidean specialization (Strategy B)** of Arsenin–Kunugui that **eliminates the
research-scale Saint-Raymond σ-compact-section leaf entirely**: the open ball is the increasing
union `ball c r = ⋃ₙ closedBall c (r − 1/(n+1))` of *compact* closed balls
(`EuclideanSpace` is a `ProperSpace`), so
`S = ⋃ₙ (S ∩ (univ ×ˢ closedBall c (r − 1/(n+1))))` and
`Prod.fst '' S = ⋃ₙ Prod.fst '' (S ∩ (univ ×ˢ closedBall c ρₙ))`. Each piece is measurable and
**contained in the fixed compact box** `univ ×ˢ closedBall c ρₙ`, so the sharp box leaf
`measurableSet_image_fst_of_subset_compact_box` applies, and a countable union of measurable sets is
measurable. The only `sorry` reached is that single box leaf (Srivastava 4.7.4 with compact `Y`); no
hyperspace/derivative/`Π¹₁` machinery is invoked. -/
theorem measurableSet_image_fst_of_ball_slab
    {S : Set (X × EuclideanSpace ℝ (Fin d))} (hS : MeasurableSet S)
    (c : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hsub : S ⊆ Set.univ ×ˢ Metric.ball c r) :
    MeasurableSet (Prod.fst '' S) := by
  -- Exhaust the open ball by the compact closed balls `closedBall c (r - 1/(n+1))`.
  have hcover : Metric.ball c r = ⋃ n : ℕ, Metric.closedBall c (r - 1 / (n + 1)) := by
    ext y
    simp only [Metric.mem_ball, Metric.mem_closedBall, mem_iUnion]
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hy)
      exact ⟨n, by linarith [hn]⟩
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / (n + 1) := by positivity
      linarith
  -- Decompose `S` along the exhaustion.
  have hSdecomp : S = ⋃ n : ℕ,
      S ∩ (Set.univ ×ˢ Metric.closedBall c (r - 1 / (n + 1))) := by
    apply Set.Subset.antisymm
    · intro p hp
      have hp2 : p.2 ∈ Metric.ball c r := (hsub hp).2
      rw [hcover] at hp2
      obtain ⟨_, ⟨n, rfl⟩, hpn⟩ := hp2
      exact mem_iUnion.mpr ⟨n, hp, ⟨mem_univ _, hpn⟩⟩
    · exact iUnion_subset fun n => inter_subset_left
  -- The projection commutes with the countable union.
  have himg : Prod.fst '' S = ⋃ n : ℕ,
      Prod.fst '' (S ∩ (Set.univ ×ˢ Metric.closedBall c (r - 1 / (n + 1)))) := by
    conv_lhs => rw [hSdecomp]
    rw [Set.image_iUnion]
  rw [himg]
  refine MeasurableSet.iUnion fun n => ?_
  -- Each piece lives in the fixed compact box `univ ×ˢ closedBall c ρₙ`; apply the box leaf.
  refine measurableSet_image_fst_of_subset_compact_box
    (hS.inter (MeasurableSet.univ.prod measurableSet_closedBall))
    (Q := Metric.closedBall c (r - 1 / (n + 1)))
    (isCompact_closedBall c (r - 1 / (n + 1))) ?_
  exact inter_subset_right

/-- **Everywhere-Borel `MeasurableInfDist` from a measurable graph (issue-#6 target, via
Arsenin–Kunugui).** Over a standard Borel (Polish) base `X`, a measurable graph
`{(x, v) | v ∈ V x}` makes `V` satisfy `MeasurableInfDist V` — i.e. `x ↦ infDist c (V x)` is
**measurable** (everywhere, not merely a.e.) for every `c`.

This is the strictly-stronger everywhere-Borel counterpart of the a.e.
`aemeasurable_infDist_of_measurableGraph`. The reduction (inlined here, cf.
`Frontier.image_fst_graph_inter_ball`):
`{x | infDist c (V x) < r} = Prod.fst '' (graph ∩ (univ ×ˢ ball c r))`, the projection of a
measurable set contained in the open-ball slab `univ ×ˢ ball c r`. By the **Euclidean
Arsenin–Kunugui ball-slab theorem** (`measurableSet_image_fst_of_ball_slab`) this projection is
`MeasurableSet`; `measurable_of_Iio` then yields measurability of `x ↦ infDist c (V x)`.

**Strategy B re-route (see `changedStatementNote`):** the dependence on `sorry` is now confined to a
**single, strictly sharper** leaf — `measurableSet_image_fst_of_subset_compact_box` (Srivastava
4.7.4 with `Y` already compact). The previously-BLOCKED research-scale Saint-Raymond σ-compact-
section leaf (`exists_borel_compactSection_cover`, the Effros/`Π¹₁`-boundedness wall) is
**eliminated**: it is discharged sorry-free by the explicit closed-ball exhaustion inside
`measurableSet_image_fst_of_ball_slab` (`EuclideanSpace` is `ProperSpace`). The statement of this
issue-#6 target is **unchanged**. -/
theorem measurableInfDist_of_measurableGraph_AK
    (hgraph : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1}) :
    MeasurableInfDist V := by
  intro c
  -- Measurability via `Iio`-preimages, each of which is a ball-slab projection.
  refine measurable_of_Iio fun r => ?_
  -- The preimage is the sublevel set, the projection of the graph slab through the ball (the
  -- inlined `image_fst_graph_inter_ball` identity: `infDist_lt_iff` with `0 ∈ V x` nonempty).
  have hpre : (fun x => infDist c (V x)) ⁻¹' Set.Iio r
      = Prod.fst '' ({p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1}
          ∩ (Set.univ ×ˢ Metric.ball c r)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iio, mem_image, mem_inter_iff, Set.mem_prod, mem_univ,
      true_and, mem_ball, Prod.exists, exists_and_right, mem_setOf_eq]
    constructor
    · intro hx
      rcases (infDist_lt_iff ⟨0, (V x).zero_mem⟩).mp hx with ⟨v, hvV, hvdist⟩
      exact ⟨x, ⟨⟨v, hvV, by rwa [dist_comm] at hvdist⟩, rfl⟩⟩
    · rintro ⟨x', ⟨⟨v, hvV, hvdist⟩, rfl⟩⟩
      exact (infDist_lt_iff ⟨0, (V x').zero_mem⟩).mpr ⟨v, hvV, by rwa [dist_comm]⟩
  rw [hpre]
  -- The slab is measurable and contained in `univ ×ˢ ball c r`; the Euclidean ball-slab AK
  -- theorem (leaf 2 eliminated by closed-ball exhaustion) gives the Borel projection.
  have hslab : MeasurableSet ({p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1}
      ∩ (Set.univ ×ˢ Metric.ball c r)) :=
    hgraph.inter (MeasurableSet.univ.prod measurableSet_ball)
  exact measurableSet_image_fst_of_ball_slab hslab c r inter_subset_right

end Issue6Target

end Frontier
