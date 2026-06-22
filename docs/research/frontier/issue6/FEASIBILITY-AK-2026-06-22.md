# Feasibility report — Arsenin–Kunugui measurable projection (Issue #11)

**Date:** 2026-06-22
**Scope:** the two BLOCKED leaves in `Frontier/Issue6/ArseninKunugui.lean`:
- `measurableSet_image_fst_of_isCompact_sections` (~line 236, Srivastava **4.7.11** / Novikov; Kechris 28.8)
- `exists_borel_compactSection_cover` (~line 266, Srivastava **5.12.3 ⇐ 5.12.2**, Saint Raymond σ-compact separation)

Downstream auto-discharge once both close: `Frontier/Issue6/CastaingSelection.lean:479`
(`measurableInfDist_of_measurableGraph`), `Frontier/Issue6/MeasurableGraphToProjector.lean:405`
(`exists_measurable_independentSpanningFrame_of_measurableGraph`), and the issue-#6 everywhere-Borel
target `measurableInfDist_of_measurableGraph_AK` (already sorry-free *given* the two leaves).

**TL;DR verdict.** Leaf 2 (`exists_borel_compactSection_cover`) is a genuine multi-component
**research wall** (Effros Borel hyperspace + transfinite derivative ranks + Π¹₁-boundedness + WO/LO
codings — none in Mathlib). Leaf 1 (`measurableSet_image_fst_of_isCompact_sections`, Novikov 4.7.11)
is **partially decomposable and meaningfully closer**: Srivastava's *first* proof of 4.7.11 uses
only (a) refine the topology on `X` to make `B` closed in the product, (b) `Y` compact ⟹ projection
closed (proper map), (c) Borel σ-algebra invariant under the refinement. Mathlib already has the
proper-map half sorry-free in this very file, plus `MeasurableSet.isClopenable`,
`isClopenable_iff_measurableSet`, `borel_eq_borel_of_le`, and `Measurable.exists_continuous`. The one
true missing piece is a **product** version of the topology-refinement / Borel-invariance
(Srivastava 4.7.4 = "Borel set with closed sections ⟹ finer Polish topology on `X` making it closed
in `X×Y`, same Borel σ-algebra"), plus the Hilbert-cube WLOG-`Y`-compact reduction. That is a
**hard but Mathlib-scale** development, *not* a research wall — and it does NOT depend on leaf 2.

No existing Mathlib analytic-set lemma shortcuts EITHER leaf to a closed proof: the analytic route
(`AnalyticSet`, `MeasureTheory.AnalyticSet.nullMeasurableSet`) only delivers *universal*
measurability (the a.e. theorem already discharged in `MeasurableProjection`), never genuine
`MeasurableSet`-ness of the projection. So neither leaf is "closeable-now" via analytic-set theory.

---

## 1. Precise Lean types of the two leaves

```lean
-- Leaf 1 (Srivastava 4.7.11 / Novikov)
theorem measurableSet_image_fst_of_isCompact_sections
    {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {B : Set (X × Y)} (hB : MeasurableSet B)
    (hsec : ∀ x, IsCompact {y | (x, y) ∈ B}) :
    MeasurableSet (Prod.fst '' B)

-- Leaf 2 (Srivastava 5.12.3 ⇐ 5.12.2, Saint Raymond)
theorem exists_borel_compactSection_cover
    {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {A : Set (X × Y)} (hA : MeasurableSet A)
    (hsec : ∀ x, IsSigmaCompact {y | (x, y) ∈ A}) :
    ∃ B : ℕ → Set (X × Y), (∀ n, MeasurableSet (B n)) ∧
      (∀ n x, IsCompact {y | (x, y) ∈ B n}) ∧ A = ⋃ n, B n
```

The assembly `arseninKunugui_measurableSet_image_fst` (line 284) and the issue-#6 discharge
`measurableInfDist_of_measurableGraph_AK` (line 373) are already sorry-free *given* these two.
The reduction wiring is verified correct (`Set.image_iUnion`, `MeasurableSet.iUnion`,
`measurable_of_Iio`, `infDist_lt_iff`).

---

## 2. The literature proof, precisely (Srivastava §5.12 + §4.7)

### 2.1 Leaf 1 — Theorem 4.7.11 (Novikov): projection of Borel set with compact sections is Borel

Srivastava gives **two** proofs. Both reduce to `Y` compact first.

> **Proof (Srivastava).** Since every Polish space is homeomorphic to a Gδ subset of the Hilbert
> cube `H`, WLOG `Y` is a compact metric space. The sections `B_x` are closed in `Y`. By **4.7.4**
> there is a finer Polish topology on `X` generating the *same* Borel σ-algebra and making `B`
> *closed* in `X × Y`. Hence by **2.3.24** [`π_X(B)` is closed when `Y` is compact and `B` is
> closed] `π_X(B)` is closed in `X` (new topology). But the Borel structure of `X` is the same for
> both topologies. ∎

The supporting lemmas:
- **4.7.4** (Cor.): `B ⊆ X×Y` Borel with closed sections ⟹ ∃ finer Polish topology `T` on `X`,
  same Borel σ-algebra, with `B` closed in the product `(X,T)×Y`. (Itself from 4.7.1/4.7.2:
  structure theorem for Borel sets with open sections, via the first separation theorem.)
- **2.3.24**: if `Y` is compact then `π_X : X×Y → X` is a closed map (`π_X(F)` closed for `F`
  closed). [This is exactly the proper-map fact already in our file.]

This is the route to mechanize. Note 4.7.11 is **independent of the §5.12 hyperspace machinery** —
the file's docstring overstates by saying leaf 1 "again [needs] the hyperspace-derivative machinery
of 5.12.3". The first Novikov proof does **not**.

### 2.2 Leaf 2 — Theorem 5.12.2 (Saint Raymond) ⟹ 5.12.3

> **5.12.3.** `X,Y` Polish, `A ⊆ X×Y` Borel with `A_x` σ-compact ⟹ `A = ⋃ₙ Bₙ`, `Bₙ` Borel with
> `(Bₙ)_x` compact. *Proof:* immediate from **5.12.2** with `B = Aᶜ` (then `A_x ⊆ K ⊆ (B_x)ᶜ = A_x`
> with `K` σ-compact, trivially). ∎

> **5.12.2 (Saint Raymond).** `A, B ⊆ X×Y` analytic, with for every `x` a σ-compact `K` with
> `A_x ⊆ K ⊆ (B_x)ᶜ`. Then ∃ Borel `(Bₙ)` with compact sections, `A ⊆ ⋃Bₙ`, `B ∩ ⋃Bₙ = ∅`.

The proof of 5.12.2 (Srivastava pp. 221–226) is the wall. It needs, in order:
1. **Effros Borel structure** on `F(Y)` (closed subsets of `Y`), a standard Borel space (Ex. 3.3.11,
   3.3.12). `{K ∈ F(Y) : K compact}` is Borel (3.3.11(iv)); `F ↦ cl(g(F))` is Borel measurable for
   continuous `g` (3.3.11(v)).
2. **Derivatives** `D : F(X) → F(X)` (`D(A) ⊆ A`, monotone), the family-`B`-derivative `D_B` for
   hereditary `B ⊆ F(X)`; transfinite iterates `Dᵅ(A)`, rank `|A|_D = least α with Dᵅ⁺¹=Dᵅ`,
   `D^∞(A) = D^{|A|_D}(A)`, `Ω_D = {A : D^∞(A)=∅}` (§5.12 (II),(III)).
3. **Prop. 5.12.6**: `Ω_{D_B} = B_σ ∩ F(X)` (a closed set is in `Ω` iff it is a countable union of
   members of `B`). Used to certify σ-compactness ⟺ `D^∞ = ∅` for `D_𝒦`, `𝒦` = compacts.
4. **Prop. 5.12.7** (the Π¹₁-boundedness theorem): if `{(A,B) : A ⊆ D(B)}` is analytic, then (i)
   `Ω_D` is coanalytic and (ii) **for every analytic `𝒜 ⊆ Ω_D`, `sup{|A|_D : A∈𝒜} < ω₁`**. Proved
   by contradiction via `WO*`/`LO*` codings of countable well-orders and the coanalyticity (=
   non-Borel-ness) of `WO` (4.2.2). This is the heart.
5. **Lemma 5.12.8**: `F ⊆ F(ℕ^ℕ)` hereditary Π¹₁, `H ⊆ X×ℕ^ℕ` closed with `H_x ∈ F_σ` ⟹ ∃ Borel
   `(Hₙ)` covering `H` with `(Hₙ)_x ∈ F`. Proved by transfinite induction (two claims) up to the
   bound `α₀` from 5.12.7, using 4.7.1, 4.7.2 (Borel sets with open sections = `⋃ Bₙ×Σ(s)`), the
   generalized first separation theorem 4.6.1, the reflection theorem 5.10.1, and Π¹₁-on-Π¹₁.
6. **Proof of 5.12.2 proper**: pull back to `ℕ^ℕ` via a continuous onto `f : ℕ^ℕ → A`; the family
   `F = {F ∈ F(ℕ^ℕ) : cl(f(F)) ⊆ Bᶜ ∧ cl(π_Y(f(F))) compact}` is hereditary Π¹₁ (uses 3.3.11);
   apply 5.12.8, then 4.7.5 (Borel separation by compact-section set) fibrewise. ∎

Every one of items 1, 2, 4, 5 is an independent Mathlib-scale development; item 4 alone (Π¹₁-bounded-
ness + coanalyticity of WO) is a substantial descriptive-set-theory chapter.

**Cross-check (Kechris).** Same theorem is Kechris 35.46 (the prompt's "28.8" and "35.46" are the
Kechris numbering of 4.7.11 and 5.12.1 respectively; they do **not** appear verbatim in the
Srivastava text file — Srivastava uses 4.7.11 and 5.12.1). The note in
`MeasurableGraphToProjector.lean:405` cites "Kechris 18.18" for AK, which is the Kechris index for
σ-compact-section projection (consistent).

---

## 3. What EXISTS in Mathlib (exact lemma names)

All under `Mathlib/MeasureTheory/Constructions/Polish/Basic.lean` unless noted.

**Topology-refinement / clopenable (the 4.7.4 building blocks — KEY for leaf 1):**
- `MeasurableSet.isClopenable` — Borel `s` in Polish `α` ⟹ ∃ finer Polish topology making `s`
  clopen. (`Mathlib/Topology/MetricSpace/Polish.lean` for `IsClopenable`, `.iUnion`, `.compl`.)
- `MeasureTheory.isClopenable_iff_measurableSet` — clopenable ⟺ MeasurableSet (the σ-algebra
  invariance).
- `MeasureTheory.borel_eq_borel_of_le` — two comparable Polish topologies on `γ` give the **same**
  Borel σ-algebra. (This is the precise "same Borel structure" fact in Srivastava 4.7.4.)
- `Measurable.exists_continuous` — Borel `f : α → β` (α Polish, β 2nd-countable) ⟹ ∃ finer Polish
  topology on `α` making `f` continuous. (The mechanism behind refining `X` per-coordinate.)
- `exists_polishSpace_forall_le` (in Polish.lean) — countable inf of finer Polish topologies is
  Polish. (Lets you refine for countably many constraints at once — needed to make a Borel `B`
  closed via its open-section pieces.)

**Proper map / closed projection (the 2.3.24 half — ALREADY sorry-free in our file):**
- `isProperMap_fst_of_compactSpace` / `isClosedMap_fst_of_compactSpace`
  (`Mathlib/Topology/Maps/Proper/Basic.lean`) — `Y` compact ⟹ `Prod.fst` proper/closed.
- `IsProperMap.isClosed_range`, `IsProperMap.restrict`, `IsClosed.isProperMap_subtypeVal`,
  `IsProperMap.comp` (same file). Our file's `isProperMap_fst_restrict_of_isClosed_compactSpace`
  and `measurableSet_image_fst_of_isProperMap_restrict` already package these.
- `Prod.borelSpace` (`Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`) — for
  2nd-countable factors, the product Borel σ-algebra = Borel of the product topology.

**Analytic-set theory (the a.e. route; does NOT close either leaf):**
- `MeasurableSet.analyticSet`, `MeasurableSet.analyticSet_image`, `AnalyticSet.iUnion`,
  `AnalyticSet.image_of_continuous`, `AnalyticSet.measurablySeparable`,
  `AnalyticSet.measurableSet_of_compl`, `IsClosed.analyticSet`,
  `measurableSet_range_of_continuous_injective`, `MeasurableSet.image_of_continuousOn_injOn`,
  `MeasurableSet.image_of_measurable_injOn` (Lusin–Souslin).
- `MeasureTheory.AnalyticSet.nullMeasurableSet` — analytic ⟹ universally measurable. THIS is what
  the sorry-free a.e. route (`Frontier.Issue6.MeasurableProjection`) uses.

**ABSENT entirely (confirmed by grep over `Mathlib/`):**
- Effros Borel structure / `F(X)` hyperspace as standard Borel — **none** (only `IsClosed`-valued
  pointwise objects; no Borel structure on the *set* of closed sets). Confirmed: no
  `Effros`, no hyperspace `MeasurableSpace`.
- Coanalytic / Π¹₁ pointclass, coanalytic ranks, Π¹₁-boundedness — **none**.
- `WO`/`LO` codings of countable orders, coanalyticity of `WO` — **none**.
- Measurable selection / uniformization (Kuratowski–Ryll-Nardzewski, Jankov–von Neumann) — **none**
  (`grep measurableSet_projection|measurable_selection|MeasurableSelection` empty).
- Hilbert-cube universality for Polish spaces (every Polish ≅ Gδ in `[0,1]^ℕ`) — **none**
  in `Polish.lean` (only `IsClosedEmbedding.polishSpace`); the WLOG-`Y`-compact reduction has no
  ready lemma.
- Any "projection of Borel with compact/σ-compact sections is Borel" — **none**.

---

## 4. Decomposition table

### Leaf 1 — `measurableSet_image_fst_of_isCompact_sections` (Novikov 4.7.11)

| # | Sub-lemma | Statement | Mathlib | Difficulty |
|---|-----------|-----------|---------|------------|
| 1a | `Prod.fst` closed-map when `Y` compact | `Y` compact, `S` closed ⟹ `Prod.fst '' S` closed | exists (`isClosedMap_fst_of_compactSpace`; packaged in file) | easy |
| 1b | WLOG `Y` compact | reduce general Polish `Y` to compact metric via Gδ-in-Hilbert-cube embedding; sections stay compact | absent (no Hilbert-cube universality lemma) | hard |
| 1c | **4.7.4 product refinement** | Borel `B ⊆ X×Y` with closed sections ⟹ ∃ finer Polish top. on `X`, same Borel σ-alg, `B` closed in `(X,T)×Y` | partial (`isClopenable`, `borel_eq_borel_of_le`, `exists_polishSpace_forall_le` exist; the *product*/sectionwise assembly is new) | hard |
| 1d | 4.7.1/4.7.2 open-section structure | Borel `C ⊆ X×Y` with open sections `= ⋃ₙ Bₙ×Vₙ`, `Bₙ` Borel | absent (drives 1c) | medium-hard |
| 1e | Borel σ-algebra of product invariant under refining `X` only | `borel((X,T)×Y) = borel(X×Y)` on the same set | partial (`borel_eq_borel_of_le` + `Prod.borelSpace`; product version is new) | medium |
| 1f | Final assembly | combine 1a–1e | — | easy given above |

### Leaf 2 — `exists_borel_compactSection_cover` (Saint Raymond 5.12.2 ⇒ 5.12.3)

| # | Sub-lemma | Statement | Mathlib | Difficulty |
|---|-----------|-----------|---------|------------|
| 2a | Effros Borel structure on `F(Y)` | `F(Y)` standard Borel; `K↦K` ops Borel; `{K compact}` Borel (3.3.11) | absent | research |
| 2b | Derivatives + transfinite ranks | `D:F(X)→F(X)`, `Dᵅ`, `|A|_D`, `Ω_D` (§5.12 II/III) | absent | research |
| 2c | Prop. 5.12.6 | `Ω_{D_B} = B_σ ∩ F(X)` | absent (needs 2a,2b) | hard |
| 2d | Coanalytic pointclass + WO/LO codings | Π¹₁ sets, `WO` coanalytic non-Borel (4.2.2), `WO*`/`LO*` | absent | research |
| 2e | **Prop. 5.12.7 Π¹₁-boundedness** | analytic `𝒜⊆Ω_D` ⟹ `sup |A|_D < ω₁` | absent (needs 2b,2d) | research |
| 2f | Lemma 5.12.8 | transfinite-induction covering lemma (uses 4.7.1/2, 4.6.1, 5.10.1, reflection) | absent | research |
| 2g | 5.12.2 proper + 4.7.5 | pull-back to `ℕ^ℕ`, hereditary-Π¹₁ family, fibrewise Borel separation | absent | hard (given 2a–2f) |
| 2h | 5.12.2 ⟹ 5.12.3 | apply with `B=Aᶜ` | trivial | easy |

Only **2h** is easy; everything else is absent, and 2a, 2b, 2d, 2e, 2f are each individually a
descriptive-set-theory chapter.

---

## 5. Independent strategies for an implementation agent

These are for **leaf 1 only** — leaf 2 has no tractable route absent a multi-month Effros/Π¹₁
project (see verdict). Each strategy below is a distinct full attempt at 4.7.11.

**Strategy A — Novikov topology-refinement (Srivastava's first proof; recommended).**
Mechanize 1a–1f. Build 1c (product 4.7.4) from `MeasurableSet.isClopenable` /
`exists_polishSpace_forall_le`: for `B` with *closed* sections, certify `B` clopenable in a product-
compatible way. The novel content is the *product* lemma: refining only `X`'s topology preserves
`borel(X×Y)` (via `borel_eq_borel_of_le` lifted through `Prod.borelSpace`) and can make `B` closed.
Then 1a (proper map, already in file) finishes. Tackle 1b (WLOG `Y` compact) either by first proving
a Hilbert-cube embedding lemma, or by restricting the *intended consumer* to `Y =
EuclideanSpace ℝ (Fin d)` and noting each compact section lives in some closed ball `closedBall 0 R`
which is compact — i.e. specialize 4.7.11 to the actual call site (`Y` = Euclidean, sections compact
⟹ bounded ⟹ contained in a fixed compact ball after an `Iio`/exhaustion split). This specialization
may dodge 1b entirely and is the most promising path to a *usable* sorry-free leaf.

**Strategy B — Euclidean-specialized direct proof (sidestep general Polish `Y`).**
The only consumer is `measurableInfDist_of_measurableGraph_AK` with `Y = EuclideanSpace ℝ (Fin d)`
and sections `V x ∩ ball c r` (σ-compact) — and downstream the compact pieces are `V x ∩
closedBall`. Prove a *bespoke* lemma: for `Y` Euclidean and `B` Borel with each section compact,
write `B = ⋃ₙ (B ∩ (X × closedBall 0 n))`; each piece has sections inside the **fixed compact**
`closedBall 0 n`, so restrict to `Y' = closedBall 0 n` (a `CompactSpace`) and apply the file's
already-sorry-free `isProperMap_fst_restrict_of_isClosed_compactSpace` after the 4.7.4 product
refinement makes the piece closed in `X × Y'`. This converts 4.7.11 into "make a compact-section
Borel set closed in `X × (compact box)` by refining `X`" — exactly 1c with `Y` already compact, no
1b needed. Highest chance of an honestly-closed *project-relevant* leaf.

**Strategy C — Lusin–Souslin / injective-image route.**
Try to express `Prod.fst '' B` (compact sections) as a measurable injective image after a
fibre-selection, leveraging `MeasurableSet.image_of_measurable_injOn` /
`measurableSet_range_of_continuous_injective`. The graph of a Borel selection
`x ↦ (some point of B_x)` over `π_X(B)` would, if measurable, give injective image = `π_X(B)`. The
obstruction: a measurable selection itself needs Kuratowski–Ryll-Nardzewski (absent), so this is
likely circular — included as an exploration to *rule out* quickly, not a primary bet.

**Strategy D (leaf 2 only — scoping bet, not a close).**
If anyone attempts leaf 2, the *minimal* sub-target with independent value is **2a: the Effros
Borel structure on `F(Y)` as a standard Borel space**, with `{K compact}` Borel and the
basic Borel maps (3.3.11). This is a self-contained, upstreamable Mathlib contribution and the
mandatory foundation for everything in §5.12. Do not expect it to close leaf 2; expect it to be
1 of ~6 prerequisite PRs. Treat as research, not a sprint.

---

## 6. Can the analytic-set theory in Mathlib shortcut either leaf? (Direct answer)

**No, neither.** The analytic route gives `AnalyticSet (Prod.fst '' B)` (via
`MeasurableSet.analyticSet_image` + `AnalyticSet.image_of_continuous`) and then only
`AnalyticSet.nullMeasurableSet` (universal/`NullMeasurableSet`). That is precisely the *a.e.* theorem
already discharged sorry-free in `Frontier.Issue6.MeasurableProjection`. Genuine
`MeasurableSet (Prod.fst '' B)` is **strictly stronger** and provably out of reach of analytic-set
theory alone — a Borel projection is analytic but not Borel in general (Lebesgue's error; cf. the
file's `not_isClosed_image_fst_of_isClosed_isCompact_sections` counterexample). The compact-section
hypothesis is exactly what rescues Borel-ness, and exploiting it requires the proper-map / 4.7.4
machinery (leaf 1) or the §5.12 hyperspace machinery (leaf 2) — never the analytic API.

The **one** way analytic theory helps: leaf 1's sub-lemma 1c (4.7.4 product refinement) is morally a
`MeasurableSet.isClopenable`-style argument, and Mathlib's analytic/clopenable infrastructure
(`isClopenable_iff_measurableSet`, `borel_eq_borel_of_le`) is the genuine reusable foundation for it.
So analytic theory *supports* leaf 1's decomposition; it does not *close* it.

---

## 7. Honest verdict

- **Leaf 1 (4.7.11 / Novikov): partial decomposition, and Strategy B (Euclidean specialization) has
  a real chance of an honestly sorry-free *project-relevant* close** in a focused multi-day effort.
  The proper-map half is already done in-file; the missing piece is the product topology-refinement
  (4.7.4) — hard but Mathlib-scale, built on `isClopenable`/`borel_eq_borel_of_le` which exist. The
  general-Polish-`Y` version (with the Hilbert-cube WLOG, 1b) is harder and probably a separate PR.
- **Leaf 2 (5.12.2 / Saint Raymond): a multi-component research wall.** It needs the Effros Borel
  hyperspace, transfinite coanalytic derivative ranks, the Π¹₁-boundedness theorem, and WO/LO order
  codings — none in Mathlib, each a chapter-sized development. No proof assistant has formalized
  Arsenin–Kunugui or the Effros Borel standard-Borel-ness (confirmed via search; arXiv 2405.16603
  notes F(P) Effros as a known *unformalized* object). Realistically months-to-years and several
  upstream PRs; not closeable in this campaign.

Because the assembly needs **both** leaves, the everywhere-Borel issue-#6 target cannot be made
sorry-free until leaf 2's wall is breached — *unless* the consumer is re-routed to need only leaf 1.
Strategy B suggests that may be possible: if one proves the Euclidean-`Y` 4.7.11 *and* directly the
Euclidean σ-compact-section decomposition (`A = ⋃ₙ A ∩ (X×closedBall 0 n)` already has compact
sections — **leaf 2 is trivial when `Y` is Euclidean and sections are compact**, because σ-compact
sections of the slab `V x ∩ ball` are exhausted by closed balls, which is exactly the sorry-free
`isSigmaCompact_isClosed_inter_ball` already in the file!). **This is the key under-exploited
observation:** for the actual call site, leaf 2's general DST machinery is overkill — the explicit
ball-exhaustion already gives the compact-section cover. An agent should first verify whether
`exists_borel_compactSection_cover` can be *specialized* to the Euclidean graph-slab consumer using
`isSigmaCompact_isClosed_inter_ball`, collapsing leaf 2 to an `easy` lemma and leaving only leaf 1
(Strategy B) as the real work.
