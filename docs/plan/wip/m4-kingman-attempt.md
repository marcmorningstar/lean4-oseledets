# M4 Kingman — interrupted attempt #1 (reference, NOT in the build)

The lean-worker hit the session limit mid-proof. This is its partial Katznelson–Weiss
scaffolding for Kingman, preserved for salvage. It does NOT fully compile:
- `le_birkhoffSum_one` is MIS-STATED at n=0: a subadditive cocycle has g 0 ≥ 0 (from
  subadditivity at (0,0)), but the Birkhoff-domination needs g 0 ≤ 0. Fix: either add
  a `g 0 = 0` field to IsSubadditiveCocycle (true for log‖A⁽ⁿ⁾‖), or state the
  domination for n ≥ 1 only. (Kingman's conclusion at n=0 is harmless: 0⁻¹·g 0 = 0.)
- `ae_eq_comp_of_le_comp`: the final `linarith` branch failed; the invariance-from-
  monotonicity argument is otherwise sound (sub-level-set + equal-finite-measure).
- `integral_comp_iterate`, `integral_subadditive` compiled (reusable).
Resume from docs/plan/blueprints/m4-kingman.md (Katznelson–Weiss route).

```lean
import Oseledets.Ergodic.Birkhoff
import Mathlib.Analysis.Subadditive

/-!
# Kingman's subadditive ergodic theorem

Kingman's theorem (layer `L2` / milestone `M4`) is the analytic engine of the
multiplicative ergodic theorem. Mathlib has only the *deterministic* Fekete lemma
(`Subadditive.tendsto_lim`); the measure-theoretic a.e.-convergence statement for a
**subadditive cocycle** over a measure-preserving system is absent.

We record the subadditive-cocycle predicate and prove the theorem in `ℝ` under the
boundedness proviso `BddBelow {(∫ gₙ)/n}` (which keeps the limit finite — exactly the
case used by Furstenberg–Kesten under the `log⁺‖A⁻¹‖ ∈ L¹` hypothesis); the fully
general `EReal`-valued version (limit possibly `−∞`) is a planned refinement.

## Strategy (Katznelson–Weiss)

We follow the Katznelson–Weiss route: derive Kingman from the maximal ergodic
inequality `M1` plus the pointwise Birkhoff theorem `M3`, via a truncation/stopping
argument rather than Steele's greedy partition.

* Write `g₁ := g 1`, `B := μ[g₁ | invariants T]` (the Birkhoff limit of `g₁`).
* `IsSubadditiveCocycle.le_birkhoffSum_one`: `g n x ≤ birkhoffSum T g₁ n x`.
* `Gp x := limsup (g (n+1) x / (n+1))`, `Gm x := liminf (…)`. Both are a.e.
  `T`-invariant; `Gm ≤ Gp` and `Gp ≤ B` a.e.
* Easy direction (Fekete + Fatou): `α ≤ ∫ Gm`, where `α := ⨅ n, (∫ g_{n+1})/(n+1)`.
* Hard direction (truncation + maximal inequality): `∫ Gp ≤ α`.
* Squeeze `∫ (Gp − Gm) ≤ 0` with `Gp ≥ Gm` a.e. ⟹ `Gp =ᵐ Gm` ⟹ convergence a.e.

## Finiteness hypothesis

`tendsto_kingman` carries `[IsFiniteMeasure μ]`. As with `M3` Birkhoff, the
Katznelson–Weiss/maximal-inequality machinery needs a finite measure (for
`ae_eq_of_subset_of_measure_ge`, Fatou via a finite shift, etc.). The Oseledets MET
only ever calls Kingman for probability measures, where this is automatic.
-/

open MeasureTheory Filter Topology

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-- A sequence `g : ℕ → X → ℝ` is a **subadditive cocycle** over `T` when
`g (m + n) x ≤ g m x + g n (T^[m] x)` for all `m, n, x`. (For `gₙ = log‖A⁽ⁿ⁾‖` this
follows from submultiplicativity of the operator norm and the cocycle identity.) -/
structure IsSubadditiveCocycle (T : X → X) (g : ℕ → X → ℝ) : Prop where
  apply_add_le : ∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x)

/-! ### A1: singleton (Birkhoff-sum) subadditivity -/

/-- **A1' — singleton partition subadditivity.** For `n ≥ 1`, a subadditive cocycle is
dominated by the Birkhoff sum of its first level: `g (n+1) x ≤ birkhoffSum T (g 1) (n+1) x`.
(The statement fails at `n = 0`: subadditivity only forces `0 ≤ g 0 x`, not `g 0 x ≤ 0`.) -/
private theorem IsSubadditiveCocycle.le_birkhoffSum_one {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (n : ℕ) (x : X) :
    g (n + 1) x ≤ birkhoffSum T (g 1) (n + 1) x := by
  induction n with
  | zero => simp only [Nat.zero_add, birkhoffSum_one]
  | succ n ih =>
      rw [birkhoffSum_succ]
      calc g (n + 1 + 1) x ≤ g (n + 1) x + g 1 (T^[n + 1] x) := hsub.apply_add_le (n + 1) 1 x
        _ ≤ birkhoffSum T (g 1) (n + 1) x + g 1 (T^[n + 1] x) := by linarith [ih]

/-! ### A2: subadditivity of the integral sequence (Fekete input) -/

/-- The integral of a measure-preserving composition equals the integral:
`∫ g n (T^[m] x) ∂μ = ∫ g n x ∂μ`. -/
private theorem integral_comp_iterate (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (m n : ℕ) :
    ∫ x, g n (T^[m] x) ∂μ = ∫ x, g n x ∂μ := by
  have hmp : MeasurePreserving (T^[m]) μ μ := hT.iterate m
  have haesm : AEStronglyMeasurable (g n) (Measure.map (T^[m]) μ) := by
    rw [hmp.map_eq]; exact (hint n).aestronglyMeasurable
  have hmap := integral_map (μ := μ) (φ := T^[m]) hmp.aemeasurable (f := g n) haesm
  rw [hmp.map_eq] at hmap
  exact hmap.symm

/-- **A2 — integral subadditivity.** The integral sequence `aₙ = ∫ gₙ` is subadditive
in Mathlib's sense (`a (m+n) ≤ a m + a n`), the Fekete input. -/
private theorem integral_subadditive (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ) :
    Subadditive (fun n => ∫ x, g n x ∂μ) := by
  intro m n
  simp only
  have hcomp : Integrable (fun x => g n (T^[m] x)) μ :=
    (hT.iterate m).integrable_comp_of_integrable (hint n)
  calc ∫ x, g (m + n) x ∂μ
      ≤ ∫ x, (g m x + g n (T^[m] x)) ∂μ :=
        integral_mono (hint _) ((hint m).add hcomp) (fun x => hsub.apply_add_le m n x)
    _ = (∫ x, g m x ∂μ) + ∫ x, g n (T^[m] x) ∂μ := integral_add (hint m) hcomp
    _ = (∫ x, g m x ∂μ) + ∫ x, g n x ∂μ := by rw [integral_comp_iterate hT hint m n]

/-! ### A3: a.e. `T`-invariance from monotonicity under `T` -/

/-- **A3 — invariance from `F ≤ F ∘ T`.** If `F` is measurable, `T` is measure-preserving
on a finite measure, and `F x ≤ F (T x)` for all `x`, then `F ∘ T =ᵐ[μ] F`. The upper
level sets `{c ≤ F}` satisfy `{c ≤ F} ⊆ T⁻¹ {c ≤ F}` with equal (finite) measure, hence
agree a.e.; ranging over rational `c` gives invariance a.e. -/
private theorem ae_eq_comp_of_le_comp [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {F : X → ℝ} (hF : Measurable F)
    (hle : ∀ x, F x ≤ F (T x)) : F ∘ T =ᵐ[μ] F := by
  -- For each rational `c`, `{c ≤ F}` and its preimage agree a.e.
  have hkey : ∀ c : ℚ, T ⁻¹' {x | (c : ℝ) ≤ F x} =ᵐ[μ] {x | (c : ℝ) ≤ F x} := by
    intro c
    set s : Set X := {x | (c : ℝ) ≤ F x} with hs
    have hsmeas : MeasurableSet s := measurableSet_le measurable_const hF
    -- `s ⊆ T⁻¹ s` because `F x ≤ F (T x)`.
    have hsub : s ⊆ T ⁻¹' s := by
      intro x hx
      simp only [hs, Set.mem_setOf_eq] at hx
      simp only [Set.mem_preimage, hs, Set.mem_setOf_eq]
      exact le_trans hx (hle x)
    -- equal measures.
    have hmeq : μ (T ⁻¹' s) = μ s := hT.measure_preimage hsmeas.nullMeasurableSet
    -- `s =ᵐ T⁻¹ s` (subset of equal finite measure).
    have : s =ᵐ[μ] T ⁻¹' s :=
      ae_eq_of_subset_of_measure_ge hsub (le_of_eq hmeq) hsmeas.nullMeasurableSet
        (measure_ne_top μ _)
    exact this.symm
  -- Collect over rationals: a.e. `x` satisfies the equivalence for all `c`.
  have hall : ∀ᵐ x ∂μ, ∀ c : ℚ,
      (x ∈ T ⁻¹' {x | (c : ℝ) ≤ F x}) ↔ (x ∈ {x | (c : ℝ) ≤ F x}) := by
    rw [ae_all_iff]
    intro c
    exact Filter.eventuallyEq_set.1 (hkey c)
  filter_upwards [hall] with x hx
  -- From `∀ c, (c ≤ F (T x)) ↔ (c ≤ F x)`, deduce `F (T x) = F x`.
  show F (T x) = F x
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- F (T x) < F x: pick rational c in between.
    obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn hlt
    have := (hx c).symm
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at this
    exact absurd (this.1 hc2.le) (not_le.2 hc1)
  · -- F x < F (T x): use hle gives ≥, contradiction with strict.
    have := hle x
    linarith

/-! ### The theorem (assembly in progress) -/

/-- **Kingman's subadditive ergodic theorem** (`M4`). For a measure-preserving `T` on a
finite measure and an integrable subadditive cocycle `g` whose normalized integrals are
bounded below, `gₙ / n` converges `μ`-a.e. to a `T`-invariant integrable limit `G`.

WORK IN PROGRESS (`sorry`): the Katznelson–Weiss scaffolding above is proved sorry-free
— A1 `IsSubadditiveCocycle.le_birkhoffSum_one`, `integral_comp_iterate`,
`integral_subadditive`, and A3 `ae_eq_comp_of_le_comp` (a.e. `T`-invariance of a function
dominated by its `T`-shift). What remains is the assembly: define
`Gp x = limsup (gₙ x / n)`, `Gm x = liminf …`, prove the hard direction `∫ Gp ≤ ⨅ aₙ/n`
via truncation + the maximal ergodic inequality `M1`, and squeeze `Gp =ᵐ Gm`. See
`docs/plan/blueprints/m4-kingman.md`.

The `[IsFiniteMeasure μ]` hypothesis is required by the maximal-inequality machinery (as
for `M3` Birkhoff); the Oseledets MET only uses Kingman for probability measures. -/
theorem tendsto_kingman [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∃ G : X → ℝ, (G ∘ T =ᵐ[μ] G) ∧ Integrable G μ ∧
      (∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * g n x) atTop (𝓝 (G x))) := by
  sorry

/-- **Kingman, ergodic case**: under ergodicity the a.e. limit is a single constant.
(WIP — follows from `tendsto_kingman` once that is closed, via a.e.-constancy of the
`T`-invariant limit.) -/
theorem tendsto_kingman_ergodic [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∃ c : ℝ, ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * g n x) atTop (𝓝 c) := by
  sorry

end Oseledets
```
