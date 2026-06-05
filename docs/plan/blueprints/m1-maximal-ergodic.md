# Blueprint — M1 / L1.1: the maximal ergodic inequality (Hopf / Garsia)

**Target file:** `Oseledets/Ergodic/MaximalErgodic.lean`
**Ladder node:** L1.1 (the analytic gate to pointwise Birkhoff, L1.3).
**Status of statement:** FIXED (below). This document is the PROOF PLAN only.

All Mathlib declaration names and signatures below were read off the pinned
source under `.lake/packages/mathlib/Mathlib` (`v4.30.0-rc2`). Each is marked
**[verified]** with file + the exact signature where load-bearing. Do **not**
rename without re-grepping.

---

## 1. The exact Lean statement (as in the repo)

```lean
open MeasureTheory Filter

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

theorem setIntegral_birkhoffSum_pos_nonneg
    (hT : MeasurePreserving T μ μ) {f : X → ℝ} (hf : Integrable f μ) :
    0 ≤ ∫ x in {x | ∃ n : ℕ, 0 < birkhoffSum T f (n + 1) x}, f x ∂μ := by
  sorry
```

Notes that drive the whole plan:

- The target set is `{x | ∃ n : ℕ, 0 < birkhoffSum T f (n+1) x}`. Because
  `n : ℕ`, the partial-sum index `n+1` ranges over `1, 2, 3, …`. So the set is
  exactly `{x | ∃ k ≥ 1, 0 < S_k x}` where `S_k x := birkhoffSum T f k x`.
- `f` is only `Integrable`, hence only `AEStronglyMeasurable` (`hf.1`), **not**
  `Measurable`. So the target set is in general only a `NullMeasurableSet`. This
  forces a *reduce-to-a-measurable-representative* step (§4, step R). The set
  integral `∫ x in s, f x ∂μ = ∫ x, f x ∂(μ.restrict s)` is well-defined even
  when `s` is not measurable, but every monotone-convergence / measurability
  lemma we use wants (null)measurable sets.
- `MeasurePreserving T μ μ` gives `hT.measurable : Measurable T`
  (`MeasurePreserving.measurable`, the structure field, **[verified]**
  `Mathlib/Dynamics/Ergodic/MeasurePreserving.lean:47`) and
  `hT.map_eq : Measure.map T μ = μ` (field, line 48). **`T` is NOT assumed a
  measurable embedding / injective** — this is the central reason we must avoid
  `MeasurePreserving.integral_comp` (needs `MeasurableEmbedding`) and instead use
  the bare `integral_map` + `hT.map_eq` (see §3, F2).

---

## 2. Mathematical proof (Garsia's short argument), made Lean-precise

Fix a **measurable** representative `g := hf.1.mk f` (so `g =ᵐ[μ] f`, `Measurable g`).
Work with `g` throughout; transfer back at the very end. Write
`S_k x := birkhoffSum T g k x = ∑ j ∈ range k, g (T^[j] x)`.

**The maximal function (the design choice that makes everything idiomatic).**
For `N : ℕ` define

```
M_N x := (Finset.range (N+1)).sup' Finset.nonempty_range_add_one (fun k => S_k x)
       = max_{0 ≤ k ≤ N} S_k x.
```

Because `0 ∈ range (N+1)` and `S_0 x = birkhoffSum T g 0 x = 0`
(`birkhoffSum_zero`, **[verified]**), we have **`M_N x ≥ 0` for all `x`** — i.e.
`M_N` already *is* its own positive part `max(0, S_1, …, S_N)`. This avoids
carrying a separate `M_N⁺`.

Define the increasing sets
```
E_N := {x | 0 < M_N x}.
```
By `Finset.lt_sup'_iff` (**[verified]**, `a < sup' ↔ ∃ b ∈ s, a < f b`) and
`Finset.mem_range`/`Nat.lt_succ_iff`,
```
x ∈ E_N  ↔  ∃ k ∈ range (N+1), 0 < S_k x  ↔  ∃ k ≤ N, 0 < S_k x.
```
Since `S_0 = 0` is never `> 0`, this is `∃ k, 1 ≤ k ∧ k ≤ N ∧ 0 < S_k x`. Hence
```
⋃ N, E_N = {x | ∃ k ≥ 1, 0 < S_k x} = {x | ∃ n, 0 < S_{n+1} x}  (the target set, for g).
```

**The pointwise Garsia inequality (holds for ALL `x ∈ E_N`).**
From `birkhoffSum_succ'` (**[verified]**:
`birkhoffSum f g (n+1) x = g x + birkhoffSum f g n (f x)`), for every `k`,
`S_{k+1} x = g x + S_k (T x)`. Therefore
```
g x + M_N (T x) = g x + max_{0≤k≤N} S_k(Tx)
              = max_{0≤k≤N} (g x + S_k(Tx))
              = max_{0≤k≤N} S_{k+1} x
              = max_{1≤j≤N+1} S_j x.
```
On `E_N` (where `M_N x > 0`), `M_N x = max_{0≤k≤N} S_k x = max_{1≤k≤N} S_k x`
(the `k=0` term `0` is not the max), and
`max_{1≤j≤N+1} S_j x ≥ max_{1≤j≤N} S_j x = M_N x`. Hence
```
g x ≥ M_N x − M_N (T x)        for all x ∈ E_N.            (★)
```

**Integrating (★) over `E_N`.**
```
∫_{E_N} g ≥ ∫_{E_N} (M_N − M_N∘T) = ∫_{E_N} M_N − ∫_{E_N} M_N∘T.   (1)
```
Three bookkeeping facts close it:

- **(a)** `∫_{E_N} M_N∘T ≤ ∫_X M_N∘T`, because `M_N∘T ≥ 0`
  (`setIntegral_le_integral`, **[verified]**).
- **(b)** `∫_X M_N∘T = ∫_X M_N`, by measure-preservation
  (`integral_map` + `hT.map_eq`, see §3 F2).
- **(c)** `∫_X M_N = ∫_{E_N} M_N`, because on `E_Nᶜ` we have `M_N = 0` *pointwise*
  (`¬(0 < M_N x)` together with `0 ≤ M_N x` gives `M_N x = 0`), so
  `∫_{E_Nᶜ} M_N = 0` (`setIntegral_eq_zero_of_forall_eq_zero`), and
  `∫_X M_N = ∫_{E_N} M_N + ∫_{E_Nᶜ} M_N` (`integral_add_compl`).

Chaining: `∫_{E_N} M_N − ∫_{E_N} M_N∘T ≥ ∫_{E_N} M_N − ∫_X M_N∘T
= ∫_{E_N} M_N − ∫_X M_N = ∫_{E_N} M_N − ∫_{E_N} M_N = 0`. With (1):
```
0 ≤ ∫_{E_N} g       for every N.                          (2)
```

**Passing to the limit `N → ∞`.**
`E_N` is monotone in `N` (`Finset.sup'_mono` on `range (N+1) ⊆ range (M+1)`),
`⋃ N, E_N` is the target set (for `g`), and `g` is integrable, so
`tendsto_setIntegral_of_monotone` (**[verified]**) gives
```
∫_{E_N} g  →  ∫_{⋃ E_N} g = ∫_{target(g)} g    as N → ∞.
```
By `ge_of_tendsto'` (the `@[to_dual]` of `le_of_tendsto'`, **[verified]**) and (2),
```
0 ≤ ∫_{target(g)} g.                                       (3)
```

**Transfer `g ↝ f`.** Since `g =ᵐ[μ] f`:
`target(g) =ᵐ[μ] target(f)` (the defining sets agree a.e. — built from
a.e.-equal Birkhoff sums) and `∫_{target(f)} f = ∫_{target(f)} g` (a.e.-equal
integrands). Both transfers via `setIntegral_congr_set` and `setIntegral_congr_ae₀`.
Then (3) gives `0 ≤ ∫_{target(f)} f`, the goal. ∎

---

## 3. Mathlib facts used, fully qualified and verified

Open: `MeasureTheory Filter Finset`. All set integrals are `∫ x in s, f x ∂μ`.

### Birkhoff-sum algebra — `Mathlib/Dynamics/BirkhoffSum/Basic.lean`
- **B1** `birkhoffSum (f : α→α) (g : α→M) (n : ℕ) (x : α) : M := ∑ k ∈ range n, g (f^[k] x)` — the `def`. **[verified]**
- **B2** `birkhoffSum_zero (f g x) : birkhoffSum f g 0 x = 0`. **[verified]** (gives `S_0 = 0`, hence `M_N ≥ 0`).
- **B3** `birkhoffSum_succ' (f g n x) : birkhoffSum f g (n+1) x = g x + birkhoffSum f g n (f x)`. **[verified]** (the heart of (★)).

### Measure-preservation / integral transport
- **F1** `MeasurePreserving` structure: fields `.measurable : Measurable f`, `.map_eq : map f μ = ν`. `Mathlib/Dynamics/Ergodic/MeasurePreserving.lean:45-48`. **[verified]**
- **F2** `MeasureTheory.integral_map {φ} (hφ : AEMeasurable φ μ) {f} (hfm : AEStronglyMeasurable f (Measure.map φ μ)) : ∫ y, f y ∂(Measure.map φ μ) = ∫ x, f (φ x) ∂μ`. `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1089`. **[verified]**
  Used as: `∫ x, M_N (T x) ∂μ = ∫ y, M_N y ∂(Measure.map T μ) = ∫ y, M_N y ∂μ` via `hT.map_eq`. **Critical: this avoids `MeasurePreserving.integral_comp` (line 1123), which requires `MeasurableEmbedding f` — `T` is not assumed injective.**
- **F3** `MeasurePreserving.iterate (hf) : ∀ n, MeasurePreserving f^[n] μ μ`. `…/MeasurePreserving.lean:193`. **[verified]** (each `g ∘ T^[k]` integrable / a.e.-transports).
- **F4** `MeasurePreserving.integrable_comp_of_integrable (hf : MeasurePreserving f μ ν) (hg : Integrable g ν) : Integrable (g ∘ f) μ`. `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:387`. **[verified]** (gives `Integrable (M_N ∘ T) μ` from `Integrable M_N μ`; no embedding needed). NB the result is about `g ∘ f`; to match `fun x => M_N (T x)` it is defeq / use `Function.comp`.
- **F5** `Measure.QuasiMeasurePreserving.ae_eq_comp (hf : QuasiMeasurePreserving f μ ν) (h : g =ᵐ[ν] g') : g ∘ f =ᵐ[μ] g' ∘ f`. `Mathlib/MeasureTheory/Measure/Restrict.lean:682`. **[verified]** Coercion `MeasurePreserving.quasiMeasurePreserving` (`…/MeasurePreserving.lean:95`, **[verified]**). With `f := T^[k]` this turns `f =ᵐ g` into `f∘T^[k] =ᵐ g∘T^[k]`, summed over `range k` to get `birkhoffSum T f k =ᵐ birkhoffSum T g k` (auxiliary L-AE below).

### Set-integral toolkit — `Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- **S1** `setIntegral_le_integral (hfi : Integrable f μ) (hf : 0 ≤ᵐ[μ] f) : ∫ x in s, f x ∂μ ≤ ∫ x, f x ∂μ`. line 728. **[verified]** (fact (a)).
- **S2** `integral_add_compl (hs : MeasurableSet s) (hfi : Integrable f μ) : ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ`. line 150. **[verified]** (fact (c)).
- **S3** `setIntegral_eq_zero_of_forall_eq_zero (h : ∀ x ∈ t, f x = 0) : ∫ x in t, f x ∂μ = 0`. line 351. **[verified]** (fact (c), the `∫_{E_Nᶜ} M_N = 0` part).
- **S4** `setIntegral_mono_on (hs : MeasurableSet s) (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) (h : ∀ x ∈ s, f x ≤ g x) : ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ`. line 747. **[verified]** (integrate (★) over `E_N`; supplies the `x ∈ E_N` hypothesis we need). The integrability args come from `Integrable.integrableOn` (`Mathlib/MeasureTheory/Integral/IntegrableOn.lean`, `Integrable.integrableOn : Integrable f μ → IntegrableOn f s μ`, **[verified]**).
- **S5** `integral_sub` / `setIntegral` linearity to split `∫_{E_N}(M_N − M_N∘T) = ∫_{E_N} M_N − ∫_{E_N} M_N∘T` — use `MeasureTheory.integral_sub` on the restricted measure (`(Integrable.restrict)` of both summands), or `setIntegral` is `integral` on `μ.restrict s` so `integral_sub` applies directly. **[verify exact name `integral_sub` at use site]**
- **S6** `setIntegral_congr_set (hst : s =ᵐ[μ] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ`. line 77. **[verified]** (transfer `target(g) ↝ target(f)`).
- **S7** `setIntegral_congr_ae₀ (hs : NullMeasurableSet s μ) (h : ∀ᵐ x ∂μ, x ∈ s → f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ`. line 61. **[verified]** (transfer integrand `g ↝ f` on `target(f)`).
- **S8** `tendsto_setIntegral_of_monotone {ι} [Preorder ι] [(atTop).IsCountablyGenerated] {s : ι → Set X} (hsm : ∀ i, MeasurableSet (s i)) (h_mono : Monotone s) (hfi : IntegrableOn f (⋃ n, s n) μ) : Tendsto (fun i => ∫ x in s i, f x ∂μ) atTop (𝓝 (∫ x in ⋃ n, s n, f x ∂μ))`. line 284. **[verified]** (the limit step; `ℕ` has `atTop` countably generated by instance).

### Order / topology / measurability
- **O1** `Finset.lt_sup'_iff : a < s.sup' H f ↔ ∃ b ∈ s, a < f b`. `Mathlib/Data/Finset/Lattice/Fold.lean:719`. **[verified]** (unfold `E_N` membership).
- **O2** `Finset.le_sup'_iff`, `Finset.le_sup' (h : b ∈ s) : f b ≤ s.sup' ⟨b,h⟩ f` (lines 714, 539). **[verified]** (for the `max` manipulations in (★)).
- **O3** `Finset.sup'_le (hs) (f) (h : ∀ b ∈ s, f b ≤ a) : s.sup' hs f ≤ a` / `Finset.sup'_le_iff` (lines 533, 529). **[verified]** (the `max_{1≤j≤N+1} ≥ max_{1≤j≤N}` and the `g x + max = max(g x + ·)` rewrites).
- **O4** `Finset.sup'_mono (h : s₁ ⊆ s₂) (h₁ : s₁.Nonempty) : s₁.sup' h₁ f ≤ s₂.sup' (h₁.mono h) f`. line 636. **[verified]** (monotonicity `M_N ≤ M_{N+1}` ⇒ `Monotone (E_·)`).
- **O5** `Finset.nonempty_range_add_one : (range (n+1)).Nonempty`. `Mathlib/Data/Finset/Range.lean:113`. **[verified]** (the `sup'` nonemptiness witness — use this exact term so it matches the measurability lemma O8).
- **O6** `ge_of_tendsto' {x} [NeBot x] (lim : Tendsto f x (𝓝 a)) (h : ∀ c, b ≤ f c) : b ≤ a` — the `@[to_dual]` of `le_of_tendsto'`, `Mathlib/Topology/Order/OrderClosed.lean:135`. **[verified]** (preserve `0 ≤` in the limit; `atTop` on `ℕ` is `NeBot`).
- **O7** `measurableSet_lt (hf : Measurable f) (hg : Measurable g) : MeasurableSet {a | f a < g a}`. `Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean:245`. **[verified]** (`E_N = {0 < M_N}` measurable; also each `{0 < S_k}` for the target set).
- **O8** `Finset.measurable_range_sup'' (hf : ∀ k ≤ n, Measurable (f k)) : Measurable fun x => (range (n+1)).sup' nonempty_range_add_one fun k => f k x`. `Mathlib/MeasureTheory/Order/Lattice.lean:221`. **[verified]** (measurability of `x ↦ M_N x`; note it bakes in `nonempty_range_add_one`, so define `M_N` with that exact witness).
- **O9** `Measurable.iterate (hf : Measurable f) : ∀ n, Measurable f^[n]`. `Mathlib/MeasureTheory/MeasurableSpace/Basic.lean:280`. **[verified]**, and `Finset.measurable_sum (s) (hf : ∀ i ∈ s, Measurable (f i)) : Measurable (∑ i ∈ s, f i)` (additive of `Finset.measurable_prod`, `Mathlib/MeasureTheory/Group/Arithmetic.lean:833`). **[verified]** (measurability of `x ↦ S_k x = birkhoffSum T g k x`, after `simp only [birkhoffSum]`).
- **O10** `Integrable.sup (hf hg : Integrable _ μ) : Integrable (f ⊔ g) μ`. `…/L1Space/Integrable.lean:564`. **[verified]** and `integrable_finsetSum'/integrable_finsetSum` (lines 439/447, **[verified]**) — building blocks for aux lemma I2 (integrability of `M_N`).
- **O11** `AEStronglyMeasurable.mk`, `.measurable_mk` (`…:156`), `.ae_eq_mk : f =ᵐ[μ] hf.mk f` (`…:160`), in `Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`. **[verified]** (produce the measurable representative `g`).
- **O12** `Set.iUnion`/`Set.mem_iUnion`, `Nat.lt_succ_iff`, `Finset.mem_range` — plumbing for the union-equals-target set identity. **[standard, no risk]**

---

## 4. Auxiliary lemmas to build first (in dependency order)

These should be **private** lemmas in `MaximalErgodic.lean`, stated for a generic
measurable `g : X → ℝ` so the final theorem just instantiates and transfers.

> Naming below is a suggestion; `M` denotes the maximal function. Throughout,
> `variable {X} [MeasurableSpace X] {μ : Measure X} {T : X → X}`.

### L-MAXDEF (definition, not a lemma)
```lean
/-- Garsia's maximal function: `M T g N x = max_{0 ≤ k ≤ N} birkhoffSum T g k x`.
Always `≥ 0` since the `k = 0` term is `birkhoffSum _ _ 0 = 0`. -/
noncomputable def maxBirkhoff (T : X → X) (g : X → ℝ) (N : ℕ) (x : X) : ℝ :=
  (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
    (fun k => birkhoffSum T g k x)
```
Use the literal `Finset.nonempty_range_add_one` so O8 (`measurable_range_sup''`)
applies without a `congr`.

### L-NONNEG  `0 ≤ maxBirkhoff T g N x`
Proof: `Finset.le_sup'_of_le` / `Finset.le_sup'` with `k = 0`, then
`birkhoffSum_zero` rewrites the `k=0` term to `0`. (O2 + B2.)

### L-MEAS  `Measurable g → Measurable (maxBirkhoff T g N)`  (needs `hT.measurable`)
Proof: O8 with `hf := fun k _ => measurability of (birkhoffSum T g k)`; the latter
by `simp only [birkhoffSum]` then `Finset.measurable_sum` + `g.comp (hT.measurable.iterate k)`
(O9). `fun_prop` may close it after unfolding `birkhoffSum`.

### L-INT  `Integrable g μ → Integrable (maxBirkhoff T g N) μ`  (needs `hT`)
Proof: induction on `N` (or `Finset.sup'_induction`).
- Each `birkhoffSum T g k` is integrable: `birkhoffSum T g k = ∑ j ∈ range k, g ∘ T^[j]`,
  every summand integrable by F4 with `hT.iterate j`, then `integrable_finsetSum'` (O10).
- `maxBirkhoff … (N+1) = maxBirkhoff … N ⊔ birkhoffSum T g (N+1)` (from `Finset.sup'`
  on `range (N+2) = insert (N+1) (range (N+1))`); close with `Integrable.sup` (O10).
  Base `N = 0`: `maxBirkhoff … 0 = birkhoffSum T g 0 = 0`, integrable.

### L-STEP  the pointwise Garsia inequality (★)
```lean
lemma maxBirkhoff_sub_le (N x) (hx : 0 < maxBirkhoff T g N x) :
    g x ≤ g x + maxBirkhoff T g N (T x) - maxBirkhoff T g N x   -- i.e. g x ≥ M_N x - M_N (T x)
```
better stated directly as the inequality used:
`maxBirkhoff T g N x - maxBirkhoff T g N (T x) ≤ g x` for `x ∈ E_N`.
Proof skeleton:
- `g x + maxBirkhoff T g N (T x) = (range (N+1)).sup' _ (fun k => g x + S_k (T x))`
  by pulling the constant `g x` through `sup'` (`Finset.sup'`-add: prove
  `c + s.sup' H f = s.sup' H (fun b => c + f b)` via `le_antisymm` with O2/O3, or
  search `Finset.sup'_add` / `Finset.add_sup'` — **verify name**; if absent, the
  two-line `le_antisymm` is trivial).
- `g x + S_k (T x) = S_{k+1} x` by B3 (`birkhoffSum_succ'`).
- So RHS `= (range (N+1)).sup' _ (fun k => S_{k+1} x) = max_{1≤j≤N+1} S_j x`.
- `maxBirkhoff T g N x ≤ max_{1≤j≤N+1} S_j x`: every `S_k x` with `0 ≤ k ≤ N`
  is `≤` the RHS. For `1 ≤ k ≤ N` directly (it appears on the RHS, O2). For
  `k = 0`, `S_0 x = 0 < maxBirkhoff … x ≤ … = RHS` using `hx` and L-NONNEG, OR
  note `S_0 = 0 ≤ S_1 x`? — cleanest: since `hx : 0 < M_N x`,
  `M_N x = max_{1≤k≤N} S_k x` (drop the dominated `0`), and that is termwise `≤ RHS`.
  Conclude `M_N x ≤ g x + M_N (T x)`, rearrange.

### L-AE  `f =ᵐ[μ] g → birkhoffSum T f n =ᵐ[μ] birkhoffSum T g n`  (needs `hT`)
Proof: `birkhoffSum T f n = ∑ k ∈ range n, f ∘ T^[k]`. For each `k`,
`f ∘ T^[k] =ᵐ[μ] g ∘ T^[k]` by F5 (`QuasiMeasurePreserving.ae_eq_comp`) with the
measure-preserving `T^[k]` (F3 → `.quasiMeasurePreserving`). Then a finite-`Finset`
a.e.-sum congruence (`Finset.sum` of finitely many `=ᵐ` is `=ᵐ`; via
`Filter.EventuallyEq` and `Finset.sum_congr`/`ae_all_iff` over `range n`).

This is used twice in the transfer: (i) the two target sets agree a.e.
(`{∃ n, 0 < S_{n+1}^f} =ᵐ {∃ n, 0 < S_{n+1}^g}` — countable union of a.e.-equal
sets, via `ae_all_iff` over `n : ℕ`), and (ii) integrand congruence is just
`hf.1.ae_eq_mk`.

---

## 5. The main proof, step by step (after the aux lemmas)

Let `g := hf.1.mk f`, `hgm := hf.1.measurable_mk : Measurable g`,
`hfg := hf.1.ae_eq_mk : f =ᵐ[μ] g`, `hgi : Integrable g μ` (= `hf.congr hfg`).
Set `E N := {x | 0 < maxBirkhoff T g N x}` and `U := ⋃ N, E N`.

1. **`E N` measurable** — `O7 (measurableSet_lt measurable_const (L-MEAS hgm))`.
2. **`E` monotone** — `Monotone E`: from O4 (`sup'_mono`, `range (N+1) ⊆ range (M+1)`),
   `maxBirkhoff T g N x ≤ maxBirkhoff T g M x`, so `0 < M_N ⇒ 0 < M_M`.
3. **`U = {x | ∃ n, 0 < birkhoffSum T g (n+1) x}`** (`target(g)`): `Set.ext`; unfold
   `E` membership with O1 + `Finset.mem_range`/`Nat.lt_succ_iff`; `S_0 = 0` kills `k=0`
   (B2); reindex `k = n+1`.
4. **`0 ≤ ∫_{E N} g` for all `N`** (the crux, combining §2 (1)(2)):
   - `hStep : ∀ x ∈ E N, maxBirkhoff T g N x - maxBirkhoff T g N (T x) ≤ g x` (L-STEP).
   - `∫_{E N} (M_N − M_N∘T) ≤ ∫_{E N} g` by S4 (`setIntegral_mono_on` with step 1’s
     measurability; integrabilities from L-INT, F4, `Integrable.integrableOn`, `.sub`).
   - `∫_{E N}(M_N − M_N∘T) = ∫_{E N} M_N − ∫_{E N} M_N∘T` (S5 `integral_sub` on `μ.restrict`).
   - `∫_{E N} M_N∘T ≤ ∫_X M_N∘T` (S1; nonneg from L-NONNEG composed with `T`).
   - `∫_X M_N∘T = ∫_X M_N` (F2 + `hT.map_eq`; `M_N∘T` matches `fun x => M_N (T x)`).
   - `∫_X M_N = ∫_{E N} M_N` (S2 `integral_add_compl` (step 1) + S3
     `setIntegral_eq_zero_of_forall_eq_zero`: on `(E N)ᶜ`, `¬0<M_N` and `0≤M_N` ⇒ `M_N=0`).
   - Chain with `linarith` ⇒ `0 ≤ ∫_{E N} M_N − ∫_{E N} M_N∘T ≤ ∫_{E N} g`.
5. **Limit** — `tendsto_setIntegral_of_monotone` (S8) with steps 1,2 and
   `hgi.integrableOn : IntegrableOn g U μ`:
   `Tendsto (fun N => ∫_{E N} g) atTop (𝓝 (∫_U g))`. Rewrite `U` by step 3.
   `ge_of_tendsto'` (O6) + step 4 ⇒ `0 ≤ ∫_{target(g)} g`.
6. **Transfer to `f`** —
   - `∫_{target(f)} f = ∫_{target(f)} g` by S7 (`setIntegral_congr_ae₀`,
     `target(f)` is `NullMeasurableSet` — see Risk R1 — and `hfg` gives the integrand a.e.eq).
   - `∫_{target(f)} g = ∫_{target(g)} g` by S6 (`setIntegral_congr_set`), since
     `target(f) =ᵐ[μ] target(g)` (L-AE (i)).
   - Conclude `0 ≤ ∫_{target(f)} f`, which is the goal (defeq after unfolding `birkhoffSum`).

---

## 6. Trickiest steps and Lean-specific risks

- **R1 (measurability of `f`, load-bearing).** `f` is only `AEStronglyMeasurable`,
  so the **target set is only `NullMeasurableSet`**, not `MeasurableSet`. The
  entire plan is engineered around proving everything for the measurable
  representative `g = hf.1.mk f`, then transferring (step 6). Do **not** try to
  apply S8/O7 to `f` directly. The `NullMeasurableSet (target f) μ` needed by S7
  follows from `target(f) =ᵐ target(g)` (L-AE) and `target(g)` measurable (step 1/3).
  *If this transfer proves fiddly, an acceptable fallback is to first state and
  prove a `private` core theorem with an extra hypothesis `Measurable f`, then
  derive the public theorem by the `mk` transfer — keeps the core clean.*

- **R2 (`T` is not an embedding).** Use **F2 `integral_map` + `hT.map_eq`**, never
  `MeasurePreserving.integral_comp`/`setIntegral_preimage_emb` (those need
  `MeasurableEmbedding T`, which we do not have). Likewise integrability of
  `M_N∘T` via **F4 `integrable_comp_of_integrable`**, not the `_emb` variant.
  Matching `M_N ∘ T` (as `Function.comp`) against `fun x => M_N (T x)` may need an
  explicit `Function.comp_apply`/`show` to line up F2/F4.

- **R3 (the `sup'` constant-pull in L-STEP).** `c + s.sup' H f = s.sup' H (c + f ·)`
  is the only “clever” algebra. Search `Finset.sup'_add`/`Finset.add_sup'` first;
  if absent, prove by `le_antisymm` using `Finset.sup'_le` (O3) and `Finset.le_sup'`
  (O2) — two ≤-directions, each one line. (For `ℝ`, `add` is monotone and the
  finset is nonempty, so this is clean; no `WithBot`/`⊥` issues because we never
  leave `ℝ`.)

- **R4 (integrability bookkeeping at S4/S5).** `setIntegral_mono_on` (S4) and
  `integral_sub` (S5) each need `IntegrableOn`/`Integrable` of `M_N`, `M_N∘T`, `g`.
  Chain: `Integrable M_N` (L-INT) → `Integrable (M_N∘T)` (F4) → `Integrable (M_N − M_N∘T)`
  (`.sub`) → restrict with `Integrable.integrableOn`. Keep these as explicit `have`s;
  `fun_prop` will not see `maxBirkhoff` through the `def` without `[fun_prop]` tags.

- **R5 (no EReal / −∞ here).** Everything is in `ℝ`; `f` integrable ⇒ all integrals
  finite. The `EReal`/`−∞` bookkeeping flagged in `understanding.md` belongs to
  Kingman (L2.6), **not** to this lemma. `M_N` is a max of finitely many real
  Birkhoff sums — finite, integrable. No `WithBot` leakage because we use
  `Finset.sup'` (nonempty) rather than `Finset.sup` (which would inject into
  `WithBot ℝ`).

- **R6 (a.e. vs everywhere).** (★) and `M_N ≥ 0` and `M_N = 0` on `E_Nᶜ` are all
  **everywhere** (pointwise) facts for the measurable `g` — no a.e. needed there,
  which simplifies S3/S4 (use the `∀ x ∈ s` forms, not the `aerestrict` forms).
  The only genuinely a.e. reasoning is the final `f ↝ g` transfer (R1) and L-AE.

- **R7 (union/index reindexing, step 3).** The off-by-one between the statement’s
  `birkhoffSum T f (n+1)` (`n : ℕ`, so indices `1,2,…`) and the `sup'` over
  `range (N+1)` (`k = 0,…,N`) is where a sign/index slip is most likely. Pin it
  with `Nat.lt_succ_iff`, `Finset.mem_range`, and an explicit `S_0 = 0` discharge
  (B2). Write the `Set.ext` proof carefully; consider a unit `#check`-style sanity
  pass on small `N` mentally.

- **R8 (`atTop` side-conditions for S8/O6).** `S8` needs
  `(atTop : Filter ℕ).IsCountablyGenerated` (instance, present) and `Monotone E`
  (step 2). `O6 ge_of_tendsto'` needs `NeBot (atTop : Filter ℕ)` (instance, present).
  No manual work expected, but if Lean cannot find the monotone-on-`ℕ` instance,
  feed `Monotone` explicitly.

- **R9 (`integral_sub` exact name).** S5 is the one place a name is not pinned to a
  read line — confirm `MeasureTheory.integral_sub (hf : Integrable f μ) (hg : Integrable g μ) : ∫ x, f x - g x ∂μ = ∫ x, f x ∂μ - ∫ x, g x ∂μ` applied to `μ.restrict (E N)` at the use site (it is standard and present; just verify on the green build).

---

## 7. Dependency summary (build order inside the file)

```
B2,B3 (Mathlib)         O5,O8,O9 (Mathlib)        F3,F4,F5 (Mathlib)
   │                        │                          │
maxBirkhoff (def) ── L-NONNEG ── L-MEAS ── L-INT     L-AE
   │                                  │                │
   └────────── L-STEP ────────────────┤                │
                                       │                │
        step 1 (E meas) ── step 2 (mono) ── step 3 (U=target g)
                                       │
                step 4 (0 ≤ ∫_{E N} g)  ◀── S1,S2,S3,S4,S5,F2,F4,L-STEP,L-INT,L-NONNEG
                                       │
                step 5 (limit)  ◀── S8,O6
                                       │
                step 6 (transfer f) ◀── S6,S7,L-AE,O11
                                       │
                setIntegral_birkhoffSum_pos_nonneg  ✓
```

The two most error-prone pieces are **L-STEP** (the `sup'` algebra, R3) and
**step 3 / step 6** (the index reindexing and the a.e. set transfer, R7+R1).
Everything else is direct lemma application.
