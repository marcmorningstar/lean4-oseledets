/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.ForwardMeasurable
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# From a measurable subspace frame to a measurable orthogonal projector

For a measurably-varying family of subspaces `V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))`
the multiplicative ergodic theorem (in its measurable / non-invertible form) needs the
**orthogonal-projection matrix** `x ↦ orthProjMatrix (V x)` to be measurable. This file
delivers the *finite-dimensional constant-rank* route to that fact: starting from a
measurable family of vectors that is, for each `x`, an **orthonormal basis** of `V x`, the
projector is the (manifestly measurable) Gram matrix of the frame.

This is the converter on which the unconditional singular Oseledets filtration ("issue #6")
turns: the measurable graph of the eventual-kernel family
(`Oseledets.measurableSet_graph_eventualKer`) plus constant kernel dimension yields, by a
finite measurable stratification + Gram–Schmidt, exactly such a measurable orthonormal frame.
The clean, fully `sorry`-free heart of the converter — *measurable orthonormal frame ⇒
measurable projector* — is `measurable_orthProjMatrix_of_orthonormalFrame`, and (granted the
KRN/Castaing **conclusion**, `HasMeasurableSpanningFrame V`) the everywhere-Borel projector is
`sorry`-free via `measurable_orthProjMatrix_of_frame`. The remaining, genuinely measure-theoretic,
step is *not* the measurable selection — that Castaing selection is `sorry`-free downstream in
`Frontier.Issue6.CastaingSelection` (polarisation shortcut) — but the KRN **hypothesis** (weak
measurability of `x ↦ V x`) in *graph* form: the projection of the Borel graph onto `X` through a
ball. Its `x`-sections are σ-compact, so by the **Arsenin–Kunugui** theorem the projection is
Borel — a *true* statement Mathlib cannot yet prove (it has only the Lusin–Souslin analytic-set
machinery, under which a projection is merely analytic). It is isolated in
`exists_measurable_independentSpanningFrame_of_measurableGraph` and flagged there. The
a.e./universally-measurable weakening of that node *is* available and `sorry`-free
(`Frontier.Issue6.MeasurableProjection`, migrated to `Oseledets.Singular.MeasurableProjection`).

## Main definitions

* `Oseledets.IsMeasurableOrthonormalFrame`: a family `e : X → Fin m → EuclideanSpace ℝ (Fin d)`
  is a measurable orthonormal frame for `V` when each component map is measurable and, for
  every `x`, `e x` is orthonormal and spans `V x`.

## Main results

* `Oseledets.starProjection_eq_sum_inner_smul_of_span`: for an orthonormal family `e` whose
  span is `K`, the orthogonal projection onto `K` is `v ↦ ∑ i, ⟪e i, v⟫ • e i`.
* `Oseledets.orthProjMatrix_entry_eq_sum`: the `(a, b)` entry of `orthProjMatrix K` equals
  `∑ i, e i a * e i b` for such a frame — the Gram (outer-product sum) formula.
* `Oseledets.measurable_orthProjMatrix_of_orthonormalFrame`: **the converter's core** —
  a measurable orthonormal frame for `V` makes `x ↦ orthProjMatrix (V x)` measurable
  (hence `MeasurableSubspace V`).
* `Oseledets.measurable_gramSchmidt`, `Oseledets.measurable_gramSchmidtNormed`: Gram–Schmidt
  is measurable in its input frame (`sorry`-free).
* `Oseledets.isMeasurableOrthonormalFrame_gramSchmidtNormed`: a measurable, pointwise
  independent, pointwise spanning frame orthonormalises to a measurable orthonormal frame
  (`sorry`-free) — this discharges the orthonormalisation half of the converter.
* `Oseledets.HasMeasurableSpanningFrame`: the KRN/Castaing **conclusion** as a hypothesis — `V`
  admits a measurable, pointwise independent, pointwise spanning frame.
* `Oseledets.measurable_orthProjMatrix_of_frame`, `Oseledets.measurableSubspace_of_frame`:
  **the conditional everywhere-Borel projector, `sorry`-free** — granted
  `HasMeasurableSpanningFrame`, `x ↦ orthProjMatrix (V x)` is measurable. The converter has *no*
  measure-theoretic gap beyond this hypothesis.
* `Oseledets.measurableSubspace_of_measurableGraph_constDim`: **the target** — a measurable
  graph together with constant finite rank gives a measurable projector. It is reduced to the
  core via the frame-existence lemma below.

## The isolated measure-theoretic gap

* `Oseledets.exists_measurable_independentSpanningFrame_of_measurableGraph` (`sorry`, BLOCKED):
  production of the measurable spanning frame from a *bare* measurable graph at constant rank. The
  measurable-selection (KRN/Castaing) content is **not** the obstruction — it is `sorry`-free
  downstream in `Frontier.Issue6.CastaingSelection`
  (`Frontier.exists_measurable_independentSpanningFrame_of_measurableInfDist`, a polarisation
  shortcut), and orthonormalisation is `sorry`-free above. The obstruction is the KRN *hypothesis*
  itself in graph form: *weak measurability* of `x ↦ V x`, i.e. measurability of the projection
  `{x | infDist c (V x) < r} = Prod.fst '' (graph ∩ (univ ×ˢ ball c r))`. Its `x`-sections are
  σ-compact, so the **Arsenin–Kunugui** theorem makes the projection Borel — *true*, but Mathlib has
  only Lusin–Souslin (projection ⟹ analytic, generally non-Borel by Suslin) and no
  `MeasurableSpace`/`Borel` structure on the Grassmannian, so the everywhere-Borel discharge has no
  Mathlib foothold. The node is *equivalent to the converter's target itself* (via
  `infDist c (V x) = ‖c − (V x).starProjection c‖`), confirming it is irreducible. The a.e.
  weakening (analytic ⟹ universally measurable) *is* `sorry`-free and already migrated
  (`Oseledets.Singular.MeasurableProjection`).

Literature: C. González-Tokman, A. Quas, *A semi-invertible operator Oseledets theorem*
(ETDS 2014), Appendix B (measurable Grassmannian, nice bases) and G. Froyland, S. Lloyd,
A. Quas, *Lyapunov exponents and the semi-invertible MET* (ETDS 2010), Lemma 6 (projection
measurability), adapted to the elementary finite-dimensional Euclidean setting.
-/

open scoped Matrix
open Submodule

namespace Oseledets

variable {d : ℕ}

section Frame

variable {m : ℕ} {K : Submodule ℝ (EuclideanSpace ℝ (Fin d))}
  {e : Fin m → EuclideanSpace ℝ (Fin d)}

/-- **Projection via an orthonormal frame.** If `e` is an orthonormal family in
`EuclideanSpace ℝ (Fin d)` whose span is `K`, then the orthogonal projection onto `K` sends
`v` to `∑ i, ⟪e i, v⟫ • e i`. We verify the defining property of `starProjection`: the
candidate lies in `K` and `v` minus it is orthogonal to every spanning vector `e j`. -/
theorem starProjection_eq_sum_inner_smul_of_span
    (hon : Orthonormal ℝ e) (hspan : span ℝ (Set.range e) = K)
    (v : EuclideanSpace ℝ (Fin d)) :
    K.starProjection v = ∑ i, (inner ℝ (e i) v) • e i := by
  -- The candidate point `p ∈ K` and its orthogonality characterise the projection.
  set p : EuclideanSpace ℝ (Fin d) := ∑ i, (inner ℝ (e i) v) • e i with hp
  have hpK : p ∈ K := by
    rw [← hspan]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  -- It suffices to check orthogonality of `v - p` against each `e j` (these span `K`).
  refine eq_starProjection_of_mem_of_inner_eq_zero hpK ?_
  -- Reduce `∀ w ∈ K, ⟪v - p, w⟫ = 0` to the spanning generators `e j`.
  rw [← hspan]
  refine fun w hw => Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨j, rfl⟩
    -- `⟪v - p, e j⟫ = ⟪v, e j⟫ - ∑ i ⟪e i, v⟫ ⟪e i, e j⟫ = ⟪v, e j⟫ - ⟪e j, v⟫ = 0`.
    rw [inner_sub_left, hp, sum_inner]
    have hδ : ∀ i, (inner ℝ ((inner ℝ (e i) v) • e i) (e j))
        = (inner ℝ (e i) v) * (if i = j then 1 else 0) := by
      intro i
      rw [inner_smul_left, RCLike.conj_to_real, (orthonormal_iff_ite.mp hon) i j]
    simp only [hδ, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ j (fun i => inner ℝ (e i) v)]
    simp only [Finset.mem_univ, if_true]
    rw [real_inner_comm (e j) v, sub_self]
  · simp
  · intro x y _ _ hx hy
    rw [inner_add_right, hx, hy, add_zero]
  · intro a x _ hx
    rw [inner_smul_right, hx, mul_zero]

/-- **Gram (outer-product) formula for the projector matrix.** For an orthonormal frame `e`
spanning `K`, the `(a, b)` entry of `orthProjMatrix K` equals `∑ i, e i a * e i b`. Using
`orthProjMatrix K a b = ⟪single a, starProjection K (single b)⟫` and the frame projection
formula, the coordinate identities `⟪single a, w⟫ = w a` and `⟪e i, single b⟫ = e i b`
collapse the sum to the stated real bilinear form. -/
theorem orthProjMatrix_entry_eq_sum
    (hon : Orthonormal ℝ e) (hspan : span ℝ (Set.range e) = K) (a b : Fin d) :
    orthProjMatrix K a b = ∑ i, e i a * e i b := by
  -- `toEuclideanCLM (orthProjMatrix K) = starProjection K`, so the entry is an inner product.
  have hclm : Matrix.toEuclideanCLM (𝕜 := ℝ) (orthProjMatrix K) = K.starProjection := by
    rw [orthProjMatrix, StarAlgEquiv.apply_symm_apply]
  have hentry : orthProjMatrix K a b
      = inner ℝ (EuclideanSpace.single a (1 : ℝ))
          (K.starProjection (EuclideanSpace.single b (1 : ℝ))) := by
    rw [← hclm, Matrix.inner_toEuclideanCLM]
    -- `single a 1 ⬝ᵥ M *ᵥ single b 1 = M a b`.
    simp [EuclideanSpace.single, dotProduct, Matrix.mulVec, PiLp.single_apply,
      Finset.sum_ite_eq, eq_comm]
  rw [hentry, starProjection_eq_sum_inner_smul_of_span hon hspan, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
  simp only [map_one, one_mul, RCLike.conj_to_real]
  ring

end Frame

variable {X : Type*} [MeasurableSpace X]

/-- A family `e : X → Fin m → EuclideanSpace ℝ (Fin d)` is a **measurable orthonormal frame**
for `V` when each coordinate map `x ↦ e x i` is measurable and, for every `x`, the tuple
`e x` is orthonormal and spans `V x`. This is the structured input consumed by the projector
converter `measurable_orthProjMatrix_of_orthonormalFrame`. -/
structure IsMeasurableOrthonormalFrame {m : ℕ}
    (V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (e : X → Fin m → EuclideanSpace ℝ (Fin d)) : Prop where
  /-- Each frame component varies measurably in `x`. -/
  measurable : ∀ i, Measurable fun x => e x i
  /-- The frame is orthonormal at every point. -/
  orthonormal : ∀ x, Orthonormal ℝ (e x)
  /-- The frame spans the assigned subspace at every point. -/
  span : ∀ x, span ℝ (Set.range (e x)) = V x

/-- **The converter's sorry-free core.** A measurable orthonormal frame for `V` makes the
orthogonal-projection matrix `x ↦ orthProjMatrix (V x)` measurable. Each matrix entry is the
finite sum `∑ i, e x i a * e x i b` (`orthProjMatrix_entry_eq_sum`), a finite sum of products
of measurable real functions, hence measurable; the matrix measurable structure is entrywise
(`Oseledets.instMeasurableSpaceMatrix`). -/
theorem measurable_orthProjMatrix_of_orthonormalFrame {m : ℕ}
    {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    {e : X → Fin m → EuclideanSpace ℝ (Fin d)} (hframe : IsMeasurableOrthonormalFrame V e) :
    Measurable fun x => orthProjMatrix (V x) := by
  -- Reduce matrix measurability to entrywise measurability.
  refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => ?_
  -- Rewrite the entry as the measurable Gram sum.
  have hentry : (fun x => orthProjMatrix (V x) a b)
      = fun x => ∑ i, e x i a * e x i b := by
    funext x
    exact orthProjMatrix_entry_eq_sum (hframe.orthonormal x) (hframe.span x) a b
  rw [hentry]
  -- A finite sum of products of measurable coordinate maps is measurable.
  -- The coordinate projection `w ↦ w c` is continuous on `EuclideanSpace`, hence measurable.
  have hcoord : ∀ c : Fin d,
      Measurable fun w : EuclideanSpace ℝ (Fin d) => w c := fun c =>
    (PiLp.continuous_apply 2 (β := fun _ : Fin d => ℝ) c).measurable
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((hcoord a).comp (hframe.measurable i)).mul ((hcoord b).comp (hframe.measurable i))

/-- A measurable orthonormal frame witnesses `MeasurableSubspace V`. -/
theorem measurableSubspace_of_orthonormalFrame {m : ℕ}
    {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    {e : X → Fin m → EuclideanSpace ℝ (Fin d)} (hframe : IsMeasurableOrthonormalFrame V e) :
    MeasurableSubspace V :=
  measurable_orthProjMatrix_of_orthonormalFrame hframe

/-! ### Measurable Gram–Schmidt: orthonormalising a measurable independent frame -/

section MeasurableGramSchmidt

open InnerProductSpace

variable {m : ℕ} {f : X → Fin m → EuclideanSpace ℝ (Fin d)}

/-- **`gramSchmidt` is measurable in the frame.** For a measurable frame `f`, each
Gram–Schmidt output `x ↦ gramSchmidt ℝ (f x) n` is measurable. Proof by well-founded (`<`)
induction on `n : Fin m` using the recursion `gramSchmidt f n = f n - ∑_{i < n} (⟪gs i, f n⟫ /
‖gs i‖²) • gs i` (`gramSchmidt_def''`): each summand is built from the (inductively measurable)
earlier outputs by measurable inner products, real inversion (measurable everywhere, junk value
at 0), and scalar multiplication. -/
theorem measurable_gramSchmidt (hf : ∀ i, Measurable fun x => f x i) (n : Fin m) :
    Measurable fun x => gramSchmidt ℝ (f x) n := by
  induction n using WellFoundedLT.induction with
  | ind n ih =>
    -- Rewrite the `n`-th output via the explicit normalised recursion.
    have hrec : (fun x => gramSchmidt ℝ (f x) n)
        = fun x => f x n - ∑ i ∈ Finset.Iio n,
          ((inner ℝ (gramSchmidt ℝ (f x) i) (f x n)) /
            (‖gramSchmidt ℝ (f x) i‖ : ℝ) ^ 2) • gramSchmidt ℝ (f x) i := by
      funext x
      exact eq_sub_of_add_eq (gramSchmidt_def'' ℝ (f x) n).symm
    rw [hrec]
    refine (hf n).sub (Finset.measurable_sum _ fun i hi => ?_)
    -- `i < n`, so `gramSchmidt ℝ (· ) i` is measurable by the induction hypothesis.
    have hi' : i < n := Finset.mem_Iio.mp hi
    have hgsi : Measurable fun x => gramSchmidt ℝ (f x) i := ih i hi'
    refine Measurable.smul ?_ hgsi
    exact (hgsi.inner (hf n)).div ((hgsi.norm).pow_const 2)

/-- **`gramSchmidtNormed` is measurable in the frame.** Immediate from `measurable_gramSchmidt`:
`gramSchmidtNormed ℝ f n = ‖gramSchmidt ℝ f n‖⁻¹ • gramSchmidt ℝ f n`, a measurable scalar
(real inversion of a measurable norm) times a measurable vector. -/
theorem measurable_gramSchmidtNormed (hf : ∀ i, Measurable fun x => f x i) (n : Fin m) :
    Measurable fun x => gramSchmidtNormed ℝ (f x) n := by
  simp only [gramSchmidtNormed]
  have hgs : Measurable fun x => gramSchmidt ℝ (f x) n := measurable_gramSchmidt hf n
  exact Measurable.smul (by simpa using hgs.norm.inv) hgs

end MeasurableGramSchmidt

/-! ### From a measurable independent spanning frame to an orthonormal frame -/

open InnerProductSpace

variable {m : ℕ}

/-- **Orthonormalising a measurable independent spanning frame.** If `f : X → Fin m →
EuclideanSpace ℝ (Fin d)` is a measurable family that is, for every `x`, linearly independent
and spans `V x`, then its Gram–Schmidt normalisation is a measurable orthonormal frame for `V`.
This discharges sub-steps (2)–(3) of the converter (orthonormalisation) entirely
`sorry`-free, leaving only the production of the independent spanning frame itself (the
Castaing/KRN selection, sub-step (1)). -/
theorem isMeasurableOrthonormalFrame_gramSchmidtNormed
    {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    {f : X → Fin m → EuclideanSpace ℝ (Fin d)} (hf : ∀ i, Measurable fun x => f x i)
    (hindep : ∀ x, LinearIndependent ℝ (f x)) (hspan : ∀ x, span ℝ (Set.range (f x)) = V x) :
    IsMeasurableOrthonormalFrame V (fun x => gramSchmidtNormed ℝ (f x)) where
  measurable i := measurable_gramSchmidtNormed hf i
  orthonormal x := gramSchmidtNormed_orthonormal (hindep x)
  span x := by
    rw [span_gramSchmidtNormed_range, span_gramSchmidt, hspan]

/-! ### The KRN/Castaing *conclusion*, conditioned: an everywhere-Borel projector

The Kuratowski–Ryll-Nardzewski / Castaing measurable-selection theorem is an *implication*
`weak measurability ⟹ a measurable selection (Castaing representation)`. The two halves of that
implication play very different roles in this converter, and it is worth isolating them precisely.

* The **conclusion** of KRN — that a measurable, pointwise linearly-independent, pointwise
  spanning frame `f` for `V` *exists* — is captured by the predicate `HasMeasurableSpanningFrame V`
  below. **Granted this conclusion, the everywhere-Borel projector is `sorry`-free**: Gram–Schmidt
  orthonormalises `f` measurably (`isMeasurableOrthonormalFrame_gramSchmidtNormed`) and the Gram
  outer-product formula turns the frame into the measurable projector
  (`measurable_orthProjMatrix_of_orthonormalFrame`). This is `measurable_orthProjMatrix_of_frame`.

* The **hypothesis** of KRN — weak measurability of the multifunction `x ↦ V x`, i.e. measurability
  of `{x | V x ∩ U ≠ ∅}` for every open `U` — is the *only* thing the bare measurable graph does not
  hand us for free. Producing the frame from a measurable graph is therefore neither the
  Gram–Schmidt step nor the selection step (both elementary / already done): it is exactly the
  *weak-measurability* step `graph ⟹ {x | V x ∩ U ≠ ∅} measurable`, which for the subspace-valued,
  constant-rank multifunction is the **Arsenin–Kunugui** projection theorem (see the BLOCKED leaf
  below).

So the converter's only genuine wall is the KRN *hypothesis* in its graph form, not the KRN
selection itself; the selection content is delivered `sorry`-free downstream in
`Frontier.Issue6.CastaingSelection` (via a finite-dimensional polarisation shortcut), and the
present section records the `sorry`-free conditional half here, at the converter's own layer. -/

/-- **The KRN/Castaing conclusion, as a hypothesis.** `V` *has a measurable spanning frame* at
rank `m` when there is a measurable family `f : X → Fin m → EuclideanSpace ℝ (Fin d)` that is, at
every `x`, linearly independent and spans `V x`. This is exactly the deliverable of the
Kuratowski–Ryll-Nardzewski / Castaing measurable-selection theorem for the closed-valued (here
finite-dimensional-subspace-valued) multifunction `x ↦ V x`. Everything the converter needs is a
`sorry`-free consequence of this predicate (`measurable_orthProjMatrix_of_frame`,
`measurableSubspace_of_frame`); only its *production* from a bare measurable graph is the
Arsenin–Kunugui wall. -/
def HasMeasurableSpanningFrame {m : ℕ}
    (V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ f : X → Fin m → EuclideanSpace ℝ (Fin d),
    (∀ i, Measurable fun x => f x i) ∧ (∀ x, LinearIndependent ℝ (f x)) ∧
      (∀ x, span ℝ (Set.range (f x)) = V x)

/-- **The everywhere-Borel projector from the KRN conclusion (`sorry`-free).** If `V` has a
measurable spanning frame at rank `m` (`HasMeasurableSpanningFrame`, the KRN/Castaing output), then
`x ↦ orthProjMatrix (V x)` is measurable. The frame is orthonormalised measurably by Gram–Schmidt
(`isMeasurableOrthonormalFrame_gramSchmidtNormed`) and fed to the `sorry`-free Gram-formula core
(`measurable_orthProjMatrix_of_orthonormalFrame`). This is the *positive* half of KRN/Castaing for
the converter, with no measure-theoretic gap: the entire dependence on the missing
measurable-selection input is now confined to the `HasMeasurableSpanningFrame` hypothesis. -/
theorem measurable_orthProjMatrix_of_frame {m : ℕ}
    {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    (hframe : HasMeasurableSpanningFrame (m := m) V) :
    Measurable fun x => orthProjMatrix (V x) := by
  obtain ⟨f, hf, hindep, hspan⟩ := hframe
  exact measurable_orthProjMatrix_of_orthonormalFrame
    (isMeasurableOrthonormalFrame_gramSchmidtNormed hf hindep hspan)

/-- **`MeasurableSubspace V` from the KRN conclusion (`sorry`-free).** Restatement of
`measurable_orthProjMatrix_of_frame` as a `MeasurableSubspace` witness. -/
theorem measurableSubspace_of_frame {m : ℕ}
    {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    (hframe : HasMeasurableSpanningFrame (m := m) V) :
    MeasurableSubspace V :=
  measurable_orthProjMatrix_of_frame hframe

/-! ### The measure-theoretic gap: from a measurable graph to a measurable frame

By the previous section the converter is `sorry`-free *given* a measurable spanning frame
(`HasMeasurableSpanningFrame`, the KRN/Castaing conclusion). The remaining BLOCKED leaf is purely
the production of that frame from a *bare measurable graph* — i.e. the KRN *hypothesis* (weak
measurability) in graph form, which is the Arsenin–Kunugui projection theorem. -/

/-- **Existence of a measurable orthonormal frame from a measurable graph at constant rank.**
A measurable graph `{(x, v) | v ∈ V x}` together with constant finite dimension `m` yields a
measurable orthonormal frame `e` for `V`.

**This is the single genuinely measure-theoretic gap of the converter and is left `sorry`
(BLOCKED).** It is the production of a `HasMeasurableSpanningFrame V` (the KRN/Castaing conclusion)
from the bare measurable graph; granted that frame, the everywhere-Borel projector is `sorry`-free
(`measurable_orthProjMatrix_of_frame`). Two contributing steps are *already done* `sorry`-free, so
the remaining gap is sharper than "Castaing representation absent":

* **The KRN/Castaing selection itself is NOT the wall.** The finite-dimensional Castaing
  representation — a measurable independent spanning frame for `V` *given weak measurability of `V`*
  — is delivered `sorry`-free downstream in `Frontier.Issue6.CastaingSelection`
  (`Frontier.exists_measurable_independentSpanningFrame_of_measurableInfDist`), via a polarisation
  shortcut that bypasses dense measurable selection entirely: every projector coordinate is a fixed
  real combination of the scalar maps `x ↦ infDist c (V x)`, so weak measurability alone yields the
  measurable projected basis, from which the recursive measurable subframe picker
  (`Frontier.pickIndependent`) extracts the frame. Orthonormalisation is likewise `sorry`-free here
  (`isMeasurableOrthonormalFrame_gramSchmidtNormed`).

* **The wall is the KRN *hypothesis* in graph form = Arsenin–Kunugui.** What the bare graph does not
  give is *weak measurability* of `x ↦ V x`, i.e. measurability of
  `{x | infDist c (V x) < r} = {x | V x ∩ ball c r ≠ ∅}`. This set is
  `Prod.fst '' (graph ∩ (univ ×ˢ ball c r))`, the projection onto `X` of a Borel set whose
  `x`-sections `V x ∩ ball c r` are **σ-compact** (open subsets of the finite-dimensional, locally
  compact `V x`). *The projection of a Borel set with σ-compact sections is Borel* — this is the
  **Arsenin–Kunugui theorem** (Kechris, *Classical Descriptive Set Theory*, 18.18; Saint-Raymond).
  The statement here is therefore **true** (the σ-compact-section hypothesis is met), but Mathlib
  has only the Lusin–Souslin analytic-set machinery and the unrestricted projection of a Borel set
  is in general merely **analytic, not Borel** (Suslin), so the everywhere-Borel discharge requires
  the Arsenin–Kunugui strengthening, which is absent from Mathlib. (The a.e./universally-measurable
  weakening *is* available — projection ⟹ analytic ⟹ universally measurable — and is proved
  `sorry`-free in `Frontier.Issue6.MeasurableProjection` /
  `Oseledets.Singular.MeasurableProjection`; that is the correct hypothesis for the a.e.
  multiplicative ergodic theorem and is already migrated into the linted library.)

This node is *equivalent to the converter's own target*:
`infDist c (V x) = ‖c − (V x).starProjection c‖`
(`Frontier.infDist_eq_norm_sub_starProjection`), so weak measurability of `V` is interderivable with
measurability of the projector. It is therefore a single irreducible measure-theoretic node, not a
removable detour, and the KRN/Castaing route cannot bypass it: KRN *consumes* weak measurability as
its hypothesis.

Literature: K. Kuratowski, C. Ryll-Nardzewski, *A general theorem on selectors* (1965);
W. Arsenin, K. Kunugui (Kechris, *Classical DST*, 18.18) on projections of Borel sets with
σ-compact sections; J. Saint-Raymond (1976); C. González-Tokman, A. Quas, *A semi-invertible
operator Oseledets theorem* (ETDS 2014), Appendix B. -/
theorem exists_measurable_independentSpanningFrame_of_measurableGraph
    {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))} {m : ℕ}
    (hgraph : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1})
    (hdim : ∀ x, Module.finrank ℝ (V x) = m) :
    ∃ f : X → Fin m → EuclideanSpace ℝ (Fin d),
      (∀ i, Measurable fun x => f x i) ∧ (∀ x, LinearIndependent ℝ (f x)) ∧
        (∀ x, span ℝ (Set.range (f x)) = V x) := by
  sorry -- BLOCKED: Arsenin–Kunugui projection theorem (projection of a Borel set with σ-compact
        -- sections is Borel) absent from Mathlib. The KRN/Castaing SELECTION is sorry-free
        -- downstream (CastaingSelection); the wall is the KRN HYPOTHESIS (weak measurability of V)
        -- in graph form, equivalent to the converter's target. See the docstring; the a.e. route
        -- (analytic ⟹ universally measurable) is sorry-free in MeasurableProjection.

/-- **Existence of a measurable orthonormal frame from a measurable graph at constant rank.**
Combines the (blocked) independent-spanning-frame existence with `sorry`-free Gram–Schmidt
orthonormalisation (`isMeasurableOrthonormalFrame_gramSchmidtNormed`). The dependence on `sorry`
is inherited solely from `exists_measurable_independentSpanningFrame_of_measurableGraph`. -/
theorem exists_measurable_orthonormalFrame_of_measurableGraph
    {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))} {m : ℕ}
    (hgraph : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1})
    (hdim : ∀ x, Module.finrank ℝ (V x) = m) :
    ∃ e : X → Fin m → EuclideanSpace ℝ (Fin d), IsMeasurableOrthonormalFrame V e := by
  obtain ⟨f, hf, hindep, hspan⟩ :=
    exists_measurable_independentSpanningFrame_of_measurableGraph hgraph hdim
  exact ⟨_, isMeasurableOrthonormalFrame_gramSchmidtNormed hf hindep hspan⟩

/-- **The target converter (constant rank).** A measurable graph together with constant finite
dimension `m` makes the orthogonal-projection matrix `x ↦ orthProjMatrix (V x)` measurable.
The proof extracts a measurable orthonormal frame from the graph
(`exists_measurable_orthonormalFrame_of_measurableGraph`) and feeds it to the `sorry`-free core
`measurable_orthProjMatrix_of_orthonormalFrame`. Consequently the inherited dependence on
`sorry` is confined to the one Castaing/KRN measurable-selection gap. -/
theorem measurableSubspace_of_measurableGraph_constDim
    {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))} {m : ℕ} [NeZero d]
    (hgraph : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1})
    (hdim : ∀ x, Module.finrank ℝ (V x) = m) :
    Measurable (fun x => orthProjMatrix (V x)) := by
  obtain ⟨e, hframe⟩ := exists_measurable_orthonormalFrame_of_measurableGraph hgraph hdim
  exact measurable_orthProjMatrix_of_orthonormalFrame hframe

end Oseledets
