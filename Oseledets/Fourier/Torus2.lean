/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Fourier analysis on the 2-torus `𝕋² = (ℝ/ℤ)²`

This module packages the Fourier-analytic infrastructure on the 2-torus that the
toral-automorphism ergodicity argument (issue #3) consumes: the `ℤ²`-indexed family of
additive characters

  `e_{(m,n)} : (a, b) ↦ exp(2πi(m·a + n·b))`

is a **Hilbert basis** (orthonormal **and** complete) of `L²(𝕋², Haar)`, together with
Parseval. The single interface the ergodicity proof needs is
`eq_zero_of_forall_char_inner_eq_zero`: an `L²` function that is orthogonal to every
character is `0`.

## Provenance: this is a thin specialization, not a re-proof

Mathlib already builds the full `d`-dimensional torus Fourier theory in
`Mathlib.Analysis.Fourier.AddCircleMulti` for `UnitAddTorus d = (d → ℝ/ℤ)`:

* `UnitAddTorus.mFourier n` — the monomial `x ↦ ∏ i, exp(2πi·nᵢ·xᵢ)` (a `ContinuousMap`);
* `UnitAddTorus.orthonormal_mFourier` — orthonormality in `L²`;
* `UnitAddTorus.span_mFourierLp_closure_eq_top` — completeness (the `Lᵖ` span is dense),
  itself obtained by Stone–Weierstrass **directly on the product torus**
  (`mFourierSubalgebra_closure_eq_top`), so completeness needs no separate product-Hilbert-
  basis / tensor construction;
* `UnitAddTorus.mFourierBasis` — the resulting `HilbertBasis (d → ℤ) ℂ L²`;
* `UnitAddTorus.hasSum_sq_mFourierCoeff` — Parseval.

Taking `d := Fin 2` is exactly the 2-torus. We re-export those results under
2-torus-flavoured names, verify the explicit closed form
`e_{(m,n)}(a,b) = exp(2πi(m·a + n·b))`, and add the orthogonality interface, all
sorry-free and reducing to the Mathlib statements.

### A measure-normalisation subtlety (load-bearing)

`AddCircleMulti` states all of its `L²` results relative to a **file-local** measure
instance `MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩` (the Haar **probability**
measure, total mass `1`). That `local instance` does **not** leak to importers, where the
ambient `MeasureSpace (AddCircle 1)` instead resolves to `AddCircle.measureSpace 1`
(`volume = ENNReal.ofReal 1 • addHaarMeasure ⊤`). The two measures are propositionally equal
but **not** definitionally equal, so without intervention every reference to `mFourierBasis`,
`mFourierLp`, … fails to typecheck in an importing file (`Lp ℂ 2 volume` is a different type).
No Mathlib file imports `AddCircleMulti`, so this was never exercised upstream.

We resolve it the same way `AddCircleMulti` does: re-declare the **same** local instance
`MeasureSpace UnitAddCircle := ⟨haarAddCircle⟩` here, so our `volume` agrees with Mathlib's.
The resulting `volume` on `𝕋² = UnitAddTorus (Fin 2)` is then the product of the normalised
Haar probability measures on the two circle factors, i.e. the normalised Haar **probability**
measure on `𝕋²` — exactly the measure the ergodicity statement is about. Downstream consumers
(the toral-automorphism slice) must adopt the same instance; for an ergodicity statement,
which is about an invariant probability measure, this is the intended normalisation.

## Main definitions

* `Torus2` — abbreviation for `UnitAddTorus (Fin 2) = Fin 2 → ℝ/ℤ`.
* `torusChar m n` — the character `e_{(m,n)}`, a `ContinuousMap`.
* `torusCharLp m n` — `torusChar m n` as an element of `L²(𝕋²)`.
* `torusFourierBasis` — the `(Fin 2 → ℤ)`-indexed Hilbert basis of `L²(𝕋²)`
  (defeq `UnitAddTorus.mFourierBasis`).
* `torusFourierCoeff f m n` — the `(m,n)`-th Fourier coefficient.

## Main statements

* `torusChar_apply` — the explicit formula `e_{(m,n)}(a,b) = exp(2πi(m·a + n·b))`.
* `orthonormal_torusChar` — the characters are orthonormal in `L²`.
* `torusFourierBasis_repr` — the basis coordinates are the Fourier coefficients.
* `hasSum_sq_torusFourierCoeff` — Parseval's identity.
* `eq_zero_of_forall_torusFourierCoeff_eq_zero` — completeness in bare form: an `L²`
  function with all Fourier coefficients zero is `0`.
* `eq_zero_of_forall_char_inner_eq_zero` — **the ergodicity interface**: an `L²` function
  orthogonal to every character is `0`.
-/


noncomputable section

open scoped ComplexConjugate
open MeasureTheory UnitAddTorus Complex Real Submodule

namespace Oseledets.Fourier

/-- Normalise the measure on each circle factor `ℝ/ℤ` to be the Haar probability measure (total
mass `1`). This re-declares the file-local instance of `Mathlib.Analysis.Fourier.AddCircleMulti`,
so that `volume` in this file agrees with the measure `mFourierBasis`/`mFourierLp` are stated for.
Without it, the ambient `AddCircle.measureSpace 1` (a propositionally-but-not-definitionally equal
mass-`1` Haar measure) makes those Mathlib results fail to typecheck. -/
local instance instMeasureSpaceUnitAddCircle' : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

/-- The 2-torus `𝕋² = (ℝ/ℤ)²`, modelled as `UnitAddTorus (Fin 2) = Fin 2 → ℝ/ℤ`. With the local
Haar-probability instance above, its `volume` is the product of the normalised Haar probability
measures on the two circle factors, i.e. the normalised Haar probability measure on `𝕋²`. -/
abbrev Torus2 : Type := UnitAddTorus (Fin 2)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

/-- Pointwise `η`-expansion for `Fin 2 → ℤ`: `![k 0, k 1] = k`. -/
private theorem vec2_eta (k : Fin 2 → ℤ) : (![k 0, k 1] : Fin 2 → ℤ) = k := by
  ext i; fin_cases i <;> simp

/-! ### The characters and their algebra -/

/-- The `(m, n)`-th additive character `e_{(m,n)} : (a,b) ↦ exp(2πi(m·a + n·b))` of the 2-torus,
bundled as a continuous map. Definitionally it is `UnitAddTorus.mFourier ![m, n]`. -/
def torusChar (m n : ℤ) : C(Torus2, ℂ) := mFourier ![m, n]

theorem torusChar_eq_mFourier (m n : ℤ) : torusChar m n = mFourier ![m, n] := rfl

/-- The 2-torus character at a point given by two real coordinate representatives:
`e_{(m,n)}((a, b)) = exp(2πi·m·a) · exp(2πi·n·b)`. -/
theorem torusChar_apply_coe (m n : ℤ) (a b : ℝ) :
    torusChar m n ![(a : AddCircle (1 : ℝ)), (b : AddCircle (1 : ℝ))] =
      Complex.exp (2 * Real.pi * Complex.I * m * a) *
        Complex.exp (2 * Real.pi * Complex.I * n * b) := by
  simp only [torusChar, mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [fourier_coe_apply, fourier_coe_apply]
  norm_num

/-- The explicit closed form of the 2-torus character as a single exponential:
`e_{(m,n)}((a, b)) = exp(2πi(m·a + n·b))`. -/
theorem torusChar_apply (m n : ℤ) (a b : ℝ) :
    torusChar m n ![(a : AddCircle (1 : ℝ)), (b : AddCircle (1 : ℝ))] =
      Complex.exp (2 * Real.pi * Complex.I * (m * a + n * b)) := by
  rw [torusChar_apply_coe, ← Complex.exp_add]
  ring_nf

/-- The conjugate of a 2-torus character is the character with negated indices. -/
theorem torusChar_conj (m n : ℤ) (x : Torus2) :
    conj (torusChar m n x) = torusChar (-m) (-n) x := by
  have h : ![(-m : ℤ), -n] = (-(![m, n] : Fin 2 → ℤ)) := by
    ext i; fin_cases i <;> simp
  rw [torusChar_eq_mFourier, torusChar_eq_mFourier, h, mFourier_neg]

/-- Characters multiply by adding indices: `e_{(m,n)} · e_{(p,q)} = e_{(m+p, n+q)}`. -/
theorem torusChar_mul (m n p q : ℤ) (x : Torus2) :
    torusChar m n x * torusChar p q x = torusChar (m + p) (n + q) x := by
  have h : ![m + p, n + q] = (![m, n] + ![p, q] : Fin 2 → ℤ) := by
    ext i; fin_cases i <;> simp
  rw [torusChar_eq_mFourier, torusChar_eq_mFourier, torusChar_eq_mFourier, h, mFourier_add]

/-- The trivial character `e_{(0,0)}` is the constant function `1`. -/
theorem torusChar_zero (x : Torus2) : torusChar 0 0 x = 1 := by
  have h : (![(0 : ℤ), 0] : Fin 2 → ℤ) = 0 := by ext i; fin_cases i <;> simp
  rw [torusChar_eq_mFourier, h, mFourier_zero, ContinuousMap.one_apply]

/-- Each character has sup-norm `1` (it is unimodular). -/
theorem norm_torusChar (m n : ℤ) : ‖torusChar m n‖ = 1 := by
  rw [torusChar_eq_mFourier]; exact mFourier_norm

/-! ### The `L²` characters, orthonormality, and the Hilbert basis -/

/-- The character `e_{(m,n)}` as an element of `L²(𝕋²)`. Definitionally `mFourierLp 2 ![m, n]`. -/
def torusCharLp (m n : ℤ) : L²(Torus2) := mFourierLp 2 ![m, n]

theorem torusCharLp_eq (m n : ℤ) : torusCharLp m n = mFourierLp 2 ![m, n] := rfl

theorem coeFn_torusCharLp (m n : ℤ) :
    torusCharLp m n =ᵐ[volume] (mFourier ![m, n] : Torus2 → ℂ) := coeFn_mFourierLp 2 ![m, n]

/-- **Orthonormality.** The 2-torus characters form an orthonormal family in `L²(𝕋²)`. -/
theorem orthonormal_torusChar :
    Orthonormal ℂ (fun p : ℤ × ℤ => torusCharLp p.1 p.2) := by
  -- Reindex `ℤ × ℤ → (Fin 2 → ℤ)` via `![·, ·]`, then transport `orthonormal_mFourier`.
  have hinj : Function.Injective (fun p : ℤ × ℤ => (![p.1, p.2] : Fin 2 → ℤ)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0 h1
    simp [h0, h1]
  exact (orthonormal_mFourier (d := Fin 2)).comp _ hinj

/-- **The Hilbert basis.** The `(Fin 2 → ℤ)`-indexed family of characters is a Hilbert basis of
`L²(𝕋²)`: it is orthonormal and its span is dense (completeness). This is exactly
`UnitAddTorus.mFourierBasis` for `d = Fin 2`; the `(m, n)` face is recovered through `![m, n]`. -/
def torusFourierBasis : HilbertBasis (Fin 2 → ℤ) ℂ L²(Torus2) := mFourierBasis (d := Fin 2)

theorem torusFourierBasis_eq : torusFourierBasis = mFourierBasis (d := Fin 2) := rfl

/-- The basis vector of `torusFourierBasis` at `![m, n]` is the `L²` character `torusCharLp m n`. -/
theorem torusFourierBasis_apply (m n : ℤ) :
    torusFourierBasis ![m, n] = torusCharLp m n := by
  rw [torusFourierBasis, coe_mFourierBasis, torusCharLp]

/-! ### Fourier coefficients, series convergence and Parseval -/

/-- The `(m, n)`-th Fourier coefficient of `f : 𝕋² → ℂ`:
`∫ exp(-2πi(m·a + n·b)) · f(a,b) d(a,b)`. Definitionally `mFourierCoeff f ![m, n]`. -/
def torusFourierCoeff (f : Torus2 → ℂ) (m n : ℤ) : ℂ := mFourierCoeff f ![m, n]

theorem torusFourierCoeff_eq (f : Torus2 → ℂ) (m n : ℤ) :
    torusFourierCoeff f m n = mFourierCoeff f ![m, n] := rfl

/-- The basis coordinate of `f` at `![m, n]` is its `(m, n)`-th Fourier coefficient. -/
theorem torusFourierBasis_repr (f : L²(Torus2)) (m n : ℤ) :
    torusFourierBasis.repr f ![m, n] = torusFourierCoeff f m n := by
  rw [torusFourierBasis, mFourierBasis_repr, torusFourierCoeff]

/-- **L² convergence of the Fourier series.** Every `L²` function on `𝕋²` is the `L²`-limit of its
Fourier series `∑ c_n · e_n` (indexed over `n : Fin 2 → ℤ`, i.e. `(m, n) ∈ ℤ²`). -/
theorem hasSum_torusFourier_series_L2 (f : L²(Torus2)) :
    HasSum (fun n : Fin 2 → ℤ => mFourierCoeff f n • (mFourierLp 2 n : L²(Torus2))) f :=
  hasSum_mFourier_series_L2 f

/-- **Parseval's identity** (norms): the sum of squared moduli of the Fourier coefficients over
`(m, n) ∈ ℤ²` equals the squared `L²` norm `∫ |f|²`. -/
theorem hasSum_sq_torusFourierCoeff (f : L²(Torus2)) :
    HasSum (fun p : ℤ × ℤ => ‖torusFourierCoeff f p.1 p.2‖ ^ 2) (∫ t, ‖f t‖ ^ 2) := by
  have h := hasSum_sq_mFourierCoeff (d := Fin 2) f
  -- Reindex the statement (over `Fin 2 → ℤ`) along `finTwoArrowEquiv : (Fin 2 → ℤ) ≃ ℤ²`.
  refine ((finTwoArrowEquiv ℤ).hasSum_iff).1 (h.congr_fun (fun n => ?_))
  have hn : (![(finTwoArrowEquiv ℤ n).1, (finTwoArrowEquiv ℤ n).2] : Fin 2 → ℤ) = n := vec2_eta n
  simp only [Function.comp_apply, torusFourierCoeff, hn]

/-! ### The ergodicity interface: orthogonal to all characters ⟹ zero -/

/-- If every Fourier coefficient of an `L²` function vanishes, the function is `0` in `L²`. This is
the completeness of the character system in its bare form: the only `L²` function whose all Fourier
coefficients are zero is the zero function. -/
theorem eq_zero_of_forall_torusFourierCoeff_eq_zero (f : L²(Torus2))
    (h : ∀ m n : ℤ, torusFourierCoeff f m n = 0) : f = 0 := by
  -- `repr` is a linear isometric equivalence, hence injective; all coordinates are `0`.
  apply torusFourierBasis.repr.injective
  rw [map_zero]
  ext k
  rw [← vec2_eta k, torusFourierBasis_repr, h (k 0) (k 1)]
  rfl

/-- **The ergodicity interface.** An `L²` function on `𝕋²` that is orthogonal to *every* character
`e_{(m,n)}` is `0`. (The `inner` is the `L²` inner product `⟪e_{(m,n)}, f⟫ = ∫ conj(e)·f`.) -/
theorem eq_zero_of_forall_char_inner_eq_zero (f : L²(Torus2))
    (h : ∀ m n : ℤ, inner ℂ (torusCharLp m n) f = 0) : f = 0 := by
  apply eq_zero_of_forall_torusFourierCoeff_eq_zero
  intro m n
  rw [← torusFourierBasis_repr, torusFourierBasis.repr_apply_apply f ![m, n],
    torusFourierBasis_apply, h m n]

/-- Restatement of the interface for ergodicity: two `L²` functions with equal Fourier
coefficients against every character are equal. -/
theorem ext_of_forall_char_inner_eq (f g : L²(Torus2))
    (h : ∀ m n : ℤ, inner ℂ (torusCharLp m n) f = inner ℂ (torusCharLp m n) g) : f = g := by
  have hsub : f - g = 0 := by
    apply eq_zero_of_forall_char_inner_eq_zero
    intro m n
    rw [inner_sub_right, h m n, sub_self]
  exact sub_eq_zero.1 hsub

end Oseledets.Fourier
