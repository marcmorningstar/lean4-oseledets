import Mathlib
import Oseledets.OperatorEntropy
open scoped MatrixOrder ComplexOrder
open Matrix

/-!
# Issue #22 keystone — VERIFIED SKELETON (de-risk scout)

Chain:  OperatorConvexOn → HPJ operator-Jensen → Effros operator perspective →
        joint convexity of Umegaki relative entropy → DPI.

ARCHITECTURE DECISION (probe-driven):
* The operator-convexity layer is stated over `Matrix (Fin m) (Fin m) ℂ`, which carries a NATIVE
  ℝ-cfc (`Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean`) so `cfc f M` elaborates, plus
  the scoped Loewner order (`MatrixOrder`).  [PROBE-VERIFIED: `cfc Real.log M` on Matrix works.]
* The ONLY operator-convexity INPUT (`−log` operator convex, K2) is imported from Mathlib's
  `CFC.concaveOn_log`, which is stated over a C⋆-algebra; it is transported `CStarMatrix → Matrix`
  once, across the defeq carrier `CStarMatrix.ofMatrix = Equiv.refl` bundled as the star-alg-equiv
  `ofMatrixStarAlgEquiv` (order-iso via `map_nonneg`; cfc-iso via `StarAlgHomClass.map_cfc`).
* FRICTION (probe4): the ℝ-cfc on `CStarMatrix` does NOT auto-synthesize; use `CFC.log`/`CFC.rpow`
  wrappers (need only `[CStarAlgebra]`, Q4/Q5 ✓) or `haveI` the instance inside K2's transport.
-/

noncomputable section
namespace Oseledets.OperatorEntropy.Lieb

/-! ## K0 — operator convexity framework (matrix-convex of all orders, over `Matrix`) -/

/-- `f` is **operator convex** on `I`: its cfc is convex (Loewner order) in every matrix order
`Matrix (Fin m) (Fin m) ℂ`.  This "matrix convex of all orders" definition is exactly what the
Hansen–Pedersen–Jensen dilation proof consumes (it needs convexity in the doubled algebra `M₂`). -/
def OperatorConvexOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ m : ℕ, ConvexOn ℝ {a : Matrix (Fin m) (Fin m) ℂ | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I}
    (fun a => cfc f a)

/-! ## K2 — `−log` is operator convex (from `CFC.concaveOn_log`, transported) -/

theorem operatorConvexOn_neg_log : OperatorConvexOn (Set.Ioi 0) (fun x => -Real.log x) := by
  sorry -- transport `(CFC.concaveOn_log (A := CStarMatrix (Fin m) (Fin m) ℂ)).neg` to Matrix via
        -- `ofMatrixStarAlgEquiv` (order-iso + `StarAlgHomClass.map_cfc`); cone bridge
        -- `IsStrictlyPositive ↔ IsSelfAdjoint ∧ spectrum ⊆ Ioi 0`, and `cfc (-Real.log)=-CFC.log`.

/-! ## K1 — Hansen–Pedersen–Jensen operator-Jensen (two forms) -/

variable {N : ℕ}

/-- **HPJ isometry form** (Hansen–Pedersen Thm 2.1(iii)): for an isometry `V` (`V⋆V=1`),
operator-convex `f` with `f 0 ≤ 0`, `f(V⋆XV) ≤ V⋆ f(X) V`. -/
theorem hpj_isometry (f : ℝ → ℝ) (I : Set ℝ) (hf : OperatorConvexOn I f)
    (V X : Matrix (Fin N) (Fin N) ℂ) (hV : star V * V = 1)
    (hX : IsSelfAdjoint X ∧ spectrum ℝ X ⊆ I) (h0 : (0:ℝ) ∈ I) (hf0 : f 0 ≤ 0) :
    cfc f (star V * X * V) ≤ star V * cfc f X * V := by
  sorry -- corollary of `hpj_affine` (take `B` with `star V*V + star B*B = 1`, `Y = 0`).

/-- **HPJ contraction (affine) form** (Effros Thm 2.1, n=2): for `A⋆A + B⋆B = 1`,
`f(A⋆XA + B⋆YB) ≤ A⋆ f(X) A + B⋆ f(Y) B`.  THE keystone theorem (Effros's perspective consumes it). -/
theorem hpj_affine (f : ℝ → ℝ) (I : Set ℝ) (hf : OperatorConvexOn I f)
    (A B X Y : Matrix (Fin N) (Fin N) ℂ) (hAB : star A * A + star B * B = 1)
    (hX : IsSelfAdjoint X ∧ spectrum ℝ X ⊆ I) (hY : IsSelfAdjoint Y ∧ spectrum ℝ Y ⊆ I) :
    cfc f (star A * X * A + star B * Y * B) ≤ star A * cfc f X * A + star B * cfc f Y * B := by
  sorry -- DILATION PROOF (the new theorem).  Sub-lemmas:
        --  S1  ∃ unitary U ∈ Matrix (Fin 2 × Fin N) ... with first block-column (A,B)
        --      (unital column → unitary; `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`
        --       on the `N` orthonormal columns of [A;B] in ℂ^{2N}).  ← HIGHEST RISK.
        --  S2  cfc conj by unitary: `cfc f (U⋆ M U) = U⋆ cfc f M U`  (Unitary.conjStarAlgAut+map_cfc).
        --  S3  cfc block-diagonal: `cfc f (diag a b) = diag (cfc f a) (cfc f b)`  (cfc_map_prod).
        --  S4  2-pt convexity in M₂ from `hf (2*N)`: `f((M+VMV)/2) ≤ (f M + V f(M) V)/2`, V=diag(1,-1).
        --  S5  block arithmetic: `(U⋆ diag(X,Y) U)₁₁ = A⋆XA + B⋆YB`; pinch identity.

/-! ## K3 — Effros Theorem 2.2: the operator perspective is jointly operator convex -/

/-- Operator perspective `P_f(L,R) = R^{1/2} f(R^{-1/2} L R^{-1/2}) R^{1/2}` (`R` strictly positive). -/
def operatorPerspective (f : ℝ → ℝ) (L R : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  CFC.rpow R (1/2) * cfc f (CFC.rpow R (-(1/2)) * L * CFC.rpow R (-(1/2))) * CFC.rpow R (1/2)

/-- **Effros Theorem 2.2**: for operator-convex `f` and commuting positive data, the perspective is
jointly convex.  ~15-line proof from `hpj_affine` with `A=(c•R₁)^{1/2}R^{-1/2}`,
`B=((1-c)•R₂)^{1/2}R^{-1/2}` (`A⋆A+B⋆B=1` by `CFC.conjugate_rpow_neg_one_half`). -/
theorem operatorPerspective_jointly_convex (f : ℝ → ℝ) (I : Set ℝ) (hf : OperatorConvexOn I f)
    (L₁ R₁ L₂ R₂ : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (hc : c ∈ Set.Icc (0:ℝ) 1)
    (hR₁ : R₁.PosDef) (hR₂ : R₂.PosDef) (hcomm₁ : Commute L₁ R₁) (hcomm₂ : Commute L₂ R₂) :
    operatorPerspective f (c • L₁ + (1-c) • L₂) (c • R₁ + (1-c) • R₂)
      ≤ c • operatorPerspective f L₁ R₁ + (1-c) • operatorPerspective f L₂ R₂ := by
  sorry -- K3: hpj_affine + conjugate_rpow_neg_one_half.

/-! ## K4/K5 — realization on the Hilbert–Schmidt space, and relative entropy -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Umegaki relative entropy `S(ρ‖σ) = Tr[ρ (log ρ − log σ)]`. -/
def relEntropy (ρ σ : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (ρ * (cfc Real.log ρ - cfc Real.log σ))).re

/-- Left multiplication `L_ρ(X) = ρ X` on the HS space. -/
def leftMul (ρ : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun X := ρ * X
  map_add' x y := by simp [mul_add]
  map_smul' c x := by simp

/-- Right multiplication `R_σ(X) = X σ` on the HS space. -/
def rightMul (σ : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun X := X * σ
  map_add' x y := by simp [add_mul]
  map_smul' c x := by simp

/-- `L_ρ` and `R_σ` commute. -/
theorem leftMul_rightMul_commute (ρ σ : Matrix n n ℂ) :
    Commute (leftMul ρ) (rightMul σ) := by
  apply LinearMap.ext; intro X
  simp only [leftMul, rightMul, Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc]

/-- **Realization** (Effros Cor 2.1): `S(ρ‖σ) = ⟨vec I, P_f(L_ρ,R_σ) vec I⟩_HS`; for commuting
`L_ρ,R_σ` this collapses to `Tr[ρ(log ρ−log σ)]`.  Placeholder; the carried statement realizes the
RHS on `Matrix (n×n)(n×n) ℂ` via `L_ρ ↔ ρ⊗I`, `R_σ ↔ I⊗σᵀ` (Kronecker), using
`eigenvalues_kronecker_multiset` and `log(ρ⊗I)=(log ρ)⊗I` (again `StarAlgHomClass.map_cfc`). -/
theorem relEntropy_eq_perspective_inner (ρ σ : Matrix n n ℂ) (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    True := trivial

/-! ## K6 — joint convexity of Umegaki relative entropy (issue-#22 core) -/

theorem relEntropy_jointly_convex (ρ₁ σ₁ ρ₂ σ₂ : Matrix n n ℂ) (c : ℝ) (hc : c ∈ Set.Icc (0:ℝ) 1)
    (hρ₁ : ρ₁.PosDef) (hσ₁ : σ₁.PosDef) (hρ₂ : ρ₂.PosDef) (hσ₂ : σ₂.PosDef) :
    relEntropy (c • ρ₁ + (1-c) • ρ₂) (c • σ₁ + (1-c) • σ₂)
      ≤ c * relEntropy ρ₁ σ₁ + (1-c) * relEntropy ρ₂ σ₂ := by
  sorry -- K6: from K3 + K5 + linearity of leftMul/rightMul + monotonicity of ⟨vec I,· vec I⟩.

/-! ## K7 — data-processing inequality (DPI) -/

/-- **DPI / monotonicity under partial trace** (consumable form). -/
theorem monotonicity_relEntropy_partialTrace
    {nA nB : Type*} [Fintype nA] [DecidableEq nA] [Fintype nB] [DecidableEq nB]
    (ρ σ : Matrix (nA × nB) (nA × nB) ℂ) (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    relEntropy (Oseledets.OperatorEntropy.partialTraceRight ρ)
        (Oseledets.OperatorEntropy.partialTraceRight σ) ≤ relEntropy ρ σ := by
  sorry -- K7: K6 (joint convexity) + twirl (partial trace = average of conjugations by a 1-design)
        --     + unitary invariance + relative-entropy additivity.  Mathlib lacks Stinespring/twirl.

end Oseledets.OperatorEntropy.Lieb
end
