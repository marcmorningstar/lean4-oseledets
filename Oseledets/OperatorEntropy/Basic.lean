import Mathlib

open Matrix Real
open scoped ComplexOrder Kronecker

noncomputable section

namespace Oseledets.OperatorEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite-dimensional density matrix over `ℂ`: a positive-semidefinite, unit-trace matrix. -/
structure DensityMatrix (n : Type*) [Fintype n] [DecidableEq n] where
  val : Matrix n n ℂ
  posSemidef : val.PosSemidef
  trace_one : val.trace = 1

/-- The von Neumann entropy `S(ρ) = ∑ᵢ negMulLog(λᵢ)` over the (real) eigenvalues of `ρ`. -/
def vonNeumannEntropy (ρ : DensityMatrix n) : ℝ :=
  ∑ i, Real.negMulLog (ρ.posSemidef.1.eigenvalues i)

/-- The eigenvalues of a density matrix are nonnegative. -/
theorem DensityMatrix.eigenvalues_nonneg (ρ : DensityMatrix n) (i : n) :
    0 ≤ ρ.posSemidef.1.eigenvalues i :=
  ρ.posSemidef.eigenvalues_nonneg i

/-- The eigenvalues of a density matrix sum to `1` (its trace). -/
theorem DensityMatrix.sum_eigenvalues_eq_one (ρ : DensityMatrix n) :
    ∑ i, ρ.posSemidef.1.eigenvalues i = 1 := by
  have h := ρ.posSemidef.1.trace_eq_sum_eigenvalues
  rw [ρ.trace_one] at h
  have h2 : ((∑ i, ρ.posSemidef.1.eigenvalues i : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simpa using h.symm
  exact_mod_cast h2

/-- Each eigenvalue of a density matrix is at most `1`. -/
theorem DensityMatrix.eigenvalues_le_one (ρ : DensityMatrix n) (i : n) :
    ρ.posSemidef.1.eigenvalues i ≤ 1 := by
  rw [← ρ.sum_eigenvalues_eq_one]
  exact Finset.single_le_sum (fun j _ => ρ.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- The von Neumann entropy of a density matrix is nonnegative. -/
theorem vonNeumannEntropy_nonneg (ρ : DensityMatrix n) : 0 ≤ vonNeumannEntropy ρ :=
  Finset.sum_nonneg fun i _ =>
    Real.negMulLog_nonneg (ρ.eigenvalues_nonneg i) (ρ.eigenvalues_le_one i)

end Oseledets.OperatorEntropy
