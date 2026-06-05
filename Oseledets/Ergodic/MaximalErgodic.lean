import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The maximal ergodic inequality (Hopf / Garsia)

The maximal ergodic inequality is the analytic gate to the pointwise (Birkhoff)
ergodic theorem (layer `L1.1` / milestone `M1`). It is **absent** from Mathlib.

For an integrable `f` and a measure-preserving `T`, on the set where some forward
Birkhoff sum is positive the integral of `f` is nonnegative:
`0 ≤ ∫_{ {x | ∃ n, 0 < birkhoffSum T f (n+1) x} } f dμ`.

Stated here with `sorry`; proved in the maximal-ergodic-inequality phase via Garsia's
short combinatorial argument.
-/

open MeasureTheory Filter

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-- **Maximal ergodic inequality** (Hopf/Garsia). For a measure-preserving `T` and an
integrable `f`, the integral of `f` over the set where some forward Birkhoff partial
sum is positive is nonnegative. -/
theorem setIntegral_birkhoffSum_pos_nonneg
    (hT : MeasurePreserving T μ μ) {f : X → ℝ} (hf : Integrable f μ) :
    0 ≤ ∫ x in {x | ∃ n : ℕ, 0 < birkhoffSum T f (n + 1) x}, f x ∂μ := by
  sorry

end Oseledets
