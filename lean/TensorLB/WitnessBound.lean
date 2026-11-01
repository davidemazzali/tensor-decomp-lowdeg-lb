module

public import TensorLB.Estimation

import Mathlib.Tactic.Ring

/-!
# Moment-matching witnesses bound low-degree estimation

This is the final probabilistic reduction in the proof of manuscript Theorem
`thm:main`. A witness is any function of the underlying signs; it need not be
observable or polynomial. Matching its moments against all degree-restricted
estimators bounds both correlation and mean squared error by its second moment.
The analytic construction of such a witness is a separate proof obligation.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

noncomputable section

/-- Equation `eq:moment-matching`, stated directly for full tensor polynomials. -/
def IsMomentMatchingWitness (n m k ℓ : ℕ) (τ : ℝ) (A : Finset (Fin n))
    (W : Sample n m → ℝ) : Prop :=
  ∀ p : TensorPolynomial n k, p.totalDegree ≤ ℓ →
    expectation n m (fun ω => W ω * estimator n m k τ p ω) =
      expectation n m (fun ω => target n m A ω * estimator n m k τ p ω)

variable {n m k ℓ : ℕ} {τ : ℝ} {A : Finset (Fin n)} {W : Sample n m → ℝ}

/-- Cauchy–Schwarz bounds each normalized correlation by the witness norm. -/
theorem correlation_le_sqrt_of_witness
    (hW : IsMomentMatchingWitness n m k ℓ τ A W) :
    correlation n m k ℓ τ A ≤ Real.sqrt (expectation n m (fun ω => W ω ^ 2)) := by
  apply correlation_le_of_forall
  intro p hp hpos
  rw [← hW p hp]
  apply (div_le_iff₀ (Real.sqrt_pos.2 hpos)).2
  have hcs := expectation_mul_sq_le W (estimator n m k τ p)
  have hle := Real.le_sqrt_of_sq_le hcs
  rwa [Real.sqrt_mul (expectation_sq_nonneg W)] at hle

/-- The square of the maximal correlation is at most the witness second moment. -/
theorem correlation_sq_le_of_witness
    (hW : IsMomentMatchingWitness n m k ℓ τ A W) :
    correlation n m k ℓ τ A ^ 2 ≤ expectation n m (fun ω => W ω ^ 2) := by
  exact (Real.le_sqrt (correlation_nonneg (n := n) (m := m) (k := k)
    (ℓ := ℓ) (τ := τ) (A := A)) (expectation_sq_nonneg W)).1
    (correlation_le_sqrt_of_witness hW)

/-- Completing the square using moment matching, with no positivity assumption
on the estimator's second moment. This also covers the zero estimator. -/
theorem expectation_sq_sub_target_eq_of_witness
    (hW : IsMomentMatchingWitness n m k ℓ τ A W)
    (p : TensorPolynomial n k) (hp : p.totalDegree ≤ ℓ) :
    expectation n m (fun ω => (estimator n m k τ p ω - target n m A ω) ^ 2) =
      1 - expectation n m (fun ω => W ω ^ 2) +
        expectation n m (fun ω => (estimator n m k τ p ω - W ω) ^ 2) := by
  have expand (f g : Sample n m → ℝ) :
      expectation n m (fun ω => (f ω - g ω) ^ 2) =
        expectation n m (fun ω => f ω ^ 2) -
          2 * expectation n m (fun ω => g ω * f ω) +
            expectation n m (fun ω => g ω ^ 2) := by
    calc
      _ = expectation n m (fun ω => f ω ^ 2 - 2 * (g ω * f ω) + g ω ^ 2) :=
        expectation_congr (fun ω => by ring)
      _ = _ := by rw [expectation_add, expectation_sub, expectation_const_mul]
  rw [expand, expand, expectation_target_sq, hW p hp]
  ring

/-- A witness gives the MMSE lower bound directly, without requiring attainment
of either optimization or the exact MMSE/correlation identity. -/
theorem one_sub_expectation_sq_le_mmse_of_witness
    (hW : IsMomentMatchingWitness n m k ℓ τ A W) :
    1 - expectation n m (fun ω => W ω ^ 2) ≤ mmse n m k ℓ τ A := by
  apply le_mmse_of_forall
  intro p hp
  rw [expectation_sq_sub_target_eq_of_witness hW p hp]
  exact le_add_of_nonneg_right
    (expectation_sq_nonneg (fun ω => estimator n m k τ p ω - W ω))

/-- A moment-matching witness of second moment at most `b` proves both desired
estimation bounds with the same `b`. No additional sign assumption on `b` is
needed: it follows from the second-moment bound. -/
theorem bounds_of_witness (hW : IsMomentMatchingWitness n m k ℓ τ A W)
    {b : ℝ} (hbound : expectation n m (fun ω => W ω ^ 2) ≤ b) :
    correlation n m k ℓ τ A ^ 2 ≤ b ∧ 1 - b ≤ mmse n m k ℓ τ A := by
  exact ⟨(correlation_sq_le_of_witness hW).trans hbound,
    (sub_le_sub_left hbound 1).trans (one_sub_expectation_sq_le_mmse_of_witness hW)⟩

end

end TensorLB
