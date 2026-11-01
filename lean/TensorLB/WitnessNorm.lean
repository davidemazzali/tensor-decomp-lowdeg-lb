module

public import TensorLB.ExpectationSum

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite second-moment norms

Triangle inequalities allow witness terms of different input degrees to
overlap. Orthogonality is not assumed when assembling the final witness.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators

noncomputable section

variable {n m : ℕ} {ι : Type*}

/-- The `L²` norm under the finite uniform sample law. -/
def witnessNorm (f : Sample n m → ℝ) : ℝ :=
  Real.sqrt (expectation n m (fun ω => f ω ^ 2))

theorem witnessNorm_nonneg (f : Sample n m → ℝ) : 0 ≤ witnessNorm f := Real.sqrt_nonneg _

@[simp] theorem witnessNorm_sq (f : Sample n m → ℝ) :
    witnessNorm f ^ 2 = expectation n m (fun ω => f ω ^ 2) :=
  Real.sq_sqrt (expectation_sq_nonneg f)

@[simp] theorem witnessNorm_zero : witnessNorm (fun _ : Sample n m => 0) = 0 := by
  simp [witnessNorm]

theorem expectation_mul_le_witnessNorm (f g : Sample n m → ℝ) :
    expectation n m (fun ω => f ω * g ω) ≤ witnessNorm f * witnessNorm g := by
  have h := Real.le_sqrt_of_sq_le (expectation_mul_sq_le f g)
  simpa only [Real.sqrt_mul (expectation_sq_nonneg f), witnessNorm] using h

theorem witnessNorm_add_le (f g : Sample n m → ℝ) :
    witnessNorm (fun ω => f ω + g ω) ≤ witnessNorm f + witnessNorm g := by
  apply (Real.sqrt_le_iff).2
  refine ⟨add_nonneg (witnessNorm_nonneg f) (witnessNorm_nonneg g), ?_⟩
  have h := expectation_mul_le_witnessNorm f g
  have hex : expectation n m (fun ω => (f ω + g ω) ^ 2) =
      expectation n m (fun ω => f ω ^ 2) +
        2 * expectation n m (fun ω => f ω * g ω) +
          expectation n m (fun ω => g ω ^ 2) := by
    calc
      _ = expectation n m (fun ω => f ω ^ 2 + 2 * (f ω * g ω) + g ω ^ 2) :=
        expectation_congr (fun _ => by ring)
      _ = _ := by rw [expectation_add, expectation_add, expectation_const_mul]
  rw [hex, ← witnessNorm_sq f, ← witnessNorm_sq g]
  nlinarith

theorem witnessNorm_finset_sum_le (s : Finset ι) (f : ι → Sample n m → ℝ) :
    witnessNorm (fun ω => ∑ i ∈ s, f i ω) ≤ ∑ i ∈ s, witnessNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (witnessNorm_add_le (f i) (fun ω => ∑ j ∈ s, f j ω)).trans (add_le_add le_rfl ih)

theorem witnessNorm_const_mul (c : ℝ) (f : Sample n m → ℝ) :
    witnessNorm (fun ω => c * f ω) = |c| * witnessNorm f := by
  unfold witnessNorm
  simp only [mul_pow, expectation_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- A second-moment bound expressed as a norm bound, with its necessary sign condition. -/
theorem witnessNorm_le_iff (f : Sample n m → ℝ) {b : ℝ} (hb : 0 ≤ b) :
    witnessNorm f ≤ b ↔ expectation n m (fun ω => f ω ^ 2) ≤ b ^ 2 := by
  exact Real.sqrt_le_iff.trans (and_iff_right hb)

end

end TensorLB
