module

public import TensorLB.ConnectedTensors

/-!
# The connected-substitution lift bound

The concrete sparse columns have norm bounds `1, 2, 2`. Applying the general
homogeneous substitution theorem gives the factor `5^d`, hence the `6^d`
bound used in the manuscript. No response coefficient estimate is assumed.
-/

set_option autoImplicit false

public section

namespace TensorLB

open scoped BigOperators

variable {n m k d : ℕ}

theorem witnessNorm_substituteConnected_le_five (p : ObservationPolynomial n k)
    (hp : p.IsHomogeneous d) (hN : 6 * d ≤ m - 1) :
    witnessNorm (liftPolynomial (substituteConnected p) : Sample n m → ℝ) ≤
      (5 : ℝ) ^ d * Real.sqrt
        (coefficientEnergy p / (((m - 1).descFactorial d : ℕ) : ℝ)) := by
  have hb := witnessNorm_homogeneous_substitution_le
    (fun j : Fin 3 => j.val + 1) (fun _ => by omega)
    (h := 3) (fun j => by omega) connectedTensor connectedTensor_orthogonal
    connectedTensorBound connectedTensor_bound_nonneg connectedTensor_norm_sq p hp
    (by omega : 2 * (3 * d) ≤ m - 1)
  simpa only [sum_connectedTensor, sum_connectedTensorBound, substituteConnected] using hb

/-- Equation (42), with all substitution estimates discharged. -/
theorem witnessNorm_substituteConnected_le (p : ObservationPolynomial n k)
    (hp : p.IsHomogeneous d) (hN : 6 * d ≤ m - 1) :
    witnessNorm (liftPolynomial (substituteConnected p) : Sample n m → ℝ) ≤
      (6 : ℝ) ^ d * Real.sqrt
        (coefficientEnergy p / (((m - 1).descFactorial d : ℕ) : ℝ)) := by
  apply (witnessNorm_substituteConnected_le_five p hp hN).trans
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) d)
    (Real.sqrt_nonneg _)

end TensorLB
