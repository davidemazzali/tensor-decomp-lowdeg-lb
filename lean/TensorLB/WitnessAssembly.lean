module

public import TensorLB.Observations
public import TensorLB.WitnessNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Assembling the homogeneous witness bounds

Triangle inequalities and a finite geometric sum give the final second-moment
bound. The summands may overlap in hidden degree and need not be orthogonal.
-/

set_option autoImplicit false

public section

namespace TensorLB

open scoped BigOperators

variable {n m k D : ℕ} {τ : ℝ}

theorem sum_half_pow_succ (D : ℕ) :
    (∑ d ∈ Finset.range D, (1 / 2 : ℝ) ^ (d + 1)) = 1 - (1 / 2 : ℝ) ^ D := by
  induction D with
  | zero => simp
  | succ D ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem witnessNorm_sum_le_of_geometric (W : ℕ → Sample n m → ℝ)
    {r : ℝ} (hr : 0 ≤ r)
    (hW : ∀ d < D, witnessNorm (W (d + 1)) ≤ r * (1 / 2 : ℝ) ^ (d + 1)) :
    witnessNorm (fun ω => ∑ d ∈ Finset.range D, W (d + 1) ω) ≤ r := by
  calc
    _ ≤ ∑ d ∈ Finset.range D, witnessNorm (W (d + 1)) := witnessNorm_finset_sum_le _ _
    _ ≤ ∑ d ∈ Finset.range D, r * (1 / 2 : ℝ) ^ (d + 1) :=
      Finset.sum_le_sum (fun d hd => hW d (Finset.mem_range.mp hd))
    _ = r * (1 - (1 / 2 : ℝ) ^ D) := by rw [← Finset.mul_sum, sum_half_pow_succ]
    _ ≤ r := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) D]

/-- Both estimation conclusions follow from geometrically decreasing norms of
the witness summands and moment matching of their sum. -/
theorem bounds_of_geometric_witness_sum (W : ℕ → Sample n m → ℝ)
    (A : Finset (Fin n)) {r : ℝ} (hr : 0 ≤ r)
    (hW : ∀ d < D, witnessNorm (W (d + 1)) ≤ r * (1 / 2 : ℝ) ^ (d + 1))
    (hmatch : IsReducedMomentMatchingWitness n m k D τ A
      (fun ω => ∑ d ∈ Finset.range D, W (d + 1) ω)) :
    correlation n m k D τ A ^ 2 ≤ r ^ 2 ∧ 1 - r ^ 2 ≤ mmse n m k D τ A := by
  apply bounds_of_reduced_witness hmatch
  exact (witnessNorm_le_iff _ hr).mp (witnessNorm_sum_le_of_geometric W hr hW)

/-- The target exponent in the specification is the square of the norm scale
`n^(-|A|/4)` appearing in the witness construction. -/
theorem target_norm_scale_sq (n a : ℕ) :
    Real.rpow (n : ℝ) (-((a : ℝ) / 4)) ^ 2 = Real.rpow (n : ℝ) (-((a : ℝ) / 2)) := by
  calc
    _ = Real.rpow (n : ℝ) (-((a : ℝ) / 4) * (2 : ℕ)) :=
      (Real.rpow_mul_natCast (Nat.cast_nonneg n) (-((a : ℝ) / 4)) 2).symm
    _ = _ := congrArg (Real.rpow (n : ℝ)) (by norm_num; ring)

/-- The conclusion of the main theorem once the homogeneous witness estimates
and the moment-matching construction have been supplied. -/
theorem main_bounds_of_geometric_witness (W : ℕ → Sample n m → ℝ)
    (A : Finset (Fin n))
    (hW : ∀ d < D, witnessNorm (W (d + 1)) ≤
      Real.rpow (n : ℝ) (-((A.card : ℝ) / 4)) * (1 / 2 : ℝ) ^ (d + 1))
    (hmatch : IsReducedMomentMatchingWitness n m k D τ A
      (fun ω => ∑ d ∈ Finset.range D, W (d + 1) ω)) :
    correlation n m k D τ A ^ 2 ≤ Real.rpow (n : ℝ) (-((A.card : ℝ) / 2)) ∧
      1 - Real.rpow (n : ℝ) (-((A.card : ℝ) / 2)) ≤ mmse n m k D τ A := by
  have h := bounds_of_geometric_witness_sum W A
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) hW hmatch
  change correlation n m k D τ A ^ 2 ≤ Real.rpow (n : ℝ) (-((A.card : ℝ) / 4)) ^ 2 ∧
    1 - Real.rpow (n : ℝ) (-((A.card : ℝ) / 4)) ^ 2 ≤ mmse n m k D τ A at h
  rwa [target_norm_scale_sq] at h

end TensorLB
