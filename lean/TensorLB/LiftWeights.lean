module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar bounds for lift weights and coefficient energies

The factorial-to-falling-factorial ratio decreases in the degree range used
by the substitution argument. The only use of `D³ ≤ n` in the coefficient
estimate is also isolated here as an exponential absorption inequality.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

noncomputable section

/-- Squared lift normalization for an order-`d` symmetric tensor. -/
def liftWeight (N d : ℕ) : ℝ := (d.factorial : ℝ) / (N.descFactorial d : ℝ)

theorem liftWeight_nonneg (N d : ℕ) : 0 ≤ liftWeight N d := by
  unfold liftWeight
  positivity

theorem liftWeight_succ (N d : ℕ) :
    liftWeight N (d + 1) = ((d + 1 : ℕ) : ℝ) / ((N - d : ℕ) : ℝ) * liftWeight N d := by
  simp only [liftWeight, Nat.factorial_succ, Nat.descFactorial_succ, Nat.cast_mul,
    div_mul_div_comm]

theorem liftWeight_succ_le {N d : ℕ} (h : 2 * d + 1 ≤ N) :
    liftWeight N (d + 1) ≤ liftWeight N d := by
  have hpos : (0 : ℝ) < ((N - d : ℕ) : ℝ) := by exact_mod_cast (show 0 < N - d by omega)
  have hle : ((d + 1 : ℕ) : ℝ) ≤ ((N - d : ℕ) : ℝ) := by
    exact_mod_cast (show d + 1 ≤ N - d by omega)
  rw [liftWeight_succ]
  have hr : ((d + 1 : ℕ) : ℝ) / ((N - d : ℕ) : ℝ) ≤ 1 := (div_le_one₀ hpos).2 hle
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hr (liftWeight_nonneg N d)

/-- The normalization decreases from input degree `d` through any hidden
degree `r ≤ N/2`, covering every substitution when `N ≥ 6D`. -/
theorem liftWeight_le_of_le {N d r : ℕ} (hdr : d ≤ r) (hN : 2 * r ≤ N) :
    liftWeight N r ≤ liftWeight N d := by
  induction r, hdr using Nat.le_induction with
  | base => exact le_rfl
  | succ r hdr ih =>
    exact (liftWeight_succ_le (by omega)).trans (ih (by omega))

/-- Uniform lower bound for a falling factorial over the degree range. -/
theorem pow_le_descFactorial {N D d : ℕ} (hd : d ≤ D) (hD : D ≤ N) :
    ((N : ℝ) - D + 1) ^ d ≤ (N.descFactorial d : ℝ) := by
  have hnat : (N + 1 - D) ^ d ≤ N.descFactorial d :=
    (Nat.pow_le_pow_left (show N + 1 - D ≤ N + 1 - d by omega) d).trans
      (Nat.pow_sub_le_descFactorial N d)
  have hcast : ((N + 1 - D : ℕ) : ℝ) = (N : ℝ) - D + 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    ring
  have hreal : ((N + 1 - D : ℕ) : ℝ) ^ d ≤ (N.descFactorial d : ℝ) := by
    exact_mod_cast hnat
  rwa [hcast] at hreal

/-- Absorb the correction `exp(4 d⁴/n)` into an exponential-in-degree constant. -/
theorem exp_degree_correction_le {n D d : ℕ} (hn : 0 < n) (hd : d ≤ D)
    (hD : D ^ 3 ≤ n) :
    Real.exp (4 * (d : ℝ) ^ 4 / n) ≤ Real.exp 4 ^ d := by
  have hc : (d : ℝ) ^ 3 ≤ n := by
    exact_mod_cast (Nat.pow_le_pow_left hd 3).trans hD
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hd' : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have he : 4 * (d : ℝ) ^ 4 / n ≤ (d : ℝ) * 4 := by
    apply (div_le_iff₀ hn').2
    nlinarith [mul_le_mul_of_nonneg_left hc hd']
  rw [← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr he

end

end TensorLB
