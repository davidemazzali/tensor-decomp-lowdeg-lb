module

public import TensorLB.ExcessCounting

/-!
# Uniform weighted even-cover bound

The exact support/excess count, factorial ratio, and rank-scale identities
give the combinatorial factor in the coefficient-energy estimate.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

def coverBoundConstant : ℝ := 16384 * (16 * Real.exp 1) ^ 4

theorem coverBoundConstant_pos : 0 < coverBoundConstant := by
  unfold coverBoundConstant
  positivity

theorem coordinate_power_identity {n k d a L : ℕ} (hn : 0 < n)
    (hL : 2 * L + a = k * d) :
    (n : ℝ) ^ L = (n : ℝ) ^ (-(a : ℝ) / 2) * ((n : ℝ) ^ ((k : ℝ) / 2)) ^ d := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.rpow_mul_natCast hn'.le, ← Real.rpow_add hn', ← Real.rpow_natCast]
  congr 1
  have hL' : 2 * (L : ℝ) + a = k * d := by exact_mod_cast hL
  linarith

theorem weightedSlotCount_div_factorial_le {n k d L : ℕ} (A : Finset (Fin n))
    (hn : 0 < n) (hk : k = 3 ∨ k = 4) (hd : 1 ≤ d) (hA : A.Nonempty)
    (ha : A.card ≤ 4) (hL : 2 * L + A.card = k * d) :
    weightedSlotCount n (k * d) A / d.factorial ≤
      (n : ℝ) ^ (-((A.card : ℝ) / 2)) * (coverBoundConstant * rankScale n d k) ^ d *
        Real.exp (4 * (d : ℝ) ^ 4 / n) := by
  have hkd : k * d ≤ 4 * d := Nat.mul_le_mul_right d (by omega)
  have hc : 1 ≤ 16 * Real.exp 1 := by
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  have hcp : (16 * Real.exp 1) ^ (k * d) ≤ ((16 * Real.exp 1) ^ 4) ^ d := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hc hkd
  have hf := tensor_factorial_ratio_le hk hd ha hL
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (Nat.zero_lt_of_lt hd)
  calc
    _ ≤ (((k * d).factorial : ℝ) * (16 * Real.exp 1) ^ (k * d) *
        ((n : ℝ) ^ L / L.factorial) * Real.exp (4 * (d : ℝ) ^ 4 / n)) / d.factorial :=
      div_le_div_of_nonneg_right (weightedSlotCount_le_exp A hn hA hL.symm hkd) (by positivity)
    _ = (((k * d).factorial : ℝ) / ((d.factorial : ℝ) * L.factorial)) *
        (16 * Real.exp 1) ^ (k * d) * (n : ℝ) ^ L * Real.exp (4 * (d : ℝ) ^ 4 / n) := by ring
    _ ≤ ((16384 : ℝ) ^ d * (d : ℝ) ^ (((k : ℝ) / 2 - 1) * d)) *
        ((16 * Real.exp 1) ^ 4) ^ d * (n : ℝ) ^ L * Real.exp (4 * (d : ℝ) ^ 4 / n) := by
      gcongr
    _ = _ := by
      rw [coordinate_power_identity hn hL, Real.rpow_mul_natCast hdpos.le]
      simp only [coverBoundConstant, rankScale, mul_pow, neg_div]
      ring

theorem weightedCoverCount_div_factorial_le {n k d L : ℕ} (A : Finset (Fin n))
    (hn : 0 < n) (hk : k = 3 ∨ k = 4) (hd : 1 ≤ d) (hA : A.Nonempty)
    (ha : A.card ≤ 4) (hL : 2 * L + A.card = k * d) :
    weightedCoverCount n k d A / d.factorial ≤
      (n : ℝ) ^ (-((A.card : ℝ) / 2)) * (coverBoundConstant * rankScale n d k) ^ d *
        Real.exp (4 * (d : ℝ) ^ 4 / n) :=
  (div_le_div_of_nonneg_right (weightedCoverCount_le_weightedSlotCount A) (by positivity)).trans
    (weightedSlotCount_div_factorial_le A hn hk hd hA ha hL)

end

end TensorLB
