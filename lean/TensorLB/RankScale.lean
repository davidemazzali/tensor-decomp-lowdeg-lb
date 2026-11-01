module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform rank constants for total component count

The manuscript's witness estimates use `N = m - 1` background components,
whereas the challenge hypothesis is stated for total rank `m`. These inequalities
account for that difference with one constant uniform in the tensor order.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

noncomputable section

/-- The common rank scale `n^(k/2) D^(k/2-1)`. -/
def rankScale (n D k : ℕ) : ℝ :=
  (n : ℝ) ^ ((k : ℝ) / 2) * (D : ℝ) ^ ((k : ℝ) / 2 - 1)

theorem rankScale_nonneg (n D k : ℕ) : 0 ≤ rankScale n D k := by
  unfold rankScale
  positivity

theorem rankScale_degree_mono (n : ℕ) {d D k : ℕ} (hd : d ≤ D) (hk : 2 ≤ k) :
    rankScale n d k ≤ rankScale n D k := by
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  apply Real.rpow_le_rpow (Nat.cast_nonneg d) (Nat.cast_le.mpr hd)
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

theorem degree_le_rankScale {n D k : ℕ} (hn : 1 ≤ n) (hD : 1 ≤ D)
    (hdegree : D ^ 3 ≤ n) (hk : 2 ≤ k) :
    (D : ℝ) ≤ rankScale n D k := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hDn : D ≤ n := by
    have hpow : D ≤ D ^ 3 := by nlinarith [Nat.mul_self_le_mul_self hD]
    exact hpow.trans hdegree
  have hnpow : (n : ℝ) ≤ (n : ℝ) ^ ((k : ℝ) / 2) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn'
      (show (1 : ℝ) ≤ (k : ℝ) / 2 by linarith)
  have hDpow : (1 : ℝ) ≤ (D : ℝ) ^ ((k : ℝ) / 2 - 1) :=
    Real.one_le_rpow hD' (by linarith)
  calc
    (D : ℝ) ≤ n := Nat.cast_le.mpr hDn
    _ ≤ (n : ℝ) ^ ((k : ℝ) / 2) := hnpow
    _ ≤ rankScale n D k := by
      simpa only [rankScale, mul_one] using
        mul_le_mul_of_nonneg_left hDpow (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- A concrete uniform choice after the coefficient constant `B` is available. -/
def sufficientRankConstant (B : ℝ) : ℝ := max 12 (576 * B)

theorem sufficientRankConstant_pos (B : ℝ) : 0 < sufficientRankConstant B :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- The total-rank hypothesis ensures both background-rank bounds used in
the substitution and geometric-series arguments. -/
theorem background_rank_bounds {n m D k : ℕ} {B : ℝ}
    (hm : 2 ≤ m) (hscale : (D : ℝ) ≤ rankScale n D k)
    (hrank : sufficientRankConstant B * rankScale n D k ≤ (m : ℝ)) :
    6 * D ≤ m - 1 ∧ 288 * B * rankScale n D k ≤ ((m - 1 : ℕ) : ℝ) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hsub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hhalf : (m : ℝ) / 2 ≤ ((m - 1 : ℕ) : ℝ) := by rw [hsub]; linarith
  have h12 := mul_le_mul_of_nonneg_right
    (show (12 : ℝ) ≤ sufficientRankConstant B from le_max_left _ _) (rankScale_nonneg n D k)
  have hB := mul_le_mul_of_nonneg_right
    (show 576 * B ≤ sufficientRankConstant B from le_max_right _ _) (rankScale_nonneg n D k)
  constructor
  · have h : (6 : ℝ) * D ≤ ((m - 1 : ℕ) : ℝ) := by linarith
    exact_mod_cast h
  · linarith

/-- The base of each term in the final norm estimate is at most `1/4`. -/
theorem geometric_base_le_quarter {n m D k d : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hm : 2 ≤ m) (hd : d ≤ D) (hk : 2 ≤ k)
    (hscale : (D : ℝ) ≤ rankScale n D k)
    (hrank : sufficientRankConstant B * rankScale n D k ≤ (m : ℝ)) :
    36 * B * rankScale n d k / (((m - 1 : ℕ) : ℝ) - D + 1) ≤ 1 / 4 := by
  obtain ⟨hD, hbound⟩ := background_rank_bounds hm hscale hrank
  have hD' : (6 : ℝ) * D ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hD
  have hN : (1 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m - 1 by omega)
  have hmono := mul_le_mul_of_nonneg_left (rankScale_degree_mono n hd hk)
    (show 0 ≤ 36 * B by positivity)
  have hpos : 0 < ((m - 1 : ℕ) : ℝ) - D + 1 := by linarith
  apply (div_le_iff₀ hpos).2
  linarith

end

end TensorLB
