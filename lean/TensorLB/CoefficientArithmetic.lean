module

public import TensorLB.RankScale
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Scalar estimates for the weighted incidence count

These estimates control the factorial weights of repeated coordinates and the
exponential correction in the coefficient-energy estimate.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators

theorem nat_sq_le_four_pow (u : ℕ) : (u : ℝ) ^ 2 ≤ 4 ^ u := by
  have h : (u : ℝ) ≤ 2 ^ u := by exact_mod_cast Nat.le_of_lt (Nat.lt_two_pow_self (n := u))
  calc
    (u : ℝ) ^ 2 ≤ (2 ^ u) ^ 2 := pow_le_pow_left₀ (by positivity) h 2
    _ = (4 : ℝ) ^ u := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num

/-- Equation (27), with the same absolute constant as in the manuscript. -/
theorem incidence_factorial_weight_le {u b e d : ℕ}
    (hb : 1 ≤ b) (hb2 : b ≤ 2) (hu : u = b + 2 * e) (hud : u ≤ 4 * d) :
    (u : ℝ) ^ (2 * u) / u.factorial ≤
      (16 * Real.exp 1) ^ u * (d : ℝ) ^ (2 * e) := by
  have hu1 : 1 ≤ u := by omega
  have hu1' : (1 : ℝ) ≤ u := by exact_mod_cast hu1
  have hud' : (u : ℝ) ≤ 4 * d := by exact_mod_cast hud
  have he : 2 * e ≤ u := by omega
  have hp : (u : ℝ) ^ u ≤ 16 ^ u * (d : ℝ) ^ (2 * e) := by
    calc
      (u : ℝ) ^ u = (u : ℝ) ^ b * (u : ℝ) ^ (2 * e) := by rw [← pow_add, ← hu]
      _ ≤ (4 : ℝ) ^ u * ((4 : ℝ) ^ (2 * e) * (d : ℝ) ^ (2 * e)) := by
        apply mul_le_mul
        · exact (pow_le_pow_right₀ hu1' hb2).trans (nat_sq_le_four_pow u)
        · simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hud' (2 * e)
        · positivity
        · positivity
      _ ≤ (4 : ℝ) ^ u * ((4 : ℝ) ^ u * (d : ℝ) ^ (2 * e)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) he) (by positivity))
          (by positivity)
      _ = _ := by rw [← mul_assoc, ← mul_pow]; norm_num
  calc
    (u : ℝ) ^ (2 * u) / u.factorial =
        (u : ℝ) ^ u * ((u : ℝ) ^ u / u.factorial) := by
      rw [two_mul, pow_add]; ring
    _ ≤ (16 ^ u * (d : ℝ) ^ (2 * e)) * Real.exp u := by
      exact mul_le_mul hp (Real.pow_div_factorial_le_exp (u : ℝ) (by positivity) u)
        (by positivity) (by positivity)
    _ = _ := by
      rw [show Real.exp (u : ℝ) = Real.exp 1 ^ u by simp, mul_pow]
      ring

/-- The factorial/choose factor in equation (29). -/
theorem factorial_choose_le (L a e : ℕ) (he : e ≤ L) :
    (L.factorial : ℝ) / (L - e).factorial * ((L + a - 1).choose e : ℝ) ≤
      ((L : ℝ) * (L + a - 1 : ℕ)) ^ e / e.factorial := by
  have hf : (0 : ℝ) < ((L - e).factorial : ℝ) := by positivity
  have hg : (0 : ℝ) < (e.factorial : ℝ) := by positivity
  have hfac : (L.factorial : ℝ) / (L - e).factorial = L.descFactorial e := by
    apply (div_eq_iff (ne_of_gt hf)).mpr
    exact_mod_cast (Nat.factorial_mul_descFactorial he).symm.trans (Nat.mul_comm _ _)
  have hchoose : ((L + a - 1).choose e : ℝ) =
      ((L + a - 1).descFactorial e : ℝ) / e.factorial := by
    apply (eq_div_iff (ne_of_gt hg)).mpr
    exact_mod_cast (Nat.mul_comm _ _).trans
      (Nat.descFactorial_eq_factorial_mul_choose (L + a - 1) e).symm
  rw [hfac, hchoose, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (le_of_lt hg)
  rw [mul_pow]
  exact mul_le_mul (by exact_mod_cast Nat.descFactorial_le_pow L e)
    (by exact_mod_cast Nat.descFactorial_le_pow (L + a - 1) e) (by positivity) (by positivity)

/-- Sum the excess-incidence parameter, as in equations (28)--(30). -/
theorem excess_incidence_sum_le (L a : ℕ) {N w : ℝ} (hN : 0 < N) (hw : 0 ≤ w) :
    (∑ e ∈ Finset.range (L + 1), N ^ (L - e) / (L - e).factorial *
      ((L + a - 1).choose e : ℝ) * w ^ e) ≤
      N ^ L / L.factorial * Real.exp ((L : ℝ) * (L + a - 1 : ℕ) * w / N) := by
  have hL : (L.factorial : ℝ) ≠ 0 := by positivity
  calc
    _ ≤ ∑ e ∈ Finset.range (L + 1), N ^ L / L.factorial *
        (((L : ℝ) * (L + a - 1 : ℕ) * w / N) ^ e / e.factorial) := by
      apply Finset.sum_le_sum
      intro e he
      have heL : e ≤ L := Nat.le_of_lt_succ (Finset.mem_range.mp he)
      have hLe : ((L - e).factorial : ℝ) ≠ 0 := by positivity
      have hep : (e.factorial : ℝ) ≠ 0 := by positivity
      have hpow : N ^ L = N ^ (L - e) * N ^ e := by rw [← pow_add, Nat.sub_add_cancel heL]
      calc
        _ = (N ^ L / L.factorial) *
            (((L.factorial : ℝ) / (L - e).factorial *
              ((L + a - 1).choose e : ℝ)) * w ^ e / N ^ e) := by
          rw [hpow]
          field_simp
        _ ≤ (N ^ L / L.factorial) *
            ((((L : ℝ) * (L + a - 1 : ℕ)) ^ e / e.factorial) * w ^ e / N ^ e) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (factorial_choose_le L a e heL) (by positivity)
        _ = _ := by rw [div_pow, mul_pow]; ring
    _ = N ^ L / L.factorial * ∑ e ∈ Finset.range (L + 1),
        ((L : ℝ) * (L + a - 1 : ℕ) * w / N) ^ e / e.factorial :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.sum_le_exp_of_nonneg (by positivity) _) (by positivity)

/-- The correction exponent is at most `4 d⁴ / n` for every allowed target. -/
theorem incidence_excess_scale_le {L a d : ℕ} (ha : 1 ≤ a)
    (hslots : 2 * L + a ≤ 4 * d) :
    (L : ℝ) * (L + a - 1 : ℕ) * (d : ℝ) ^ 2 ≤ 4 * (d : ℝ) ^ 4 := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hslots' : 2 * (L : ℝ) + a ≤ 4 * d := by exact_mod_cast hslots
  have hsub : ((L + a - 1 : ℕ) : ℝ) = L + a - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  rw [hsub]
  have hquad : (L : ℝ) * (L + a - 1) ≤ 4 * (d : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (2 * (L : ℝ) + a - 4 * d),
      mul_nonneg (show 0 ≤ 4 * (d : ℝ) - (2 * L + a) by linarith)
        (show 0 ≤ 4 * (d : ℝ) + (2 * L + a) by positivity), sq_nonneg (a : ℝ)]
  nlinarith [mul_le_mul_of_nonneg_right hquad (sq_nonneg (d : ℝ))]

/-- A binomial coefficient and a descending factorial suffice for the
factorial ratio; no asymptotic factorial estimate is needed. -/
theorem factorial_ratio_le {s d L : ℕ} (hdL : d + L ≤ s) :
    (s.factorial : ℝ) / ((d.factorial : ℝ) * L.factorial) ≤
      2 ^ s * (s : ℝ) ^ (s - d - L) := by
  have hd : d ≤ s := by omega
  have hL : L ≤ s - d := by omega
  have hf : (s.factorial : ℝ) =
      (s.choose d : ℝ) * d.factorial * L.factorial * (s - d).descFactorial (s - d - L) := by
    have h1 := Nat.choose_mul_factorial_mul_factorial hd
    have h2 := Nat.factorial_mul_descFactorial (Nat.sub_le (s - d) L)
    rw [Nat.sub_sub_self hL] at h2
    rw [← h2] at h1
    exact_mod_cast h1.symm.trans (by ring)
  have hd0 : (d.factorial : ℝ) ≠ 0 := by positivity
  have hL0 : (L.factorial : ℝ) ≠ 0 := by positivity
  calc
    _ = (s.choose d : ℝ) * (s - d).descFactorial (s - d - L) := by rw [hf]; field_simp
    _ ≤ 2 ^ s * (s : ℝ) ^ (s - d - L) := by
      apply mul_le_mul
      · exact_mod_cast Nat.choose_le_two_pow s d
      · exact_mod_cast (Nat.descFactorial_le_pow (s - d) (s - d - L)).trans
          (Nat.pow_le_pow_left (Nat.sub_le s d) _)
      · positivity
      · positivity

/-- Equation (31), with a uniform explicit exponential constant. -/
theorem tensor_factorial_ratio_le {k d a L : ℕ} (hk : k = 3 ∨ k = 4)
    (hd : 1 ≤ d) (ha : a ≤ 4) (hL : 2 * L + a = k * d) :
    ((k * d).factorial : ℝ) / ((d.factorial : ℝ) * L.factorial) ≤
      (16384 : ℝ) ^ d * (d : ℝ) ^ (((k : ℝ) / 2 - 1) * d) := by
  have hk2 : 2 ≤ k := by omega
  have hk4 : k ≤ 4 := by omega
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by positivity
  have hkd : k * d ≤ 4 * d := Nat.mul_le_mul_right d hk4
  have hdL : d + L ≤ k * d := by nlinarith
  have hr : k * d - d - L ≤ 4 * d := by omega
  have hre : ((k * d - d - L : ℕ) : ℝ) = ((k : ℝ) / 2 - 1) * d + (a : ℝ) / 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_mul]
    have hL' : 2 * (L : ℝ) + a = k * d := by exact_mod_cast hL
    linarith
  have hdextra : (d : ℝ) ^ ((a : ℝ) / 2) ≤ 4 ^ d := by
    have ha' : (a : ℝ) ≤ 4 := by exact_mod_cast ha
    apply (Real.rpow_le_rpow_of_exponent_le hd' (show (a : ℝ) / 2 ≤ 2 by linarith)).trans
    simpa only [Real.rpow_two] using nat_sq_le_four_pow d
  calc
    _ ≤ 2 ^ (k * d) * ((k * d : ℕ) : ℝ) ^ (k * d - d - L) := factorial_ratio_le hdL
    _ ≤ (2 : ℝ) ^ (4 * d) * ((4 : ℝ) * d) ^ (k * d - d - L) := by
      apply mul_le_mul
      · exact pow_le_pow_right₀ (by norm_num) hkd
      · apply pow_le_pow_left₀ (by positivity)
        exact_mod_cast hkd
      · positivity
      · positivity
    _ = (2 : ℝ) ^ (4 * d) * (4 ^ (k * d - d - L) *
        ((d : ℝ) ^ (((k : ℝ) / 2 - 1) * d) * (d : ℝ) ^ ((a : ℝ) / 2))) := by
      rw [mul_pow, ← Real.rpow_natCast (d : ℝ), hre, Real.rpow_add hdpos]
    _ ≤ (2 : ℝ) ^ (4 * d) * (4 ^ (4 * d) *
        ((d : ℝ) ^ (((k : ℝ) / 2 - 1) * d) * 4 ^ d)) := by
      gcongr
      norm_num
    _ = _ := by
      rw [pow_mul, pow_mul]
      norm_num only [show (2 : ℝ) ^ 4 = 16 by norm_num,
        show (4 : ℝ) ^ 4 = 256 by norm_num]
      rw [show (16384 : ℝ) = 16 * 256 * 4 by norm_num, mul_pow, mul_pow]
      ring

theorem exp_coefficient_correction_le {n d : ℕ} (hn : 0 < n) (hdeg : d ^ 3 ≤ n) :
    Real.exp (4 * (d : ℝ) ^ 4 / n) ≤ (Real.exp 4) ^ d := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hdeg' : (d : ℝ) ^ 3 ≤ n := by exact_mod_cast hdeg
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ hn').mpr
  nlinarith [mul_le_mul_of_nonneg_right hdeg' (show 0 ≤ (4 : ℝ) * d by positivity)]

/-- Absorb the finite-dimensional correction using exactly the degree
restriction in the challenge. -/
theorem absorb_energy_correction {n d k : ℕ} {B a E : ℝ}
    (hn : 0 < n) (hdeg : d ^ 3 ≤ n) (hB : 0 ≤ B)
    (hE : E ≤ Real.rpow (n : ℝ) (-a / 2) * (B * rankScale n d k) ^ d *
      Real.exp (4 * (d : ℝ) ^ 4 / n)) :
    E ≤ Real.rpow (n : ℝ) (-a / 2) *
      ((B * Real.exp 4) * rankScale n d k) ^ d := by
  have hs := rankScale_nonneg n d k
  calc
    E ≤ _ := hE
    _ ≤ Real.rpow (n : ℝ) (-a / 2) * (B * rankScale n d k) ^ d *
        (Real.exp 4) ^ d := mul_le_mul_of_nonneg_left
          (exp_coefficient_correction_le hn hdeg)
          (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
            (pow_nonneg (mul_nonneg hB hs) d))
    _ = _ := by simp only [mul_pow]; ring

end TensorLB
