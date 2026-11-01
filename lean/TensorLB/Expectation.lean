module

public import TensorLB.Definitions
public import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Finite expectation for the tensor model

The sample space is nonempty for every `n` and `m`, including zero. Its uniform
average agrees with Mathlib's finite expectation. These lemmas expose the
linearity, positivity, and Cauchy–Schwarz properties needed by witness bounds.
-/

set_option autoImplicit false

public section

namespace TensorLB

open scoped BigOperators

variable {n m : ℕ}

/-- The model's average is Mathlib's uniform finite expectation. -/
theorem expectation_eq_expect (f : Sample n m → ℝ) :
    expectation n m f = 𝔼 ω, f ω := by
  exact (Fintype.expect_eq_sum_div_card f).symm

theorem expectation_congr {f g : Sample n m → ℝ} (h : ∀ ω, f ω = g ω) :
    expectation n m f = expectation n m g := by
  congr 1
  exact funext h

@[simp] theorem expectation_const (c : ℝ) :
    expectation n m (fun _ => c) = c := by
  rw [expectation_eq_expect]
  exact Finset.expect_const Finset.univ_nonempty c

theorem expectation_add (f g : Sample n m → ℝ) :
    expectation n m (fun ω => f ω + g ω) = expectation n m f + expectation n m g := by
  simp only [expectation_eq_expect, Finset.expect_add_distrib]

theorem expectation_sub (f g : Sample n m → ℝ) :
    expectation n m (fun ω => f ω - g ω) = expectation n m f - expectation n m g := by
  simp only [expectation, Finset.sum_sub_distrib, sub_div]

theorem expectation_neg (f : Sample n m → ℝ) :
    expectation n m (fun ω => -f ω) = -expectation n m f := by
  simp only [expectation, Finset.sum_neg_distrib, neg_div]

theorem expectation_const_mul (c : ℝ) (f : Sample n m → ℝ) :
    expectation n m (fun ω => c * f ω) = c * expectation n m f := by
  simp only [expectation, ← Finset.mul_sum, mul_div_assoc]

theorem expectation_mul_const (f : Sample n m → ℝ) (c : ℝ) :
    expectation n m (fun ω => f ω * c) = expectation n m f * c := by
  simpa only [mul_comm] using expectation_const_mul c f

theorem expectation_nonneg {f : Sample n m → ℝ} (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ expectation n m f := by
  rw [expectation_eq_expect]
  exact Finset.expect_nonneg fun ω _ => h ω

theorem expectation_mono {f g : Sample n m → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    expectation n m f ≤ expectation n m g := by
  simp only [expectation_eq_expect]
  exact Finset.expect_le_expect fun ω _ => h ω

theorem expectation_sq_nonneg (f : Sample n m → ℝ) :
    0 ≤ expectation n m (fun ω => f ω ^ 2) :=
  expectation_nonneg fun ω => sq_nonneg (f ω)

/-- Cauchy–Schwarz for the uniform law on all sign arrays. -/
theorem expectation_mul_sq_le (f g : Sample n m → ℝ) :
    expectation n m (fun ω => f ω * g ω) ^ 2 ≤
      expectation n m (fun ω => f ω ^ 2) * expectation n m (fun ω => g ω ^ 2) := by
  simp only [expectation_eq_expect]
  exact Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f g

@[simp] theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> simp [sign]

/-- Every target character takes values in the two signs, even for the empty target. -/
@[simp] theorem target_sq (A : Finset (Fin n)) (ω : Sample n m) :
    target n m A ω ^ 2 = 1 := by
  simp [target, ← Finset.prod_pow]

@[simp] theorem expectation_target_sq (A : Finset (Fin n)) :
    expectation n m (fun ω => target n m A ω ^ 2) = 1 := by
  simp

end TensorLB
