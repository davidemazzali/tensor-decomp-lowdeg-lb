module

public import TensorLB.Expectation
public import Mathlib.Algebra.BigOperators.Ring.Finset

import Mathlib.Tactic.Ring

/-!
# Finite sums under expectation

Finite linear combinations of orthogonal random variables have second moment
equal to the sum of their weighted second moments. This supplies the exact norm
formula for polynomial combinations of the distinct-component witnesses.
-/

set_option autoImplicit false

public section

namespace TensorLB

open scoped BigOperators

variable {n m : ℕ} {ι κ : Type*}

/-- Finite expectation commutes with any finite sum. -/
theorem expectation_finset_sum (s : Finset ι) (f : ι → Sample n m → ℝ) :
    expectation n m (fun ω => ∑ i ∈ s, f i ω) =
      ∑ i ∈ s, expectation n m (f i) := by
  unfold expectation
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem expectation_sum [Fintype ι] (f : ι → Sample n m → ℝ) :
    expectation n m (fun ω => ∑ i, f i ω) = ∑ i, expectation n m (f i) :=
  expectation_finset_sum Finset.univ f

theorem expectation_div_const (f : Sample n m → ℝ) (c : ℝ) :
    expectation n m (fun ω => f ω / c) = expectation n m f / c := by
  simp only [div_eq_mul_inv, expectation_mul_const]

/-- Expand the inner product of two finite sums into pairwise inner products. -/
theorem expectation_finset_sum_mul_finset_sum (s : Finset ι) (t : Finset κ)
    (f : ι → Sample n m → ℝ) (g : κ → Sample n m → ℝ) :
    expectation n m (fun ω => (∑ i ∈ s, f i ω) * ∑ j ∈ t, g j ω) =
      ∑ i ∈ s, ∑ j ∈ t, expectation n m (fun ω => f i ω * g j ω) := by
  simp_rw [Finset.sum_mul_sum, expectation_finset_sum]

theorem expectation_sum_mul_sum [Fintype ι] [Fintype κ]
    (f : ι → Sample n m → ℝ) (g : κ → Sample n m → ℝ) :
    expectation n m (fun ω => (∑ i, f i ω) * ∑ j, g j ω) =
      ∑ i, ∑ j, expectation n m (fun ω => f i ω * g j ω) :=
  expectation_finset_sum_mul_finset_sum Finset.univ Finset.univ f g

/-- Exact second moment of a finite weighted sum of pairwise orthogonal variables. -/
theorem expectation_sq_sum_of_orthogonal (s : Finset ι) (a : ι → ℝ)
    (f : ι → Sample n m → ℝ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      expectation n m (fun ω => f i ω * f j ω) = 0) :
    expectation n m (fun ω => (∑ i ∈ s, a i * f i ω) ^ 2) =
      ∑ i ∈ s, a i ^ 2 * expectation n m (fun ω => f i ω ^ 2) := by
  classical
  simp only [sq, expectation_finset_sum_mul_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · calc
      _ = expectation n m (fun ω => (a i * a i) * (f i ω * f i ω)) :=
        expectation_congr (fun ω => by ring)
      _ = _ := expectation_const_mul _ _
  · intro j hj hji
    calc
      _ = expectation n m (fun ω => (a i * a j) * (f i ω * f j ω)) :=
        expectation_congr (fun ω => by ring)
      _ = 0 := by rw [expectation_const_mul, horth i hi j hj (Ne.symm hji), mul_zero]
  · exact fun h => (h hi).elim

end TensorLB
