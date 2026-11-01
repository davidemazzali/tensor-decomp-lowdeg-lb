module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Ring

/-!
# Tensor products of orthogonal-column maps

The connected-coordinate maps have disjoint supports for distinct output
sets. Their tensor products therefore have orthogonal columns too. Expanding
finite sums proves the Hilbert–Schmidt bound without introducing an abstract
completed tensor product.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β] [DecidableEq ι]

/-- Squared Euclidean norm of a combination of orthogonal columns. -/
theorem sum_sq_linearCombination_of_orthogonal
    (Q : α → β → ℝ) (M : α → ℝ)
    (hQ : ∀ a b, a ≠ b → (∑ v, Q a v * Q b v) = 0) :
    (∑ v, (∑ a, M a * Q a v) ^ 2) =
      ∑ a, M a ^ 2 * ∑ v, Q a v ^ 2 := by
  simp only [sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm, Finset.sum_eq_single a]
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  · intro b _ hba
    calc
      _ = M a * M b * ∑ v, Q a v * Q b v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = 0 := by rw [hQ a b hba.symm, mul_zero]
  · simp

variable {γ : ι → Type*} [∀ i, Fintype (γ i)]

/-- A tensor product column, allowing a different output space at each slot. -/
def productColumn (Q : ∀ i, α → γ i → ℝ) (t : ι → α) (s : ∀ i, γ i) : ℝ :=
  ∏ i, Q i (t i) (s i)

omit [Fintype α] in
theorem sum_productColumn_mul (Q : ∀ i, α → γ i → ℝ) (t u : ι → α) :
    (∑ s : ∀ i, γ i, productColumn Q t s * productColumn Q u s) =
      ∏ i, ∑ v : γ i, Q i (t i) v * Q i (u i) v := by
  simp only [productColumn, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i (v : γ i) => Q i (t i) v * Q i (u i) v)).symm

omit [Fintype α] in
theorem productColumn_orthogonal (Q : ∀ i, α → γ i → ℝ)
    (hQ : ∀ i a b, a ≠ b → (∑ v, Q i a v * Q i b v) = 0)
    (t u : ι → α) (htu : t ≠ u) :
    (∑ s : ∀ i, γ i, productColumn Q t s * productColumn Q u s) = 0 := by
  rw [sum_productColumn_mul]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp htu
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hQ i (t i) (u i) hi)

/-- Apply a separate finite matrix to each slot of an input tensor. -/
def contractTensor (Q : ∀ i, α → γ i → ℝ) (M : (ι → α) → ℝ) (s : ∀ i, γ i) : ℝ :=
  ∑ t, M t * productColumn Q t s

theorem sum_sq_contractTensor (Q : ∀ i, α → γ i → ℝ) (M : (ι → α) → ℝ)
    (hQ : ∀ i a b, a ≠ b → (∑ v, Q i a v * Q i b v) = 0) :
    (∑ s : ∀ i, γ i, contractTensor Q M s ^ 2) =
      ∑ t, M t ^ 2 * ∏ i, ∑ v : γ i, Q i (t i) v ^ 2 := by
  simp only [contractTensor]
  rw [sum_sq_linearCombination_of_orthogonal _ M (productColumn_orthogonal Q hQ)]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  simpa only [sq] using sum_productColumn_mul Q t t

/-- Tensoring maps multiplies their column norm bounds, with no dimension factor. -/
theorem sum_sq_contractTensor_le (Q : ∀ i, α → γ i → ℝ) (M : (ι → α) → ℝ)
    (hQ : ∀ i a b, a ≠ b → (∑ v, Q i a v * Q i b v) = 0)
    (C : ι → ℝ) (hC : ∀ i a, (∑ v : γ i, Q i a v ^ 2) ≤ C i) :
    (∑ s : ∀ i, γ i, contractTensor Q M s ^ 2) ≤ (∏ i, C i) * ∑ t, M t ^ 2 := by
  rw [sum_sq_contractTensor Q M hQ, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  rw [mul_comm (∏ i, C i)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (fun i _ => hC i (t i))

end

end TensorLB
