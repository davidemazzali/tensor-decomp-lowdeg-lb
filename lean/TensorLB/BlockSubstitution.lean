module

public import TensorLB.IndexedTensor
public import TensorLB.TensorContraction
public import TensorLB.LiftWeights
public import TensorLB.WitnessNorm
public import Mathlib.Algebra.MvPolynomial.Funext

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# One choice of substitution block sizes

Replacing each input tensor slot by a homogeneous tensor creates a sigma-indexed
output tensor. Orthogonal columns control its squared norm and the monotonicity
of the lift weight controls the increase in hidden degree.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {ι α H : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype H]
  (j : ι → ℕ)

def blockTensor (Q : ∀ i, α → (Fin (j i) → H) → ℝ) (M : (ι → α) → ℝ)
    (t : (Σ i, Fin (j i)) → H) : ℝ := contractTensor Q M (fun i b => t ⟨i, b⟩)

theorem sum_sq_blockTensor (Q : ∀ i, α → (Fin (j i) → H) → ℝ) (M : (ι → α) → ℝ) :
    (∑ t : (Σ i, Fin (j i)) → H, blockTensor j Q M t ^ 2) =
      ∑ s : ∀ i, Fin (j i) → H, contractTensor Q M s ^ 2 := by
  exact Fintype.sum_equiv (Equiv.piCurry (fun _ _ => H)) _ _ (fun _ => rfl)

theorem blockTensor_polynomial (Q : ∀ i, α → (Fin (j i) → H) → ℝ)
    (M : (ι → α) → ℝ) :
    indexedTensorPolynomial (blockTensor j Q M) =
      ∑ t : ι → α, MvPolynomial.C (M t) * ∏ i, tensorPolynomial (Q i (t i)) := by
  apply MvPolynomial.funext
  intro u
  simp only [eval_indexedTensorPolynomial, map_sum, map_mul, MvPolynomial.eval_C,
    map_prod, eval_tensorPolynomial]
  calc
    _ = ∑ s : ∀ i, Fin (j i) → H,
        contractTensor Q M s * ∏ i, ∏ b, u (s i b) := by
      apply Fintype.sum_equiv (Equiv.piCurry (fun _ _ => H))
      intro t
      simp only [blockTensor, Equiv.piCurry_apply, Sigma.curry, Fintype.prod_sigma]
      rfl
    _ = ∑ t : ι → α, M t *
        ∑ s : ∀ i, Fin (j i) → H, ∏ i, Q i (t i) (s i) * ∏ b, u (s i b) := by
      simp only [contractTensor, productColumn, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      exact (Fintype.prod_sum (fun i (s : Fin (j i) → H) =>
        Q i (t i) s * ∏ b, u (s b))).symm

variable {n m : ℕ}

/-- Squared lift bound for one substitution choice. -/
theorem expectation_lift_blockTensor_sq_le
    (Q : ∀ i, α → (Fin (j i) → NonemptyCharacter n) → ℝ) (M : (ι → α) → ℝ)
    (hQ : ∀ i a b, a ≠ b → (∑ v, Q i a v * Q i b v) = 0)
    (C : ι → ℝ) (hC : ∀ i a, (∑ v, Q i a v ^ 2) ≤ C i) :
    expectation n m (fun ω => liftPolynomial (indexedTensorPolynomial (blockTensor j Q M)) ω ^ 2) ≤
      liftWeight (m - 1) (∑ i, j i) * ((∏ i, C i) * ∑ t, M t ^ 2) := by
  have h := expectation_lift_indexedTensorPolynomial_sq_le (m := m) (blockTensor j Q M)
  simp only [Fintype.card_sigma, Fintype.card_fin, sum_sq_blockTensor] at h
  exact h.trans (mul_le_mul_of_nonneg_left (sum_sq_contractTensor_le Q M hQ C hC)
    (liftWeight_nonneg _ _))

/-- Increasing the hidden degree within the permitted range does not increase
the lift weight. The resulting norm bound multiplies the individual column norms. -/
theorem witnessNorm_lift_blockTensor_le
    (Q : ∀ i, α → (Fin (j i) → NonemptyCharacter n) → ℝ) (M : (ι → α) → ℝ)
    (hQ : ∀ i a b, a ≠ b → (∑ v, Q i a v * Q i b v) = 0)
    (C : ι → ℝ) (hC0 : ∀ i, 0 ≤ C i) (hC : ∀ i a, (∑ v, Q i a v ^ 2) ≤ C i ^ 2)
    (hj : Fintype.card ι ≤ ∑ i, j i) (hN : 2 * (∑ i, j i) ≤ m - 1) :
    witnessNorm (liftPolynomial (indexedTensorPolynomial (blockTensor j Q M)) : Sample n m → ℝ) ≤
      (∏ i, C i) * Real.sqrt (liftWeight (m - 1) (Fintype.card ι) * ∑ t, M t ^ 2) := by
  have hM0 : 0 ≤ ∑ t : ι → α, M t ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hprod0 : 0 ≤ ∏ i, C i := Finset.prod_nonneg (fun i _ => hC0 i)
  apply (witnessNorm_le_iff _ (mul_nonneg hprod0 (Real.sqrt_nonneg _))).2
  calc
    _ ≤ liftWeight (m - 1) (∑ i, j i) * ((∏ i, C i ^ 2) * ∑ t, M t ^ 2) :=
      expectation_lift_blockTensor_sq_le j Q M hQ (fun i => C i ^ 2) hC
    _ ≤ liftWeight (m - 1) (Fintype.card ι) * ((∏ i, C i ^ 2) * ∑ t, M t ^ 2) :=
      mul_le_mul_of_nonneg_right (liftWeight_le_of_le hj hN)
        (mul_nonneg (Finset.prod_nonneg (fun _ _ => sq_nonneg _)) hM0)
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg (liftWeight_nonneg _ _) hM0), ← Finset.prod_pow]
      ring

end

end TensorLB
