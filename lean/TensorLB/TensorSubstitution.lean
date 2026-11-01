module

public import TensorLB.BlockSubstitution

/-!
# Summing the substitution choices

Expanding each connected coordinate into homogeneous tensors creates one term
for each choice of block sizes. The triangle inequality and the tensor-product
column bound control their sum, including collisions between different choices.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {α H J : Type*} [Fintype α] [Fintype H] [Fintype J] {d n m h : ℕ}

theorem tensorPolynomial_eq_sum_products (M : (Fin d → α) → ℝ) :
    tensorPolynomial M = ∑ t, MvPolynomial.C (M t) * ∏ i, MvPolynomial.X (t i) := by
  apply Finset.sum_congr rfl
  intro t _
  rw [prod_X_eq_monomial_tupleIndex, MvPolynomial.C_mul_monomial, mul_one]

omit [Fintype H] in
theorem eval₂_tensorPolynomial (M : (Fin d → α) → ℝ) (b : α → MvPolynomial H ℝ) :
    MvPolynomial.eval₂ MvPolynomial.C b (tensorPolynomial M) =
      ∑ t, MvPolynomial.C (M t) * ∏ i, b (t i) := by
  rw [tensorPolynomial_eq_sum_products]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_prod, MvPolynomial.eval₂_X]

/-- Exact expansion of tensor substitution into sigma-indexed block tensors. -/
theorem tensor_substitution_eq_sum_blocks (len : J → ℕ)
    (Q : ∀ a, α → (Fin (len a) → H) → ℝ) (M : (Fin d → α) → ℝ) :
    MvPolynomial.eval₂ MvPolynomial.C (fun i => ∑ a, tensorPolynomial (Q a i))
      (tensorPolynomial M) =
        ∑ choice : Fin d → J, indexedTensorPolynomial
          (blockTensor (fun i => len (choice i)) (fun i => Q (choice i)) M) := by
  rw [eval₂_tensorPolynomial]
  simp_rw [blockTensor_polynomial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.prod_sum (fun i a => tensorPolynomial (Q a (t i)))

/-- General substitution bound for homogeneous inputs and orthogonal tensor
columns. The maximum block size is `h`, and the sum of column norm bounds is `∑ C`. -/
theorem witnessNorm_tensor_substitution_le (len : J → ℕ)
    (hlen1 : ∀ a, 1 ≤ len a) (hlenh : ∀ a, len a ≤ h)
    (Q : ∀ a, α → (Fin (len a) → NonemptyCharacter n) → ℝ)
    (hQ : ∀ a i j, i ≠ j → (∑ v, Q a i v * Q a j v) = 0)
    (C : J → ℝ) (hC0 : ∀ a, 0 ≤ C a) (hC : ∀ a i, (∑ v, Q a i v ^ 2) ≤ C a ^ 2)
    (M : (Fin d → α) → ℝ) (hN : 2 * (h * d) ≤ m - 1) :
    witnessNorm (liftPolynomial
      (MvPolynomial.eval₂ MvPolynomial.C (fun i => ∑ a, tensorPolynomial (Q a i))
        (tensorPolynomial M)) : Sample n m → ℝ) ≤
      (∑ a, C a) ^ d * Real.sqrt (liftWeight (m - 1) d * tensorNormSq M) := by
  rw [tensor_substitution_eq_sum_blocks]
  change witnessNorm (fun ω : Sample n m => liftPolynomial _ ω) ≤ _
  simp_rw [liftPolynomial_finset_sum]
  apply (witnessNorm_finset_sum_le _ _).trans
  calc
    _ ≤ ∑ choice : Fin d → J, (∏ i, C (choice i)) *
        Real.sqrt (liftWeight (m - 1) d * tensorNormSq M) := by
      apply Finset.sum_le_sum
      intro choice _
      have hlo : Fintype.card (Fin d) ≤ ∑ i, len (choice i) := by
        calc
          _ = ∑ _i : Fin d, 1 := by simp
          _ ≤ _ := Finset.sum_le_sum (fun i _ => hlen1 (choice i))
      have hhi : (∑ i : Fin d, len (choice i)) ≤ h * d := by
        calc
          _ ≤ ∑ _i : Fin d, h := Finset.sum_le_sum (fun i _ => hlenh (choice i))
          _ = _ := by simp [Nat.mul_comm]
      simpa only [Fintype.card_fin, tensorNormSq] using
        witnessNorm_lift_blockTensor_le (fun i => len (choice i)) (fun i => Q (choice i)) M
          (fun i => hQ (choice i)) (fun i => C (choice i)) (fun i => hC0 (choice i))
          (fun i => hC (choice i)) hlo ((Nat.mul_le_mul_left 2 hhi).trans hN)
    _ = _ := by rw [← Finset.sum_mul, ← Fintype.sum_pow]

/-- In terms of coefficient energy the input factorial cancels exactly. -/
theorem witnessNorm_homogeneous_substitution_le (len : J → ℕ)
    (hlen1 : ∀ a, 1 ≤ len a) (hlenh : ∀ a, len a ≤ h)
    (Q : ∀ a, α → (Fin (len a) → NonemptyCharacter n) → ℝ)
    (hQ : ∀ a i j, i ≠ j → (∑ v, Q a i v * Q a j v) = 0)
    (C : J → ℝ) (hC0 : ∀ a, 0 ≤ C a) (hC : ∀ a i, (∑ v, Q a i v ^ 2) ≤ C a ^ 2)
    (p : MvPolynomial α ℝ) (hp : p.IsHomogeneous d) (hN : 2 * (h * d) ≤ m - 1) :
    witnessNorm (liftPolynomial
      (MvPolynomial.eval₂ MvPolynomial.C (fun i => ∑ a, tensorPolynomial (Q a i)) p) :
        Sample n m → ℝ) ≤
      (∑ a, C a) ^ d * Real.sqrt (coefficientEnergy p / (((m - 1).descFactorial d : ℕ) : ℝ)) := by
  have hbound := witnessNorm_tensor_substitution_le len hlen1 hlenh Q hQ C hC0 hC
    (polynomialTensor p d) hN
  rw [tensorPolynomial_polynomialTensor p hp] at hbound
  have hnorm : liftWeight (m - 1) d * tensorNormSq (polynomialTensor p d) =
      coefficientEnergy p / (((m - 1).descFactorial d : ℕ) : ℝ) := by
    rw [← factorial_mul_tensorNormSq_polynomialTensor p hp]
    unfold liftWeight
    ring
  rwa [hnorm] at hbound

end

end TensorLB
