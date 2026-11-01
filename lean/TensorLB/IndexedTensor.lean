module

public import TensorLB.SymmetricTensor
public import Mathlib.Data.Fintype.EquivFin

/-!
# Tensor polynomials with arbitrary finite slot sets

Substitution creates blocks of different lengths. Indexing slots by a sigma
type avoids an arbitrary flattening convention; an explicit equivalence with
`Fin r` transfers the checked lift normalization to these tensors.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {ι κ α : Type*} [Fintype ι] [Fintype κ] [Fintype α]
  [DecidableEq ι] [DecidableEq κ]

def indexedTuple (t : ι → α) : α →₀ ℕ := ∑ i, Finsupp.single (t i) 1

def indexedTensorPolynomial (M : (ι → α) → ℝ) : MvPolynomial α ℝ :=
  ∑ t, MvPolynomial.monomial (indexedTuple t) (M t)

omit [Fintype α] [DecidableEq ι] in
theorem prod_pow_indexedTuple (u : α → ℝ) (t : ι → α) :
    (indexedTuple t).prod (fun a r => u a ^ r) = ∏ i, u (t i) := by
  unfold indexedTuple
  rw [← Finsupp.prod_finsetSum_index (fun _ => pow_zero _)
    (fun _ _ _ => pow_add _ _ _)]
  simp

theorem eval_indexedTensorPolynomial (M : (ι → α) → ℝ) (u : α → ℝ) :
    MvPolynomial.eval u (indexedTensorPolynomial M) = ∑ t, M t * ∏ i, u (t i) := by
  simp only [indexedTensorPolynomial, map_sum, MvPolynomial.eval_monomial,
    prod_pow_indexedTuple]

/-- Reorder the slots, preserving every label and coefficient. -/
def reindexTuple (e : κ ≃ ι) : (ι → α) ≃ (κ → α) where
  toFun t i := t (e i)
  invFun t i := t (e.symm i)
  left_inv t := by funext i; simp
  right_inv t := by funext i; simp

omit [Fintype α] [DecidableEq ι] [DecidableEq κ] in
theorem indexedTuple_reindex (e : κ ≃ ι) (t : ι → α) :
    indexedTuple (reindexTuple e t) = indexedTuple t := by
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem indexedTensorPolynomial_reindex (e : κ ≃ ι) (M : (ι → α) → ℝ) :
    indexedTensorPolynomial M =
      indexedTensorPolynomial (fun t : κ → α => M ((reindexTuple e).symm t)) := by
  apply Fintype.sum_equiv (reindexTuple e)
  intro t
  simp only [Equiv.symm_apply_apply, indexedTuple_reindex]

theorem sum_sq_reindex (e : κ ≃ ι) (M : (ι → α) → ℝ) :
    (∑ t : κ → α, M ((reindexTuple e).symm t) ^ 2) = ∑ t : ι → α, M t ^ 2 := by
  exact Fintype.sum_equiv (reindexTuple e).symm _ _ (fun _ => rfl)

theorem indexedTensorPolynomial_eq_tensorPolynomial (M : (ι → α) → ℝ) :
    indexedTensorPolynomial M =
      tensorPolynomial (fun t : Fin (Fintype.card ι) → α =>
        M ((reindexTuple (Fintype.equivFin ι).symm).symm t)) :=
  indexedTensorPolynomial_reindex (Fintype.equivFin ι).symm M

variable {n m : ℕ}

/-- The nonsymmetric lift bound is independent of how the slots are enumerated. -/
theorem expectation_lift_indexedTensorPolynomial_sq_le
    (M : (ι → NonemptyCharacter n) → ℝ) :
    expectation n m (fun ω => liftPolynomial (indexedTensorPolynomial M) ω ^ 2) ≤
      ((Fintype.card ι).factorial : ℝ) /
        (((m - 1).descFactorial (Fintype.card ι) : ℕ) : ℝ) * ∑ t, M t ^ 2 := by
  rw [indexedTensorPolynomial_eq_tensorPolynomial]
  have h := expectation_lift_tensorPolynomial_sq_le (m := m)
    (fun t : Fin (Fintype.card ι) → NonemptyCharacter n =>
      M ((reindexTuple (Fintype.equivFin ι).symm).symm t))
  unfold tensorNormSq at h
  rw [sum_sq_reindex] at h
  exact h

end

end TensorLB
