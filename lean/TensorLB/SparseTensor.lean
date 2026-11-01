module

public import TensorLB.TensorSubstitution
public import Mathlib.Data.Finset.Sort

/-!
# Sparse tensor columns

The concrete substitution maps have constant coefficients on small finite sets
of ordered tuples. Their squared norms are cardinality times coefficient squared.
Recovering the output set from a tuple proves orthogonality of distinct columns.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {α : Type*} [Fintype α] {d n : ℕ}

def sparseTensor (s : Finset (Fin d → α)) (c : ℝ) (t : Fin d → α) : ℝ :=
  if t ∈ s then c else 0

theorem sum_sq_sparseTensor (s : Finset (Fin d → α)) (c : ℝ) :
    (∑ t, sparseTensor s c t ^ 2) = (s.card : ℝ) * c ^ 2 := by
  simp only [sparseTensor, ite_pow, zero_pow (by decide : 2 ≠ 0)]
  rw [← Finset.sum_filter]
  simp

theorem eval_tensorPolynomial_sparseTensor (s : Finset (Fin d → α)) (c : ℝ) (u : α → ℝ) :
    MvPolynomial.eval u (tensorPolynomial (sparseTensor s c)) =
      c * ∑ t ∈ s, ∏ i, u (t i) := by
  rw [eval_tensorPolynomial]
  simp only [sparseTensor, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp [← Finset.mul_sum]

/-- The union of all hidden character supports in a tuple. -/
def tupleUnion (t : Fin d → NonemptyCharacter n) : Finset (Fin n) :=
  Finset.univ.biUnion (fun i => (t i).val)

/-- A tuple cannot belong to two columns when its union identifies the column. -/
theorem orthogonal_of_tupleUnion {σ : Type*} (label : σ → Finset (Fin n))
    (hinj : Function.Injective label) (Q : σ → (Fin d → NonemptyCharacter n) → ℝ)
    (hQ : ∀ a t, Q a t ≠ 0 → tupleUnion t = label a) (a b : σ) (hab : a ≠ b) :
    (∑ t, Q a t * Q b t) = 0 := by
  apply Finset.sum_eq_zero
  intro t _
  by_cases ha : Q a t = 0
  · rw [ha, zero_mul]
  · have hb : Q b t = 0 := by
      by_contra hb
      exact hab (hinj ((hQ a t ha).symm.trans (hQ b t hb)))
    rw [hb, mul_zero]

end

end TensorLB
