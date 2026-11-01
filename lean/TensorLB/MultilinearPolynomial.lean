module

public import TensorLB.SymmetricTensor
public import Mathlib.Analysis.Analytic.IteratedFDeriv

/-!
# Homogeneous polynomials from multilinear Taylor terms

Evaluating a multilinear map on coordinate basis vectors gives an ordered
tensor. Its polynomial is exactly the map's diagonal evaluation.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {α : Type*} [Fintype α] {d : ℕ}

def multilinearPolynomial (M : (α → ℝ) [×d]→L[ℝ] ℝ) : MvPolynomial α ℝ :=
  tensorPolynomial (fun t => M (fun i => Pi.single (t i) 1))

theorem multilinearPolynomial_isHomogeneous (M : (α → ℝ) [×d]→L[ℝ] ℝ) :
    (multilinearPolynomial M).IsHomogeneous d := tensorPolynomial_isHomogeneous _

theorem eval_multilinearPolynomial (M : (α → ℝ) [×d]→L[ℝ] ℝ) (x : α → ℝ) :
    MvPolynomial.eval x (multilinearPolynomial M) = M (fun _ => x) := by
  rw [multilinearPolynomial, eval_tensorPolynomial]
  have hx : x = ∑ a, x a • (Pi.single a 1 : α → ℝ) := by
    ext a
    simp [Pi.single_apply]
  conv_rhs => rw [hx]
  rw [M.map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [M.map_smul_univ]
  exact mul_comm _ _

end

end TensorLB
