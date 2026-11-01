module

public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Total degree under polynomial substitution

Replacing each variable by a polynomial of degree at most `d` multiplies total
degree by at most `d`. In particular, substitution of constants and individual
variables does not increase degree, as needed for the tensor observation map.
-/

set_option autoImplicit false

public section

namespace TensorLB

open scoped BigOperators

variable {σ υ R : Type*} [CommSemiring R]

/-- Substitution by polynomials of degree at most `d` multiplies degree by at
most `d`, including in the presence of cancellations or zero coefficients. -/
theorem totalDegree_eval₂_le_mul (q : σ → MvPolynomial υ R)
    (p : MvPolynomial σ R) {d : ℕ} (h : ∀ i, (q i).totalDegree ≤ d) :
    (MvPolynomial.eval₂ MvPolynomial.C q p).totalDegree ≤ p.totalDegree * d := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  calc
    _ ≤ (MvPolynomial.C (p.coeff s) : MvPolynomial υ R).totalDegree +
        (∏ i ∈ s.support, q i ^ s i).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = (∏ i ∈ s.support, q i ^ s i).totalDegree := by simp
    _ ≤ ∑ i ∈ s.support, (q i ^ s i).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ s.support, s i * d := by
      apply Finset.sum_le_sum
      intro i _
      exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (h i))
    _ = (s.sum fun _ e => e) * d := by simp only [Finsupp.sum, Finset.sum_mul]
    _ ≤ p.totalDegree * d := Nat.mul_le_mul_right _ (MvPolynomial.le_totalDegree hs)

/-- Substitution of affine polynomials preserves an upper bound on total degree. -/
theorem totalDegree_eval₂_le (q : σ → MvPolynomial υ R)
    (p : MvPolynomial σ R) (h : ∀ i, (q i).totalDegree ≤ 1) :
    (MvPolynomial.eval₂ MvPolynomial.C q p).totalDegree ≤ p.totalDegree := by
  simpa only [Nat.mul_one] using totalDegree_eval₂_le_mul q p h

end TensorLB
