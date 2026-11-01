module

public import TensorLB.Lift
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Lifting polynomials to averaged Fourier witnesses

Each monomial is replaced by its distinct-component witness, and the map is
extended linearly over the polynomial coefficients. Orthogonality of different
multisets gives an exact coefficient formula for the lifted second moment.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators

noncomputable section

variable {n m : ℕ}

/-- Replace every monomial by its averaged distinct-component Fourier witness. -/
def liftPolynomial (p : MvPolynomial (NonemptyCharacter n) ℝ) (ω : Sample n m) : ℝ :=
  p.coeff.sum fun R c => c * monomialWitness R ω

theorem liftPolynomial_eq_sum (p : MvPolynomial (NonemptyCharacter n) ℝ)
    (ω : Sample n m) :
    liftPolynomial p ω = ∑ R ∈ p.support, p.coeff R * monomialWitness R ω :=
  MvPolynomial.sum_def

@[simp] theorem liftPolynomial_zero (ω : Sample n m) :
    liftPolynomial (0 : MvPolynomial (NonemptyCharacter n) ℝ) ω = 0 := by
  simp [liftPolynomial]

@[simp] theorem liftPolynomial_monomial (R : NonemptyCharacter n →₀ ℕ)
    (c : ℝ) (ω : Sample n m) :
    liftPolynomial (MvPolynomial.monomial R c) ω = c * monomialWitness R ω := by
  unfold liftPolynomial
  exact MvPolynomial.sum_monomial_eq (by simp)

theorem liftPolynomial_add (p q : MvPolynomial (NonemptyCharacter n) ℝ)
    (ω : Sample n m) :
    liftPolynomial (p + q) ω = liftPolynomial p ω + liftPolynomial q ω := by
  unfold liftPolynomial
  rw [AddMonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem liftPolynomial_finset_sum {ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial (NonemptyCharacter n) ℝ) (ω : Sample n m) :
    liftPolynomial (∑ i ∈ s, p i) ω = ∑ i ∈ s, liftPolynomial (p i) ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, liftPolynomial_add, ih]

theorem liftPolynomial_smul (c : ℝ) (p : MvPolynomial (NonemptyCharacter n) ℝ)
    (ω : Sample n m) :
    liftPolynomial (c • p) ω = c * liftPolynomial p ω := by
  unfold liftPolynomial
  rw [AddMonoidAlgebra.coeff_smul, Finsupp.sum_smul_index (fun _ => zero_mul _)]
  simp only [Finsupp.sum, mul_assoc, Finset.mul_sum]

@[simp] theorem liftPolynomial_C (c : ℝ) (ω : Sample n m) :
    liftPolynomial (MvPolynomial.C c) ω = c := by
  change liftPolynomial (MvPolynomial.monomial 0 c) ω = c
  rw [liftPolynomial_monomial, monomialWitness_zero, mul_one]

@[simp] theorem liftPolynomial_one (ω : Sample n m) :
    liftPolynomial (1 : MvPolynomial (NonemptyCharacter n) ℝ) ω = 1 := by
  simpa using liftPolynomial_C 1 ω

/-- The expectation of the lift is the polynomial's constant coefficient. -/
theorem expectation_liftPolynomial (p : MvPolynomial (NonemptyCharacter n) ℝ) :
    expectation n m (liftPolynomial p) = p.coeff 0 := by
  classical
  change expectation n m (fun ω => liftPolynomial p ω) = _
  simp only [liftPolynomial_eq_sum, expectation_finset_sum, expectation_const_mul]
  rw [Finset.sum_eq_single 0]
  · rw [expectation_congr (fun ω => monomialWitness_zero ω), expectation_const, mul_one]
  · intro R _ hR
    rw [expectation_monomialWitness_eq_zero hR, mul_zero]
  · intro h0
    simp [MvPolynomial.notMem_support_iff.mp h0]

/-- Orthogonality eliminates cross terms, leaving the exact weighted coefficient
sum. Terms with too many occurrences have zero witness under the total definition. -/
theorem expectation_liftPolynomial_sq (p : MvPolynomial (NonemptyCharacter n) ℝ) :
    expectation n m (fun ω => liftPolynomial p ω ^ 2) =
      ∑ R ∈ p.support, p.coeff R ^ 2 *
        ((witnessFactorial R : ℝ) /
          (((m - 1).descFactorial (witnessDegree R) : ℕ) : ℝ)) := by
  simp only [liftPolynomial_eq_sum]
  rw [expectation_sq_sum_of_orthogonal p.support p.coeff
    (fun R ω => monomialWitness R ω)
    (fun R _ S _ h => expectation_monomialWitness_mul_eq_zero R S h)]
  simp only [expectation_monomialWitness_sq]

end

end TensorLB
