module

public import TensorLB.PolynomialLift
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Symmetric tensors and the exact lift normalization

An order-`d` tensor is represented by its entries on ordered `d`-tuples.
The polynomial sums these entries against the corresponding monomials.
Repeated labels are counted by the multinomial coefficient, so the squared
Hilbert–Schmidt norm has the factorial normalization used in the manuscript.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {α : Type*} {d n m : ℕ}

/-- The multiplicities of labels in an ordered tuple. -/
def tupleIndex (t : Fin d → α) : α →₀ ℕ :=
  ∑ i, Finsupp.single (t i) 1

theorem tupleIndex_degree (t : Fin d → α) :
    (tupleIndex t).sum (fun _ r => r) = d := by
  classical
  unfold tupleIndex
  rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  simp

theorem prod_X_eq_monomial_tupleIndex (t : Fin d → α) :
    (∏ i, MvPolynomial.X (t i) : MvPolynomial α ℝ) =
      MvPolynomial.monomial (tupleIndex t) 1 := by
  classical
  have h (s : Finset (Fin d)) :
      (∏ i ∈ s, MvPolynomial.X (t i) : MvPolynomial α ℝ) =
        MvPolynomial.monomial (∑ i ∈ s, Finsupp.single (t i) 1) 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih]
      simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
  exact h Finset.univ

/-- Count all orderings of a multiset, including repeated labels. -/
theorem sum_tupleIndex_eq [Fintype α] (R : α →₀ ℕ) :
    (∑ t : Fin d → α, if tupleIndex t = R then (1 : ℝ) else 0) =
      if R.sum (fun _ r => r) = d then (R.multinomial : ℝ) else 0 := by
  classical
  have h := MvPolynomial.coeff_sum_X_pow_of_fintype (R := ℝ) R d
  rw [Fintype.sum_pow] at h
  simpa only [prod_X_eq_monomial_tupleIndex, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial, Nat.cast_ite, Nat.cast_zero] using h

/-- Symmetry expressed by independence of the ordering of the input labels. -/
def IsSymmetricTensor (M : (Fin d → α) → ℝ) : Prop :=
  ∀ s t, tupleIndex s = tupleIndex t → M s = M t

/-- Polynomial represented by an array of tensor entries. -/
def tensorPolynomial [Fintype α] (M : (Fin d → α) → ℝ) : MvPolynomial α ℝ :=
  ∑ t, MvPolynomial.monomial (tupleIndex t) (M t)

/-- Squared Hilbert–Schmidt norm in the standard orthonormal tensor basis. -/
def tensorNormSq [Fintype α] (M : (Fin d → α) → ℝ) : ℝ :=
  ∑ t, M t ^ 2

theorem eval_tensorPolynomial [Fintype α] (M : (Fin d → α) → ℝ) (u : α → ℝ) :
    MvPolynomial.eval u (tensorPolynomial M) = ∑ t, M t * ∏ i, u (t i) := by
  classical
  simp only [tensorPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [MvPolynomial.monomial_eq, map_mul, MvPolynomial.eval_C]
  congr 1
  have h := congrArg (MvPolynomial.eval u) (prod_X_eq_monomial_tupleIndex t)
  simpa [MvPolynomial.eval_monomial] using h.symm

theorem coeff_tensorPolynomial [Fintype α] (M : (Fin d → α) → ℝ) (R : α →₀ ℕ) :
    (tensorPolynomial M).coeff R = ∑ t, if tupleIndex t = R then M t else 0 := by
  classical
  simp only [tensorPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]

theorem coeff_tensorPolynomial_of_symmetric [Fintype α]
    {M : (Fin d → α) → ℝ} (hM : IsSymmetricTensor M) (t : Fin d → α) :
    (tensorPolynomial M).coeff (tupleIndex t) =
      ((tupleIndex t).multinomial : ℝ) * M t := by
  classical
  rw [coeff_tensorPolynomial]
  calc
    _ = (∑ s : Fin d → α, if tupleIndex s = tupleIndex t then (1 : ℝ) else 0) * M t := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      split_ifs with h
      · simpa using hM s t h
      · simp
    _ = _ := by rw [sum_tupleIndex_eq, tupleIndex_degree, ite_eq_left rfl]

theorem factorial_mul_multinomial (R : α →₀ ℕ) :
    R.prod (fun _ r => r.factorial) * R.multinomial =
      (R.sum (fun _ r => r)).factorial :=
  Nat.multinomial_spec R.support R

/-- Weighted coefficient energy, with the exponential-series normalization:
if the coefficient is `c_R / R!`, its contribution is `c_R² / R!`. -/
def coefficientEnergy (p : MvPolynomial α ℝ) : ℝ :=
  ∑ R ∈ p.support, p.coeff R ^ 2 * (R.prod (fun _ r => r.factorial) : ℝ)

theorem degree_of_mem_tensorPolynomial_support [Fintype α]
    (M : (Fin d → α) → ℝ) {R : α →₀ ℕ} (hR : R ∈ (tensorPolynomial M).support) :
    R.sum (fun _ r => r) = d := by
  by_contra h
  have hz : (tensorPolynomial M).coeff R = 0 := by
    rw [coeff_tensorPolynomial]
    apply Finset.sum_eq_zero
    intro t _
    rw [ite_eq_right]
    intro ht
    exact h (ht ▸ tupleIndex_degree t)
  exact (MvPolynomial.mem_support_iff.mp hR) hz

theorem tensorPolynomial_isHomogeneous [Fintype α] (M : (Fin d → α) → ℝ) :
    (tensorPolynomial M).IsHomogeneous d := by
  intro R hR
  have h := degree_of_mem_tensorPolynomial_support M (MvPolynomial.mem_support_iff.mpr hR)
  simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] using h

theorem tensorPolynomial_totalDegree_le [Fintype α] (M : (Fin d → α) → ℝ) :
    (tensorPolynomial M).totalDegree ≤ d := (tensorPolynomial_isHomogeneous M).totalDegree_le

/-- Canonical symmetric tensor of a homogeneous polynomial. For coefficients
`c_R / R!`, each entry is exactly `c_R / d!`. -/
def polynomialTensor (p : MvPolynomial α ℝ) (d : ℕ) (t : Fin d → α) : ℝ :=
  p.coeff (tupleIndex t) * ((tupleIndex t).prod (fun _ r => r.factorial) : ℝ) /
    (d.factorial : ℝ)

theorem polynomialTensor_isSymmetric (p : MvPolynomial α ℝ) (d : ℕ) :
    IsSymmetricTensor (polynomialTensor p d) := by
  intro s t h
  simp only [polynomialTensor, h]

/-- Every homogeneous polynomial is represented by its canonical symmetric tensor. -/
theorem tensorPolynomial_polynomialTensor [Fintype α] (p : MvPolynomial α ℝ)
    (hp : p.IsHomogeneous d) : tensorPolynomial (polynomialTensor p d) = p := by
  classical
  ext R
  rw [coeff_tensorPolynomial]
  have hs : (∑ t : Fin d → α, if tupleIndex t = R then polynomialTensor p d t else 0) =
      (∑ t : Fin d → α, if tupleIndex t = R then (1 : ℝ) else 0) *
        (p.coeff R * (R.prod (fun _ r => r.factorial) : ℝ) / (d.factorial : ℝ)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs with h
    · simp only [polynomialTensor, h, one_mul]
    · simp
  rw [hs, sum_tupleIndex_eq]
  by_cases hR : R.sum (fun _ r => r) = d
  · rw [ite_eq_left hR]
    have hf : (R.prod (fun _ r => r.factorial) : ℝ) * (R.multinomial : ℝ) =
        (d.factorial : ℝ) := by
      exact_mod_cast (factorial_mul_multinomial R).trans (congrArg Nat.factorial hR)
    have hd : (d.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    nlinarith [congrArg (fun x : ℝ => p.coeff R * x) hf]
  · rw [ite_eq_right hR, zero_mul]
    symm
    by_contra hc
    apply hR
    simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] using (hp hc)

/-- Equation `eq:tensor-normalization`. The identity counts every ordering,
including tuples with repeated labels. -/
theorem coefficientEnergy_tensorPolynomial [Fintype α]
    {M : (Fin d → α) → ℝ} (hM : IsSymmetricTensor M) :
    coefficientEnergy (tensorPolynomial M) = (d.factorial : ℝ) * tensorNormSq M := by
  classical
  let p := tensorPolynomial M
  have hcoeff (R : α →₀ ℕ) :
      p.coeff R ^ 2 * (R.prod (fun _ r => r.factorial) : ℝ) =
        ∑ t : Fin d → α, if tupleIndex t = R then
          p.coeff R * M t * (R.prod (fun _ r => r.factorial) : ℝ) else 0 := by
    calc
      _ = p.coeff R * (∑ t : Fin d → α, if tupleIndex t = R then M t else 0) *
          (R.prod (fun _ r => r.factorial) : ℝ) := by
        rw [← coeff_tensorPolynomial, sq]
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  unfold coefficientEnergy
  change (∑ R ∈ p.support, p.coeff R ^ 2 * (R.prod (fun _ r => r.factorial) : ℝ)) = _
  simp_rw [hcoeff]
  rw [Finset.sum_comm]
  calc
    _ = ∑ t : Fin d → α,
        p.coeff (tupleIndex t) * M t *
          ((tupleIndex t).prod (fun _ r => r.factorial) : ℝ) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_eq_single (tupleIndex t)]
      · simp
      · intro R _ hR
        exact ite_eq_right (Ne.symm hR)
      · intro ht
        simp [MvPolynomial.notMem_support_iff.mp ht]
    _ = ∑ t : Fin d → α, (d.factorial : ℝ) * M t ^ 2 := by
      apply Finset.sum_congr rfl
      intro t _
      rw [show p.coeff (tupleIndex t) =
        ((tupleIndex t).multinomial : ℝ) * M t from
          coeff_tensorPolynomial_of_symmetric hM t]
      have hf : ((tupleIndex t).prod (fun _ r => r.factorial) : ℝ) *
          ((tupleIndex t).multinomial : ℝ) = (d.factorial : ℝ) := by
        exact_mod_cast (factorial_mul_multinomial (tupleIndex t)).trans
          (congrArg Nat.factorial (tupleIndex_degree t))
      rw [← hf]
      ring
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The coefficient energy determines the Hilbert–Schmidt norm of the canonical
tensor, completing the normalization in both directions. -/
theorem factorial_mul_tensorNormSq_polynomialTensor [Fintype α]
    (p : MvPolynomial α ℝ) (hp : p.IsHomogeneous d) :
    (d.factorial : ℝ) * tensorNormSq (polynomialTensor p d) = coefficientEnergy p := by
  rw [← coefficientEnergy_tensorPolynomial (polynomialTensor_isSymmetric p d),
    tensorPolynomial_polynomialTensor p hp]

/-- Equation `eq:lift-normalization`. Symmetry is required for the equality;
it prevents replacing multiple orderings by unrelated tensor entries. -/
theorem expectation_lift_tensorPolynomial_sq
    {M : (Fin d → NonemptyCharacter n) → ℝ} (hM : IsSymmetricTensor M) :
    expectation n m (fun ω => liftPolynomial (tensorPolynomial M) ω ^ 2) =
      (d.factorial : ℝ) / (((m - 1).descFactorial d : ℕ) : ℝ) * tensorNormSq M := by
  rw [expectation_liftPolynomial_sq]
  calc
    _ = coefficientEnergy (tensorPolynomial M) /
        (((m - 1).descFactorial d : ℕ) : ℝ) := by
      unfold coefficientEnergy
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro R hR
      rw [witnessFactorial_eq_prod,
        show witnessDegree R = d from degree_of_mem_tensorPolynomial_support M hR]
      simp only [Finsupp.prod, Nat.cast_prod]
      ring
    _ = _ := by rw [coefficientEnergy_tensorPolynomial hM]; ring

/-- Cauchy–Schwarz on the orderings of a fixed multiset. -/
theorem coeff_tensorPolynomial_sq_le [Fintype α]
    (M : (Fin d → α) → ℝ) (R : α →₀ ℕ) (hR : R.sum (fun _ r => r) = d) :
    (tensorPolynomial M).coeff R ^ 2 ≤ (R.multinomial : ℝ) *
      ∑ t : Fin d → α, if tupleIndex t = R then M t ^ 2 else 0 := by
  classical
  let s : Finset (Fin d → α) := Finset.univ.filter (fun t => tupleIndex t = R)
  have hc : (s.card : ℝ) = (R.multinomial : ℝ) := by
    simpa only [s, Finset.sum_boole, hR, ite_true] using sum_tupleIndex_eq (d := d) R
  have h := sq_sum_le_card_mul_sum_sq (s := s) (f := M)
  rw [hc] at h
  simpa only [s, Finset.sum_filter, coeff_tensorPolynomial] using h

/-- Symmetrization cannot increase the Hilbert–Schmidt norm, expressed directly
as the coefficient estimate needed for arbitrary substitution tensors. -/
theorem coefficientEnergy_tensorPolynomial_le [Fintype α]
    (M : (Fin d → α) → ℝ) :
    coefficientEnergy (tensorPolynomial M) ≤ (d.factorial : ℝ) * tensorNormSq M := by
  classical
  let p := tensorPolynomial M
  calc
    _ ≤ ∑ R ∈ p.support, ∑ t : Fin d → α,
        if tupleIndex t = R then (d.factorial : ℝ) * M t ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro R hR
      have hd := degree_of_mem_tensorPolynomial_support M hR
      have hf : (R.prod (fun _ r => r.factorial) : ℝ) * (R.multinomial : ℝ) =
          (d.factorial : ℝ) := by
        exact_mod_cast (factorial_mul_multinomial R).trans (congrArg Nat.factorial hd)
      calc
        _ ≤ ((R.multinomial : ℝ) *
            ∑ t : Fin d → α, if tupleIndex t = R then M t ^ 2 else 0) *
              (R.prod (fun _ r => r.factorial) : ℝ) :=
          mul_le_mul_of_nonneg_right (coeff_tensorPolynomial_sq_le M R hd)
            (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
        _ = _ := by
          rw [mul_right_comm, mul_comm (R.multinomial : ℝ), hf, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _
          split_ifs <;> simp
    _ = ∑ t : Fin d → α, ∑ R ∈ p.support,
        if tupleIndex t = R then (d.factorial : ℝ) * M t ^ 2 else 0 :=
      Finset.sum_comm
    _ ≤ ∑ t : Fin d → α, (d.factorial : ℝ) * M t ^ 2 := by
      apply Finset.sum_le_sum
      intro t _
      rw [Finset.sum_ite_eq]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The lift bound for a tensor that has not been symmetrized. This form avoids
introducing an orthogonal-projection operator in the substitution proof. -/
theorem expectation_lift_tensorPolynomial_sq_le
    (M : (Fin d → NonemptyCharacter n) → ℝ) :
    expectation n m (fun ω => liftPolynomial (tensorPolynomial M) ω ^ 2) ≤
      (d.factorial : ℝ) / (((m - 1).descFactorial d : ℕ) : ℝ) * tensorNormSq M := by
  rw [expectation_liftPolynomial_sq]
  calc
    _ = coefficientEnergy (tensorPolynomial M) /
        (((m - 1).descFactorial d : ℕ) : ℝ) := by
      unfold coefficientEnergy
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro R hR
      rw [witnessFactorial_eq_prod,
        show witnessDegree R = d from degree_of_mem_tensorPolynomial_support M hR]
      simp only [Finsupp.prod, Nat.cast_prod]
      ring
    _ ≤ ((d.factorial : ℝ) * tensorNormSq M) /
        (((m - 1).descFactorial d : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (coefficientEnergy_tensorPolynomial_le M) (Nat.cast_nonneg _)
    _ = _ := by ring

end

end TensorLB
