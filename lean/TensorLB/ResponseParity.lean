module

public import TensorLB.SignSymmetry
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Parity of the response coefficients

Coordinate sign equivariance of the response passes to every homogeneous
Taylor polynomial. A nonzero coefficient must have exactly the target's
incidence parity.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {α : Type*} {n k : ℕ}

def scalePolynomial (p : MvPolynomial α ℝ) (s : α → ℝ) : MvPolynomial α ℝ :=
  ∑ R ∈ p.support, MvPolynomial.monomial R (p.coeff R * R.prod (fun i r => s i ^ r))

theorem coeff_scalePolynomial (p : MvPolynomial α ℝ) (s : α → ℝ) (R : α →₀ ℕ) :
    (scalePolynomial p s).coeff R = p.coeff R * R.prod (fun i r => s i ^ r) := by
  simp only [scalePolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, zero_mul]

theorem eval_scalePolynomial (p : MvPolynomial α ℝ) (s x : α → ℝ) :
    MvPolynomial.eval x (scalePolynomial p s) = MvPolynomial.eval (fun i => s i * x i) p := by
  simp only [scalePolynomial, map_sum, MvPolynomial.eval_monomial]
  rw [MvPolynomial.eval_eq]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, mul_assoc]

theorem coeff_scale_of_eval_covariant (p : MvPolynomial α ℝ) (s : α → ℝ) (c : ℝ)
    (h : ∀ x, MvPolynomial.eval (fun i => s i * x i) p = c * MvPolynomial.eval x p)
    (R : α →₀ ℕ) (hR : p.coeff R ≠ 0) : R.prod (fun i r => s i ^ r) = c := by
  have hp : scalePolynomial p s = MvPolynomial.C c * p := by
    apply MvPolynomial.funext
    intro x
    simpa only [eval_scalePolynomial, map_mul, MvPolynomial.eval_C] using h x
  have hc := congrArg (fun p : MvPolynomial α ℝ => p.coeff R) hp
  rw [coeff_scalePolynomial, MvPolynomial.coeff_C_mul] at hc
  exact mul_left_cancel₀ hR (hc.trans (mul_comm _ _))

theorem eval_responseTerm_twist (τ : ℝ) (A : Finset (Fin n)) (ε : Fin n → Bool)
    (q : ObservationIndex n k → ℝ) (d : ℕ) :
    MvPolynomial.eval (realSignTwist ε q) (responseTerm τ A d) =
      character A ε * MvPolynomial.eval q (responseTerm τ A d) := by
  simp only [eval_responseTerm]
  exact taylor_diagonal_covariant (hasFPowerSeriesAt_realResponse τ A) (realSignTwist ε)
    (character A ε) (realResponse_twist τ A ε) q d

theorem responseTerm_coeff_character (τ : ℝ) (A : Finset (Fin n)) (d : ℕ)
    (R : ObservationIndex n k →₀ ℕ) (hR : (responseTerm τ A d).coeff R ≠ 0)
    (ε : Fin n → Bool) :
    R.prod (fun I r => character I.val ε ^ r) = character A ε := by
  apply coeff_scale_of_eval_covariant (responseTerm τ A d) _ _ _ R hR
  intro q
  exact eval_responseTerm_twist τ A ε q d

/-- The number of observation incidences at one spin coordinate. -/
def incidenceCount (R : ObservationIndex n k →₀ ℕ) (i : Fin n) : ℕ :=
  R.sum (fun I r => if i ∈ I.val then r else 0)

def incidenceParity (R : ObservationIndex n k →₀ ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => incidenceCount R i % 2 = 1)

def singleFlipSigns (i : Fin n) : Fin n → Bool := fun j => if j = i then false else true

theorem character_singleFlipSigns (B : Finset (Fin n)) (i : Fin n) :
    character B (singleFlipSigns i) = if i ∈ B then -1 else 1 := by
  have hs : ∀ j, sign (singleFlipSigns i j) = if j = i then -1 else 1 := by
    intro j
    by_cases hj : j = i <;> simp [singleFlipSigns, hj, sign]
  simp only [character, hs]
  exact Finset.prod_ite_eq' B i (fun _ => (-1 : ℝ))

theorem prod_character_singleFlipSigns (R : ObservationIndex n k →₀ ℕ) (i : Fin n) :
    R.prod (fun I r => character I.val (singleFlipSigns i) ^ r) =
      (-1 : ℝ) ^ incidenceCount R i := by
  unfold Finsupp.prod incidenceCount Finsupp.sum
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro I _
  dsimp only
  rw [character_singleFlipSigns]
  split_ifs <;> simp

/-- Equation (23): only multisets with symmetric difference `A` contribute. -/
theorem responseTerm_coeff_parity (τ : ℝ) (A : Finset (Fin n)) (d : ℕ)
    (R : ObservationIndex n k →₀ ℕ) (hR : (responseTerm τ A d).coeff R ≠ 0) :
    incidenceParity R = A := by
  ext i
  simp only [incidenceParity, Finset.mem_filter, Finset.mem_univ, true_and]
  have h := responseTerm_coeff_character τ A d R hR (singleFlipSigns i)
  rw [prod_character_singleFlipSigns, character_singleFlipSigns,
    neg_one_pow_eq_pow_mod_two] at h
  have hmod : incidenceCount R i % 2 = 0 ∨ incidenceCount R i % 2 = 1 := by omega
  rcases hmod with hm | hm <;> by_cases hi : i ∈ A <;> simp_all <;> norm_num at h

theorem character_all_negative (B : Finset (Fin n)) :
    character B (fun _ => false) = (-1 : ℝ) ^ B.card := by
  simp [character, sign]

theorem observationCharacter_all_negative (I : ObservationIndex n k) :
    character I.val (fun _ => false) = (-1 : ℝ) ^ k := by
  rw [character_all_negative, neg_one_pow_eq_pow_mod_two,
    I.property.2.2, ← neg_one_pow_eq_pow_mod_two]

theorem responseTerm_coeff_degree_parity (τ : ℝ) (A : Finset (Fin n)) (d : ℕ)
    (R : ObservationIndex n k →₀ ℕ) (hR : (responseTerm τ A d).coeff R ≠ 0) :
    (k * d) % 2 = A.card % 2 := by
  have hdeg : R.sum (fun _ r => r) = d := by
    have h := responseTerm_isHomogeneous (k := k) τ A d hR
    simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] using h
  have h := responseTerm_coeff_character τ A d R hR (fun _ => false)
  simp only [observationCharacter_all_negative] at h
  rw [character_all_negative] at h
  have hp : R.prod (fun _ r => ((-1 : ℝ) ^ k) ^ r) = (-1 : ℝ) ^ (k * d) := by
    simp only [← pow_mul, Finsupp.prod, Finset.prod_pow_eq_pow_sum]
    rw [← Finset.mul_sum]
    exact congrArg (fun r => (-1 : ℝ) ^ (k * r)) hdeg
  rw [hp, neg_one_pow_eq_pow_mod_two (k * d), neg_one_pow_eq_pow_mod_two A.card] at h
  have hl : (k * d) % 2 = 0 ∨ (k * d) % 2 = 1 := by omega
  have hr : A.card % 2 = 0 ∨ A.card % 2 = 1 := by omega
  rcases hl with hl | hl <;> rcases hr with hr | hr
  · rw [hl, hr]
  · norm_num [hl, hr] at h
  · norm_num [hl, hr] at h
  · rw [hl, hr]

/-- Cubic singleton responses have no even-degree Taylor terms. -/
theorem cubic_responseTerm_even_eq_zero (τ : ℝ) (A : Finset (Fin n)) (hA : A.card = 1)
    (d : ℕ) (hd : d % 2 = 0) : responseTerm (k := 3) τ A d = 0 := by
  apply MvPolynomial.ext
  intro R
  change (responseTerm (k := 3) τ A d).coeff R = 0
  by_contra hR
  have h := responseTerm_coeff_degree_parity τ A d R hR
  simp [Nat.mul_mod, hd, hA] at h

end

end TensorLB
