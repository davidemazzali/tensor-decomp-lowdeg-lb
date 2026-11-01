module

public import TensorLB.Observations
public import TensorLB.ExpectationSum
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.MvPolynomial.Funext

import Mathlib.Tactic.Ring

/-!
# Checking moment matching on linear forms

Equality of all moments through degree `D` of every linear form in the
observations implies equality against every polynomial of total degree at most
`D`. Polynomial extensionality and the multinomial formula prove this without
any assumptions about linear independence of observable monomials.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {σ : Type*} [Fintype σ] {n m k D : ℕ} {τ : ℝ}

/-- The moment of an arbitrary linear form, viewed as a polynomial in its
coefficients. Its degree-`R` coefficient extracts the corresponding mixed moment. -/
def momentPolynomial (Y : Sample n m → σ → ℝ) (W : Sample n m → ℝ)
    (d : ℕ) : MvPolynomial σ ℝ :=
  ∑ ω, (W ω / (Fintype.card (Sample n m) : ℝ)) •
    (∑ i, Y ω i • MvPolynomial.X i) ^ d

theorem eval_momentPolynomial (Y : Sample n m → σ → ℝ) (W : Sample n m → ℝ)
    (d : ℕ) (t : σ → ℝ) :
    MvPolynomial.eval t (momentPolynomial Y W d) =
      expectation n m (fun ω => W ω * (∑ i, t i * Y ω i) ^ d) := by
  simp only [momentPolynomial, map_sum, MvPolynomial.smul_eq_C_mul, map_mul,
    MvPolynomial.eval_C, map_pow, MvPolynomial.eval_X, expectation,
    div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  have h : (∑ i, Y ω i * t i) = ∑ i, t i * Y ω i := by
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [h]
  ring

theorem coeff_momentPolynomial (Y : Sample n m → σ → ℝ) (W : Sample n m → ℝ)
    (d : ℕ) (R : σ →₀ ℕ) (hR : R.sum (fun _ r => r) = d) :
    (momentPolynomial Y W d).coeff R = (R.multinomial : ℝ) *
      expectation n m (fun ω => W ω * R.prod (fun i r => Y ω i ^ r)) := by
  simp only [momentPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_linearCombination_X_pow_of_fintype, hR, ite_true,
    smul_eq_mul, expectation, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

omit [Fintype σ] in
theorem multinomial_ne_zero (R : σ →₀ ℕ) : R.multinomial ≠ 0 := by
  have h := Nat.multinomial_spec R.support R
  change R.prod (fun _ r => r.factorial) * R.multinomial =
    (R.sum (fun _ r => r)).factorial at h
  intro hz
  rw [hz, mul_zero] at h
  exact Nat.factorial_ne_zero _ h.symm

/-- Linear-form moment equality extracts each mixed moment of that degree. -/
theorem monomial_moment_eq_of_linearForm_moments
    (Y : Sample n m → σ → ℝ) (W V : Sample n m → ℝ) (d : ℕ)
    (h : ∀ t : σ → ℝ,
      expectation n m (fun ω => W ω * (∑ i, t i * Y ω i) ^ d) =
        expectation n m (fun ω => V ω * (∑ i, t i * Y ω i) ^ d))
    (R : σ →₀ ℕ) (hR : R.sum (fun _ r => r) = d) :
    expectation n m (fun ω => W ω * R.prod (fun i r => Y ω i ^ r)) =
      expectation n m (fun ω => V ω * R.prod (fun i r => Y ω i ^ r)) := by
  have hp : momentPolynomial Y W d = momentPolynomial Y V d := by
    apply MvPolynomial.funext
    intro t
    simpa only [eval_momentPolynomial] using h t
  have hc := congrArg (fun p : MvPolynomial σ ℝ => p.coeff R) hp
  rw [coeff_momentPolynomial Y W d R hR, coeff_momentPolynomial Y V d R hR] at hc
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (multinomial_ne_zero R)) hc

omit [Fintype σ] in
/-- Testing monomials suffices even when estimators mix degrees and their
evaluated monomials have linear dependencies. -/
theorem polynomial_moment_eq_of_monomial_moments
    (Y : Sample n m → σ → ℝ) (W V : Sample n m → ℝ)
    (h : ∀ R : σ →₀ ℕ, R.sum (fun _ r => r) ≤ D →
      expectation n m (fun ω => W ω * R.prod (fun i r => Y ω i ^ r)) =
        expectation n m (fun ω => V ω * R.prod (fun i r => Y ω i ^ r)))
    (p : MvPolynomial σ ℝ) (hp : p.totalDegree ≤ D) :
    expectation n m (fun ω => W ω * MvPolynomial.eval (Y ω) p) =
      expectation n m (fun ω => V ω * MvPolynomial.eval (Y ω) p) := by
  simp only [MvPolynomial.eval_eq, Finset.mul_sum, expectation_finset_sum]
  apply Finset.sum_congr rfl
  intro R hR
  calc
    _ = p.coeff R * expectation n m
        (fun ω => W ω * R.prod (fun i r => Y ω i ^ r)) := by
      rw [← expectation_const_mul]
      apply expectation_congr
      intro ω
      unfold Finsupp.prod
      ring
    _ = p.coeff R * expectation n m
        (fun ω => V ω * R.prod (fun i r => Y ω i ^ r)) := by
      rw [h R ((MvPolynomial.le_totalDegree hR).trans hp)]
    _ = _ := by
      rw [← expectation_const_mul]
      apply expectation_congr
      intro ω
      unfold Finsupp.prod
      ring

/-- A convenient interface for Taylor coefficients of the exponential moment:
the order-`d` directional derivative at zero is precisely the moment tested here. -/
theorem reducedMomentMatching_of_linearForm_moments
    (W : Sample n m → ℝ) (A : Finset (Fin n))
    (h : ∀ d ≤ D, ∀ t : ObservationIndex n k → ℝ,
      expectation n m (fun ω => W ω * (∑ I, t I * reducedObservation n m k τ ω I) ^ d) =
        expectation n m (fun ω => target n m A ω *
          (∑ I, t I * reducedObservation n m k τ ω I) ^ d)) :
    IsReducedMomentMatchingWitness n m k D τ A W := by
  intro p hp
  apply polynomial_moment_eq_of_monomial_moments (reducedObservation n m k τ)
    W (target n m A) _ p hp
  intro R hR
  exact monomial_moment_eq_of_linearForm_moments _ _ _ _ (h _ hR) R rfl

end

end TensorLB
