module

public import TensorLB.GeneratingFunction
public import TensorLB.MomentMatching
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Extracting moment matching from exponential Taylor coefficients

All averages are finite. Differentiation therefore commutes with the average,
and the order-`d` derivative in an arbitrary direction is the degree-`d` moment
of the corresponding linear form. The multinomial argument in `MomentMatching`
then recovers all mixed moments, including the constant term.
-/

set_option autoImplicit false

public section

namespace TensorLB

open scoped BigOperators

variable {n m k D : ℕ} {τ : ℝ}

theorem iteratedDeriv_expectation_exp
    (W L : Sample n m → ℝ) (d : ℕ) (s : ℝ) :
    iteratedDeriv d (fun x => expectation n m (fun ω => W ω * Real.exp (L ω * x))) s =
      expectation n m (fun ω => W ω * L ω ^ d * Real.exp (L ω * s)) := by
  unfold expectation
  rw [iteratedDeriv_div_const]
  rw [iteratedDeriv_fun_sum (fun ω _ => by fun_prop)]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_exp_const_mul, mul_assoc]

/-- Directional derivatives of the observation exponential are moments of
linear forms in the observations, with no factorial left over. -/
theorem iteratedDeriv_observationExponential_zero
    (W : Sample n m → ℝ) (t : ObservationIndex n k → ℝ) (d : ℕ) :
    iteratedDeriv d (fun s => expectation n m
      (fun ω => W ω * observationExponential τ (fun I => s * t I) ω)) 0 =
        expectation n m (fun ω => W ω * (∑ I, t I * reducedObservation n m k τ ω I) ^ d) := by
  have hex (s : ℝ) (ω : Sample n m) :
      observationExponential τ (fun I => s * t I) ω =
        Real.exp ((∑ I, t I * reducedObservation n m k τ ω I) * s) := by
    unfold observationExponential
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro I _
    ring
  simp_rw [hex]
  rw [iteratedDeriv_expectation_exp]
  simp only [mul_zero, Real.exp_zero, mul_one]

/-- Equality of exponential jets through degree `D` implies the full
moment-matching property; testing only coordinate axes would not suffice. -/
theorem reducedMomentMatching_of_exponential_jets
    (W : Sample n m → ℝ) (A : Finset (Fin n))
    (h : ∀ d ≤ D, ∀ t : ObservationIndex n k → ℝ,
      iteratedDeriv d (fun s => expectation n m
        (fun ω => W ω * observationExponential τ (fun I => s * t I) ω)) 0 =
      iteratedDeriv d (fun s => expectation n m
        (fun ω => target n m A ω * observationExponential τ (fun I => s * t I) ω)) 0) :
    IsReducedMomentMatchingWitness n m k D τ A W := by
  apply reducedMomentMatching_of_linearForm_moments
  intro d hd t
  simpa only [iteratedDeriv_observationExponential_zero] using h d hd t

/-- A polynomial identity to order `D` after substitution of the tilted moments
gives a witness. The common partition factors are retained in this interface,
so it does not assume an unproved rule for truncated analytic division. -/
theorem reducedMomentMatching_lift_of_tilted_jets
    (p : MvPolynomial (NonemptyCharacter n) ℝ) (hp : p.totalDegree ≤ m - 1)
    (A : Finset (Fin n))
    (h : ∀ d ≤ D, ∀ t : ObservationIndex n k → ℝ,
      iteratedDeriv d (fun s =>
        partitionFunction (fun I => τ * (s * t I)) *
          partitionFunction (fun I => s * t I) ^ (m - 1) *
            MvPolynomial.eval (fun B => tiltedMoment (fun I => s * t I) B.val) p) 0 =
      iteratedDeriv d (fun s =>
        partitionFunction (fun I => τ * (s * t I)) *
          partitionFunction (fun I => s * t I) ^ (m - 1) *
            tiltedMoment (fun I => τ * (s * t I)) A) 0) :
    IsReducedMomentMatchingWitness n m k D τ A (liftPolynomial p) := by
  apply reducedMomentMatching_of_exponential_jets
  intro d hd t
  simpa only [expectation_liftPolynomial_exponential p hp, expectation_target_exponential]
    using h d hd t

end TensorLB
