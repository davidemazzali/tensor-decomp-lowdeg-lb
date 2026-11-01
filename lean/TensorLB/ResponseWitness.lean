module

public import TensorLB.ConnectedSubstitution
public import TensorLB.ExponentialMatching

/-!
# Witness associated with a truncated response

Given the homogeneous polynomials of a response, substitute the connected
coordinates and lift the resulting finite polynomial. This module checks the
degree accounting and reduces moment matching to the response Taylor identity.
The response coefficients and their uniform estimates are separate obligations.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators

noncomputable section

variable {n m k D : ℕ} {τ : ℝ}

/-- The polynomial `P_{A,D}` of equation (38), once its response terms are supplied. -/
def responsePolynomial (q : ℕ → ObservationPolynomial n k) (D : ℕ) :
    MvPolynomial (NonemptyCharacter n) ℝ :=
  ∑ d ∈ Finset.range D, substituteConnected (q (d + 1))

/-- The witness `W_{A,D}` associated with the truncated response. -/
def responseWitness (q : ℕ → ObservationPolynomial n k) (D : ℕ) : Sample n m → ℝ :=
  liftPolynomial (responsePolynomial q D)

theorem responsePolynomial_totalDegree_le (q : ℕ → ObservationPolynomial n k)
    (hq : ∀ d, 1 ≤ d → d ≤ D → (q d).totalDegree ≤ d) :
    (responsePolynomial q D).totalDegree ≤ D * substitutionDegree k := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  have hdD : d + 1 ≤ D := Finset.mem_range.mp hd
  exact (substituteConnected_totalDegree_le _).trans
    (Nat.mul_le_mul_right _ ((hq _ (by omega) hdD).trans hdD))

theorem responsePolynomial_degree_le_background (q : ℕ → ObservationPolynomial n k)
    (hq : ∀ d, 1 ≤ d → d ≤ D → (q d).totalDegree ≤ d) (hN : 6 * D ≤ m - 1) :
    (responsePolynomial q D).totalDegree ≤ m - 1 := by
  apply (responsePolynomial_totalDegree_le q hq).trans
  have hs : substitutionDegree k ≤ 3 := by unfold substitutionDegree; split <;> decide
  exact (Nat.mul_le_mul_left D hs).trans (by omega)

theorem responseWitness_eq_sum (q : ℕ → ObservationPolynomial n k) (ω : Sample n m) :
    responseWitness q D ω =
      ∑ d ∈ Finset.range D, liftPolynomial (substituteConnected (q (d + 1))) ω :=
  liftPolynomial_finset_sum _ _ _

theorem eval_responsePolynomial (q : ℕ → ObservationPolynomial n k)
    (t : ObservationIndex n k → ℝ) :
    MvPolynomial.eval (fun B => tiltedMoment t B.val) (responsePolynomial q D) =
      ∑ d ∈ Finset.range D, MvPolynomial.eval (connectedCoordinate t) (q (d + 1)) := by
  simp only [responsePolynomial, map_sum, eval_substituteConnected]

/-- The Taylor identity of the response is sufficient for moment matching of
the explicit lifted polynomial. The sum includes exactly degrees one through `D`. -/
theorem responseWitness_momentMatching (q : ℕ → ObservationPolynomial n k)
    (hq : ∀ d, 1 ≤ d → d ≤ D → (q d).totalDegree ≤ d) (hN : 6 * D ≤ m - 1)
    (A : Finset (Fin n))
    (hjet : ∀ d ≤ D, ∀ t : ObservationIndex n k → ℝ,
      iteratedDeriv d (fun s =>
        partitionFunction (fun I => τ * (s * t I)) *
          partitionFunction (fun I => s * t I) ^ (m - 1) *
            (∑ r ∈ Finset.range D,
              MvPolynomial.eval (connectedCoordinate (fun I => s * t I)) (q (r + 1)))) 0 =
      iteratedDeriv d (fun s =>
        partitionFunction (fun I => τ * (s * t I)) *
          partitionFunction (fun I => s * t I) ^ (m - 1) *
            tiltedMoment (fun I => τ * (s * t I)) A) 0) :
    IsReducedMomentMatchingWitness n m k D τ A (responseWitness q D) := by
  apply reducedMomentMatching_lift_of_tilted_jets (responsePolynomial q D)
    (responsePolynomial_degree_le_background q hq hN) A
  simpa only [eval_responsePolynomial] using hjet

end

end TensorLB
