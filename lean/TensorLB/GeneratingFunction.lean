module

public import TensorLB.Observations
public import TensorLB.PolynomialLift
public import TensorLB.ProductExpectation
public import Mathlib.Analysis.SpecialFunctions.Exp

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exponential moments of the Fourier witnesses

The real generating functions satisfy the identities underlying
`eq:moment-matching`. The factorization is exact, and averaging over
embeddings is legitimate when the hidden degree fits in the background.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n m k : ℕ} {ι : Type*} [Fintype ι]

/-- The interaction Hamiltonian for one Rademacher component. -/
def interactionExponent (t : ObservationIndex n k → ℝ) (z : Fin n → Bool) : ℝ :=
  ∑ I, t I * character I.val z

/-- The one-component partition function `F(t)`. -/
def partitionFunction (t : ObservationIndex n k → ℝ) : ℝ :=
  𝔼 z : Fin n → Bool, Real.exp (interactionExponent t z)

/-- The normalized exponential tilt, of uniform mean one. -/
def tiltedWeight (t : ObservationIndex n k → ℝ) (z : Fin n → Bool) : ℝ :=
  Real.exp (interactionExponent t z) / partitionFunction t

/-- The character moment `φ_B(t)`; hidden characters need not be observations. -/
def tiltedMoment (t : ObservationIndex n k → ℝ) (B : Finset (Fin n)) : ℝ :=
  (𝔼 z : Fin n → Bool, character B z * Real.exp (interactionExponent t z)) /
    partitionFunction t

theorem partitionFunction_pos (t : ObservationIndex n k → ℝ) :
    0 < partitionFunction t :=
  Finset.expect_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem expect_tiltedWeight (t : ObservationIndex n k → ℝ) :
    (𝔼 z : Fin n → Bool, tiltedWeight t z) = 1 := by
  unfold tiltedWeight
  rw [← Finset.expect_div]
  exact div_self (ne_of_gt (partitionFunction_pos t))

theorem expect_character_mul_tiltedWeight (t : ObservationIndex n k → ℝ)
    (B : Finset (Fin n)) :
    (𝔼 z : Fin n → Bool, character B z * tiltedWeight t z) = tiltedMoment t B := by
  simp only [tiltedWeight, tiltedMoment, ← mul_div_assoc, ← Finset.expect_div]

/-- The full observation exponential. -/
def observationExponential (τ : ℝ) (t : ObservationIndex n k → ℝ)
    (ω : Sample n m) : ℝ :=
  Real.exp (∑ I, t I * reducedObservation n m k τ ω I)

theorem observationExponential_factor (τ : ℝ) (t : ObservationIndex n k → ℝ)
    (ω : Sample n m) :
    observationExponential τ t ω =
      Real.exp (interactionExponent (fun I => τ * t I) ω.1) *
        ∏ j, Real.exp (interactionExponent t (ω.2 j)) := by
  have hex : (∑ I, t I * reducedObservation n m k τ ω I) =
      interactionExponent (fun I => τ * t I) ω.1 +
        ∑ j, interactionExponent t (ω.2 j) := by
    unfold interactionExponent reducedObservation character
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro I _
    ring
  rw [observationExponential, hex, Real.exp_add, Real.exp_sum]

theorem observationExponential_eq_tilted (τ : ℝ) (t : ObservationIndex n k → ℝ)
    (ω : Sample n m) :
    observationExponential τ t ω = partitionFunction t ^ (m - 1) *
      (Real.exp (interactionExponent (fun I => τ * t I) ω.1) *
        ∏ j, tiltedWeight t (ω.2 j)) := by
  rw [observationExponential_factor]
  simp only [tiltedWeight, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have h := ne_of_gt (partitionFunction_pos t)
  field_simp

/-- Each distinct-component placement has the same tilted expectation. -/
theorem expectation_placedCharacter_exponential
    (B : ι → NonemptyCharacter n) (e : ι ↪ Fin (m - 1))
    (τ : ℝ) (t : ObservationIndex n k → ℝ) :
    expectation n m (fun ω => placedCharacter B e ω * observationExponential τ t ω) =
      partitionFunction (fun I => τ * t I) * partitionFunction t ^ (m - 1) *
        ∏ i, tiltedMoment t (B i).val := by
  simp_rw [observationExponential_eq_tilted]
  calc
    _ = partitionFunction t ^ (m - 1) *
        expectation n m (fun ω =>
          Real.exp (interactionExponent (fun I => τ * t I) ω.1) *
          ((∏ i, character (B i).val (ω.2 (e i))) * ∏ j, tiltedWeight t (ω.2 j))) := by
      rw [← expectation_const_mul]
      apply expectation_congr
      intro ω
      unfold placedCharacter
      ring
    _ = _ := by
      rw [expectation_separated
        (fun z => Real.exp (interactionExponent (fun I => τ * t I) z))
        (fun z => (∏ i, character (B i).val (z (e i))) * ∏ j, tiltedWeight t (z j)),
        expect_pi_prod_mul_embedding e (fun i z => character (B i).val z)
          (tiltedWeight t) (expect_tiltedWeight t)]
      simp only [expect_character_mul_tiltedWeight, partitionFunction]
      ring

/-- The first identity in equation (35), for an ordered enumeration. -/
theorem expectation_orderedWitness_exponential (B : ι → NonemptyCharacter n)
    (hdegree : Fintype.card ι ≤ m - 1) (τ : ℝ) (t : ObservationIndex n k → ℝ) :
    expectation n m (fun ω => orderedWitness B ω * observationExponential τ t ω) =
      partitionFunction (fun I => τ * t I) * partitionFunction t ^ (m - 1) *
        ∏ i, tiltedMoment t (B i).val := by
  simp only [orderedWitness, div_mul_eq_mul_div, Finset.sum_mul, expectation_div_const,
    expectation_sum, expectation_placedCharacter_exponential, Finset.sum_const,
    Finset.card_univ, Fintype.card_embedding_eq, Fintype.card_fin, nsmul_eq_mul]
  have h : (((m - 1).descFactorial (Fintype.card ι) : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr hdegree))
  field_simp

/-- Equation (35) for the multiset-indexed witness. -/
theorem expectation_monomialWitness_exponential (R : NonemptyCharacter n →₀ ℕ)
    (hdegree : witnessDegree R ≤ m - 1) (τ : ℝ) (t : ObservationIndex n k → ℝ) :
    expectation n m (fun ω => monomialWitness R ω * observationExponential τ t ω) =
      partitionFunction (fun I => τ * t I) * partitionFunction t ^ (m - 1) *
        R.prod (fun B r => tiltedMoment t B.val ^ r) := by
  simp only [monomialWitness]
  rw [expectation_orderedWitness_exponential (witnessLabel R)
    (by simpa only [card_witnessSlot] using hdegree)]
  congr 1
  simp only [WitnessSlot, witnessLabel, Fintype.prod_sigma, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  exact (Finsupp.prod_fintype R _ (fun _ => pow_zero _)).symm

/-- The target generating function, the second identity in equation (35). -/
theorem expectation_target_exponential (A : Finset (Fin n))
    (τ : ℝ) (t : ObservationIndex n k → ℝ) :
    expectation n m (fun ω => target n m A ω * observationExponential τ t ω) =
      partitionFunction (fun I => τ * t I) * partitionFunction t ^ (m - 1) *
        tiltedMoment (fun I => τ * t I) A := by
  simp_rw [observationExponential_factor]
  calc
    _ = expectation n m (fun ω =>
        (character A ω.1 * Real.exp (interactionExponent (fun I => τ * t I) ω.1)) *
          ∏ j, Real.exp (interactionExponent t (ω.2 j))) :=
      expectation_congr (fun _ => by unfold target character; ring)
    _ = (𝔼 z, character A z * Real.exp (interactionExponent (fun I => τ * t I) z)) *
        partitionFunction t ^ (m - 1) := by
      rw [expectation_component_prod
        (fun z => character A z * Real.exp (interactionExponent (fun I => τ * t I) z))
        (fun _ z => Real.exp (interactionExponent t z))]
      simp only [partitionFunction, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = _ := by
      unfold tiltedMoment
      have h := ne_of_gt (partitionFunction_pos (fun I => τ * t I))
      field_simp

/-- Linear extension of equation (35) to every polynomial whose hidden degree
fits in the background. This is the generating-function input to moment matching. -/
theorem expectation_liftPolynomial_exponential
    (p : MvPolynomial (NonemptyCharacter n) ℝ) (hp : p.totalDegree ≤ m - 1)
    (τ : ℝ) (t : ObservationIndex n k → ℝ) :
    expectation n m (fun ω => liftPolynomial p ω * observationExponential τ t ω) =
      partitionFunction (fun I => τ * t I) * partitionFunction t ^ (m - 1) *
        MvPolynomial.eval (fun B => tiltedMoment t B.val) p := by
  simp only [liftPolynomial_eq_sum, Finset.sum_mul, expectation_finset_sum]
  rw [MvPolynomial.eval_eq]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R hR
  calc
    _ = p.coeff R * expectation n m
        (fun ω => monomialWitness R ω * observationExponential τ t ω) := by
      rw [← expectation_const_mul]
      exact expectation_congr (fun _ => mul_assoc _ _ _)
    _ = _ := by
      rw [expectation_monomialWitness_exponential R ((MvPolynomial.le_totalDegree hR).trans hp)]
      unfold Finsupp.prod
      ring

end

end TensorLB
