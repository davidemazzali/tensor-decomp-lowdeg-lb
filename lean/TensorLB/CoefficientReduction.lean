module

public import TensorLB.ResponseJets
public import TensorLB.ResponseParity
public import TensorLB.WitnessEstimate

/-!
# Reduction to the coefficient energy of the actual response

The response, homogeneous polynomial terms, Taylor identity, substitution norm,
moment-matching witness, and final rank arithmetic have all been constructed.
This module isolates the remaining quantitative coefficient estimate.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

/-- The absorbed coefficient estimate (32), for the response defined from the
local analytic inverse. The constant must be uniform in dimension and degree. -/
def UniformResponseEnergy (τ B : ℝ) : Prop :=
  ∀ n k d : ℕ, 4 ≤ n → 1 ≤ d → (k = 3 ∨ k = 4) → d ^ 3 ≤ n →
    ∀ A : Finset (Fin n), admissibleTarget n k A →
      coefficientEnergy (responseTerm (k := k) τ A d) ≤
        Real.rpow (n : ℝ) (-((A.card : ℝ) / 2)) * (B * rankScale n d k) ^ d

theorem uniformWitnessEstimates_of_energy {τ B : ℝ} (hB : 0 < B)
    (he : UniformResponseEnergy τ B) : UniformWitnessEstimates τ B := by
  apply uniformWitnessEstimates_of_response hB
  intro n m D k hn hm hD hk hdeg hN A hA
  have hA0 : A.Nonempty := by
    apply Finset.card_pos.mp
    unfold admissibleTarget at hA
    omega
  refine ⟨responseTerm τ A, ?_, ?_, ?_⟩
  · intro d _ _
    exact responseTerm_isHomogeneous τ A d
  · intro d hd hdD
    exact he n k d hn hd hk ((Nat.pow_le_pow_left hdD 3).trans hdeg) A hA
  · exact responseTerm_jets τ A hA0

/-- The full challenge statement follows from the uniform coefficient bound
alone; no Taylor identity or substitution bound is left as a hypothesis. -/
theorem main_of_uniformResponseEnergy
    (h : ∀ τ : ℝ, 1 < τ → ∃ B : ℝ, 0 < B ∧ UniformResponseEnergy τ B) :
    ∀ τ : ℝ, 1 < τ →
      ∃ C : ℝ, 0 < C ∧
        ∀ n m D k : ℕ,
          4 ≤ n → 2 ≤ m → 1 ≤ D → (k = 3 ∨ k = 4) →
          D ^ 3 ≤ n →
          C * Real.rpow (n : ℝ) ((k : ℝ) / 2) *
            Real.rpow (D : ℝ) ((k : ℝ) / 2 - 1) ≤ (m : ℝ) →
          ∀ A : Finset (Fin n), admissibleTarget n k A →
            correlation n m k D τ A ^ 2 ≤
                Real.rpow (n : ℝ) (-((A.card : ℝ) / 2)) ∧
              1 - Real.rpow (n : ℝ) (-((A.card : ℝ) / 2)) ≤
                mmse n m k D τ A := by
  apply main_of_uniformWitnessEstimates
  intro τ hτ
  obtain ⟨B, hB, he⟩ := h τ hτ
  exact ⟨B, hB, uniformWitnessEstimates_of_energy hB he⟩

end TensorLB
