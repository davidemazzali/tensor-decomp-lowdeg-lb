module

public import TensorLB.CoefficientReduction
public import TensorLB.CoverBound

/-!
# Reduction to the uniform analytic response lemma

Cauchy estimates, parity, weighted even-cover counting, and the degree
restriction now prove the coefficient-energy estimate from a bounded analytic
extension of the response on a dimension-independent local ball.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped Topology

noncomputable section

/-- The analytic lemma of manuscript Section 3. A single positive radius works
for every dimension, tensor order, and admissible target. -/
def UniformBoundedResponse (τ ρ : ℝ) : Prop :=
  ∀ n k : ℕ, 4 ≤ n → (k = 3 ∨ k = 4) →
    ∀ A : Finset (Fin n), admissibleTarget n k A →
      ∃ f : ComplexParameters n k → ℂ,
        AnalyticOnNhd ℂ f {x | localNorm x ≤ ρ} ∧
        (∀ x, localNorm x ≤ ρ → ‖f x‖ ≤ 1) ∧
        f =ᶠ[𝓝 0] complexResponse τ A

def responseEnergyConstant (ρ : ℝ) : ℝ := (ρ⁻¹ ^ 2 * coverBoundConstant) * Real.exp 4

theorem responseEnergyConstant_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < responseEnergyConstant ρ := by
  have hc := coverBoundConstant_pos
  unfold responseEnergyConstant
  positivity

theorem uniformResponseEnergy_of_boundedResponse {τ ρ : ℝ} (hρ : 0 < ρ)
    (h : UniformBoundedResponse τ ρ) : UniformResponseEnergy τ (responseEnergyConstant ρ) := by
  intro n k d hn hd hk hdeg A hA
  have hn0 : 0 < n := by omega
  have hA0 : A.Nonempty := Finset.card_pos.mp (by unfold admissibleTarget at hA; omega)
  have ha : A.card ≤ 4 := by unfold admissibleTarget at hA; omega
  have hakd : A.card ≤ k * d := by
    have hk3 : 3 ≤ k := by omega
    unfold admissibleTarget at hA
    rcases hA with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ <;> omega
  have hC0 : 0 ≤ ρ⁻¹ ^ 2 * coverBoundConstant :=
    mul_nonneg (sq_nonneg _) coverBoundConstant_pos.le
  by_cases hpar : (k * d) % 2 = A.card % 2
  · let L := (k * d - A.card) / 2
    have hL : 2 * L + A.card = k * d := by dsimp [L]; omega
    obtain ⟨f, hf, hb, he⟩ := h n k hn hk A hA
    have hec := responseTerm_energy_le_weightedCoverCount (d := d) τ A hρ hf hb he
    have hc := weightedCoverCount_div_factorial_le A hn0 hk hd hA0 ha hL
    unfold responseEnergyConstant
    rw [← neg_div]
    apply absorb_energy_correction (a := (A.card : ℝ)) hn0 hdeg hC0
    calc
      _ ≤ ρ⁻¹ ^ (2 * d) * (weightedCoverCount n k d A / d.factorial) := by
        convert! hec using 1
        ring
      _ ≤ ρ⁻¹ ^ (2 * d) *
          ((n : ℝ) ^ (-((A.card : ℝ) / 2)) *
            (coverBoundConstant * rankScale n d k) ^ d *
              Real.exp (4 * (d : ℝ) ^ 4 / n)) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by
        change ρ⁻¹ ^ (2 * d) *
          (Real.rpow (n : ℝ) (-((A.card : ℝ) / 2)) *
            (coverBoundConstant * rankScale n d k) ^ d *
              Real.exp (4 * (d : ℝ) ^ 4 / n)) = _
        rw [pow_mul]
        simp only [mul_pow, neg_div]
        ring
  · have hz : responseTerm (k := k) τ A d = 0 := by
      apply MvPolynomial.ext
      intro R
      change (responseTerm τ A d).coeff R = 0
      by_contra hc
      exact hpar (responseTerm_coeff_degree_parity τ A d R hc)
    rw [hz]
    have hB := responseEnergyConstant_pos hρ
    have hs := rankScale_nonneg n d k
    simp only [coefficientEnergy, MvPolynomial.support_zero, Finset.sum_empty]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (pow_nonneg (mul_nonneg hB.le hs) _)

/-- All combinatorial, Taylor, witness, and rank steps are discharged. -/
theorem main_of_uniformBoundedResponse
    (h : ∀ τ : ℝ, 1 < τ → ∃ ρ : ℝ, 0 < ρ ∧ UniformBoundedResponse τ ρ) :
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
  apply main_of_uniformResponseEnergy
  intro τ hτ
  obtain ⟨ρ, hρ, hb⟩ := h τ hτ
  exact ⟨responseEnergyConstant ρ, responseEnergyConstant_pos hρ,
    uniformResponseEnergy_of_boundedResponse hρ hb⟩

end

end TensorLB
