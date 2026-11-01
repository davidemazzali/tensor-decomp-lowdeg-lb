module

public import TensorLB.CauchyResponse

/-!
# Reduction of coefficient energy to weighted even covers

The factorial normalization converts the polynomial energy into a sum over
ordered observation tuples. Parity removes all tuples with the wrong boundary.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical Topology

noncomputable section

variable {α : Type*} [Fintype α] {d n k : ℕ}

theorem coefficientEnergy_eq_ordered_sum (p : MvPolynomial α ℝ) (hp : p.IsHomogeneous d) :
    coefficientEnergy p = (∑ t : Fin d → α,
      (p.coeff (tupleIndex t) * ((tupleIndex t).prod (fun _ r => r.factorial) : ℝ)) ^ 2) /
        d.factorial := by
  rw [← factorial_mul_tensorNormSq_polynomialTensor p hp, tensorNormSq,
    Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  unfold polynomialTensor
  have hd : (d.factorial : ℝ) ≠ 0 := by positivity
  field_simp

def incidenceWeight (R : ObservationIndex n k →₀ ℕ) : ℝ :=
  ∏ i : Fin n, (incidenceCount R i : ℝ) ^ (2 * incidenceCount R i)

def weightedCoverCount (n k d : ℕ) (A : Finset (Fin n)) : ℝ :=
  ∑ t : Fin d → ObservationIndex n k,
    if incidenceParity (tupleIndex t) = A then incidenceWeight (tupleIndex t) else 0

theorem incidenceWeight_nonneg (R : ObservationIndex n k →₀ ℕ) : 0 ≤ incidenceWeight R :=
  Finset.prod_nonneg (fun i _ => by positivity)

theorem incidenceWeight_eq_sq (R : ObservationIndex n k →₀ ℕ) :
    incidenceWeight R = (∏ i : Fin n, (incidenceCount R i : ℝ) ^ incidenceCount R i) ^ 2 := by
  rw [← Finset.prod_pow]
  simp only [incidenceWeight, ← pow_mul, Nat.mul_comm 2]

theorem coefficientEnergy_le_weightedCoverCount (p : ObservationPolynomial n k)
    (hp : p.IsHomogeneous d) (A : Finset (Fin n)) {ρ : ℝ}
    (hpar : ∀ R, p.coeff R ≠ 0 → incidenceParity R = A)
    (hb : ∀ t : Fin d → ObservationIndex n k,
      |p.coeff (tupleIndex t) * ((tupleIndex t).prod (fun _ r => r.factorial) : ℝ)| ≤
        ρ⁻¹ ^ d * ∏ i : Fin n,
          (incidenceCount (tupleIndex t) i : ℝ) ^ incidenceCount (tupleIndex t) i) :
    coefficientEnergy p ≤ ρ⁻¹ ^ (2 * d) / d.factorial * weightedCoverCount n k d A := by
  rw [coefficientEnergy_eq_ordered_sum p hp]
  have hs : (∑ t : Fin d → ObservationIndex n k,
      (p.coeff (tupleIndex t) * ((tupleIndex t).prod (fun _ r => r.factorial) : ℝ)) ^ 2) ≤
      ρ⁻¹ ^ (2 * d) * weightedCoverCount n k d A := by
    rw [weightedCoverCount, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    by_cases ht : incidenceParity (tupleIndex t) = A
    · rw [ite_eq_left ht, incidenceWeight_eq_sq]
      have h := pow_le_pow_left₀ (abs_nonneg _) (hb t) 2
      simpa only [sq_abs, mul_pow, ← pow_mul, Nat.mul_comm d 2] using h
    · have hz : p.coeff (tupleIndex t) = 0 := by
        by_contra hn
        exact ht (hpar _ hn)
      simp [hz, ht]
  calc
    _ ≤ (ρ⁻¹ ^ (2 * d) * weightedCoverCount n k d A) / d.factorial :=
      div_le_div_of_nonneg_right hs (by positivity)
    _ = _ := by ring

/-- Equation (25), now for the response actually used in the witness. -/
theorem responseTerm_energy_le_weightedCoverCount {f : ComplexParameters n k → ℂ}
    (τ : ℝ) (A : Finset (Fin n)) {ρ : ℝ} (hρ : 0 < ρ)
    (ha : AnalyticOnNhd ℂ f {x | localNorm x ≤ ρ})
    (hb : ∀ x, localNorm x ≤ ρ → ‖f x‖ ≤ 1)
    (he : f =ᶠ[𝓝 0] complexResponse τ A) :
    coefficientEnergy (responseTerm (k := k) τ A d) ≤
      ρ⁻¹ ^ (2 * d) / d.factorial * weightedCoverCount n k d A := by
  apply coefficientEnergy_le_weightedCoverCount _ (responseTerm_isHomogeneous τ A d) A
  · exact responseTerm_coeff_parity τ A d
  · exact responseTerm_normalized_coefficient_bound τ A hρ ha hb he

end

end TensorLB
