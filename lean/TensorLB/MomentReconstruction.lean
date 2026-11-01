module

public import TensorLB.ComplexConnected
public import TensorLB.LocalNorm

/-!
# Reconstructing admissible moments from connected coordinates

Singleton and pair targets are coordinates of the connected map. A quartet
requires the three pair products. The reconstruction is an entire polynomial,
so it also applies to analytic extensions of the connected-coordinate germ.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n k : ℕ}

def observationCoordinate (B : Finset (Fin n)) : ComplexParameters n k →L[ℂ] ℂ :=
  if h : B.Nonempty ∧ B.card ≤ k ∧ B.card % 2 = k % 2 then
    ContinuousLinearMap.proj ⟨B, h⟩ else 0

theorem observationCoordinate_apply (B : Finset (Fin n))
    (hB : B.Nonempty ∧ B.card ≤ k ∧ B.card % 2 = k % 2) (q : ComplexParameters n k) :
    observationCoordinate B q = q ⟨B, hB⟩ := by
  simp only [observationCoordinate, dite_eq_left hB, ContinuousLinearMap.proj_apply]

theorem norm_observationCoordinate_le (B : Finset (Fin n)) (q : ComplexParameters n k) :
    ‖observationCoordinate B q‖ ≤ ‖q‖ := by
  unfold observationCoordinate
  split
  · exact norm_le_pi_norm q _
  · simp

def momentFromConnected (A : Finset (Fin n)) (q : ComplexParameters n k) : ℂ :=
  observationCoordinate A q + if k = 4 ∧ A.card = 4 then
    (1 / 2) * ∑ B ∈ A.powersetCard 2,
      observationCoordinate B q * observationCoordinate (A \ B) q else 0

theorem analyticAt_momentFromConnected (A : Finset (Fin n)) (q : ComplexParameters n k) :
    AnalyticAt ℂ (momentFromConnected A) q := by
  unfold momentFromConnected
  apply ((observationCoordinate A).analyticAt q).add
  split
  · exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ (fun B _ =>
      ((observationCoordinate B).analyticAt q).mul
        ((observationCoordinate (A \ B)).analyticAt q)))
  · exact analyticAt_const

theorem observationCoordinate_complexConnected_pair (B : Finset (Fin n))
    (hB : B.card = 2) (t : ComplexParameters n 4) :
    observationCoordinate B (complexConnected t) = complexMoment t B := by
  have hb : B.Nonempty ∧ B.card ≤ 4 ∧ B.card % 2 = 4 % 2 := by
    refine ⟨Finset.card_pos.mp (by omega), by omega, by omega⟩
  rw [observationCoordinate_apply B hb]
  simp only [complexConnected, hB]
  norm_num

theorem momentFromConnected_complexConnected (A : Finset (Fin n))
    (hA : admissibleTarget n k A) (t : ComplexParameters n k) :
    momentFromConnected A (complexConnected t) = complexMoment t A := by
  have ha : A.Nonempty ∧ A.card ≤ k ∧ A.card % 2 = k % 2 := by
    unfold admissibleTarget at hA
    refine ⟨Finset.card_pos.mp (by omega), by omega, by omega⟩
  unfold momentFromConnected
  rw [observationCoordinate_apply A ha]
  rcases hA with ⟨rfl, hA⟩ | ⟨rfl, hA | hA⟩
  · simp [complexConnected, hA]
  · simp [complexConnected, hA]
  · have hs : (∑ B ∈ A.powersetCard 2,
        observationCoordinate B (complexConnected t) *
          observationCoordinate (A \ B) (complexConnected t)) =
        ∑ B ∈ A.powersetCard 2, complexMoment t B * complexMoment t (A \ B) := by
      apply Finset.sum_congr rfl
      intro B hB
      obtain ⟨hBA, hB2⟩ := Finset.mem_powersetCard.mp hB
      have hAB : (A \ B).card = 2 := by
        rw [Finset.card_sdiff_of_subset hBA, hA, hB2]
      rw [observationCoordinate_complexConnected_pair B hB2,
        observationCoordinate_complexConnected_pair (A \ B) hAB]
    simp only [hA, and_self, ite_true, hs, complexConnected]
    norm_num

theorem norm_momentFromConnected_le (A : Finset (Fin n)) (q : ComplexParameters n k) :
    ‖momentFromConnected A q‖ ≤ ‖q‖ + 3 * ‖q‖ ^ 2 := by
  unfold momentFromConnected
  split
  · rename_i hA
    calc
      _ ≤ ‖observationCoordinate A q‖ +
          ‖(1 / 2 : ℂ) * ∑ B ∈ A.powersetCard 2,
            observationCoordinate B q * observationCoordinate (A \ B) q‖ := norm_add_le _ _
      _ ≤ ‖q‖ + (1 / 2 : ℝ) * (6 * ‖q‖ ^ 2) := by
        gcongr
        · exact norm_observationCoordinate_le A q
        · rw [norm_mul]
          have hc : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
          rw [hc]
          gcongr
          calc
            _ ≤ ∑ B ∈ A.powersetCard 2,
                ‖observationCoordinate B q * observationCoordinate (A \ B) q‖ := norm_sum_le _ _
            _ ≤ ∑ _B ∈ A.powersetCard 2, ‖q‖ ^ 2 := by
              apply Finset.sum_le_sum
              intro B _
              rw [norm_mul, pow_two]
              exact mul_le_mul (norm_observationCoordinate_le B q)
                (norm_observationCoordinate_le (A \ B) q) (norm_nonneg _) (norm_nonneg _)
            _ = _ := by norm_num [Finset.card_powersetCard, hA.2, Nat.choose]
      _ = _ := by ring
  · simp only [add_zero]
    exact (norm_observationCoordinate_le A q).trans (by nlinarith [sq_nonneg ‖q‖])

theorem norm_momentFromConnected_le_one (A : Finset (Fin n))
    (q : ComplexParameters n k) (hq : ‖q‖ ≤ 1 / 4) : ‖momentFromConnected A q‖ ≤ 1 := by
  have h := norm_momentFromConnected_le A q
  have hq0 := norm_nonneg q
  nlinarith

end

end TensorLB
