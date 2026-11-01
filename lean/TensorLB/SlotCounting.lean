module

public import TensorLB.ObservationPadding
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Weighted slot assignments and their multiplicities

Padding reduces observation tuples to unrestricted slot assignments. Grouping
assignments by multiplicity supplies the exact multinomial factor.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n k d s : ℕ}

def coordinateParity (R : Fin n →₀ ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => R i % 2 = 1)

def coordinateWeight (R : Fin n →₀ ℕ) : ℝ := ∏ i : Fin n, (R i : ℝ) ^ (2 * R i)

def weightedSlotCount (n s : ℕ) (A : Finset (Fin n)) : ℝ :=
  ∑ t : Fin s → Fin n,
    if coordinateParity (tupleIndex t) = A then coordinateWeight (tupleIndex t) else 0

theorem coordinateWeight_nonneg (R : Fin n →₀ ℕ) : 0 ≤ coordinateWeight R :=
  Finset.prod_nonneg (fun i _ => by positivity)

theorem nat_self_power_mono {u v : ℕ} (h : u ≤ v) : u ^ (2 * u) ≤ v ^ (2 * v) := by
  by_cases hv : v = 0
  · have hu : u = 0 := by omega
    simp [hu, hv]
  · exact (Nat.pow_le_pow_left h _).trans
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 2 h))

theorem coordinateParity_paddedTuple (t : Fin d → ObservationIndex n k) :
    coordinateParity (tupleIndex (paddedTuple t)) = incidenceParity (tupleIndex t) := by
  ext i
  simp only [coordinateParity, incidenceParity, Finset.mem_filter, Finset.mem_univ, true_and,
    paddedTuple_incidence_parity]

theorem incidenceWeight_le_coordinateWeight_paddedTuple (t : Fin d → ObservationIndex n k) :
    incidenceWeight (tupleIndex t) ≤ coordinateWeight (tupleIndex (paddedTuple t)) := by
  apply Finset.prod_le_prod₀
  · intro i _
    positivity
  · intro i _
    exact_mod_cast nat_self_power_mono (paddedTuple_incidence_le t i)

theorem weightedCoverCount_le_weightedSlotCount (A : Finset (Fin n)) :
    weightedCoverCount n k d A ≤ weightedSlotCount n (k * d) A := by
  unfold weightedCoverCount weightedSlotCount
  calc
    _ ≤ ∑ t : Fin d → ObservationIndex n k,
        if coordinateParity (tupleIndex (paddedTuple t)) = A then
          coordinateWeight (tupleIndex (paddedTuple t)) else 0 := by
      apply Finset.sum_le_sum
      intro t _
      rw [coordinateParity_paddedTuple]
      split_ifs
      · exact incidenceWeight_le_coordinateWeight_paddedTuple t
      · rfl
    _ = ∑ t ∈ Finset.univ.image (paddedTuple (n := n) (k := k) (d := d)),
        if coordinateParity (tupleIndex t) = A then coordinateWeight (tupleIndex t) else 0 := by
      rw [Finset.sum_image (fun _ _ _ _ h => paddedTuple_injective h)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun t _ _ => by split_ifs; exact coordinateWeight_nonneg _; rfl)

theorem sum_tupleIndex_grouped {α : Type*} [Fintype α]
    (F : (α →₀ ℕ) → ℝ) :
    (∑ t : Fin s → α, F (tupleIndex t)) =
      ∑ R ∈ Finset.finsuppAntidiag (Finset.univ : Finset α) s, (R.multinomial : ℝ) * F R := by
  have hmem (t : Fin s → α) : tupleIndex t ∈ Finset.finsuppAntidiag Finset.univ s := by
    rw [Finset.mem_finsuppAntidiag']
    exact ⟨tupleIndex_degree t, Finset.subset_univ _⟩
  rw [← Finset.sum_fiberwise_of_maps_to (fun t _ => hmem t)]
  apply Finset.sum_congr rfl
  intro R hR
  have hdeg : R.sum (fun _ r => r) = s := (Finset.mem_finsuppAntidiag'.mp hR).1
  have hc := sum_tupleIndex_eq (d := s) R
  rw [ite_eq_left hdeg, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  calc
    _ = ∑ t ∈ Finset.univ.filter (fun t : Fin s → α => tupleIndex t = R), F R := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [(Finset.mem_filter.mp ht).2]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hc]

theorem weightedSlotCount_eq_multiplicity_sum (A : Finset (Fin n)) :
    weightedSlotCount n s A =
      ∑ R ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin n)) s,
        if coordinateParity R = A then (R.multinomial : ℝ) * coordinateWeight R else 0 := by
  convert! sum_tupleIndex_grouped
    (fun R : Fin n →₀ ℕ => if coordinateParity R = A then coordinateWeight R else 0) using 1
  simp only [mul_ite, mul_zero]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext R
  simp only [Finset.mem_finsuppAntidiag]

end

end TensorLB
