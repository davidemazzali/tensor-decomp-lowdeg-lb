module

public import TensorLB.IncidenceEnergy

/-!
# Padding observations to equally sized incidence blocks

Each observable support is represented by exactly `k` slots. Extra slots are
copies of one coordinate and occur an even number of times, preserving parity.
This embeds the observation tuples into unrestricted `k d`-slot assignments.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {α : Type*} [Fintype α] {n k d : ℕ}

theorem exists_tupleIndex (R : α →₀ ℕ) (hR : R.sum (fun _ r => r) = d) :
    ∃ t : Fin d → α, tupleIndex t = R := by
  have h := sum_tupleIndex_eq (d := d) R
  rw [ite_eq_left hR] at h
  by_contra hn
  have hs : (∑ t : Fin d → α, if tupleIndex t = R then (1 : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    exact ite_eq_right (fun ht => hn ⟨t, ht⟩)
  rw [hs] at h
  have hz : R.multinomial = 0 := Nat.cast_eq_zero.mp h.symm
  have hf := factorial_mul_multinomial R
  simp only [hz, mul_zero] at hf
  exact Nat.factorial_ne_zero _ hf.symm

def paddedMultiplicity (I : ObservationIndex n k) : Fin n →₀ ℕ :=
  (∑ i ∈ I.val, Finsupp.single i 1) +
    Finsupp.single I.property.1.choose (k - I.val.card)

theorem paddedMultiplicity_apply (I : ObservationIndex n k) (i : Fin n) :
    paddedMultiplicity I i = (if i ∈ I.val then 1 else 0) +
      (if I.property.1.choose = i then k - I.val.card else 0) := by
  simp only [paddedMultiplicity, Finsupp.add_apply, Finsupp.finsetSum_apply,
    Finsupp.single_apply]
  split_ifs <;> simp_all

theorem paddedMultiplicity_degree (I : ObservationIndex n k) :
    (paddedMultiplicity I).sum (fun _ r => r) = k := by
  unfold paddedMultiplicity
  rw [Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl),
    ← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  simp only [Finsupp.sum_single_index, Finset.sum_const, smul_eq_mul, mul_one]
  exact Nat.add_sub_of_le I.property.2.1

theorem paddedMultiplicity_mod_two (I : ObservationIndex n k) (i : Fin n) :
    paddedMultiplicity I i % 2 = if i ∈ I.val then 1 else 0 := by
  have hp : (k - I.val.card) % 2 = 0 := by
    have h1 := I.property.2.1
    have h2 := I.property.2.2
    omega
  rw [paddedMultiplicity_apply]
  split_ifs <;> omega

def paddedObservation (I : ObservationIndex n k) : Fin k → Fin n :=
  Classical.choose (exists_tupleIndex (paddedMultiplicity I) (paddedMultiplicity_degree I))

theorem tupleIndex_paddedObservation (I : ObservationIndex n k) :
    tupleIndex (paddedObservation I) = paddedMultiplicity I :=
  Classical.choose_spec (exists_tupleIndex (paddedMultiplicity I) (paddedMultiplicity_degree I))

theorem paddedObservation_injective : Function.Injective (paddedObservation (n := n) (k := k)) := by
  intro I J hIJ
  apply Subtype.ext
  ext i
  have hh := congrArg (fun t : Fin k → Fin n => tupleIndex t i % 2) hIJ
  rw [tupleIndex_paddedObservation, tupleIndex_paddedObservation,
    paddedMultiplicity_mod_two, paddedMultiplicity_mod_two] at hh
  by_cases hi : i ∈ I.val <;> by_cases hj : i ∈ J.val <;> simp_all

def paddedTuple (t : Fin d → ObservationIndex n k) : Fin (k * d) → Fin n :=
  fun j => paddedObservation (t (finProdFinEquiv.symm j).2) (finProdFinEquiv.symm j).1

theorem paddedTuple_injective : Function.Injective (paddedTuple (n := n) (k := k) (d := d)) := by
  intro t u h
  funext j
  apply paddedObservation_injective
  funext i
  have hh := congrFun h (finProdFinEquiv (i, j))
  simpa only [paddedTuple, Equiv.symm_apply_apply] using hh

theorem tupleIndex_paddedTuple (t : Fin d → ObservationIndex n k) :
    tupleIndex (paddedTuple t) = ∑ j, paddedMultiplicity (t j) := by
  unfold tupleIndex
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin k × Fin d ≃ Fin (k * d))]
  simp only [paddedTuple, Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact tupleIndex_paddedObservation (t j)

theorem paddedTuple_incidence_le (t : Fin d → ObservationIndex n k) (i : Fin n) :
    incidenceCount (tupleIndex t) i ≤ tupleIndex (paddedTuple t) i := by
  rw [incidenceCount_tupleIndex, tupleIndex_paddedTuple, Finsupp.finsetSum_apply]
  exact Finset.sum_le_sum (fun j _ => by rw [paddedMultiplicity_apply]; omega)

theorem paddedTuple_incidence_parity (t : Fin d → ObservationIndex n k) (i : Fin n) :
    tupleIndex (paddedTuple t) i % 2 = incidenceCount (tupleIndex t) i % 2 := by
  rw [incidenceCount_tupleIndex, tupleIndex_paddedTuple, Finsupp.finsetSum_apply,
    Finset.sum_nat_mod]
  simp only [paddedMultiplicity_mod_two]

end

end TensorLB
