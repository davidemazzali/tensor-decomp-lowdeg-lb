module

public import TensorLB.ConnectedSubstitution
public import TensorLB.SparseTensor

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Sparse tensor representations of the connected coordinates

Symmetry is unnecessary for the upper lift bound. The cubic quadratic part uses
three singleton/pair tuples with coefficient `-1`, and its cubic part uses one
enumeration of the triple with coefficient `2`. Column norm bounds `1, 2, 2`
suffice for both tensor orders and sum to less than the manuscript's constant `6`.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n k : ℕ}

def singletonCharacter (i : Fin n) : NonemptyCharacter n := ⟨{i}, Finset.singleton_nonempty i⟩

def linearTuple (I : ObservationIndex n k) : Fin 1 → NonemptyCharacter n :=
  fun _ => ⟨I.val, I.property.1⟩

def triplePairTuple (I : Finset (Fin n)) (hI : I.card = 3) (i : I) :
    Fin 2 → NonemptyCharacter n :=
  ![singletonCharacter i.val, ⟨I.erase i.val, by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem i.property, hI]
    decide⟩]

def quartetPairTuple (I : Finset (Fin n)) (hI : I.card = 4) (B : I.powersetCard 2) :
    Fin 2 → NonemptyCharacter n :=
  ![⟨B.val, by
      apply Finset.card_pos.mp
      rw [(Finset.mem_powersetCard.mp B.property).2]
      decide⟩,
    ⟨I \ B.val, by
      apply Finset.card_pos.mp
      rw [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp B.property).1, hI,
        (Finset.mem_powersetCard.mp B.property).2]
      decide⟩]

def tripleSingletonTuple (I : Finset (Fin n)) (hI : I.card = 3) :
    Fin 3 → NonemptyCharacter n :=
  fun b => singletonCharacter (I.orderIsoOfFin hI b).val

theorem triplePairTuple_injective (I : Finset (Fin n)) (hI : I.card = 3) :
    Function.Injective (triplePairTuple I hI) := by
  intro i j h
  apply Subtype.ext
  have h0 := congrArg (fun t => (t 0).val) h
  simpa only [triplePairTuple, Matrix.cons_val_zero, singletonCharacter,
    Finset.singleton_inj] using h0

theorem quartetPairTuple_injective (I : Finset (Fin n)) (hI : I.card = 4) :
    Function.Injective (quartetPairTuple I hI) := by
  intro B C h
  apply Subtype.ext
  exact congrArg (fun t => (t 0).val) h

theorem tupleUnion_linearTuple (I : ObservationIndex n k) : tupleUnion (linearTuple I) = I.val := by
  simp [tupleUnion, linearTuple]

theorem tupleUnion_triplePairTuple (I : Finset (Fin n)) (hI : I.card = 3) (i : I) :
    tupleUnion (triplePairTuple I hI i) = I := by
  simp [tupleUnion, triplePairTuple, singletonCharacter, Fin.univ_succ, Finset.insert_erase i.property]

theorem tupleUnion_quartetPairTuple (I : Finset (Fin n)) (hI : I.card = 4)
    (B : I.powersetCard 2) : tupleUnion (quartetPairTuple I hI B) = I := by
  simpa [tupleUnion, Fin.univ_succ, quartetPairTuple] using
    Finset.union_sdiff_of_subset (Finset.mem_powersetCard.mp B.property).1

theorem tupleUnion_tripleSingletonTuple (I : Finset (Fin n)) (hI : I.card = 3) :
    tupleUnion (tripleSingletonTuple I hI) = I := by
  ext i
  simp only [tupleUnion, Finset.mem_biUnion, Finset.mem_univ, true_and,
    tripleSingletonTuple, singletonCharacter, Finset.mem_singleton]
  constructor
  · rintro ⟨b, rfl⟩
    exact (I.orderIsoOfFin hI b).property
  · intro hi
    exact ⟨(I.orderIsoOfFin hI).symm ⟨i, hi⟩, by simp⟩

def linearConnectedTensor (I : ObservationIndex n k) : (Fin 1 → NonemptyCharacter n) → ℝ :=
  sparseTensor {linearTuple I} 1

def quadraticConnectedTensor (I : ObservationIndex n k) : (Fin 2 → NonemptyCharacter n) → ℝ :=
  if h : k = 3 ∧ I.val.card = 3 then
    sparseTensor (Finset.univ.image (triplePairTuple I.val h.2)) (-1)
  else if h : k = 4 ∧ I.val.card = 4 then
    sparseTensor (Finset.univ.image (quartetPairTuple I.val h.2)) (-1 / 2)
  else fun _ => 0

def cubicConnectedTensor (I : ObservationIndex n k) : (Fin 3 → NonemptyCharacter n) → ℝ :=
  if h : k = 3 ∧ I.val.card = 3 then sparseTensor {tripleSingletonTuple I.val h.2} 2
  else fun _ => 0

theorem linearConnectedTensor_norm_sq (I : ObservationIndex n k) :
    (∑ t, linearConnectedTensor I t ^ 2) ≤ 1 := by
  simp [linearConnectedTensor, sum_sq_sparseTensor]

theorem quadraticConnectedTensor_norm_sq (I : ObservationIndex n k) :
    (∑ t, quadraticConnectedTensor I t ^ 2) ≤ 4 := by
  unfold quadraticConnectedTensor
  split
  · rename_i h
    rw [sum_sq_sparseTensor]
    have hc := Finset.card_image_le (s := (Finset.univ : Finset I.val))
      (f := triplePairTuple I.val h.2)
    simp only [Finset.card_univ, Fintype.card_coe, h.2] at hc
    have hc' : ((Finset.univ.image (triplePairTuple I.val h.2)).card : ℝ) ≤ 3 := by
      exact_mod_cast hc
    nlinarith
  · split
    · rename_i h
      rw [sum_sq_sparseTensor]
      have hc := Finset.card_image_le (s := (Finset.univ : Finset (I.val.powersetCard 2)))
        (f := quartetPairTuple I.val h.2)
      simp only [Finset.card_univ, Fintype.card_coe, Finset.card_powersetCard, h.2] at hc
      have hc' : ((Finset.univ.image (quartetPairTuple I.val h.2)).card : ℝ) ≤ 6 := by
        exact_mod_cast hc
      nlinarith
    · simp

theorem cubicConnectedTensor_norm_sq (I : ObservationIndex n k) :
    (∑ t, cubicConnectedTensor I t ^ 2) ≤ 4 := by
  unfold cubicConnectedTensor
  split <;> norm_num [sum_sq_sparseTensor]

theorem linearConnectedTensor_support (I : ObservationIndex n k)
    (t : Fin 1 → NonemptyCharacter n) (ht : linearConnectedTensor I t ≠ 0) :
    tupleUnion t = I.val := by
  have : t = linearTuple I := by
    by_contra h
    exact ht (by simp [linearConnectedTensor, sparseTensor, h])
  rw [this, tupleUnion_linearTuple]

theorem quadraticConnectedTensor_support (I : ObservationIndex n k)
    (t : Fin 2 → NonemptyCharacter n) (ht : quadraticConnectedTensor I t ≠ 0) :
    tupleUnion t = I.val := by
  unfold quadraticConnectedTensor at ht
  split at ht
  · rename_i h
    have hm : t ∈ Finset.univ.image (triplePairTuple I.val h.2) := by
      by_contra hm
      exact ht (by simp only [sparseTensor, ite_eq_right hm])
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
    exact tupleUnion_triplePairTuple I.val h.2 i
  · split at ht
    · rename_i h
      have hm : t ∈ Finset.univ.image (quartetPairTuple I.val h.2) := by
        by_contra hm
        exact ht (by simp only [sparseTensor, ite_eq_right hm])
      obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hm
      exact tupleUnion_quartetPairTuple I.val h.2 B
    · exact (ht rfl).elim

theorem cubicConnectedTensor_support (I : ObservationIndex n k)
    (t : Fin 3 → NonemptyCharacter n) (ht : cubicConnectedTensor I t ≠ 0) :
    tupleUnion t = I.val := by
  unfold cubicConnectedTensor at ht
  split at ht
  · rename_i h
    have : t = tripleSingletonTuple I.val h.2 := by
      by_contra hm
      exact ht (by simp [sparseTensor, hm])
    rw [this, tupleUnion_tripleSingletonTuple]
  · exact (ht rfl).elim

theorem hiddenVariable_of_nonempty (I : Finset (Fin n)) (hI : I.Nonempty) :
    hiddenVariable I = MvPolynomial.X ⟨I, hI⟩ := by
  simp [hiddenVariable, hI]

theorem tensorPolynomial_linearConnectedTensor (I : ObservationIndex n k) :
    tensorPolynomial (linearConnectedTensor I) = hiddenVariable I.val := by
  apply MvPolynomial.funext
  intro u
  rw [hiddenVariable_of_nonempty I.val I.property.1]
  simp [linearConnectedTensor, eval_tensorPolynomial_sparseTensor, linearTuple]

theorem eval_tensorPolynomial_triplePair (I : Finset (Fin n)) (hI : I.card = 3)
    (u : NonemptyCharacter n → ℝ) :
    MvPolynomial.eval u
        (tensorPolynomial (sparseTensor (Finset.univ.image (triplePairTuple I hI)) (-1))) =
      -(∑ i ∈ I, MvPolynomial.eval u (hiddenVariable {i}) *
        MvPolynomial.eval u (hiddenVariable (I.erase i))) := by
  rw [eval_tensorPolynomial_sparseTensor, Finset.sum_image]
  · rw [neg_one_mul]
    congr 1
    rw [← Finset.sum_coe_sort I]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.prod_univ_two]
    simp only [triplePairTuple, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hiddenVariable_of_nonempty _ (Finset.singleton_nonempty _),
      hiddenVariable_of_nonempty _ (by
        apply Finset.card_pos.mp
        rw [Finset.card_erase_of_mem i.property, hI]
        decide)]
    simp [MvPolynomial.eval_X, singletonCharacter]
  · exact fun _ _ _ _ h => triplePairTuple_injective I hI h

theorem eval_tensorPolynomial_quartetPair (I : Finset (Fin n)) (hI : I.card = 4)
    (u : NonemptyCharacter n → ℝ) :
    MvPolynomial.eval u
        (tensorPolynomial (sparseTensor (Finset.univ.image (quartetPairTuple I hI)) (-1 / 2))) =
      -(1 / 2) * (∑ B ∈ I.powersetCard 2, MvPolynomial.eval u (hiddenVariable B) *
        MvPolynomial.eval u (hiddenVariable (I \ B))) := by
  rw [eval_tensorPolynomial_sparseTensor, Finset.sum_image]
  · rw [neg_div]
    congr 1
    rw [← Finset.sum_coe_sort (I.powersetCard 2)]
    apply Finset.sum_congr rfl
    intro B _
    rw [Fin.prod_univ_two]
    simp only [quartetPairTuple, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hiddenVariable_of_nonempty _ (by
        apply Finset.card_pos.mp
        rw [(Finset.mem_powersetCard.mp B.property).2]
        decide),
      hiddenVariable_of_nonempty _ (by
        apply Finset.card_pos.mp
        rw [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp B.property).1,
          hI, (Finset.mem_powersetCard.mp B.property).2]
        decide)]
    simp only [MvPolynomial.eval_X]
  · exact fun _ _ _ _ h => quartetPairTuple_injective I hI h

theorem eval_tensorPolynomial_tripleSingleton (I : Finset (Fin n)) (hI : I.card = 3)
    (u : NonemptyCharacter n → ℝ) :
    MvPolynomial.eval u (tensorPolynomial (sparseTensor {tripleSingletonTuple I hI} 2)) =
      2 * ∏ i ∈ I, MvPolynomial.eval u (hiddenVariable {i}) := by
  rw [eval_tensorPolynomial_sparseTensor]
  simp only [Finset.sum_singleton]
  congr 1
  rw [← Finset.prod_coe_sort I]
  apply Fintype.prod_equiv (I.orderIsoOfFin hI).toEquiv _ _
  intro i
  rw [hiddenVariable_of_nonempty _ (Finset.singleton_nonempty _)]
  simp [MvPolynomial.eval_X, tripleSingletonTuple, singletonCharacter]

theorem connectedSubstitution_eq_tensor_sum (I : ObservationIndex n k) :
    connectedSubstitution I = tensorPolynomial (linearConnectedTensor I) +
      tensorPolynomial (quadraticConnectedTensor I) + tensorPolynomial (cubicConnectedTensor I) := by
  rw [tensorPolynomial_linearConnectedTensor]
  apply MvPolynomial.funext
  intro u
  simp only [map_add]
  unfold connectedSubstitution quadraticConnectedTensor cubicConnectedTensor
  split
  · rename_i h
    simp only [cubicConnectedPolynomial, map_add, map_sub, map_mul,
      map_sum, map_prod, MvPolynomial.eval_C, eval_tensorPolynomial_triplePair,
      eval_tensorPolynomial_tripleSingleton]
    ring
  · rename_i h
    split
    · rename_i h4
      rw [eval_tensorPolynomial_quartetPair]
      simp only [quarticConnectedPolynomial, map_sub, map_mul,
        map_sum, MvPolynomial.eval_C,
        eval_tensorPolynomial, zero_mul, Finset.sum_const_zero, add_zero]
      ring
    · rename_i h4
      simp [eval_tensorPolynomial]

/-- The three homogeneous blocks, indexed by their degree minus one. -/
def connectedTensor : (j : Fin 3) → ObservationIndex n k →
    (Fin (j.val + 1) → NonemptyCharacter n) → ℝ
  | ⟨0, _⟩ => linearConnectedTensor
  | ⟨1, _⟩ => quadraticConnectedTensor
  | ⟨2, _⟩ => cubicConnectedTensor

def connectedTensorBound (j : Fin 3) : ℝ := if j = 0 then 1 else 2

theorem connectedTensor_orthogonal (a : Fin 3) (I J : ObservationIndex n k) (hIJ : I ≠ J) :
    (∑ t, connectedTensor a I t * connectedTensor a J t) = 0 := by
  fin_cases a
  · exact orthogonal_of_tupleUnion Subtype.val Subtype.val_injective linearConnectedTensor
      linearConnectedTensor_support I J hIJ
  · exact orthogonal_of_tupleUnion Subtype.val Subtype.val_injective quadraticConnectedTensor
      quadraticConnectedTensor_support I J hIJ
  · exact orthogonal_of_tupleUnion Subtype.val Subtype.val_injective cubicConnectedTensor
      cubicConnectedTensor_support I J hIJ

theorem connectedTensor_bound_nonneg (a : Fin 3) : 0 ≤ connectedTensorBound a := by
  unfold connectedTensorBound
  split <;> norm_num

theorem connectedTensor_norm_sq (a : Fin 3) (I : ObservationIndex n k) :
    (∑ t, connectedTensor a I t ^ 2) ≤ connectedTensorBound a ^ 2 := by
  fin_cases a
  · simpa [connectedTensor, connectedTensorBound] using linearConnectedTensor_norm_sq I
  · change (∑ t, quadraticConnectedTensor I t ^ 2) ≤ (2 : ℝ) ^ 2
    norm_num
    exact quadraticConnectedTensor_norm_sq I
  · change (∑ t, cubicConnectedTensor I t ^ 2) ≤ (2 : ℝ) ^ 2
    norm_num
    exact cubicConnectedTensor_norm_sq I

theorem sum_connectedTensor (I : ObservationIndex n k) :
    (∑ a, tensorPolynomial (connectedTensor a I)) = connectedSubstitution I := by
  rw [connectedSubstitution_eq_tensor_sum]
  simp [Fin.sum_univ_succ, connectedTensor, add_assoc]

theorem sum_connectedTensorBound : (∑ a, connectedTensorBound a) = 5 := by
  norm_num [Fin.sum_univ_succ, connectedTensorBound]

end

end TensorLB
