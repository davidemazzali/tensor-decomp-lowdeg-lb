module

public import TensorLB.CumulantExtension

/-! # Explicit cumulant formulas through order four -/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

theorem sum_orderedPartition_succ {R : Type*} [AddCommMonoid R] (n : ℕ)
    (f : OrderedFinpartition (n+1) → R) :
    (∑ c, f c) = ∑ c : OrderedFinpartition n, (f c.extendLeft + ∑ j, f (c.extendMiddle j)) := by
  rw [← Equiv.sum_comp (OrderedFinpartition.extendEquiv n), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  simp only [OrderedFinpartition.extendEquiv_apply, Fintype.sum_option,
    OrderedFinpartition.extend_none, OrderedFinpartition.extend_some]

theorem orderedBlock_atomic {n : ℕ} (j : Fin n) :
    orderedBlock (OrderedFinpartition.atomic n) j = {j} := by
  change (Finset.univ : Finset (Fin 1)).image (fun _ => j) = {j}
  simp

theorem orderedCumulant_one (M : Finset (Fin 1) → ℂ) : orderedCumulant M = M {0} := by
  unfold orderedCumulant
  simp only [Fintype.sum_unique, OrderedFinpartition.default_eq]
  simp +instances +decide [orderedBlock, OrderedFinpartition.atomic, cumulantMobius]

theorem orderedCumulant_two (M : Finset (Fin 2) → ℂ) :
    orderedCumulant M = M {0,1} - M {0} * M {1} := by
  rw [orderedCumulant_extend]
  simp only [Fintype.sum_unique, OrderedFinpartition.default_eq]
  simp +instances +decide [orderedBlock, OrderedFinpartition.atomic, cumulantMobius]
  ring

theorem orderedCumulant_three (M : Finset (Fin 3) → ℂ) :
    orderedCumulant M = M {0,1,2} - M {0} * M {1,2} - M {1} * M {0,2} -
      M {2} * M {0,1} + 2 * M {0} * M {1} * M {2} := by
  rw [orderedCumulant, sum_orderedPartition_succ 2, sum_orderedPartition_succ 1]
  simp only [Fintype.sum_unique, OrderedFinpartition.default_eq]
  simp +instances +decide [orderedBlock, OrderedFinpartition.atomic,
    OrderedFinpartition.extendLeft, OrderedFinpartition.extendMiddle, cumulantMobius,
    Fin.sum_univ_succ, Fin.prod_univ_succ]
  simp +instances [Fin.univ_def, List.finRange, List.ofFn, Function.comp_def,
    Fin.cases, Fin.cons, Fin.induction, Fin.induction.go, Finset.image, Multiset.map_coe,
    Fin.foldr, Fin.foldr.loop, Function.update, List.toFinset_cons]
  ring

theorem orderedCumulant_three_symmetric (M : Finset (Fin 3) → ℂ) :
    orderedCumulant M = M Finset.univ -
      (∑ i : Fin 3, M {i} * M (Finset.univ.erase i)) + 2 * ∏ i : Fin 3, M {i} := by
  rw [orderedCumulant_three]
  have hu : (Finset.univ : Finset (Fin 3)) = {0,1,2} := by decide
  simp +decide [hu, Finset.erase_insert_of_ne]
  ring

theorem orderedCumulant_four_centered (M : Finset (Fin 4) → ℂ) (hM : ∀ i, M {i} = 0) :
    orderedCumulant M = M {0,1,2,3} - M {0,1} * M {2,3} -
      M {0,2} * M {1,3} - M {0,3} * M {1,2} := by
  rw [orderedCumulant, sum_orderedPartition_succ 3, sum_orderedPartition_succ 2,
    sum_orderedPartition_succ 1]
  simp only [Fintype.sum_unique, OrderedFinpartition.default_eq]
  simp +instances +decide [orderedBlock, OrderedFinpartition.atomic,
    OrderedFinpartition.extendLeft, OrderedFinpartition.extendMiddle, cumulantMobius,
    Fin.sum_univ_succ, Fin.prod_univ_succ]
  simp +instances [Fin.univ_def, List.finRange, List.ofFn, Function.comp_def,
    Fin.cases, Fin.cons, Fin.induction, Fin.induction.go, Finset.image, Multiset.map_coe,
    Fin.foldr, Fin.foldr.loop, Function.update, List.toFinset_cons, hM]
  ring

theorem orderedCumulant_four_symmetric (M : Finset (Fin 4) → ℂ) (hM : ∀ i, M {i} = 0) :
    orderedCumulant M = M Finset.univ - (1/2) *
      ∑ B ∈ (Finset.univ : Finset (Fin 4)).powersetCard 2, M B * M (Finset.univ \ B) := by
  rw [orderedCumulant_four_centered M hM]
  have hu : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  have hp : (Finset.univ : Finset (Fin 4)).powersetCard 2 =
      {{0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}} := by decide
  rw [hp]
  simp +decide [hu, Finset.sdiff_insert, Finset.sdiff_singleton_eq_erase, Finset.erase_insert_of_ne]
  ring

end

end TensorLB
