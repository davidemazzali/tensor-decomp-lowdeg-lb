module

public import TensorLB.OrderedPartitionBridge
public import TensorLB.ComplexCoordinates

/-!
# Inserting an occurrence into a cumulant partition

The extension bijection separates the new singleton block from insertion into
an existing block. This is the combinatorial identity behind differentiation
of a tilted cumulant.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n k : ℕ}

theorem image_fin_cons_univ {A : Type*} [DecidableEq A] (a : A) (f : Fin n → A) :
    Finset.univ.image (Fin.cons a f) = insert a (Finset.univ.image f) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Fin.exists_fin_succ,
    Fin.cons_zero, Fin.cons_succ, Finset.mem_insert]
  rw [eq_comm (a := a)]

theorem image_univ_fin_cast {A : Type*} [DecidableEq A] {m r : ℕ}
    (h : m = r) (f : Fin r → A) :
    Finset.univ.image (f ∘ Fin.cast h) = Finset.univ.image f := by
  subst r
  rfl

theorem orderedBlock_extendLeft_zero (c : OrderedFinpartition n) :
    orderedBlock c.extendLeft (0 : Fin (c.length + 1)) = {0} := by
  change (Finset.univ : Finset (Fin 1)).image (fun _ => (0 : Fin (n + 1))) = {0}
  simp

theorem orderedBlock_extendLeft_succ (c : OrderedFinpartition n) (j : Fin c.length) :
    orderedBlock c.extendLeft j.succ = (orderedBlock c j).image Fin.succ := by
  simp only [orderedBlock, OrderedFinpartition.extendLeft, Fin.cases_succ,
    Finset.image_image, Function.comp_def]
  rfl

theorem orderedBlock_extendMiddle_same (c : OrderedFinpartition n) (j : Fin c.length) :
    orderedBlock (c.extendMiddle j) j = insert 0 ((orderedBlock c j).image Fin.succ) := by
  simp only [orderedBlock, OrderedFinpartition.extendMiddle, dite_eq_left]
  erw [image_univ_fin_cast]
  change Finset.univ.image (Fin.cons 0 (Fin.succ ∘ c.emb j)) = _
  rw [image_fin_cons_univ, Finset.image_image]

theorem orderedBlock_extendMiddle_ne (c : OrderedFinpartition n) (j k : Fin c.length) (hjk : j ≠ k) :
    orderedBlock (c.extendMiddle k) j = (orderedBlock c j).image Fin.succ := by
  simp only [orderedBlock, OrderedFinpartition.extendMiddle, dite_eq_right hjk]
  rw [← Function.comp_assoc]
  erw [image_univ_fin_cast]
  rw [Finset.image_image]

def orderedCumulant (M : Finset (Fin n) → ℂ) : ℂ :=
  ∑ c : OrderedFinpartition n, (cumulantMobius c.length : ℂ) * ∏ j, M (orderedBlock c j)

theorem prod_orderedBlock_extendLeft (c : OrderedFinpartition n) (M : Finset (Fin (n + 1)) → ℂ) :
    (∏ j, M (orderedBlock c.extendLeft j)) =
      M {0} * ∏ j, M ((orderedBlock c j).image Fin.succ) := by
  change (∏ j : Fin (c.length + 1), M (orderedBlock c.extendLeft j)) = _
  rw [Fin.prod_univ_succ, orderedBlock_extendLeft_zero]
  congr 1
  exact Finset.prod_congr rfl (fun j _ => congrArg M (orderedBlock_extendLeft_succ c j))

theorem prod_orderedBlock_extendMiddle (c : OrderedFinpartition n) (k : Fin c.length)
    (M : Finset (Fin (n + 1)) → ℂ) :
    (∏ j, M (orderedBlock (c.extendMiddle k) j)) =
      M (insert 0 ((orderedBlock c k).image Fin.succ)) *
        ∏ j ∈ Finset.univ.erase k, M ((orderedBlock c j).image Fin.succ) := by
  change (∏ j : Fin c.length, M (orderedBlock (c.extendMiddle k) j)) = _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), orderedBlock_extendMiddle_same]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact congrArg M (orderedBlock_extendMiddle_ne c j k (Finset.mem_erase.mp hj).1)

theorem orderedCumulant_extend (M : Finset (Fin (n + 1)) → ℂ) :
    orderedCumulant M = ∑ c : OrderedFinpartition n,
      ((cumulantMobius (c.length + 1) : ℂ) * M {0} *
        (∏ j, M ((orderedBlock c j).image Fin.succ)) +
      (cumulantMobius c.length : ℂ) *
        ∑ k, M (insert 0 ((orderedBlock c k).image Fin.succ)) *
          ∏ j ∈ Finset.univ.erase k, M ((orderedBlock c j).image Fin.succ)) := by
  rw [orderedCumulant, ← Equiv.sum_comp (OrderedFinpartition.extendEquiv n), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  rw [Fintype.sum_option]
  change (cumulantMobius (c.length + 1) : ℂ) *
      (∏ j, M (orderedBlock c.extendLeft j)) +
    (∑ k : Fin c.length, (cumulantMobius c.length : ℂ) *
      ∏ j, M (orderedBlock (c.extendMiddle k) j)) = _
  rw [prod_orderedBlock_extendLeft c M, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro k _
    rw [prod_orderedBlock_extendMiddle c k M]


theorem orderedCumulant_extend_sub (hn : 1 ≤ n) (M : Finset (Fin (n + 1)) → ℂ) :
    orderedCumulant M = ∑ c : OrderedFinpartition n, (cumulantMobius c.length : ℂ) *
      ((∑ k, M (insert 0 ((orderedBlock c k).image Fin.succ)) *
          ∏ j ∈ Finset.univ.erase k, M ((orderedBlock c j).image Fin.succ)) -
        (c.length : ℂ) * M {0} * ∏ j, M ((orderedBlock c j).image Fin.succ)) := by
  rw [orderedCumulant_extend]
  apply Finset.sum_congr rfl
  intro c _
  have hl : 1 ≤ c.length := c.length_pos (by omega)
  have hμ : (cumulantMobius (c.length + 1) : ℂ) =
      -(c.length : ℂ) * (cumulantMobius c.length : ℂ) := by
    exact_mod_cast cumulantMobius_succ hl
  rw [hμ]
  ring

theorem orderedCumulant_characterMoment (X : Fin n → Finset (Fin k)) :
    orderedCumulant (fun B => (characterMoment X B : ℂ)) = (jointCharacterCumulant X : ℂ) := by
  unfold orderedCumulant jointCharacterCumulant partitionCumulant
  rw [Complex.ofReal_sum, ← Equiv.sum_comp orderedPartitionEquiv]
  apply Finset.sum_congr rfl
  intro c _
  change _ = ((cumulantMobius (orderedPartition c).parts.card *
    ∏ B ∈ (orderedPartition c).parts, characterMoment X B : ℝ) : ℂ)
  rw [orderedPartition_card, Complex.ofReal_mul, Complex.ofReal_prod, orderedPartition_parts,
    Finset.prod_image (fun a _ b _ h => orderedBlock_injective c h)]

end

end TensorLB
