module

public import TensorLB.CumulantMoments
public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno

/-!
# Cumulant weights on Faà di Bruno partitions

Mathlib's ordered partitions have a canonical ordering of blocks, not an extra
permutation factor. Their extension equivalence supplies the exact cancellation
of the signed factorial weights at every order greater than one.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

theorem sum_orderedPartition_succ_by_length {R : Type*} [AddCommMonoid R]
    (n : ℕ) (f : ℕ → R) :
    (∑ c : OrderedFinpartition (n + 1), f c.length) =
      ∑ c : OrderedFinpartition n, (f (c.length + 1) + c.length • f c.length) := by
  rw [← Equiv.sum_comp (OrderedFinpartition.extendEquiv n), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  simp only [OrderedFinpartition.extendEquiv_apply, Fintype.sum_option,
    OrderedFinpartition.extend_none, OrderedFinpartition.extend_some,
    OrderedFinpartition.extendLeft_length, OrderedFinpartition.extendMiddle_length,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]

theorem sum_orderedPartition_mobius_succ {n : ℕ} (hn : 1 ≤ n) :
    (∑ c : OrderedFinpartition (n + 1), cumulantMobius c.length) = 0 := by
  rw [sum_orderedPartition_succ_by_length]
  apply Finset.sum_eq_zero
  intro c _
  rw [cumulantMobius_succ (by have := c.length_pos (by omega); omega), nsmul_eq_mul]
  ring

theorem sum_orderedPartition_mobius_one :
    (∑ c : OrderedFinpartition 1, cumulantMobius c.length) = 1 := by
  simp only [Fintype.sum_unique, OrderedFinpartition.default_eq, OrderedFinpartition.atomic_length]
  norm_num [cumulantMobius]

theorem sum_orderedPartition_mobius {n : ℕ} (hn : 1 ≤ n) :
    (∑ c : OrderedFinpartition n, cumulantMobius c.length) = if n = 1 then 1 else 0 := by
  by_cases h : n = 1
  · subst n
    simpa using sum_orderedPartition_mobius_one
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [sum_orderedPartition_mobius_succ (by omega), ite_eq_right h]

end

end TensorLB
