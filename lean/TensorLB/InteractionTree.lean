module

public import TensorLB.RootedTree
public import TensorLB.LocalNorm

/-!
# Summing interaction and marked-spin trees

Each state is an interaction support or a marked spin. The one-child sums cost
at most `k * localNorm t` for interactions and `k` for marked spins. The rooted
tree summation consequently has no ambient dimension factor.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n k : ℕ}

abbrev TreeState (n k : ℕ) := ObservationIndex n k ⊕ Fin n

def treeStateSupport : TreeState n k → Finset (Fin n)
  | .inl I => I.val
  | .inr i => {i}

theorem treeStateSupport_card_le (hk : 1 ≤ k) (s : TreeState n k) :
    (treeStateSupport s).card ≤ k := by
  cases s with
  | inl I => exact I.property.2.1
  | inr i => simpa only [treeStateSupport, Finset.card_singleton] using hk

def interactionTreeKernel (t : ComplexParameters n k) (a : TreeState n k) : TreeState n k → ℝ
  | .inl I => if (I.val ∩ treeStateSupport a).Nonempty then ‖t I‖ else 0
  | .inr _ => 0

def markedTreeKernel (a : TreeState n k) : TreeState n k → ℝ
  | .inl _ => 0
  | .inr i => if i ∈ treeStateSupport a then 1 else 0

theorem interactionTreeKernel_nonneg (t : ComplexParameters n k) (a b : TreeState n k) :
    0 ≤ interactionTreeKernel t a b := by
  cases b with
  | inl I => dsimp [interactionTreeKernel]; split_ifs <;> positivity
  | inr i => exact le_rfl

theorem markedTreeKernel_nonneg (a b : TreeState n k) : 0 ≤ markedTreeKernel a b := by
  cases b with
  | inl I => exact le_rfl
  | inr i => dsimp [markedTreeKernel]; split_ifs <;> positivity

theorem sum_interactionTreeKernel_le (hk : 1 ≤ k) (t : ComplexParameters n k)
    (a : TreeState n k) :
    (∑ b : TreeState n k, interactionTreeKernel t a b) ≤ (k : ℝ) * localNorm t := by
  rw [Fintype.sum_sum_type]
  simp only [interactionTreeKernel, Finset.sum_const_zero, add_zero]
  exact (sum_intersecting_norm_le t (treeStateSupport a)).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast treeStateSupport_card_le hk a)
      (localNorm_nonneg t))

theorem sum_markedTreeKernel_le (hk : 1 ≤ k) (a : TreeState n k) :
    (∑ b : TreeState n k, markedTreeKernel a b) ≤ (k : ℝ) := by
  rw [Fintype.sum_sum_type]
  simp only [markedTreeKernel, Finset.sum_const_zero, zero_add]
  have he : (∑ i : Fin n, if i ∈ treeStateSupport a then (1 : ℝ) else 0) =
      ((treeStateSupport a).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [he]
  exact_mod_cast treeStateSupport_card_le hk a

def mixedTreeKernel {p d : ℕ} (w : Fin d → ComplexParameters n k) :
    (Fin p ⊕ Fin d) → TreeState n k → TreeState n k → ℝ
  | .inl _ => markedTreeKernel
  | .inr j => interactionTreeKernel (w j)

def mixedTreeCost {p d : ℕ} (w : Fin d → ComplexParameters n k) : (Fin p ⊕ Fin d) → ℝ
  | .inl _ => k
  | .inr j => (k : ℝ) * localNorm (w j)

theorem prod_mixedTreeCost {p d : ℕ} (w : Fin d → ComplexParameters n k) :
    (∏ v : Fin p ⊕ Fin d, mixedTreeCost w v) =
      (k : ℝ) ^ (p + d) * ∏ j, localNorm (w j) := by
  rw [Fintype.prod_sum_type]
  simp only [mixedTreeCost, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, pow_add]
  ring

/-- The summation step in equation (15), for a fixed rooted dependency tree.
Here `p` is the number of marked spins other than the fixed root. -/
theorem sum_mixedTreeWeight_le {p d : ℕ} (hk : 1 ≤ k)
    (w : Fin d → ComplexParameters n k) (root : TreeState n k)
    (T : RootedParent (Fin p ⊕ Fin d)) :
    (∑ x : (Fin p ⊕ Fin d) → TreeState n k, T.weight (mixedTreeKernel w) root x) ≤
      (k : ℝ) ^ (p + d) * ∏ j, localNorm (w j) := by
  rw [← prod_mixedTreeCost w]
  apply T.sum_weight_le (mixedTreeKernel w) root (mixedTreeCost w)
  · intro v a b
    cases v with
    | inl _ => exact markedTreeKernel_nonneg a b
    | inr j => exact interactionTreeKernel_nonneg (w j) a b
  · intro v
    cases v with
    | inl _ => exact Nat.cast_nonneg k
    | inr j => exact mul_nonneg (Nat.cast_nonneg k) (localNorm_nonneg (w j))
  · intro v a
    cases v with
    | inl _ => exact sum_markedTreeKernel_le hk a
    | inr j => exact sum_interactionTreeKernel_le hk (w j) a

/-- Sum over all rooted parent maps, using a simple parent-function count
instead of Cayley's exact tree count. -/
theorem sum_all_mixedTreeWeight_le {p d : ℕ} (hk : 1 ≤ k)
    (w : Fin d → ComplexParameters n k) (root : TreeState n k) :
    (∑ T : RootedParent (Fin p ⊕ Fin d),
      ∑ x : (Fin p ⊕ Fin d) → TreeState n k, T.weight (mixedTreeKernel w) root x) ≤
      ((p + d + 1 : ℕ) : ℝ) ^ (p + d) * (k : ℝ) ^ (p + d) *
        ∏ j, localNorm (w j) := by
  have hcount : (Fintype.card (RootedParent (Fin p ⊕ Fin d)) : ℝ) ≤
      ((p + d + 1 : ℕ) : ℝ) ^ (p + d) := by
    exact_mod_cast (by simpa using (RootedParent.card_le (V := Fin p ⊕ Fin d)))
  calc
    _ ≤ ∑ _T : RootedParent (Fin p ⊕ Fin d),
        (k : ℝ) ^ (p + d) * ∏ j, localNorm (w j) :=
      Finset.sum_le_sum (fun T _ => sum_mixedTreeWeight_le hk w root T)
    _ = (Fintype.card (RootedParent (Fin p ⊕ Fin d)) : ℝ) *
        ((k : ℝ) ^ (p + d) * ∏ j, localNorm (w j)) := by simp
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_right hcount
      exact mul_nonneg (pow_nonneg (Nat.cast_nonneg k) _)
        (Finset.prod_nonneg (fun j _ => localNorm_nonneg (w j)))

end

end TensorLB
