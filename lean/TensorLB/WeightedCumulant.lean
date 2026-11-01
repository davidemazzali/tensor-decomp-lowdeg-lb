module

public import TensorLB.RootedGraph
public import TensorLB.InteractionTree
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Weighted rooted cumulants and the local interaction norm

The spanning-tree estimate is transported to well-founded parent maps and
summed using the one-child local-norm bounds. Marked spins and interactions
retain their distinct roles, and repeated supports remain permitted.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {n k : ℕ}

theorem abs_cumulant_weighted_le_rooted (X : Option V → Finset (Fin n))
    (a : V → ℝ) (K : V → Option V → ℝ)
    (ha : ∀ v, 0 ≤ a v) (hK : ∀ v b, 0 ≤ K v b)
    (hbound : ∀ v b, (characterDependencyGraph X).Adj (some v) b → a v ≤ K v b) :
    |jointCharacterCumulant X| * (∏ v, a v) ≤
      2 ^ Fintype.card V * ∑ p : RootedParent V, ∏ v, K v (p.val v) := by
  let G := characterDependencyGraph X
  let A := {p : RootedParent V // ∀ v, G.Adj (some v) (p.val v)}
  have hc : |jointCharacterCumulant X| ≤ 2 ^ Fintype.card V * (Fintype.card A : ℝ) := by
    have h := abs_jointCharacterCumulant_le_trees X
    simp only [Fintype.card_option, Nat.add_sub_cancel] at h
    apply h.trans
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (spanningTreeCount_le_rootedParents G))
      (by positivity)
  have hs : (Fintype.card A : ℝ) * (∏ v, a v) ≤
      ∑ p : RootedParent V, ∏ v, K v (p.val v) := by
    calc
      _ = ∑ p : RootedParent V,
          if ∀ v, G.Adj (some v) (p.val v) then ∏ v, a v else 0 := by
        rw [← Finset.sum_filter, Finset.sum_subtype
          (p := fun p : RootedParent V => ∀ v, G.Adj (some v) (p.val v))
          (F := inferInstance) _ (by simp)]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, A]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p _
        split_ifs with hp
        · exact Finset.prod_le_prod₀ (fun v _ => ha v) (fun v _ => hbound v _ (hp v))
        · exact Finset.prod_nonneg (fun v _ => hK v _)
  calc
    _ ≤ (2 ^ Fintype.card V * (Fintype.card A : ℝ)) * ∏ v, a v :=
      mul_le_mul_of_nonneg_right hc (Finset.prod_nonneg (fun v _ => ha v))
    _ = 2 ^ Fintype.card V * ((Fintype.card A : ℝ) * ∏ v, a v) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

def mixedVertexWeight {p d : ℕ} (w : Fin d → ComplexParameters n k) :
    (Fin p ⊕ Fin d) → TreeState n k → ℝ
  | .inl _, .inr _ => 1
  | .inr j, .inl I => ‖w j I‖
  | _, _ => 0

theorem mixedVertexWeight_nonneg {p d : ℕ} (w : Fin d → ComplexParameters n k)
    (v : Fin p ⊕ Fin d) (b : TreeState n k) : 0 ≤ mixedVertexWeight w v b := by
  cases v <;> cases b <;> simp only [mixedVertexWeight] <;> positivity

theorem mixedTreeKernel_of_intersect {p d : ℕ} (w : Fin d → ComplexParameters n k)
    (v : Fin p ⊕ Fin d) (a b : TreeState n k)
    (h : ¬Disjoint (treeStateSupport b) (treeStateSupport a)) :
    mixedTreeKernel w v a b = mixedVertexWeight w v b := by
  cases v with
  | inl i =>
    cases b with
    | inl I => rfl
    | inr j =>
      have hj : j ∈ treeStateSupport a := by simpa only [treeStateSupport, Finset.disjoint_singleton_left, not_not] using h
      exact ite_eq_left hj
  | inr j =>
    cases b with
    | inl I => exact ite_eq_left (Finset.not_disjoint_iff_nonempty_inter.mp h)
    | inr i => rfl

def stateCharacterFamily (root : TreeState n k) (x : V → TreeState n k) :
    Option V → Finset (Fin n) := fun v => treeStateSupport (v.elim root x)

theorem abs_stateCumulant_weighted_le {p d : ℕ} (w : Fin d → ComplexParameters n k)
    (root : TreeState n k) (x : (Fin p ⊕ Fin d) → TreeState n k) :
    |jointCharacterCumulant (stateCharacterFamily root x)| *
        (∏ v, mixedVertexWeight w v (x v)) ≤
      2 ^ (p + d) * ∑ T : RootedParent (Fin p ⊕ Fin d), T.weight (mixedTreeKernel w) root x := by
  have h := abs_cumulant_weighted_le_rooted (stateCharacterFamily root x)
    (fun v => mixedVertexWeight w v (x v))
    (fun v b => mixedTreeKernel w v (b.elim root x) (x v))
    (fun v => mixedVertexWeight_nonneg w v (x v))
    (fun v b => by
      cases v with
      | inl i => exact markedTreeKernel_nonneg _ _
      | inr j => exact interactionTreeKernel_nonneg (w j) _ _)
    (fun v b hab => by
      have hh : ¬Disjoint (treeStateSupport (x v)) (treeStateSupport (b.elim root x)) := hab.2
      rw [mixedTreeKernel_of_intersect w v _ _ hh])
  simpa only [Fintype.card_sum, Fintype.card_fin, RootedParent.weight] using h

/-- The rooted sum underlying manuscript equation (15). Here `p` counts
marked spins other than the fixed root. -/
theorem sum_abs_stateCumulant_weighted_le {p d : ℕ} (hk : 1 ≤ k)
    (w : Fin d → ComplexParameters n k) (root : TreeState n k) :
    (∑ x : (Fin p ⊕ Fin d) → TreeState n k,
      |jointCharacterCumulant (stateCharacterFamily root x)| *
        ∏ v, mixedVertexWeight w v (x v)) ≤
      (2 * (k : ℝ)) ^ (p + d) * ((p + d + 1 : ℕ) : ℝ) ^ (p + d) *
        ∏ j, localNorm (w j) := by
  calc
    _ ≤ ∑ x : (Fin p ⊕ Fin d) → TreeState n k,
        2 ^ (p + d) * ∑ T : RootedParent (Fin p ⊕ Fin d), T.weight (mixedTreeKernel w) root x :=
      Finset.sum_le_sum (fun x _ => abs_stateCumulant_weighted_le w root x)
    _ = 2 ^ (p + d) * ∑ T : RootedParent (Fin p ⊕ Fin d),
        ∑ x : (Fin p ⊕ Fin d) → TreeState n k, T.weight (mixedTreeKernel w) root x := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ 2 ^ (p + d) * (((p + d + 1 : ℕ) : ℝ) ^ (p + d) * (k : ℝ) ^ (p + d) *
        ∏ j, localNorm (w j)) :=
      mul_le_mul_of_nonneg_left (sum_all_mixedTreeWeight_le hk w root) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- Absorb the tree count and Taylor factorial into an absolute exponential.
At most three marked spins accompany the distinguished root. -/
theorem sum_abs_stateCumulant_div_factorial_le {p d : ℕ} (hp : p ≤ 3) (hd : 1 ≤ d)
    (hk : 1 ≤ k) (hk4 : k ≤ 4) (w : Fin d → ComplexParameters n k) (root : TreeState n k) :
    (∑ x : (Fin p ⊕ Fin d) → TreeState n k,
      |jointCharacterCumulant (stateCharacterFamily root x)| *
        ∏ v, mixedVertexWeight w v (x v)) / d.factorial ≤
      treeTaylorConstant ^ d * ∏ j, localNorm (w j) := by
  have hpref := tree_taylor_prefactor_le (p := p + 1) hd (by omega) hk4
  have hexp : d + (p + 1) - 1 = p + d := by omega
  have hbase : d + (p + 1) = p + d + 1 := by omega
  rw [hexp, hbase] at hpref
  calc
    _ ≤ ((2 * (k : ℝ)) ^ (p + d) * ((p + d + 1 : ℕ) : ℝ) ^ (p + d) *
        ∏ j, localNorm (w j)) / d.factorial :=
      div_le_div_of_nonneg_right (sum_abs_stateCumulant_weighted_le hk w root) (by positivity)
    _ = ((2 * (k : ℝ)) ^ (p + d) * ((p + d + 1 : ℕ) : ℝ) ^ (p + d) / d.factorial) *
        ∏ j, localNorm (w j) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpref (Finset.prod_nonneg (fun j _ => localNorm_nonneg (w j)))

end

end TensorLB
