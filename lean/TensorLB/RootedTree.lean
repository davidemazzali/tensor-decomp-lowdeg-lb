module

public import TensorLB.TreeMajorant
public import Mathlib.Order.Extension.Well
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Option

/-!
# Rooted parent maps and weighted tree sums

The root is external to the vertex type. `none` is an edge to the root, and
`some v` is an edge to a nonroot parent. Well-foundedness excludes cycles. This
representation gives an elementary upper bound on the number of trees and
allows leaf summation without choosing extra combinatorial data to count.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

def RootedParent (V : Type*) :=
  {p : V → Option V // WellFounded (fun a b => p b = some a)}

namespace RootedParent

variable {V S : Type*} [Fintype V]

instance : Fintype (RootedParent V) :=
  inferInstanceAs (Fintype {p : V → Option V // WellFounded (fun a b => p b = some a)})

theorem card_le : Fintype.card (RootedParent V) ≤ (Fintype.card V + 1) ^ Fintype.card V := by
  calc
    _ ≤ Fintype.card (V → Option V) := Fintype.card_subtype_le _
    _ = _ := by simp

/-- Every tree admits an ordering with parents before children. The ordering
is only a proof device and does not contribute to the count. -/
theorem exists_order (p : RootedParent V) :
    ∃ e : Fin (Fintype.card V) ≃ V,
      ∀ i j, p.val (e j) = some (e i) → i < j := by
  let R := fun a b => p.val b = some a
  let : WellFounded R := p.property
  let : LinearOrder V := WellFounded.wellOrderExtension R
  let e := Fintype.orderIsoFinOfCardEq V rfl
  refine ⟨e.toEquiv, ?_⟩
  intro i j hij
  apply e.lt_iff_lt.mp
  exact Prod.Lex.left _ _ (WellFounded.rank_lt_of_rel hij)

def weight (p : RootedParent V) (K : V → S → S → ℝ) (root : S) (x : V → S) : ℝ :=
  ∏ v, K v ((p.val v).elim root x) (x v)

theorem weight_nonneg (p : RootedParent V) (K : V → S → S → ℝ) (root : S)
    (hK : ∀ v a b, 0 ≤ K v a b) (x : V → S) : 0 ≤ p.weight K root x :=
  Finset.prod_nonneg (fun v _ => hK v _ _)

/-- A rooted tree costs the product of its one-child bounds. -/
theorem sum_weight_le [DecidableEq V] [Fintype S] (p : RootedParent V) (K : V → S → S → ℝ)
    (root : S) (c : V → ℝ) (hK : ∀ v a b, 0 ≤ K v a b)
    (hc : ∀ v, 0 ≤ c v) (hs : ∀ v a, (∑ b, K v a b) ≤ c v) :
    (∑ x : V → S, p.weight K root x) ≤ ∏ v, c v := by
  obtain ⟨e, he⟩ := p.exists_order
  let parentState (j : Fin (Fintype.card V)) (hist : Fin j.val → S) : S :=
    (p.val (e j)).elim root (fun v =>
      if h : (e.symm v).val < j.val then hist ⟨(e.symm v).val, h⟩ else root)
  let L (j : Fin (Fintype.card V)) (hist : Fin j.val → S) (a : S) : ℝ :=
    K (e j) (parentState j hist) a
  let aEquiv : (Fin (Fintype.card V) → S) ≃ (V → S) :=
    e.arrowCongr (Equiv.refl S)
  have hparent (y : Fin (Fintype.card V) → S) (j : Fin (Fintype.card V)) :
      parentState j (tupleHistory y j) = (p.val (e j)).elim root (aEquiv y) := by
    dsimp only [parentState]
    cases hp : p.val (e j) with
    | none => rfl
    | some v =>
      have hv : e.symm v < j := he (e.symm v) j (by simpa only [e.apply_symm_apply] using hp)
      have hv' : (e.symm v).val < j.val := hv
      simp only [Option.elim_some, dite_eq_left hv']
      rfl
  have hw (y : Fin (Fintype.card V) → S) :
      sequentialWeight L y = p.weight K root (aEquiv y) := by
    unfold sequentialWeight weight
    rw [← Equiv.prod_comp e]
    apply Finset.prod_congr rfl
    intro j _
    dsimp only [L]
    rw [hparent]
    congr 1
    change y j = y (e.symm (e j))
    rw [e.symm_apply_apply]
  calc
    _ = ∑ y : Fin (Fintype.card V) → S, sequentialWeight L y := by
      rw [← Equiv.sum_comp aEquiv]
      exact Finset.sum_congr rfl (fun y _ => (hw y).symm)
    _ ≤ ∏ j : Fin (Fintype.card V), c (e j) :=
      sum_sequentialWeight_le L (fun j => c (e j)) (fun j _ _ => hK (e j) _ _)
        (fun j => hc (e j)) (fun j _ => hs (e j) _)
    _ = _ := Equiv.prod_comp e c

end RootedParent

end

end TensorLB
