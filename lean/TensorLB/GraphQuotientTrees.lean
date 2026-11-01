module

public import TensorLB.GraphCoefficientBound

/-!
# Lifting a quotient tree through connected blocks

A tree on the quotient can be realized by a spanning tree of the original
graph while preserving connectivity inside every partition block. Extending
a spanning forest avoids making arbitrary edge lifts part of the counting data.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {V W : Type*}

theorem reachable_graphMap (G : SimpleGraph V) (f : V → W) {x y : V}
    (h : G.Reachable x y) : (G.map f).Reachable (f x) (f y) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact .rfl
  | @cons a b c hab w ih =>
    by_cases he : f a = f b
    · exact he ▸ ih
    · exact (SimpleGraph.map_adj_apply' hab he).reachable.trans ih

theorem connected_graphMap (G : SimpleGraph V) (f : V → W) (hG : G.Connected)
    (hf : Function.Surjective f) : (G.map f).Connected := by
  let : Nonempty W := Nonempty.map f hG.nonempty
  apply SimpleGraph.Connected.mk
  intro a b
  obtain ⟨x, rfl⟩ := hf a
  obtain ⟨y, rfl⟩ := hf b
  exact reachable_graphMap G f (hG x y)

theorem connected_of_graphMap [Nonempty V] (G : SimpleGraph V) (f : V → W)
    (hG : (G.map f).Connected)
    (hfiber : ∀ x y, f x = f y → G.Reachable x y) : G.Connected := by
  have lift : ∀ a b, (G.map f).Reachable a b →
      ∀ x y, f x = a → f y = b → G.Reachable x y := by
    rintro a b ⟨w⟩
    induction w with
    | nil =>
      intro x y hx hy
      exact hfiber x y (hx.trans hy.symm)
    | @cons a b c hab w ih =>
      intro x y hx hy
      obtain ⟨_, u, v, huv, hu, hv⟩ := (SimpleGraph.map_adj' f G a b).mp hab
      exact (hfiber x u (hx.trans hu.symm)).trans (huv.reachable.trans (ih v y hv hy))
  exact SimpleGraph.Connected.mk (fun x y => lift _ _ (hG (f x) (f y)) x y rfl rfl)

variable [Fintype V] [DecidableEq V]

def quotientTreeLift (G : SimpleGraph V) (R : VertexPartition V)
    (Q : SimpleGraph (Quotient (partitionSetoid R))) : SimpleGraph V :=
  withinPartitionGraph G R ⊔ (G ⊓ Q.comap (Quotient.mk (partitionSetoid R)))

theorem quotientTreeLift_le (G : SimpleGraph V) (R : VertexPartition V)
    (Q : SimpleGraph (Quotient (partitionSetoid R))) : quotientTreeLift G R Q ≤ G := by
  apply sup_le
  · exact fun _ _ h => h.1
  · exact inf_le_left

theorem quotientTreeLift_map (G : SimpleGraph V) (R : VertexPartition V)
    (Q : SimpleGraph (Quotient (partitionSetoid R))) (hQ : Q ≤ quotientPartitionGraph G R) :
    (quotientTreeLift G R Q).map (Quotient.mk (partitionSetoid R)) = Q := by
  ext a b
  constructor
  · intro hab
    obtain ⟨hne, x, y, hxy, rfl, rfl⟩ := (SimpleGraph.map_adj' _ _ _ _).mp hab
    rcases hxy with hxy | hxy
    · exact False.elim (hne (Quotient.sound hxy.2))
    · exact hxy.2
  · intro hab
    obtain ⟨hne, x, y, hxy, hx, hy⟩ := (SimpleGraph.map_adj' _ _ _ _).mp (hQ hab)
    apply (SimpleGraph.map_adj' _ _ _ _).mpr
    refine ⟨hne, x, y, Or.inr ⟨hxy, ?_⟩, hx, hy⟩
    change Q.Adj (Quotient.mk _ x) (Quotient.mk _ y)
    rw [hx, hy]
    exact hab

theorem quotientTreeLift_connected [Nonempty V] (G : SimpleGraph V) (R : VertexPartition V)
    (hR : connectedRefinement G R = R)
    (Q : SimpleGraph (Quotient (partitionSetoid R))) (hQ : Q ≤ quotientPartitionGraph G R)
    (hconn : Q.Connected) : (quotientTreeLift G R Q).Connected := by
  apply connected_of_graphMap _ (Quotient.mk (partitionSetoid R))
  · rw [quotientTreeLift_map G R Q hQ]
    exact hconn
  · intro x y hxy
    have hr : partitionSetoid (connectedRefinement G R) x y := by
      rw [hR]
      exact Quotient.exact hxy
    have hreach := (connectedRefinement_rel G R x y).mp hr
    exact hreach.mono le_sup_left

/-- A quotient spanning tree has a realization whose blocks remain connected.
Both the partition and quotient tree can be recovered from that realization. -/
theorem exists_tree_realizing_quotient [Nonempty V] (G : SimpleGraph V) (R : VertexPartition V)
    (hR : connectedRefinement G R = R)
    (Q : SimpleGraph (Quotient (partitionSetoid R))) (hQ : Q ≤ quotientPartitionGraph G R)
    (hQT : Q.IsTree) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧ connectedRefinement T R = R ∧
      quotientPartitionGraph T R = Q := by
  obtain ⟨S, hSle, hSacyc, hSreach⟩ := (withinPartitionGraph G R).exists_isAcyclic_reachable_eq_le
  have hconn := quotientTreeLift_connected G R hR Q hQ hQT.connected
  obtain ⟨T, hST, hTH, hT⟩ := hconn.exists_isTree_le_of_le_of_isAcyclic
    (hSle.trans le_sup_left) hSacyc
  refine ⟨T, hTH.trans (quotientTreeLift_le G R Q), hT, ?_, ?_⟩
  · apply le_antisymm (connectedRefinement_le T R)
    apply (partitionSetoid_le_iff _ _).mp
    intro x y hxy
    apply (connectedRefinement_rel T R x y).mpr
    have hs : S.Reachable x y := by
      rw [hSreach]
      apply (connectedRefinement_rel G R x y).mp
      rwa [hR]
    apply hs.mono
    exact fun a b hab => ⟨hST hab, (hSle hab).2⟩
  · have hmap : quotientPartitionGraph T R ≤ Q := by
      rw [← quotientTreeLift_map G R Q hQ]
      exact SimpleGraph.map_monotone _ hTH
    have hmapconn : (quotientPartitionGraph T R).Connected :=
      connected_graphMap T (Quotient.mk (partitionSetoid R)) hT.connected Quotient.mk_surjective
    exact le_antisymm hmap
      ((SimpleGraph.isTree_iff_minimal_connected.mp hQT).le_of_le hmapconn hmap)

end

end TensorLB
