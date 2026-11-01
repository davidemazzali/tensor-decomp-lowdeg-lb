module

public import TensorLB.BrokenCircuitCancellation
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Alternating connected-subgraph sums are bounded by trees

An edge is redundant when its endpoints are connected using earlier edges.
Toggling the least such edge preserves connectivity and reverses the sign.
Every surviving connected subgraph is acyclic, which proves the tree bound for
the graph coefficient appearing in the dependency-cumulant argument.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {V E : Type*} [LinearOrder E]

def indexedEdgeGraph (u v : E → V) (F : Finset E) : SimpleGraph V :=
  F.sup (fun e => SimpleGraph.edge (u e) (v e))

omit [LinearOrder E] in
theorem indexedEdgeGraph_mono (u v : E → V) {F H : Finset E} (h : F ⊆ H) :
    indexedEdgeGraph u v F ≤ indexedEdgeGraph u v H := Finset.sup_mono h

theorem indexedEdgeGraph_insert (u v : E → V) (F : Finset E) (e : E) :
    indexedEdgeGraph u v (insert e F) = indexedEdgeGraph u v F ⊔ SimpleGraph.edge (u e) (v e) := by
  simp only [indexedEdgeGraph, Finset.sup_insert, sup_comm]

theorem reachable_sup_redundant_edge {G : SimpleGraph V} {u v : V} (huv : G.Reachable u v)
    (a b : V) : (G ⊔ SimpleGraph.edge u v).Reachable a b ↔ G.Reachable a b := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact .rfl
    | @cons a b c hab w ih =>
      apply SimpleGraph.Reachable.trans _ ih
      rcases hab with hab | hab
      · exact hab.reachable
      · rcases (SimpleGraph.edge_adj u v a b).mp hab with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
        · exact huv
        · exact huv.symm
  · exact SimpleGraph.Reachable.mono le_sup_left

theorem connected_sup_redundant_edge {G : SimpleGraph V} {u v : V}
    (huv : G.Reachable u v) : (G ⊔ SimpleGraph.edge u v).Connected ↔ G.Connected := by
  simp only [SimpleGraph.connected_iff, SimpleGraph.Preconnected,
    reachable_sup_redundant_edge huv]

theorem indexedEdgeGraph_toggle_connected (u v : E → V) (F : Finset E) (e : E)
    (he : (indexedEdgeGraph u v (F.filter (· < e))).Reachable (u e) (v e)) :
    (indexedEdgeGraph u v (toggleEdge F e)).Connected ↔ (indexedEdgeGraph u v F).Connected := by
  by_cases heF : e ∈ F
  · rw [toggleEdge, ite_eq_left heF]
    have hp : F.filter (· < e) ⊆ F.erase e := by
      intro a ha
      obtain ⟨haF, hae⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_erase.mpr ⟨ne_of_lt hae, haF⟩
    have hr := he.mono (indexedEdgeGraph_mono u v hp)
    have hgraph : indexedEdgeGraph u v F =
        indexedEdgeGraph u v (F.erase e) ⊔ SimpleGraph.edge (u e) (v e) := by
      rw [← indexedEdgeGraph_insert, Finset.insert_erase heF]
    rw [hgraph]
    exact (connected_sup_redundant_edge hr).symm
  · rw [toggleEdge, ite_eq_right heF, indexedEdgeGraph_insert]
    exact connected_sup_redundant_edge (he.mono (indexedEdgeGraph_mono u v (Finset.filter_subset _ _)))

/-- The surviving edge sets are forests. This uses only increasing-edge
insertion, with no appeal to a graph-counting formula. -/
theorem indexedEdgeGraph_acyclic_of_no_redundant (u v : E → V) (F : Finset E)
    (hF : ∀ e ∈ F, ¬(indexedEdgeGraph u v (F.filter (· < e))).Reachable (u e) (v e)) :
    (indexedEdgeGraph u v F).IsAcyclic := by
  induction F using Finset.induction_on_max with
  | empty => exact SimpleGraph.isAcyclic_bot
  | insert e F hmax ih =>
    have hprefix : (insert e F).filter (· < e) = F := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | ha, hae⟩
        · exact False.elim (lt_irrefl _ hae)
        · exact ha
      · intro ha
        exact ⟨Or.inr ha, hmax a ha⟩
    have hnot := hF e (Finset.mem_insert_self _ _)
    rw [hprefix] at hnot
    rw [indexedEdgeGraph_insert]
    apply SimpleGraph.IsAcyclic.sup_edge_of_not_reachable hnot
    apply ih
    intro a ha
    have h := hF a (Finset.mem_insert_of_mem ha)
    have hfilter : (insert e F).filter (· < a) = F.filter (· < a) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hb, hba⟩
        · exact False.elim ((not_lt_of_ge (hmax a ha).le) hba)
        · exact ⟨hb, hba⟩
      · tauto
    rwa [hfilter] at h

variable [Fintype E]

/-- The graph coefficient bound used after grouping cumulant partitions by
their connected refinement. Edge labels are retained, so this statement also
allows several labels with the same endpoints. -/
theorem abs_connected_graph_sum_le_trees (u v : E → V) :
    |∑ F ∈ Finset.univ.filter (fun F : Finset E => (indexedEdgeGraph u v F).Connected),
      (-1 : ℝ) ^ F.card| ≤
      ((Finset.univ.filter (fun F : Finset E => (indexedEdgeGraph u v F).IsTree)).card : ℝ) := by
  let R := fun e F => (indexedEdgeGraph u v F).Reachable (u e) (v e)
  have h := abs_signed_family_sum_le R
    (fun F => (indexedEdgeGraph u v F).Connected) (indexedEdgeGraph_toggle_connected u v)
  apply h.trans
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro F hF
  obtain ⟨_, hconn, hred⟩ := Finset.mem_filter.mp hF
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ⟨hconn, ?_⟩⟩
  apply indexedEdgeGraph_acyclic_of_no_redundant u v F
  intro e _ he
  apply hred
  exact ⟨e, (mem_redundantEdges R F e).mpr he⟩

end

end TensorLB
