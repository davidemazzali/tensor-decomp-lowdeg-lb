module

public import TensorLB.QuotientCumulant

/-!
# A graph coefficient is bounded by its spanning trees

The edge-indexed cancellation theorem is specialized to the actual undirected
edges of a simple graph. Thus every surviving edge set gives a distinct
spanning tree, with no multiplicity from edge labels or orientations.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def graphEdgeLeft (G : SimpleGraph V) (e : G.edgeSet) : V := e.val.out.1

def graphEdgeRight (G : SimpleGraph V) (e : G.edgeSet) : V := e.val.out.2

omit [Fintype V] [DecidableEq V] in
theorem graphEdge_mk (G : SimpleGraph V) (e : G.edgeSet) :
    s(graphEdgeLeft G e, graphEdgeRight G e) = e.val := e.val.out_eq

omit [Fintype V] [DecidableEq V] in
theorem graphEdge_adj (G : SimpleGraph V) (e : G.edgeSet) :
    G.Adj (graphEdgeLeft G e) (graphEdgeRight G e) := by
  apply G.mem_edgeSet.mp
  rw [graphEdge_mk]
  exact e.property

def edgeSubgraph (G : SimpleGraph V) (F : Finset G.edgeSet) : SimpleGraph V :=
  indexedEdgeGraph (graphEdgeLeft G) (graphEdgeRight G) F

omit [Fintype V] [DecidableEq V] in
theorem edgeSubgraph_adj (G : SimpleGraph V) (F : Finset G.edgeSet) (x y : V) :
    (edgeSubgraph G F).Adj x y ↔ ∃ e ∈ F, e.val = s(x, y) := by
  simp only [edgeSubgraph, indexedEdgeGraph, Finset.sup_eq_iSup,
    SimpleGraph.iSup_adj, SimpleGraph.adj_edge, graphEdge_mk]
  constructor
  · rintro ⟨e, he, hxy, _⟩
    exact ⟨e, he, hxy⟩
  · rintro ⟨e, he, hxy⟩
    refine ⟨e, he, hxy, ?_⟩
    have h := e.property
    rw [hxy] at h
    exact (G.mem_edgeSet.mp h).ne

omit [Fintype V] [DecidableEq V] in
theorem edgeSubgraph_le (G : SimpleGraph V) (F : Finset G.edgeSet) : edgeSubgraph G F ≤ G := by
  intro x y hxy
  obtain ⟨e, _, he⟩ := (edgeSubgraph_adj G F x y).mp hxy
  exact G.mem_edgeSet.mp (he ▸ e.property)

omit [Fintype V] [DecidableEq V] in
theorem edgeSubgraph_contains (G : SimpleGraph V) (F : Finset G.edgeSet) (e : G.edgeSet) :
    (edgeSubgraph G F).Adj (graphEdgeLeft G e) (graphEdgeRight G e) ↔ e ∈ F := by
  rw [edgeSubgraph_adj, graphEdge_mk]
  constructor
  · rintro ⟨f, hf, he⟩
    exact (Subtype.ext he) ▸ hf
  · intro he
    exact ⟨e, he, rfl⟩

omit [Fintype V] [DecidableEq V] in
theorem edgeSubgraph_injective (G : SimpleGraph V) : Function.Injective (edgeSubgraph G) := by
  intro F H h
  ext e
  rw [← edgeSubgraph_contains G F e, h, edgeSubgraph_contains]

theorem independentPartition_edges (G : SimpleGraph V) (P : VertexPartition V) :
    IndependentPartition G P ↔ ∀ e : G.edgeSet,
      ¬partitionSetoid P (graphEdgeLeft G e) (graphEdgeRight G e) := by
  constructor
  · exact fun h e => h _ _ (graphEdge_adj G e)
  · intro h x y hxy hP
    let e : G.edgeSet := ⟨s(x, y), G.mem_edgeSet.mpr hxy⟩
    apply h e
    have he := graphEdge_mk G e
    change s(graphEdgeLeft G e, graphEdgeRight G e) = s(x, y) at he
    rcases Sym2.eq_iff.mp he with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · simpa only [hl, hr] using hP
    · simpa only [hl, hr] using (partitionSetoid P).symm hP

/-- The number of spanning trees, as distinct spanning subgraphs. -/
def spanningTreeCount (G : SimpleGraph V) : ℕ :=
  Fintype.card {T : SimpleGraph V // T ≤ G ∧ T.IsTree}

theorem edgeSubgraph_tree_count_le (G : SimpleGraph V) :
    (Finset.univ.filter (fun F : Finset G.edgeSet => (edgeSubgraph G F).IsTree)).card ≤
      spanningTreeCount G := by
  rw [← Fintype.card_coe]
  apply Fintype.card_le_of_injective
    (fun F => (⟨edgeSubgraph G F.val, edgeSubgraph_le G F.val,
      by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using F.property⟩ :
        {T : SimpleGraph V // T ≤ G ∧ T.IsTree}))
  intro F H h
  apply Subtype.ext
  exact edgeSubgraph_injective G (congrArg Subtype.val h)

theorem abs_graphCumulantCoefficient_le_spanningTreeCount [Nonempty V] (G : SimpleGraph V) :
    |graphCumulantCoefficient G| ≤ (spanningTreeCount G : ℝ) := by
  let : LinearOrder G.edgeSet :=
    LinearOrder.lift' (Fintype.equivFin G.edgeSet) (Fintype.equivFin G.edgeSet).injective
  have he : graphCumulantCoefficient G =
      ∑ P ∈ Finset.univ.filter (fun P : VertexPartition V =>
        ∀ e : G.edgeSet, ¬partitionSetoid P (graphEdgeLeft G e) (graphEdgeRight G e)),
        cumulantMobius P.parts.card := by
    rw [Finset.sum_subtype (p := fun P : VertexPartition V => IndependentPartition G P) _
      (by intro P; simp only [Finset.mem_filter, Finset.mem_univ, true_and, independentPartition_edges])]
    rfl
  rw [he]
  apply (abs_independentPartition_coefficient_le_trees (graphEdgeLeft G) (graphEdgeRight G)).trans
  exact Nat.cast_le.mpr (edgeSubgraph_tree_count_le G)

end

end TensorLB
