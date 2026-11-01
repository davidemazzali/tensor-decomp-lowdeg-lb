module

public import TensorLB.GraphQuotientTrees

/-!
# Counting connected partitions and quotient trees

A quotient tree lifts to a spanning tree with connected blocks. In a fixed
spanning tree, such a partition is determined by a subset of its edges. The
resulting injection gives the factor `2^(|V|-1)` in the cumulant tree estimate.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def partitionInternalEdges (G : SimpleGraph V) (P : VertexPartition V) : Finset G.edgeSet :=
  Finset.univ.filter (fun e => partitionSetoid P (graphEdgeLeft G e) (graphEdgeRight G e))

omit [Fintype V] [DecidableEq V] in
theorem graphEdge_relation (G : SimpleGraph V) (e : G.edgeSet) (s : Setoid V)
    {x y : V} (he : e.val = s(x, y)) :
    s (graphEdgeLeft G e) (graphEdgeRight G e) ↔ s x y := by
  have h := (graphEdge_mk G e).trans he
  rcases Sym2.eq_iff.mp h with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · rw [hl, hr]
  · rw [hl, hr]
    exact ⟨s.symm, s.symm⟩

theorem edgeSubgraph_internalEdges (G : SimpleGraph V) (P : VertexPartition V) :
    edgeSubgraph G (partitionInternalEdges G P) = withinPartitionGraph G P := by
  ext x y
  rw [edgeSubgraph_adj]
  constructor
  · rintro ⟨e, he, hxy⟩
    refine ⟨G.mem_edgeSet.mp (hxy ▸ e.property), ?_⟩
    exact (graphEdge_relation G e (partitionSetoid P) hxy).mp (Finset.mem_filter.mp he).2
  · rintro ⟨hxy, hP⟩
    let e : G.edgeSet := ⟨s(x, y), G.mem_edgeSet.mpr hxy⟩
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (graphEdge_relation G e (partitionSetoid P) rfl).mpr hP⟩, rfl⟩

def connectedPartitionCount (G : SimpleGraph V) : ℕ :=
  Fintype.card {R : VertexPartition V // connectedRefinement G R = R}

theorem connectedPartitionCount_le (G : SimpleGraph V) :
    connectedPartitionCount G ≤ 2 ^ Fintype.card G.edgeSet := by
  change Fintype.card {R : VertexPartition V // connectedRefinement G R = R} ≤ _
  rw [← Fintype.card_finset]
  apply Fintype.card_le_of_injective (fun R => partitionInternalEdges G R.val)
  intro R P h
  apply Subtype.ext
  have hg := congrArg (fun F => graphPartition (edgeSubgraph G F)) h
  rw [edgeSubgraph_internalEdges, edgeSubgraph_internalEdges] at hg
  change connectedRefinement G R.val = connectedRefinement G P.val at hg
  rwa [R.property, P.property] at hg

theorem connectedPartitionCount_tree_le (T : SimpleGraph V) (hT : T.IsTree) :
    connectedPartitionCount T ≤ 2 ^ (Fintype.card V - 1) := by
  have hc : Fintype.card T.edgeSet = Fintype.card V - 1 := by
    have h := hT.card_edgeFinset
    rw [SimpleGraph.edgeFinset_card] at h
    omega
  simpa only [hc] using connectedPartitionCount_le T

def ConnectedTreePair (G : SimpleGraph V) :=
  Σ R : {R : VertexPartition V // connectedRefinement G R = R},
    {Q : SimpleGraph (Quotient (partitionSetoid R.val)) //
      Q ≤ quotientPartitionGraph G R.val ∧ Q.IsTree}

def TreePartitionPair (G : SimpleGraph V) :=
  Σ T : {T : SimpleGraph V // T ≤ G ∧ T.IsTree},
    {R : VertexPartition V // connectedRefinement T.val R = R}

instance (G : SimpleGraph V) : Fintype (ConnectedTreePair G) :=
  inferInstanceAs (Fintype (Σ R : {R : VertexPartition V // connectedRefinement G R = R},
    {Q : SimpleGraph (Quotient (partitionSetoid R.val)) //
      Q ≤ quotientPartitionGraph G R.val ∧ Q.IsTree}))

instance (G : SimpleGraph V) : Fintype (TreePartitionPair G) :=
  inferInstanceAs (Fintype (Σ T : {T : SimpleGraph V // T ≤ G ∧ T.IsTree},
    {R : VertexPartition V // connectedRefinement T.val R = R}))

variable [Nonempty V]

def liftConnectedTreePair (G : SimpleGraph V) (p : ConnectedTreePair G) : TreePartitionPair G :=
  let h := exists_tree_realizing_quotient G p.1.val p.1.property p.2.val p.2.property.1 p.2.property.2
  ⟨⟨h.choose, h.choose_spec.1, h.choose_spec.2.1⟩, ⟨p.1.val, h.choose_spec.2.2.1⟩⟩

theorem liftConnectedTreePair_partition (G : SimpleGraph V) (p : ConnectedTreePair G) :
    (liftConnectedTreePair G p).2.val = p.1.val := rfl

theorem liftConnectedTreePair_quotient (G : SimpleGraph V) (p : ConnectedTreePair G) :
    quotientPartitionGraph (liftConnectedTreePair G p).1.val p.1.val = p.2.val :=
  (exists_tree_realizing_quotient G p.1.val p.1.property p.2.val
    p.2.property.1 p.2.property.2).choose_spec.2.2.2

theorem liftConnectedTreePair_injective (G : SimpleGraph V) :
    Function.Injective (liftConnectedTreePair G) := by
  rintro ⟨⟨R, hR⟩, Q⟩ ⟨⟨S, hS⟩, U⟩ h
  have hRS := congrArg (fun p : TreePartitionPair G => p.2.val) h
  change R = S at hRS
  subst S
  have hT := congrArg (fun p : TreePartitionPair G => p.1.val) h
  have hQU : Q.val = U.val := by
    rw [← liftConnectedTreePair_quotient G ⟨⟨R, hR⟩, Q⟩,
      ← liftConnectedTreePair_quotient G ⟨⟨R, hS⟩, U⟩]
    exact congrArg (fun T => quotientPartitionGraph T R) hT
  have hQU' : Q = U := Subtype.ext hQU
  subst U
  rfl

theorem sum_connected_quotient_trees_le (G : SimpleGraph V) :
    (∑ R : {R : VertexPartition V // connectedRefinement G R = R},
      spanningTreeCount (quotientPartitionGraph G R.val)) ≤
      spanningTreeCount G * 2 ^ (Fintype.card V - 1) := by
  calc
    _ = Fintype.card (ConnectedTreePair G) := by
      change _ = Fintype.card (Σ R : {R : VertexPartition V // connectedRefinement G R = R},
        {Q : SimpleGraph (Quotient (partitionSetoid R.val)) //
          Q ≤ quotientPartitionGraph G R.val ∧ Q.IsTree})
      rw [Fintype.card_sigma]
      rfl
    _ ≤ Fintype.card (TreePartitionPair G) :=
      Fintype.card_le_of_injective _ (liftConnectedTreePair_injective G)
    _ = ∑ T : {T : SimpleGraph V // T ≤ G ∧ T.IsTree}, connectedPartitionCount T.val := by
      change Fintype.card (Σ T : {T : SimpleGraph V // T ≤ G ∧ T.IsTree},
        {R : VertexPartition V // connectedRefinement T.val R = R}) = _
      rw [Fintype.card_sigma]
      rfl
    _ ≤ ∑ _T : {T : SimpleGraph V // T ≤ G ∧ T.IsTree}, 2 ^ (Fintype.card V - 1) :=
      Finset.sum_le_sum (fun T _ => connectedPartitionCount_tree_le T.val T.property.2)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, spanningTreeCount]

end

end TensorLB
