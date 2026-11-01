module

public import TensorLB.CumulantTreeBound
public import TensorLB.RootedTree

/-!
# Orienting a spanning tree toward an external root

A parent is selected along a shortest path to the root. Distance strictly
decreases, giving the well-founded parent map used by the weighted tree sum.
Its edges recover the original tree, so this orientation is injective.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {V : Type*}

theorem connected_root_predecessor (G : SimpleGraph (Option V)) (hG : G.Connected) (v : V) :
    ∃ a : Option V, G.Adj (some v) a ∧ G.dist a none < G.dist (some v) none := by
  obtain ⟨w, hw⟩ := hG.exists_walk_length_eq_dist (some v) none
  cases w with
  | @cons _ a _ hadj tail =>
    refine ⟨a, hadj, ?_⟩
    have h := SimpleGraph.dist_le tail
    simp only [SimpleGraph.Walk.length_cons] at hw
    omega

def treeParent (T : SimpleGraph (Option V)) (hT : T.IsTree) : RootedParent V := by
  let parent := fun v => (connected_root_predecessor T hT.connected v).choose
  refine ⟨parent, (InvImage.wf (fun v => T.dist (some v) none) Nat.lt_wfRel.wf).mono ?_⟩
  intro a b hab
  have h := (connected_root_predecessor T hT.connected b).choose_spec.2
  change parent b = some a at hab
  change T.dist (parent b) none < T.dist (some b) none at h
  rwa [hab] at h

theorem treeParent_adj (T : SimpleGraph (Option V)) (hT : T.IsTree) (v : V) :
    T.Adj (some v) ((treeParent T hT).val v) :=
  (connected_root_predecessor T hT.connected v).choose_spec.1

namespace RootedParent

variable [Fintype V]

def graph (p : RootedParent V) : SimpleGraph (Option V) :=
  Finset.univ.sup (fun v => SimpleGraph.edge (some v) (p.val v))

theorem parent_ne_self (p : RootedParent V) (v : V) : p.val v ≠ some v := by
  obtain ⟨e, he⟩ := p.exists_order
  intro hv
  have h := he (e.symm v) (e.symm v) (by simpa only [e.apply_symm_apply] using hv)
  exact lt_irrefl _ h

theorem graph_parent_adj (p : RootedParent V) (v : V) : p.graph.Adj (some v) (p.val v) := by
  apply (Finset.le_sup (f := fun v => SimpleGraph.edge (some v) (p.val v)) (Finset.mem_univ v))
  apply (SimpleGraph.edge_adj _ _ _ _).mpr
  exact ⟨Or.inl ⟨rfl, rfl⟩, (p.parent_ne_self v).symm⟩

theorem graph_reachable_root (p : RootedParent V) (v : V) : p.graph.Reachable (some v) none := by
  induction v using p.property.induction with
  | h v ih =>
    have hadj := p.graph_parent_adj v
    cases hp : p.val v with
    | none => simpa only [hp] using hadj.reachable
    | some w =>
      rw [hp] at hadj
      exact hadj.reachable.trans (ih w hp)

theorem graph_connected (p : RootedParent V) : p.graph.Connected := by
  apply (p.graph.connected_iff_exists_forall_reachable).mpr
  refine ⟨none, ?_⟩
  intro a
  cases a with
  | none => exact .rfl
  | some v => exact (p.graph_reachable_root v).symm

theorem graph_le_iff (p : RootedParent V) (G : SimpleGraph (Option V)) :
    p.graph ≤ G ↔ ∀ v, G.Adj (some v) (p.val v) := by
  constructor
  · exact fun h v => h (p.graph_parent_adj v)
  · intro h
    apply Finset.sup_le
    intro v _
    exact (SimpleGraph.edge_le_iff G).mpr (Or.inr (h v))

end RootedParent

variable [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem treeParent_graph (T : SimpleGraph (Option V)) (hT : T.IsTree) :
    (treeParent T hT).graph = T := by
  have hle := (RootedParent.graph_le_iff _ T).mpr (treeParent_adj T hT)
  exact (SimpleGraph.isTree_iff_minimal_connected.mp hT).eq_of_le
    (RootedParent.graph_connected _) hle

def treeParentEmbedding (G : SimpleGraph (Option V)) :
    {T : SimpleGraph (Option V) // T ≤ G ∧ T.IsTree} ↪
      {p : RootedParent V // ∀ v, G.Adj (some v) (p.val v)} where
  toFun T := ⟨treeParent T.val T.property.2, fun v => T.property.1 (treeParent_adj _ _ v)⟩
  inj' := by
    intro T U h
    apply Subtype.ext
    have hp := congrArg (fun p : {p : RootedParent V // ∀ v, G.Adj (some v) (p.val v)} => p.val.graph) h
    simpa only [treeParent_graph] using hp

theorem spanningTreeCount_le_rootedParents (G : SimpleGraph (Option V)) :
    spanningTreeCount G ≤
      Fintype.card {p : RootedParent V // ∀ v, G.Adj (some v) (p.val v)} :=
  Fintype.card_le_of_injective _ (treeParentEmbedding G).injective

end

end TensorLB
