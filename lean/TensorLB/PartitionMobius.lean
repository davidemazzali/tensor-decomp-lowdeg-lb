module

public import TensorLB.OrderedPartitionBridge
public import TensorLB.GraphTreeCancellation
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Partition Möbius cancellation and graph coefficients

The signed factorial weights cancel over every nontrivial coarsening interval.
Applied to connected-component partitions, this identifies the alternating
connected-subgraph sum with the independent-partition coefficient.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem sum_vertexPartition_mobius :
    (∑ P : VertexPartition V, cumulantMobius P.parts.card) =
      if Fintype.card V = 1 then 1 else 0 := by
  rw [sum_partition_by_card_relabel (Fintype.equivFin V)]
  exact sum_finPartition_mobius (Fintype.card_pos (α := V))

theorem partition_card_pos (P : VertexPartition V) : 0 < P.parts.card := by
  rw [← card_partition_quotient]
  let : Nonempty (Quotient (partitionSetoid P)) := ⟨Quotient.mk _ (Classical.arbitrary V)⟩
  exact Fintype.card_pos

theorem sum_coarsening_mobius (P : VertexPartition V) :
    (∑ Q : {Q : VertexPartition V // P ≤ Q}, cumulantMobius Q.val.parts.card) =
      if P.parts.card = 1 then 1 else 0 := by
  let : Nonempty (Quotient (partitionSetoid P)) := ⟨Quotient.mk _ (Classical.arbitrary V)⟩
  rw [sum_coarsening_by_card, sum_vertexPartition_mobius, card_partition_quotient]

def graphPartition (G : SimpleGraph V) : VertexPartition V :=
  Finpartition.ofSetoid G.reachableSetoid

theorem graphPartition_card_one (G : SimpleGraph V) :
    (graphPartition G).parts.card = 1 ↔ G.Connected := by
  rw [← card_partition_quotient]
  change Fintype.card (Quotient (partitionSetoid (Finpartition.ofSetoid G.reachableSetoid))) = 1 ↔ _
  rw [partitionSetoid_ofSetoid G.reachableSetoid]
  constructor
  · intro h
    obtain ⟨q, hq⟩ := Fintype.card_eq_one_iff.mp h
    apply SimpleGraph.Connected.mk
    intro x y
    exact Quotient.exact ((hq (Quotient.mk _ x)).trans (hq (Quotient.mk _ y)).symm)
  · intro h
    let x : V := Classical.arbitrary V
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨Quotient.mk _ x, ?_⟩
    intro q
    induction q using Quotient.inductionOn with
    | _ y => exact Quotient.sound (h y x)

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem reachableSetoid_le_iff (G : SimpleGraph V) (s : Setoid V) :
    G.reachableSetoid ≤ s ↔ ∀ x y, G.Adj x y → s x y := by
  constructor
  · intro h x y hxy
    exact h hxy.reachable
  · intro h x y hxy
    obtain ⟨w⟩ := hxy
    induction w with
    | nil => exact s.refl _
    | @cons a b c hab w ih => exact s.trans (h a b hab) ih

omit [Nonempty V] in
theorem graphPartition_le_iff (G : SimpleGraph V) (P : VertexPartition V) :
    graphPartition G ≤ P ↔ ∀ x y, G.Adj x y → partitionSetoid P x y := by
  rw [← partitionSetoid_le_iff, graphPartition,
    partitionSetoid_ofSetoid G.reachableSetoid, reachableSetoid_le_iff]

variable {E : Type*} [Fintype E] [LinearOrder E]

omit [Nonempty V] [Fintype E] in
theorem edgeGraphPartition_le_iff (u v : E → V) (F : Finset E) (P : VertexPartition V) :
    graphPartition (indexedEdgeGraph u v F) ≤ P ↔
      ∀ e ∈ F, partitionSetoid P (u e) (v e) := by
  rw [graphPartition_le_iff]
  constructor
  · intro h e he
    by_cases huv : u e = v e
    · rw [huv]
    · apply h
      apply (Finset.le_sup (f := fun e => SimpleGraph.edge (u e) (v e)) he)
      exact (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩
  · intro h x y hxy
    induction F using Finset.induction_on with
    | empty => exact False.elim hxy
    | @insert e F he ih =>
      rw [indexedEdgeGraph_insert] at hxy
      rcases hxy with hxy | hxy
      · exact ih (fun a ha => h a (Finset.mem_insert_of_mem ha)) hxy
      · rcases (SimpleGraph.edge_adj _ _ _ _).mp hxy with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
        · exact h e (Finset.mem_insert_self _ _)
        · exact (partitionSetoid P).symm (h e (Finset.mem_insert_self _ _))

theorem sum_edgeGraph_coarsening_mobius (u v : E → V) (F : Finset E) :
    (∑ P : {P : VertexPartition V // ∀ e ∈ F, partitionSetoid P (u e) (v e)},
      cumulantMobius P.val.parts.card) =
      if (indexedEdgeGraph u v F).Connected then 1 else 0 := by
  let e : {P : VertexPartition V // ∀ e ∈ F, partitionSetoid P (u e) (v e)} ≃
      {P : VertexPartition V // graphPartition (indexedEdgeGraph u v F) ≤ P} :=
    Equiv.subtypeEquivRight (fun P => (edgeGraphPartition_le_iff u v F P).symm)
  rw [← Equiv.sum_comp e.symm]
  change (∑ P : {P : VertexPartition V // graphPartition (indexedEdgeGraph u v F) ≤ P},
    cumulantMobius P.val.parts.card) = _
  rw [sum_coarsening_mobius]
  simp only [graphPartition_card_one]

omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype E] in
theorem sum_subsets_sign (s : Finset E) :
    (∑ F ∈ s.powerset, (-1 : ℝ) ^ F.card) = if s = ∅ then 1 else 0 := by
  have h := Finset.sum_pow_mul_eq_add_pow (-1 : ℝ) 1 s
  simp only [one_pow, mul_one, neg_add_cancel] at h
  rw [h]
  by_cases hs : s = ∅
  · simp [hs]
  · simp [hs, Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hs)]

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem sum_subsets_satisfying_sign (p : E → Prop) :
    (∑ F : Finset E, if ∀ e ∈ F, p e then (-1 : ℝ) ^ F.card else 0) =
      if ∀ e, ¬p e then 1 else 0 := by
  let s := Finset.univ.filter p
  have hF : Finset.univ.filter (fun F : Finset E => ∀ e ∈ F, p e) = s.powerset := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset,
      Finset.subset_iff, s]
  have hs : s = ∅ ↔ ∀ e, ¬p e := by
    simp only [s, Finset.filter_eq_empty_iff, Finset.mem_univ, forall_true_left]
  rw [← Finset.sum_filter, hF, sum_subsets_sign]
  simp only [hs]

theorem independentPartition_coefficient (u v : E → V) :
    (∑ P ∈ Finset.univ.filter (fun P : VertexPartition V =>
        ∀ e, ¬partitionSetoid P (u e) (v e)), cumulantMobius P.parts.card) =
      ∑ F ∈ Finset.univ.filter (fun F : Finset E => (indexedEdgeGraph u v F).Connected),
        (-1 : ℝ) ^ F.card := by
  rw [Finset.sum_filter]
  calc
    _ = ∑ P : VertexPartition V, cumulantMobius P.parts.card *
        ∑ F : Finset E, if ∀ e ∈ F, partitionSetoid P (u e) (v e)
          then (-1 : ℝ) ^ F.card else 0 := by
      apply Finset.sum_congr rfl
      intro P _
      rw [sum_subsets_satisfying_sign]
      split_ifs <;> simp
    _ = ∑ F : Finset E, (-1 : ℝ) ^ F.card *
        ∑ P : VertexPartition V, if ∀ e ∈ F, partitionSetoid P (u e) (v e)
          then cumulantMobius P.parts.card else 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro F _
      apply Finset.sum_congr rfl
      intro P _
      split_ifs <;> ring
    _ = ∑ F : Finset E, (-1 : ℝ) ^ F.card *
        (if (indexedEdgeGraph u v F).Connected then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro F _
      congr 1
      rw [← Finset.sum_filter, Finset.sum_subtype
        (p := fun P : VertexPartition V => ∀ e ∈ F, partitionSetoid P (u e) (v e)) _
        (by simp), sum_edgeGraph_coarsening_mobius u v F]
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro F _
      split_ifs <;> simp

theorem abs_independentPartition_coefficient_le_trees (u v : E → V) :
    |∑ P ∈ Finset.univ.filter (fun P : VertexPartition V =>
        ∀ e, ¬partitionSetoid P (u e) (v e)), cumulantMobius P.parts.card| ≤
      ((Finset.univ.filter (fun F : Finset E => (indexedEdgeGraph u v F).IsTree)).card : ℝ) := by
  rw [independentPartition_coefficient]
  exact abs_connected_graph_sum_le_trees u v

end

end TensorLB
