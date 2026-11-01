module

public import TensorLB.PartitionMobius

/-!
# Refining partition blocks into connected components

The cumulant grouping uses the connected components inside each block, rather
than the original blocks. The refinement is idempotent, and its fibers are
characterized by the absence of new edges between its components.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def withinPartitionGraph (G : SimpleGraph V) (P : VertexPartition V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ partitionSetoid P x y
  symm := ⟨fun _ _ h => ⟨h.1.symm, (partitionSetoid P).symm h.2⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

def connectedRefinement (G : SimpleGraph V) (P : VertexPartition V) : VertexPartition V :=
  graphPartition (withinPartitionGraph G P)

theorem connectedRefinement_le (G : SimpleGraph V) (P : VertexPartition V) :
    connectedRefinement G P ≤ P := by
  apply (graphPartition_le_iff _ _).mpr
  exact fun _ _ h => h.2

theorem connectedRefinement_rel (G : SimpleGraph V) (P : VertexPartition V) (x y : V) :
    partitionSetoid (connectedRefinement G P) x y ↔ (withinPartitionGraph G P).Reachable x y := by
  change partitionSetoid (Finpartition.ofSetoid (withinPartitionGraph G P).reachableSetoid) x y ↔ _
  rw [partitionSetoid_ofSetoid]
  rfl

theorem withinPartitionGraph_connectedRefinement (G : SimpleGraph V) (P : VertexPartition V) :
    withinPartitionGraph G (connectedRefinement G P) = withinPartitionGraph G P := by
  ext x y
  constructor
  · intro h
    exact ⟨h.1, ((partitionSetoid_le_iff _ _).mpr (connectedRefinement_le G P)) h.2⟩
  · intro h
    exact ⟨h.1, (connectedRefinement_rel G P x y).mpr h.reachable⟩

theorem connectedRefinement_idem (G : SimpleGraph V) (P : VertexPartition V) :
    connectedRefinement G (connectedRefinement G P) = connectedRefinement G P := by
  change graphPartition (withinPartitionGraph G (connectedRefinement G P)) = _
  rw [withinPartitionGraph_connectedRefinement]
  rfl

theorem withinPartitionGraph_mono (G : SimpleGraph V) {P Q : VertexPartition V} (h : P ≤ Q) :
    withinPartitionGraph G P ≤ withinPartitionGraph G Q :=
  fun _ _ hxy => ⟨hxy.1, ((partitionSetoid_le_iff P Q).mpr h) hxy.2⟩

theorem connectedRefinement_mono (G : SimpleGraph V) {P Q : VertexPartition V} (h : P ≤ Q) :
    connectedRefinement G P ≤ connectedRefinement G Q := by
  apply (partitionSetoid_le_iff _ _).mp
  intro x y hxy
  rw [connectedRefinement_rel] at hxy ⊢
  exact hxy.mono (withinPartitionGraph_mono G h)

theorem connectedRefinement_fiber_iff (G : SimpleGraph V) (P R : VertexPartition V) :
    connectedRefinement G P = R ↔ connectedRefinement G R = R ∧ R ≤ P ∧
      ∀ x y, G.Adj x y → partitionSetoid P x y → partitionSetoid R x y := by
  constructor
  · rintro rfl
    refine ⟨connectedRefinement_idem G P, connectedRefinement_le G P, ?_⟩
    intro x y hxy hP
    exact (connectedRefinement_rel G P x y).mpr (SimpleGraph.Adj.reachable ⟨hxy, hP⟩)
  · rintro ⟨hR, hle, h⟩
    have hg : withinPartitionGraph G P = withinPartitionGraph G R := by
      apply le_antisymm
      · exact fun x y hxy => ⟨hxy.1, h x y hxy.1 hxy.2⟩
      · exact withinPartitionGraph_mono G hle
    change graphPartition (withinPartitionGraph G P) = R
    rw [hg]
    exact hR

/-- Distinct refined blocks inside one original block have no dependency edge. -/
theorem connectedRefinement_no_cross_edge (G : SimpleGraph V) (P : VertexPartition V)
    (x y : V) (hP : partitionSetoid P x y)
    (hR : ¬partitionSetoid (connectedRefinement G P) x y) : ¬G.Adj x y := by
  intro hxy
  exact hR ((connectedRefinement_rel G P x y).mpr (SimpleGraph.Adj.reachable ⟨hxy, hP⟩))

def partitionMoment (m : Finset V → ℝ) (P : VertexPartition V) : ℝ :=
  ∏ B ∈ P.parts, m B


def blocksBelow (R : VertexPartition V) (B : Finset V) : Finset (Finset V) :=
  R.parts.filter (· ⊆ B)

theorem biUnion_blocksBelow {R P : VertexPartition V} (hRP : R ≤ P)
    {B : Finset V} (hB : B ∈ P.parts) : (blocksBelow R B).biUnion id = B := by
  ext x
  constructor
  · intro hx
    obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hC).2 hxC
  · intro hx
    refine Finset.mem_biUnion.mpr ⟨R.part x, ?_, R.mem_part (Finset.mem_univ x)⟩
    apply Finset.mem_filter.mpr
    refine ⟨R.part_mem.mpr (Finset.mem_univ x), ?_⟩
    obtain ⟨D, hD, hRD⟩ := hRP (R.part_mem.mpr (Finset.mem_univ x))
    have hDB : D = B := P.eq_of_mem_parts hD hB
      (hRD (R.mem_part (Finset.mem_univ x))) hx
    exact hDB ▸ hRD

theorem blocksBelow_pairwiseDisjoint (R P : VertexPartition V) :
    Set.PairwiseDisjoint (P.parts : Set (Finset V)) (blocksBelow R) := by
  intro B hB C hC hBC
  apply Finset.disjoint_left.mpr
  intro D hDB hDC
  obtain ⟨hD, hDB⟩ := Finset.mem_filter.mp hDB
  obtain ⟨_, hDC⟩ := Finset.mem_filter.mp hDC
  obtain ⟨x, hx⟩ := R.nonempty_of_mem_parts hD
  exact hBC (P.eq_of_mem_parts hB hC (hDB hx) (hDC hx))

theorem biUnion_all_blocksBelow {R P : VertexPartition V} (hRP : R ≤ P) :
    P.parts.biUnion (blocksBelow R) = R.parts := by
  ext C
  constructor
  · intro hC
    obtain ⟨B, _, hCB⟩ := Finset.mem_biUnion.mp hC
    exact (Finset.mem_filter.mp hCB).1
  · intro hC
    obtain ⟨B, hB, hCB⟩ := hRP hC
    exact Finset.mem_biUnion.mpr ⟨B, hB, Finset.mem_filter.mpr ⟨hC, hCB⟩⟩

theorem partitionMoment_eq_of_refinement (m : Finset V → ℝ) {R P : VertexPartition V}
    (hRP : R ≤ P) (hm : ∀ B ∈ P.parts, m B = ∏ C ∈ blocksBelow R B, m C) :
    partitionMoment m P = partitionMoment m R := by
  unfold partitionMoment
  calc
    _ = ∏ B ∈ P.parts, ∏ C ∈ blocksBelow R B, m C := Finset.prod_congr rfl hm
    _ = ∏ C ∈ P.parts.biUnion (blocksBelow R), m C :=
      (Finset.prod_biUnion (blocksBelow_pairwiseDisjoint R P)).symm
    _ = _ := by rw [biUnion_all_blocksBelow hRP]

/-- Regrouping the cumulant by connected refinement. The only analytic input
is factorization of the moment product over that refinement. -/
theorem partitionCumulant_group_by_refinement (G : SimpleGraph V) (m : Finset V → ℝ)
    (hm : ∀ P, partitionMoment m P = partitionMoment m (connectedRefinement G P)) :
    partitionCumulant Finset.univ m =
      ∑ R : VertexPartition V, partitionMoment m R *
        ∑ P : {P : VertexPartition V // connectedRefinement G P = R}, cumulantMobius P.val.parts.card := by
  rw [partitionCumulant, ← Fintype.sum_fiberwise (connectedRefinement G)]
  apply Finset.sum_congr rfl
  intro R _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P _
  change cumulantMobius P.val.parts.card * partitionMoment m P.val = _
  rw [hm P.val, P.property, mul_comm]

end

end TensorLB
