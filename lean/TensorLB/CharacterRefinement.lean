module

public import TensorLB.ConnectedPartition

/-!
# Factorization over the support dependency graph

Character moments factor across connected components of their support graph.
Consequently the full partition cumulant can be regrouped by connected
refinement, with one bounded moment product for each connected partition.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [DecidableEq V] {n : ℕ}

def characterDependencyGraph (X : V → Finset (Fin n)) : SimpleGraph V where
  Adj a b := a ≠ b ∧ ¬Disjoint (X a) (X b)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hd => h.2 hd.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem characterMoment_biUnion (X : V → Finset (Fin n)) (S : Finset (Finset V))
    (hd : Set.PairwiseDisjoint (S : Set (Finset V)) id)
    (hs : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, Disjoint (X a) (X b)) :
    characterMoment X (S.biUnion id) = ∏ B ∈ S, characterMoment X B := by
  induction S using Finset.induction_on with
  | empty => simp [characterMoment_empty]
  | @insert A S hA ih =>
    rw [Finset.biUnion_insert, Finset.prod_insert hA]
    dsimp only [id]
    have hdAS : Disjoint A (S.biUnion id) := by
      apply (Finset.disjoint_biUnion_right A S id).mpr
      intro B hB
      exact hd (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hB)
        (fun h => hA (h ▸ hB))
    rw [characterMoment_union_of_disjoint_support X A (S.biUnion id) hdAS]
    · congr 1
      apply ih
      · intro B hB C hC hBC
        exact hd (Finset.mem_insert_of_mem hB) (Finset.mem_insert_of_mem hC) hBC
      · intro B hB C hC hBC
        exact hs B (Finset.mem_insert_of_mem hB) C (Finset.mem_insert_of_mem hC) hBC
    · intro a ha b hb
      obtain ⟨B, hB, hb⟩ := Finset.mem_biUnion.mp hb
      exact hs A (Finset.mem_insert_self _ _) B (Finset.mem_insert_of_mem hB)
        (fun h => hA (h ▸ hB)) a ha b hb

variable [Fintype V]

theorem characterMoment_connected_blocks (X : V → Finset (Fin n)) (P : VertexPartition V)
    {B : Finset V} (hB : B ∈ P.parts) :
    characterMoment X B =
      ∏ C ∈ blocksBelow (connectedRefinement (characterDependencyGraph X) P) B,
        characterMoment X C := by
  let R := connectedRefinement (characterDependencyGraph X) P
  have hRP : R ≤ P := connectedRefinement_le _ _
  conv_lhs => rw [← biUnion_blocksBelow hRP hB]
  apply characterMoment_biUnion
  · intro C hC D hD hCD
    exact R.disjoint (Finset.mem_filter.mp hC).1 (Finset.mem_filter.mp hD).1 hCD
  · intro C hC D hD hCD a ha b hb
    obtain ⟨hC, hCB⟩ := Finset.mem_filter.mp hC
    obtain ⟨hD, hDB⟩ := Finset.mem_filter.mp hD
    have hP : partitionSetoid P a b :=
      (P.part_eq_of_mem hB (hCB ha)).trans (P.part_eq_of_mem hB (hDB hb)).symm
    have hR : ¬partitionSetoid R a b := by
      intro hab
      apply hCD
      change R.part a = R.part b at hab
      rw [R.part_eq_of_mem hC ha, R.part_eq_of_mem hD hb] at hab
      exact hab
    have hab : a ≠ b := by
      intro hab
      subst b
      exact hCD (R.eq_of_mem_parts hC hD ha hb)
    by_contra hd
    exact connectedRefinement_no_cross_edge (characterDependencyGraph X) P a b hP hR ⟨hab, hd⟩

theorem character_partitionMoment_refinement (X : V → Finset (Fin n)) (P : VertexPartition V) :
    partitionMoment (characterMoment X) P =
      partitionMoment (characterMoment X) (connectedRefinement (characterDependencyGraph X) P) := by
  apply partitionMoment_eq_of_refinement _ (connectedRefinement_le _ _)
  exact fun _ hB => characterMoment_connected_blocks X P hB

theorem jointCharacterCumulant_group_by_refinement (X : V → Finset (Fin n)) :
    jointCharacterCumulant X =
      ∑ R : VertexPartition V, partitionMoment (characterMoment X) R *
        ∑ P : {P : VertexPartition V // connectedRefinement (characterDependencyGraph X) P = R},
          cumulantMobius P.val.parts.card :=
  partitionCumulant_group_by_refinement _ _ (character_partitionMoment_refinement X)

end

end TensorLB
