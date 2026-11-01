module

public import TensorLB.WeightedCumulant

/-!
# Relabeling character occurrences

Cumulants depend on the indexed family up to equivalence of occurrence labels.
This permits choosing any marked spin as the external root of the dependency tree.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem relabelPartition_part (e : V ≃ W) (P : VertexPartition V) (x : V) :
    (relabelPartition e P).part (e x) = (P.part x).image e := by
  apply Finset.ext
  intro y
  obtain ⟨z, rfl⟩ := e.surjective y
  change e z ∈ (Finpartition.ofSetoid ((partitionSetoid P).comap e.symm)).part (e x) ↔ _
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  simp only [Setoid.comap_rel, Equiv.symm_apply_apply]
  rw [Finset.mem_image]
  constructor
  · intro h
    refine ⟨z, ?_, rfl⟩
    rw [P.mem_part_iff_part_eq_part (Finset.mem_univ z) (Finset.mem_univ x)]
    exact h.symm
  · rintro ⟨a, ha, haz⟩
    have he : a = z := e.injective haz
    subst a
    exact ((P.mem_part_iff_part_eq_part (Finset.mem_univ z) (Finset.mem_univ x)).mp ha).symm

theorem relabelPartition_parts (e : V ≃ W) (P : VertexPartition V) :
    (relabelPartition e P).parts = P.parts.image (fun B => B.image e) := by
  ext B
  constructor
  · intro hB
    obtain ⟨y, hy⟩ := (relabelPartition e P).nonempty_of_mem_parts hB
    obtain ⟨x, rfl⟩ := e.surjective y
    refine Finset.mem_image.mpr ⟨P.part x, P.part_mem.mpr (Finset.mem_univ x), ?_⟩
    rw [← relabelPartition_part]
    exact (relabelPartition e P).part_eq_of_mem hB hy
  · intro hB
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hC
    rw [← P.part_eq_of_mem hC hx, ← relabelPartition_part]
    exact (relabelPartition e P).part_mem.mpr (Finset.mem_univ _)

omit [Fintype V] [DecidableEq V] [Fintype W] in
theorem characterMoment_image {n : ℕ} (e : V ≃ W) (X : W → Finset (Fin n)) (B : Finset V) :
    characterMoment X (B.image e) = characterMoment (X ∘ e) B := by
  unfold characterMoment
  congr 1
  funext z
  exact Finset.prod_image (fun a _ b _ h => e.injective h)

theorem character_partitionMoment_relabel {n : ℕ} (e : V ≃ W) (X : W → Finset (Fin n))
    (P : VertexPartition V) :
    partitionMoment (characterMoment X) (relabelPartition e P) =
      partitionMoment (characterMoment (X ∘ e)) P := by
  unfold partitionMoment
  rw [relabelPartition_parts, Finset.prod_image]
  · exact Finset.prod_congr rfl (fun B _ => characterMoment_image e X B)
  · intro A _ B _ h
    exact (Finset.image_injective e.injective) h

theorem jointCharacterCumulant_equiv {n : ℕ} (e : V ≃ W) (X : W → Finset (Fin n)) :
    jointCharacterCumulant X = jointCharacterCumulant (X ∘ e) := by
  unfold jointCharacterCumulant partitionCumulant
  rw [← Equiv.sum_comp (relabelPartition e)]
  apply Finset.sum_congr rfl
  intro P _
  rw [relabelPartition_card]
  congr 1
  exact character_partitionMoment_relabel e X P

end

end TensorLB
