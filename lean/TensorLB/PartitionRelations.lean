module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Fintype.Quotient
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite partitions as equivalence relations

The correspondence allows connected refinements and coarsenings to use the
quotient API for equivalence relations. The quotient cardinality is exactly
the number of partition blocks, preserving the cumulant Möbius weight.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev VertexPartition (V : Type*) [Fintype V] [DecidableEq V] := Finpartition (Finset.univ : Finset V)

def partitionSetoid (P : VertexPartition V) : Setoid V := Setoid.ker P.part

theorem vertexPartition_ext_part {P Q : VertexPartition V}
    (h : ∀ x, P.part x = Q.part x) : P = Q := by
  apply Finpartition.ext
  ext B
  constructor
  · intro hB
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hB
    have he := P.part_eq_of_mem hB hx
    rw [← he, h]
    exact Q.part_mem.mpr (Finset.mem_univ x)
  · intro hB
    obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts hB
    have he := Q.part_eq_of_mem hB hx
    rw [← he, ← h]
    exact P.part_mem.mpr (Finset.mem_univ x)

theorem ofSetoid_partitionSetoid (P : VertexPartition V) :
    Finpartition.ofSetoid (partitionSetoid P) = P := by
  apply vertexPartition_ext_part
  intro x
  ext y
  rw [Finpartition.mem_part_ofSetoid_iff_rel,
    P.mem_part_iff_part_eq_part (Finset.mem_univ y) (Finset.mem_univ x)]
  change P.part x = P.part y ↔ P.part y = P.part x
  exact eq_comm

theorem partitionSetoid_ofSetoid (s : Setoid V) :
    partitionSetoid (Finpartition.ofSetoid s) = s := by
  apply Setoid.ext
  intro x y
  change (Finpartition.ofSetoid s).part x = (Finpartition.ofSetoid s).part y ↔ s x y
  rw [← (Finpartition.ofSetoid s).mem_part_iff_part_eq_part
    (Finset.mem_univ x) (Finset.mem_univ y), Finpartition.mem_part_ofSetoid_iff_rel]
  exact ⟨s.symm, s.symm⟩

def partitionSetoidEquiv : VertexPartition V ≃ Setoid V where
  toFun := partitionSetoid
  invFun := fun s => Finpartition.ofSetoid s
  left_inv := ofSetoid_partitionSetoid
  right_inv := partitionSetoid_ofSetoid

theorem partitionSetoid_le_iff (P Q : VertexPartition V) :
    partitionSetoid P ≤ partitionSetoid Q ↔ P ≤ Q := by
  constructor
  · intro h B hB
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hB
    refine ⟨Q.part x, Q.part_mem.mpr (Finset.mem_univ x), ?_⟩
    intro y hy
    have hP : P.part y = P.part x :=
      (P.part_eq_of_mem hB hy).trans (P.part_eq_of_mem hB hx).symm
    have hQ : Q.part y = Q.part x := h hP
    rw [← hQ]
    exact Q.mem_part (Finset.mem_univ y)
  · intro h x y hxy
    obtain ⟨B, hB, hPB⟩ := h (P.part_mem.mpr (Finset.mem_univ x))
    have hx : x ∈ B := hPB (P.mem_part (Finset.mem_univ x))
    have hy : y ∈ B := by
      apply hPB
      change P.part x = P.part y at hxy
      rw [hxy]
      exact P.mem_part (Finset.mem_univ y)
    exact (Q.part_eq_of_mem hB hx).trans (Q.part_eq_of_mem hB hy).symm

def partitionSetoidOrderIso : VertexPartition V ≃o Setoid V where
  toEquiv := partitionSetoidEquiv
  map_rel_iff' := partitionSetoid_le_iff _ _

def partitionPartMap (P : VertexPartition V) (x : V) : P.parts :=
  ⟨P.part x, P.part_mem.mpr (Finset.mem_univ x)⟩

theorem partitionPartMap_surjective (P : VertexPartition V) : Function.Surjective (partitionPartMap P) := by
  rintro ⟨B, hB⟩
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hB
  exact ⟨x, Subtype.ext (P.part_eq_of_mem hB hx)⟩

def partitionQuotientEquivParts (P : VertexPartition V) : Quotient (partitionSetoid P) ≃ P.parts :=
  (Quotient.congrRight (r := partitionSetoid P) (r' := Setoid.ker (partitionPartMap P))
    (fun x y => by
      change (partitionPartMap P x).val = (partitionPartMap P y).val ↔
        partitionPartMap P x = partitionPartMap P y
      exact Subtype.val_inj)).trans
      (Setoid.quotientKerEquivOfSurjective (partitionPartMap P) (partitionPartMap_surjective P))

theorem card_partition_quotient (P : VertexPartition V) :
    Fintype.card (Quotient (partitionSetoid P)) = P.parts.card := by
  simpa using Fintype.card_congr (partitionQuotientEquivParts P)

def correspondenceQuotientEquiv (r s : Setoid V) (h : r ≤ s) :
    Quotient (Setoid.correspondence r ⟨s, h⟩) ≃ Quotient s :=
  (Quotient.congrRight (r := Setoid.correspondence r ⟨s, h⟩)
    (r' := Setoid.ker (Quot.mapRight h)) (fun x y => by
      induction x using Quotient.inductionOn with | _ a =>
        induction y using Quotient.inductionOn with | _ b =>
          change s a b ↔ Quotient.mk s a = Quotient.mk s b
          exact Quotient.eq.symm)).trans
    (Setoid.quotientQuotientEquivQuotient r s h)

/-- Coarsenings of a partition are partitions of its blocks. The quotient
version avoids selecting representatives for the original vertices. -/
def coarseningPartitionEquiv (P : VertexPartition V) :
    {Q : VertexPartition V // P ≤ Q} ≃ VertexPartition (Quotient (partitionSetoid P)) :=
  (partitionSetoidEquiv.subtypeEquiv (fun Q => (partitionSetoid_le_iff P Q).symm)).trans
    ((Setoid.correspondence (partitionSetoid P)).toEquiv.trans partitionSetoidEquiv.symm)

theorem coarseningPartitionEquiv_card (P : VertexPartition V)
    (Q : {Q : VertexPartition V // P ≤ Q}) :
    (coarseningPartitionEquiv P Q).parts.card = Q.val.parts.card := by
  let S := Setoid.correspondence (partitionSetoid P)
    ⟨partitionSetoid Q.val, (partitionSetoid_le_iff P Q.val).mpr Q.property⟩
  have he : coarseningPartitionEquiv P Q = Finpartition.ofSetoid S := rfl
  calc
    _ = Fintype.card (Quotient S) := by
      have h := (card_partition_quotient (coarseningPartitionEquiv P Q)).symm
      simpa only [he, partitionSetoid_ofSetoid] using h
    _ = Fintype.card (Quotient (partitionSetoid Q.val)) :=
      Fintype.card_congr (correspondenceQuotientEquiv (partitionSetoid P) (partitionSetoid Q.val)
        ((partitionSetoid_le_iff P Q.val).mpr Q.property))
    _ = _ := card_partition_quotient Q.val

theorem sum_coarsening_by_card (P : VertexPartition V) {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) :
    (∑ Q : {Q : VertexPartition V // P ≤ Q}, f Q.val.parts.card) =
      ∑ Q : VertexPartition (Quotient (partitionSetoid P)), f Q.parts.card := by
  rw [← Equiv.sum_comp (coarseningPartitionEquiv P)]
  exact Finset.sum_congr rfl (fun Q _ => congrArg f (coarseningPartitionEquiv_card P Q).symm)

variable {W : Type*} [Fintype W] [DecidableEq W]

def relabelSetoid (e : V ≃ W) : Setoid V ≃ Setoid W where
  toFun r := r.comap e.symm
  invFun r := r.comap e
  left_inv r := by
    apply Setoid.ext
    intro x y
    simp only [Setoid.comap_rel, Equiv.symm_apply_apply]
  right_inv r := by
    apply Setoid.ext
    intro x y
    simp only [Setoid.comap_rel, Equiv.apply_symm_apply]

def relabelPartition (e : V ≃ W) : VertexPartition V ≃ VertexPartition W :=
  partitionSetoidEquiv.trans ((relabelSetoid e).trans partitionSetoidEquiv.symm)

theorem relabelPartition_card (e : V ≃ W) (P : VertexPartition V) :
    (relabelPartition e P).parts.card = P.parts.card := by
  rw [← card_partition_quotient, ← card_partition_quotient]
  apply Fintype.card_congr
  symm
  apply Quotient.congr e
  intro x y
  change partitionSetoid P x y ↔ partitionSetoid
    (Finpartition.ofSetoid ((partitionSetoid P).comap e.symm)) (e x) (e y)
  rw [partitionSetoid_ofSetoid ((partitionSetoid P).comap e.symm)]
  simp only [Setoid.comap_rel, Equiv.symm_apply_apply]

theorem sum_partition_by_card_relabel {R : Type*} [AddCommMonoid R]
    (e : V ≃ W) (f : ℕ → R) :
    (∑ P : VertexPartition V, f P.parts.card) =
      ∑ P : VertexPartition W, f P.parts.card := by
  rw [← Equiv.sum_comp (relabelPartition e)]
  exact Finset.sum_congr rfl (fun P _ => congrArg f (relabelPartition_card e P).symm)

end

end TensorLB
