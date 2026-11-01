module

public import TensorLB.PartitionRelations
public import TensorLB.OrderedCumulant
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Hom.Set

/-!
# The underlying blocks of Faà di Bruno partitions

Ordered partitions use the increasing order of block maxima. This module
relates their embeddings to ordinary finite partitions, so the analytic
composition formula and the graph-cumulant argument use the same blocks.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n : ℕ}

def orderedBlock (c : OrderedFinpartition n) (j : Fin c.length) : Finset (Fin n) :=
  Finset.univ.image (c.emb j)

theorem ordered_index_emb (c : OrderedFinpartition n) (j : Fin c.length) (a : Fin (c.partSize j)) :
    c.index (c.emb j a) = j := by
  have h := c.emb_injective (a₁ := ⟨c.index (c.emb j a), c.invEmbedding (c.emb j a)⟩)
    (a₂ := ⟨j, a⟩) (c.emb_invEmbedding (c.emb j a))
  exact congrArg Sigma.fst h

theorem mem_orderedBlock (c : OrderedFinpartition n) (j : Fin c.length) (a : Fin n) :
    a ∈ orderedBlock c j ↔ c.index a = j := by
  constructor
  · intro ha
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
    exact ordered_index_emb c j b
  · intro h
    rw [← h]
    exact Finset.mem_image.mpr ⟨c.invEmbedding a, Finset.mem_univ _, c.emb_invEmbedding a⟩

theorem orderedBlock_nonempty (c : OrderedFinpartition n) (j : Fin c.length) :
    (orderedBlock c j).Nonempty :=
  ⟨c.emb j ⟨0, c.partSize_pos j⟩,
    Finset.mem_image.mpr ⟨⟨0, c.partSize_pos j⟩, Finset.mem_univ _, rfl⟩⟩

theorem orderedBlock_card (c : OrderedFinpartition n) (j : Fin c.length) :
    (orderedBlock c j).card = c.partSize j := by
  rw [orderedBlock, Finset.card_image_of_injective _ (c.emb_strictMono j).injective]
  exact Fintype.card_fin _

theorem orderedBlock_injective (c : OrderedFinpartition n) : Function.Injective (orderedBlock c) := by
  intro i j hij
  obtain ⟨a, ha⟩ := orderedBlock_nonempty c i
  have hb : a ∈ orderedBlock c j := hij ▸ ha
  exact ((mem_orderedBlock c i a).mp ha).symm.trans ((mem_orderedBlock c j a).mp hb)

def orderedPartition (c : OrderedFinpartition n) : VertexPartition (Fin n) :=
  Finpartition.ofSetoid (Setoid.ker c.index)

theorem orderedPartition_part (c : OrderedFinpartition n) (a : Fin n) :
    (orderedPartition c).part a = orderedBlock c (c.index a) := by
  ext b
  rw [orderedPartition, Finpartition.mem_part_ofSetoid_iff_rel, mem_orderedBlock]
  exact eq_comm

theorem orderedPartition_parts (c : OrderedFinpartition n) :
    (orderedPartition c).parts = Finset.univ.image (orderedBlock c) := by
  ext B
  constructor
  · intro hB
    obtain ⟨a, ha⟩ := (orderedPartition c).nonempty_of_mem_parts hB
    refine Finset.mem_image.mpr ⟨c.index a, Finset.mem_univ _, ?_⟩
    exact (orderedPartition_part c a).symm.trans ((orderedPartition c).part_eq_of_mem hB ha)
  · intro hB
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
    let a := c.emb j ⟨0, c.partSize_pos j⟩
    have h : (orderedPartition c).part a = orderedBlock c j := by
      rw [orderedPartition_part, ordered_index_emb]
    rw [← h]
    exact (orderedPartition c).part_mem.mpr (Finset.mem_univ a)

theorem orderedPartition_card (c : OrderedFinpartition n) :
    (orderedPartition c).parts.card = c.length := by
  rw [orderedPartition_parts, Finset.card_image_of_injective _ (orderedBlock_injective c)]
  exact Fintype.card_fin _

def partitionBlockMax (P : VertexPartition (Fin n)) (B : P.parts) : Fin n :=
  B.val.max' (P.nonempty_of_mem_parts B.property)

theorem partitionBlockMax_injective (P : VertexPartition (Fin n)) :
    Function.Injective (partitionBlockMax P) := by
  intro B C h
  apply Subtype.ext
  apply P.eq_of_mem_parts (a := partitionBlockMax P B) B.property C.property
  · exact B.val.max'_mem (P.nonempty_of_mem_parts B.property)
  · rw [h]
    exact C.val.max'_mem (P.nonempty_of_mem_parts C.property)

def partitionBlockEnumeration (P : VertexPartition (Fin n)) : Fin P.parts.card ≃ P.parts :=
  let : LinearOrder P.parts := LinearOrder.lift' (partitionBlockMax P) (partitionBlockMax_injective P)
  (Fintype.orderIsoFinOfCardEq P.parts (Fintype.card_coe _)).toEquiv

theorem partitionBlockEnumeration_strictMono (P : VertexPartition (Fin n)) :
    StrictMono (fun j => partitionBlockMax P (partitionBlockEnumeration P j)) := by
  let o : LinearOrder P.parts := LinearOrder.lift' (partitionBlockMax P) (partitionBlockMax_injective P)
  let e := @Fintype.orderIsoFinOfCardEq P.parts o _ P.parts.card (Fintype.card_coe _)
  intro i j hij
  have hle : partitionBlockMax P (partitionBlockEnumeration P i) ≤
      partitionBlockMax P (partitionBlockEnumeration P j) := e.map_rel_iff'.mpr hij.le
  apply lt_of_le_of_ne hle
  exact (partitionBlockMax_injective P).ne ((partitionBlockEnumeration P).injective.ne hij.ne)

theorem partitionBlockEnumeration_last (P : VertexPartition (Fin n)) (j : Fin P.parts.card) :
    (partitionBlockEnumeration P j).val.orderEmbOfFin rfl
      ⟨(partitionBlockEnumeration P j).val.card - 1,
        Nat.sub_one_lt_of_lt (Finset.card_pos.mpr
          (P.nonempty_of_mem_parts (partitionBlockEnumeration P j).property))⟩ =
      partitionBlockMax P (partitionBlockEnumeration P j) := by
  exact Finset.orderEmbOfFin_last rfl (Finset.card_pos.mpr
    (P.nonempty_of_mem_parts (partitionBlockEnumeration P j).property))

def orderedOfPartition (P : VertexPartition (Fin n)) : OrderedFinpartition n where
  length := P.parts.card
  partSize j := (partitionBlockEnumeration P j).val.card
  partSize_pos j := Finset.card_pos.mpr (P.nonempty_of_mem_parts (partitionBlockEnumeration P j).property)
  emb j := (partitionBlockEnumeration P j).val.orderEmbOfFin rfl
  emb_strictMono j := Finset.orderEmbOfFin _ rfl |>.strictMono
  parts_strictMono := by
    intro i j hij
    dsimp only
    rw [partitionBlockEnumeration_last, partitionBlockEnumeration_last]
    exact partitionBlockEnumeration_strictMono P hij
  disjoint := by
    intro i _ j _ hij
    dsimp only [Function.onFun]
    rw [Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin]
    apply Finset.disjoint_coe.mpr
    apply P.disjoint (partitionBlockEnumeration P i).property (partitionBlockEnumeration P j).property
    intro he
    exact hij ((partitionBlockEnumeration P).injective (Subtype.ext he))
  cover a := by
    let B : P.parts := ⟨P.part a, P.part_mem.mpr (Finset.mem_univ a)⟩
    refine ⟨(partitionBlockEnumeration P).symm B, ?_⟩
    rw [Finset.range_orderEmbOfFin, Equiv.apply_symm_apply]
    exact P.mem_part (Finset.mem_univ a)

theorem orderedBlock_orderedOfPartition (P : VertexPartition (Fin n)) (j : Fin P.parts.card) :
    orderedBlock (orderedOfPartition P) j = (partitionBlockEnumeration P j).val := by
  exact Finset.image_orderEmbOfFin_univ _ rfl

theorem orderedPartition_orderedOfPartition (P : VertexPartition (Fin n)) :
    orderedPartition (orderedOfPartition P) = P := by
  apply Finpartition.ext
  rw [orderedPartition_parts]
  ext B
  constructor
  · intro hB
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
    rw [orderedBlock_orderedOfPartition P j]
    exact (partitionBlockEnumeration P j).property
  · intro hB
    let j := (partitionBlockEnumeration P).symm ⟨B, hB⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    rw [orderedBlock_orderedOfPartition]
    exact congrArg Subtype.val ((partitionBlockEnumeration P).apply_symm_apply ⟨B, hB⟩)

def orderedBlockMax (c : OrderedFinpartition n) (j : Fin c.length) : Fin n :=
  (orderedBlock c j).max' (orderedBlock_nonempty c j)

theorem orderedBlockMax_eq (c : OrderedFinpartition n) (j : Fin c.length) :
    orderedBlockMax c j =
      c.emb j ⟨c.partSize j - 1, Nat.sub_one_lt_of_lt (c.partSize_pos j)⟩ := by
  apply (Finset.max'_eq_iff _ _ _).mpr
  constructor
  · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · intro b hb
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
    apply (c.emb_strictMono j).monotone
    apply Fin.le_iff_val_le_val.mpr
    change a.val ≤ c.partSize j - 1
    have := a.isLt
    omega

theorem orderedBlockMax_strictMono (c : OrderedFinpartition n) :
    StrictMono (orderedBlockMax c) := by
  intro i j hij
  rw [orderedBlockMax_eq, orderedBlockMax_eq]
  exact c.parts_strictMono hij

theorem orderedBlock_mem_parts (c : OrderedFinpartition n) (j : Fin c.length) :
    orderedBlock c j ∈ (orderedPartition c).parts := by
  rw [orderedPartition_parts]
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

theorem orderedBlockMax_range (c : OrderedFinpartition n) :
    Set.range (orderedBlockMax c) = Set.range (partitionBlockMax (orderedPartition c)) := by
  ext a
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨⟨orderedBlock c j, orderedBlock_mem_parts c j⟩, rfl⟩
  · rintro ⟨B, rfl⟩
    have hB := B.property
    simp only [orderedPartition_parts] at hB
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hB
    refine ⟨j, ?_⟩
    unfold orderedBlockMax partitionBlockMax
    congr 1

theorem orderedPartition_injective : Function.Injective (@orderedPartition n) := by
  intro c d h
  have hl : c.length = d.length := by
    rw [← orderedPartition_card c, h, orderedPartition_card]
  have hr : Set.range (orderedBlockMax c) = Set.range (orderedBlockMax d) := by
    rw [orderedBlockMax_range, h, ← orderedBlockMax_range]
  cases c with
  | mk cl cs cp ce cm co cd cc =>
    cases d with
    | mk dl ds dp de dm do_ dd dc =>
      dsimp only at hl
      subst dl
      have hm := (orderedBlockMax_strictMono ⟨cl, cs, cp, ce, cm, co, cd, cc⟩).eq_of_range_eq
        (orderedBlockMax_strictMono ⟨cl, ds, dp, de, dm, do_, dd, dc⟩) hr
      have hb : ∀ j : Fin cl,
          orderedBlock ⟨cl, cs, cp, ce, cm, co, cd, cc⟩ j =
          orderedBlock ⟨cl, ds, dp, de, dm, do_, dd, dc⟩ j := by
        intro j
        apply (orderedPartition ⟨cl, cs, cp, ce, cm, co, cd, cc⟩).eq_of_mem_parts
          (a := orderedBlockMax ⟨cl, cs, cp, ce, cm, co, cd, cc⟩ j)
          (orderedBlock_mem_parts _ j)
        · rw [h]
          exact orderedBlock_mem_parts ⟨cl, ds, dp, de, dm, do_, dd, dc⟩ j
        · exact Finset.max'_mem _ _
        · rw [congrFun hm j]
          exact Finset.max'_mem _ _
      have hs : cs = ds := by
        funext j
        simpa only [orderedBlock_card] using congrArg Finset.card (hb j)
      subst ds
      have he : ce = de := by
        funext j
        apply (cm j).eq_of_range_eq (dm j)
        have hj := congrArg (fun B : Finset (Fin n) => (B : Set (Fin n))) (hb j)
        simpa only [orderedBlock, Finset.coe_image, Finset.coe_univ, Set.image_univ] using hj
      subst de
      rfl

def orderedPartitionEquiv : OrderedFinpartition n ≃ VertexPartition (Fin n) where
  toFun := orderedPartition
  invFun := orderedOfPartition
  left_inv _c := orderedPartition_injective (orderedPartition_orderedOfPartition _)
  right_inv := orderedPartition_orderedOfPartition

theorem sum_finPartition_by_card {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    (∑ P : VertexPartition (Fin n), f P.parts.card) =
      ∑ c : OrderedFinpartition n, f c.length := by
  rw [← Equiv.sum_comp orderedPartitionEquiv]
  simp only [orderedPartitionEquiv, Equiv.coe_fn_mk, orderedPartition_card]

theorem sum_finPartition_mobius (hn : 1 ≤ n) :
    (∑ P : VertexPartition (Fin n), cumulantMobius P.parts.card) =
      if n = 1 then 1 else 0 := by
  rw [sum_finPartition_by_card, sum_orderedPartition_mobius hn]

end

end TensorLB
