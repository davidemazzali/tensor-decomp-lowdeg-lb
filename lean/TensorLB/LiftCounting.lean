module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.Data.Multiset.Filter

/-!
# Counting labelled placements into distinct components

An embedding places one label at each selected component. Repeated labels
give the same placement under label-preserving permutations; their factorial
multiplicity is the normalization factor in the averaged Fourier witnesses.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators

noncomputable section

variable {ι κ J α : Type*} [Fintype ι] [Fintype κ]

/-- The graph of labels assigned to distinct components. -/
def labelledPlacement (B : ι → α) (e : ι ↪ J) : Finset (J × α) :=
  Finset.univ.map ⟨fun i => (e i, B i), fun _ _ h => e.injective (Prod.mk.inj h).1⟩

/-- The multiset of labels, independently of their ordering. -/
def labelMultiset (B : ι → α) : Multiset α := Finset.univ.val.map B

/-- The product of factorials of label multiplicities. -/
def placementMultiplicity [Fintype α] [DecidableEq α] (B : ι → α) : ℕ :=
  ∏ a : α, (Fintype.card {i // B i = a}).factorial

theorem mem_labelledPlacement (B : ι → α) (e : ι ↪ J) (j : J) (a : α) :
    (j, a) ∈ labelledPlacement B e ↔ ∃ i, e i = j ∧ B i = a := by
  simp only [labelledPlacement, Finset.mem_map, Finset.mem_univ, true_and]
  change (∃ i, (e i, B i) = (j, a)) ↔ _
  simp only [Prod.mk.injEq]

/-- A labelled placement determines its multiset of labels. -/
theorem labelMultiset_eq_of_labelledPlacement_eq
    (B : ι → α) (C : κ → α) (e : ι ↪ J) (f : κ ↪ J)
    (h : labelledPlacement B e = labelledPlacement C f) :
    labelMultiset B = labelMultiset C := by
  have hh := congrArg (fun p : Finset (J × α) => p.val.map Prod.snd) h
  simp only [labelledPlacement, Finset.map_val, Multiset.map_map] at hh
  exact hh

theorem count_labelMultiset [DecidableEq α] (B : ι → α) (a : α) :
    (labelMultiset B).count a = Fintype.card {i // B i = a} := by
  classical
  simp only [labelMultiset, Multiset.count_map, Fintype.card_subtype]
  simp only [← Finset.filter_val, Finset.card_def, eq_comm (a := a)]

/-- Permuting occurrences of the same labels leaves their placement unchanged. -/
theorem labelledPlacement_perm (B : ι → α) (e : ι ↪ J) (σ : Equiv.Perm ι)
    (hσ : B ∘ σ = B) :
    labelledPlacement B (σ.toEmbedding.trans e) = labelledPlacement B e := by
  classical
  ext ⟨j, a⟩
  simp only [mem_labelledPlacement]
  constructor
  · rintro ⟨i, hj, ha⟩
    exact ⟨σ i, hj, (congrFun hσ i).trans ha⟩
  · rintro ⟨i, hj, ha⟩
    refine ⟨σ.symm i, ?_, ?_⟩
    · simpa using hj
    · have hs := congrFun hσ (σ.symm i)
      simpa using hs.symm.trans (by simpa using ha)

/-- Equal placements differ by a permutation preserving their labels. -/
theorem exists_perm_of_labelledPlacement_eq (B : ι → α) (e f : ι ↪ J)
    (h : labelledPlacement B f = labelledPlacement B e) :
    ∃ σ : Equiv.Perm ι, B ∘ σ = B ∧ σ.toEmbedding.trans e = f := by
  classical
  have hex (i : ι) : ∃ j, e j = f i ∧ B j = B i := by
    apply (mem_labelledPlacement B e (f i) (B i)).mp
    rw [← h]
    exact (mem_labelledPlacement B f (f i) (B i)).mpr ⟨i, rfl, rfl⟩
  choose g hg hB using hex
  have hinj : Function.Injective g := by
    intro i j hij
    apply f.injective
    rw [← hg i, ← hg j, hij]
  let σ : Equiv.Perm ι := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hinj)
  refine ⟨σ, ?_, ?_⟩
  · funext i
    exact hB i
  · ext i
    exact hg i

/-- For a fixed placement, its repeated enumeration multiplicity is the product
of factorials of the numbers of equal labels. -/
theorem card_labelledPlacement_fiber [Fintype J] [Fintype α]
    [DecidableEq J] [DecidableEq α] (B : ι → α) (e : ι ↪ J) :
    Fintype.card {f : ι ↪ J // labelledPlacement B f = labelledPlacement B e} =
      placementMultiplicity B := by
  classical
  let ψ : {σ : Equiv.Perm ι // B ∘ σ = B} →
      {f : ι ↪ J // labelledPlacement B f = labelledPlacement B e} :=
    fun σ => ⟨σ.val.toEmbedding.trans e, labelledPlacement_perm B e σ.val σ.property⟩
  have hinj : Function.Injective ψ := by
    intro σ ρ h
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact e.injective (congrArg (fun f => f.val i) h)
  have hsurj : Function.Surjective ψ := by
    intro f
    obtain ⟨σ, hσ, hf⟩ := exists_perm_of_labelledPlacement_eq B e f.val f.property
    exact ⟨⟨σ, hσ⟩, Subtype.ext hf⟩
  calc
    _ = Fintype.card {σ : Equiv.Perm ι // B ∘ σ = B} :=
      (Fintype.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩)).symm
    _ = placementMultiplicity B := DomMulAct.stabilizer_card B

end

end TensorLB
