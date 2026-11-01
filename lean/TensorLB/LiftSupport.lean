module

public import TensorLB.Fourier
public import TensorLB.LiftCounting

/-!
# Fourier supports of distinct-component placements

Nonempty character labels are placed into distinct background components.
Their product is one Boolean character, and its full sign support recovers
both the chosen components and their labels. This reduces inner products to
equality of labelled placements, before averaging over the embeddings.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators

noncomputable section

/-- A nonconstant character of one component. The auxiliary sets `Λ_k` are
subsets of these labels. Nonemptiness makes the component label recoverable. -/
abbrev NonemptyCharacter (n : ℕ) := {A : Finset (Fin n) // A.Nonempty}

variable {n m : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The complete sign support of a product using distinct background components. -/
def placementSupport (B : ι → NonemptyCharacter n) (e : ι ↪ Fin (m - 1)) :
    Finset (SignIndex n m) :=
  Finset.univ.biUnion (fun i => backgroundSupport (e i) (B i).val)

@[simp] theorem mem_backgroundSupport_inl (j : Fin (m - 1)) (A : Finset (Fin n))
    (x : Fin n) : Sum.inl x ∉ backgroundSupport j A := by
  simp [backgroundSupport]

@[simp] theorem mem_backgroundSupport_inr (j q : Fin (m - 1)) (A : Finset (Fin n))
    (x : Fin n) : Sum.inr (q, x) ∈ backgroundSupport j A ↔ j = q ∧ x ∈ A := by
  rw [backgroundSupport, Finset.mem_map]
  constructor
  · rintro ⟨a, ha, heq⟩
    obtain ⟨hjq, rfl⟩ := Prod.mk.inj (Sum.inr.inj heq)
    exact ⟨hjq, ha⟩
  · rintro ⟨rfl, hx⟩
    exact ⟨x, hx, rfl⟩

@[simp] theorem mem_placementSupport_inl (B : ι → NonemptyCharacter n)
    (e : ι ↪ Fin (m - 1)) (x : Fin n) : Sum.inl x ∉ placementSupport B e := by
  simp [placementSupport]

theorem mem_placementSupport_inr (B : ι → NonemptyCharacter n)
    (e : ι ↪ Fin (m - 1)) (j : Fin (m - 1)) (x : Fin n) :
    Sum.inr (j, x) ∈ placementSupport B e ↔ ∃ i, e i = j ∧ x ∈ (B i).val := by
  simp [placementSupport]

@[simp] theorem mem_placementSupport_at (B : ι → NonemptyCharacter n)
    (e : ι ↪ Fin (m - 1)) (i : ι) (x : Fin n) :
    Sum.inr (e i, x) ∈ placementSupport B e ↔ x ∈ (B i).val := by
  simp [mem_placementSupport_inr, e.injective.eq_iff]

/-- A labelled placement is sufficient to reconstruct the full sign support. -/
theorem mem_placementSupport_iff_labelledPlacement (B : ι → NonemptyCharacter n)
    (e : ι ↪ Fin (m - 1)) (j : Fin (m - 1)) (x : Fin n) :
    Sum.inr (j, x) ∈ placementSupport B e ↔
      ∃ A : NonemptyCharacter n, (j, A) ∈ labelledPlacement B e ∧ x ∈ A.val := by
  rw [mem_placementSupport_inr]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact ⟨B i, (mem_labelledPlacement B e j (B i)).2 ⟨i, hi, rfl⟩, hx⟩
  · rintro ⟨A, hA, hx⟩
    obtain ⟨i, hi, rfl⟩ := (mem_labelledPlacement B e j A).1 hA
    exact ⟨i, hi, hx⟩

theorem labelledPlacement_subset_of_placementSupport_eq
    (B : ι → NonemptyCharacter n) (C : κ → NonemptyCharacter n)
    (e : ι ↪ Fin (m - 1)) (f : κ ↪ Fin (m - 1))
    (h : placementSupport B e = placementSupport C f) :
    labelledPlacement B e ⊆ labelledPlacement C f := by
  classical
  rintro ⟨j, A⟩ hA
  obtain ⟨i, rfl, rfl⟩ := (mem_labelledPlacement B e j A).1 hA
  obtain ⟨x, hx⟩ := (B i).property
  have hx' : Sum.inr (e i, x) ∈ placementSupport C f := by
    rw [← h, mem_placementSupport_at]
    exact hx
  obtain ⟨a, ha, _⟩ := (mem_placementSupport_inr C f (e i) x).1 hx'
  have heq : C a = B i := by
    apply Subtype.ext
    apply Finset.ext
    intro y
    rw [← mem_placementSupport_at C f a y, ha, ← h, mem_placementSupport_at]
  exact (mem_labelledPlacement C f (e i) (B i)).2 ⟨a, ha, heq⟩

/-- Nonempty labels ensure that no occupied component disappears from the support. -/
theorem labelledPlacement_eq_of_placementSupport_eq
    (B : ι → NonemptyCharacter n) (C : κ → NonemptyCharacter n)
    (e : ι ↪ Fin (m - 1)) (f : κ ↪ Fin (m - 1))
    (h : placementSupport B e = placementSupport C f) :
    labelledPlacement B e = labelledPlacement C f :=
  Finset.Subset.antisymm (labelledPlacement_subset_of_placementSupport_eq B C e f h)
    (labelledPlacement_subset_of_placementSupport_eq C B f e h.symm)

theorem placementSupport_eq_iff
    (B : ι → NonemptyCharacter n) (C : κ → NonemptyCharacter n)
    (e : ι ↪ Fin (m - 1)) (f : κ ↪ Fin (m - 1)) :
    placementSupport B e = placementSupport C f ↔
      labelledPlacement B e = labelledPlacement C f := by
  constructor
  · exact labelledPlacement_eq_of_placementSupport_eq B C e f
  · intro h
    apply Finset.ext
    intro x
    cases x with
    | inl x => simp
    | inr jx =>
      obtain ⟨j, x⟩ := jx
      simp only [mem_placementSupport_iff_labelledPlacement, h]

/-- The unaveraged monomial appearing in `eq:fourier-witnesses`. -/
def placedCharacter (B : ι → NonemptyCharacter n) (e : ι ↪ Fin (m - 1))
    (ω : Sample n m) : ℝ :=
  ∏ i, character (B i).val (ω.2 (e i))

theorem backgroundSupport_disjoint {j q : Fin (m - 1)} (h : j ≠ q)
    (A B : Finset (Fin n)) : Disjoint (backgroundSupport j A) (backgroundSupport q B) := by
  apply Finset.disjoint_left.mpr
  intro x hA hB
  cases x with
  | inl x => exact mem_backgroundSupport_inl j A x hA
  | inr jx =>
    have ha := (mem_backgroundSupport_inr j jx.1 A jx.2).1 hA
    have hb := (mem_backgroundSupport_inr q jx.1 B jx.2).1 hB
    exact h (ha.1.trans hb.1.symm)

/-- Distinct component indices make the product one Fourier character. -/
theorem placedCharacter_eq_sampleCharacter (B : ι → NonemptyCharacter n)
    (e : ι ↪ Fin (m - 1)) (ω : Sample n m) :
    placedCharacter B e ω = sampleCharacter (placementSupport B e) ω := by
  classical
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι))
      (fun i => backgroundSupport (e i) (B i).val) := by
    intro i _ a _ hia
    exact backgroundSupport_disjoint (fun h => hia (e.injective h)) _ _
  symm
  change (∏ x ∈ placementSupport B e, sign (sampleEquiv n m ω x)) =
    ∏ i, character (B i).val (ω.2 (e i))
  rw [placementSupport, Finset.prod_biUnion hd]
  apply Finset.prod_congr rfl
  intro i _
  exact sampleCharacter_backgroundSupport (e i) (B i).val ω

/-- Inner products depend only on equality of labelled placements. -/
theorem expectation_placedCharacter_mul
    (B : ι → NonemptyCharacter n) (C : κ → NonemptyCharacter n)
    (e : ι ↪ Fin (m - 1)) (f : κ ↪ Fin (m - 1)) :
    expectation n m (fun ω => placedCharacter B e ω * placedCharacter C f ω) =
      if labelledPlacement B e = labelledPlacement C f then 1 else 0 := by
  simp_rw [placedCharacter_eq_sampleCharacter]
  rw [expectation_sampleCharacter_mul]
  simp only [placementSupport_eq_iff]

end

end TensorLB
