module

public import TensorLB.LiftSupport
public import Mathlib.Data.Finsupp.Multiset

/-!
# Multiset indices for the averaged witnesses

A finitely supported multiplicity function records the multiset `R` of
nonempty character labels. Each occurrence has a canonical slot `(A, i)`;
its label forgets `i`. The slot count is `|R|`, and the label-preserving
permutation multiplicity is exactly `R!`.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- One slot for each occurrence of a character in the multiset. -/
abbrev WitnessSlot (R : NonemptyCharacter n →₀ ℕ) :=
  Σ A : NonemptyCharacter n, Fin (R A)

/-- Forget the occurrence number and retain the character label. -/
def witnessLabel (R : NonemptyCharacter n →₀ ℕ) : WitnessSlot R → NonemptyCharacter n :=
  Sigma.fst

/-- The cardinality `|R|` of the multiset of labels. -/
def witnessDegree (R : NonemptyCharacter n →₀ ℕ) : ℕ :=
  R.sum (fun _ r => r)

/-- The repeated-label multiplicity `R! = ∏_A (R_A)!`. -/
def witnessFactorial (R : NonemptyCharacter n →₀ ℕ) : ℕ :=
  ∏ A : NonemptyCharacter n, (R A).factorial

/-- Labels with zero multiplicity contribute one, so `R!` is a support product. -/
theorem witnessFactorial_eq_prod (R : NonemptyCharacter n →₀ ℕ) :
    witnessFactorial R = R.prod (fun _ r => r.factorial) := by
  exact (Finsupp.prod_fintype R (fun _ r => r.factorial) (fun _ => rfl)).symm

@[simp] theorem witnessDegree_single (A : NonemptyCharacter n) (r : ℕ) :
    witnessDegree (Finsupp.single A r) = r := by
  simp [witnessDegree]

@[simp] theorem witnessFactorial_single (A : NonemptyCharacter n) (r : ℕ) :
    witnessFactorial (Finsupp.single A r) = r.factorial := by
  rw [witnessFactorial_eq_prod]
  exact Finsupp.prod_single_index rfl

theorem card_witnessSlot (R : NonemptyCharacter n →₀ ℕ) :
    Fintype.card (WitnessSlot R) = witnessDegree R := by
  simp only [WitnessSlot, Fintype.card_sigma, Fintype.card_fin, witnessDegree]
  exact (Finsupp.sum_fintype R (fun _ r => r) (fun _ => rfl)).symm

/-- The slots carrying label `A` are exactly its `R A` occurrences. -/
def witnessLabelFiberEquiv (R : NonemptyCharacter n →₀ ℕ) (A : NonemptyCharacter n) :
    {s : WitnessSlot R // witnessLabel R s = A} ≃ Fin (R A) where
  toFun x := by
    rcases x with ⟨⟨B, i⟩, h⟩
    change B = A at h
    exact h ▸ i
  invFun i := ⟨⟨A, i⟩, rfl⟩
  left_inv x := by
    rcases x with ⟨⟨B, i⟩, h⟩
    change B = A at h
    subst B
    rfl
  right_inv i := rfl

theorem card_witnessLabel_fiber (R : NonemptyCharacter n →₀ ℕ)
    (A : NonemptyCharacter n) :
    Fintype.card {s : WitnessSlot R // witnessLabel R s = A} = R A := by
  rw [Fintype.card_congr (witnessLabelFiberEquiv R A), Fintype.card_fin]

theorem count_labelMultiset_witnessLabel (R : NonemptyCharacter n →₀ ℕ)
    (A : NonemptyCharacter n) :
    (labelMultiset (witnessLabel R)).count A = R A := by
  rw [count_labelMultiset, card_witnessLabel_fiber]

/-- Canonical slots enumerate exactly the multiset encoded by `R`. -/
theorem labelMultiset_witnessLabel (R : NonemptyCharacter n →₀ ℕ) :
    labelMultiset (witnessLabel R) = R.toMultiset := by
  apply Multiset.ext.mpr
  intro A
  rw [count_labelMultiset_witnessLabel, Finsupp.count_toMultiset]

theorem placementMultiplicity_witnessLabel (R : NonemptyCharacter n →₀ ℕ) :
    placementMultiplicity (witnessLabel R) = witnessFactorial R := by
  unfold placementMultiplicity witnessFactorial
  apply Finset.prod_congr rfl
  intro A _
  rw [card_witnessLabel_fiber]

theorem labelMultiset_witnessLabel_injective :
    Function.Injective (fun R : NonemptyCharacter n →₀ ℕ => labelMultiset (witnessLabel R)) := by
  intro R S h
  apply Finsupp.ext
  intro A
  have hc := congrArg (fun M : Multiset (NonemptyCharacter n) => M.count A) h
  simpa only [count_labelMultiset_witnessLabel] using hc

@[simp] theorem witnessDegree_zero : witnessDegree (0 : NonemptyCharacter n →₀ ℕ) = 0 := by
  simp [witnessDegree]

@[simp] theorem witnessFactorial_zero : witnessFactorial (0 : NonemptyCharacter n →₀ ℕ) = 1 := by
  simp [witnessFactorial]

theorem witnessFactorial_pos (R : NonemptyCharacter n →₀ ℕ) : 0 < witnessFactorial R := by
  exact Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem witnessDegree_eq_card_toMultiset (R : NonemptyCharacter n →₀ ℕ) :
    witnessDegree R = R.toMultiset.card := by
  simp only [Finsupp.card_toMultiset, witnessDegree, Function.id_def]

end

end TensorLB
