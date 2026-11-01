module

public import TensorLB.LiftSupport
public import TensorLB.ExpectationSum

import Mathlib.Tactic.FieldSimp

/-!
# Averaging characters over distinct background components

An embedding assigns each labelled slot to a different background component.
The number of embeddings is the falling factorial in equation
`eq:fourier-witnesses`. Orthogonality reduces the second moment to the number
of assignments giving the same labelled placement.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators

noncomputable section

variable {n m : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Average a labelled family of characters over all distinct component choices.
If there are too many slots, the empty sum and zero denominator give zero. -/
def orderedWitness (B : ι → NonemptyCharacter n) (ω : Sample n m) : ℝ :=
  (∑ e : ι ↪ Fin (m - 1), placedCharacter B e ω) /
    (((m - 1).descFactorial (Fintype.card ι) : ℕ) : ℝ)

/-- The inner product is a normalized count of coinciding labelled placements. -/
theorem expectation_orderedWitness_mul
    (B : ι → NonemptyCharacter n) (C : κ → NonemptyCharacter n) :
    expectation n m (fun ω => orderedWitness B ω * orderedWitness C ω) =
      (∑ e : ι ↪ Fin (m - 1), ∑ f : κ ↪ Fin (m - 1),
        if labelledPlacement B e = labelledPlacement C f then (1 : ℝ) else 0) /
      ((((m - 1).descFactorial (Fintype.card ι) : ℕ) : ℝ) *
        (((m - 1).descFactorial (Fintype.card κ) : ℕ) : ℝ)) := by
  classical
  simp only [orderedWitness, div_mul_div_comm, expectation_div_const,
    expectation_sum_mul_sum, expectation_placedCharacter_mul]

/-- Different multisets of character labels have disjoint Fourier supports. -/
theorem expectation_orderedWitness_mul_eq_zero
    (B : ι → NonemptyCharacter n) (C : κ → NonemptyCharacter n)
    (h : labelMultiset B ≠ labelMultiset C) :
    expectation n m (fun ω => orderedWitness B ω * orderedWitness C ω) = 0 := by
  classical
  rw [expectation_orderedWitness_mul]
  have hne (e : ι ↪ Fin (m - 1)) (f : κ ↪ Fin (m - 1)) :
      labelledPlacement B e ≠ labelledPlacement C f :=
    fun heq => h (labelMultiset_eq_of_labelledPlacement_eq B C e f heq)
  simp only [hne, ite_false, Finset.sum_const_zero, zero_div]

/-- Every placement occurs once for each permutation of its identical labels. -/
theorem sum_matching_placements (B : ι → NonemptyCharacter n)
    (e : ι ↪ Fin (m - 1)) :
    (∑ f : ι ↪ Fin (m - 1),
      if labelledPlacement B e = labelledPlacement B f then (1 : ℝ) else 0) =
      (placementMultiplicity B : ℝ) := by
  classical
  rw [Finset.sum_boole]
  have h := card_labelledPlacement_fiber B e
  rw [Fintype.card_subtype] at h
  exact_mod_cast (by simpa only [eq_comm] using h)

/-- Equation `eq:orthogonality` for a labelled enumeration of a multiset.
The numerator is the product of factorials of repeated-label counts. -/
theorem expectation_orderedWitness_sq (B : ι → NonemptyCharacter n) :
    expectation n m (fun ω => orderedWitness B ω ^ 2) =
      (placementMultiplicity B : ℝ) /
        (((m - 1).descFactorial (Fintype.card ι) : ℕ) : ℝ) := by
  classical
  simp only [sq, expectation_orderedWitness_mul, sum_matching_placements,
    Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq, Fintype.card_fin,
    nsmul_eq_mul]
  by_cases h : (((m - 1).descFactorial (Fintype.card ι) : ℕ) : ℝ) = 0
  · simp [h]
  · field_simp

/-- The witness with no slots is the constant one. -/
@[simp] theorem orderedWitness_empty [IsEmpty ι] (B : ι → NonemptyCharacter n)
    (ω : Sample n m) : orderedWitness B ω = 1 := by
  simp [orderedWitness, placedCharacter]

end

end TensorLB

