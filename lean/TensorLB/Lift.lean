module

public import TensorLB.OrderedLift
public import TensorLB.LiftIndex

/-!
# Distinct-component Fourier witnesses

A finitely supported multiplicity function represents the multiset `R` of
nonempty character labels. Its canonical labelled slots are the pairs `(B,i)`
with `i < R B`. Averaging their characters over embeddings into the background
components is exactly `U_R` in equation `eq:fourier-witnesses`, without choosing
an ordering of the multiset.

The construction permits all nonempty characters, and thus in particular both
auxiliary index sets `Λ_3` and `Λ_4`. These are functions of the underlying
signs, not additional observations. The normalization and orthogonality proved
here are equation `eq:orthogonality`.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

noncomputable section

variable {n m : ℕ}

/-- The averaged witness `U_R` with one slot for every copy of a character.
For degree greater than `m - 1`, the injection sum is empty and this is zero. -/
def monomialWitness (R : NonemptyCharacter n →₀ ℕ) (ω : Sample n m) : ℝ :=
  orderedWitness (witnessLabel R) ω

/-- The empty multiset gives the constant witness one. -/
@[simp] theorem monomialWitness_zero (ω : Sample n m) :
    monomialWitness (0 : NonemptyCharacter n →₀ ℕ) ω = 1 := by
  let : IsEmpty (WitnessSlot (0 : NonemptyCharacter n →₀ ℕ)) :=
    ⟨fun s => Fin.elim0 s.2⟩
  exact orderedWitness_empty (witnessLabel 0) ω

/-- There are no distinct-component placements once all background slots are exhausted. -/
theorem monomialWitness_eq_zero_of_degree_gt (R : NonemptyCharacter n →₀ ℕ)
    (h : m - 1 < witnessDegree R) (ω : Sample n m) : monomialWitness R ω = 0 := by
  unfold monomialWitness orderedWitness
  rw [card_witnessSlot, Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.cast_zero, div_zero]

/-- Different multisets have disjoint Fourier supports, even when they have
different numbers of character factors. -/
theorem expectation_monomialWitness_mul_eq_zero
    (R S : NonemptyCharacter n →₀ ℕ) (h : R ≠ S) :
    expectation n m (fun ω => monomialWitness R ω * monomialWitness S ω) = 0 := by
  apply expectation_orderedWitness_mul_eq_zero (witnessLabel R) (witnessLabel S)
  exact fun heq => h (labelMultiset_witnessLabel_injective heq)

/-- The exact witness second moment is `R! / (m - 1)^{underlined |R|}`.
This includes the empty multiset and, by division by zero, the empty injection
sum when the degree exceeds the number of background components. -/
theorem expectation_monomialWitness_sq (R : NonemptyCharacter n →₀ ℕ) :
    expectation n m (fun ω => monomialWitness R ω ^ 2) =
      (witnessFactorial R : ℝ) /
        (((m - 1).descFactorial (witnessDegree R) : ℕ) : ℝ) := by
  simpa only [monomialWitness, placementMultiplicity_witnessLabel, card_witnessSlot]
    using expectation_orderedWitness_sq (m := m) (witnessLabel R)

/-- In the manuscript's degree range the normalization is strictly positive. -/
theorem expectation_monomialWitness_sq_pos (R : NonemptyCharacter n →₀ ℕ)
    (h : witnessDegree R ≤ m - 1) :
    0 < expectation n m (fun ω => monomialWitness R ω ^ 2) := by
  rw [expectation_monomialWitness_sq]
  exact div_pos (Nat.cast_pos.mpr (witnessFactorial_pos R))
    (Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr h))

/-- Every witness indexed by a nonempty multiset has mean zero. -/
theorem expectation_monomialWitness_eq_zero
    {R : NonemptyCharacter n →₀ ℕ} (h : R ≠ 0) :
    expectation n m (monomialWitness R) = 0 := by
  simpa only [monomialWitness_zero, mul_one] using
    expectation_monomialWitness_mul_eq_zero (m := m) R 0 h

/-- Combined diagonal/off-diagonal inner product formula for the witness family. -/
theorem expectation_monomialWitness_mul (R S : NonemptyCharacter n →₀ ℕ) :
    expectation n m (fun ω => monomialWitness R ω * monomialWitness S ω) =
      if R = S then
        (witnessFactorial R : ℝ) /
          (((m - 1).descFactorial (witnessDegree R) : ℕ) : ℝ)
      else 0 := by
  classical
  by_cases h : R = S
  · subst S
    simpa only [ite_true, ← sq] using expectation_monomialWitness_sq (m := m) R
  · rw [ite_eq_right h, expectation_monomialWitness_mul_eq_zero R S h]

end

end TensorLB

