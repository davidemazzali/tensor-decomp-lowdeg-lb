module

public import TensorLB.GeneratingFunction
public import TensorLB.PolynomialSubstitution

import Mathlib.Tactic.NormNum

/-!
# Connected-coordinate substitution

The cubic formula sums over the three singleton/complement splits; the quartic
formula sums over all six pairs and divides by two to count the three unordered
pair partitions. This avoids choosing an ordering of a target set.

Hidden letters range over all nonempty characters. Each letter actually used
by the cubic map has size at most three, and the quartic map uses only pairs
and quartets, as in the manuscript's auxiliary alphabets.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n m k : ℕ}

/-- Hidden character variable, with the deterministic empty character equal to one. -/
def hiddenVariable (B : Finset (Fin n)) : MvPolynomial (NonemptyCharacter n) ℝ :=
  if h : B.Nonempty then MvPolynomial.X ⟨B, h⟩ else 1

theorem hiddenVariable_totalDegree_le (B : Finset (Fin n)) :
    (hiddenVariable B).totalDegree ≤ 1 := by
  unfold hiddenVariable
  split <;> simp

/-- The cubic third-cumulant polynomial, valid in particular for a triple `I`. -/
def cubicConnectedPolynomial (I : Finset (Fin n)) : MvPolynomial (NonemptyCharacter n) ℝ :=
  hiddenVariable I - (∑ i ∈ I, hiddenVariable {i} * hiddenVariable (I.erase i)) +
    MvPolynomial.C 2 * ∏ i ∈ I, hiddenVariable {i}

/-- The quartic fourth-cumulant polynomial under a globally even tilt. -/
def quarticConnectedPolynomial (I : Finset (Fin n)) : MvPolynomial (NonemptyCharacter n) ℝ :=
  hiddenVariable I - MvPolynomial.C (1 / 2) *
    ∑ B ∈ I.powersetCard 2, hiddenVariable B * hiddenVariable (I \ B)

/-- The substitution `b_k` of equation (37). -/
def connectedSubstitution (I : ObservationIndex n k) : MvPolynomial (NonemptyCharacter n) ℝ :=
  if k = 3 ∧ I.val.card = 3 then cubicConnectedPolynomial I.val
  else if k = 4 ∧ I.val.card = 4 then quarticConnectedPolynomial I.val
  else hiddenVariable I.val

theorem cubicConnectedPolynomial_totalDegree_le (I : Finset (Fin n)) (hI : I.card ≤ 3) :
    (cubicConnectedPolynomial I).totalDegree ≤ 3 := by
  unfold cubicConnectedPolynomial
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · exact (hiddenVariable_totalDegree_le I).trans (by decide)
    · apply MvPolynomial.totalDegree_finsetSum_le
      intro i _
      exact (MvPolynomial.totalDegree_mul _ _).trans
        ((Nat.add_le_add (hiddenVariable_totalDegree_le _) (hiddenVariable_totalDegree_le _)).trans
          (by decide))
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    simp only [MvPolynomial.totalDegree_C, zero_add]
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    calc
      _ ≤ ∑ _i ∈ I, 1 := Finset.sum_le_sum (fun i _ => hiddenVariable_totalDegree_le {i})
      _ = I.card := by simp
      _ ≤ 3 := hI

theorem quarticConnectedPolynomial_totalDegree_le (I : Finset (Fin n)) :
    (quarticConnectedPolynomial I).totalDegree ≤ 2 := by
  unfold quarticConnectedPolynomial
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · exact (hiddenVariable_totalDegree_le I).trans (by decide)
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    simp only [MvPolynomial.totalDegree_C, zero_add]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro B _
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (hiddenVariable_totalDegree_le _) (hiddenVariable_totalDegree_le _))

/-- Maximum hidden degree of one connected coordinate. -/
def substitutionDegree (k : ℕ) : ℕ := if k = 3 then 3 else 2

theorem connectedSubstitution_totalDegree_le (I : ObservationIndex n k) :
    (connectedSubstitution I).totalDegree ≤ substitutionDegree k := by
  unfold connectedSubstitution
  split
  · rename_i h
    simpa [substitutionDegree, h.1] using
      cubicConnectedPolynomial_totalDegree_le I.val h.2.le
  · split
    · rename_i h
      simpa [substitutionDegree, h.1] using quarticConnectedPolynomial_totalDegree_le I.val
    · exact (hiddenVariable_totalDegree_le _).trans (by unfold substitutionDegree; split <;> decide)

/-- Substitute hidden-character connected coordinates in an observable polynomial. -/
def substituteConnected (p : ObservationPolynomial n k) : MvPolynomial (NonemptyCharacter n) ℝ :=
  MvPolynomial.eval₂ MvPolynomial.C connectedSubstitution p

theorem substituteConnected_totalDegree_le (p : ObservationPolynomial n k) :
    (substituteConnected p).totalDegree ≤ p.totalDegree * substitutionDegree k :=
  totalDegree_eval₂_le_mul connectedSubstitution p connectedSubstitution_totalDegree_le

/-- Connected coordinates defined by their explicit moment formulas. -/
def connectedCoordinate (t : ObservationIndex n k → ℝ) (I : ObservationIndex n k) : ℝ :=
  if k = 3 ∧ I.val.card = 3 then
    tiltedMoment t I.val - (∑ i ∈ I.val, tiltedMoment t {i} * tiltedMoment t (I.val.erase i)) +
      2 * ∏ i ∈ I.val, tiltedMoment t {i}
  else if k = 4 ∧ I.val.card = 4 then
    tiltedMoment t I.val - (1 / 2) *
      ∑ B ∈ I.val.powersetCard 2, tiltedMoment t B * tiltedMoment t (I.val \ B)
  else tiltedMoment t I.val

theorem tiltedMoment_empty (t : ObservationIndex n k → ℝ) : tiltedMoment t ∅ = 1 := by
  simp only [tiltedMoment, character_empty, one_mul]
  exact div_self (ne_of_gt (partitionFunction_pos t))

theorem eval_hiddenVariable (t : ObservationIndex n k → ℝ) (B : Finset (Fin n)) :
    MvPolynomial.eval (fun B => tiltedMoment t B.val) (hiddenVariable B) = tiltedMoment t B := by
  unfold hiddenVariable
  split
  · simp
  · rename_i h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, tiltedMoment_empty, map_one]

/-- The exact substitution identity `b_k(φ(t)) = K(t)`. -/
theorem eval_connectedSubstitution (t : ObservationIndex n k → ℝ) (I : ObservationIndex n k) :
    MvPolynomial.eval (fun B => tiltedMoment t B.val) (connectedSubstitution I) =
      connectedCoordinate t I := by
  unfold connectedSubstitution connectedCoordinate
  split
  · simp only [cubicConnectedPolynomial, map_add, map_sub, map_sum, map_mul, map_prod,
      MvPolynomial.eval_C, eval_hiddenVariable]
  · split
    · simp only [quarticConnectedPolynomial, map_sub, map_mul, map_sum,
        MvPolynomial.eval_C, eval_hiddenVariable]
    · exact eval_hiddenVariable t I.val

theorem eval_substituteConnected (t : ObservationIndex n k → ℝ) (p : ObservationPolynomial n k) :
    MvPolynomial.eval (fun B => tiltedMoment t B.val) (substituteConnected p) =
      MvPolynomial.eval (connectedCoordinate t) p := by
  unfold substituteConnected
  rw [← MvPolynomial.eval_assoc]
  simp only [Function.comp_def, eval_connectedSubstitution]

end

end TensorLB
