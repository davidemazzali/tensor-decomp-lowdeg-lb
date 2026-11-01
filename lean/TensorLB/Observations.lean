module

public import TensorLB.Parity
public import TensorLB.PolynomialSubstitution
public import TensorLB.WitnessBound

/-!
# Reduction from full tensor entries to parity coordinates

The nonempty parity supports form `Ω_k` from equation `eq:observations`.
Every full tensor entry is either one such observation or the deterministic
empty-support value. Substituting these expressions preserves evaluation and
does not increase total degree. Consequently moment matching against reduced
observations suffices for the full tensor estimation bounds.

Only the tensor-to-reduced-observation direction is needed here. The converse
realization of every reduced coordinate as a tensor entry is not used.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators

noncomputable section

/-- The index set `Ω_k`: nonempty sets of size at most `k` and the parity of `k`. -/
abbrev ObservationIndex (n k : ℕ) :=
  {A : Finset (Fin n) // A.Nonempty ∧ A.card ≤ k ∧ A.card % 2 = k % 2}

/-- Equation `eq:observations`, using only nonempty parity coordinates. -/
def reducedObservation (n m k : ℕ) (τ : ℝ) (ω : Sample n m)
    (A : ObservationIndex n k) : ℝ :=
  τ * (∏ i ∈ A.val, sign (ω.1 i)) +
    ∑ j : Fin (m - 1), ∏ i ∈ A.val, sign (ω.2 j i)

/-- Polynomial estimators in the reduced observation coordinates. -/
abbrev ObservationPolynomial (n k : ℕ) := MvPolynomial (ObservationIndex n k) ℝ

def reducedEstimator (n m k : ℕ) (τ : ℝ) (p : ObservationPolynomial n k)
    (ω : Sample n m) : ℝ :=
  MvPolynomial.eval (reducedObservation n m k τ ω) p

variable {n m k ℓ : ℕ} {τ : ℝ}

/-- Repeated indices cancel in pairs in each component of a tensor entry. -/
theorem tensor_eq_support (I : TensorIndex n k) (ω : Sample n m) :
    tensor n m k τ ω I =
      τ * (∏ i ∈ tensorSupport I, sign (ω.1 i)) +
        ∑ j : Fin (m - 1), ∏ i ∈ tensorSupport I, sign (ω.2 j i) := by
  simp only [tensor, prod_sign_eq_tensorSupport]

/-- Empty parity support gives a constant, not an additional random observation. -/
theorem tensor_eq_const_of_support_empty (I : TensorIndex n k)
    (h : tensorSupport I = ∅) (ω : Sample n m) :
    tensor n m k τ ω I = τ + ((m - 1 : ℕ) : ℝ) := by
  rw [tensor_eq_support, h]
  simp

/-- Each tensor variable becomes one reduced variable or the empty-support constant. -/
def tensorEntryPolynomial (n m k : ℕ) (τ : ℝ) (I : TensorIndex n k) :
    ObservationPolynomial n k :=
  if h : (tensorSupport I).Nonempty then
    MvPolynomial.X ⟨tensorSupport I, h, tensorSupport_card_le I,
      tensorSupport_card_mod_two I⟩
  else
    MvPolynomial.C (τ + ((m - 1 : ℕ) : ℝ))

theorem tensorEntryPolynomial_totalDegree_le (I : TensorIndex n k) :
    (tensorEntryPolynomial n m k τ I).totalDegree ≤ 1 := by
  classical
  unfold tensorEntryPolynomial
  split <;> simp only [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C,
    Nat.zero_le, le_refl]

@[simp] theorem eval_tensorEntryPolynomial (I : TensorIndex n k) (ω : Sample n m) :
    MvPolynomial.eval (reducedObservation n m k τ ω)
      (tensorEntryPolynomial n m k τ I) = tensor n m k τ ω I := by
  classical
  by_cases h : (tensorSupport I).Nonempty
  · simp only [tensorEntryPolynomial, dite_eq_left h, MvPolynomial.eval_X, reducedObservation]
    exact (tensor_eq_support I ω).symm
  · rw [tensorEntryPolynomial, dite_eq_right h, MvPolynomial.eval_C]
    exact (tensor_eq_const_of_support_empty I (Finset.not_nonempty_iff_eq_empty.mp h) ω).symm

/-- Substitute the parity-coordinate expressions into a full tensor polynomial. -/
def reducePolynomial (n m k : ℕ) (τ : ℝ) (p : TensorPolynomial n k) :
    ObservationPolynomial n k :=
  MvPolynomial.eval₂ MvPolynomial.C (tensorEntryPolynomial n m k τ) p

theorem reducePolynomial_totalDegree_le (p : TensorPolynomial n k) :
    (reducePolynomial n m k τ p).totalDegree ≤ p.totalDegree := by
  exact totalDegree_eval₂_le (tensorEntryPolynomial n m k τ) p
    tensorEntryPolynomial_totalDegree_le

@[simp] theorem reducedEstimator_reducePolynomial (p : TensorPolynomial n k)
    (ω : Sample n m) :
    reducedEstimator n m k τ (reducePolynomial n m k τ p) ω = estimator n m k τ p ω := by
  unfold reducedEstimator reducePolynomial
  rw [← MvPolynomial.eval_assoc]
  simp only [Function.comp_def, eval_tensorEntryPolynomial, estimator]

/-- Every degree-restricted tensor estimator has an identical reduced estimator
of no greater degree. This is the direction needed for the lower bound. -/
theorem exists_reduced_estimator (p : TensorPolynomial n k) :
    ∃ q : ObservationPolynomial n k, q.totalDegree ≤ p.totalDegree ∧
      ∀ ω, reducedEstimator n m k τ q ω = estimator n m k τ p ω :=
  ⟨reducePolynomial n m k τ p, reducePolynomial_totalDegree_le p,
    reducedEstimator_reducePolynomial p⟩

/-- Moment matching tested on polynomials in `Ω_k`, as in `eq:moment-matching`. -/
def IsReducedMomentMatchingWitness (n m k ℓ : ℕ) (τ : ℝ) (A : Finset (Fin n))
    (W : Sample n m → ℝ) : Prop :=
  ∀ p : ObservationPolynomial n k, p.totalDegree ≤ ℓ →
    expectation n m (fun ω => W ω * reducedEstimator n m k τ p ω) =
      expectation n m (fun ω => target n m A ω * reducedEstimator n m k τ p ω)

variable {A : Finset (Fin n)} {W : Sample n m → ℝ}

/-- Reduced-observation moment matching includes every full tensor polynomial. -/
theorem IsReducedMomentMatchingWitness.to_tensor
    (hW : IsReducedMomentMatchingWitness n m k ℓ τ A W) :
    IsMomentMatchingWitness n m k ℓ τ A W := by
  intro p hp
  simpa only [reducedEstimator_reducePolynomial] using
    hW (reducePolynomial n m k τ p) ((reducePolynomial_totalDegree_le p).trans hp)

/-- The observable reduction connects a witness built in reduced coordinates
to both conclusions stated in the full tensor specification. -/
theorem bounds_of_reduced_witness
    (hW : IsReducedMomentMatchingWitness n m k ℓ τ A W)
    {b : ℝ} (hbound : expectation n m (fun ω => W ω ^ 2) ≤ b) :
    correlation n m k ℓ τ A ^ 2 ≤ b ∧ 1 - b ≤ mmse n m k ℓ τ A :=
  bounds_of_witness hW.to_tensor hbound

end

end TensorLB
