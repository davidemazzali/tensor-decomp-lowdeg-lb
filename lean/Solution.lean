module

public import TensorLB
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Pi

/-!
# Comparator solution entry point

The literal specification below independently repeats `Challenge.lean`.
Neither entry point imports the other. Definitional equality connects it to the
proof library; Comparator checks the reference and solution environments.

STATUS: the proof library's main theorem still contains `sorry`, so this solution
is unfinished and must fail strict verification until that proof is completed.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLBSpec

open scoped BigOperators

noncomputable section

-- BEGIN STATEMENT DEFINITIONS

/-- One distinguished component followed by the remaining `m - 1` components. -/
abbrev Sample (n m : ℕ) :=
  (Fin n → Bool) × (Fin (m - 1) → Fin n → Bool)

/-- The two equally likely values of a Rademacher sign. -/
def sign : Bool → ℝ
  | false => -1
  | true => 1

/-- Expectation with respect to the uniform distribution on all sign arrays. -/
def expectation (n m : ℕ) (f : Sample n m → ℝ) : ℝ :=
  (∑ ω : Sample n m, f ω) / (Fintype.card (Sample n m) : ℝ)

/-- An ordered index of a full order-`k` tensor, including repeated coordinates. -/
abbrev TensorIndex (n k : ℕ) := Fin k → Fin n

/-- Equation `eq:model`, entry by entry, with exactly `m - 1` unweighted terms. -/
def tensor (n m k : ℕ) (τ : ℝ) (ω : Sample n m) (I : TensorIndex n k) : ℝ :=
  τ * (∏ a : Fin k, sign (ω.1 (I a))) +
    ∑ j : Fin (m - 1), ∏ a : Fin k, sign (ω.2 j (I a))

/-- The target `x_A`: the product of the distinguished component's entries in `A`. -/
def target (n m : ℕ) (A : Finset (Fin n)) (ω : Sample n m) : ℝ :=
  ∏ i ∈ A, sign (ω.1 i)

/-- The target classes in equation `eq:targets`. -/
def admissibleTarget (n k : ℕ) (A : Finset (Fin n)) : Prop :=
  (k = 3 ∧ A.card = 1) ∨ (k = 4 ∧ (A.card = 2 ∨ A.card = 4))

/-- Real polynomials in all entries of the full tensor observation. -/
abbrev TensorPolynomial (n k : ℕ) := MvPolynomial (TensorIndex n k) ℝ

/-- The random estimator obtained by evaluating a polynomial at the tensor. -/
def estimator (n m k : ℕ) (τ : ℝ) (p : TensorPolynomial n k)
    (ω : Sample n m) : ℝ :=
  MvPolynomial.eval (tensor n m k τ ω) p

/-- Equation `eq:corr`: the signed normalized correlation, optimized over
all real tensor polynomials of total degree at most `ℓ` with positive second moment.
Nonemptiness and boundedness of this set remain proof obligations in the library. -/
def correlation (n m k ℓ : ℕ) (τ : ℝ) (A : Finset (Fin n)) : ℝ :=
  sSup {r : ℝ | ∃ p : TensorPolynomial n k,
    p.totalDegree ≤ ℓ ∧
    0 < expectation n m (fun ω => estimator n m k τ p ω ^ 2) ∧
    r = expectation n m (fun ω => target n m A ω * estimator n m k τ p ω) /
      Real.sqrt (expectation n m (fun ω => estimator n m k τ p ω ^ 2))}

/-- Equation `eq:mmse`: the infimum of the mean square errors over the same
degree-restricted polynomial space, with no second-moment restriction.
Nonemptiness and boundedness below remain proof obligations in the library. -/
def mmse (n m k ℓ : ℕ) (τ : ℝ) (A : Finset (Fin n)) : ℝ :=
  sInf {r : ℝ | ∃ p : TensorPolynomial n k,
    p.totalDegree ≤ ℓ ∧
    r = expectation n m (fun ω => (estimator n m k τ p ω - target n m A ω) ^ 2)}

-- END STATEMENT DEFINITIONS

/-- The reference statement, discharged by the proof library once complete. -/
theorem main :
    ∀ τ : ℝ, 1 < τ →
      ∃ C : ℝ, 0 < C ∧
        ∀ n m ℓ k : ℕ,
          4 ≤ n → 2 ≤ m → 1 ≤ ℓ → (k = 3 ∨ k = 4) →
          ℓ ^ 3 ≤ n →
          C * Real.rpow (n : ℝ) ((k : ℝ) / 2) *
            Real.rpow (ℓ : ℝ) ((k : ℝ) / 2 - 1) ≤ (m : ℝ) →
          ∀ A : Finset (Fin n), admissibleTarget n k A →
            correlation n m k ℓ τ A ^ 2 ≤
                Real.rpow (n : ℝ) (-((A.card : ℝ) / 2)) ∧
              1 - Real.rpow (n : ℝ) (-((A.card : ℝ) / 2)) ≤
                mmse n m k ℓ τ A := by
  exact TensorLB.main

end

end TensorLBSpec
