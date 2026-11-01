module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Pi

/-!
# Reference challenge for the tensor lower bound

This file imports only Mathlib. Its definitions and theorem statement constitute
an independently readable reference specification for `thm:main` in
`tensor_low_degree_k3_k4.tex`; they still require mathematical review.
Keep this file independent of `Solution.lean` and the proof library.

The sample space has one distinguished sign vector and `m - 1` noise vectors.
Under the theorem's `m ≥ 2` assumption this is exactly the manuscript's model.
Coordinate zero in `Fin n` corresponds to coordinate one in the manuscript.

The final `sorry` is an intentional challenge placeholder. It supplies no proof
to the solution, which must pass the configured axiom audit independently.
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

/-- Reference statement of manuscript Theorem `thm:main`, with one constant
uniform in `n`, `m`, `ℓ`, tensor order `k`, and target `A`. -/
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
  sorry

end

end TensorLBSpec
