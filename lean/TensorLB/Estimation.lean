module

public import TensorLB.Expectation
public import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Linarith

/-!
# Well-posed low-degree estimation

The real supremum and infimum in the reference definitions range over nonempty
sets, bounded above and below respectively. The resulting correlation and mean
squared error lie in `[0, 1]`.
The final two lemmas pass bounds for individual estimators to the optimizations.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

noncomputable section

variable {n m k ℓ : ℕ} {τ : ℝ} {A : Finset (Fin n)}

@[simp] theorem estimator_zero (ω : Sample n m) :
    estimator n m k τ 0 ω = 0 := by
  simp [estimator]

@[simp] theorem estimator_one (ω : Sample n m) :
    estimator n m k τ 1 ω = 1 := by
  simp [estimator]

@[simp] theorem estimator_neg (p : TensorPolynomial n k) (ω : Sample n m) :
    estimator n m k τ (-p) ω = -estimator n m k τ p ω := by
  simp [estimator]

/-- The attainable normalized correlations appearing in `correlation`. -/
def correlationValues (n m k ℓ : ℕ) (τ : ℝ) (A : Finset (Fin n)) : Set ℝ :=
  {r | ∃ p : TensorPolynomial n k,
    p.totalDegree ≤ ℓ ∧
    0 < expectation n m (fun ω => estimator n m k τ p ω ^ 2) ∧
    r = expectation n m (fun ω => target n m A ω * estimator n m k τ p ω) /
      Real.sqrt (expectation n m (fun ω => estimator n m k τ p ω ^ 2))}

/-- The attainable squared errors appearing in `mmse`. -/
def mmseValues (n m k ℓ : ℕ) (τ : ℝ) (A : Finset (Fin n)) : Set ℝ :=
  {r | ∃ p : TensorPolynomial n k,
    p.totalDegree ≤ ℓ ∧
    r = expectation n m (fun ω => (estimator n m k τ p ω - target n m A ω) ^ 2)}

theorem correlation_eq_sSup :
    correlation n m k ℓ τ A = sSup (correlationValues n m k ℓ τ A) := rfl

theorem mmse_eq_sInf : mmse n m k ℓ τ A = sInf (mmseValues n m k ℓ τ A) := rfl

theorem expectation_target_mem_correlationValues :
    expectation n m (target n m A) ∈ correlationValues n m k ℓ τ A := by
  refine ⟨1, by simp, ?_, ?_⟩ <;> simp

theorem correlationValues_nonempty : (correlationValues n m k ℓ τ A).Nonempty :=
  ⟨_, expectation_target_mem_correlationValues⟩

/-- Negating an estimator negates its normalized correlation. -/
theorem neg_mem_correlationValues {r : ℝ}
    (hr : r ∈ correlationValues n m k ℓ τ A) :
    -r ∈ correlationValues n m k ℓ τ A := by
  obtain ⟨p, hp, hpos, rfl⟩ := hr
  refine ⟨-p, ?_, ?_, ?_⟩
  · simpa only [MvPolynomial.totalDegree_neg] using hp
  · simpa only [estimator_neg, neg_sq] using hpos
  · simp only [estimator_neg, neg_sq, mul_neg, expectation_neg, neg_div]

/-- Every normalized target correlation has square at most one. -/
theorem sq_le_one_of_mem_correlationValues {r : ℝ}
    (hr : r ∈ correlationValues n m k ℓ τ A) : r ^ 2 ≤ 1 := by
  obtain ⟨p, _, hpos, rfl⟩ := hr
  have hcs := expectation_mul_sq_le (target n m A) (estimator n m k τ p)
  simp only [expectation_target_sq, one_mul] at hcs
  rw [div_pow, Real.sq_sqrt hpos.le]
  exact (div_le_one hpos).2 hcs

theorem correlationValues_bddAbove : BddAbove (correlationValues n m k ℓ τ A) := by
  refine ⟨1, fun r hr => ?_⟩
  have h := sq_le_one_of_mem_correlationValues hr
  nlinarith [sq_nonneg (r - 1)]

theorem correlation_nonneg : 0 ≤ correlation n m k ℓ τ A := by
  obtain ⟨r, hr⟩ := correlationValues_nonempty (n := n) (m := m) (k := k)
    (ℓ := ℓ) (τ := τ) (A := A)
  have hpos := le_csSup correlationValues_bddAbove hr
  have hneg := le_csSup correlationValues_bddAbove (neg_mem_correlationValues hr)
  rw [correlation_eq_sSup]
  linarith

theorem correlation_le_one : correlation n m k ℓ τ A ≤ 1 := by
  rw [correlation_eq_sSup]
  apply csSup_le correlationValues_nonempty
  intro r hr
  have h := sq_le_one_of_mem_correlationValues hr
  nlinarith [sq_nonneg (r - 1)]

theorem one_mem_mmseValues : 1 ∈ mmseValues n m k ℓ τ A := by
  refine ⟨0, by simp, ?_⟩
  simp

theorem mmseValues_nonempty : (mmseValues n m k ℓ τ A).Nonempty :=
  ⟨1, one_mem_mmseValues⟩

theorem mmseValues_bddBelow : BddBelow (mmseValues n m k ℓ τ A) := by
  refine ⟨0, ?_⟩
  rintro r ⟨p, _, rfl⟩
  exact expectation_sq_nonneg _

theorem mmse_nonneg : 0 ≤ mmse n m k ℓ τ A := by
  rw [mmse_eq_sInf]
  apply le_csInf mmseValues_nonempty
  rintro r ⟨p, _, rfl⟩
  exact expectation_sq_nonneg _

theorem mmse_le_one : mmse n m k ℓ τ A ≤ 1 := by
  rw [mmse_eq_sInf]
  exact csInf_le mmseValues_bddBelow one_mem_mmseValues

/-- An upper bound for each normalized estimator also bounds the supremum. -/
theorem correlation_le_of_forall {b : ℝ}
    (h : ∀ p : TensorPolynomial n k, p.totalDegree ≤ ℓ →
      0 < expectation n m (fun ω => estimator n m k τ p ω ^ 2) →
      expectation n m (fun ω => target n m A ω * estimator n m k τ p ω) /
        Real.sqrt (expectation n m (fun ω => estimator n m k τ p ω ^ 2)) ≤ b) :
    correlation n m k ℓ τ A ≤ b := by
  rw [correlation_eq_sSup]
  apply csSup_le correlationValues_nonempty
  rintro r ⟨p, hp, hpos, rfl⟩
  exact h p hp hpos

/-- A lower bound for every estimator's error also bounds the infimum. -/
theorem le_mmse_of_forall {b : ℝ}
    (h : ∀ p : TensorPolynomial n k, p.totalDegree ≤ ℓ →
      b ≤ expectation n m (fun ω => (estimator n m k τ p ω - target n m A ω) ^ 2)) :
    b ≤ mmse n m k ℓ τ A := by
  rw [mmse_eq_sInf]
  apply le_csInf mmseValues_nonempty
  rintro r ⟨p, hp, rfl⟩
  exact h p hp

end

end TensorLB
