module

public import TensorLB.WitnessAssembly
public import TensorLB.RankScale

import Mathlib.Tactic.NormNum

/-!
# The final reduction to uniform homogeneous witness estimates

This module proves the quantified conclusion of the challenge conditional on
the remaining analytic/combinatorial construction, stated explicitly below.
It is not a proof of that construction. No additional axiom is introduced.

The remaining estimate is the termwise version of equation (43), after the
coefficient estimate, substitution norm bound, and falling-factorial bound.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators

noncomputable section

/-- The witness construction and uniform estimates still required from the
response-coefficient and substitution arguments. The background-rank condition
here is only `N ≥ 6D`; the large rank constant is supplied by the final reduction. -/
def UniformWitnessEstimates (τ B : ℝ) : Prop :=
  ∀ n m D k : ℕ, 4 ≤ n → 2 ≤ m → 1 ≤ D → (k = 3 ∨ k = 4) →
    D ^ 3 ≤ n → 6 * D ≤ m - 1 →
    ∀ A : Finset (Fin n), admissibleTarget n k A →
      ∃ W : ℕ → Sample n m → ℝ,
        IsReducedMomentMatchingWitness n m k D τ A
          (fun ω => ∑ d ∈ Finset.range D, W (d + 1) ω) ∧
        ∀ d, 1 ≤ d → d ≤ D → witnessNorm (W d) ≤
          Real.rpow (n : ℝ) (-((A.card : ℝ) / 4)) *
            Real.sqrt (36 * B * rankScale n d k / (((m - 1 : ℕ) : ℝ) - D + 1)) ^ d

/-- The geometric-base comparison gives both bounds with the same constant. -/
theorem bounds_of_uniformWitnessEstimates {τ B : ℝ} (hB : 0 ≤ B)
    (hW : UniformWitnessEstimates τ B)
    {n m D k : ℕ} (hn : 4 ≤ n) (hm : 2 ≤ m) (hD : 1 ≤ D)
    (hk : k = 3 ∨ k = 4) (hdegree : D ^ 3 ≤ n)
    (hrank : sufficientRankConstant B * rankScale n D k ≤ (m : ℝ))
    (A : Finset (Fin n)) (hA : admissibleTarget n k A) :
    correlation n m k D τ A ^ 2 ≤ Real.rpow (n : ℝ) (-((A.card : ℝ) / 2)) ∧
      1 - Real.rpow (n : ℝ) (-((A.card : ℝ) / 2)) ≤ mmse n m k D τ A := by
  have hk2 : 2 ≤ k := by omega
  have hscale := degree_le_rankScale (by omega : 1 ≤ n) hD hdegree hk2
  have hN := (background_rank_bounds hm hscale hrank).1
  obtain ⟨W, hmatch, hnorm⟩ := hW n m D k hn hm hD hk hdegree hN A hA
  apply main_bounds_of_geometric_witness W A _ hmatch
  intro d hd
  apply (hnorm (d + 1) (by omega) (by omega)).trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hbase := geometric_base_le_quarter hB hm (by omega : d + 1 ≤ D) hk2 hscale hrank
  have hsqrt : Real.sqrt
      (36 * B * rankScale n (d + 1) k / (((m - 1 : ℕ) : ℝ) - D + 1)) ≤ 1 / 2 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · nlinarith
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt (d + 1)

/-- All quantifiers and both estimation conclusions of `TensorLB.main` follow
from the single remaining uniform witness construction. The challenge and the
solution retain their original, unconditional statement. -/
theorem main_of_uniformWitnessEstimates
    (h : ∀ τ : ℝ, 1 < τ → ∃ B : ℝ, 0 < B ∧ UniformWitnessEstimates τ B) :
    ∀ τ : ℝ, 1 < τ →
      ∃ C : ℝ, 0 < C ∧
        ∀ n m D k : ℕ,
          4 ≤ n → 2 ≤ m → 1 ≤ D → (k = 3 ∨ k = 4) →
          D ^ 3 ≤ n →
          C * Real.rpow (n : ℝ) ((k : ℝ) / 2) *
            Real.rpow (D : ℝ) ((k : ℝ) / 2 - 1) ≤ (m : ℝ) →
          ∀ A : Finset (Fin n), admissibleTarget n k A →
            correlation n m k D τ A ^ 2 ≤
                Real.rpow (n : ℝ) (-((A.card : ℝ) / 2)) ∧
              1 - Real.rpow (n : ℝ) (-((A.card : ℝ) / 2)) ≤
                mmse n m k D τ A := by
  intro τ hτ
  obtain ⟨B, hB, hW⟩ := h τ hτ
  refine ⟨sufficientRankConstant B, sufficientRankConstant_pos B, ?_⟩
  intro n m D k hn hm hD hk hdegree hrank A hA
  apply bounds_of_uniformWitnessEstimates hB.le hW hn hm hD hk hdegree _ A hA
  change sufficientRankConstant B *
    (Real.rpow (n : ℝ) ((k : ℝ) / 2) * Real.rpow (D : ℝ) ((k : ℝ) / 2 - 1)) ≤ (m : ℝ)
  simpa only [mul_assoc] using hrank

end

end TensorLB
