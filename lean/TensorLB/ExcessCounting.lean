module

public import TensorLB.MultiplicityEncoding
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Summing supports and excess multiplicities

The support/excess encoding reduces weighted slot assignments to a sum of
binomial coefficients. The exponential-series estimate then sums that bound.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n s d L : ℕ}

def coverCodes (A : Finset (Fin n)) (L : ℕ) :
    Finset (Σ _e : ℕ, Σ _H : Finset (Fin n), Fin n →₀ ℕ) :=
  (Finset.range (L + 1)).sigma (fun e =>
    ((Finset.univ : Finset (Fin n)).powersetCard (L - e)).sigma
      (fun H => Finset.finsuppAntidiag (A ∪ H) e))

def multiplicityCode (R : Fin n →₀ ℕ) (A : Finset (Fin n)) :
    Σ _e : ℕ, Σ _H : Finset (Fin n), Fin n →₀ ℕ :=
  ⟨(excessMultiplicity R A).sum (fun _ r => r), nonrootSupport R A, excessMultiplicity R A⟩

theorem multiplicityCode_mem {R : Fin n →₀ ℕ} {A : Finset (Fin n)}
    (hR : coordinateParity R = A) (hs : R.sum (fun _ r => r) = 2 * L + A.card) :
    multiplicityCode R A ∈ coverCodes A L := by
  have h := excessMultiplicity_degree hR hs
  apply Finset.mem_sigma.mpr
  refine ⟨Finset.mem_range.mpr (by dsimp [multiplicityCode]; omega), ?_⟩
  apply Finset.mem_sigma.mpr
  constructor
  · apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _, by dsimp [multiplicityCode]; omega⟩
  · apply Finset.mem_finsuppAntidiag'.mpr
    exact ⟨rfl, excessMultiplicity_support A⟩

theorem weightedSlotCount_le_code_sum (A : Finset (Fin n))
    (hs : s = 2 * L + A.card) (hslot : s ≤ 4 * d) :
    weightedSlotCount n s A ≤
      ∑ c ∈ coverCodes A L,
        (s.factorial : ℝ) * (16 * Real.exp 1) ^ s * (d : ℝ) ^ (2 * c.1) := by
  rw [weightedSlotCount_eq_multiplicity_sum, ← Finset.sum_filter]
  apply Finset.sum_le_sum_of_injOn (fun R => multiplicityCode R A)
  · intro R hR S hS h
    apply multiplicity_encoding_injective A (Finset.mem_filter.mp hR).2
      (Finset.mem_filter.mp hS).2
    exact congrArg (fun c : Σ _e : ℕ, Σ _H : Finset (Fin n), Fin n →₀ ℕ =>
      (c.2.1, c.2.2)) h
  · intro c hc
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hRdeg, hRpar⟩ := Finset.mem_filter.mp hR
    apply multiplicityCode_mem hRpar
    exact (Finset.mem_finsuppAntidiag'.mp hRdeg).1.trans hs
  · intro R hR
    obtain ⟨hRdeg, hRpar⟩ := Finset.mem_filter.mp hR
    exact multinomial_weight_le hRpar (Finset.mem_finsuppAntidiag'.mp hRdeg).1 hslot
  · intro c _ _
    positivity

theorem coverCodes_sum_le (A : Finset (Fin n)) :
    (∑ c ∈ coverCodes A L,
      (s.factorial : ℝ) * (16 * Real.exp 1) ^ s * (d : ℝ) ^ (2 * c.1)) ≤
      (s.factorial : ℝ) * (16 * Real.exp 1) ^ s *
        ∑ e ∈ Finset.range (L + 1),
          (n : ℝ) ^ (L - e) / (L - e).factorial *
            ((L + A.card - 1).choose e : ℝ) * (d : ℝ) ^ (2 * e) := by
  rw [coverCodes, Finset.sum_sigma, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  have heL : e ≤ L := Nat.le_of_lt_succ (Finset.mem_range.mp he)
  rw [Finset.sum_sigma]
  calc
    _ ≤ ∑ _H ∈ (Finset.univ : Finset (Fin n)).powersetCard (L - e),
        ((L + A.card - 1).choose e : ℝ) *
          ((s.factorial : ℝ) * (16 * Real.exp 1) ^ s * (d : ℝ) ^ (2 * e)) := by
      apply Finset.sum_le_sum
      intro H hH
      dsimp only
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [Finset.card_finsuppAntidiag_nat_eq_choose]
      apply Nat.cast_le.mpr
      apply Nat.choose_le_choose
      have hc := Finset.card_union_le A H
      have hh := (Finset.mem_powersetCard.mp hH).2
      omega
    _ = (n.choose (L - e) : ℝ) *
        (((L + A.card - 1).choose e : ℝ) *
          ((s.factorial : ℝ) * (16 * Real.exp 1) ^ s * (d : ℝ) ^ (2 * e))) := by
      simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ((n : ℝ) ^ (L - e) / (L - e).factorial) *
        (((L + A.card - 1).choose e : ℝ) *
          ((s.factorial : ℝ) * (16 * Real.exp 1) ^ s * (d : ℝ) ^ (2 * e))) :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div (L - e) n) (by positivity)
    _ = _ := by ring

/-- The counting bound (28), using padding in place of separate size patterns. -/
theorem weightedSlotCount_le_excess_sum (A : Finset (Fin n))
    (hs : s = 2 * L + A.card) (hslot : s ≤ 4 * d) :
    weightedSlotCount n s A ≤ (s.factorial : ℝ) * (16 * Real.exp 1) ^ s *
      ∑ e ∈ Finset.range (L + 1),
        (n : ℝ) ^ (L - e) / (L - e).factorial *
          ((L + A.card - 1).choose e : ℝ) * (d : ℝ) ^ (2 * e) :=
  (weightedSlotCount_le_code_sum A hs hslot).trans (coverCodes_sum_le A)

/-- Equation (30) for arbitrary slot number `s ≤ 4d`. -/
theorem weightedSlotCount_le_exp (A : Finset (Fin n)) (hn : 0 < n) (hA : A.Nonempty)
    (hs : s = 2 * L + A.card) (hslot : s ≤ 4 * d) :
    weightedSlotCount n s A ≤ (s.factorial : ℝ) * (16 * Real.exp 1) ^ s *
      ((n : ℝ) ^ L / L.factorial) * Real.exp (4 * (d : ℝ) ^ 4 / n) := by
  have hsum := excess_incidence_sum_le L A.card
    (by exact_mod_cast hn : (0 : ℝ) < n) (sq_nonneg (d : ℝ))
  simp only [← pow_mul] at hsum
  have hscale := incidence_excess_scale_le (Finset.card_pos.mpr hA)
    (hs ▸ hslot)
  have he : Real.exp ((L : ℝ) * (L + A.card - 1 : ℕ) * (d : ℝ) ^ 2 / n) ≤
      Real.exp (4 * (d : ℝ) ^ 4 / n) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hscale (Nat.cast_nonneg n))
  calc
    _ ≤ _ := weightedSlotCount_le_excess_sum A hs hslot
    _ ≤ (s.factorial : ℝ) * (16 * Real.exp 1) ^ s *
        ((n : ℝ) ^ L / L.factorial *
          Real.exp ((L : ℝ) * (L + A.card - 1 : ℕ) * (d : ℝ) ^ 2 / n)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left he (by positivity)

end

end TensorLB
