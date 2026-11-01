module

public import TensorLB.SlotCounting
public import TensorLB.CoefficientArithmetic

/-!
# Encoding even covers by support and excess multiplicity

Target coordinates have multiplicity `1 + 2 b`; other occurring coordinates
have multiplicity `2 + 2 b`. Their excess counts and their non-target support
determine the full multiplicity vector.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n : ℕ}

def nonrootSupport (R : Fin n →₀ ℕ) (A : Finset (Fin n)) : Finset (Fin n) := R.support \ A

def excessMultiplicity (R : Fin n →₀ ℕ) (A : Finset (Fin n)) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (R i - if i ∈ A then 1 else 2) / 2)

theorem excessMultiplicity_apply (R : Fin n →₀ ℕ) (A : Finset (Fin n)) (i : Fin n) :
    excessMultiplicity R A i = (R i - if i ∈ A then 1 else 2) / 2 := rfl

theorem coordinateParity_mem {R : Fin n →₀ ℕ} {A : Finset (Fin n)}
    (hR : coordinateParity R = A) (i : Fin n) : i ∈ A ↔ R i % 2 = 1 := by
  rw [← hR]
  simp only [coordinateParity, Finset.mem_filter, Finset.mem_univ, true_and]

theorem multiplicity_reconstruction {R : Fin n →₀ ℕ} {A : Finset (Fin n)}
    (hR : coordinateParity R = A) (i : Fin n) :
    R i = (if i ∈ A then 1 else 0) +
      2 * (if i ∈ nonrootSupport R A then 1 else 0) + 2 * excessMultiplicity R A i := by
  have hp := coordinateParity_mem hR i
  by_cases hiA : i ∈ A
  · have hmod := hp.mp hiA
    simp only [nonrootSupport, Finset.mem_sdiff, Finsupp.mem_support_iff,
      excessMultiplicity_apply, hiA, not_true_eq_false, and_false, ite_true, ite_false,
      mul_zero, add_zero]
    omega
  · have hmod : R i % 2 = 0 := by
      have hn := mt hp.mpr hiA
      omega
    by_cases hRi : R i = 0
    · simp [nonrootSupport, excessMultiplicity_apply, hiA, hRi]
    · have hiH : i ∈ nonrootSupport R A :=
        Finset.mem_sdiff.mpr ⟨Finsupp.mem_support_iff.mpr hRi, hiA⟩
      simp only [excessMultiplicity_apply, ite_eq_right hiA, ite_eq_left hiH, mul_one, zero_add]
      omega

theorem excessMultiplicity_support {R : Fin n →₀ ℕ} (A : Finset (Fin n)) :
    (excessMultiplicity R A).support ⊆ A ∪ nonrootSupport R A := by
  intro i hi
  have hne : excessMultiplicity R A i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hRi : R i ≠ 0 := by
    intro hz
    simp only [excessMultiplicity_apply, hz, Nat.zero_sub, Nat.zero_div] at hne
    exact hne rfl
  by_cases hiA : i ∈ A
  · exact Finset.mem_union_left _ hiA
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finsupp.mem_support_iff.mpr hRi, hiA⟩)

theorem multiplicity_degree_reconstruction {R : Fin n →₀ ℕ} {A : Finset (Fin n)}
    (hR : coordinateParity R = A) :
    R.sum (fun _ r => r) = A.card + 2 * (nonrootSupport R A).card +
      2 * (excessMultiplicity R A).sum (fun _ r => r) := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp_rw [multiplicity_reconstruction hR]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp

theorem excessMultiplicity_degree {R : Fin n →₀ ℕ} {A : Finset (Fin n)} {L : ℕ}
    (hR : coordinateParity R = A) (hs : R.sum (fun _ r => r) = 2 * L + A.card) :
    (nonrootSupport R A).card + (excessMultiplicity R A).sum (fun _ r => r) = L := by
  have h := multiplicity_degree_reconstruction hR
  omega

theorem multiplicity_encoding_injective (A : Finset (Fin n)) :
    Set.InjOn (fun R : Fin n →₀ ℕ => (nonrootSupport R A, excessMultiplicity R A))
      {R | coordinateParity R = A} := by
  intro R hR S hS h
  obtain ⟨hh, he⟩ := Prod.mk.inj h
  ext i
  rw [multiplicity_reconstruction hR, multiplicity_reconstruction hS, hh, he]

/-- Weighted multinomial counts factor coordinate by coordinate. -/
theorem multinomial_mul_coordinateWeight {R : Fin n →₀ ℕ} {s : ℕ}
    (hs : R.sum (fun _ r => r) = s) :
    (R.multinomial : ℝ) * coordinateWeight R =
      (s.factorial : ℝ) * ∏ i : Fin n, (R i : ℝ) ^ (2 * R i) / (R i).factorial := by
  have hfac : ((∏ i : Fin n, (R i).factorial : ℕ) : ℝ) * R.multinomial = s.factorial := by
    have h := factorial_mul_multinomial R
    rw [hs] at h
    have hp : R.prod (fun _ r => r.factorial) = ∏ i : Fin n, (R i).factorial :=
      Finsupp.prod_fintype _ _ (fun _ => rfl)
    rw [hp] at h
    exact_mod_cast h
  have hpos : (0 : ℝ) < ∏ i : Fin n, ((R i).factorial : ℝ) :=
    Finset.prod_pos (fun i _ => by positivity)
  push_cast at hfac
  rw [Finset.prod_div_distrib, ← hfac]
  unfold coordinateWeight
  field_simp

/-- The fixed-multiplicity bound in equation (28). -/
theorem multinomial_weight_le {R : Fin n →₀ ℕ} {A : Finset (Fin n)} {s d : ℕ}
    (hR : coordinateParity R = A) (hs : R.sum (fun _ r => r) = s) (hslot : s ≤ 4 * d) :
    (R.multinomial : ℝ) * coordinateWeight R ≤
      (s.factorial : ℝ) * (16 * Real.exp 1) ^ s *
        (d : ℝ) ^ (2 * (excessMultiplicity R A).sum (fun _ r => r)) := by
  rw [multinomial_mul_coordinateWeight hs]
  have hfactor (i : Fin n) : (R i : ℝ) ^ (2 * R i) / (R i).factorial ≤
      (16 * Real.exp 1) ^ (R i) * (d : ℝ) ^ (2 * excessMultiplicity R A i) := by
    by_cases hi : R i = 0
    · simp [hi, excessMultiplicity_apply]
    · have hle : R i ≤ 4 * d := by
        calc
          R i ≤ ∑ j : Fin n, R j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          _ = s := by
            rw [← Finsupp.sum_fintype R (fun _ r => r) (fun _ => rfl)]
            exact hs
          _ ≤ _ := hslot
      have he := multiplicity_reconstruction hR i
      by_cases hiA : i ∈ A
      · have hiH : i ∉ nonrootSupport R A := by simp [nonrootSupport, hiA]
        simp only [hiA, hiH, ite_true, ite_false, mul_zero, add_zero] at he
        exact incidence_factorial_weight_le (by omega) (by omega) he hle
      · have hiH : i ∈ nonrootSupport R A := by simp [nonrootSupport, hiA, hi]
        simp only [hiA, hiH, ite_true, ite_false, mul_one, zero_add] at he
        exact incidence_factorial_weight_le (by omega) (by omega) he hle
  calc
    _ ≤ (s.factorial : ℝ) * ∏ i : Fin n,
        (16 * Real.exp 1) ^ (R i) * (d : ℝ) ^ (2 * excessMultiplicity R A i) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => hfactor i)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
        ← Finset.mul_sum, ← Finsupp.sum_fintype R (fun _ r => r) (fun _ => rfl), hs,
        ← Finsupp.sum_fintype (excessMultiplicity R A) (fun _ r => r) (fun _ => rfl)]
      ring

end

end TensorLB
