module

public import TensorLB.LocalNorm
public import TensorLB.Polarization

/-!
# Incidence-scaled coefficient extraction

For a fixed tuple of observation indices, the reciprocal maximum incidence
scales its coordinate vectors into the local norm ball. Boolean polarization
then controls the factorial-normalized coefficient by incidence weights.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n k d : ℕ}

theorem incidenceCount_tupleIndex (t : Fin d → ObservationIndex n k) (i : Fin n) :
    incidenceCount (tupleIndex t) i = ∑ j, if i ∈ (t j).val then 1 else 0 := by
  unfold incidenceCount tupleIndex
  rw [← Finsupp.sum_finsetSum_index]
  · simp
  · intro I
    split_ifs <;> rfl
  · intro I a b
    split_ifs <;> simp

theorem incidenceCount_pos_of_mem (t : Fin d → ObservationIndex n k) (j : Fin d)
    {i : Fin n} (hi : i ∈ (t j).val) : 0 < incidenceCount (tupleIndex t) i := by
  rw [incidenceCount_tupleIndex]
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun l : Fin d => if i ∈ (t l).val then 1 else 0)
    (fun l _ => Nat.zero_le _) (Finset.mem_univ j)
  simpa only [ite_eq_left hi, Nat.succ_le_iff] using h

def maxIncidence (t : Fin d → ObservationIndex n k) (j : Fin d) : ℕ :=
  (t j).val.sup (incidenceCount (tupleIndex t))

theorem incidenceCount_le_maxIncidence (t : Fin d → ObservationIndex n k) (j : Fin d)
    {i : Fin n} (hi : i ∈ (t j).val) :
    incidenceCount (tupleIndex t) i ≤ maxIncidence t j := Finset.le_sup hi

theorem maxIncidence_pos (t : Fin d → ObservationIndex n k) (j : Fin d) :
    0 < maxIncidence t j := by
  obtain ⟨i, hi⟩ := (t j).property.1
  exact (incidenceCount_pos_of_mem t j hi).trans_le (incidenceCount_le_maxIncidence t j hi)

theorem incidentNorm_sum_le {α : Type*} (s : Finset α) (v : α → ComplexParameters n k)
    (i : Fin n) : incidentNorm (∑ a ∈ s, v a) i ≤ ∑ a ∈ s, incidentNorm (v a) i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (incidentNorm_add_le _ _ i).trans (add_le_add (le_refl _) ih)

theorem incidentNorm_single (I : ObservationIndex n k) (c : ℂ) (i : Fin n) :
    incidentNorm (Pi.single I c) i = if i ∈ I.val then ‖c‖ else 0 := by
  unfold incidentNorm
  rw [Finset.sum_eq_single I]
  · simp
  · intro J _ hJI
    simp [Ne.symm hJI]
  · simp

/-- Every signed corner used by polarization lies in the local ball. -/
theorem localNorm_scaled_corner_le (t : Fin d → ObservationIndex n k)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (ε : Fin d → Bool) :
    localNorm (complexifyParameters
      (∑ j, (sign (ε j) * (ρ / maxIncidence t j)) • Pi.single (t j) 1)) ≤ ρ := by
  apply (localNorm_le_iff _ hρ).mpr
  intro i
  have hv (j : Fin d) : complexifyParameters
      ((sign (ε j) * (ρ / maxIncidence t j)) • Pi.single (t j) 1) =
      Pi.single (t j) ((sign (ε j) * (ρ / maxIncidence t j) : ℝ) : ℂ) := by
    ext I
    by_cases hI : I = t j <;> simp [hI]
  have hn (j : Fin d) :
      ‖((sign (ε j) * (ρ / maxIncidence t j) : ℝ) : ℂ)‖ = ρ / maxIncidence t j := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (div_nonneg hρ (Nat.cast_nonneg _))]
    cases ε j <;> simp [sign]
  rw [map_sum]
  calc
    _ ≤ ∑ j, incidentNorm (complexifyParameters
        ((sign (ε j) * (ρ / maxIncidence t j)) • Pi.single (t j) 1)) i :=
      incidentNorm_sum_le _ _ i
    _ = ∑ j, if i ∈ (t j).val then ρ / maxIncidence t j else 0 := by
      simp only [hv, incidentNorm_single, hn]
    _ ≤ ∑ j : Fin d, if i ∈ (t j).val then
        ρ / incidenceCount (tupleIndex t) i else 0 := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hi
      · exact div_le_div_of_nonneg_left hρ
          (by exact_mod_cast incidenceCount_pos_of_mem t j hi)
          (by exact_mod_cast incidenceCount_le_maxIncidence t j hi)
      · rfl
    _ = (incidenceCount (tupleIndex t) i : ℝ) *
        (ρ / incidenceCount (tupleIndex t) i) := by
      rw [incidenceCount_tupleIndex, Nat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    _ ≤ ρ := by
      by_cases hi : incidenceCount (tupleIndex t) i = 0
      · simpa only [hi, Nat.cast_zero, zero_mul] using hρ
      · have hi' : (incidenceCount (tupleIndex t) i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hi
        exact le_of_eq (by field_simp)

/-- A homogeneous diagonal bound gives the first coefficient bound in (24). -/
theorem normalized_coefficient_le_maxIncidence (p : ObservationPolynomial n k)
    (hp : p.IsHomogeneous d) (t : Fin d → ObservationIndex n k) {ρ : ℝ} (hρ : 0 < ρ)
    (hb : ∀ x : ObservationIndex n k → ℝ, localNorm (complexifyParameters x) ≤ ρ →
      |MvPolynomial.eval x p| ≤ 1) :
    |p.coeff (tupleIndex t) * ((tupleIndex t).prod (fun _ r => r.factorial) : ℝ)| ≤
      ρ⁻¹ ^ d * ∏ j, (maxIncidence t j : ℝ) := by
  have h := abs_normalized_coefficient_mul_prod_le p hp t
    (fun j => ρ / maxIncidence t j) (fun ε => hb _ (by
      convert! localNorm_scaled_corner_le t hρ.le ε))
  have hm : 0 < ∏ j, (maxIncidence t j : ℝ) :=
    Finset.prod_pos (fun j _ => by exact_mod_cast maxIncidence_pos t j)
  have he : (∏ j, ρ / (maxIncidence t j : ℝ)) = ρ ^ d / ∏ j, (maxIncidence t j : ℝ) := by
    rw [Finset.prod_div_distrib]
    simp
  rw [abs_mul, he, abs_of_pos (div_pos (pow_pos hρ d) hm)] at h
  rw [inv_pow]
  have h' : |p.coeff (tupleIndex t) * ((tupleIndex t).prod (fun _ r => r.factorial) : ℝ)| *
      ρ ^ d ≤ ∏ j, (maxIncidence t j : ℝ) := by
    rw [← mul_div_assoc] at h
    simpa only [one_mul] using (div_le_iff₀ hm).mp h
  simpa only [div_eq_mul_inv, mul_comm] using (le_div_iff₀ (pow_pos hρ d)).mpr h'

theorem prod_maxIncidence_le (t : Fin d → ObservationIndex n k) :
    (∏ j, maxIncidence t j) ≤
      ∏ i : Fin n, incidenceCount (tupleIndex t) i ^ incidenceCount (tupleIndex t) i := by
  calc
    _ ≤ ∏ j, ∏ i ∈ (t j).val, incidenceCount (tupleIndex t) i := by
      apply Finset.prod_le_prod
      intro j _
      apply Finset.sup_le
      intro i hi
      exact Finset.single_le_prod
        (fun l hl => incidenceCount_pos_of_mem t j hl) hi
    _ = ∏ j : Fin d, ∏ i : Fin n,
        if i ∈ (t j).val then incidenceCount (tupleIndex t) i else 1 := by
      apply Finset.prod_congr rfl
      intro j _
      exact (Finset.prod_ite_mem_eq (t j).val _).symm
    _ = ∏ i : Fin n, ∏ j : Fin d,
        if i ∈ (t j).val then incidenceCount (tupleIndex t) i else 1 := Finset.prod_comm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      conv_rhs => arg 2; rw [incidenceCount_tupleIndex]
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro j _
      split_ifs <;> simp

/-- Equation (24) follows from a bound on homogeneous diagonals in the local ball. -/
theorem normalized_coefficient_le_incidence (p : ObservationPolynomial n k)
    (hp : p.IsHomogeneous d) (t : Fin d → ObservationIndex n k) {ρ : ℝ} (hρ : 0 < ρ)
    (hb : ∀ x : ObservationIndex n k → ℝ, localNorm (complexifyParameters x) ≤ ρ →
      |MvPolynomial.eval x p| ≤ 1) :
    |p.coeff (tupleIndex t) * ((tupleIndex t).prod (fun _ r => r.factorial) : ℝ)| ≤
      ρ⁻¹ ^ d * ∏ i : Fin n,
        (incidenceCount (tupleIndex t) i : ℝ) ^ incidenceCount (tupleIndex t) i := by
  apply (normalized_coefficient_le_maxIncidence p hp t hρ hb).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast prod_maxIncidence_le t

end

end TensorLB
