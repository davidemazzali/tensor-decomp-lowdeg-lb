module

public import Mathlib.Analysis.Analytic.Inverse
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Quantitative majorant for inverse power series

This exposes a dimension-independent version of the partial-sum induction in
Mathlib's analytic inverse theorem. A geometric bound on the forward series,
together with a norm bound on the inverse linear term, gives an explicit common
radius and a bound on the weighted coefficients of the inverse.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Topology NNReal ENNReal

noncomputable section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The scalar smallness conditions retain quantitative information that is
discarded by a qualitative positive-radius inverse theorem. -/
theorem inverse_majorant_partial_sum (p : FormalMultilinearSeries 𝕜 E F)
    (i : E ≃L[𝕜] F) (x : E) {r a : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a)
    (hi : ‖(i.symm : F →L[𝕜] E)‖ ≤ 1) (hp : ∀ n, ‖p n‖ ≤ r ^ n)
    (hra : 2 * r * a ≤ 1 / 2) (hrra : 8 * r ^ 2 * a ≤ 1) :
    ∀ n : ℕ, 1 ≤ n →
      (∑ j ∈ Finset.Ico 1 n, a ^ j * ‖p.rightInv i x j‖) ≤ 2 * a := by
  let S n := ∑ j ∈ Finset.Ico 1 n, a ^ j * ‖p.rightInv i x j‖
  have hS (n : ℕ) : 0 ≤ S n := Finset.sum_nonneg (fun _ _ => by positivity)
  change ∀ n, 1 ≤ n → S n ≤ 2 * a
  apply Nat.le_induction
  · simp only [S, Finset.Ico_self, Finset.sum_empty]
    positivity
  · intro n hn ih
    have hrS : r * S n ≤ 1 / 2 := by nlinarith
    have hrec := FormalMultilinearSeries.radius_rightInv_pos_of_radius_pos_aux2
      (x := x) (show 2 ≤ n + 1 by omega) p i hr ha (by norm_num : (0 : ℝ) ≤ 1)
      (fun n => by simpa only [one_mul] using hp n)
    change S (n + 1) ≤ ‖(i.symm : F →L[𝕜] E)‖ * a +
      ‖(i.symm : F →L[𝕜] E)‖ * 1 *
        ∑ j ∈ Finset.Ico 2 (n + 1), (r * S n) ^ j at hrec
    calc
      S (n + 1) ≤ _ := hrec
      _ ≤ a + ∑ j ∈ Finset.Ico 2 (n + 1), (r * S n) ^ j := by
        have hsum : 0 ≤ ∑ j ∈ Finset.Ico 2 (n + 1), (r * S n) ^ j :=
          Finset.sum_nonneg (fun _ _ => pow_nonneg (mul_nonneg hr (hS n)) _)
        nlinarith
      _ = a + ((r * S n) ^ 2 - (r * S n) ^ (n + 1)) / (1 - r * S n) := by
        rw [geom_sum_Ico' _ (show 2 ≤ n + 1 by omega)]
        exact ne_of_lt (hrS.trans_lt (by norm_num))
      _ ≤ a + (r * S n) ^ 2 / (1 / 2) := by
        gcongr
        · exact sub_le_self _ (pow_nonneg (mul_nonneg hr (hS n)) _)
        · linarith
      _ = a + 2 * (r * S n) ^ 2 := by ring
      _ ≤ a + 2 * (r * (2 * a)) ^ 2 := by gcongr
      _ = (1 + 8 * r ^ 2 * a) * a := by ring
      _ ≤ 2 * a := by nlinarith

theorem inverse_majorant_coefficient (p : FormalMultilinearSeries 𝕜 E F)
    (i : E ≃L[𝕜] F) (x : E) {r a : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a)
    (hi : ‖(i.symm : F →L[𝕜] E)‖ ≤ 1) (hp : ∀ n, ‖p n‖ ≤ r ^ n)
    (hra : 2 * r * a ≤ 1 / 2) (hrra : 8 * r ^ 2 * a ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) : a ^ n * ‖p.rightInv i x n‖ ≤ 2 * a := by
  calc
    _ ≤ ∑ j ∈ Finset.Ico 1 (n + 1), a ^ j * ‖p.rightInv i x j‖ :=
      Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_Ico.mpr ⟨hn, by omega⟩)
    _ ≤ _ := inverse_majorant_partial_sum p i x hr ha hi hp hra hrra (n + 1) (by omega)

def inverseMajorantRadius (r : ℝ) : ℝ := 1 / (16 * r ^ 2)

theorem inverseMajorantRadius_pos {r : ℝ} (hr : 1 ≤ r) : 0 < inverseMajorantRadius r := by
  unfold inverseMajorantRadius
  positivity

theorem inverseMajorantRadius_small {r : ℝ} (hr : 1 ≤ r) :
    2 * r * inverseMajorantRadius r ≤ 1 / 2 ∧
      8 * r ^ 2 * inverseMajorantRadius r ≤ 1 := by
  have hr0 : 0 < r := by linarith
  unfold inverseMajorantRadius
  constructor
  · rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith
  · rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg r]

theorem inverse_radius_ge (p : FormalMultilinearSeries 𝕜 E F)
    (i : E ≃L[𝕜] F) (x : E) {r : ℝ} (hr : 1 ≤ r)
    (hi : ‖(i.symm : F →L[𝕜] E)‖ ≤ 1) (hp : ∀ n, ‖p n‖ ≤ r ^ n) :
    ENNReal.ofReal (inverseMajorantRadius r) ≤ (p.rightInv i x).radius := by
  have ha := inverseMajorantRadius_pos hr
  obtain ⟨hra, hrra⟩ := inverseMajorantRadius_small hr
  let a : ℝ≥0 := ⟨inverseMajorantRadius r, ha.le⟩
  have he : ENNReal.ofReal (inverseMajorantRadius r) = (a : ℝ≥0∞) := by
    exact ENNReal.ofReal_eq_coe_nnreal ha.le
  rw [he]
  apply FormalMultilinearSeries.le_radius_of_eventually_le _ (2 * inverseMajorantRadius r)
  filter_upwards [Filter.Ici_mem_atTop 1] with n hn
  change ‖p.rightInv i x n‖ * inverseMajorantRadius r ^ n ≤ 2 * inverseMajorantRadius r
  rw [mul_comm]
  exact inverse_majorant_coefficient p i x (by linarith) ha.le hi hp hra hrra hn

theorem inverse_partialSum_norm_le (p : FormalMultilinearSeries 𝕜 E F)
    (i : E ≃L[𝕜] F) {r : ℝ} (hr : 1 ≤ r)
    (hi : ‖(i.symm : F →L[𝕜] E)‖ ≤ 1) (hp : ∀ n, ‖p n‖ ≤ r ^ n)
    (z : F) (hz : ‖z‖ ≤ inverseMajorantRadius r) (N : ℕ) :
    ‖(p.rightInv i 0).partialSum N z‖ ≤ 2 * ‖z‖ := by
  let a := inverseMajorantRadius r
  have ha : 0 < a := inverseMajorantRadius_pos hr
  obtain ⟨hra, hrra⟩ := inverseMajorantRadius_small hr
  have hratio : ‖z‖ / a ≤ 1 := (div_le_one ha).mpr hz
  have hsplit : (p.rightInv i 0).partialSum N z =
      ∑ j ∈ Finset.Ico 1 N, p.rightInv i 0 j (fun _ => z) := by
    unfold FormalMultilinearSeries.partialSum
    symm
    apply Finset.sum_subset
    · intro j hj
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
    · intro j hj hnot
      have hj0 : j = 0 := by
        simp only [Finset.mem_range, Finset.mem_Ico, not_and, not_lt] at hj hnot
        omega
      subst j
      simp
  rw [hsplit]
  by_cases hN : 1 ≤ N
  · calc
      _ ≤ ∑ j ∈ Finset.Ico 1 N, ‖p.rightInv i 0 j (fun _ => z)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.Ico 1 N, (‖z‖ / a) * (a ^ j * ‖p.rightInv i 0 j‖) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj1 := (Finset.mem_Ico.mp hj).1
        have hpow : ‖z‖ ^ j ≤ (‖z‖ / a) * a ^ j := by
          have h := pow_le_pow_of_le_one (div_nonneg (norm_nonneg _) ha.le) hratio hj1
          rw [pow_one, div_pow] at h
          exact (div_le_iff₀ (pow_pos ha j)).mp h
        calc
          _ ≤ ‖p.rightInv i 0 j‖ * ‖z‖ ^ j := by
            simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
              (p.rightInv i 0 j).le_opNorm (fun _ => z)
          _ ≤ ‖p.rightInv i 0 j‖ * ((‖z‖ / a) * a ^ j) :=
            mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
          _ = _ := by ring
      _ = (‖z‖ / a) * ∑ j ∈ Finset.Ico 1 N, a ^ j * ‖p.rightInv i 0 j‖ :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (‖z‖ / a) * (2 * a) := mul_le_mul_of_nonneg_left
        (inverse_majorant_partial_sum p i 0 (by linarith) ha.le hi hp hra hrra N hN)
        (div_nonneg (norm_nonneg _) ha.le)
      _ = _ := by field_simp
  · have hN0 : N = 0 := by omega
    simp only [hN0, Finset.Ico_eq_empty_of_le (by omega : 0 ≤ 1), Finset.sum_empty, norm_zero]
    positivity

/-- The inverse series obeys the same factor-two displacement bound as the
contraction argument in the manuscript. -/
theorem inverse_sum_norm_le [CompleteSpace E] (p : FormalMultilinearSeries 𝕜 E F)
    (i : E ≃L[𝕜] F) {r : ℝ} (hr : 1 ≤ r)
    (hi : ‖(i.symm : F →L[𝕜] E)‖ ≤ 1) (hp : ∀ n, ‖p n‖ ≤ r ^ n)
    (z : F) (hz : ‖z‖ < inverseMajorantRadius r) :
    ‖(p.rightInv i 0).sum z‖ ≤ 2 * ‖z‖ := by
  have ha := inverseMajorantRadius_pos hr
  have hball : z ∈ Metric.eball 0 (p.rightInv i 0).radius := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right]
    exact (ENNReal.ofReal_lt_ofReal_iff ha).mpr hz |>.trans_le (inverse_radius_ge p i 0 hr hi hp)
  have hlim := ((p.rightInv i 0).hasSum hball).tendsto_sum_nat.norm
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall (inverse_partialSum_norm_le p i hr hi hp z hz.le)

end

end TensorLB
