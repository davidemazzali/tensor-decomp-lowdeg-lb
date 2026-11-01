module

public import TensorLB.InverseMajorant
public import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Analytic extensions from geometric Taylor bounds

A geometric bound on multilinear coefficients controls both the convergence
radius and the displacement of the sum. These estimates use the norm on the
parameter space and have no dimension factor.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Topology NNReal ENNReal

noncomputable section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem geometric_series_radius_ge (p : FormalMultilinearSeries 𝕜 E F)
    {r : ℝ} (hr : 0 < r) (hp : ∀ d, ‖p d‖ ≤ r ^ d) :
    ENNReal.ofReal r⁻¹ ≤ p.radius := by
  let a : ℝ≥0 := ⟨r⁻¹, inv_nonneg.mpr hr.le⟩
  rw [show ENNReal.ofReal r⁻¹ = (a : ℝ≥0∞) from
    ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr hr.le)]
  apply p.le_radius_of_bound 1
  intro d
  change ‖p d‖ * r⁻¹ ^ d ≤ 1
  calc
    _ ≤ r ^ d * r⁻¹ ^ d := mul_le_mul_of_nonneg_right (hp d) (by positivity)
    _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hr.ne', one_pow]

theorem geometric_series_mem_ball (p : FormalMultilinearSeries 𝕜 E F)
    {r : ℝ} (hr : 0 < r) (hp : ∀ d, ‖p d‖ ≤ r ^ d)
    (z : E) (hz : r * ‖z‖ < 1) : z ∈ Metric.eball 0 p.radius := by
  rw [Metric.mem_eball, edist_dist, dist_zero_right]
  apply lt_of_lt_of_le _ (geometric_series_radius_ge p hr hp)
  rw [ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hr)]
  rw [inv_eq_one_div, lt_div_iff₀ hr]
  simpa only [mul_comm] using hz

theorem geometric_partialSum_norm_le (p : FormalMultilinearSeries 𝕜 E F)
    (hp0 : p 0 = 0) {r : ℝ} (hr : 0 ≤ r) (hp : ∀ d, ‖p d‖ ≤ r ^ d)
    (z : E) (hz : r * ‖z‖ ≤ 1 / 2) (N : ℕ) :
    ‖p.partialSum N z‖ ≤ 2 * r * ‖z‖ := by
  have hs : p.partialSum N z = ∑ j ∈ Finset.Ico 1 N, p j (fun _ => z) := by
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
      simp [hp0]
  rw [hs]
  by_cases hN : 1 ≤ N
  · calc
      _ ≤ ∑ j ∈ Finset.Ico 1 N, ‖p j (fun _ => z)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.Ico 1 N, (r * ‖z‖) ^ j := by
        apply Finset.sum_le_sum
        intro j _
        calc
          _ ≤ ‖p j‖ * ‖z‖ ^ j := by
            simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
              (p j).le_opNorm (fun _ => z)
          _ ≤ r ^ j * ‖z‖ ^ j := mul_le_mul_of_nonneg_right (hp j) (by positivity)
          _ = _ := (mul_pow _ _ _).symm
      _ = (r * ‖z‖ - (r * ‖z‖) ^ N) / (1 - r * ‖z‖) := by
        rw [geom_sum_Ico' (by linarith : r * ‖z‖ ≠ 1) hN, pow_one]
      _ ≤ (r * ‖z‖) / (1 / 2) := by
        gcongr
        · exact sub_le_self _ (pow_nonneg (mul_nonneg hr (norm_nonneg _)) _)
        · linarith
      _ = _ := by ring
  · have hN0 : N = 0 := by omega
    simp only [hN0, Finset.Ico_eq_empty_of_le (by omega : 0 ≤ 1), Finset.sum_empty, norm_zero]
    positivity

theorem geometric_sum_norm_le [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F)
    (hp0 : p 0 = 0) {r : ℝ} (hr : 0 < r) (hp : ∀ d, ‖p d‖ ≤ r ^ d)
    (z : E) (hz : r * ‖z‖ ≤ 1 / 2) : ‖p.sum z‖ ≤ 2 * r * ‖z‖ := by
  have hz' : r * ‖z‖ < 1 := by linarith
  have hlim := (p.hasSum (geometric_series_mem_ball p hr hp z hz')).tendsto_sum_nat.norm
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall (geometric_partialSum_norm_le p hp0 hr.le hp z hz)

theorem powerSeries_sum_germ {f : E → F} {p : FormalMultilinearSeries 𝕜 E F}
    (hf : HasFPowerSeriesAt f p 0) : p.sum =ᶠ[𝓝 0] f := by
  filter_upwards [hf.eventually_hasSum] with z hz
  simpa only [FormalMultilinearSeries.sum, zero_add] using hz.tsum_eq

theorem analyticAt_geometric_sum [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F)
    {r : ℝ} (hr : 0 < r) (hp : ∀ d, ‖p d‖ ≤ r ^ d)
    (z : E) (hz : r * ‖z‖ < 1) : AnalyticAt 𝕜 p.sum z := by
  have hrad : 0 < p.radius :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr hr)).trans_le (geometric_series_radius_ge p hr hp)
  exact (p.hasFPowerSeriesOnBall hrad).analyticAt_of_mem
    (geometric_series_mem_ball p hr hp z hz)

theorem analyticAt_inverse_sum [CompleteSpace E] (p : FormalMultilinearSeries 𝕜 E F)
    (i : E ≃L[𝕜] F) {r : ℝ} (hr : 1 ≤ r)
    (hi : ‖(i.symm : F →L[𝕜] E)‖ ≤ 1) (hp : ∀ d, ‖p d‖ ≤ r ^ d)
    (z : F) (hz : ‖z‖ < inverseMajorantRadius r) :
    AnalyticAt 𝕜 (p.rightInv i 0).sum z := by
  have ha := inverseMajorantRadius_pos hr
  have hrad := inverse_radius_ge p i 0 hr hi hp
  apply ((p.rightInv i 0).hasFPowerSeriesOnBall
    ((ENNReal.ofReal_pos.mpr ha).trans_le hrad)).analyticAt_of_mem
  rw [Metric.mem_eball, edist_dist, dist_zero_right]
  exact ((ENNReal.ofReal_lt_ofReal_iff ha).mpr hz).trans_le hrad

end

end TensorLB
