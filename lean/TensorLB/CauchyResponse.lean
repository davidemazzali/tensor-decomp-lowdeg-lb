module

public import TensorLB.CoefficientGeometry
public import Mathlib.Analysis.Complex.Liouville

/-!
# Cauchy bounds for the response coefficients

One-variable Cauchy estimates bound homogeneous diagonals on the local ball.
The incidence-scaled polarization identity then yields the coefficient bound.
An analytic extension need only agree with the inverse-defined response near
zero; no behavior of the chosen local inverse away from its domain is assumed.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem complex_iteratedDeriv_along_line {f : E → ℂ} {p : FormalMultilinearSeries ℂ E ℂ}
    (hf : HasFPowerSeriesAt f p 0) (x : E) (d : ℕ) :
    iteratedDeriv d (fun s : ℂ => f (s • x)) 0 =
      (d.factorial : ℂ) * p d (fun _ => x) := by
  let u : ℂ →L[ℂ] E := ContinuousLinearMap.toSpanSingleton ℂ x
  have hfu : HasFPowerSeriesAt f p (u 0) := by simpa only [map_zero] using hf
  obtain ⟨r, hr⟩ := hfu.compContinuousLinearMap
  have hh := hr.factorial_smul (1 : ℂ) d
  simpa only [← iteratedDeriv_eq_iteratedFDeriv, Function.comp_def, u,
    ContinuousLinearMap.toSpanSingleton_apply, FormalMultilinearSeries.compContinuousLinearMap,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, one_smul, nsmul_eq_mul] using hh.symm

theorem norm_taylor_diagonal_le {f : E → ℂ} {p : FormalMultilinearSeries ℂ E ℂ}
    (hf : HasFPowerSeriesAt f p 0) (x : E) (d : ℕ) {C : ℝ}
    (ha : DiffContOnCl ℂ (fun s : ℂ => f (s • x)) (Metric.ball 0 1))
    (hb : ∀ s : ℂ, ‖s‖ = 1 → ‖f (s • x)‖ ≤ C) :
    ‖p d (fun _ => x)‖ ≤ C := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le d
    (by norm_num : (0 : ℝ) < 1) ha (by simpa [Metric.mem_sphere, dist_zero_right] using hb)
  rw [complex_iteratedDeriv_along_line hf, norm_mul, Complex.norm_natCast] at h
  simp only [one_pow, div_one] at h
  exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < d.factorial)).mp h

variable {n k d : ℕ}

def realPartSeries (p : FormalMultilinearSeries ℂ (ComplexParameters n k) ℂ) :
    FormalMultilinearSeries ℝ (ObservationIndex n k → ℝ) ℝ :=
  Complex.reCLM.compFormalMultilinearSeries
    ((p.restrictScalars ℝ).compContinuousLinearMap complexifyParameters)

theorem hasFPowerSeriesAt_realPart {f : ComplexParameters n k → ℂ}
    {p : FormalMultilinearSeries ℂ (ComplexParameters n k) ℂ}
    (hf : HasFPowerSeriesAt f p 0) :
    HasFPowerSeriesAt (fun x => (f (complexifyParameters x)).re) (realPartSeries p) 0 := by
  have h0 : HasFPowerSeriesAt f (p.restrictScalars ℝ)
      (complexifyParameters (0 : ObservationIndex n k → ℝ)) := by
    simpa only [map_zero] using hf.restrictScalars (𝕜 := ℝ)
  obtain ⟨r, hr⟩ := h0.compContinuousLinearMap
  exact ⟨r, Complex.reCLM.comp_hasFPowerSeriesOnBall hr⟩

theorem realPartSeries_apply (p : FormalMultilinearSeries ℂ (ComplexParameters n k) ℂ)
    (x : ObservationIndex n k → ℝ) (d : ℕ) :
    realPartSeries p d (fun _ => x) = (p d (fun _ => complexifyParameters x)).re := rfl

theorem eval_responseTerm_eq_realPart {f : ComplexParameters n k → ℂ}
    {p : FormalMultilinearSeries ℂ (ComplexParameters n k) ℂ}
    (hf : HasFPowerSeriesAt f p 0) (τ : ℝ) (A : Finset (Fin n))
    (he : f =ᶠ[𝓝 0] complexResponse τ A) (x : ObservationIndex n k → ℝ) (d : ℕ) :
    MvPolynomial.eval x (responseTerm τ A d) = (p d (fun _ => complexifyParameters x)).re := by
  have hlim : Filter.Tendsto (complexifyParameters (n := n) (k := k)) (𝓝 0) (𝓝 0) :=
    complexifyParameters.continuous.tendsto' _ _ (map_zero _)
  have he' : (fun x => (f (complexifyParameters x)).re) =ᶠ[𝓝 0] realResponse τ A := by
    filter_upwards [hlim.eventually he] with x hx
    exact congrArg Complex.re hx
  have hr := (hasFPowerSeriesAt_realPart hf).congr he'
  have h1 := iteratedDeriv_along_line hr x d
  have h2 := iteratedDeriv_along_line (hasFPowerSeriesAt_realResponse τ A) x d
  rw [eval_responseTerm, ← realPartSeries_apply]
  apply mul_left_cancel₀ (show (d.factorial : ℝ) ≠ 0 by positivity)
  exact h2.symm.trans h1

/-- An extension on a closed local ball supplies every homogeneous diagonal
bound used by coefficient extraction. -/
theorem responseTerm_diagonal_bound {f : ComplexParameters n k → ℂ}
    (τ : ℝ) (A : Finset (Fin n)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (ha : AnalyticOnNhd ℂ f {x | localNorm x ≤ ρ})
    (hb : ∀ x, localNorm x ≤ ρ → ‖f x‖ ≤ 1)
    (he : f =ᶠ[𝓝 0] complexResponse τ A)
    (x : ObservationIndex n k → ℝ) (hx : localNorm (complexifyParameters x) ≤ ρ) (d : ℕ) :
    |MvPolynomial.eval x (responseTerm τ A d)| ≤ 1 := by
  obtain ⟨p, hp⟩ := ha 0 (by simpa only [Set.mem_ofPred_eq, localNorm_zero] using hρ)
  rw [eval_responseTerm_eq_realPart hp τ A he]
  apply (Complex.abs_re_le_norm _).trans
  apply norm_taylor_diagonal_le hp (complexifyParameters x) d
  · apply DifferentiableOn.diffContOnCl
    intro s hs
    have hs' : ‖s‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        (Metric.closure_ball_subset_closedBall hs)
    have hsl : localNorm (s • complexifyParameters x) ≤ ρ := by
      rw [localNorm_smul]
      exact (mul_le_mul_of_nonneg_right hs' (localNorm_nonneg _)).trans (by simpa using hx)
    exact ((ha _ hsl).differentiableAt.comp s
      ((ContinuousLinearMap.toSpanSingleton ℂ (complexifyParameters x)).differentiableAt)).differentiableWithinAt
  · intro s hs
    apply hb
    simpa only [localNorm_smul, hs, one_mul] using hx

/-- The analytic part of equation (24), for the actual response coefficients. -/
theorem responseTerm_normalized_coefficient_bound {f : ComplexParameters n k → ℂ}
    (τ : ℝ) (A : Finset (Fin n)) {ρ : ℝ} (hρ : 0 < ρ)
    (ha : AnalyticOnNhd ℂ f {x | localNorm x ≤ ρ})
    (hb : ∀ x, localNorm x ≤ ρ → ‖f x‖ ≤ 1)
    (he : f =ᶠ[𝓝 0] complexResponse τ A) (t : Fin d → ObservationIndex n k) :
    |(responseTerm τ A d).coeff (tupleIndex t) *
      ((tupleIndex t).prod (fun _ r => r.factorial) : ℝ)| ≤
      ρ⁻¹ ^ d * ∏ i : Fin n,
        (incidenceCount (tupleIndex t) i : ℝ) ^ incidenceCount (tupleIndex t) i := by
  apply normalized_coefficient_le_incidence _ (responseTerm_isHomogeneous τ A d) t hρ
  intro x hx
  exact responseTerm_diagonal_bound τ A hρ.le ha hb he x hx d

end

end TensorLB
