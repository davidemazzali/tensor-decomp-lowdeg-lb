module

public import TensorLB.LocalResponse
public import TensorLB.MultilinearPolynomial
public import TensorLB.TaylorTruncation

/-!
# The real analytic response germ

Restrict the complex response to real parameters and take its real part. The
complex inverse identity then gives the exact real germ identity used for
moment matching. The response is not assumed to have a uniform radius here.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Topology

noncomputable section

variable {n k : ℕ}

def complexifyParameters : (ObservationIndex n k → ℝ) →L[ℝ] ComplexParameters n k :=
  ContinuousLinearMap.pi (fun I => Complex.ofRealCLM.comp (ContinuousLinearMap.proj I))

@[simp] theorem complexifyParameters_apply (t : ObservationIndex n k → ℝ) (I : ObservationIndex n k) :
    complexifyParameters t I = (t I : ℂ) := rfl

def realResponse (τ : ℝ) (A : Finset (Fin n)) (q : ObservationIndex n k → ℝ) : ℝ :=
  (complexResponse τ A (complexifyParameters q)).re

theorem analyticAt_realResponse (τ : ℝ) (A : Finset (Fin n)) :
    AnalyticAt ℝ (realResponse (k := k) τ A) 0 := by
  have hc := (analyticAt_complexResponse (k := k) τ A).restrictScalars (𝕜 := ℝ)
  have hcp : AnalyticAt ℝ (fun q : ObservationIndex n k → ℝ =>
      complexResponse τ A (complexifyParameters q)) 0 := by
    apply hc.comp (f := complexifyParameters)
    exact complexifyParameters.analyticAt 0
  exact (Complex.reCLM.analyticAt _).comp hcp

@[simp] theorem realResponse_zero (τ : ℝ) (A : Finset (Fin n)) (hA : A.Nonempty) :
    realResponse (k := k) τ A 0 = 0 := by
  simp [realResponse, complexResponse_zero τ A hA]

theorem realResponse_comp_connected (τ : ℝ) (A : Finset (Fin n)) :
    ∀ᶠ t : ObservationIndex n k → ℝ in 𝓝 0,
      realResponse τ A (connectedCoordinate t) = tiltedMoment (fun I => τ * t I) A := by
  have hlim : Filter.Tendsto (complexifyParameters (n := n) (k := k)) (𝓝 0) (𝓝 0) :=
    complexifyParameters.continuous.tendsto' _ _ (map_zero _)
  have h := hlim.eventually (complexResponse_comp_connected (k := k) τ A)
  filter_upwards [h] with t ht
  have hK : complexConnected (complexifyParameters t) =
      complexifyParameters (connectedCoordinate t) := by
    funext I
    exact complexConnected_ofReal t I
  have hτ : (τ : ℂ) • complexifyParameters t = complexifyParameters (fun I => τ * t I) := by
    ext I
    simp
  rw [hK, hτ] at ht
  have hr := complexMoment_ofReal A (fun I => τ * t I)
  change complexMoment (complexifyParameters (fun I => τ * t I)) A = _ at hr
  rw [hr] at ht
  exact congrArg Complex.re ht

theorem analyticAt_partitionFunction (t : ObservationIndex n k → ℝ) :
    AnalyticAt ℝ partitionFunction t := by
  have hc := (analyticAt_complexPartition (complexifyParameters t)).restrictScalars (𝕜 := ℝ)
  have hcp := hc.comp (complexifyParameters.analyticAt t)
  have hr := (Complex.reCLM.analyticAt _).comp hcp
  convert! hr using 1
  funext x
  exact (congrArg Complex.re (complexPartition_ofReal x)).symm

theorem analyticAt_tiltedMoment (B : Finset (Fin n)) (t : ObservationIndex n k → ℝ) :
    AnalyticAt ℝ (fun t => tiltedMoment t B) t := by
  have hne : complexPartition (complexifyParameters t) ≠ 0 := by
    change complexPartition (fun I => (t I : ℂ)) ≠ 0
    rw [complexPartition_ofReal]
    exact Complex.ofReal_ne_zero.mpr (partitionFunction_pos t).ne'
  have hc : AnalyticAt ℂ (fun z : ComplexParameters n k => complexMoment z B)
      (complexifyParameters t) :=
    (analyticAt_complexNumerator B _).div (analyticAt_complexPartition _) hne
  have hcp := (hc.restrictScalars (𝕜 := ℝ)).comp (complexifyParameters.analyticAt t)
  have hr := (Complex.reCLM.analyticAt _).comp hcp
  convert! hr using 1
  funext x
  exact (congrArg Complex.re (complexMoment_ofReal B x)).symm

theorem analyticAt_connectedCoordinate (t : ObservationIndex n k → ℝ) :
    AnalyticAt ℝ connectedCoordinate t := by
  apply analyticAt_pi_iff.mpr
  intro I
  unfold connectedCoordinate
  split
  · apply AnalyticAt.add
    · apply (analyticAt_tiltedMoment I.val t).sub
      exact Finset.analyticAt_fun_sum _ (fun i _ =>
        (analyticAt_tiltedMoment {i} t).mul (analyticAt_tiltedMoment (I.val.erase i) t))
    · exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun i _ =>
        analyticAt_tiltedMoment {i} t))
  · split
    · apply (analyticAt_tiltedMoment I.val t).sub
      exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ (fun B _ =>
        (analyticAt_tiltedMoment B t).mul (analyticAt_tiltedMoment (I.val \ B) t)))
    · exact analyticAt_tiltedMoment I.val t

@[simp] theorem connectedCoordinate_zero : connectedCoordinate (n := n) (k := k) 0 = 0 := by
  funext I
  have h := congrArg Complex.re (complexConnected_ofReal (0 : ObservationIndex n k → ℝ) I)
  simpa only [Pi.zero_apply, Complex.ofReal_zero, ← Pi.zero_def, complexConnected_zero,
    Complex.zero_re, Complex.ofReal_re] using h.symm

/-- A chosen real Taylor expansion of the response germ. -/
def realResponseSeries (τ : ℝ) (A : Finset (Fin n)) :
    FormalMultilinearSeries ℝ (ObservationIndex n k → ℝ) ℝ :=
  Classical.choose (analyticAt_realResponse (k := k) τ A)

theorem hasFPowerSeriesAt_realResponse (τ : ℝ) (A : Finset (Fin n)) :
    HasFPowerSeriesAt (realResponse (k := k) τ A) (realResponseSeries τ A) 0 :=
  Classical.choose_spec (analyticAt_realResponse (k := k) τ A)

def responseTerm (τ : ℝ) (A : Finset (Fin n)) (d : ℕ) : ObservationPolynomial n k :=
  multilinearPolynomial (realResponseSeries τ A d)

theorem responseTerm_isHomogeneous (τ : ℝ) (A : Finset (Fin n)) (d : ℕ) :
    (responseTerm (k := k) τ A d).IsHomogeneous d := multilinearPolynomial_isHomogeneous _

theorem eval_responseTerm (τ : ℝ) (A : Finset (Fin n)) (d : ℕ) (q : ObservationIndex n k → ℝ) :
    MvPolynomial.eval q (responseTerm τ A d) = realResponseSeries τ A d (fun _ => q) :=
  eval_multilinearPolynomial _ _

theorem sum_eval_responseTerm (τ : ℝ) (A : Finset (Fin n)) (hA : A.Nonempty)
    (D : ℕ) (q : ObservationIndex n k → ℝ) :
    (∑ d ∈ Finset.range D, MvPolynomial.eval q (responseTerm τ A (d + 1))) =
      (realResponseSeries τ A).partialSum (D + 1) q := by
  simp only [eval_responseTerm, FormalMultilinearSeries.partialSum]
  rw [Finset.sum_range_succ']
  rw [(hasFPowerSeriesAt_realResponse τ A).coeff_zero, realResponse_zero τ A hA, add_zero]

end

end TensorLB
