module

public import TensorLB.ComplexConnected
public import Mathlib.Analysis.Analytic.Inverse
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Local analytic response

The inverse function theorem constructs the response germ for every finite
dimension. The radius and coefficient estimates needed by the main theorem
require additional uniform bounds; they are not inferred from local existence.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped Topology

noncomputable section

variable {n k : ℕ}

theorem hasStrictFDerivAt_complexConnected :
    HasStrictFDerivAt (complexConnected (n := n) (k := k))
      (ContinuousLinearMap.id ℂ (ComplexParameters n k)) 0 := by
  have h := (analyticAt_complexConnected (n := n) (k := k)).hasStrictFDerivAt
  rwa [hasFDerivAt_complexConnected.fderiv] at h

/-- A total function representing the unique local inverse germ at zero. -/
def complexInverse : ComplexParameters n k → ComplexParameters n k :=
  hasStrictFDerivAt_complexConnected.localInverse complexConnected
    (ContinuousLinearEquiv.refl ℂ (ComplexParameters n k)) 0

theorem complexInverse_left :
    ∀ᶠ t : ComplexParameters n k in 𝓝 0, complexInverse (complexConnected t) = t :=
  hasStrictFDerivAt_complexConnected.eventually_left_inverse

@[simp] theorem complexInverse_zero : complexInverse (n := n) (k := k) 0 = 0 := by
  simpa only [complexConnected_zero, complexInverse] using
    (complexInverse_left (n := n) (k := k)).self_of_nhds

theorem complexInverse_right :
    ∀ᶠ q : ComplexParameters n k in 𝓝 0, complexConnected (complexInverse q) = q := by
  simpa only [complexConnected_zero, complexInverse] using
    (hasStrictFDerivAt_complexConnected (n := n) (k := k)).eventually_right_inverse
      (f' := ContinuousLinearEquiv.refl ℂ (ComplexParameters n k))

theorem analyticAt_complexInverse :
    AnalyticAt ℂ (complexInverse (n := n) (k := k)) 0 := by
  let i := ContinuousLinearEquiv.refl ℂ (ComplexParameters n k)
  let R := (hasStrictFDerivAt_complexConnected (n := n) (k := k)).toOpenPartialHomeomorph
    complexConnected (f' := i)
  have h0 : (0 : ComplexParameters n k) ∈ R.source :=
    HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  obtain ⟨p, hp⟩ := analyticAt_complexConnected (n := n) (k := k)
  have hp1 : p 1 = (continuousMultilinearCurryFin1 ℂ (ComplexParameters n k)
      (ComplexParameters n k)).symm (i : ComplexParameters n k →L[ℂ] ComplexParameters n k) := by
    apply (continuousMultilinearCurryFin1 ℂ (ComplexParameters n k)
      (ComplexParameters n k)).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact hp.hasFDerivAt.unique hasFDerivAt_complexConnected
  have hinv := (R.hasFPowerSeriesAt_symm h0 hp hp1).analyticAt
  change AnalyticAt ℂ complexInverse (complexConnected (0 : ComplexParameters n k)) at hinv
  simpa only [complexConnected_zero] using hinv

/-- Equation (12), initially as an analytic germ. -/
def complexResponse (τ : ℝ) (A : Finset (Fin n)) (q : ComplexParameters n k) : ℂ :=
  complexMoment ((τ : ℂ) • complexInverse q) A

theorem analyticAt_complexResponse (τ : ℝ) (A : Finset (Fin n)) :
    AnalyticAt ℂ (complexResponse (k := k) τ A) 0 := by
  have hscale := (analyticAt_complexInverse (n := n) (k := k)).const_smul (c := (τ : ℂ))
  have hm := analyticAt_complexMoment_zero (n := n) (k := k) A
  have hzero : (τ : ℂ) • complexInverse (n := n) (k := k) 0 = 0 := by simp
  rw [← hzero] at hm
  exact hm.comp (f := fun q : ComplexParameters n k => (τ : ℂ) • complexInverse q) hscale

theorem complexResponse_zero (τ : ℝ) (A : Finset (Fin n)) (hA : A.Nonempty) :
    complexResponse (k := k) τ A 0 = 0 := by
  simp [complexResponse, complexMoment_zero_of_nonempty A hA]

/-- Exact germ identity underlying the truncated response's moment matching. -/
theorem complexResponse_comp_connected (τ : ℝ) (A : Finset (Fin n)) :
    ∀ᶠ t : ComplexParameters n k in 𝓝 0,
      complexResponse τ A (complexConnected t) = complexMoment ((τ : ℂ) • t) A := by
  filter_upwards [complexInverse_left (n := n) (k := k)] with t ht
  simp only [complexResponse, ht]

end

end TensorLB
