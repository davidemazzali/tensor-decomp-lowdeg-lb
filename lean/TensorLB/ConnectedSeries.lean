module

public import TensorLB.LocalNorm
public import TensorLB.LocalResponse
public import TensorLB.SeriesMajorant

/-!
# Connected-coordinate series in the local norm

Transporting the connected map to the incident-weight norm preserves its
analytic germ and identity derivative. Its inverse series represents the
already constructed inverse germ. The uniform Taylor bound is stated here as
the quantitative input needed for a dimension-independent response extension.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped Topology

noncomputable section

variable {n k : ℕ}

def localConnected (t : LocalParameters n k) : LocalParameters n k :=
  LocalParameters.equiv.symm (complexConnected (LocalParameters.equiv t))

def localInverse (q : LocalParameters n k) : LocalParameters n k :=
  LocalParameters.equiv.symm (complexInverse (LocalParameters.equiv q))

@[simp] theorem localConnected_zero : localConnected (n := n) (k := k) 0 = 0 := by
  simp only [localConnected, map_zero, complexConnected_zero]

@[simp] theorem localInverse_zero : localInverse (n := n) (k := k) 0 = 0 := by
  simp only [localInverse, map_zero, complexInverse_zero]

theorem analyticAt_localConnected : AnalyticAt ℂ (localConnected (n := n) (k := k)) 0 := by
  let e := LocalParameters.equiv (n := n) (k := k)
  exact (e.symm.analyticAt _).comp
    (analyticAt_complexConnected.comp_of_eq (e.analyticAt 0) e.map_zero)

theorem analyticAt_localInverse : AnalyticAt ℂ (localInverse (n := n) (k := k)) 0 := by
  let e := LocalParameters.equiv (n := n) (k := k)
  exact (e.symm.analyticAt _).comp
    (analyticAt_complexInverse.comp_of_eq (e.analyticAt 0) e.map_zero)

theorem hasFDerivAt_localConnected :
    HasFDerivAt (localConnected (n := n) (k := k))
      (ContinuousLinearMap.id ℂ (LocalParameters n k)) 0 := by
  let e := LocalParameters.equiv (n := n) (k := k)
  have hm : HasFDerivAt complexConnected
      (ContinuousLinearMap.id ℂ (ComplexParameters n k)) (e 0) := by
    simpa only [map_zero] using (hasFDerivAt_complexConnected (n := n) (k := k))
  have h := e.symm.hasFDerivAt.comp (0 : LocalParameters n k) (hm.comp 0 e.hasFDerivAt)
  convert! h using 1

theorem hasStrictFDerivAt_localConnected :
    HasStrictFDerivAt (localConnected (n := n) (k := k))
      (ContinuousLinearMap.id ℂ (LocalParameters n k)) 0 := by
  have h := (analyticAt_localConnected (n := n) (k := k)).hasStrictFDerivAt
  rwa [hasFDerivAt_localConnected.fderiv] at h

theorem localInverse_left :
    ∀ᶠ t : LocalParameters n k in 𝓝 0, localInverse (localConnected t) = t := by
  let e := LocalParameters.equiv (n := n) (k := k)
  have hc : Filter.Tendsto e (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using e.continuous.continuousAt.tendsto (x := 0)
  have h := hc.eventually (complexInverse_left (n := n) (k := k))
  filter_upwards [h] with t ht
  simpa only [localInverse, localConnected, e, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply] using congrArg e.symm ht

theorem localInverse_right :
    ∀ᶠ q : LocalParameters n k in 𝓝 0, localConnected (localInverse q) = q := by
  let e := LocalParameters.equiv (n := n) (k := k)
  have hc : Filter.Tendsto e (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using e.continuous.continuousAt.tendsto (x := 0)
  have h := hc.eventually (complexInverse_right (n := n) (k := k))
  filter_upwards [h] with q hq
  simpa only [localInverse, localConnected, e, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply] using congrArg e.symm hq

theorem localConnected_series_zero
    {p : FormalMultilinearSeries ℂ (LocalParameters n k) (LocalParameters n k)}
    (hp : HasFPowerSeriesAt localConnected p 0) : p 0 = 0 := by
  ext v
  simpa using hp.coeff_zero v

theorem localConnected_series_one
    {p : FormalMultilinearSeries ℂ (LocalParameters n k) (LocalParameters n k)}
    (hp : HasFPowerSeriesAt localConnected p 0) :
    p 1 = (continuousMultilinearCurryFin1 ℂ (LocalParameters n k)
      (LocalParameters n k)).symm (ContinuousLinearEquiv.refl ℂ (LocalParameters n k)) := by
  apply (continuousMultilinearCurryFin1 ℂ (LocalParameters n k)
    (LocalParameters n k)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact hp.hasFDerivAt.unique hasFDerivAt_localConnected

theorem hasFPowerSeriesAt_localInverse
    {p : FormalMultilinearSeries ℂ (LocalParameters n k) (LocalParameters n k)}
    (hp : HasFPowerSeriesAt localConnected p 0) :
    HasFPowerSeriesAt localInverse
      (p.rightInv (ContinuousLinearEquiv.refl ℂ (LocalParameters n k)) 0) 0 := by
  let i := ContinuousLinearEquiv.refl ℂ (LocalParameters n k)
  let R := (hasStrictFDerivAt_localConnected (n := n) (k := k)).toOpenPartialHomeomorph
    localConnected (f' := i)
  have h0 : (0 : LocalParameters n k) ∈ R.source :=
    HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  have hp1 := localConnected_series_one hp
  have hR := R.hasFPowerSeriesAt_symm h0 hp hp1
  change HasFPowerSeriesAt R.symm (p.leftInv i 0) (localConnected 0) at hR
  rw [localConnected_zero, FormalMultilinearSeries.leftInv_eq_rightInv p i 0 hp1] at hR
  apply hR.congr
  have hR0 : R.symm 0 = 0 := by
    have h := R.left_inv h0
    change R.symm (localConnected 0) = 0 at h
    simpa using h
  have ht : (0 : LocalParameters n k) ∈ R.target := by
    have h := R.map_source h0
    change localConnected 0 ∈ R.target at h
    simpa using h
  have hc : Filter.Tendsto R.symm (𝓝 0) (𝓝 0) := by
    simpa only [hR0] using (R.continuousAt_symm ht).tendsto
  filter_upwards [R.open_target.mem_nhds ht, hc.eventually localInverse_left] with q hq hleft
  have hright : localConnected (R.symm q) = q := R.right_inv hq
  rw [hright] at hleft
  exact hleft.symm

/-- The mixed operator bound of manuscript equation (16), including the
constant coefficient. Its single constant is uniform in dimension and order. -/
def UniformConnectedTaylorBound (r : ℝ) : Prop :=
  ∀ n k : ℕ, 4 ≤ n → (k = 3 ∨ k = 4) →
    ∃ p : FormalMultilinearSeries ℂ (LocalParameters n k) (LocalParameters n k),
      HasFPowerSeriesAt localConnected p 0 ∧ ∀ d : ℕ, ‖p d‖ ≤ r ^ d

end

end TensorLB
