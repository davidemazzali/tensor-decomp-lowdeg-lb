module

public import TensorLB.MarkedCumulant
public import TensorLB.ConnectedCumulantSeries

/-!
# The connected-cumulant Taylor expansion

Iterating the tilted-cumulant derivative identifies every coefficient. The
geometric coefficient bound supplies a positive radius for the explicit
series, and analyticity identifies its sum with the connected map near zero.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical Topology

noncomputable section

variable {n k d : ℕ}

theorem iteratedFDeriv_complexConnected (hk : k = 3 ∨ k = 4) (I : ObservationIndex n k)
    (w : Fin d → ComplexParameters n k) :
    iteratedFDeriv ℂ d (fun t => complexConnected t I) 0 w =
      ∑ J : Fin d → ObservationIndex n k, (outputCumulant I.val J : ℂ) * ∏ j, w j (J j) := by
  let e : Fin I.val.card ≃ I.val :=
    (Fintype.equivFinOfCardEq (by simp : Fintype.card I.val = I.val.card)).symm
  have he : (fun t : ComplexParameters n k => complexConnected t I) =
      tiltedCumulant (fun j z => (character {(e j).val} z : ℂ)) := by
    funext t
    exact (tiltedCumulant_eq_complexConnected hk I e t).symm
  rw [he]
  exact iteratedFDeriv_marked I.val e (Finset.card_pos.mpr I.property.1) d w

theorem iteratedFDeriv_localConnected_coordinate (hk : k = 3 ∨ k = 4)
    (I : ObservationIndex n k) (w : Fin d → LocalParameters n k) :
    LocalParameters.equiv (iteratedFDeriv ℂ d localConnected 0 w) I =
      ∑ J : Fin d → ObservationIndex n k, (outputCumulant I.val J : ℂ) *
        ∏ j, LocalParameters.equiv (w j) (J j) := by
  let e := LocalParameters.equiv (n := n) (k := k)
  let L : LocalParameters n k →L[ℂ] ℂ := (ContinuousLinearMap.proj I).comp e.toContinuousLinearMap
  have hl := L.iteratedFDeriv_comp_left
    (analyticAt_localConnected.contDiffAt (n := (d : WithTop ℕ∞))) (i := d) le_rfl
  have hr := e.iteratedFDerivWithin_comp_right (fun t => complexConnected t I)
    uniqueDiffOn_univ (x := (0 : LocalParameters n k)) (Set.mem_univ _) d
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ, map_zero] at hr
  have hf : L ∘ localConnected = (fun t => complexConnected t I) ∘ e := by
    funext t
    change e (e.symm (complexConnected (e t))) I = complexConnected (e t) I
    rw [e.apply_symm_apply]
  rw [hf] at hl
  have he := congrArg (fun f : ContinuousMultilinearMap ℂ
    (fun _ : Fin d => LocalParameters n k) ℂ => f w) (hl.symm.trans hr)
  change LocalParameters.equiv (iteratedFDeriv ℂ d localConnected 0 w) I =
    iteratedFDeriv ℂ d (fun t => complexConnected t I) 0 (fun j => e (w j)) at he
  rw [he, iteratedFDeriv_complexConnected hk]

theorem connectedCumulantSeries_eq_factorial_derivative (hk : k = 3 ∨ k = 4)
    (w : Fin d → LocalParameters n k) :
    connectedCumulantSeries d w =
      (d.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ d localConnected 0 w := by
  by_cases hd : d = 0
  · subst d
    simp [connectedCumulantSeries]
  · apply LocalParameters.equiv.injective
    funext I
    rw [map_smul]
    change LocalParameters.equiv (connectedCumulantSeries d w) I =
      (d.factorial : ℂ)⁻¹ * LocalParameters.equiv (iteratedFDeriv ℂ d localConnected 0 w) I
    rw [iteratedFDeriv_localConnected_coordinate hk]
    rw [connectedCumulantSeries, ite_eq_right hd]
    change LocalParameters.equiv
      (LocalParameters.equiv.symm (fun I : ObservationIndex n k => cumulantCoordinateTerm d I.val w)) I = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact cumulantCoordinateTerm_apply I.val w

theorem hasFPowerSeriesAt_connectedCumulantSeries (hk : k = 3 ∨ k = 4) :
    HasFPowerSeriesAt (localConnected (n := n) (k := k)) connectedCumulantSeries 0 := by
  obtain ⟨p, r, hp⟩ := analyticAt_localConnected (n := n) (k := k)
  have hC : 0 < connectedCumulantConstant := lt_of_lt_of_le zero_lt_one connectedCumulantConstant_ge_one
  have hnorm := connectedCumulantSeries_norm_le (n := n)
    (show 1 ≤ k by rcases hk with rfl | rfl <;> norm_num)
    (show k ≤ 4 by rcases hk with rfl | rfl <;> norm_num)
  have hrad : 0 < (connectedCumulantSeries (n := n) (k := k)).radius :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr hC)).trans_le
      (geometric_series_radius_ge _ hC hnorm)
  refine ⟨min r connectedCumulantSeries.radius, ⟨min_le_right _ _, lt_min hp.r_pos hrad, ?_⟩⟩
  intro y hy
  have hyr : y ∈ Metric.eball (0 : LocalParameters n k) r := by
    exact (Metric.mem_eball.mp hy).trans_le (min_le_left _ _)
  convert! hp.hasSum_iteratedFDeriv hyr using 1
  funext j
  exact connectedCumulantSeries_eq_factorial_derivative hk _

theorem connectedCumulantExpansion : ConnectedCumulantExpansion := by
  intro n k _ hk
  exact hasFPowerSeriesAt_connectedCumulantSeries hk

end

end TensorLB
