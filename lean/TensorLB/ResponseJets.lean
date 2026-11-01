module

public import TensorLB.RealResponse
public import TensorLB.ResponseWitness

/-!
# Moment matching for the constructed response

The response polynomials are obtained from an actual analytic germ. Their
truncation preserves all required directional jets, including the partition
factors, so the polynomial lift is an unconditional moment-matching witness.
The quantitative coefficient bound is a separate requirement.
-/

set_option autoImplicit false

public section

namespace TensorLB

open scoped BigOperators Topology

variable {n m k D : ℕ}

theorem responseTerm_jets (τ : ℝ) (A : Finset (Fin n)) (hA : A.Nonempty)
    (d : ℕ) (hd : d ≤ D) (t : ObservationIndex n k → ℝ) :
    iteratedDeriv d (fun s =>
      partitionFunction (fun I => τ * (s * t I)) *
        partitionFunction (fun I => s * t I) ^ (m - 1) *
          (∑ r ∈ Finset.range D,
            MvPolynomial.eval (connectedCoordinate (fun I => s * t I)) (responseTerm τ A (r + 1)))) 0 =
    iteratedDeriv d (fun s =>
      partitionFunction (fun I => τ * (s * t I)) *
        partitionFunction (fun I => s * t I) ^ (m - 1) *
          tiltedMoment (fun I => τ * (s * t I)) A) 0 := by
  let p := realResponseSeries (k := k) τ A
  have hline : AnalyticAt ℝ (fun s : ℝ => fun I => s * t I) 0 :=
    analyticAt_pi_iff.mpr (fun _ => analyticAt_id.mul analyticAt_const)
  have hscaled : AnalyticAt ℝ (fun s : ℝ => fun I => τ * (s * t I)) 0 :=
    analyticAt_pi_iff.mpr (fun _ => analyticAt_const.mul (analyticAt_id.mul analyticAt_const))
  have hconn : AnalyticAt ℝ (fun s : ℝ => connectedCoordinate (fun I => s * t I)) 0 :=
    (analyticAt_connectedCoordinate _).comp hline
  have hconn0 : connectedCoordinate (fun I => (0 : ℝ) * t I) = 0 := by
    have he : (fun I => (0 : ℝ) * t I) = (0 : ObservationIndex n k → ℝ) := by
      funext I
      simp
    rw [he, connectedCoordinate_zero]
  have hf : AnalyticAt ℝ (fun s => p.partialSum (D + 1)
      (connectedCoordinate (fun I => s * t I))) 0 := by
    have hh := (hasFPowerSeriesAt_partialSum p (D + 1)).analyticAt
    rw [← hconn0] at hh
    exact hh.comp (f := fun s : ℝ => connectedCoordinate (fun I => s * t I)) hconn
  have hg : AnalyticAt ℝ (fun s => tiltedMoment (fun I => τ * (s * t I)) A) 0 :=
    (analyticAt_tiltedMoment A _).comp hscaled
  have hw : AnalyticAt ℝ (fun s => partitionFunction (fun I => τ * (s * t I)) *
      partitionFunction (fun I => s * t I) ^ (m - 1)) 0 :=
    ((analyticAt_partitionFunction _).comp hscaled).mul
      (((analyticAt_partitionFunction _).comp hline).pow (m - 1))
  simp_rw [sum_eval_responseTerm τ A hA]
  apply iteratedDeriv_mul_eq_of_jets hf hg hw
  intro i hi
  have hj := iteratedDeriv_partialSum_comp (hasFPowerSeriesAt_realResponse τ A)
    hconn hconn0 (by omega : i < D + 1)
  apply hj.trans
  apply Filter.EventuallyEq.iteratedDeriv_eq
  have hlim : Filter.Tendsto (fun s : ℝ => fun I => s * t I) (𝓝 0) (𝓝 0) := by
    convert! hline.continuousAt.tendsto using 1
    congr 1
    ext I
    simp
  exact hlim.eventually (realResponse_comp_connected τ A)

theorem responseTerm_momentMatching (τ : ℝ) (A : Finset (Fin n)) (hA : A.Nonempty)
    (hN : 6 * D ≤ m - 1) :
    IsReducedMomentMatchingWitness n m k D τ A
      (responseWitness (responseTerm (k := k) τ A) D) := by
  apply responseWitness_momentMatching
  · intro d _ _
    exact (responseTerm_isHomogeneous τ A d).totalDegree_le
  · exact hN
  · exact responseTerm_jets τ A hA

end TensorLB
