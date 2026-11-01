module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.CPolynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Taylor truncation under analytic composition

Keeping terms through degree `D` preserves derivatives through degree `D`
after composition with an analytic curve through zero and multiplication by
an analytic scalar factor.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def truncateSeries (p : FormalMultilinearSeries ℝ E ℝ) (D : ℕ) :
    FormalMultilinearSeries ℝ E ℝ := fun d => if d < D then p d else 0

theorem hasFPowerSeriesAt_partialSum (p : FormalMultilinearSeries ℝ E ℝ) (D : ℕ) :
    HasFPowerSeriesAt (p.partialSum D) (truncateSeries p D) 0 := by
  have h : HasFiniteFPowerSeriesOnBall (p.partialSum D) (truncateSeries p D) 0 D 1 := by
    apply HasFiniteFPowerSeriesOnBall.mk'
    · intro d hd
      simp [truncateSeries, Nat.not_lt.mpr hd]
    · norm_num
    · intro y _
      simp only [zero_add, FormalMultilinearSeries.partialSum]
      apply Finset.sum_congr rfl
      intro d hd
      simp only [truncateSeries, Finset.mem_range.mp hd, ite_true]
  exact h.toHasFPowerSeriesOnBall.hasFPowerSeriesAt

theorem truncateSeries_comp_coeff (p : FormalMultilinearSeries ℝ E ℝ)
    (q : FormalMultilinearSeries ℝ ℝ E) {D d : ℕ} (hd : d < D) :
    ((truncateSeries p D).comp q) d = (p.comp q) d := by
  apply Finset.sum_congr rfl
  intro c _
  unfold FormalMultilinearSeries.compAlongComposition
  rw [truncateSeries, ite_eq_left (c.length_le.trans_lt hd)]

theorem iteratedDeriv_eq_of_series_coeff {f g : ℝ → ℝ}
    {p q : FormalMultilinearSeries ℝ ℝ ℝ}
    (hf : HasFPowerSeriesAt f p 0) (hg : HasFPowerSeriesAt g q 0)
    (d : ℕ) (hd : p d = q d) : iteratedDeriv d f 0 = iteratedDeriv d g 0 := by
  obtain ⟨r, hr⟩ := hf
  obtain ⟨s, hs⟩ := hg
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    ← hr.factorial_smul 1 d, ← hs.factorial_smul 1 d, hd]

theorem iteratedDeriv_partialSum_comp {f : E → ℝ} {p : FormalMultilinearSeries ℝ E ℝ}
    (hf : HasFPowerSeriesAt f p 0) {g : ℝ → E} (hg : AnalyticAt ℝ g 0) (hg0 : g 0 = 0)
    {D d : ℕ} (hd : d < D) :
    iteratedDeriv d (fun s => p.partialSum D (g s)) 0 =
      iteratedDeriv d (fun s => f (g s)) 0 := by
  obtain ⟨q, hq⟩ := hg
  have hp := hasFPowerSeriesAt_partialSum p D
  rw [← hg0] at hp hf
  exact iteratedDeriv_eq_of_series_coeff (hp.comp hq) (hf.comp hq) d
    (truncateSeries_comp_coeff p q hd)

theorem iteratedDeriv_mul_eq_of_jets {f g w : ℝ → ℝ} {d : ℕ}
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) (hw : AnalyticAt ℝ w 0)
    (hjet : ∀ i ≤ d, iteratedDeriv i f 0 = iteratedDeriv i g 0) :
    iteratedDeriv d (fun s => w s * f s) 0 = iteratedDeriv d (fun s => w s * g s) 0 := by
  rw [iteratedDeriv_fun_mul (hw.contDiffAt.of_le le_top) (hf.contDiffAt.of_le le_top),
    iteratedDeriv_fun_mul (hw.contDiffAt.of_le le_top) (hg.contDiffAt.of_le le_top)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hjet (d - i) (Nat.sub_le d i)]

theorem iteratedDeriv_along_line {f : E → ℝ} {p : FormalMultilinearSeries ℝ E ℝ}
    (hf : HasFPowerSeriesAt f p 0) (x : E) (d : ℕ) :
    iteratedDeriv d (fun s : ℝ => f (s • x)) 0 =
      (d.factorial : ℝ) * p d (fun _ => x) := by
  let u : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ x
  have hfu : HasFPowerSeriesAt f p (u 0) := by simpa only [map_zero] using hf
  obtain ⟨r, hr⟩ := hfu.compContinuousLinearMap
  have hh := hr.factorial_smul (1 : ℝ) d
  simpa only [← iteratedDeriv_eq_iteratedFDeriv, Function.comp_def, u,
    ContinuousLinearMap.toSpanSingleton_apply, FormalMultilinearSeries.compContinuousLinearMap,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, one_smul, nsmul_eq_mul] using hh.symm

theorem taylor_diagonal_covariant {f : E → ℝ} {p : FormalMultilinearSeries ℝ E ℝ}
    (hf : HasFPowerSeriesAt f p 0) (S : E →L[ℝ] E) (c : ℝ)
    (he : ∀ᶠ x in 𝓝 0, f (S x) = c * f x) (x : E) (d : ℕ) :
    p d (fun _ => S x) = c * p d (fun _ => x) := by
  have ht : Filter.Tendsto (fun s : ℝ => s • x) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ => s • x) := continuous_id.smul continuous_const
    exact hc.tendsto' 0 0 (zero_smul ℝ x)
  have heq : (fun s : ℝ => f (S (s • x))) =ᶠ[𝓝 0] (fun s => c * f (s • x)) :=
    ht.eventually he
  have hj := Filter.EventuallyEq.iteratedDeriv_eq d heq
  simp only [map_smul] at hj
  rw [iteratedDeriv_along_line hf, iteratedDeriv_const_mul_field,
    iteratedDeriv_along_line hf] at hj
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d) : (d.factorial : ℝ) ≠ 0)
  simpa only [mul_left_comm] using hj

end

end TensorLB
