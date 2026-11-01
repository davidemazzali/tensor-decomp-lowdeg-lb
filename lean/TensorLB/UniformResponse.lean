module

public import TensorLB.ConnectedSeries
public import TensorLB.MomentReconstruction
public import TensorLB.AnalyticReduction

/-!
# A uniform response ball from the connected Taylor estimate

The inverse majorant gives an analytic extension of the inverse germ. Composing
it with the connected series and the moment reconstruction proves the bounded
response lemma directly; only equality of germs is needed for the coefficient
argument, so no separate zero-free continuation of the partition function is
required here.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped Topology

noncomputable section

variable {n k : ℕ}

def uniformResponseRadius (τ r : ℝ) : ℝ :=
  min (inverseMajorantRadius r / 2) (1 / (16 * r * τ))

theorem uniformResponseRadius_pos {τ r : ℝ} (hτ : 0 < τ) (hr : 1 ≤ r) :
    0 < uniformResponseRadius τ r := by
  have ha := inverseMajorantRadius_pos hr
  unfold uniformResponseRadius
  apply lt_min <;> positivity

def seriesResponse (τ : ℝ) (A : Finset (Fin n))
    (p : FormalMultilinearSeries ℂ (LocalParameters n k) (LocalParameters n k))
    (q : ComplexParameters n k) : ℂ :=
  momentFromConnected A (LocalParameters.equiv (p.sum ((τ : ℂ) •
    (p.rightInv (ContinuousLinearEquiv.refl ℂ (LocalParameters n k)) 0).sum
      (LocalParameters.equiv.symm q))))

theorem seriesResponse_germ (τ : ℝ) (A : Finset (Fin n)) (hA : admissibleTarget n k A)
    {p : FormalMultilinearSeries ℂ (LocalParameters n k) (LocalParameters n k)}
    (hp : HasFPowerSeriesAt localConnected p 0) :
    seriesResponse τ A p =ᶠ[𝓝 0] complexResponse τ A := by
  let e := LocalParameters.equiv (n := n) (k := k)
  let Q := p.rightInv (ContinuousLinearEquiv.refl ℂ (LocalParameters n k)) 0
  have hQ : Q.sum =ᶠ[𝓝 0] localInverse := powerSeries_sum_germ (hasFPowerSeriesAt_localInverse hp)
  have he : Filter.Tendsto e.symm (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using e.symm.continuous.continuousAt.tendsto (x := 0)
  have ht : Filter.Tendsto (fun q : ComplexParameters n k =>
      (τ : ℂ) • localInverse (e.symm q)) (𝓝 0) (𝓝 0) := by
    have hc := (analyticAt_localInverse.comp_of_eq (e.symm.analyticAt 0)
      e.symm.map_zero).const_smul (c := (τ : ℂ))
    convert! hc.continuousAt.tendsto using 1
    simp only [Function.comp_apply, Pi.smul_apply, map_zero, localInverse_zero, smul_zero]
  filter_upwards [he.eventually hQ, ht.eventually (powerSeries_sum_germ hp)] with q hq htq
  change momentFromConnected A (e (p.sum ((τ : ℂ) • Q.sum (e.symm q)))) = _
  rw [hq, htq]
  simp only [localConnected, localInverse, ContinuousLinearEquiv.apply_symm_apply,
    map_smul, e]
  exact momentFromConnected_complexConnected A hA _

theorem seriesResponse_bounded_analytic {τ r : ℝ} (hτ : 0 < τ) (hr : 1 ≤ r)
    (A : Finset (Fin n))
    {p : FormalMultilinearSeries ℂ (LocalParameters n k) (LocalParameters n k)}
    (hp : HasFPowerSeriesAt localConnected p 0) (hb : ∀ d, ‖p d‖ ≤ r ^ d) :
    AnalyticOnNhd ℂ (seriesResponse τ A p) {q | localNorm q ≤ uniformResponseRadius τ r} ∧
      (∀ q, localNorm q ≤ uniformResponseRadius τ r → ‖seriesResponse τ A p q‖ ≤ 1) := by
  let e := LocalParameters.equiv (n := n) (k := k)
  let i := ContinuousLinearEquiv.refl ℂ (LocalParameters n k)
  let Q := p.rightInv i 0
  have hr0 : 0 < r := by linarith
  have hi : ‖(i.symm : LocalParameters n k →L[ℂ] LocalParameters n k)‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  have hτnorm : ‖(τ : ℂ)‖ = τ := by simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
  have hball (q : ComplexParameters n k) (hq : localNorm q ≤ uniformResponseRadius τ r) :
      ‖e.symm q‖ < inverseMajorantRadius r ∧
        r * ‖(τ : ℂ) • Q.sum (e.symm q)‖ ≤ 1 / 8 := by
    have hqn : ‖e.symm q‖ = localNorm q := rfl
    have h1 := hq.trans (min_le_left _ _)
    have h2 := hq.trans (min_le_right _ _)
    change localNorm q ≤ inverseMajorantRadius r / 2 at h1
    change localNorm q ≤ 1 / (16 * r * τ) at h2
    have hinv : ‖e.symm q‖ < inverseMajorantRadius r := by
      rw [hqn]
      have ha := inverseMajorantRadius_pos hr
      linarith
    refine ⟨hinv, ?_⟩
    have hQ := inverse_sum_norm_le p i hr hi hb (e.symm q) hinv
    change ‖Q.sum (e.symm q)‖ ≤ 2 * ‖e.symm q‖ at hQ
    have hsmall := (le_div_iff₀ (by positivity : 0 < 16 * r * τ)).mp h2
    rw [norm_smul, hτnorm]
    rw [hqn] at hQ
    have hmul := mul_le_mul_of_nonneg_left hQ (show 0 ≤ r * τ by positivity)
    nlinarith
  constructor
  · intro q hq
    obtain ⟨hinv, hscale⟩ := hball q hq
    have haQ := analyticAt_inverse_sum p i hr hi hb (e.symm q) hinv
    have hap := analyticAt_geometric_sum p hr0 hb ((τ : ℂ) • Q.sum (e.symm q))
      (by linarith)
    have haS : AnalyticAt ℂ (fun q : ComplexParameters n k =>
        (τ : ℂ) • Q.sum (e.symm q)) q :=
      (haQ.comp (e.symm.analyticAt q)).const_smul (c := (τ : ℂ))
    exact (analyticAt_momentFromConnected A _).comp
      ((e.analyticAt _).comp (hap.comp (f := fun q : ComplexParameters n k =>
        (τ : ℂ) • Q.sum (e.symm q)) haS))
  · intro q hq
    obtain ⟨_, hscale⟩ := hball q hq
    apply norm_momentFromConnected_le_one
    have hpbound := geometric_sum_norm_le p (localConnected_series_zero hp) hr0 hb
      ((τ : ℂ) • Q.sum (e.symm q)) (by linarith : r * ‖(τ : ℂ) • Q.sum (e.symm q)‖ ≤ 1 / 2)
    have hnorm := norm_le_localNorm (e (p.sum ((τ : ℂ) • Q.sum (e.symm q))))
    change ‖e (p.sum ((τ : ℂ) • Q.sum (e.symm q)))‖ ≤
      ‖p.sum ((τ : ℂ) • Q.sum (e.symm q))‖ at hnorm
    nlinarith

theorem uniformBoundedResponse_of_connectedTaylor {r : ℝ} (hr : 1 ≤ r)
    (h : UniformConnectedTaylorBound r) {τ : ℝ} (hτ : 0 < τ) :
    UniformBoundedResponse τ (uniformResponseRadius τ r) := by
  intro n k hn hk A hA
  obtain ⟨p, hp, hb⟩ := h n k hn hk
  obtain ⟨ha, hbnd⟩ := seriesResponse_bounded_analytic hτ hr A hp hb
  exact ⟨seriesResponse τ A p, ha, hbnd, seriesResponse_germ τ A hA hp⟩

theorem uniformResponseRadius_exists_of_connectedTaylor
    (h : ∃ r : ℝ, 1 ≤ r ∧ UniformConnectedTaylorBound r) :
    ∀ τ : ℝ, 1 < τ → ∃ ρ : ℝ, 0 < ρ ∧ UniformBoundedResponse τ ρ := by
  obtain ⟨r, hr, h⟩ := h
  intro τ hτ
  have hτ0 : 0 < τ := by linarith
  exact ⟨uniformResponseRadius τ r, uniformResponseRadius_pos hτ0 hr,
    uniformBoundedResponse_of_connectedTaylor hr h hτ0⟩

end

end TensorLB
