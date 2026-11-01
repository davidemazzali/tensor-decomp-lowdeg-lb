module

public import TensorLB.RootedOutput
public import TensorLB.ConnectedSeries

/-!
# The uniformly bounded connected-cumulant series

These multilinear coefficients are the right-hand side of manuscript equation
(13). Their local operator norms are bounded using rooted output enumeration
and the dependency-tree estimate. Identifying this series with the analytic
connected map is a separate Taylor identity.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n k d : ℕ}

def cumulantCoordinateTerm (d : ℕ) (B : Finset (Fin n)) :
    ContinuousMultilinearMap ℂ (fun _ : Fin d => LocalParameters n k) ℂ :=
  (d.factorial : ℂ)⁻¹ • ∑ J : Fin d → ObservationIndex n k,
    (outputCumulant B J : ℂ) •
      (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin d) ℂ).compContinuousLinearMap
        (fun j => (ContinuousLinearMap.proj (J j)).comp LocalParameters.equiv.toContinuousLinearMap)

theorem cumulantCoordinateTerm_apply (B : Finset (Fin n)) (w : Fin d → LocalParameters n k) :
    cumulantCoordinateTerm d B w = (d.factorial : ℂ)⁻¹ *
      ∑ J : Fin d → ObservationIndex n k,
        (outputCumulant B J : ℂ) * ∏ j, LocalParameters.equiv (w j) (J j) := by
  simp [cumulantCoordinateTerm, ContinuousMultilinearMap.mkPiAlgebra_apply]
  left
  rfl

def connectedCumulantTerm (d : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin d => LocalParameters n k) (LocalParameters n k) :=
  LocalParameters.equiv.symm.toContinuousLinearMap.compContinuousMultilinearMap
    (ContinuousMultilinearMap.pi (fun I : ObservationIndex n k => cumulantCoordinateTerm d I.val))

def connectedCumulantSeries : FormalMultilinearSeries ℂ (LocalParameters n k) (LocalParameters n k) :=
  fun d => if d = 0 then 0 else connectedCumulantTerm d

theorem cumulantCoordinateTerm_norm_le (B : Finset (Fin n)) (w : Fin d → LocalParameters n k) :
    ‖cumulantCoordinateTerm d B w‖ ≤
      (∑ J : Fin d → ObservationIndex n k,
        |outputCumulant B J| * ∏ j, ‖LocalParameters.equiv (w j) (J j)‖) / d.factorial := by
  rw [cumulantCoordinateTerm_apply, norm_mul, norm_inv]
  have hnorm : ‖(d.factorial : ℂ)‖ = (d.factorial : ℝ) := by simp
  rw [hnorm, div_eq_mul_inv, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ J : Fin d → ObservationIndex n k,
        ‖(outputCumulant B J : ℂ) * ∏ j, LocalParameters.equiv (w j) (J j)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_prod]

theorem sum_incident_le_sum_rootedOutputs (hk : k ≤ 4) (i : Fin n)
    (f : Finset (Fin n) → ℝ) (hf : ∀ B, 0 ≤ f B) :
    (∑ I : ObservationIndex n k, if i ∈ I.val then f I.val else 0) ≤
      ∑ p : Fin 4, ∑ B : RootedOutput n i p.val, f B.val := by
  let A := {I : ObservationIndex n k // i ∈ I.val}
  let g : A → Σ p : Fin 4, RootedOutput n i p.val := fun I =>
    ⟨⟨I.val.val.card - 1, by have := I.val.property.2.1; omega⟩,
      ⟨I.val.val, I.property, by
        change I.val.val.card = I.val.val.card - 1 + 1
        have := Finset.card_pos.mpr I.val.property.1
        omega⟩⟩
  have hg : Function.Injective g := by
    intro I J h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Σ p : Fin 4, RootedOutput n i p.val => z.2.val) h
  rw [← Finset.sum_filter, Finset.sum_subtype (p := fun I : ObservationIndex n k => i ∈ I.val)
    (F := inferInstance) _ (by simp)]
  rw [← Fintype.sum_sigma (f := fun z : Σ p : Fin 4, RootedOutput n i p.val => f z.2.val)]
  change (∑ I : A, f I.val.val) ≤ _
  calc
    _ = ∑ z ∈ Finset.univ.image g, f z.2.val :=
      (Finset.sum_image (fun a _ b _ h => hg h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun z _ _ => hf z.2.val)

def connectedCumulantConstant : ℝ := 4 * treeTaylorConstant

theorem connectedCumulantConstant_ge_one : 1 ≤ connectedCumulantConstant := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  unfold connectedCumulantConstant treeTaylorConstant
  nlinarith

theorem connectedCumulantTerm_norm_le (hd : 1 ≤ d) (hk : 1 ≤ k) (hk4 : k ≤ 4) :
    ‖(connectedCumulantTerm d : ContinuousMultilinearMap ℂ
      (fun _ : Fin d => LocalParameters n k) (LocalParameters n k))‖ ≤ connectedCumulantConstant ^ d := by
  have hC : 0 ≤ connectedCumulantConstant := zero_le_one.trans connectedCumulantConstant_ge_one
  apply ContinuousMultilinearMap.opNorm_le_bound (pow_nonneg hC _)
  intro w
  rw [LocalParameters.norm_eq]
  apply (localNorm_le_iff _ (by positivity)).mpr
  intro i
  have hterm : LocalParameters.equiv (connectedCumulantTerm d w) =
      fun I : ObservationIndex n k => cumulantCoordinateTerm d I.val w := rfl
  rw [hterm]
  let f := fun B : Finset (Fin n) =>
    (∑ J : Fin d → ObservationIndex n k,
      |outputCumulant B J| * ∏ j, ‖LocalParameters.equiv (w j) (J j)‖) / d.factorial
  have hf : ∀ B, 0 ≤ f B := by intro B; dsimp only [f]; positivity
  calc
    _ ≤ ∑ I : ObservationIndex n k, if i ∈ I.val then f I.val else 0 := by
      apply Finset.sum_le_sum
      intro I _
      split_ifs
      · exact cumulantCoordinateTerm_norm_le I.val w
      · exact le_rfl
    _ ≤ ∑ p : Fin 4, ∑ B : RootedOutput n i p.val, f B.val :=
      sum_incident_le_sum_rootedOutputs hk4 i f hf
    _ ≤ ∑ _p : Fin 4, treeTaylorConstant ^ d * ∏ j, ‖w j‖ := by
      apply Finset.sum_le_sum
      intro p _
      dsimp only [f]
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      simpa only [LocalParameters.norm_eq, div_eq_mul_inv] using
        sum_outputCumulant_div_factorial_le i (by have := p.isLt; omega) hd hk hk4
          (fun j => LocalParameters.equiv (w j))
    _ = (4 * treeTaylorConstant ^ d) * ∏ j, ‖w j‖ := by simp; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun j _ => norm_nonneg (w j)))
      unfold connectedCumulantConstant
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg treeTaylorConstant_pos.le _)
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hd

theorem connectedCumulantSeries_norm_le (hk : 1 ≤ k) (hk4 : k ≤ 4) (d : ℕ) :
    ‖(connectedCumulantSeries (n := n) (k := k)) d‖ ≤ connectedCumulantConstant ^ d := by
  by_cases hd : d = 0
  · simp [connectedCumulantSeries, hd]
  · rw [connectedCumulantSeries, ite_eq_right hd]
    exact connectedCumulantTerm_norm_le (by omega) hk hk4

/-- The connected-coordinate Taylor identity, manuscript equation (13).
The coefficient estimate is proved independently above. -/
def ConnectedCumulantExpansion : Prop :=
  ∀ n k : ℕ, 4 ≤ n → (k = 3 ∨ k = 4) →
    HasFPowerSeriesAt (localConnected (n := n) (k := k)) connectedCumulantSeries 0

theorem uniformConnectedTaylor_exists_of_cumulantExpansion (h : ConnectedCumulantExpansion) :
    ∃ r : ℝ, 1 ≤ r ∧ UniformConnectedTaylorBound r := by
  refine ⟨connectedCumulantConstant, connectedCumulantConstant_ge_one, ?_⟩
  intro n k hn hk
  refine ⟨connectedCumulantSeries, h n k hn hk, ?_⟩
  intro d
  exact connectedCumulantSeries_norm_le (by rcases hk with rfl | rfl <;> norm_num)
    (by rcases hk with rfl | rfl <;> norm_num) d

end

end TensorLB
