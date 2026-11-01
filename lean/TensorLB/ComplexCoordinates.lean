module

public import TensorLB.ConnectedSubstitution
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Complex tilted moments near the origin

These are the complex extensions of the finite real generating functions.
Character orthogonality computes their values and derivatives at zero exactly.
All analyticity statements in this module are local; a radius uniform in the
dimension is a separate estimate.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n k : ℕ}

abbrev ComplexParameters (n k : ℕ) := ObservationIndex n k → ℂ

def complexInteraction (z : Fin n → Bool) : ComplexParameters n k →L[ℂ] ℂ :=
  ∑ I, (character I.val z : ℂ) • ContinuousLinearMap.proj I

def complexNumerator (B : Finset (Fin n)) (t : ComplexParameters n k) : ℂ :=
  (Fintype.card (Fin n → Bool) : ℂ)⁻¹ *
    ∑ z, (character B z : ℂ) * Complex.exp (complexInteraction z t)

def complexPartition (t : ComplexParameters n k) : ℂ := complexNumerator ∅ t

def complexMoment (t : ComplexParameters n k) (B : Finset (Fin n)) : ℂ :=
  complexNumerator B t / complexPartition t

def complexMomentDerivative (B : Finset (Fin n)) : ComplexParameters n k →L[ℂ] ℂ :=
  (Fintype.card (Fin n → Bool) : ℂ)⁻¹ •
    ∑ z, (character B z : ℂ) • complexInteraction z

theorem complexInteraction_apply (z : Fin n → Bool) (t : ComplexParameters n k) :
    complexInteraction z t = ∑ I, (character I.val z : ℂ) * t I := by
  simp [complexInteraction]

theorem complexNumerator_zero (B : Finset (Fin n)) :
    complexNumerator (k := k) B 0 = if B = ∅ then 1 else 0 := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) (expect_character B)
  by_cases hB : B = ∅
  · simp [complexNumerator, hB]
  · simpa [complexNumerator, Fintype.expect_eq_sum_div_card, hB, div_eq_mul_inv,
      mul_comm] using h

@[simp] theorem complexPartition_zero : complexPartition (n := n) (k := k) 0 = 1 := by
  simp [complexPartition, complexNumerator_zero]

theorem complexMoment_zero (B : Finset (Fin n)) :
    complexMoment (k := k) 0 B = if B = ∅ then 1 else 0 := by
  simp [complexMoment, complexNumerator_zero]

theorem complexMomentDerivative_apply (B : Finset (Fin n)) (t : ComplexParameters n k) :
    complexMomentDerivative B t = ∑ I, (if B = I.val then 1 else 0) * t I := by
  simp only [complexMomentDerivative, smul_apply, smul_eq_mul,
    sum_apply, complexInteraction_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  have h : (∑ z, (character B z : ℂ) * (character I.val z : ℂ)) /
      (Fintype.card (Fin n → Bool) : ℂ) = if B = I.val then 1 else 0 := by
    have hc := congrArg (fun x : ℝ => (x : ℂ)) (expect_character_mul B I.val)
    by_cases hBI : B = I.val <;>
      simpa only [Fintype.expect_eq_sum_div_card, Complex.ofReal_div, Complex.ofReal_sum,
        Complex.ofReal_natCast, Complex.ofReal_mul, hBI, ite_true, ite_false,
        Complex.ofReal_one, Complex.ofReal_zero] using hc
  rw [← h]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem complexMomentDerivative_observation (I : ObservationIndex n k) :
    complexMomentDerivative I.val = ContinuousLinearMap.proj I := by
  ext t
  rw [complexMomentDerivative_apply]
  have he : ∀ J : ObservationIndex n k, I.val = J.val ↔ I = J :=
    fun _ => Subtype.val_inj
  simp [he]

theorem complexMomentDerivative_empty :
    complexMomentDerivative (n := n) (k := k) ∅ = 0 := by
  ext t
  rw [complexMomentDerivative_apply]
  apply Finset.sum_eq_zero
  intro I _
  simp [Ne.symm I.property.1.ne_empty]

theorem hasFDerivAt_complexNumerator_zero (B : Finset (Fin n)) :
    HasFDerivAt (complexNumerator (k := k) B) (complexMomentDerivative B) 0 := by
  change HasFDerivAt (fun t => (Fintype.card (Fin n → Bool) : ℂ)⁻¹ *
    ∑ z, (character B z : ℂ) * Complex.exp (complexInteraction z t)) _ _
  have hs := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin n → Bool)))
    (fun z _ => ((complexInteraction (k := k) z).hasFDerivAt
      (x := (0 : ComplexParameters n k))).cexp.const_mul (character B z : ℂ))
  simpa [complexMomentDerivative] using
    hs.const_mul (Fintype.card (Fin n → Bool) : ℂ)⁻¹

theorem hasFDerivAt_complexPartition_zero :
    HasFDerivAt (complexPartition (n := n) (k := k))
      (0 : ComplexParameters n k →L[ℂ] ℂ) 0 := by
  change HasFDerivAt (complexNumerator ∅) (0 : ComplexParameters n k →L[ℂ] ℂ) 0
  simpa only [complexMomentDerivative_empty] using
    hasFDerivAt_complexNumerator_zero (n := n) (k := k) ∅

theorem hasFDerivAt_complexMoment_zero (B : Finset (Fin n)) :
    HasFDerivAt (fun t : ComplexParameters n k => complexMoment t B)
      (complexMomentDerivative B) 0 := by
  have hi : HasFDerivAt (fun t : ComplexParameters n k => (complexPartition t)⁻¹)
      (0 : ComplexParameters n k →L[ℂ] ℂ) 0 := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_zero] using
      (hasFDerivAt_inv (by simp : complexPartition (n := n) (k := k) 0 ≠ 0)).comp
      0 hasFDerivAt_complexPartition_zero
  have hm := (hasFDerivAt_complexNumerator_zero (k := k) B).mul hi
  convert! hm using 1
  ext t
  simp

theorem analyticAt_complexNumerator (B : Finset (Fin n)) (t : ComplexParameters n k) :
    AnalyticAt ℂ (complexNumerator B) t := by
  change AnalyticAt ℂ (fun t => (Fintype.card (Fin n → Bool) : ℂ)⁻¹ *
    ∑ z, (character B z : ℂ) * Complex.exp (complexInteraction z t)) t
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro z _
  exact analyticAt_const.mul (((complexInteraction z).analyticAt t).cexp)

theorem analyticAt_complexPartition (t : ComplexParameters n k) :
    AnalyticAt ℂ complexPartition t := analyticAt_complexNumerator ∅ t

theorem analyticAt_complexMoment_zero (B : Finset (Fin n)) :
    AnalyticAt ℂ (fun t : ComplexParameters n k => complexMoment t B) 0 := by
  exact (analyticAt_complexNumerator B 0).div (analyticAt_complexPartition 0) (by simp)

theorem complexInteraction_ofReal (t : ObservationIndex n k → ℝ) (z : Fin n → Bool) :
    complexInteraction z (fun I => (t I : ℂ)) = (interactionExponent t z : ℂ) := by
  simp only [complexInteraction_apply, interactionExponent, Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro I _
  ring

theorem complexNumerator_ofReal (B : Finset (Fin n)) (t : ObservationIndex n k → ℝ) :
    complexNumerator B (fun I => (t I : ℂ)) =
      ((𝔼 z, character B z * Real.exp (interactionExponent t z) : ℝ) : ℂ) := by
  simp only [complexNumerator, complexInteraction_ofReal, Fintype.expect_eq_sum_div_card,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_exp, div_eq_mul_inv]
  push_cast
  ring

theorem complexPartition_ofReal (t : ObservationIndex n k → ℝ) :
    complexPartition (fun I => (t I : ℂ)) = (partitionFunction t : ℂ) := by
  simp only [complexPartition, complexNumerator_ofReal, character_empty, one_mul, partitionFunction]

theorem complexMoment_ofReal (B : Finset (Fin n)) (t : ObservationIndex n k → ℝ) :
    complexMoment (fun I => (t I : ℂ)) B = (tiltedMoment t B : ℂ) := by
  simp only [complexMoment, complexNumerator_ofReal, complexPartition_ofReal,
    tiltedMoment, Complex.ofReal_div]

end

end TensorLB
