module

public import TensorLB.CumulantExtension

/-!
# Differentiating finite tilted expectations

The quotient rule for the finite exponential tilt is the covariance identity.
It is proved for arbitrary complex observables so it can be applied to products
of marked spins and interaction characters in the cumulant recurrence.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n k : ℕ}

def observableNumerator (X : (Fin n → Bool) → ℂ) (t : ComplexParameters n k) : ℂ :=
  (Fintype.card (Fin n → Bool) : ℂ)⁻¹ *
    ∑ z, X z * Complex.exp (complexInteraction z t)

def observableMean (X : (Fin n → Bool) → ℂ) (t : ComplexParameters n k) : ℂ :=
  observableNumerator X t / complexPartition t

def observableNumeratorDerivative (X : (Fin n → Bool) → ℂ) (t : ComplexParameters n k) :
    ComplexParameters n k →L[ℂ] ℂ :=
  (Fintype.card (Fin n → Bool) : ℂ)⁻¹ •
    ∑ z, (X z * Complex.exp (complexInteraction z t)) • complexInteraction z

theorem observableNumerator_one (t : ComplexParameters n k) :
    observableNumerator (fun _ => 1) t = complexPartition t := by
  simp only [observableNumerator, complexPartition, complexNumerator, character_empty,
    Complex.ofReal_one, one_mul]

theorem observableMean_character (B : Finset (Fin n)) (t : ComplexParameters n k) :
    observableMean (fun z => (character B z : ℂ)) t = complexMoment t B := rfl

theorem hasFDerivAt_observableNumerator (X : (Fin n → Bool) → ℂ) (t : ComplexParameters n k) :
    HasFDerivAt (observableNumerator X) (observableNumeratorDerivative X t) t := by
  change HasFDerivAt (fun y : ComplexParameters n k =>
    (Fintype.card (Fin n → Bool) : ℂ)⁻¹ * ∑ z, X z * Complex.exp (complexInteraction z y)) _ t
  have h := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin n → Bool)))
    (fun z _ => ((complexInteraction (k := k) z).hasFDerivAt (x := t)).cexp.const_mul (X z))
  simpa [observableNumerator, observableNumeratorDerivative, smul_smul] using
    h.const_mul (Fintype.card (Fin n → Bool) : ℂ)⁻¹

theorem analyticAt_observableNumerator (X : (Fin n → Bool) → ℂ) (t : ComplexParameters n k) :
    AnalyticAt ℂ (observableNumerator X) t := by
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro z _
  exact analyticAt_const.mul (((complexInteraction z).analyticAt t).cexp)

theorem analyticAt_observableMean (X : (Fin n → Bool) → ℂ) (t : ComplexParameters n k)
    (ht : complexPartition t ≠ 0) : AnalyticAt ℂ (observableMean X) t :=
  (analyticAt_observableNumerator X t).div (analyticAt_complexPartition t) ht

def observableMeanDerivative (X : (Fin n → Bool) → ℂ) (t : ComplexParameters n k) :
    ComplexParameters n k →L[ℂ] ℂ :=
  (complexPartition t)⁻¹ • observableNumeratorDerivative X t -
    (observableNumerator X t * ((complexPartition t) ^ 2)⁻¹) •
      observableNumeratorDerivative (fun _ => 1) t

theorem hasFDerivAt_observableMean (X : (Fin n → Bool) → ℂ) (t : ComplexParameters n k)
    (ht : complexPartition t ≠ 0) :
    HasFDerivAt (observableMean X) (observableMeanDerivative X t) t := by
  have hZ : HasFDerivAt complexPartition (observableNumeratorDerivative (fun _ => 1) t) t := by
    have he : (observableNumerator (n := n) (k := k) (fun _ => (1 : ℂ))) = complexPartition :=
      funext observableNumerator_one
    rw [← he]
    exact hasFDerivAt_observableNumerator (fun _ => 1) t
  have hi := (hasFDerivAt_inv ht).comp t hZ
  have hm := (hasFDerivAt_observableNumerator X t).mul hi
  convert! hm using 1
  ext w
  simp only [observableMeanDerivative, sub_apply,
      smul_apply, add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, Function.comp_apply]
  ring

theorem observableNumeratorDerivative_apply (X : (Fin n → Bool) → ℂ)
    (t w : ComplexParameters n k) :
    observableNumeratorDerivative X t w =
      observableNumerator (fun z => X z * complexInteraction z w) t := by
  simp only [observableNumeratorDerivative, smul_apply,
    sum_apply, smul_eq_mul, observableNumerator]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem observableMeanDerivative_apply (X : (Fin n → Bool) → ℂ)
    (t w : ComplexParameters n k) :
    observableMeanDerivative X t w =
      observableMean (fun z => X z * complexInteraction z w) t -
        observableMean X t * observableMean (fun z => complexInteraction z w) t := by
  simp only [observableMeanDerivative, sub_apply,
    smul_apply, smul_eq_mul, observableNumeratorDerivative_apply,
    one_mul, observableMean, div_eq_mul_inv]
  ring

end

end TensorLB
