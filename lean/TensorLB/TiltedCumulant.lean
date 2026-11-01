module

public import TensorLB.TiltedObservable

/-!
# Differentiation appends an occurrence to a tilted cumulant

The covariance derivative for each block combines with the ordered partition
extension identity. The normalization terms become exactly the contribution
of the new singleton block.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n k s : ℕ}

abbrev SpinObservable (n : ℕ) := (Fin n → Bool) → ℂ

def familyObservable (X : Fin s → SpinObservable n) (B : Finset (Fin s)) : SpinObservable n :=
  fun z => ∏ j ∈ B, X j z

def familyMean (X : Fin s → SpinObservable n) (B : Finset (Fin s)) (t : ComplexParameters n k) : ℂ :=
  observableMean (familyObservable X B) t

def tiltedCumulant (X : Fin s → SpinObservable n) (t : ComplexParameters n k) : ℂ :=
  orderedCumulant (fun B => familyMean X B t)

theorem familyMean_cons_image (Y : SpinObservable n) (X : Fin s → SpinObservable n)
    (B : Finset (Fin s)) (t : ComplexParameters n k) :
    familyMean (Fin.cons Y X) (B.image Fin.succ) t = familyMean X B t := by
  unfold familyMean
  congr 1
  funext z
  simp only [familyObservable, Finset.prod_image (fun _ _ _ _ h => Fin.succ_injective _ h), Fin.cons_succ]

theorem familyMean_cons_insert (Y : SpinObservable n) (X : Fin s → SpinObservable n)
    (B : Finset (Fin s)) (t : ComplexParameters n k) :
    familyMean (Fin.cons Y X) (insert 0 (B.image Fin.succ)) t =
      observableMean (fun z => Y z * familyObservable X B z) t := by
  unfold familyMean
  congr 1
  funext z
  have h0 : (0 : Fin (s + 1)) ∉ B.image Fin.succ := by simp
  simp only [familyObservable, Finset.prod_insert h0, Fin.cons_zero,
    Finset.prod_image (fun _ _ _ _ h => Fin.succ_injective _ h), Fin.cons_succ]

theorem familyMean_cons_singleton (Y : SpinObservable n) (X : Fin s → SpinObservable n)
    (t : ComplexParameters n k) : familyMean (Fin.cons Y X) {0} t = observableMean Y t := by
  unfold familyMean
  congr 1
  funext z
  simp only [familyObservable, Finset.prod_singleton, Fin.cons_zero]

theorem familyMeanDerivative_apply (X : Fin s → SpinObservable n) (B : Finset (Fin s))
    (t w : ComplexParameters n k) :
    observableMeanDerivative (familyObservable X B) t w =
      familyMean (Fin.cons (fun z => complexInteraction z w) X) (insert 0 (B.image Fin.succ)) t -
        familyMean X B t * observableMean (fun z => complexInteraction z w) t := by
  rw [observableMeanDerivative_apply, familyMean_cons_insert]
  congr 1
  apply congrArg (fun Y => observableMean Y t)
  funext z
  exact mul_comm _ _

def tiltedCumulantDerivative (X : Fin s → SpinObservable n) (t : ComplexParameters n k) :
    ComplexParameters n k →L[ℂ] ℂ :=
  ∑ c : OrderedFinpartition s, (cumulantMobius c.length : ℂ) •
    ∑ j : Fin c.length, (∏ l ∈ Finset.univ.erase j, familyMean X (orderedBlock c l) t) •
      observableMeanDerivative (familyObservable X (orderedBlock c j)) t

theorem hasFDerivAt_tiltedCumulant (X : Fin s → SpinObservable n) (t : ComplexParameters n k)
    (ht : complexPartition t ≠ 0) :
    HasFDerivAt (tiltedCumulant X) (tiltedCumulantDerivative X t) t := by
  unfold tiltedCumulant tiltedCumulantDerivative orderedCumulant
  apply HasFDerivAt.fun_sum
  intro c _
  apply HasFDerivAt.const_mul
  apply HasFDerivAt.finsetProd
  intro j _
  exact hasFDerivAt_observableMean _ t ht

theorem analyticAt_tiltedCumulant (X : Fin s → SpinObservable n) (t : ComplexParameters n k)
    (ht : complexPartition t ≠ 0) : AnalyticAt ℂ (tiltedCumulant X) t := by
  apply Finset.analyticAt_fun_sum
  intro c _
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_prod
  intro j _
  exact analyticAt_observableMean _ t ht

theorem tiltedCumulantDerivative_apply (hs : 1 ≤ s) (X : Fin s → SpinObservable n)
    (t w : ComplexParameters n k) :
    tiltedCumulantDerivative X t w = tiltedCumulant (Fin.cons (fun z => complexInteraction z w) X) t := by
  rw [tiltedCumulant, orderedCumulant_extend_sub hs]
  simp only [tiltedCumulantDerivative, sum_apply, smul_apply, smul_eq_mul,
    familyMean_cons_image, familyMean_cons_singleton]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  let M := fun j : Fin c.length => familyMean X (orderedBlock c j) t
  let N := fun j : Fin c.length => familyMean (Fin.cons (fun z => complexInteraction z w) X)
    (insert 0 ((orderedBlock c j).image Fin.succ)) t
  let a := observableMean (fun z => complexInteraction z w) t
  have he (j : Fin c.length) :
      (∏ l ∈ Finset.univ.erase j, M l) * (N j - M j * a) =
        N j * (∏ l ∈ Finset.univ.erase j, M l) - a * ∏ l, M l := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    ring
  simp only [familyMeanDerivative_apply]
  change (∑ j : Fin c.length, (∏ l ∈ Finset.univ.erase j, M l) * (N j - M j * a)) = _
  simp only [he, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem fderiv_tiltedCumulant_apply (hs : 1 ≤ s) (X : Fin s → SpinObservable n)
    (t w : ComplexParameters n k) (ht : complexPartition t ≠ 0) :
    fderiv ℂ (tiltedCumulant X) t w = tiltedCumulant (Fin.cons (fun z => complexInteraction z w) X) t := by
  rw [(hasFDerivAt_tiltedCumulant X t ht).fderiv, tiltedCumulantDerivative_apply hs]

end

end TensorLB
