module

public import TensorLB.ComplexCoordinates

/-!
# The complex connected-coordinate map

The map is analytic at zero and has identity derivative. These local statements
do not yet assert a dimension-independent inverse neighborhood.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n k : ℕ}

def complexConnected (t : ComplexParameters n k) (I : ObservationIndex n k) : ℂ :=
  if k = 3 ∧ I.val.card = 3 then
    complexMoment t I.val -
      (∑ i ∈ I.val, complexMoment t {i} * complexMoment t (I.val.erase i)) +
        2 * ∏ i ∈ I.val, complexMoment t {i}
  else if k = 4 ∧ I.val.card = 4 then
    complexMoment t I.val - (1 / 2) *
      ∑ B ∈ I.val.powersetCard 2, complexMoment t B * complexMoment t (I.val \ B)
  else complexMoment t I.val

theorem complexMoment_zero_of_nonempty (B : Finset (Fin n)) (hB : B.Nonempty) :
    complexMoment (k := k) 0 B = 0 := by
  simp [complexMoment_zero, hB.ne_empty]

theorem hasFDerivAt_complexMoment_mul_zero (A B : Finset (Fin n))
    (hA : A.Nonempty) (hB : B.Nonempty) :
    HasFDerivAt (fun t : ComplexParameters n k => complexMoment t A * complexMoment t B)
      (0 : ComplexParameters n k →L[ℂ] ℂ) 0 := by
  convert! (hasFDerivAt_complexMoment_zero (k := k) A).mul
    (hasFDerivAt_complexMoment_zero B) using 1
  ext t
  simp [complexMoment_zero_of_nonempty A hA, complexMoment_zero_of_nonempty B hB]

theorem hasFDerivAt_complexMoment_prod_singletons_zero (I : Finset (Fin n))
    (hI : 2 ≤ I.card) :
    HasFDerivAt (fun t : ComplexParameters n k => ∏ i ∈ I, complexMoment t {i})
      (0 : ComplexParameters n k →L[ℂ] ℂ) 0 := by
  have hd := HasFDerivAt.finsetProd
    (u := I) (fun i _ => hasFDerivAt_complexMoment_zero (k := k) {i})
  convert! hd using 1
  symm
  apply Finset.sum_eq_zero
  intro i hi
  have he : (I.erase i).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hi]
    omega
  obtain ⟨j, hj⟩ := he
  rw [Finset.prod_eq_zero hj (complexMoment_zero_of_nonempty _ (Finset.singleton_nonempty j))]
  ext t
  simp

theorem complexConnected_zero : complexConnected (n := n) (k := k) 0 = 0 := by
  funext I
  unfold complexConnected
  have hI := complexMoment_zero_of_nonempty (k := k) I.val I.property.1
  split
  · simp [hI, complexMoment_zero, I.property.1.ne_empty]
  · split
    · rename_i h h4
      simp only [hI, Pi.zero_apply, zero_sub]
      have hs : (∑ B ∈ I.val.powersetCard 2,
          complexMoment (k := k) 0 B * complexMoment (k := k) 0 (I.val \ B)) = 0 := by
        apply Finset.sum_eq_zero
        intro B hB
        have hn : B.Nonempty := Finset.card_pos.mp (by
          rw [(Finset.mem_powersetCard.mp hB).2]
          decide)
        rw [complexMoment_zero_of_nonempty B hn, zero_mul]
      rw [hs, mul_zero, neg_zero]
    · exact hI

theorem analyticAt_complexConnected :
    AnalyticAt ℂ (complexConnected (n := n) (k := k)) 0 := by
  apply analyticAt_pi_iff.mpr
  intro I
  unfold complexConnected
  split
  · apply AnalyticAt.add
    · apply (analyticAt_complexMoment_zero I.val).sub
      exact Finset.analyticAt_fun_sum _ (fun i _ =>
        (analyticAt_complexMoment_zero {i}).mul (analyticAt_complexMoment_zero (I.val.erase i)))
    · exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun i _ =>
        analyticAt_complexMoment_zero {i}))
  · split
    · apply (analyticAt_complexMoment_zero I.val).sub
      exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ (fun B _ =>
        (analyticAt_complexMoment_zero B).mul (analyticAt_complexMoment_zero (I.val \ B))))
    · exact analyticAt_complexMoment_zero I.val

theorem hasFDerivAt_complexConnected_component (I : ObservationIndex n k) :
    HasFDerivAt (fun t : ComplexParameters n k => complexConnected t I)
      (ContinuousLinearMap.proj I : ComplexParameters n k →L[ℂ] ℂ) 0 := by
  have hlead : HasFDerivAt (fun t : ComplexParameters n k => complexMoment t I.val)
      (ContinuousLinearMap.proj I : ComplexParameters n k →L[ℂ] ℂ) 0 := by
    simpa only [complexMomentDerivative_observation] using
      hasFDerivAt_complexMoment_zero (k := k) I.val
  unfold complexConnected
  split
  · rename_i h3
    have hsum : HasFDerivAt (fun t : ComplexParameters n k =>
        ∑ i ∈ I.val, complexMoment t {i} * complexMoment t (I.val.erase i))
        (0 : ComplexParameters n k →L[ℂ] ℂ) 0 := by
      have hd := HasFDerivAt.sum (u := I.val) (fun i hi =>
        hasFDerivAt_complexMoment_mul_zero (k := k) {i} (I.val.erase i)
          (Finset.singleton_nonempty _) (Finset.card_pos.mp (by
            rw [Finset.card_erase_of_mem hi, h3.2]
            decide)))
      simp only [Finset.sum_const_zero] at hd
      convert! hd using 1
      ext t
      simp
    have hp := (hasFDerivAt_complexMoment_prod_singletons_zero (k := k) I.val
      (by omega)).const_mul (2 : ℂ)
    convert! (hlead.sub hsum).add hp using 1
    ext t
    simp
  · split
    · rename_i h3 h4
      have hsum : HasFDerivAt (fun t : ComplexParameters n k =>
          ∑ B ∈ I.val.powersetCard 2, complexMoment t B * complexMoment t (I.val \ B))
          (0 : ComplexParameters n k →L[ℂ] ℂ) 0 := by
        have hd := HasFDerivAt.sum (u := I.val.powersetCard 2) (fun B hB =>
          hasFDerivAt_complexMoment_mul_zero (k := k) B (I.val \ B)
            (Finset.card_pos.mp (by rw [(Finset.mem_powersetCard.mp hB).2]; decide))
            (Finset.card_pos.mp (by
              rw [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp hB).1,
                h4.2, (Finset.mem_powersetCard.mp hB).2]
              decide)))
        simp only [Finset.sum_const_zero] at hd
        convert! hd using 1
        ext t
        simp
      convert! hlead.sub (hsum.const_mul (1 / 2 : ℂ)) using 1
      ext t
      simp
    · exact hlead

theorem hasFDerivAt_complexConnected :
    HasFDerivAt (complexConnected (n := n) (k := k))
      (ContinuousLinearMap.id ℂ (ComplexParameters n k)) 0 := by
  apply hasFDerivAt_pi''
  intro I
  simpa only [ContinuousLinearMap.comp_id] using hasFDerivAt_complexConnected_component I

theorem complexConnected_ofReal (t : ObservationIndex n k → ℝ) (I : ObservationIndex n k) :
    complexConnected (fun J => (t J : ℂ)) I = (connectedCoordinate t I : ℂ) := by
  unfold complexConnected connectedCoordinate
  split
  · simp only [complexMoment_ofReal, Complex.ofReal_add, Complex.ofReal_sub,
      Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_ofNat]
  · split
    · simp only [complexMoment_ofReal, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_sum]
    · exact complexMoment_ofReal I.val t

end

end TensorLB
