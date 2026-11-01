module

public import TensorLB.RealResponse

/-!
# Coordinate sign symmetry

Multiplying each spin by a fixed sign vector is a permutation of the Boolean
cube. It acts diagonally on interaction parameters and on tilted moments.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical Topology

noncomputable section

variable {n k : ℕ}

def spinFlip (ε : Fin n → Bool) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun z i := if ε i then z i else !(z i)
  invFun z i := if ε i then z i else !(z i)
  left_inv z := by funext i; cases he : ε i <;> simp [he]
  right_inv z := by funext i; cases he : ε i <;> simp [he]

theorem sign_spinFlip (ε z : Fin n → Bool) (i : Fin n) :
    sign (spinFlip ε z i) = sign (ε i) * sign (z i) := by
  cases he : ε i <;> cases hz : z i <;> simp [spinFlip, he, hz, sign]

theorem character_spinFlip (ε z : Fin n → Bool) (B : Finset (Fin n)) :
    character B (spinFlip ε z) = character B ε * character B z := by
  simp only [character, sign_spinFlip, Finset.prod_mul_distrib]

def signTwist (ε : Fin n → Bool) : ComplexParameters n k →L[ℂ] ComplexParameters n k :=
  ContinuousLinearMap.pi (fun I => (character I.val ε : ℂ) • ContinuousLinearMap.proj I)

@[simp] theorem signTwist_apply (ε : Fin n → Bool) (t : ComplexParameters n k)
    (I : ObservationIndex n k) : signTwist ε t I = (character I.val ε : ℂ) * t I := by
  simp [signTwist]

theorem signTwist_involutive (ε : Fin n → Bool) :
    Function.Involutive (signTwist (k := k) ε) := by
  intro t
  ext I
  simp only [signTwist_apply, ← mul_assoc, ← sq, ← Complex.ofReal_pow, character_sq,
    Complex.ofReal_one, one_mul]

theorem complexInteraction_twist (ε z : Fin n → Bool) (t : ComplexParameters n k) :
    complexInteraction z (signTwist ε t) = complexInteraction (spinFlip ε z) t := by
  simp only [complexInteraction_apply, signTwist_apply, character_spinFlip, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro I _
  ring

theorem complexNumerator_twist (ε : Fin n → Bool) (B : Finset (Fin n))
    (t : ComplexParameters n k) :
    complexNumerator B (signTwist ε t) = (character B ε : ℂ) * complexNumerator B t := by
  unfold complexNumerator
  have hs := (spinFlip ε).sum_comp (fun z =>
    (character B z : ℂ) * Complex.exp (complexInteraction z (signTwist ε t)))
  rw [← hs]
  simp only [character_spinFlip, complexInteraction_twist,
    Complex.ofReal_mul]
  have hflip : ∀ z : Fin n → Bool, spinFlip ε (spinFlip ε z) = z := by
    intro z
    exact (spinFlip ε).left_inv z
  simp only [hflip]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

theorem complexPartition_twist (ε : Fin n → Bool) (t : ComplexParameters n k) :
    complexPartition (signTwist ε t) = complexPartition t := by
  simp [complexPartition, complexNumerator_twist]

theorem complexMoment_twist (ε : Fin n → Bool) (B : Finset (Fin n))
    (t : ComplexParameters n k) :
    complexMoment (signTwist ε t) B = (character B ε : ℂ) * complexMoment t B := by
  simp only [complexMoment, complexNumerator_twist, complexPartition_twist, mul_div_assoc]

theorem character_singleton_mul_erase (ε : Fin n → Bool) (I : Finset (Fin n))
    {i : Fin n} (hi : i ∈ I) :
    character {i} ε * character (I.erase i) ε = character I ε := by
  simpa only [character, Finset.prod_singleton] using
    Finset.mul_prod_erase I (fun j => sign (ε j)) hi

theorem character_mul_sdiff (ε : Fin n → Bool) (I B : Finset (Fin n)) (hB : B ⊆ I) :
    character B ε * character (I \ B) ε = character I ε := by
  simpa only [character, Finset.inter_eq_right.mpr hB] using
    Finset.prod_inter_mul_prod_sdiff I B (fun j => sign (ε j))

theorem complexMoment_twist_split (ε : Fin n → Bool) (t : ComplexParameters n k)
    (B C I : Finset (Fin n)) (h : character B ε * character C ε = character I ε) :
    complexMoment (signTwist ε t) B * complexMoment (signTwist ε t) C =
      (character I ε : ℂ) * (complexMoment t B * complexMoment t C) := by
  rw [complexMoment_twist, complexMoment_twist]
  calc
    _ = ((character B ε : ℂ) * (character C ε : ℂ)) *
        (complexMoment t B * complexMoment t C) := by ring
    _ = _ := by rw [← Complex.ofReal_mul, h]

theorem complexConnected_twist (ε : Fin n → Bool) (t : ComplexParameters n k) :
    complexConnected (signTwist ε t) = signTwist ε (complexConnected t) := by
  ext I
  rw [signTwist_apply]
  unfold complexConnected
  split
  · have hs : (∑ i ∈ I.val, complexMoment (signTwist ε t) {i} *
        complexMoment (signTwist ε t) (I.val.erase i)) =
        (character I.val ε : ℂ) * ∑ i ∈ I.val, complexMoment t {i} *
          complexMoment t (I.val.erase i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact complexMoment_twist_split ε t _ _ _ (character_singleton_mul_erase ε I.val hi)
    have hp : (∏ i ∈ I.val, complexMoment (signTwist ε t) {i}) =
        (character I.val ε : ℂ) * ∏ i ∈ I.val, complexMoment t {i} := by
      simp only [complexMoment_twist, Finset.prod_mul_distrib, ← Complex.ofReal_prod]
      simp [character]
    rw [hs, hp, complexMoment_twist]
    ring
  · split
    · have hs : (∑ B ∈ I.val.powersetCard 2, complexMoment (signTwist ε t) B *
          complexMoment (signTwist ε t) (I.val \ B)) =
          (character I.val ε : ℂ) * ∑ B ∈ I.val.powersetCard 2,
            complexMoment t B * complexMoment t (I.val \ B) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro B hB
        exact complexMoment_twist_split ε t _ _ _
          (character_mul_sdiff ε I.val B (Finset.mem_powersetCard.mp hB).1)
      rw [hs, complexMoment_twist]
      ring
    · exact complexMoment_twist ε I.val t

theorem complexInverse_twist (ε : Fin n → Bool) :
    ∀ᶠ q : ComplexParameters n k in 𝓝 0,
      complexInverse (signTwist ε q) = signTwist ε (complexInverse q) := by
  have hc : ContinuousAt (fun q : ComplexParameters n k => signTwist ε (complexInverse q)) 0 :=
    (signTwist ε).continuous.continuousAt.comp analyticAt_complexInverse.continuousAt
  have ht : Filter.Tendsto (fun q : ComplexParameters n k => signTwist ε (complexInverse q))
      (𝓝 0) (𝓝 0) := by simpa only [complexInverse_zero, map_zero] using hc.tendsto
  filter_upwards [ht.eventually (complexInverse_left (n := n) (k := k)),
    complexInverse_right (n := n) (k := k)] with q hleft hright
  rwa [complexConnected_twist, hright] at hleft

theorem complexResponse_twist (τ : ℝ) (A : Finset (Fin n)) (ε : Fin n → Bool) :
    ∀ᶠ q : ComplexParameters n k in 𝓝 0,
      complexResponse τ A (signTwist ε q) = (character A ε : ℂ) * complexResponse τ A q := by
  filter_upwards [complexInverse_twist (k := k) ε] with q hq
  simp only [complexResponse, hq, ← map_smul, complexMoment_twist]

def realSignTwist (ε : Fin n → Bool) :
    (ObservationIndex n k → ℝ) →L[ℝ] (ObservationIndex n k → ℝ) :=
  ContinuousLinearMap.pi (fun I => character I.val ε • ContinuousLinearMap.proj I)

@[simp] theorem realSignTwist_apply (ε : Fin n → Bool) (t : ObservationIndex n k → ℝ)
    (I : ObservationIndex n k) : realSignTwist ε t I = character I.val ε * t I := by
  simp [realSignTwist]

theorem complexify_realSignTwist (ε : Fin n → Bool) (t : ObservationIndex n k → ℝ) :
    complexifyParameters (realSignTwist ε t) = signTwist ε (complexifyParameters t) := by
  ext I
  simp

theorem realResponse_twist (τ : ℝ) (A : Finset (Fin n)) (ε : Fin n → Bool) :
    ∀ᶠ q : ObservationIndex n k → ℝ in 𝓝 0,
      realResponse τ A (realSignTwist ε q) = character A ε * realResponse τ A q := by
  have ht : Filter.Tendsto (complexifyParameters (n := n) (k := k)) (𝓝 0) (𝓝 0) :=
    complexifyParameters.continuous.tendsto' _ _ (map_zero _)
  filter_upwards [ht.eventually (complexResponse_twist τ A ε)] with q hq
  have hr := congrArg Complex.re hq
  simpa only [realResponse, complexify_realSignTwist, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using hr

end

end TensorLB
