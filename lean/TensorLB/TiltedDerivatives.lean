module

public import TensorLB.TiltedCumulant
public import TensorLB.CumulantRelabel
public import TensorLB.RootedOutput

/-!
# Iterated derivatives of tilted cumulants

Each derivative inserts its interaction observable. At the origin the tilted
expectation is the uniform Boolean expectation, so coordinate derivatives are
the character cumulants used in the tree estimate.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical Topology

noncomputable section

variable {n k s : ℕ}

def insertInteractionFamily (X : Fin s → SpinObservable n) :
    (d : ℕ) → (Fin d → ComplexParameters n k) → Fin (s + d) → SpinObservable n
  | 0, _ => X
  | d + 1, w => Fin.cons (fun z => complexInteraction z (w 0))
      (insertInteractionFamily X d (Fin.tail w))

theorem iteratedFDeriv_tiltedCumulant (hs : 1 ≤ s) (X : Fin s → SpinObservable n)
    (d : ℕ) (w : Fin d → ComplexParameters n k) (t : ComplexParameters n k)
    (ht : complexPartition t ≠ 0) :
    iteratedFDeriv ℂ d (tiltedCumulant X) t w =
      tiltedCumulant (insertInteractionFamily X d w) t := by
  induction d generalizing t with
  | zero => rfl
  | succ d ih =>
    have ha : AnalyticOnNhd ℂ (tiltedCumulant X)
        {u : ComplexParameters n k | complexPartition u ≠ 0} :=
      fun u hu => analyticAt_tiltedCumulant X u hu
    rw [((ha.iteratedFDeriv d t ht).differentiableAt).iteratedFDeriv_succ_apply_left']
    have he : (fun u => iteratedFDeriv ℂ d (tiltedCumulant X) u (Fin.tail w)) =ᶠ[𝓝 t]
        (fun u => tiltedCumulant (insertInteractionFamily X d (Fin.tail w)) u) := by
      filter_upwards [(analyticAt_complexPartition t).continuousAt.eventually_ne ht] with u hu
      exact ih (Fin.tail w) u hu
    rw [he.fderiv_eq]
    exact fderiv_tiltedCumulant_apply (by omega) _ t (w 0) ht

theorem familyMean_character_zero (X : Fin s → Finset (Fin n)) (B : Finset (Fin s)) :
    familyMean (fun j z => (character (X j) z : ℂ)) B (0 : ComplexParameters n k) =
      (characterMoment X B : ℂ) := by
  simp only [familyMean, observableMean, observableNumerator, complexPartition_zero,
    div_one, map_zero, Complex.exp_zero, mul_one, familyObservable, characterMoment,
    Fintype.expect_eq_sum_div_card, Complex.ofReal_div, Complex.ofReal_sum,
    Complex.ofReal_natCast, Complex.ofReal_prod]
  rw [div_eq_mul_inv, mul_comm]

theorem tiltedCumulant_character_zero (X : Fin s → Finset (Fin n)) :
    tiltedCumulant (fun j z => (character (X j) z : ℂ)) (0 : ComplexParameters n k) =
      (jointCharacterCumulant X : ℂ) := by
  simp only [tiltedCumulant, familyMean_character_zero]
  exact orderedCumulant_characterMoment X

def insertedLabel (s : ℕ) : (d : ℕ) → Fin (s + d) → Fin s ⊕ Fin d
  | 0 => Sum.inl
  | d + 1 => Fin.cons (Sum.inr 0) (Sum.map id Fin.succ ∘ insertedLabel s d)

theorem insertedLabel_bijective (s d : ℕ) : Function.Bijective (insertedLabel s d) := by
  induction d with
  | zero =>
    constructor
    · intro a b h; exact Sum.inl.inj h
    · intro a; cases a with
      | inl a => exact ⟨a, rfl⟩
      | inr a => exact Fin.elim0 a
  | succ d ih =>
    have hm : Function.Injective (Sum.map (id : Fin s → Fin s) (Fin.succ : Fin d → Fin (d+1))) :=
      Sum.map_injective.mpr ⟨Function.injective_id, Fin.succ_injective d⟩
    constructor
    · intro a b h
      cases a using Fin.cases with
      | zero =>
        cases b using Fin.cases with
        | zero => rfl
        | succ b =>
          simp only [insertedLabel, Fin.cons_zero, Fin.cons_succ, Function.comp_apply] at h
          cases he : insertedLabel s d b <;> simp [he, eq_comm] at h
      | succ a =>
        cases b using Fin.cases with
        | zero =>
          simp only [insertedLabel, Fin.cons_zero, Fin.cons_succ, Function.comp_apply] at h
          cases he : insertedLabel s d a <;> simp [he] at h
        | succ b => exact congrArg Fin.succ (ih.1 (hm h))
    · intro a
      cases a with
      | inl a =>
        obtain ⟨b, hb⟩ := ih.2 (Sum.inl a)
        exact ⟨b.succ, by simp [insertedLabel, hb]⟩
      | inr a =>
        cases a using Fin.cases with
        | zero => exact ⟨0, rfl⟩
        | succ a =>
          obtain ⟨b, hb⟩ := ih.2 (Sum.inr a)
          exact ⟨b.succ, by simp [insertedLabel, hb]⟩

def insertedEquiv (s d : ℕ) : Fin (s + d) ≃ Fin s ⊕ Fin d :=
  Equiv.ofBijective (insertedLabel s d) (insertedLabel_bijective s d)

def parameterBasis (I : ObservationIndex n k) : ComplexParameters n k := Pi.single I 1

theorem complexInteraction_parameterBasis (z : Fin n → Bool) (I : ObservationIndex n k) :
    complexInteraction z (parameterBasis I) = (character I.val z : ℂ) := by
  simp [complexInteraction_apply, parameterBasis, Pi.single_apply]

theorem insertInteractionFamily_basis (X : Fin s → Finset (Fin n))
    (d : ℕ) (J : Fin d → ObservationIndex n k) :
    insertInteractionFamily (fun j z => (character (X j) z : ℂ)) d (fun j => parameterBasis (J j)) =
      fun a z => (character (Sum.elim X (fun j => (J j).val) (insertedLabel s d a)) z : ℂ) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    funext a z
    cases a using Fin.cases with
    | zero => exact complexInteraction_parameterBasis z (J 0)
    | succ a =>
      change insertInteractionFamily _ d (fun j => parameterBasis (J j.succ)) a z = _
      rw [ih]
      cases he : insertedLabel s d a <;> simp [insertedLabel, he]

theorem iteratedFDeriv_tiltedCumulant_basis (hs : 1 ≤ s) (X : Fin s → Finset (Fin n))
    (d : ℕ) (J : Fin d → ObservationIndex n k) :
    iteratedFDeriv ℂ d (tiltedCumulant (fun j z => (character (X j) z : ℂ)))
      (0 : ComplexParameters n k) (fun j => parameterBasis (J j)) =
      (jointCharacterCumulant (Sum.elim X (fun j => (J j).val)) : ℂ) := by
  rw [iteratedFDeriv_tiltedCumulant hs _ _ _ _ (by simp), insertInteractionFamily_basis,
    tiltedCumulant_character_zero]
  exact congrArg (fun a : ℝ => (a : ℂ))
    (jointCharacterCumulant_equiv (insertedEquiv s d) _).symm

theorem iteratedFDeriv_marked_basis (B : Finset (Fin n)) (e : Fin s ≃ B) (hs : 1 ≤ s)
    (d : ℕ) (J : Fin d → ObservationIndex n k) :
    iteratedFDeriv ℂ d (tiltedCumulant (fun j z => (character {(e j).val} z : ℂ)))
      (0 : ComplexParameters n k) (fun j => parameterBasis (J j)) = (outputCumulant B J : ℂ) := by
  rw [iteratedFDeriv_tiltedCumulant_basis hs]
  have h := (jointCharacterCumulant_equiv (Equiv.sumCongr e (Equiv.refl (Fin d)))
      (outputCharacterFamily B J)).symm
  have he : outputCharacterFamily B J ∘ Equiv.sumCongr e (Equiv.refl (Fin d)) =
      Sum.elim (fun j => {(e j).val}) (fun j => (J j).val) := by
    funext a
    cases a <;> rfl
  rw [he] at h
  exact congrArg (fun a : ℝ => (a : ℂ)) h

theorem multilinear_parameterBasis {d : ℕ}
    (f : ContinuousMultilinearMap ℂ (fun _ : Fin d => ComplexParameters n k) ℂ)
    (w : Fin d → ComplexParameters n k) :
    f w = ∑ J : Fin d → ObservationIndex n k,
      f (fun j => parameterBasis (J j)) * ∏ j, w j (J j) := by
  have hw : w = fun j => ∑ I : ObservationIndex n k, w j I • parameterBasis I := by
    funext j I
    simp [parameterBasis, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  rw [f.map_sum]
  apply Finset.sum_congr rfl
  intro J _
  rw [f.map_smul_univ]
  exact mul_comm _ _

theorem iteratedFDeriv_marked (B : Finset (Fin n)) (e : Fin s ≃ B) (hs : 1 ≤ s)
    (d : ℕ) (w : Fin d → ComplexParameters n k) :
    iteratedFDeriv ℂ d (tiltedCumulant (fun j z => (character {(e j).val} z : ℂ)))
      (0 : ComplexParameters n k) w =
      ∑ J : Fin d → ObservationIndex n k, (outputCumulant B J : ℂ) * ∏ j, w j (J j) := by
  rw [multilinear_parameterBasis]
  apply Finset.sum_congr rfl
  intro J _
  rw [iteratedFDeriv_marked_basis B e hs]

end

end TensorLB
