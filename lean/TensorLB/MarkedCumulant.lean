module

public import TensorLB.TiltedDerivatives
public import TensorLB.SmallCumulants
public import TensorLB.SignSymmetry

/-! # Connected coordinates as cumulants of the marked spins -/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n k s : ℕ}

def markedEmbedding (B : Finset (Fin n)) (e : Fin s ≃ B) : Fin s ↪ Fin n :=
  ⟨fun j => (e j).val, Subtype.val_injective.comp e.injective⟩

theorem markedEmbedding_univ (B : Finset (Fin n)) (e : Fin s ≃ B) :
    Finset.univ.image (markedEmbedding B e) = B := by
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩; exact (e j).property
  · intro hi
    obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
    exact ⟨j, congrArg Subtype.val hj⟩

theorem familyMean_marked (B : Finset (Fin n)) (e : Fin s ≃ B) (A : Finset (Fin s))
    (t : ComplexParameters n k) :
    familyMean (fun j z => (character {(e j).val} z : ℂ)) A t =
      complexMoment t (A.image (markedEmbedding B e)) := by
  rw [familyMean, ← observableMean_character]
  congr 1
  funext z
  simp only [familyObservable, character, Finset.prod_singleton, Complex.ofReal_prod,
    Finset.prod_image (fun _ _ _ _ h => (markedEmbedding B e).injective h)]
  rfl

theorem signTwist_all_negative_even (hk : k % 2 = 0) (t : ComplexParameters n k) :
    signTwist (fun _ => false) t = t := by
  ext I
  rw [signTwist_apply]
  have h : character I.val (fun _ => false) = 1 := by
    simp only [character, sign, Finset.prod_const]
    rw [neg_one_pow_eq_pow_mod_two, I.property.2.2, hk]
    simp
  simp [h]

theorem complexMoment_singleton_even (hk : k % 2 = 0) (t : ComplexParameters n k) (i : Fin n) :
    complexMoment t {i} = 0 := by
  have h := complexMoment_twist (fun _ => false) {i} t
  rw [signTwist_all_negative_even hk] at h
  have hc : character {i} (fun _ => false) = -1 := by simp [character, sign]
  rw [hc] at h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  apply Complex.ext <;> simp at hr hi ⊢ <;> linarith

theorem sum_markedEmbedding (B : Finset (Fin n)) (e : Fin s ≃ B) (f : Fin n → ℂ) :
    (∑ j : Fin s, f (markedEmbedding B e j)) = ∑ i ∈ B, f i := by
  simpa only [markedEmbedding_univ] using
    (Finset.sum_image (s := Finset.univ) (f := f)
      (fun _ _ _ _ h => (markedEmbedding B e).injective h)).symm

theorem prod_markedEmbedding (B : Finset (Fin n)) (e : Fin s ≃ B) (f : Fin n → ℂ) :
    (∏ j : Fin s, f (markedEmbedding B e j)) = ∏ i ∈ B, f i := by
  simpa only [markedEmbedding_univ] using
    (Finset.prod_image (s := Finset.univ) (f := f)
      (fun _ _ _ _ h => (markedEmbedding B e).injective h)).symm

theorem sum_powersetCard_markedEmbedding (B : Finset (Fin n)) (e : Fin s ≃ B)
    (f : Finset (Fin n) → ℂ) :
    (∑ A ∈ (Finset.univ : Finset (Fin s)).powersetCard 2, f (A.image (markedEmbedding B e))) =
      ∑ C ∈ B.powersetCard 2, f C := by
  have hu : (Finset.univ : Finset (Fin s)).map (markedEmbedding B e) = B := by
    simpa only [Finset.map_eq_image] using markedEmbedding_univ B e
  conv_rhs => rw [← hu, Finset.powersetCard_map, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro A _
  change f (A.image (markedEmbedding B e)) = f (A.map (markedEmbedding B e))
  rw [Finset.map_eq_image]

theorem tiltedCumulant_marked_three (B : Finset (Fin n)) (e : Fin 3 ≃ B)
    (t : ComplexParameters n k) :
    tiltedCumulant (fun j z => (character {(e j).val} z : ℂ)) t =
      complexMoment t B - (∑ i ∈ B, complexMoment t {i} * complexMoment t (B.erase i)) +
        2 * ∏ i ∈ B, complexMoment t {i} := by
  rw [tiltedCumulant, orderedCumulant_three_symmetric]
  simp only [familyMean_marked, Finset.image_singleton,
    Finset.image_erase (markedEmbedding B e).injective, markedEmbedding_univ]
  rw [sum_markedEmbedding B e (fun i => complexMoment t {i} * complexMoment t (B.erase i)),
    prod_markedEmbedding B e (fun i => complexMoment t {i})]

theorem tiltedCumulant_marked_four (B : Finset (Fin n)) (e : Fin 4 ≃ B)
    (t : ComplexParameters n 4) :
    tiltedCumulant (fun j z => (character {(e j).val} z : ℂ)) t =
      complexMoment t B - (1/2) * ∑ A ∈ B.powersetCard 2,
        complexMoment t A * complexMoment t (B \ A) := by
  rw [tiltedCumulant, orderedCumulant_four_symmetric]
  · simp only [familyMean_marked, Finset.image_sdiff _ _ (markedEmbedding B e).injective,
      markedEmbedding_univ]
    rw [sum_powersetCard_markedEmbedding B e (fun A => complexMoment t A * complexMoment t (B \ A))]
  · intro i
    rw [familyMean_marked, Finset.image_singleton]
    exact complexMoment_singleton_even (by decide) t _

theorem tiltedCumulant_marked_one (B : Finset (Fin n)) (e : Fin 1 ≃ B)
    (t : ComplexParameters n k) :
    tiltedCumulant (fun j z => (character {(e j).val} z : ℂ)) t = complexMoment t B := by
  rw [tiltedCumulant, orderedCumulant_one, familyMean_marked]
  have hu : ({0} : Finset (Fin 1)) = Finset.univ := by decide
  rw [hu, markedEmbedding_univ]

theorem tiltedCumulant_marked_two (B : Finset (Fin n)) (e : Fin 2 ≃ B)
    (t : ComplexParameters n 4) :
    tiltedCumulant (fun j z => (character {(e j).val} z : ℂ)) t = complexMoment t B := by
  rw [tiltedCumulant, orderedCumulant_two]
  simp only [familyMean_marked, Finset.image_singleton, complexMoment_singleton_even (k := 4) (by decide),
    mul_zero, sub_zero]
  have hu : ({0,1} : Finset (Fin 2)) = Finset.univ := by decide
  rw [hu, markedEmbedding_univ]

theorem tiltedCumulant_finCongr {r : ℕ} (h : s = r) (X : Fin s → SpinObservable n)
    (t : ComplexParameters n k) :
    tiltedCumulant (X ∘ (finCongr h).symm) t = tiltedCumulant X t := by
  subst r
  rfl

theorem tiltedCumulant_eq_complexConnected (hk : k = 3 ∨ k = 4) (I : ObservationIndex n k)
    (e : Fin I.val.card ≃ I.val) (t : ComplexParameters n k) :
    tiltedCumulant (fun j z => (character {(e j).val} z : ℂ)) t = complexConnected t I := by
  have hpos := Finset.card_pos.mpr I.property.1
  have hle := I.property.2.1
  have hpar := I.property.2.2
  rcases hk with rfl | rfl
  · have hc : I.val.card = 1 ∨ I.val.card = 3 := by omega
    rcases hc with hc | hc
    · have he := tiltedCumulant_marked_one I.val ((finCongr hc).symm.trans e) t
      rw [show (fun j z => (character {(((finCongr hc).symm.trans e) j).val} z : ℂ)) =
        (fun j z => (character {(e j).val} z : ℂ)) ∘ (finCongr hc).symm from rfl,
        tiltedCumulant_finCongr] at he
      simpa [complexConnected, hc] using he
    · have he := tiltedCumulant_marked_three I.val ((finCongr hc).symm.trans e) t
      rw [show (fun j z => (character {(((finCongr hc).symm.trans e) j).val} z : ℂ)) =
        (fun j z => (character {(e j).val} z : ℂ)) ∘ (finCongr hc).symm from rfl,
        tiltedCumulant_finCongr] at he
      simpa [complexConnected, hc] using he
  · have hc : I.val.card = 2 ∨ I.val.card = 4 := by omega
    rcases hc with hc | hc
    · have he := tiltedCumulant_marked_two I.val ((finCongr hc).symm.trans e) t
      rw [show (fun j z => (character {(((finCongr hc).symm.trans e) j).val} z : ℂ)) =
        (fun j z => (character {(e j).val} z : ℂ)) ∘ (finCongr hc).symm from rfl,
        tiltedCumulant_finCongr] at he
      simpa [complexConnected, hc] using he
    · have he := tiltedCumulant_marked_four I.val ((finCongr hc).symm.trans e) t
      rw [show (fun j z => (character {(((finCongr hc).symm.trans e) j).val} z : ℂ)) =
        (fun j z => (character {(e j).val} z : ℂ)) ∘ (finCongr hc).symm from rfl,
        tiltedCumulant_finCongr] at he
      simpa [complexConnected, hc] using he

end

end TensorLB
