module

public import TensorLB.CumulantRelabel

/-!
# Rooting and enumerating output supports

Fixing an incident coordinate as root embeds each output support and interaction
tuple into the marked/interaction state assignments used by the weighted tree
estimate. Ordering the remaining output coordinates makes this map injective.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n k p d : ℕ}

abbrev RootedOutput (n : ℕ) (i : Fin n) (p : ℕ) :=
  {B : Finset (Fin n) // i ∈ B ∧ B.card = p + 1}

def outputNonrootEnumeration {i : Fin n} (B : RootedOutput n i p) : Fin p ≃ (B.val.erase i) :=
  (B.val.erase i).orderIsoOfFin (by rw [Finset.card_erase_of_mem B.property.1, B.property.2]; omega) |>.toEquiv

def rootedOutputStates {i : Fin n} (B : RootedOutput n i p) (J : Fin d → ObservationIndex n k) :
    (Fin p ⊕ Fin d) → TreeState n k
  | .inl a => .inr (outputNonrootEnumeration B a).val
  | .inr j => .inl (J j)

theorem outputNonrootEnumeration_image {i : Fin n} (B : RootedOutput n i p) :
    Finset.univ.image (fun a => (outputNonrootEnumeration B a).val) = B.val.erase i := by
  ext x
  constructor
  · rintro hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact (outputNonrootEnumeration B a).property
  · intro hx
    refine Finset.mem_image.mpr ⟨(outputNonrootEnumeration B).symm ⟨x, hx⟩, Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val ((outputNonrootEnumeration B).apply_symm_apply ⟨x, hx⟩)

theorem rootedOutputStates_injective (i : Fin n) :
    Function.Injective (fun z : RootedOutput n i p × (Fin d → ObservationIndex n k) =>
      rootedOutputStates z.1 z.2) := by
  rintro ⟨B, J⟩ ⟨C, K⟩ h
  have he : ∀ a : Fin p, (outputNonrootEnumeration B a).val = (outputNonrootEnumeration C a).val := by
    intro a
    exact Sum.inr.inj (congrFun h (.inl a))
  have hBC : B.val = C.val := by
    have herase : B.val.erase i = C.val.erase i := by
      rw [← outputNonrootEnumeration_image B, ← outputNonrootEnumeration_image C]
      exact congrArg (fun f : Fin p → Fin n => Finset.univ.image f) (funext he)
    have hi := congrArg (insert i) herase
    simpa only [Finset.insert_erase B.property.1, Finset.insert_erase C.property.1] using hi
  apply Prod.ext (Subtype.ext hBC)
  funext j
  exact Sum.inl.inj (congrFun h (.inr j))

theorem prod_rootedOutputStates_weight {i : Fin n} (B : RootedOutput n i p)
    (J : Fin d → ObservationIndex n k) (w : Fin d → ComplexParameters n k) :
    (∏ v, mixedVertexWeight w v (rootedOutputStates B J v)) = ∏ j, ‖w j (J j)‖ := by
  rw [Fintype.prod_sum_type]
  simp only [rootedOutputStates, mixedVertexWeight, Finset.prod_const_one, one_mul]

def outputCharacterFamily (B : Finset (Fin n)) (J : Fin d → ObservationIndex n k) :
    (B ⊕ Fin d) → Finset (Fin n)
  | .inl i => {i.val}
  | .inr j => (J j).val

def outputCumulant (B : Finset (Fin n)) (J : Fin d → ObservationIndex n k) : ℝ :=
  jointCharacterCumulant (outputCharacterFamily B J)

def outputRootMap {i : Fin n} (B : RootedOutput n i p) :
    Option (Fin p ⊕ Fin d) → (B.val ⊕ Fin d)
  | none => .inl ⟨i, B.property.1⟩
  | some (.inl a) => .inl ⟨(outputNonrootEnumeration B a).val,
      Finset.mem_of_mem_erase (outputNonrootEnumeration B a).property⟩
  | some (.inr j) => .inr j

def outputRootEquiv {i : Fin n} (B : RootedOutput n i p) :
    Option (Fin p ⊕ Fin d) ≃ (B.val ⊕ Fin d) :=
  Equiv.ofBijective (outputRootMap B) ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨by
    intro z
    cases z with
    | inl a =>
      by_cases ha : a.val = i
      · refine ⟨none, ?_⟩
        apply congrArg Sum.inl
        exact Subtype.ext ha.symm
      · let b : B.val.erase i := ⟨a.val, Finset.mem_erase.mpr ⟨ha, a.property⟩⟩
        refine ⟨some (.inl ((outputNonrootEnumeration B).symm b)), ?_⟩
        apply congrArg Sum.inl
        apply Subtype.ext
        exact congrArg (fun x : B.val.erase i => x.val)
          ((outputNonrootEnumeration B).apply_symm_apply b)
    | inr j => exact ⟨some (.inr j), rfl⟩,
    by simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_coe, B.property.2]; omega⟩)

theorem outputCumulant_rooted {i : Fin n} (B : RootedOutput n i p)
    (J : Fin d → ObservationIndex n k) :
    outputCumulant B.val J =
      jointCharacterCumulant (stateCharacterFamily (.inr i) (rootedOutputStates B J)) := by
  rw [outputCumulant, jointCharacterCumulant_equiv (outputRootEquiv B)]
  congr 1
  funext z
  cases z with
  | none => rfl
  | some z => cases z <;> rfl

theorem sum_outputCumulant_le_states (i : Fin n) (w : Fin d → ComplexParameters n k) :
    (∑ B : RootedOutput n i p, ∑ J : Fin d → ObservationIndex n k,
      |outputCumulant B.val J| * ∏ j, ‖w j (J j)‖) ≤
      ∑ x : (Fin p ⊕ Fin d) → TreeState n k,
        |jointCharacterCumulant (stateCharacterFamily (.inr i) x)| *
          ∏ v, mixedVertexWeight w v (x v) := by
  let f := fun x : (Fin p ⊕ Fin d) → TreeState n k =>
    |jointCharacterCumulant (stateCharacterFamily (.inr i) x)| * ∏ v, mixedVertexWeight w v (x v)
  let g := fun z : RootedOutput n i p × (Fin d → ObservationIndex n k) => rootedOutputStates z.1 z.2
  have he : (∑ B : RootedOutput n i p, ∑ J : Fin d → ObservationIndex n k,
      |outputCumulant B.val J| * ∏ j, ‖w j (J j)‖) = ∑ z, f (g z) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro B _
    apply Finset.sum_congr rfl
    intro J _
    dsimp only [f, g]
    rw [outputCumulant_rooted, prod_rootedOutputStates_weight]
  rw [he]
  calc
    _ = ∑ x ∈ Finset.univ.image g, f x :=
      (Finset.sum_image (fun a _ b _ h => rootedOutputStates_injective i h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ =>
      mul_nonneg (abs_nonneg _) (Finset.prod_nonneg (fun v _ => mixedVertexWeight_nonneg w v (x v))))

theorem sum_outputCumulant_div_factorial_le (i : Fin n) (hp : p ≤ 3) (hd : 1 ≤ d)
    (hk : 1 ≤ k) (hk4 : k ≤ 4) (w : Fin d → ComplexParameters n k) :
    (∑ B : RootedOutput n i p, ∑ J : Fin d → ObservationIndex n k,
      |outputCumulant B.val J| * ∏ j, ‖w j (J j)‖) / d.factorial ≤
      treeTaylorConstant ^ d * ∏ j, localNorm (w j) := by
  exact (div_le_div_of_nonneg_right (sum_outputCumulant_le_states i w) (by positivity)).trans
    (sum_abs_stateCumulant_div_factorial_le hp hd hk hk4 w (.inr i))

end

end TensorLB
