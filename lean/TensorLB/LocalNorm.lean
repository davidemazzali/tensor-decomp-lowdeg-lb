module

public import TensorLB.ComplexCoordinates
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Local interaction norm

The local norm is the maximum incident absolute interaction weight. The basic
intersection estimate bounds the total weight of interactions meeting a support
by its cardinality times this norm, independently of the ambient dimension.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {n k : ℕ}

def incidentNorm (t : ComplexParameters n k) (i : Fin n) : ℝ :=
  ∑ I, if i ∈ I.val then ‖t I‖ else 0

def localNorm (t : ComplexParameters n k) : ℝ := ‖incidentNorm t‖

theorem incidentNorm_nonneg (t : ComplexParameters n k) (i : Fin n) : 0 ≤ incidentNorm t i := by
  apply Finset.sum_nonneg
  intro I _
  split_ifs <;> positivity

theorem localNorm_nonneg (t : ComplexParameters n k) : 0 ≤ localNorm t := norm_nonneg _

theorem incidentNorm_le_localNorm (t : ComplexParameters n k) (i : Fin n) :
    incidentNorm t i ≤ localNorm t := by
  simpa only [localNorm, Real.norm_eq_abs, abs_of_nonneg (incidentNorm_nonneg t i)] using
    norm_le_pi_norm (incidentNorm t) i

theorem localNorm_le_iff (t : ComplexParameters n k) {r : ℝ} (hr : 0 ≤ r) :
    localNorm t ≤ r ↔ ∀ i, incidentNorm t i ≤ r := by
  simp only [localNorm, pi_norm_le_iff_of_nonneg hr, Real.norm_eq_abs,
    abs_of_nonneg (incidentNorm_nonneg t _)]

@[simp] theorem incidentNorm_zero (i : Fin n) : incidentNorm (n := n) (k := k) 0 i = 0 := by
  simp [incidentNorm]

@[simp] theorem localNorm_zero : localNorm (n := n) (k := k) 0 = 0 := by
  simp [localNorm, show incidentNorm (n := n) (k := k) 0 = 0 by ext; simp]

theorem norm_le_incidentNorm (t : ComplexParameters n k) (I : ObservationIndex n k)
    {i : Fin n} (hi : i ∈ I.val) : ‖t I‖ ≤ incidentNorm t i := by
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset (ObservationIndex n k)))
    (f := fun J => if i ∈ J.val then ‖t J‖ else 0)
    (fun J _ => by split_ifs <;> positivity) (Finset.mem_univ I)
  simpa only [incidentNorm, ite_eq_left hi] using h

theorem norm_le_localNorm (t : ComplexParameters n k) : ‖t‖ ≤ localNorm t := by
  apply (pi_norm_le_iff_of_nonneg (localNorm_nonneg t)).mpr
  intro I
  obtain ⟨i, hi⟩ := I.property.1
  exact (norm_le_incidentNorm t I hi).trans (incidentNorm_le_localNorm t i)

theorem localNorm_eq_zero_iff (t : ComplexParameters n k) : localNorm t = 0 ↔ t = 0 := by
  constructor
  · intro ht
    exact norm_eq_zero.mp ((norm_le_localNorm t).trans_eq ht |>.antisymm (norm_nonneg t))
  · rintro rfl
    exact localNorm_zero

theorem incidentNorm_add_le (t u : ComplexParameters n k) (i : Fin n) :
    incidentNorm (t + u) i ≤ incidentNorm t i + incidentNorm u i := by
  unfold incidentNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro I _
  split_ifs <;> simp only [Pi.add_apply, add_zero, le_refl]
  exact norm_add_le _ _

theorem localNorm_add_le (t u : ComplexParameters n k) :
    localNorm (t + u) ≤ localNorm t + localNorm u := by
  apply (localNorm_le_iff _ (add_nonneg (localNorm_nonneg t) (localNorm_nonneg u))).mpr
  intro i
  exact (incidentNorm_add_le t u i).trans
    (add_le_add (incidentNorm_le_localNorm t i) (incidentNorm_le_localNorm u i))

theorem incidentNorm_smul (c : ℂ) (t : ComplexParameters n k) (i : Fin n) :
    incidentNorm (c • t) i = ‖c‖ * incidentNorm t i := by
  simp only [incidentNorm, Pi.smul_apply, norm_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  split_ifs <;> simp

theorem localNorm_smul (c : ℂ) (t : ComplexParameters n k) :
    localNorm (c • t) = ‖c‖ * localNorm t := by
  have he : incidentNorm (c • t) = ‖c‖ • incidentNorm t := by
    ext i
    exact incidentNorm_smul c t i
  rw [localNorm, he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg c)]
  rfl

theorem localNorm_le_card_mul_norm (t : ComplexParameters n k) :
    localNorm t ≤ Fintype.card (ObservationIndex n k) * ‖t‖ := by
  apply (localNorm_le_iff _ (by positivity)).mpr
  intro i
  calc
    incidentNorm t i ≤ ∑ _I : ObservationIndex n k, ‖t‖ := by
      apply Finset.sum_le_sum
      intro I _
      split_ifs
      · exact norm_le_pi_norm t I
      · exact norm_nonneg t
    _ = _ := by simp

/-- The total interaction weight loses only a factor of the number of sites. -/
theorem sum_norm_le_mul_localNorm (t : ComplexParameters n k) :
    (∑ I, ‖t I‖) ≤ (n : ℝ) * localNorm t := by
  calc
    _ ≤ ∑ I : ObservationIndex n k, ∑ i : Fin n,
        if i ∈ I.val then ‖t I‖ else 0 := by
      apply Finset.sum_le_sum
      intro I _
      obtain ⟨i, hi⟩ := I.property.1
      have h := Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin n => if j ∈ I.val then ‖t I‖ else 0)
        (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ i)
      simpa only [ite_eq_left hi] using h
    _ = ∑ i : Fin n, incidentNorm t i := by rw [Finset.sum_comm]; rfl
    _ ≤ ∑ _i : Fin n, localNorm t := Finset.sum_le_sum
      (fun i _ => incidentNorm_le_localNorm t i)
    _ = _ := by simp

/-- One interaction child in the rooted dependency-tree estimate. -/
theorem sum_intersecting_norm_le (t : ComplexParameters n k) (B : Finset (Fin n)) :
    (∑ I : ObservationIndex n k, if (I.val ∩ B).Nonempty then ‖t I‖ else 0) ≤
      (B.card : ℝ) * localNorm t := by
  calc
    _ ≤ ∑ I : ObservationIndex n k, ∑ i ∈ B, if i ∈ I.val then ‖t I‖ else 0 := by
      apply Finset.sum_le_sum
      intro I _
      split_ifs with h
      · obtain ⟨i, hi⟩ := h
        obtain ⟨hiI, hiB⟩ := Finset.mem_inter.mp hi
        have hh := Finset.single_le_sum (s := B)
          (f := fun j => if j ∈ I.val then ‖t I‖ else 0)
          (fun j _ => by split_ifs <;> positivity) hiB
        simpa only [ite_eq_left hiI] using hh
      · apply Finset.sum_nonneg
        intro i _
        split_ifs <;> positivity
    _ = ∑ i ∈ B, incidentNorm t i := by
      rw [Finset.sum_comm]
      rfl
    _ ≤ ∑ _i ∈ B, localNorm t := Finset.sum_le_sum (fun i _ => incidentNorm_le_localNorm t i)
    _ = _ := by simp

/-- Interaction parameters equipped with the incident-weight norm. -/
def LocalParameters (n k : ℕ) := ComplexParameters n k

namespace LocalParameters

instance : AddCommGroup (LocalParameters n k) :=
  inferInstanceAs (AddCommGroup (ComplexParameters n k))

instance : Module ℂ (LocalParameters n k) :=
  inferInstanceAs (Module ℂ (ComplexParameters n k))

instance : Norm (LocalParameters n k) := ⟨localNorm⟩

theorem normCore : NormedSpace.Core ℂ (LocalParameters n k) where
  norm_nonneg := localNorm_nonneg
  norm_smul := localNorm_smul
  norm_triangle := localNorm_add_le
  norm_eq_zero_iff := localNorm_eq_zero_iff

instance : NormedAddCommGroup (LocalParameters n k) := .ofCore normCore

instance : NormedSpace ℂ (LocalParameters n k) := .ofCore normCore

instance : FiniteDimensional ℂ (LocalParameters n k) :=
  inferInstanceAs (FiniteDimensional ℂ (ComplexParameters n k))

instance : CompleteSpace (LocalParameters n k) := FiniteDimensional.complete ℂ _

/-- Changing norms preserves the analytic parameter space. -/
def equiv : LocalParameters n k ≃L[ℂ] ComplexParameters n k :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun t => t
      invFun := fun t => t
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] theorem equiv_apply (t : LocalParameters n k) : equiv t = t := rfl

@[simp] theorem equiv_symm_apply (t : ComplexParameters n k) : equiv.symm t = t := rfl

@[simp] theorem norm_eq (t : LocalParameters n k) : ‖t‖ = localNorm (equiv t) := rfl

end LocalParameters

end

end TensorLB
