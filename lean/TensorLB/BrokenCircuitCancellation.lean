module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto

/-!
# Cancellation by the least redundant edge

The broken-circuit argument only needs two facts: redundancy at an edge depends
on the earlier edges, and toggling a redundant edge preserves the family being
summed. Toggling the least redundant edge is then a sign-reversing involution.
This module proves that finite combinatorial statement independently of graphs.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {E : Type*} [LinearOrder E]

def toggleEdge (F : Finset E) (e : E) : Finset E :=
  if e ∈ F then F.erase e else insert e F

theorem mem_toggleEdge_self (F : Finset E) (e : E) : e ∈ toggleEdge F e ↔ e ∉ F := by
  by_cases he : e ∈ F <;> simp [toggleEdge, he]

theorem toggleEdge_ne (F : Finset E) (e : E) : toggleEdge F e ≠ F := by
  intro h
  have he := mem_toggleEdge_self F e
  rw [h] at he
  tauto

theorem toggleEdge_twice (F : Finset E) (e : E) : toggleEdge (toggleEdge F e) e = F := by
  by_cases he : e ∈ F
  · simp only [toggleEdge, ite_eq_left he, Finset.notMem_erase, ite_false,
      Finset.insert_erase he]
  · simp only [toggleEdge, ite_eq_right he, Finset.mem_insert_self, ite_true,
      Finset.erase_insert he]

theorem toggleEdge_sign (F : Finset E) (e : E) :
    (-1 : ℝ) ^ F.card + (-1 : ℝ) ^ (toggleEdge F e).card = 0 := by
  by_cases he : e ∈ F
  · rw [toggleEdge, ite_eq_left he]
    have hcard : F.card = (F.erase e).card + 1 := by
      rw [Finset.card_erase_of_mem he]
      have := Finset.card_pos.mpr ⟨e, he⟩
      omega
    conv_lhs => arg 1; rw [hcard, pow_succ]
    ring
  · rw [toggleEdge, ite_eq_right he, Finset.card_insert_of_notMem he, pow_succ]
    ring

theorem filter_toggleEdge_lt (F : Finset E) {e a : E} (ha : a ≤ e) :
    (toggleEdge F e).filter (· < a) = F.filter (· < a) := by
  ext b
  by_cases he : e ∈ F <;> simp only [toggleEdge, he, ite_true, ite_false,
    Finset.mem_filter, Finset.mem_erase, Finset.mem_insert]
  · constructor
    · tauto
    · rintro ⟨hb, hba⟩
      exact ⟨⟨(ne_of_lt (hba.trans_le ha)), hb⟩, hba⟩
  · constructor
    · rintro ⟨hb | hb, hba⟩
      · subst b
        exact False.elim ((not_lt_of_ge ha) hba)
      · exact ⟨hb, hba⟩
    · tauto

variable [Fintype E]

/-- The second argument of `R e` contains only edges preceding `e`. -/
def redundantEdges (R : E → Finset E → Prop) (F : Finset E) : Finset E :=
  Finset.univ.filter (fun e => R e (F.filter (· < e)))

theorem mem_redundantEdges (R : E → Finset E → Prop) (F : Finset E) (e : E) :
    e ∈ redundantEdges R F ↔ R e (F.filter (· < e)) := by
  simp only [redundantEdges, Finset.mem_filter, Finset.mem_univ, true_and]

theorem redundantEdges_toggle_mem_iff (R : E → Finset E → Prop) (F : Finset E)
    {e a : E} (ha : a ≤ e) :
    a ∈ redundantEdges R (toggleEdge F e) ↔ a ∈ redundantEdges R F := by
  rw [mem_redundantEdges, mem_redundantEdges, filter_toggleEdge_lt F ha]

theorem least_redundant_toggle (R : E → Finset E → Prop) (F : Finset E)
    (hF : (redundantEdges R F).Nonempty) :
    let e := (redundantEdges R F).min' hF
    ∃ hT : (redundantEdges R (toggleEdge F e)).Nonempty,
      (redundantEdges R (toggleEdge F e)).min' hT = e := by
  dsimp only
  let e := (redundantEdges R F).min' hF
  have he : e ∈ redundantEdges R F := Finset.min'_mem _ _
  have heT : e ∈ redundantEdges R (toggleEdge F e) :=
    (redundantEdges_toggle_mem_iff R F le_rfl).mpr he
  refine ⟨⟨e, heT⟩, ?_⟩
  apply (Finset.min'_eq_iff _ _ e).mpr
  refine ⟨heT, ?_⟩
  intro a ha
  by_contra hle
  have hae : a < e := lt_of_not_ge hle
  have haF := (redundantEdges_toggle_mem_iff R F hae.le).mp ha
  exact (not_lt_of_ge ((redundantEdges R F).min'_le a haF)) hae

/-- All sets containing a broken circuit cancel in pairs. -/
theorem sum_redundant_sign_eq_zero (R : E → Finset E → Prop) (P : Finset E → Prop)
    (hP : ∀ F e, R e (F.filter (· < e)) → (P (toggleEdge F e) ↔ P F)) :
    (∑ F ∈ Finset.univ.filter (fun F : Finset E =>
      P F ∧ (redundantEdges R F).Nonempty), (-1 : ℝ) ^ F.card) = 0 := by
  let s := Finset.univ.filter (fun F : Finset E => P F ∧ (redundantEdges R F).Nonempty)
  let g (F : Finset E) (hF : F ∈ s) : Finset E :=
    toggleEdge F ((redundantEdges R F).min' (Finset.mem_filter.mp hF).2.2)
  have hgmem (F : Finset E) (hF : F ∈ s) : g F hF ∈ s := by
    obtain ⟨hPF, hRF⟩ := (Finset.mem_filter.mp hF).2
    have he := (mem_redundantEdges R F _).mp ((redundantEdges R F).min'_mem hRF)
    obtain ⟨hT, _⟩ := least_redundant_toggle R F hRF
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hP _ _ he).mpr hPF, hT⟩
  refine Finset.sum_involution g ?_ ?_ hgmem ?_
  · intro F hF
    exact toggleEdge_sign F _
  · intro F hF _
    exact toggleEdge_ne F _
  · intro F hF
    have hRF := (Finset.mem_filter.mp hF).2.2
    obtain ⟨hT, he⟩ := least_redundant_toggle R F hRF
    change toggleEdge (g F hF) ((redundantEdges R (g F hF)).min' _) = F
    rw [show (redundantEdges R (g F hF)).min' _ =
      (redundantEdges R F).min' hRF from he]
    exact toggleEdge_twice F _

/-- The alternating sum is bounded by the number of irredundant survivors. -/
theorem abs_signed_family_sum_le (R : E → Finset E → Prop) (P : Finset E → Prop)
    (hP : ∀ F e, R e (F.filter (· < e)) → (P (toggleEdge F e) ↔ P F)) :
    |∑ F ∈ Finset.univ.filter P, (-1 : ℝ) ^ F.card| ≤
      ((Finset.univ.filter (fun F : Finset E => P F ∧ ¬(redundantEdges R F).Nonempty)).card : ℝ) := by
  have hs := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter P) (fun F => (redundantEdges R F).Nonempty)
    (fun F => (-1 : ℝ) ^ F.card)
  simp only [Finset.filter_filter] at hs
  rw [sum_redundant_sign_eq_zero R P hP, zero_add] at hs
  rw [← hs]
  calc
    _ ≤ ∑ F ∈ Finset.univ.filter (fun F : Finset E => P F ∧ ¬(redundantEdges R F).Nonempty),
        |(-1 : ℝ) ^ F.card| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp

end

end TensorLB
