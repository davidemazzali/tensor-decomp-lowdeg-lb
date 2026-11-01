module

public import TensorLB.Expectation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.Count

import Lean.Elab.Tactic.Omega

/-!
# Parity supports of tensor entries

A product of signs depends only on coordinates occurring an odd number of
times. Its support has size at most the number of tensor slots and has the
same parity. These statements hold for every tensor order.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators

/-- Coordinates with odd multiplicity, built by toggling membership. -/
def listOddSupport {α : Type*} [DecidableEq α] : List α → Finset α
  | [] => ∅
  | a :: l => if a ∈ listOddSupport l then (listOddSupport l).erase a
    else insert a (listOddSupport l)

theorem listOddSupport_card_le {α : Type*} [DecidableEq α] (l : List α) :
    (listOddSupport l).card ≤ l.length := by
  induction l with
  | nil => simp [listOddSupport]
  | cons a l ih =>
    simp only [listOddSupport, List.length_cons]
    split_ifs with h
    · have hc := Finset.card_erase_add_one h
      omega
    · rw [Finset.card_insert_of_notMem h]
      omega

theorem listOddSupport_card_mod_two {α : Type*} [DecidableEq α] (l : List α) :
    (listOddSupport l).card % 2 = l.length % 2 := by
  induction l with
  | nil => simp [listOddSupport]
  | cons a l ih =>
    simp only [listOddSupport, List.length_cons]
    split_ifs with h
    · have hc := Finset.card_erase_add_one h
      omega
    · rw [Finset.card_insert_of_notMem h]
      omega

/-- Membership agrees with the parity of the number of occurrences. -/
theorem mem_listOddSupport {α : Type*} [DecidableEq α] (a : α) (l : List α) :
    a ∈ listOddSupport l ↔ l.count a % 2 = 1 := by
  induction l with
  | nil => simp [listOddSupport]
  | cons b l ih =>
    by_cases hab : b = a
    · subst b
      simp only [listOddSupport, List.count_cons_self]
      split_ifs with h
      · simp only [Finset.notMem_erase, false_iff]
        have hh := ih.mp h
        omega
      · simp only [Finset.mem_insert_self, true_iff]
        have hh : l.count a % 2 ≠ 1 := fun hc => h (ih.mpr hc)
        omega
    · simp only [listOddSupport, List.count_cons_of_ne hab]
      split_ifs with h
      · simpa [Finset.mem_erase, Ne.symm hab] using ih
      · simpa [Finset.mem_insert, Ne.symm hab] using ih

theorem prod_sign_list_eq_support {α : Type*} [DecidableEq α]
    (l : List α) (z : α → Bool) :
    (l.map (fun i => sign (z i))).prod = ∏ i ∈ listOddSupport l, sign (z i) := by
  induction l with
  | nil => simp [listOddSupport]
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, ih, listOddSupport]
    split_ifs with h
    · rw [← Finset.mul_prod_erase _ _ h, ← mul_assoc]
      simp [← sq]
    · rw [Finset.prod_insert h]

/-- The parity support of a full ordered tensor index, including repeated slots. -/
def tensorSupport {n k : ℕ} (I : TensorIndex n k) : Finset (Fin n) :=
  listOddSupport (List.ofFn I)

theorem tensorSupport_card_le {n k : ℕ} (I : TensorIndex n k) :
    (tensorSupport I).card ≤ k := by
  simpa only [tensorSupport, List.length_ofFn] using listOddSupport_card_le (List.ofFn I)

theorem tensorSupport_card_mod_two {n k : ℕ} (I : TensorIndex n k) :
    (tensorSupport I).card % 2 = k % 2 := by
  simpa only [tensorSupport, List.length_ofFn] using
    listOddSupport_card_mod_two (List.ofFn I)

theorem prod_sign_eq_tensorSupport {n k : ℕ} (I : TensorIndex n k)
    (z : Fin n → Bool) :
    (∏ a : Fin k, sign (z (I a))) = ∏ i ∈ tensorSupport I, sign (z i) := by
  simpa only [tensorSupport, List.map_ofFn, List.prod_ofFn, Function.comp_def] using
    prod_sign_list_eq_support (List.ofFn I) z

end TensorLB
