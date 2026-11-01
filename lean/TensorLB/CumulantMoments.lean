module

public import TensorLB.ProductExpectation
public import TensorLB.Fourier
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Character moments and finite joint cumulants

The cumulant is the usual signed partition sum. Its moments are finite Boolean
averages. Disjoint coordinate supports give the exact factorization needed for
the dependency graph; no measure-theoretic independence assumption is added.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} {n : ℕ}

def characterMoment (X : V → Finset (Fin n)) (B : Finset V) : ℝ :=
  𝔼 z : Fin n → Bool, ∏ j ∈ B, character (X j) z

def characterSiteFactor (X : V → Finset (Fin n)) (B : Finset V) (i : Fin n) (b : Bool) : ℝ :=
  ∏ j ∈ B, if i ∈ X j then sign b else 1

theorem characterMoment_eq_prod_sites (X : V → Finset (Fin n)) (B : Finset V) :
    characterMoment X B = ∏ i : Fin n, 𝔼 b : Bool, characterSiteFactor X B i b := by
  have he (z : Fin n → Bool) :
      (∏ j ∈ B, character (X j) z) = ∏ i : Fin n, characterSiteFactor X B i (z i) := by
    simp only [character_eq_prod_ite, characterSiteFactor]
    exact Finset.prod_comm
  simp only [characterMoment, he]
  exact expect_pi_prod _

theorem characterMoment_empty (X : V → Finset (Fin n)) : characterMoment X ∅ = 1 := by
  simp [characterMoment]

theorem characterMoment_singleton (X : V → Finset (Fin n)) (v : V) :
    characterMoment X {v} = if X v = ∅ then 1 else 0 := by
  simp only [characterMoment, Finset.prod_singleton, expect_character]

theorem abs_characterMoment_le_one (X : V → Finset (Fin n)) (B : Finset V) :
    |characterMoment X B| ≤ 1 := by
  have hchar (A : Finset (Fin n)) (z : Fin n → Bool) : |character A z| = 1 := by
    have h := character_sq A z
    have ha := abs_nonneg (character A z)
    nlinarith [sq_abs (character A z)]
  calc
    _ ≤ 𝔼 z : Fin n → Bool, |∏ j ∈ B, character (X j) z| := Finset.abs_expect_le _ _
    _ = 1 := by simp only [Finset.abs_prod, hchar, Finset.prod_const_one, Fintype.expect_const]

theorem characterSiteFactor_eq_one (X : V → Finset (Fin n)) (B : Finset V) (i : Fin n)
    (h : ∀ j ∈ B, i ∉ X j) (b : Bool) : characterSiteFactor X B i b = 1 := by
  apply Finset.prod_eq_one
  intro j hj
  exact ite_eq_right (h j hj)

variable [DecidableEq V]

/-- This factorization certifies the support-intersection dependency graph. -/
theorem characterMoment_union_of_disjoint_support (X : V → Finset (Fin n))
    (A B : Finset V) (hAB : Disjoint A B)
    (hs : ∀ a ∈ A, ∀ b ∈ B, Disjoint (X a) (X b)) :
    characterMoment X (A ∪ B) = characterMoment X A * characterMoment X B := by
  rw [characterMoment_eq_prod_sites, characterMoment_eq_prod_sites,
    characterMoment_eq_prod_sites, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hu (b : Bool) : characterSiteFactor X (A ∪ B) i b =
      characterSiteFactor X A i b * characterSiteFactor X B i b := by
    exact Finset.prod_union hAB
  simp only [hu]
  by_cases hi : ∃ a ∈ A, i ∈ X a
  · obtain ⟨a, ha, hia⟩ := hi
    have hb : ∀ b ∈ B, i ∉ X b := by
      intro b hb hib
      exact Finset.disjoint_left.mp (hs a ha b hb) hia hib
    simp only [characterSiteFactor_eq_one X B i hb, mul_one, Fintype.expect_const]
  · have ha : ∀ a ∈ A, i ∉ X a := by
      intro a ha hia
      exact hi ⟨a, ha, hia⟩
    simp only [characterSiteFactor_eq_one X A i ha, one_mul, Fintype.expect_const]

def cumulantMobius (b : ℕ) : ℝ := (-1 : ℝ) ^ (b - 1) * (b - 1).factorial

theorem cumulantMobius_succ {b : ℕ} (hb : 1 ≤ b) :
    cumulantMobius (b + 1) = -(b : ℝ) * cumulantMobius b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  simp only [cumulantMobius, Nat.succ_sub_one,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
  ring

theorem abs_cumulantMobius (b : ℕ) : |cumulantMobius b| = ((b - 1).factorial : ℝ) := by
  simp [cumulantMobius]

/-- The partition formula is valid for arbitrary scalar moments. -/
def partitionCumulant (s : Finset V) (m : Finset V → ℝ) : ℝ :=
  ∑ P : Finpartition s, cumulantMobius P.parts.card * ∏ B ∈ P.parts, m B

def jointCharacterCumulant [Fintype V] (X : V → Finset (Fin n)) : ℝ :=
  partitionCumulant Finset.univ (characterMoment X)

/-- A useful bound on each moment factor before the connected-partition
coefficients are grouped. -/
theorem abs_partition_moment_le_one (X : V → Finset (Fin n)) (s : Finset V)
    (P : Finpartition s) : |∏ B ∈ P.parts, characterMoment X B| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun B _ => abs_nonneg _) (fun B _ => abs_characterMoment_le_one X B)

end

end TensorLB
