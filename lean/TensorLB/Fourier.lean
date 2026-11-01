module

public import TensorLB.Expectation
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Boolean characters of the underlying signs

Characters indexed by finite sets of sign coordinates have mean zero unless
their support is empty, and distinct characters are orthogonal. The explicit
equivalence `sampleEquiv` transfers these identities to the tensor model's
sample space, retaining the distinguished and background component labels.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators symmDiff

noncomputable section

/-- A Boolean character is the product of the signs in its support. -/
def character {ι : Type*} (A : Finset ι) (z : ι → Bool) : ℝ :=
  ∏ i ∈ A, sign (z i)

@[simp] theorem character_empty {ι : Type*} (z : ι → Bool) :
    character ∅ z = 1 := by simp [character]

@[simp] theorem character_sq {ι : Type*} (A : Finset ι) (z : ι → Bool) :
    character A z ^ 2 = 1 := by simp [character, ← Finset.prod_pow]

section Cube

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem character_eq_prod_ite (A : Finset ι) (z : ι → Bool) :
    character A z = ∏ i, if i ∈ A then sign (z i) else 1 := by
  exact (Finset.prod_ite_mem_eq A (fun i => sign (z i))).symm

/-- Repeated sign coordinates cancel, so multiplication is symmetric difference. -/
theorem character_mul (A B : Finset ι) (z : ι → Bool) :
    character A z * character B z = character (A ∆ B) z := by
  simp only [character_eq_prod_ite, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;>
    simp [Finset.mem_symmDiff, hA, hB, ← sq]

/-- Uniform averaging kills every nonconstant Boolean character. -/
theorem expect_character (A : Finset ι) :
    (𝔼 z : ι → Bool, character A z) = if A = ∅ then 1 else 0 := by
  by_cases hA : A = ∅
  · simp [hA]
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hA
    have hs : (∑ z : ι → Bool, character A z) = 0 := by
      simp_rw [character_eq_prod_ite]
      rw [← Fintype.prod_sum (fun i (b : Bool) => if i ∈ A then sign b else 1)]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi, sign]
    simp only [Fintype.expect_eq_sum_div_card, hs, zero_div, ite_eq_right hA]

/-- The Boolean characters are orthonormal for uniform finite expectation. -/
theorem expect_character_mul (A B : Finset ι) :
    (𝔼 z : ι → Bool, character A z * character B z) = if A = B then 1 else 0 := by
  simp_rw [character_mul, expect_character, Finset.symmDiff_eq_empty]

end Cube

/-- All independent sign coordinates, including their component labels. -/
abbrev SignIndex (n m : ℕ) := Fin n ⊕ (Fin (m - 1) × Fin n)

/-- Flatten the tensor sample into one Boolean cube without losing component labels. -/
def sampleEquiv (n m : ℕ) : Sample n m ≃ (SignIndex n m → Bool) where
  toFun ω := Sum.elim ω.1 (fun ji => ω.2 ji.1 ji.2)
  invFun z := (fun i => z (Sum.inl i), fun j i => z (Sum.inr (j, i)))
  left_inv ω := rfl
  right_inv z := by
    funext a
    cases a with
    | inl i => rfl
    | inr ji => rfl

/-- A Fourier monomial in the underlying signs of the tensor model. -/
def sampleCharacter {n m : ℕ} (A : Finset (SignIndex n m)) (ω : Sample n m) : ℝ :=
  character A (sampleEquiv n m ω)

variable {n m : ℕ}

@[simp] theorem sampleEquiv_inl (ω : Sample n m) (i : Fin n) :
    sampleEquiv n m ω (Sum.inl i) = ω.1 i := rfl

@[simp] theorem sampleEquiv_inr (ω : Sample n m) (j : Fin (m - 1)) (i : Fin n) :
    sampleEquiv n m ω (Sum.inr (j, i)) = ω.2 j i := rfl

@[simp] theorem sampleCharacter_empty (ω : Sample n m) :
    sampleCharacter ∅ ω = 1 := by simp [sampleCharacter]

@[simp] theorem sampleCharacter_sq (A : Finset (SignIndex n m)) (ω : Sample n m) :
    sampleCharacter A ω ^ 2 = 1 := by simp [sampleCharacter]

theorem sampleCharacter_mul (A B : Finset (SignIndex n m)) (ω : Sample n m) :
    sampleCharacter A ω * sampleCharacter B ω = sampleCharacter (A ∆ B) ω :=
  character_mul A B (sampleEquiv n m ω)

theorem expectation_sampleCharacter (A : Finset (SignIndex n m)) :
    expectation n m (sampleCharacter A) = if A = ∅ then 1 else 0 := by
  rw [expectation_eq_expect]
  calc
    _ = 𝔼 z : SignIndex n m → Bool, character A z :=
      Fintype.expect_equiv (sampleEquiv n m) _ _ (fun _ => rfl)
    _ = _ := expect_character A

/-- Orthogonality applies to supports spanning any number of components. -/
theorem expectation_sampleCharacter_mul (A B : Finset (SignIndex n m)) :
    expectation n m (fun ω => sampleCharacter A ω * sampleCharacter B ω) =
      if A = B then 1 else 0 := by
  simp_rw [sampleCharacter_mul]
  rw [expectation_sampleCharacter]
  simp only [Finset.symmDiff_eq_empty]

/-- Embed a target support into the distinguished component's sign coordinates. -/
def distinguishedSupport (m : ℕ) (A : Finset (Fin n)) : Finset (SignIndex n m) :=
  A.map Function.Embedding.inl

@[simp] theorem sampleCharacter_distinguishedSupport (A : Finset (Fin n)) :
    sampleCharacter (distinguishedSupport m A) = target n m A := by
  funext ω
  unfold sampleCharacter distinguishedSupport character target
  rw [Finset.prod_map]
  rfl

/-- The target has mean zero exactly when its support is nonempty. -/
theorem expectation_target (A : Finset (Fin n)) :
    expectation n m (target n m A) = if A = ∅ then 1 else 0 := by
  have h := expectation_sampleCharacter (distinguishedSupport m A)
  simp only [sampleCharacter_distinguishedSupport] at h
  simpa only [distinguishedSupport, Finset.map_eq_empty] using h

theorem expectation_target_eq_zero {A : Finset (Fin n)} (hA : A.Nonempty) :
    expectation n m (target n m A) = 0 := by
  simp [expectation_target, hA.ne_empty]

/-- Distinct distinguished-component targets are orthogonal. -/
theorem expectation_target_mul (A B : Finset (Fin n)) :
    expectation n m (fun ω => target n m A ω * target n m B ω) =
      if A = B then 1 else 0 := by
  have h := expectation_sampleCharacter_mul (distinguishedSupport m A) (distinguishedSupport m B)
  simp only [sampleCharacter_distinguishedSupport] at h
  simpa only [distinguishedSupport, Finset.map_inj] using h

/-- Embed a character support into one background component. -/
def backgroundSupport (j : Fin (m - 1)) (A : Finset (Fin n)) :
    Finset (SignIndex n m) :=
  A.map ⟨fun i => Sum.inr (j, i), fun _ _ h => (Prod.mk.inj (Sum.inr.inj h)).2⟩

@[simp] theorem sampleCharacter_backgroundSupport (j : Fin (m - 1))
    (A : Finset (Fin n)) (ω : Sample n m) :
    sampleCharacter (backgroundSupport j A) ω = character A (ω.2 j) := by
  unfold sampleCharacter backgroundSupport character
  rw [Finset.prod_map]
  rfl

theorem expectation_backgroundCharacter (j : Fin (m - 1)) (A : Finset (Fin n)) :
    expectation n m (fun ω => character A (ω.2 j)) = if A = ∅ then 1 else 0 := by
  have h := expectation_sampleCharacter (backgroundSupport j A)
  change expectation n m (fun ω => sampleCharacter (backgroundSupport j A) ω) = _ at h
  simp only [sampleCharacter_backgroundSupport] at h
  simpa only [backgroundSupport, Finset.map_eq_empty] using h

end

end TensorLB
