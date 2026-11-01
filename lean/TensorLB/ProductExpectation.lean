module

public import TensorLB.ExpectationSum

/-!
# Independence under finite product averages

These identities retain the independent component labels. They apply to
arbitrary real weights, so no probabilistic measure infrastructure or limiting
argument is needed for the generating-function factorization.
-/

set_option autoImplicit false

public section

namespace TensorLB

open scoped BigOperators Classical

variable {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι]

/-- Independence of all coordinates of a uniformly chosen function. -/
theorem expect_pi_prod (f : ι → β → ℝ) :
    (𝔼 z : ι → β, ∏ i, f i (z i)) = ∏ i, 𝔼 b : β, f i b := by
  simp only [Fintype.expect_eq_sum_div_card, ← Fintype.prod_sum,
    Finset.prod_div_distrib, Fintype.card_fun, Nat.cast_pow,
    Finset.prod_const, Finset.card_univ]

/-- Independence of the distinguished vector from the whole background. -/
theorem expectation_separated {n m : ℕ}
    (f : (Fin n → Bool) → ℝ) (g : (Fin (m - 1) → Fin n → Bool) → ℝ) :
    expectation n m (fun ω => f ω.1 * g ω.2) =
      (𝔼 z : Fin n → Bool, f z) * (𝔼 z, g z) := by
  rw [expectation_eq_expect]
  change (𝔼 ω : (Fin n → Bool) × (Fin (m - 1) → Fin n → Bool), _) = _
  rw [← Finset.univ_product_univ, Finset.expect_product]
  dsimp only
  rw [← Fintype.expect_mul_expect]

/-- The distinguished vector and all background vectors are independent. -/
theorem expectation_component_prod {n m : ℕ}
    (f : (Fin n → Bool) → ℝ) (g : Fin (m - 1) → (Fin n → Bool) → ℝ) :
    expectation n m (fun ω => f ω.1 * ∏ j, g j (ω.2 j)) =
      (𝔼 z : Fin n → Bool, f z) * ∏ j, 𝔼 z : Fin n → Bool, g j z := by
  rw [expectation_separated f (fun z => ∏ j, g j (z j))]
  exact congrArg (fun x => (𝔼 z, f z) * x) (expect_pi_prod g)

/-- Multiplying selected coordinates by test functions preserves the product
factorization when each unselected coordinate has weight of mean one. -/
theorem expect_pi_prod_mul_embedding {κ : Type*} [Fintype κ]
    (e : κ ↪ ι) (f : κ → β → ℝ) (g : β → ℝ) (hg : (𝔼 b, g b) = 1) :
    (𝔼 z : ι → β, (∏ i, f i (z (e i))) * ∏ j, g (z j)) =
      ∏ i, 𝔼 b, f i b * g b := by
  classical
  have hprod (z : ι → β) :
      (∏ i, f i (z (e i))) * ∏ j, g (z j) =
        ∏ j, g (z j) * ∏ i, if e i = j then f i (z j) else 1 := by
    rw [Finset.prod_mul_distrib, Finset.prod_comm]
    simp only [Fintype.prod_ite_eq]
    exact mul_comm _ _
  simp_rw [hprod]
  rw [expect_pi_prod (fun j b => g b * ∏ i, if e i = j then f i b else 1)]
  have hmean (j : ι) :
      (𝔼 b, g b * ∏ i, if e i = j then f i b else 1) =
        ∏ i, if e i = j then (𝔼 b, f i b * g b) else 1 := by
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      simp only [e.injective.eq_iff, Fintype.prod_ite_eq']
      simp only [mul_comm]
    · have hne (i : κ) : e i ≠ j := fun h => hj ⟨i, h⟩
      simp only [hne, ite_false, Finset.prod_const_one, mul_one, hg]
  simp_rw [hmean]
  rw [Finset.prod_comm]
  simp only [Fintype.prod_ite_eq]

end TensorLB
