module

public import TensorLB.ResponseParity

/-!
# Boolean polarization of homogeneous polynomials

Averaging the diagonal of a multilinear map against the full Boolean character
retains precisely its permutations. This extracts a mixed coefficient without
the dimension-dependent loss from a bound on the operator norm.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {d : ℕ}

theorem expect_fullCharacter_prod_comp (f : Fin d → Fin d) :
    (𝔼 ε : Fin d → Bool, character Finset.univ ε * ∏ i, sign (ε (f i))) =
      if Function.Bijective f then 1 else 0 := by
  by_cases hf : Function.Bijective f
  · rw [ite_eq_left hf]
    have hp (ε : Fin d → Bool) : (∏ i, sign (ε (f i))) = character Finset.univ ε := by
      exact Fintype.prod_bijective f hf _ _ (fun _ => rfl)
    simp only [hp, ← sq, character_sq, Finset.expect_const, Finset.univ_nonempty]
  · rw [ite_eq_right hf]
    have hns : ¬ Function.Surjective f := fun hs =>
      hf ⟨(Finite.injective_iff_surjective).mpr hs, hs⟩
    simp only [Function.Surjective, not_forall, not_exists] at hns
    obtain ⟨j, hj⟩ := hns
    let g := fun ε : Fin d → Bool => character Finset.univ ε * ∏ i, sign (ε (f i))
    have hg (ε : Fin d → Bool) : g (spinFlip (singleFlipSigns j) ε) = -g ε := by
      have hp : ∀ i, sign (singleFlipSigns j (f i)) = 1 := by
        intro i
        simp [singleFlipSigns, hj i, sign]
      simp only [g, character_spinFlip, character_singleFlipSigns,
        Finset.mem_univ, ite_true, sign_spinFlip, hp, one_mul]
      ring
    have he := Fintype.expect_equiv (spinFlip (singleFlipSigns j))
      (fun ε => g (spinFlip (singleFlipSigns j) ε)) g (fun _ => rfl)
    simp only [hg, Finset.expect_neg_distrib] at he
    change (𝔼 ε, g ε) = 0
    linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact polarization, with no symmetry assumption on the multilinear map. -/
theorem boolean_polarization (M : E [×d]→L[ℝ] ℝ) (v : Fin d → E) :
    (𝔼 ε : Fin d → Bool, character Finset.univ ε *
      M (fun _ => ∑ j, sign (ε j) • v j)) =
      ∑ f : Fin d → Fin d, if Function.Bijective f then M (fun i => v (f i)) else 0 := by
  simp_rw [M.map_sum, M.map_smul_univ, smul_eq_mul, Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  simp only [← mul_assoc, ← Finset.expect_mul, expect_fullCharacter_prod_comp]
  split_ifs <;> simp

theorem abs_character (A : Finset (Fin d)) (ε : Fin d → Bool) : |character A ε| = 1 := by
  have h := character_sq A ε
  nlinarith [sq_abs (character A ε), abs_nonneg (character A ε)]

/-- A bound on all signed diagonals bounds the full symmetrization. -/
theorem abs_sum_bijective_le (M : E [×d]→L[ℝ] ℝ) (v : Fin d → E) {C : ℝ}
    (h : ∀ ε : Fin d → Bool, |M (fun _ => ∑ j, sign (ε j) • v j)| ≤ C) :
    |∑ f : Fin d → Fin d, if Function.Bijective f then M (fun i => v (f i)) else 0| ≤ C := by
  rw [← boolean_polarization, Fintype.expect_eq_sum_div_card, abs_div,
    abs_of_nonneg (a := (Fintype.card (Fin d → Bool) : ℝ)) (by positivity)]
  apply (div_le_iff₀ (by positivity :
    (0 : ℝ) < Fintype.card (Fin d → Bool))).mpr
  calc
    _ ≤ ∑ ε : Fin d → Bool, |character Finset.univ ε *
        M (fun _ => ∑ j, sign (ε j) • v j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ε : Fin d → Bool, C := by
      apply Finset.sum_le_sum
      intro ε _
      simpa only [abs_mul, abs_character, one_mul] using h ε
    _ = _ := by simp [mul_comm]

theorem sum_bijective_eq_sum_perm (F : (Fin d → Fin d) → ℝ) :
    (∑ f : Fin d → Fin d, if Function.Bijective f then F f else 0) =
      ∑ σ : Equiv.Perm (Fin d), F σ := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun f hf => Equiv.ofBijective f (Finset.mem_filter.mp hf).2)
  · intro f hf
    exact Finset.mem_univ _
  · intro f hf g hg h
    exact congrArg (fun σ : Equiv.Perm (Fin d) => (σ : Fin d → Fin d)) h
  · intro σ _
    refine ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.bijective⟩, ?_⟩
    exact Equiv.ext (fun _ => rfl)
  · intro f hf
    rfl

variable {α : Type*} [Fintype α]

/-- A tensor array, viewed as a continuous multilinear map. -/
def tensorMultilinear (T : (Fin d → α) → ℝ) : (α → ℝ) [×d]→L[ℝ] ℝ :=
  ∑ t, T t • (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin d) ℝ).compContinuousLinearMap
    (fun i => ContinuousLinearMap.proj (t i))

theorem tensorMultilinear_apply (T : (Fin d → α) → ℝ) (v : Fin d → α → ℝ) :
    tensorMultilinear T v = ∑ t, T t * ∏ i, v i (t i) := by
  simp [tensorMultilinear, ContinuousMultilinearMap.mkPiAlgebra_apply]

theorem tensorMultilinear_diagonal (T : (Fin d → α) → ℝ) (x : α → ℝ) :
    tensorMultilinear T (fun _ => x) = MvPolynomial.eval x (tensorPolynomial T) := by
  rw [tensorMultilinear_apply, eval_tensorPolynomial]

theorem tensorMultilinear_basis (T : (Fin d → α) → ℝ) (t : Fin d → α) :
    tensorMultilinear T (fun i => Pi.single (t i) 1) = T t := by
  rw [tensorMultilinear_apply]
  have hp (s : Fin d → α) : (∏ i, (Pi.single (t i) 1 : α → ℝ) (s i)) =
      if s = t then 1 else 0 := by
    by_cases hs : s = t
    · simp [hs]
    · rw [ite_eq_right hs]
      have hn : ∃ i, s i ≠ t i := by
        by_contra h
        apply hs
        ext i
        push Not at h
        exact h i
      obtain ⟨i, hi⟩ := hn
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [Ne.symm hi]
  simp only [hp, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [Fintype α] in
theorem tupleIndex_comp_perm (t : Fin d → α) (σ : Equiv.Perm (Fin d)) :
    tupleIndex (t ∘ σ) = tupleIndex t := by
  exact Equiv.sum_comp σ (fun i => Finsupp.single (t i) 1)

/-- Boolean polarization extracts the factorial-normalized coefficient even
when the chosen tuple has repeated labels. -/
theorem polynomial_polarization (p : MvPolynomial α ℝ) (hp : p.IsHomogeneous d)
    (t : Fin d → α) (w : Fin d → ℝ) :
    (𝔼 ε : Fin d → Bool, character Finset.univ ε *
      MvPolynomial.eval (∑ j, (sign (ε j) * w j) • Pi.single (t j) 1) p) =
      p.coeff (tupleIndex t) * ((tupleIndex t).prod (fun _ r => r.factorial) : ℝ) *
        ∏ j, w j := by
  let M := tensorMultilinear (polynomialTensor p d)
  have hdiag (x : α → ℝ) : M (fun _ => x) = MvPolynomial.eval x p := by
    rw [tensorMultilinear_diagonal, tensorPolynomial_polynomialTensor p hp]
  have h := boolean_polarization M (fun j => w j • Pi.single (t j) 1)
  simp only [smul_smul, hdiag] at h
  rw [h, sum_bijective_eq_sum_perm]
  have hs (σ : Equiv.Perm (Fin d)) :
      M (fun i => w (σ i) • Pi.single (t (σ i)) 1) =
        (∏ j, w j) * polynomialTensor p d t := by
    rw [M.map_smul_univ]
    change (∏ i, w (σ i)) * tensorMultilinear (polynomialTensor p d)
      (fun i => Pi.single ((t ∘ σ) i) 1) = _
    rw [tensorMultilinear_basis, Equiv.prod_comp σ]
    rw [polynomialTensor_isSymmetric p d _ _ (tupleIndex_comp_perm t σ)]
  simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, polynomialTensor]
  have hd : (d.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem abs_normalized_coefficient_mul_prod_le (p : MvPolynomial α ℝ)
    (hp : p.IsHomogeneous d) (t : Fin d → α) (w : Fin d → ℝ) {C : ℝ}
    (h : ∀ ε : Fin d → Bool,
      |MvPolynomial.eval (∑ j, (sign (ε j) * w j) • Pi.single (t j) 1) p| ≤ C) :
    |p.coeff (tupleIndex t) * ((tupleIndex t).prod (fun _ r => r.factorial) : ℝ) *
      ∏ j, w j| ≤ C := by
  rw [← polynomial_polarization p hp t w]
  let M := tensorMultilinear (polynomialTensor p d)
  have hd (x : α → ℝ) : M (fun _ => x) = MvPolynomial.eval x p := by
    rw [tensorMultilinear_diagonal, tensorPolynomial_polynomialTensor p hp]
  have hb := abs_sum_bijective_le M (fun j => w j • Pi.single (t j) 1)
    (by simpa only [smul_smul, hd] using h)
  have he := boolean_polarization M (fun j => w j • Pi.single (t j) 1)
  simp only [smul_smul, hd] at he
  exact (congrArg abs he).le.trans hb

end

end TensorLB
