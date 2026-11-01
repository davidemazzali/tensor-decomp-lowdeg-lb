module

public import TensorLB.CoefficientArithmetic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Scalar and summation bounds for rooted dependency trees

Summing a nonnegative kernel at a leaf costs its row-sum bound. The sequential
version below iterates this fact for any ordering in which parents precede
children. The scalar estimate absorbs the parent-function tree count and the
Taylor factorial into one absolute exponential constant.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

def tupleHistory {S : Type*} {N : ℕ} (x : Fin N → S) (i : Fin N) : Fin i.val → S :=
  fun j => x ⟨j.val, j.is_lt.trans i.is_lt⟩

theorem tupleHistory_snoc_castSucc {S : Type*} {N : ℕ}
    (x : Fin N → S) (a : S) (i : Fin N) :
    tupleHistory (Fin.snoc x a) i.castSucc = tupleHistory x i := by
  funext j
  exact Fin.snoc_castSucc (α := fun _ : Fin (N + 1) => S) a x ⟨j.val, j.is_lt.trans i.is_lt⟩

theorem tupleHistory_snoc_last {S : Type*} {N : ℕ} (x : Fin N → S) (a : S) :
    tupleHistory (Fin.snoc x a) (Fin.last N) = x := by
  funext j
  exact Fin.snoc_castSucc (α := fun _ : Fin (N + 1) => S) a x j

def sequentialWeight {S : Type*} {N : ℕ}
    (K : (i : Fin N) → (Fin i.val → S) → S → ℝ) (x : Fin N → S) : ℝ :=
  ∏ i, K i (tupleHistory x i) (x i)

theorem sequentialWeight_nonneg {S : Type*} {N : ℕ}
    (K : (i : Fin N) → (Fin i.val → S) → S → ℝ)
    (hK : ∀ i x a, 0 ≤ K i x a) (x : Fin N → S) : 0 ≤ sequentialWeight K x :=
  Finset.prod_nonneg (fun i _ => hK i _ _)

theorem sequentialWeight_snoc {S : Type*} {N : ℕ}
    (K : (i : Fin (N + 1)) → (Fin i.val → S) → S → ℝ)
    (x : Fin N → S) (a : S) :
    sequentialWeight K (Fin.snoc x a) =
      sequentialWeight (fun i => K i.castSucc) x * K (Fin.last N) x a := by
  simp only [sequentialWeight, Fin.prod_univ_castSucc, tupleHistory_snoc_castSucc,
    tupleHistory_snoc_last, Fin.snoc_castSucc, Fin.snoc_last]

/-- Iterated leaf summation. No cardinality factor is lost when each conditional
row sum is controlled independently of the preceding assignment. -/
theorem sum_sequentialWeight_le {S : Type*} [Fintype S] {N : ℕ}
    (K : (i : Fin N) → (Fin i.val → S) → S → ℝ) (c : Fin N → ℝ)
    (hK : ∀ i x a, 0 ≤ K i x a) (hc : ∀ i, 0 ≤ c i)
    (hs : ∀ i x, (∑ a, K i x a) ≤ c i) :
    (∑ x : Fin N → S, sequentialWeight K x) ≤ ∏ i, c i := by
  induction N with
  | zero => simp [sequentialWeight]
  | succ N ih =>
    let K' := fun i : Fin N => K i.castSucc
    let e : ((Fin N → S) × S) ≃ (Fin (N + 1) → S) :=
      (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => S))
    have he (x : Fin N → S) (a : S) : e (x, a) = Fin.snoc x a := rfl
    rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
    simp only [he, sequentialWeight_snoc]
    calc
      _ = ∑ x : Fin N → S, sequentialWeight K' x * ∑ a, K (Fin.last N) x a := by
        apply Finset.sum_congr rfl
        intro x _
        exact (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ x : Fin N → S, sequentialWeight K' x * c (Fin.last N) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (hs _ _) (sequentialWeight_nonneg K' (fun i => hK i.castSucc) x)
      _ = (∑ x : Fin N → S, sequentialWeight K' x) * c (Fin.last N) :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ (∏ i : Fin N, c i.castSucc) * c (Fin.last N) := by
        apply mul_le_mul_of_nonneg_right _ (hc _)
        exact ih K' (fun i => c i.castSucc) (fun i => hK i.castSucc)
          (fun i => hc i.castSucc) (fun i => hs i.castSucc)
      _ = _ := (Fin.prod_univ_castSucc c).symm

def treeTaylorConstant : ℝ := 16 * 40 ^ 5 * Real.exp 1

theorem treeTaylorConstant_pos : 0 < treeTaylorConstant := by
  unfold treeTaylorConstant
  positivity

/-- We use the elementary parent-function count `(d+p)^(d+p-1)`.
It is slightly larger than Cayley's count and has the same exponential cost
after the Taylor factorial is included. -/
theorem tree_taylor_prefactor_le {d p k : ℕ} (hd : 1 ≤ d) (hp : p ≤ 4) (hk : k ≤ 4) :
    (2 * (k : ℝ)) ^ (d + p - 1) * ((d + p : ℕ) : ℝ) ^ (d + p - 1) / d.factorial ≤
      treeTaylorConstant ^ d := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hk4 : (k : ℝ) ≤ 4 := by exact_mod_cast hk
  have hs : ((d + p : ℕ) : ℝ) ≤ 5 * d := by
    have hp4 : (p : ℝ) ≤ 4 := by exact_mod_cast hp
    push_cast
    linarith
  have hd4 : (d : ℝ) ^ 4 ≤ 16 ^ d := by
    calc
      _ = ((d : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ (4 ^ d) ^ 2 := pow_le_pow_left₀ (by positivity) (nat_sq_le_four_pow d) 2
      _ = _ := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  calc
    _ ≤ (8 : ℝ) ^ (d + 4) * (5 * d) ^ (d + 4) / d.factorial := by
      gcongr
      · exact (pow_le_pow_left₀ (by positivity) (by linarith : 2 * (k : ℝ) ≤ 8) _).trans
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 8) (by omega))
      · exact (pow_le_pow_left₀ (by positivity) hs _).trans
          (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 5 * d) (by omega))
    _ = 40 ^ (d + 4) * (d : ℝ) ^ 4 * ((d : ℝ) ^ d / d.factorial) := by
      rw [mul_pow, ← mul_assoc, ← mul_pow]
      norm_num
      rw [pow_add]
      ring
    _ ≤ 40 ^ (5 * d) * (16 : ℝ) ^ d * Real.exp d := by
      have h40 : (40 : ℝ) ^ (d + 4) ≤ 40 ^ (5 * d) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      exact mul_le_mul (mul_le_mul h40 hd4 (by positivity) (by positivity))
        (Real.pow_div_factorial_le_exp (d : ℝ) (by positivity) d) (by positivity) (by positivity)
    _ = treeTaylorConstant ^ d := by
      rw [show Real.exp (d : ℝ) = Real.exp 1 ^ d by simp, pow_mul]
      simp only [treeTaylorConstant, mul_pow]
      ring

end

end TensorLB
