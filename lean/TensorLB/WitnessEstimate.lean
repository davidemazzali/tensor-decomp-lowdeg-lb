module

public import TensorLB.SymmetricTensor
public import TensorLB.LiftWeights
public import TensorLB.ResponseWitness
public import TensorLB.FinalReduction
public import TensorLB.SubstitutionBound

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Combining coefficient energy with the substitution estimate

The response coefficient energy remains an explicit hypothesis. The connected
substitution norm is proved in `SubstitutionBound`. This module combines these
with the falling-factorial estimate and packages the witness for `FinalReduction`.
-/

set_option autoImplicit false

public section

namespace TensorLB

open scoped BigOperators

variable {n m k D : ℕ} {τ B : ℝ}

theorem sqrt_pow_of_nonneg {x : ℝ} (hx : 0 ≤ x) (d : ℕ) :
    Real.sqrt (x ^ d) = Real.sqrt x ^ d := by
  induction d with
  | zero => simp
  | succ d ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx d), ih, pow_succ]

/-- The scalar calculation turning coefficient energy and the substitution
bound into the termwise estimate used in equation (43). -/
theorem homogeneous_norm_estimate {N D d : ℕ} {E r c w : ℝ}
    (hd : d ≤ D) (hD : D ≤ N) (hr : 0 ≤ r) (hc : 0 ≤ c)
    (hE : E ≤ r ^ 2 * c ^ d)
    (hw : w ≤ (6 : ℝ) ^ d * Real.sqrt (E / (N.descFactorial d : ℝ))) :
    w ≤ r * Real.sqrt (36 * c / ((N : ℝ) - D + 1)) ^ d := by
  have hs : 0 < (N : ℝ) - D + 1 := by
    have : (D : ℝ) ≤ N := Nat.cast_le.mpr hD
    linarith
  have hdesc : 0 < (N.descFactorial d : ℝ) :=
    Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr (hd.trans hD))
  have hden := pow_le_descFactorial hd hD
  have hquot : E / (N.descFactorial d : ℝ) ≤
      r ^ 2 * (c / ((N : ℝ) - D + 1)) ^ d := by
    calc
      _ ≤ (r ^ 2 * c ^ d) / (N.descFactorial d : ℝ) :=
        div_le_div_of_nonneg_right hE hdesc.le
      _ ≤ (r ^ 2 * c ^ d) / ((N : ℝ) - D + 1) ^ d :=
        div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg r) (pow_nonneg hc d))
          (pow_pos hs d) hden
      _ = _ := by rw [div_pow]; ring
  have hsqrt : Real.sqrt (36 * c / ((N : ℝ) - D + 1)) =
      6 * Real.sqrt (c / ((N : ℝ) - D + 1)) := by
    rw [mul_div_assoc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 36)]
    have h6 : Real.sqrt (36 : ℝ) = 6 := by
      rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h6]
  calc
    w ≤ (6 : ℝ) ^ d * Real.sqrt (E / (N.descFactorial d : ℝ)) := hw
    _ ≤ (6 : ℝ) ^ d * Real.sqrt (r ^ 2 * (c / ((N : ℝ) - D + 1)) ^ d) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hquot) (by positivity)
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr,
        sqrt_pow_of_nonneg (div_nonneg hc hs.le), hsqrt, mul_pow]
      ring

/-- The coefficient estimate and homogeneity imply the termwise witness bound. -/
theorem responseWitness_term_bound
    (q : ℕ → ObservationPolynomial n k) (A : Finset (Fin n))
    (hB : 0 ≤ B) (hN : 6 * D ≤ m - 1)
    (henergy : ∀ d, 1 ≤ d → d ≤ D → coefficientEnergy (q d) ≤
      Real.rpow (n : ℝ) (-((A.card : ℝ) / 2)) * (B * rankScale n d k) ^ d)
    (hq : ∀ d, 1 ≤ d → d ≤ D → (q d).IsHomogeneous d)
    {d : ℕ} (hd1 : 1 ≤ d) (hdD : d ≤ D) :
    witnessNorm (liftPolynomial (substituteConnected (q d)) : Sample n m → ℝ) ≤
      Real.rpow (n : ℝ) (-((A.card : ℝ) / 4)) *
        Real.sqrt (36 * B * rankScale n d k / (((m - 1 : ℕ) : ℝ) - D + 1)) ^ d := by
  have hE := henergy d hd1 hdD
  rw [← target_norm_scale_sq n A.card] at hE
  simpa only [mul_assoc] using homogeneous_norm_estimate
    (r := Real.rpow (n : ℝ) (-((A.card : ℝ) / 4))) hdD (by omega : D ≤ m - 1)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) (mul_nonneg hB (rankScale_nonneg n d k))
    hE (witnessNorm_substituteConnected_le (q d) (hq d hd1 hdD)
      ((Nat.mul_le_mul_left 6 hdD).trans hN))

/-- The only remaining inputs are the response Taylor identity and its uniform
coefficient-energy bound. Substitution, lifting, and witness assembly are proved. -/
theorem uniformWitnessEstimates_of_response (hB : 0 < B)
    (hresponse : ∀ n m D k : ℕ, 4 ≤ n → 2 ≤ m → 1 ≤ D → (k = 3 ∨ k = 4) →
      D ^ 3 ≤ n → 6 * D ≤ m - 1 →
      ∀ A : Finset (Fin n), admissibleTarget n k A →
        ∃ q : ℕ → ObservationPolynomial n k,
          (∀ d, 1 ≤ d → d ≤ D → (q d).IsHomogeneous d) ∧
          (∀ d, 1 ≤ d → d ≤ D → coefficientEnergy (q d) ≤
            Real.rpow (n : ℝ) (-((A.card : ℝ) / 2)) * (B * rankScale n d k) ^ d) ∧
          (∀ d ≤ D, ∀ t : ObservationIndex n k → ℝ,
            iteratedDeriv d (fun s =>
              partitionFunction (fun I => τ * (s * t I)) *
                partitionFunction (fun I => s * t I) ^ (m - 1) *
                  (∑ r ∈ Finset.range D,
                    MvPolynomial.eval (connectedCoordinate (fun I => s * t I)) (q (r + 1)))) 0 =
            iteratedDeriv d (fun s =>
              partitionFunction (fun I => τ * (s * t I)) *
                partitionFunction (fun I => s * t I) ^ (m - 1) *
                  tiltedMoment (fun I => τ * (s * t I)) A) 0)) :
    UniformWitnessEstimates τ B := by
  intro n m D k hn hm hD hk hdeg hN A hA
  obtain ⟨q, hq, he, hj⟩ := hresponse n m D k hn hm hD hk hdeg hN A hA
  refine ⟨fun d => liftPolynomial (substituteConnected (q d)), ?_, ?_⟩
  · have hmatch := responseWitness_momentMatching q
      (fun d h1 hD => (hq d h1 hD).totalDegree_le) hN A hj
    have hw : responseWitness q D =
        (fun ω : Sample n m => ∑ d ∈ Finset.range D,
          liftPolynomial (substituteConnected (q (d + 1))) ω) := by
      funext ω
      exact responseWitness_eq_sum q ω
    rwa [hw] at hmatch
  · intro d hd1 hdD
    exact responseWitness_term_bound q A hB.le hN he hq hd1 hdD

end TensorLB
