module

public import TensorLB.UniformResponse
public import TensorLB.CumulantTaylor

/-!
# Main theorem

The response germ, Cauchy coefficient bounds, weighted even-cover count,
response Taylor identity, substitution bound, witness, and rank arithmetic are proved.
The cumulant coefficients satisfy the uniform local operator-norm estimate.
The cumulant Taylor identity identifies this series with the connected map,
supplying the bounded response extension and completing both estimation bounds.
-/

set_option autoImplicit false

public section

namespace TensorLB

/-- Theorem `thm:main` in `tensor_low_degree_k3_k4.tex`.
The positive real constant is chosen before all size parameters and the tensor
order. Both conclusions use this same constant. Fractional powers are real powers.

`TensorLB.UniformResponse` constructs the required bounded response from
`UniformConnectedTaylorBound`, proved by the cumulant tree estimate and
the connected-coordinate Taylor expansion. -/
theorem main :
    ∀ τ : ℝ, 1 < τ →
      ∃ C : ℝ, 0 < C ∧
        ∀ n m ℓ k : ℕ,
          4 ≤ n → 2 ≤ m → 1 ≤ ℓ → (k = 3 ∨ k = 4) →
          ℓ ^ 3 ≤ n →
          C * Real.rpow (n : ℝ) ((k : ℝ) / 2) *
            Real.rpow (ℓ : ℝ) ((k : ℝ) / 2 - 1) ≤ (m : ℝ) →
          ∀ A : Finset (Fin n), admissibleTarget n k A →
            correlation n m k ℓ τ A ^ 2 ≤
                Real.rpow (n : ℝ) (-((A.card : ℝ) / 2)) ∧
              1 - Real.rpow (n : ℝ) (-((A.card : ℝ) / 2)) ≤
                mmse n m k ℓ τ A := by
  apply main_of_uniformBoundedResponse
  apply uniformResponseRadius_exists_of_connectedTaylor
  apply uniformConnectedTaylor_exists_of_cumulantExpansion
  exact connectedCumulantExpansion

end TensorLB
