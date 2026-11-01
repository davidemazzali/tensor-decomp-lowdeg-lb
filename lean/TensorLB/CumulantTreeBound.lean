module

public import TensorLB.TreePartitionCounting

/-!
# The dependency-tree bound for Boolean character cumulants

The partition formula, exact factorization over disjoint supports, graph
coefficient cancellation, and quotient-tree counting give the standard bound
`2^(s-1)` times the number of spanning trees of the support-intersection graph.
Repeated character occurrences are distinct vertices throughout the argument.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {n : ℕ}

theorem abs_jointCharacterCumulant_le_quotient_trees (X : V → Finset (Fin n)) :
    |jointCharacterCumulant X| ≤
      ∑ R : {R : VertexPartition V // connectedRefinement (characterDependencyGraph X) R = R},
        (spanningTreeCount (quotientPartitionGraph (characterDependencyGraph X) R.val) : ℝ) := by
  have he : jointCharacterCumulant X =
      ∑ R : {R : VertexPartition V // connectedRefinement (characterDependencyGraph X) R = R},
        partitionMoment (characterMoment X) R.val *
          graphCumulantCoefficient (quotientPartitionGraph (characterDependencyGraph X) R.val) := by
    rw [jointCharacterCumulant_eq_quotient_sum, ← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro R _
  let : Nonempty (Quotient (partitionSetoid R.val)) := ⟨Quotient.mk _ (Classical.arbitrary V)⟩
  rw [abs_mul]
  calc
    _ ≤ 1 * (spanningTreeCount (quotientPartitionGraph (characterDependencyGraph X) R.val) : ℝ) :=
      mul_le_mul (abs_partition_moment_le_one X Finset.univ R.val)
        (abs_graphCumulantCoefficient_le_spanningTreeCount _) (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- The dependency graph estimate used in manuscript equation (14). -/
theorem abs_jointCharacterCumulant_le_trees (X : V → Finset (Fin n)) :
    |jointCharacterCumulant X| ≤
      2 ^ (Fintype.card V - 1) * (spanningTreeCount (characterDependencyGraph X) : ℝ) := by
  apply (abs_jointCharacterCumulant_le_quotient_trees X).trans
  have h := sum_connected_quotient_trees_le (characterDependencyGraph X)
  have hr :
      (∑ R : {R : VertexPartition V // connectedRefinement (characterDependencyGraph X) R = R},
        (spanningTreeCount (quotientPartitionGraph (characterDependencyGraph X) R.val) : ℝ)) ≤
      (spanningTreeCount (characterDependencyGraph X) : ℝ) * 2 ^ (Fintype.card V - 1) := by
    exact_mod_cast h
  simpa only [mul_comm] using hr

end

end TensorLB
