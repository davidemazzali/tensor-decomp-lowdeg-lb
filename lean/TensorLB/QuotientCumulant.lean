module

public import TensorLB.CharacterRefinement

/-!
# The quotient graph coefficient of a connected refinement

Once a connected refinement is fixed, its possible coarsenings correspond
exactly to partitions into independent sets of the quotient dependency graph.
The correspondence preserves the number of blocks and hence the cumulant weight.
-/

set_option autoImplicit false

@[expose] public section

namespace TensorLB

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def IndependentPartition (G : SimpleGraph V) (P : VertexPartition V) : Prop :=
  ∀ x y, G.Adj x y → ¬partitionSetoid P x y

def graphCumulantCoefficient (G : SimpleGraph V) : ℝ :=
  ∑ P : {P : VertexPartition V // IndependentPartition G P}, cumulantMobius P.val.parts.card

def refinementCoefficient (G : SimpleGraph V) (R : VertexPartition V) : ℝ :=
  ∑ P : {P : VertexPartition V // connectedRefinement G P = R}, cumulantMobius P.val.parts.card

def quotientPartitionGraph (G : SimpleGraph V) (R : VertexPartition V) :
    SimpleGraph (Quotient (partitionSetoid R)) := G.map (Quotient.mk (partitionSetoid R))

theorem coarseningPartitionEquiv_rel (R : VertexPartition V)
    (P : {P : VertexPartition V // R ≤ P}) (x y : V) :
    partitionSetoid (coarseningPartitionEquiv R P)
      (Quotient.mk _ x) (Quotient.mk _ y) ↔ partitionSetoid P.val x y := by
  let S := Setoid.correspondence (partitionSetoid R)
    ⟨partitionSetoid P.val, (partitionSetoid_le_iff R P.val).mpr P.property⟩
  change partitionSetoid (Finpartition.ofSetoid S) (Quotient.mk _ x) (Quotient.mk _ y) ↔ _
  rw [partitionSetoid_ofSetoid S]
  rfl

theorem independent_coarsening_iff (G : SimpleGraph V) (R : VertexPartition V)
    (P : {P : VertexPartition V // R ≤ P}) :
    IndependentPartition (quotientPartitionGraph G R) (coarseningPartitionEquiv R P) ↔
      ∀ x y, G.Adj x y → partitionSetoid P.val x y → partitionSetoid R x y := by
  constructor
  · intro h x y hxy hP
    by_contra hR
    have hne : Quotient.mk (partitionSetoid R) x ≠ Quotient.mk _ y :=
      fun he => hR (Quotient.exact he)
    exact h _ _ (SimpleGraph.map_adj_apply' hxy hne)
      ((coarseningPartitionEquiv_rel R P x y).mpr hP)
  · intro h a b hab hQ
    obtain ⟨hne, x, y, hxy, rfl, rfl⟩ := (SimpleGraph.map_adj' _ _ _ _).mp hab
    exact hne (Quotient.sound (h x y hxy ((coarseningPartitionEquiv_rel R P x y).mp hQ)))

def refinementFiberEquiv (G : SimpleGraph V) (R : VertexPartition V)
    (hR : connectedRefinement G R = R) :
    {P : VertexPartition V // connectedRefinement G P = R} ≃
      {Q : VertexPartition (Quotient (partitionSetoid R)) //
        IndependentPartition (quotientPartitionGraph G R) Q} where
  toFun P := ⟨coarseningPartitionEquiv R
      ⟨P.val, ((connectedRefinement_fiber_iff G P.val R).mp P.property).2.1⟩,
    (independent_coarsening_iff G R _).mpr
      ((connectedRefinement_fiber_iff G P.val R).mp P.property).2.2⟩
  invFun Q := ⟨((coarseningPartitionEquiv R).symm Q.val).val,
    (connectedRefinement_fiber_iff G _ R).mpr ⟨hR,
      ((coarseningPartitionEquiv R).symm Q.val).property,
      (independent_coarsening_iff G R _).mp (by
        simpa only [Equiv.apply_symm_apply] using Q.property)⟩⟩
  left_inv P := by
    apply Subtype.ext
    exact congrArg (fun Q : {Q : VertexPartition V // R ≤ Q} => Q.val)
      ((coarseningPartitionEquiv R).symm_apply_apply
      ⟨P.val, ((connectedRefinement_fiber_iff G P.val R).mp P.property).2.1⟩)
  right_inv Q := by
    apply Subtype.ext
    exact (coarseningPartitionEquiv R).apply_symm_apply Q.val

theorem refinementFiberEquiv_card (G : SimpleGraph V) (R : VertexPartition V)
    (hR : connectedRefinement G R = R)
    (P : {P : VertexPartition V // connectedRefinement G P = R}) :
    (refinementFiberEquiv G R hR P).val.parts.card = P.val.parts.card :=
  coarseningPartitionEquiv_card R _

theorem refinementCoefficient_eq_quotient (G : SimpleGraph V) (R : VertexPartition V)
    (hR : connectedRefinement G R = R) :
    refinementCoefficient G R = graphCumulantCoefficient (quotientPartitionGraph G R) := by
  unfold refinementCoefficient graphCumulantCoefficient
  rw [← Equiv.sum_comp (refinementFiberEquiv G R hR)]
  exact Finset.sum_congr rfl (fun P _ => congrArg cumulantMobius (refinementFiberEquiv_card G R hR P).symm)

theorem refinementCoefficient_eq_zero (G : SimpleGraph V) (R : VertexPartition V)
    (hR : connectedRefinement G R ≠ R) : refinementCoefficient G R = 0 := by
  apply Finset.sum_eq_zero
  intro P _
  exact False.elim (hR ((connectedRefinement_fiber_iff G P.val R).mp P.property).1)

theorem jointCharacterCumulant_eq_quotient_sum {n : ℕ} (X : V → Finset (Fin n)) :
    jointCharacterCumulant X =
      ∑ R : VertexPartition V, if connectedRefinement (characterDependencyGraph X) R = R then
        partitionMoment (characterMoment X) R *
          graphCumulantCoefficient (quotientPartitionGraph (characterDependencyGraph X) R) else 0 := by
  rw [jointCharacterCumulant_group_by_refinement]
  apply Finset.sum_congr rfl
  intro R _
  change partitionMoment (characterMoment X) R * refinementCoefficient _ R = _
  by_cases hR : connectedRefinement (characterDependencyGraph X) R = R
  · rw [ite_eq_left hR, refinementCoefficient_eq_quotient _ _ hR]
  · rw [ite_eq_right hR, refinementCoefficient_eq_zero _ _ hR, mul_zero]

end

end TensorLB
