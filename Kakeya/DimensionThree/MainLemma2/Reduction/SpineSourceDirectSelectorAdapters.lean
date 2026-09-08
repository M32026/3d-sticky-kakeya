/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectWindowData

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- The source mass and actual subshading pay multiplicity with exactly the
same loss. This adds no selection or new analytic hypothesis. -/
theorem source_direct_retained_payment (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (R : Finset iota) (Q' : SourceThreadedTower R T M C)
    (Z' : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (loss : ENNReal) (H : SourceZeroRetainedState Q Z R Z' Q' loss) :
    SourceDirectRetainedState Q Z R Q' Z' loss := by
  refine { toSourceZeroRetainedState := H, multiplicity := ?_ }
  apply ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset S
    (fun i => (Z i).toShadedBody) R (fun i => (Z' i).toShadedBody) loss _ H.mass
  exact Set.iUnion₂_subset fun i hi =>
    Set.subset_iUnion₂_of_subset i (H.restriction.subset hi) (H.subshade i)

/-- The ordinary P coefficient is identical to the coefficient in the
reviewed eccentric data. The actual parts are preserved, not re-factored. -/
theorem source_direct_plank_eccentric_data (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    {a m : Nat} {etaParent bias : Real} {D aw bw cw : NNReal}
    (P : SourceDirectPlankFactors Q Z a m etaParent bias D aw bw cw) :
    sourceParentPlankConstant delta bias = sourceZeroPlankConstant delta bias /\
    exists E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw,
      forall j, forall hj : j ∈ Q.indexSet a,
        (E.factor j hj).parts = (P.factor j hj).parts := by
  have hconstant : sourceParentPlankConstant delta bias = sourceZeroPlankConstant delta bias := rfl
  refine ⟨hconstant, {
    factor := P.factor
    coarse_lt_middle := P.coarse_lt_middle
    middle_bound := P.middle_bound
    dimension_comparison := P.comparison_one
    short_pos := P.short_positive
    short_le_middle := P.short_le_middle
    middle_le_long := P.middle_le_long
    long_lower := P.long_lower
    long_upper := P.long_upper
    eccentric := P.eccentric
    dimensions := P.dimensions
    same_tubes := P.same_tubes
    shade_floor := P.shade_floor
    complete_leaves := P.assigned_partition
    complete_leaf_mass := P.assigned_mass }, ?_⟩
  intro j hj
  rfl

end Kakeya.ML2Core
