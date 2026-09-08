/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceParentIndependent

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- An actual B5 certificate belongs to its immediate input and output families.
There is no claim here about partitions chosen after this operation. -/
structure SourceImmediateBiasedParent (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (F G : Finset iota) (a m : Nat) (j : iota) (bias : Real) where
  partition : ML2Assembly.SourceDescendantPartition
    (F.filter (fun i => Q.place a i = j)) (Q.retainedAssignedFibre F a m j)
  assignment : partition.assign = Q.place m
  normalization : EuclideanSpace Real (Fin 3) ≃ᵃ[Real] EuclideanSpace Real (Fin 3)
  comparison : NNReal
  comparison_one_le : 1 <= comparison
  normalizedThickness : NNReal
  normalized_positive : 0 < normalizedThickness
  normalized_le_one : normalizedThickness <= 1
  normalized_geometry : forall i, i ∈ Q.retainedAssignedFibre F a m j ->
    (normalizedThickness : ENNReal) <= ethickness.scale Real
      (((Q.tube m i).toConvexSpaceBody).mapAffine normalization).carrier
  actual : ML2Assembly.SourceAffineWeightedParent partition
    (fun i => (Z i).toShadedBody) (fun i => (Q.tube m i).toConvexSpaceBody)
    (Q.tube a j).toConvexSpaceBody normalization comparison normalizedThickness bias
  output_nodes : Q.retainedAssignedFibre G a m j = actual.selection.selected
  output_leaves : G.filter (fun i => Q.place a i = j) =
    ML2Assembly.sourceDescendantUnion partition actual.selection.selected
  whole_output_fibres : forall k, k ∈ actual.selection.selected ->
    G.filter (fun i => Q.place a i = j /\ Q.place m i = k) =
      F.filter (fun i => Q.place a i = j /\ Q.place m i = k)

/-- Every marked stage executes the displayed actual B5 operations. The remaining
stages are the legal whole-cell operations in the trace, with their own payments. -/
structure SourcePaidFactorHistory (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (R : Finset iota) (bias : Real) (K : Nat) where
  trace : SourceWholeFactorTrace Q Z R K
  length_bound : trace.length <= K
  monotone : forall n k, n <= k -> k <= trace.length -> trace.state k <= trace.state n
  factoringStages : Finset Nat
  stage_bound : forall n, n ∈ factoringStages -> n < trace.length
  coarse : Nat -> Nat
  coarse_lt : forall n, n ∈ factoringStages -> coarse n < trace.level n
  stage : forall n, n ∈ factoringStages -> forall j,
    j ∈ Q.assignedFootprint (trace.state n) (coarse n) ->
      SourceImmediateBiasedParent Q Z (trace.state n) (trace.state (n + 1))
        (coarse n) (trace.level n) j bias
  stage_blocks : forall n, forall hn : n ∈ factoringStages,
    trace.retainedBlocks n =
      (Q.assignedFootprint (trace.state n) (coarse n)).attach.biUnion
        (fun j => (stage n hn j.val j.property).actual.selection.parts)
  actual_loss_paid : forall n, forall hn : n ∈ factoringStages,
    forall j, forall hj : j ∈ Q.assignedFootprint (trace.state n) (coarse n),
      nonempty_biasedFactorization.L 3
        (Q.retainedAssignedFibre (trace.state n) (coarse n) (trace.level n) j).card
        (stage n hn j hj).normalizedThickness bias <= trace.stepLoss n

/-- Current parts may cross historical parts. The actual intersections form the
comparison diagram; only an explicitly whole surviving old part keeps its hull.
The displayed analytic coefficient pays the actual two reference comparisons. -/
structure SourceCurrentHistoricalPieces (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    {F G R : Finset iota} (Q' : SourceThreadedTower R T M C)
    {a m : Nat} {j : iota} {bias : Real}
    (H : SourceImmediateBiasedParent Q Z F G a m j bias)
    (B : SourceParentBiasedFactors Q' a m j bias) where
  retained_subset : R <= G
  current_nodes_subset : Q'.fibre a m j <= H.actual.selection.selected
  current_piece_union : forall part, part ∈ B.partition.parts ->
    part = H.actual.selection.parts.biUnion (fun old => part ∩ old)
  historical_piece_union : forall old, old ∈ H.actual.selection.parts ->
    old ∩ Q'.fibre a m j = B.partition.parts.biUnion (fun part => part ∩ old)
  piece_disjoint : forall part, part ∈ B.partition.parts ->
    (H.actual.selection.parts : Set (Finset iota)).PairwiseDisjoint (fun old => part ∩ old)
  piece_hull : forall part, part ∈ B.partition.parts ->
    forall old, old ∈ H.actual.selection.parts -> (part ∩ old).Nonempty ->
      (part ∩ old).convexHull_biUnion (fun i => (Q'.tube m i).toConvexSpaceBody) =
        (part ∩ old).convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)
  piece_hull_le_current : forall part, part ∈ B.partition.parts ->
    forall old, old ∈ H.actual.selection.parts -> (part ∩ old).Nonempty ->
      (part ∩ old).convexHull_biUnion (fun i => (Q'.tube m i).toConvexSpaceBody) <=
        part.convexHull_biUnion (fun i => (Q'.tube m i).toConvexSpaceBody)
  piece_hull_le_historical : forall part, part ∈ B.partition.parts ->
    forall old, old ∈ H.actual.selection.parts -> (part ∩ old).Nonempty ->
      (part ∩ old).convexHull_biUnion (fun i => (Q'.tube m i).toConvexSpaceBody) <=
        old.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)
  whole_historical_hull : forall old, old ∈ H.actual.selection.parts ->
    old <= Q'.fibre a m j ->
      old.convexHull_biUnion (fun i => (Q'.tube m i).toConvexSpaceBody) =
        old.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)
  reference_same_parent : (Q'.tube a j).toConvexSpaceBody = (Q.tube a j).toConvexSpaceBody
  referencePayment : ENNReal
  payment_eq : referencePayment = (nonempty_biasedFactorization.C 3 bias : ENNReal) *
    ((max B.comparison H.comparison : NNReal) : ENNReal) ^ bias
  payment_positive : 0 < referencePayment
  payment_finite : referencePayment < ⊤
  current_capture_paid : forall part, part ∈ B.partition.parts ->
    referencePayment⁻¹ *
      (volume (part.convexHull_biUnion (fun i => (Q'.tube m i).toConvexSpaceBody)).carrier /
        volume (Q'.tube a j).carrier) ^ bias *
      Kakeya.maxDensity (Q'.fibre a m j) (fun i => (Q'.tube m i).toConvexSpaceBody) <=
        Kakeya.densityIn part (fun i => (Q'.tube m i).toConvexSpaceBody)
          (part.convexHull_biUnion (fun i => (Q'.tube m i).toConvexSpaceBody))

/-- Final factorings are actual final-family certificates, independent of which
old parts they intersect. Their real normalized scale and B5 cost are also paid. -/
structure SourceCurrentWindowHistory (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    {R : Finset iota} (Q' : SourceThreadedTower R T M C)
    {e bias : Real} {a b : Nat} (B : SourceJointWindowFactors Q' e a b bias) (K : Nat) where
  history : SourcePaidFactorHistory Q Z R bias K
  stage : Nat -> Nat
  marked : forall m, SourceTowerWindow delta M e a b m -> stage m ∈ history.factoringStages
  coarse_eq : forall m, SourceTowerWindow delta M e a b m -> history.coarse (stage m) = a
  level_eq : forall m, SourceTowerWindow delta M e a b m -> history.trace.level (stage m) = m
  earlier_occupied : forall m, SourceTowerWindow delta M e a b m ->
    forall j, j ∈ Q'.indexSet a ->
      j ∈ Q.assignedFootprint (history.trace.state (stage m)) a
  immediate : forall m, SourceTowerWindow delta M e a b m ->
    forall j, j ∈ Q'.indexSet a ->
      SourceImmediateBiasedParent Q Z (history.trace.state (stage m))
        (history.trace.state (stage m + 1)) a m j bias
  immediate_stage : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
      HEq (immediate m hm j hj)
        (history.stage (stage m) (marked m hm) j
          ((coarse_eq m hm).symm ▸ earlier_occupied m hm j hj))
  pieces : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
      SourceCurrentHistoricalPieces Q Z Q' (immediate m hm j hj) (B.factor m hm j hj)
  normalizedThickness : Nat -> iota -> NNReal
  normalized_positive : forall m, SourceTowerWindow delta M e a b m ->
    forall j, j ∈ Q'.indexSet a -> 0 < normalizedThickness m j
  normalized_le_one : forall m, SourceTowerWindow delta M e a b m ->
    forall j, j ∈ Q'.indexSet a -> normalizedThickness m j <= 1
  normalized_geometry : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a, forall i, i ∈ Q'.fibre a m j ->
      (normalizedThickness m j : ENNReal) <= ethickness.scale Real
        (((Q'.tube m i).toConvexSpaceBody).mapAffine (B.factor m hm j hj).normalization).carrier
  current_loss_paid : forall m, SourceTowerWindow delta M e a b m ->
    forall j, j ∈ Q'.indexSet a ->
      nonempty_biasedFactorization.L 3 (Q'.fibre a m j).card (normalizedThickness m j) bias <=
        history.trace.stepLoss (stage m)

/-- Reparented final factors use the same paid trace. Historical reparent B5
operations retain their stage's cells; the final factors carry their own capture. -/
structure SourceCurrentParentHistory (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    {R : Finset iota} (Q' : SourceThreadedTower R T M C)
    {e bias etaParent tau : Real} {a b : Nat} {cap : NNReal}
    (B : SourceJointWindowFactors Q' e a b bias)
    (P : SourceActualParent Q' B etaParent tau cap) (K : Nat) where
  coarse_history : SourceCurrentWindowHistory Q Z Q' B K
  stage : Nat -> iota -> iota -> Nat
  marked : forall m, SourceTowerWindow delta M e a b m ->
    forall j, j ∈ Q'.indexSet a -> forall jp, jp ∈ Q'.fibre a P.parent j ->
      stage m j jp ∈ coarse_history.history.factoringStages
  coarse_eq : forall m, SourceTowerWindow delta M e a b m ->
    forall j, j ∈ Q'.indexSet a -> forall jp, jp ∈ Q'.fibre a P.parent j ->
      coarse_history.history.coarse (stage m j jp) = P.parent
  level_eq : forall m, SourceTowerWindow delta M e a b m ->
    forall j, j ∈ Q'.indexSet a -> forall jp, jp ∈ Q'.fibre a P.parent j ->
      coarse_history.history.trace.level (stage m j jp) = m
  earlier_occupied : forall m, SourceTowerWindow delta M e a b m ->
    forall j, j ∈ Q'.indexSet a -> forall jp, jp ∈ Q'.fibre a P.parent j ->
      jp ∈ Q.assignedFootprint (coarse_history.history.trace.state (stage m j jp)) P.parent
  immediate : forall m, SourceTowerWindow delta M e a b m ->
    forall j, j ∈ Q'.indexSet a -> forall jp, jp ∈ Q'.fibre a P.parent j ->
      SourceImmediateBiasedParent Q Z (coarse_history.history.trace.state (stage m j jp))
        (coarse_history.history.trace.state (stage m j jp + 1)) P.parent m jp bias
  immediate_stage : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
    forall jp, forall hjp : jp ∈ Q'.fibre a P.parent j,
      HEq (immediate m hm j hj jp hjp)
        (coarse_history.history.stage (stage m j jp) (marked m hm j hj jp hjp) jp
          ((coarse_eq m hm j hj jp hjp).symm ▸ earlier_occupied m hm j hj jp hjp))
  pieces : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
    forall jp, forall hjp : jp ∈ Q'.fibre a P.parent j,
      SourceCurrentHistoricalPieces Q Z Q' (immediate m hm j hj jp hjp)
        (P.reparented m hm j hj jp hjp).factor
  normalizedThickness : Nat -> iota -> iota -> NNReal
  normalized_positive : forall m, SourceTowerWindow delta M e a b m ->
    forall j, j ∈ Q'.indexSet a -> forall jp, jp ∈ Q'.fibre a P.parent j ->
      0 < normalizedThickness m j jp
  normalized_le_one : forall m, SourceTowerWindow delta M e a b m ->
    forall j, j ∈ Q'.indexSet a -> forall jp, jp ∈ Q'.fibre a P.parent j ->
      normalizedThickness m j jp <= 1
  normalized_geometry : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
    forall jp, forall hjp : jp ∈ Q'.fibre a P.parent j,
    forall i, i ∈ Q'.fibre P.parent m jp ->
      (normalizedThickness m j jp : ENNReal) <= ethickness.scale Real
        (((Q'.tube m i).toConvexSpaceBody).mapAffine
          (P.reparented m hm j hj jp hjp).factor.normalization).carrier
  current_loss_paid : forall m, SourceTowerWindow delta M e a b m ->
    forall j, j ∈ Q'.indexSet a -> forall jp, jp ∈ Q'.fibre a P.parent j ->
      nonempty_biasedFactorization.L 3 (Q'.fibre P.parent m jp).card
        (normalizedThickness m j jp) bias <= coarse_history.history.trace.stepLoss (stage m j jp)

end Kakeya.ML2Core
