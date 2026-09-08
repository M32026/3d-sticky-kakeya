/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectWindowTrial
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectOrdinaryFragments

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- The exact descendant-count projection consumed at one named level. -/
def SourceTerminalDescendantCounts (Q : SourceThreadedTower S T M C) (k : Nat) : Prop :=
  forall j, j ∈ Q.indexSet k -> forall j', j' ∈ Q.indexSet k ->
    ((Q.cell k j).card : ENNReal) <= 2 * ((Q.cell k j').card : ENNReal)

/-- Only these two count levels enter the completed P consumers. -/
structure SourceTerminalPlankStatistics (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))) (a m : Nat) : Prop where
  same_tubes : forall i, (Z i).toTube = T i
  outer_count : SourceTerminalDescendantCounts Q a
  middle_count : SourceTerminalDescendantCounts Q m

/-- Actual paid restriction, without continuation statistics. Terminal P
consumes this state once; F and D below separately retain full statistics. -/
structure SourceTerminalRetainedState (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (R : Finset iota) (Q' : SourceThreadedTower R T M C)
    (Z' : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))) (loss : ENNReal) : Prop where
  restriction : SourceTowerRestriction Q Q'
  nonempty : R.Nonempty
  original_tubes : forall i, (Z i).toTube = T i
  same_tubes : forall i, (Z' i).toTube = T i
  subshade : forall i, (Z' i).shade <= (Z i).shade
  mass : (∑ i ∈ S, volume (Z i).shade) <= loss * ∑ i ∈ R, volume (Z' i).shade
  fullness : ShadedBody.fullness' S (fun i => (Z i).toShadedBody) <=
    loss * ShadedBody.fullness' R (fun i => (Z' i).toShadedBody)
  multiplicity : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
    loss * ShadedBody.multiplicity R (fun i => (Z' i).toShadedBody)

/-- A common dimension bin selects complete old parts and then complete
a-cells. Every final factor is an unchanged old part, with the same hull.
Eccentricity is tested after this actual bin has been constructed. -/
structure SourceTerminalCommonFactorBin (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    {G : Finset iota} {QG : SourceThreadedTower G T M C}
    {a m : Nat} {bias : Real} {A : NNReal} {Kstage : Nat}
    (B : SourceDirectOrdinaryCellStage Q Z G QG a m bias A Kstage)
    (R : Finset iota) (QR : SourceThreadedTower R T M C) (D : NNReal) (K : Nat) where
  partFamily : Finset iota
  partTower : SourceThreadedTower partFamily T M C
  part_restriction : SourceTowerRestriction QG partTower
  part_nonempty : partFamily.Nonempty
  part_step : SourceWholeCellStep Q G partFamily m
  kept : forall j, j ∈ Q.indexSet a -> Finset (Finset iota)
  kept_subset : forall j, forall hj : j ∈ Q.indexSet a,
    kept j hj <= (B.factor j hj).parts
  part_fibres : forall j, forall hj : j ∈ Q.indexSet a,
    partTower.fibre a m j = (kept j hj).biUnion id
  final_restriction : SourceTowerRestriction partTower QR
  outer_step : SourceWholeCellStep Q partFamily R a
  nonempty : R.Nonempty
  coarse_origin : forall j, j ∈ QR.indexSet a -> j ∈ Q.indexSet a
  middle_cells : forall j, j ∈ QR.indexSet m -> QR.cell m j = Q.cell m j
  statistics : SourceTerminalPlankStatistics QR Z a m
  short : NNReal
  middle : NNReal
  long : NNReal
  comparison_one : 1 <= D
  short_positive : 0 < short
  short_le_middle : short <= middle
  middle_le_long : middle <= long
  long_lower : Real.toNNReal (1 / (4 * Real.sqrt 3)) <= long
  long_upper : long <= 64
  factor : forall j, j ∈ QR.indexSet a ->
    Factorization (QR.fibre a m j) (fun k => (QR.tube m k).toConvexSpaceBody)
      (sourceParentPlankConstant delta bias)
  factor_parts : forall j, forall hj : j ∈ QR.indexSet a,
    (factor j hj).parts = kept j (coarse_origin j hj)
  dimensions : forall j, forall hj : j ∈ QR.indexSet a,
    forall part, part ∈ (factor j hj).parts ->
      SourceZeroFactorDimensions D short middle long
        (part.convexHull_biUnion (fun k => (QR.tube m k).toConvexSpaceBody))
  retained : SourceTerminalRetainedState Q Z R QR Z (sourceFixedPreparationLoss K delta)
  cell_stage : SourceDirectPlankCellStage Q Z R Z m K
  stage_before : cell_stage.before = S
  stage_after : cell_stage.after = G
  stage_shading : cell_stage.stageShade = Z
  part_loss : ENNReal
  outer_loss : ENNReal
  part_loss_one : 1 <= part_loss
  outer_loss_one : 1 <= outer_loss
  part_loss_finite : part_loss < ⊤
  outer_loss_finite : outer_loss < ⊤
  part_mass : (∑ i ∈ G, volume (Z i).shade) <=
    part_loss * ∑ i ∈ partFamily, volume (Z i).shade
  outer_mass : (∑ i ∈ partFamily, volume (Z i).shade) <=
    outer_loss * ∑ i ∈ R, volume (Z i).shade
  total_loss : B.stageLoss * part_loss * outer_loss <= sourceFixedPreparationLoss K delta

/-- Source-ordered alternative: P needs only its two actual count levels.
Both continuing alternatives carry the full statistics of their actual
retained family and shading, as in the original protected selector. -/
structure SourceTerminalWindowOutcome (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (R : Finset iota) (Q' : SourceThreadedTower R T M C)
    (Z' : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (N J A0 A1 : Nat) (e : Real) (eta : Nat -> Real)
    (etaParent bias etaF : Real) (K : Nat) (D : NNReal) (a b : Nat) : Prop where
  retained : SourceTerminalRetainedState Q Z R Q' Z' (sourceFixedPreparationLoss K delta)
  input : SourceFixedTowerInput Q' A0 A1 etaF
  upper : SourceParentUpperWindow Q' A0 A1 N eta e a b J
  alternative :
    (exists P : SourceDirectPlank Q Z R Q' Z' e etaParent bias a b K D,
      SourceTerminalPlankStatistics Q' Z' a P.level) \/
    (SourceTowerStatistics Q' Z' /\
      (Nonempty (SourceDirectFloor Q' e (eta (J + 1)) etaParent a b) \/
        SourceDirectPotentialDrop Q R (eta 1 * e ^ 2 / 8)))

end Kakeya.ML2Core
