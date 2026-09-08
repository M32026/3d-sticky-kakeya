/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceRetainedAnalyticData
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceEccentricAssignedPartB
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourcePaidDescentClosure

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- The literal common retained state. Its statistics use the actual final
shading; a per-tube shading floor is an additional conclusion only in P. -/
structure SourceDirectRetainedState (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (R : Finset iota) (Q' : SourceThreadedTower R T M C)
    (Z' : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (loss : ENNReal) : Prop extends SourceZeroRetainedState Q Z R Z' Q' loss where
  multiplicity : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
    loss * ShadedBody.multiplicity R (fun i => (Z' i).toShadedBody)

/-- F records precisely a genuine parent, its actual density and the actual
assigned count floor. SourceZeroFloor already contains those literal rows. -/
structure SourceDirectFloor (Q : SourceThreadedTower S T M C)
    (e tau etaParent : Real) (a b : Nat) where
  parent : Nat
  geometry : SourceZeroFloor Q e tau etaParent a b parent

/-- A complete-cell certificate belongs to its immediate stage. Later
restrictions retain descendants inside its actual output, with no assertion
that all final factor parts were parts of an earlier biased partition. -/
structure SourceDirectPlankCellStage (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (R : Finset iota)
    (Z' : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))) (m : Nat) (K : Nat) where
  before : Finset iota
  after : Finset iota
  before_subset : before <= S
  before_nonempty : before.Nonempty
  after_nonempty : after.Nonempty
  selected : SourceWholeCellStep Q before after m
  final_subset : R <= after
  stageShade : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))
  same_tubes : forall i, (stageShade i).toTube = T i
  subshade : forall i, (stageShade i).shade <= (Z i).shade
  final_subshade : forall i, (Z' i).shade <= (stageShade i).shade
  prefixLoss : ENNReal
  stageLoss : ENNReal
  suffixLoss : ENNReal
  prefix_one : 1 <= prefixLoss
  loss_one : 1 <= stageLoss
  suffix_one : 1 <= suffixLoss
  prefix_finite : prefixLoss < ⊤
  loss_finite : stageLoss < ⊤
  suffix_finite : suffixLoss < ⊤
  prefix_paid : (∑ i ∈ S, volume (Z i).shade) <=
    prefixLoss * ∑ i ∈ before, volume (stageShade i).shade
  stage_paid : (∑ i ∈ before, volume (stageShade i).shade) <=
    stageLoss * ∑ i ∈ after, volume (stageShade i).shade
  suffix_paid : (∑ i ∈ after, volume (stageShade i).shade) <=
    suffixLoss * ∑ i ∈ R, volume (Z' i).shade
  total_loss : prefixLoss * stageLoss * suffixLoss <= sourceFixedPreparationLoss K delta

/-- The actual one-level ordinary P data. D is the fixed John-to-affine
thickness comparison used by the reviewed eccentric consumers; no axis
identity or biased-factorization coefficient is substituted. -/
structure SourceDirectPlankFactors (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (a m : Nat) (etaParent bias : Real) (D aw bw cw : NNReal) where
  factor : forall j, j ∈ Q.indexSet a ->
    ConvexSpaceBody.Factorization (Q.fibre a m j)
      (fun k => (Q.tube m k).toConvexSpaceBody) (sourceParentPlankConstant delta bias)
  coarse_lt_middle : a < m
  middle_bound : m <= M
  comparison_one : 1 <= D
  short_positive : 0 < aw
  short_le_middle : aw <= bw
  middle_le_long : bw <= cw
  long_lower : Real.toNNReal (1 / (4 * Real.sqrt 3)) <= cw
  long_upper : cw <= 64
  eccentric : aw / bw <= delta ^ etaParent
  dimensions : forall j, forall hj : j ∈ Q.indexSet a,
    forall part, part ∈ (factor j hj).parts ->
      SourceZeroFactorDimensions D aw bw cw
        (part.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody))
  same_tubes : forall i, (Z i).toTube = T i
  shade_floor : forall i, i ∈ S ->
    (delta : ENNReal) ^ (10 : Real) * volume (T i).carrier <= volume (Z i).shade
  nonempty_parts : forall j, forall hj : j ∈ Q.indexSet a,
    forall part, part ∈ (factor j hj).parts -> part.Nonempty
  assigned_partition : forall j, forall hj : j ∈ Q.indexSet a,
    Q.cell a j = (factor j hj).parts.biUnion
      (fun part => S.filter (fun i => Q.place m i ∈ part))
  assigned_mass : forall j, forall hj : j ∈ Q.indexSet a,
    (∑ i ∈ Q.cell a j, volume (Z i).shade) =
      ∑ part ∈ (factor j hj).parts,
        ∑ i ∈ S.filter (fun i => Q.place m i ∈ part), volume (Z i).shade

/-- P exposes one level and the ordinary factors on the final tower. The
immediate complete-cell selection is bound to the original named Q. -/
structure SourceDirectPlank (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (R : Finset iota) (Q' : SourceThreadedTower R T M C)
    (Z' : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (e etaParent bias : Real) (a b K : Nat) (D : NNReal) where
  level : Nat
  in_window : SourceTowerWindow delta M e a b level
  short : NNReal
  middle : NNReal
  long : NNReal
  factors : SourceDirectPlankFactors Q' Z' a level etaParent bias D short middle long
  cell_stage : SourceDirectPlankCellStage Q Z R Z' level K

/-- The source D endpoint is the actual integer potential inequality.
It does not claim that the final output includes a particular failed test. -/
def SourceDirectPotentialDrop (Q : SourceThreadedTower S T M C)
    (R : Finset iota) (h : Real) : Prop :=
  Q.assignedPotential h R + 1 <= Q.assignedPotential h S

/-- All three alternatives use this same retained family, restricted tower,
actual subshading, upper-window rows and uniformly paid mass. -/
structure SourceDirectWindowOutcome (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (R : Finset iota) (Q' : SourceThreadedTower R T M C)
    (Z' : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (N J A0 A1 : Nat) (e : Real) (eta : Nat -> Real)
    (etaParent bias etaF : Real) (K : Nat) (D : NNReal) (a b : Nat) : Prop where
  retained : SourceDirectRetainedState Q Z R Q' Z' (sourceFixedPreparationLoss K delta)
  input : SourceFixedTowerInput Q' A0 A1 etaF
  upper : SourceParentUpperWindow Q' A0 A1 N eta e a b J
  alternative :
    Nonempty (SourceDirectFloor Q' e (eta (J + 1)) etaParent a b) \/
    Nonempty (SourceDirectPlank Q Z R Q' Z' e etaParent bias a b K D) \/
    SourceDirectPotentialDrop Q R (eta 1 * e ^ 2 / 8)

end Kakeya.ML2Core
