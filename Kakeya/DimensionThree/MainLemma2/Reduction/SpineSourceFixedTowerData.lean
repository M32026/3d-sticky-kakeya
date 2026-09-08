/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFibreSupplyProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCentredHandBack
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteClosure

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceFixedMesh

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {V : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M : Nat}

structure SourceThreadedTower (S : Finset iota)
    (V : iota -> Tube delta (EuclideanSpace Real (Fin 3))) (M : Nat) (C : Nat) where
  indexSet : Nat -> Finset iota
  place : Nat -> iota -> iota
  parent : Nat -> iota -> iota
  tube : (k : Nat) -> iota -> Tube (sourceTowerRadius delta M k) (EuclideanSpace Real (Fin 3))
  tube_injective : ∀ k, k <= M -> Set.InjOn (tube k) (indexSet k : Set iota)
  place_mem : ∀ k, k <= M -> ∀ i ∈ S, place k i ∈ indexSet k
  place_surjective : ∀ k, k <= M -> ∀ j ∈ indexSet k,
    ∃ i ∈ S, place k i = j
  leaf_containment : ∀ k, k <= M -> ∀ i ∈ S,
    (V i).toConvexSpaceBody <= (tube k (place k i)).toConvexSpaceBody
  parent_mem : ∀ k, k < M -> ∀ j ∈ indexSet (k + 1), parent (k + 1) j ∈ indexSet k
  parent_composition : ∀ k, k < M -> ∀ i ∈ S,
    place k i = parent (k + 1) (place (k + 1) i)
  parent_containment : ∀ k, k < M -> ∀ j ∈ indexSet (k + 1),
    (tube (k + 1) j).toConvexSpaceBody <= (tube k (parent (k + 1) j)).toConvexSpaceBody
  bottom_index : indexSet M = S
  bottom_place : ∀ i ∈ S, place M i = i
  bottom_body : ∀ i ∈ S, (tube M i).toConvexSpaceBody = (V i).toConvexSpaceBody
  containment_multiplicity : ∀ k, k <= M -> ∀ i ∈ S,
    (open scoped Classical in
      ((indexSet k).filter
        (fun j => (V i).toConvexSpaceBody <= (tube k j).toConvexSpaceBody)).card) <= C

open scoped Classical in
noncomputable def SourceThreadedTower.cell {C : Nat} (Q : SourceThreadedTower S V M C)
    (k : Nat) (j : iota) : Finset iota := S.filter (fun i => Q.place k i = j)

open scoped Classical in
noncomputable def SourceThreadedTower.fibre {C : Nat} (Q : SourceThreadedTower S V M C)
    (a b : Nat) (j : iota) : Finset iota := (Q.cell a j).image (Q.place b)

structure SourceTowerGeometry {C : Nat} (Q : SourceThreadedTower S V M C)
    (A0 A1 : Nat) : Prop where
  nonempty : S.Nonempty
  original_centred : ∀ i ∈ S, (V i).IsCentred
  original_ball : ∀ i ∈ S, (V i).carrier <= Metric.closedBall 0 (3 / 4)
  original_ed : Kakeya.VeryNotSticky.IsLineEssDistinct A0 S V
  coarse_centred : ∀ k, k < M -> ∀ j ∈ Q.indexSet k, (Q.tube k j).IsCentred
  coarse_ball : ∀ k, k < M -> ∀ j ∈ Q.indexSet k,
    (Q.tube k j).carrier <= Metric.closedBall 0 3
  coarse_ed : ∀ k, k < M ->
    Kakeya.VeryNotSticky.IsLineEssDistinct A1 (Q.indexSet k) (Q.tube k)
  coarse_card : ∀ k, k < M ->
    ((Q.indexSet k).card : Real) <= (32 / (sourceTowerRadius delta M k : Real)) ^ 6
  segment_sharing : ∀ k, k < M -> ∀ x y : EuclideanSpace Real (Fin 3),
    dist x y = 1 ->
    (open scoped Classical in
      ((Q.indexSet k).filter (fun j => segment Real x y <= (Q.tube k j).carrier)).card) <= C

structure SourceTowerStatistics {C : Nat} (Q : SourceThreadedTower S V M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))) : Prop where
  same_tubes : ∀ i, (Z i).toTube = V i
  descendant_count : ∀ k, k <= M -> ∀ j ∈ Q.indexSet k, ∀ j' ∈ Q.indexSet k,
    ((Q.cell k j).card : ENNReal) <= 2 * ((Q.cell k j').card : ENNReal)
  two_level_count : ∀ a b, a < b -> b <= M ->
    ∀ j ∈ Q.indexSet a, ∀ j' ∈ Q.indexSet a,
      ((Q.fibre a b j).card : ENNReal) <= 2 * ((Q.fibre a b j').card : ENNReal)
  two_level_density : ∀ a b, a < b -> b <= M ->
    ∀ j ∈ Q.indexSet a, ∀ j' ∈ Q.indexSet a,
      Kakeya.maxDensity (Q.fibre a b j) (fun k => (Q.tube b k).toConvexSpaceBody) <=
        2 * Kakeya.maxDensity (Q.fibre a b j') (fun k => (Q.tube b k).toConvexSpaceBody)
  fibre_mass : ∀ k, k <= M -> ∀ j ∈ Q.indexSet k, ∀ j' ∈ Q.indexSet k,
    (∑ i ∈ Q.cell k j, volume (Z i).shade) <= 2 * (∑ i ∈ Q.cell k j', volume (Z i).shade)

def SourceTowerWindow (delta : NNReal) (M : Nat) (e : Real) (a b k : Nat) : Prop :=
  a < k /\ k < b /\
    ((sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M a : Real)) ^ (1 - e) <=
      (sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M k : Real) /\
    (sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M k : Real) <=
      ((sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M a : Real)) ^ e

def sourceTowerWindowConstant (C A0 A1 : Nat) : Nat :=
  max (max (300 ^ 9 * C) (625 * max A0 A1)) 3

structure SourceTowerDividingWindow {C : Nat} (Q : SourceThreadedTower S V M C)
    (A0 A1 N : Nat) (eta : Nat -> Real) (e : Real) (a b J : Nat) : Prop where
  source_index_lower : 1 <= J
  source_index_upper : J <= N
  coarse_lt_fine : a < b
  fine_bound : b <= M
  scale_separation : (sourceTowerRadius delta M b : Real) /
    (sourceTowerRadius delta M a : Real) <= (delta : Real) ^ e
  coarse_density : a > 0 -> ∀ j ∈ Q.indexSet 0,
    Kakeya.maxDensity (Q.fibre 0 a j) (fun k => (Q.tube a k).toConvexSpaceBody) <=
      (sourceTowerWindowConstant C A0 A1 : ENNReal) ^ N * ENNReal.ofReal
        (((sourceTowerRadius delta M 0 : Real) / (sourceTowerRadius delta M a : Real)) ^ eta J)
  middle_density : ∀ j ∈ Q.indexSet a,
    Kakeya.maxDensity (Q.fibre a b j) (fun k => (Q.tube b k).toConvexSpaceBody) <=
      ENNReal.ofReal
        (((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M b : Real)) ^ eta J)
  window_lower : ∀ k, SourceTowerWindow delta M e a b k -> ∀ j ∈ Q.indexSet a,
    (1 / 2 : ENNReal) * ENNReal.ofReal
      (((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M k : Real)) ^ eta (J + 1)) <
      Kakeya.maxDensity (Q.fibre a k j) (fun l => (Q.tube k l).toConvexSpaceBody)

end Kakeya.ML2Core
