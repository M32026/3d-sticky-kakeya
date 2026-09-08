/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceFixedTowerData

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

/-- Source constants fixed before every runtime family and bottom scale. -/
def sourceBottomED : Nat := 2 * 223 ^ 6

def sourceLevelED : Nat := 2 * 641 ^ 6

def sourceThreadConstant : Nat := 2 * 897 ^ 6

section FixedTower

variable {iota : Type u} {delta : NNReal} {ambient : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- The extra pairwise segment-sharing row explicitly stated by the one-trial caller.
It is distinguished from bounding the tubes containing one preselected segment. -/
def SourceTowerNeighbourSharing (Q : SourceThreadedTower ambient T M C) : Prop :=
  ∀ k, k < M -> ∀ j ∈ Q.indexSet k,
    (open scoped Classical in
      ((Q.indexSet k).filter (fun j' => ∃ x y : EuclideanSpace Real (Fin 3), dist x y = 1 /\
        segment Real x y <= (Q.tube k j).carrier /\
        segment Real x y <= (Q.tube k j').carrier)).card) <= C

end FixedTower

end Kakeya.ML2Core
