/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectWindowConstruction

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

open ML2Assembly

universe u

/-- The good exit is the same mass-form analytic estimate used by Dichotomy. -/
def SourceDirectGoodMass {iota : Type u} {delta : NNReal} (S : Finset iota)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (beta gain : Real) : Prop :=
  (∑ i ∈ S, volume (Z i).shade) <= (delta : ENNReal) ^ gain *
    (S.card : ENNReal) ^ beta * volume (⋃ i ∈ S, (Z i).shade)

section Paid

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
  {Y : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}

/-- The literal paid D step. The original fixed Q supplies the potential;
actual subsets and shade/mass payments are retained, without a false
inference from integer descent to a two-h coordinate descent. -/
structure SourceDirectPaidStep (Q : SourceThreadedTower S T M C)
    (h : Real) (loss : ENNReal) (x y : SourcePaidState S T Y) : Prop where
  subset : y.family <= x.family
  shade_subset : forall i, i ∈ y.family -> (y.shaded i).shade <= (x.shaded i).shade
  weighted_mass : x.mass <= loss * y.mass
  potential_drop : Q.assignedPotential h y.family + 1 <= Q.assignedPotential h x.family

/-- A trial may run on any actual retained state of this fixed tower once
its fullness permits it. The real preparation and dividing-scales choices
are constructed in the supplier theorem, not part of this input state. -/
def SourceDirectPaidTrialLaw
    (Y : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (Q : SourceThreadedTower S T M C)
    (h eta0 alpha gamma beta : Real) (loss : ENNReal) : Prop :=
  forall x : SourcePaidState S T Y, (delta : ENNReal) ^ (2 * eta0) <= x.fullness ->
    SourcePaidTerminal loss alpha gamma beta x \/
      exists y : SourcePaidState S T Y, SourceDirectPaidStep Q h loss x y

/-- Both the existing coordinate-certified step and the direct D endpoint
feed the same integer descent relation; the converse is not asserted. -/
theorem source_direct_paidStep_of_coordinate_step
    (Q : SourceThreadedTower S T M C) {h : Real} {loss : ENNReal}
    (hh : 0 < h) (hd0 : 0 < delta) (hd1 : delta < 1)
    {x y : SourcePaidState S T Y} (H : SourcePaidStep Q h loss x y) :
    SourceDirectPaidStep Q h loss x y := by
  exact ⟨H.subset, H.shade_subset, H.weighted_mass,
    source_paidStep_potential_drop Q hh hd0 hd1 H⟩

end Paid

end Kakeya.ML2Core
