/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceCurrentParentActual
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceRetainedParentOutcomeData

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- Nonemptiness is explicit: restriction alone also permits the empty family.
Every actual current retained state supplies precisely this hypothesis. -/
theorem source_current_retained_fixed_input (Q : SourceThreadedTower S T M C)
    {R : Finset iota} (Q' : SourceThreadedTower R T M C)
    {A0 A1 : Nat} {etaIn etaOut : Real}
    (hdelta : 0 < delta) (hdelta1 : delta <= 1) (haccuracy : etaIn <= etaOut)
    (H : SourceTowerRestriction Q Q') (hR : R.Nonempty)
    (hinput : SourceFixedTowerInput Q A0 A1 etaIn) :
    SourceFixedTowerInput Q' A0 A1 etaOut := by
  classical
  have hocc (k : Nat) (hk : k <= M) : Q'.indexSet k <= Q.indexSet k := by
    rw [H.occupied k hk]
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Q.place_mem k hk i (H.subset hi)
  refine {
    geometry := {
      nonempty := hR
      original_centred := fun i hi => hinput.geometry.original_centred i (H.subset hi)
      original_ball := fun i hi => hinput.geometry.original_ball i (H.subset hi)
      original_ed := hinput.geometry.original_ed.subset H.subset
      coarse_centred := ?_
      coarse_ball := ?_
      coarse_ed := ?_
      coarse_card := ?_
      segment_sharing := ?_ }
    neighbour_sharing := ?_
    maximal_density := ?_ }
  · simpa only [H.tubes] using
      (fun k hk j hj => hinput.geometry.coarse_centred k hk j (hocc k hk.le hj))
  · simpa only [H.tubes] using
      (fun k hk j hj => hinput.geometry.coarse_ball k hk j (hocc k hk.le hj))
  · intro k hk
    simpa only [H.tubes] using (hinput.geometry.coarse_ed k hk).subset (hocc k hk.le)
  · intro k hk
    exact (show ((Q'.indexSet k).card : Real) <= ((Q.indexSet k).card : Real) from
      Nat.cast_le.mpr (Finset.card_le_card (hocc k hk.le))).trans
        (hinput.geometry.coarse_card k hk)
  · intro k hk x y hxy
    rw [H.tubes]
    exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk.le))).trans
      (hinput.geometry.segment_sharing k hk x y hxy)
  · intro k hk j hj
    rw [H.tubes]
    exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk.le))).trans
      (hinput.neighbour_sharing k hk j (hocc k hk.le hj))
  · refine (Kakeya.maxDensity_mono (fun i => (T i).toConvexSpaceBody) H.subset).trans
      (hinput.maximal_density.trans (ENNReal.ofReal_le_ofReal ?_))
    exact Real.rpow_le_rpow_of_exponent_ge hdelta (show (delta : Real) <= 1 by exact_mod_cast hdelta1)
      (neg_le_neg haccuracy)

/-- Current F/P data project to the common terminal geometry with the exact
original-Q payment. This does not manufacture a legacy history witness. -/
theorem source_current_parent_terminal_geometry
    (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    {R : Finset iota} (Q' : SourceThreadedTower R T M C)
    {N J A0 A1 : Nat} {e : Real} {eta : Nat -> Real}
    {etaParent bias etaF : Real} {K : Nat} {cap : NNReal} {a b : Nat}
    (H : SourceCurrentParentOutcome Q Z R Q' N J A0 A1 e eta
      etaParent bias etaF K cap a b) :
    SourceParentTerminalGeometry Q Z R Q' N J A0 A1 e eta
      etaParent bias etaF K cap a b := by
  refine ⟨H.retained, H.input, H.upper, ?_⟩
  rcases H.alternative with hdrop | ⟨B, hhistory, hconc, hecc | ⟨P, hp⟩⟩
  · exact Or.inl hdrop
  · exact Or.inr ⟨B, hconc, Or.inl hecc⟩
  · exact Or.inr ⟨B, hconc, Or.inr ⟨P⟩⟩

/-- A supplied legacy result has the same common geometry; its stronger
historical contract is not a prerequisite of this terminal interface. -/
theorem source_legacy_parent_terminal_geometry
    (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    {R : Finset iota} (Q' : SourceThreadedTower R T M C)
    {N J A0 A1 : Nat} {e : Real} {eta : Nat -> Real}
    {etaParent bias etaF : Real} {K : Nat} {cap : NNReal} {a b : Nat}
    (H : SourceRetainedParentOutcome Q Z R Q' N J A0 A1 e eta
      etaParent bias etaF K cap a b) :
    SourceParentTerminalGeometry Q Z R Q' N J A0 A1 e eta
      etaParent bias etaF K cap a b := by
  refine ⟨H.retained, H.input, H.upper, ?_⟩
  rcases H.alternative with hdrop | ⟨B, hhistory, hconc, hecc | ⟨P, hp⟩⟩
  · exact Or.inl hdrop
  · exact Or.inr ⟨B, hconc, Or.inl hecc⟩
  · exact Or.inr ⟨B, hconc, Or.inr ⟨P⟩⟩

end Kakeya.ML2Core
