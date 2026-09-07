import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedParentwiseStructuralProducerStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperStructuralMergedFiberReindex

/-!
# Parentwise mass lower bound after the structural merge

The prepared caller gives every complete caller fiber mass at least
`delta^stableLoss * rho^2`.  The one-parent structural refinement retains one
fixed fourth power of the paper logarithmic fraction.  Reindexing the merged
full fiber therefore gives the same lower bound on every merged parent.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

def wz2PaperPreparedMergedParentMass
    {delta sourceLoss stableLoss sigma floorLoss strongLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    {critical :
      WZ2PaperCriticalFloorSelectionData
        sigma floorLoss strongLoss}
    (structural :
      WZ2PaperPreparedParentwiseStructuralProducerData
        (outputLoss := outputLoss) prepared critical)
    (parent : Fin prepared.callerStrict.coarse.card) : ENNReal :=
  (restrictPaperShading
    (structural.merged.restrictedCover.fullFiberSubfamily parent)
    structural.merged.merged.refinement.refined).mass

theorem wz2_paper_prepared_merged_parent_mass_eq_local
    {delta sourceLoss stableLoss sigma floorLoss strongLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (critical :
      WZ2PaperCriticalFloorSelectionData
        sigma floorLoss strongLoss)
    (structural :
      WZ2PaperPreparedParentwiseStructuralProducerData
        (outputLoss := outputLoss) prepared critical)
    (parent : Fin prepared.callerStrict.coarse.card) :
    wz2PaperPreparedMergedParentMass structural parent =
      (structural.fiberProducer parent).structural.refinement.refined.mass := by
  let localData :=
    (structural.fiberProducer parent).structural
  let reindex :
      WZ2PaperStructuralMergedFiberReindexData
        prepared.callerStrict.cover prepared.refinement.refined
        prepared.callerStrict.rho_pos 4
        (fun current =>
          (structural.fiberProducer current).structural)
        structural.merged parent :=
    Classical.choice <|
      wz2_paper_structural_merged_fiber_reindex
        prepared.callerStrict.cover prepared.refinement.refined
        prepared.callerStrict.rho_pos 4
        (fun current =>
          (structural.fiberProducer current).structural)
        structural.merged parent
  change
    (∑ index :
        Fin
          (structural.merged.restrictedCover.fullFiberSubfamily
            parent).family.card,
      volume
        ((restrictPaperShading
          (structural.merged.restrictedCover.fullFiberSubfamily parent)
          structural.merged.merged.refinement.refined).carrier index)) =
    ∑ index : Fin localData.refinement.selected.family.card,
      volume (localData.refinement.refined.carrier index)
  let equivalence :
      Fin
          (structural.merged.restrictedCover.fullFiberSubfamily
            parent).family.card ≃
        Fin localData.refinement.selected.family.card :=
    Equiv.ofBijective reindex.localIndex reindex.localIndex_bijective
  exact
    Fintype.sum_equiv equivalence
      (fun index =>
        volume
          ((restrictPaperShading
            (structural.merged.restrictedCover.fullFiberSubfamily parent)
            structural.merged.merged.refinement.refined).carrier index))
      (fun index =>
        volume (localData.refinement.refined.carrier index))
      (fun index => by
        simpa [equivalence, localData] using
          congrArg volume (reindex.carrier_eq index))

theorem sum_wz2PaperPreparedMergedParentMass
    {delta sourceLoss stableLoss sigma floorLoss strongLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    {critical :
      WZ2PaperCriticalFloorSelectionData
        sigma floorLoss strongLoss}
    (structural :
      WZ2PaperPreparedParentwiseStructuralProducerData
        (outputLoss := outputLoss) prepared critical) :
    (∑ parent : Fin prepared.callerStrict.coarse.card,
        wz2PaperPreparedMergedParentMass structural parent) =
      structural.merged.merged.refinement.refined.mass := by
  exact
    structural.merged.restrictedCover.sum_fullFiberShading_mass
      structural.merged.merged.refinement.refined

theorem wz2_paper_prepared_merged_parent_mass_lower
    {delta sourceLoss stableLoss sigma floorLoss strongLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (critical :
      WZ2PaperCriticalFloorSelectionData
        sigma floorLoss strongLoss)
    (structural :
      WZ2PaperPreparedParentwiseStructuralProducerData
        (outputLoss := outputLoss) prepared critical) :
    ∀ parent : Fin prepared.callerStrict.coarse.card,
      wz1PaperRefinementFraction delta 4 *
            (Kakeya.realRpowENN delta stableLoss *
              Kakeya.realRpowENN caller.1 2) ≤
        wz2PaperPreparedMergedParentMass structural parent := by
  intro parent
  let localData :=
    (structural.fiberProducer parent).structural
  have hLocal :
      wz1PaperRefinementFraction delta 4 *
            (Kakeya.realRpowENN delta stableLoss *
              Kakeya.realRpowENN caller.1 2) ≤
        localData.refinement.refined.mass := by
    calc
      wz1PaperRefinementFraction delta 4 *
            (Kakeya.realRpowENN delta stableLoss *
              Kakeya.realRpowENN caller.1 2) ≤
          wz1PaperRefinementFraction delta 4 *
            (wz2PaperPreparedOneParentShading
              prepared parent).mass := by
        exact mul_le_mul_left'
          (prepared.caller_parent_mass parent)
          (wz1PaperRefinementFraction delta 4)
      _ ≤ localData.refinement.refined.mass :=
        localData.refinement.retained_mass
  rw [wz2_paper_prepared_merged_parent_mass_eq_local
    prepared critical structural parent]
  exact hLocal

end Kakeya.Assouad

end
