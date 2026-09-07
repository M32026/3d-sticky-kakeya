import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentLocalBranchStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementCompositionStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralSeparationConstants

/-!
# Fixed-polylog one-parent source selection

Inside one complete caller parent fiber:

1. apply one paper tube-packing refinement, retaining each selected tube's
   complete current shading;
2. prune whole branches of the nested strict tree;
3. select one final dyadic point-multiplicity band.

The packing loss is absorbed by exponent `2`.  The branch loss and final
dyadic band are absorbed together by exponent `2`, so the composed paper
refinement has the absolute exponent `4`, independent of the requested loss.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPreparedOneParentSelectionData
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (parent : Fin prepared.callerStrict.coarse.card) where
  packing :
    WZ1PaperRefinement
      (wz2PaperPreparedOneParentShading prepared parent) 2
  packing_separated :
    ∀ first second, first ≠ second →
      10000 * delta <
        wz1PaperLineDistance
          (packing.selected.family.tube first)
          (packing.selected.family.tube second)
  packing_literal_separated :
    ∀ first second, first ≠ second →
      wz2PaperLiteralSourceSeparationFactor * delta <
        wz1PaperLineDistance
          (packing.selected.family.tube first)
          (packing.selected.family.tube second)
  packing_refined_eq :
    packing.refined =
      restrictPaperShading packing.selected
        (wz2PaperPreparedOneParentShading prepared parent)
  packing_mass_retention :
    (wz2PaperPreparedOneParentShading prepared parent).mass ≤
      (packingConstant10000 : ENNReal) *
        packing.refined.mass
  branch :
    WZ2PaperPreparedOneParentLocalBranchData
      prepared parent packing.selected packing.refined
  branch_mass_retention :
    packing.refined.mass ≤
      (2 : ENNReal) ^
          (wz2PaperPreparedOneParentFineScaleCount prepared parent) *
        branch.refined.mass
  inner :
    WZ1PaperRefinement packing.refined 2
  inner_selected_eq :
    inner.selected = branch.selected
  finalLevel : ℕ
  final_cubical :
    WZ1PaperIsCubicalShading inner.refined
  final_multiplicity_band :
    ∀ point ∈ inner.refined.union,
      (2 ^ finalLevel : ENNReal) ≤
          (inner.refined.pointMultiplicity point : ENNReal) ∧
        (inner.refined.pointMultiplicity point : ENNReal) <
          (2 ^ (finalLevel + 1) : ENNReal)
  composition :
    WZ2PaperRefinementCompositionData
      (wz2PaperPreparedOneParentShading prepared parent)
      2 2 packing inner
  refinement :
    WZ1PaperRefinement
      (wz2PaperPreparedOneParentShading prepared parent) 4
  refinement_eq :
    refinement = composition.toRefinement
  selected_eq :
    refinement.selected =
      packing.selected.comp branch.selected
  refined_cubical :
    WZ1PaperIsCubicalShading refinement.refined
  selected_strongly_separated :
    ∀ first second, first ≠ second →
      10000 * delta <
        wz1PaperLineDistance
          (refinement.selected.family.tube first)
          (refinement.selected.family.tube second)
  selected_literal_separated :
    ∀ first second, first ≠ second →
      wz2PaperLiteralSourceSeparationFactor * delta <
        wz1PaperLineDistance
          (refinement.selected.family.tube first)
          (refinement.selected.family.tube second)
  refined_multiplicity_band :
    ∀ point ∈ refinement.refined.union,
      (2 ^ finalLevel : ENNReal) ≤
          (refinement.refined.pointMultiplicity point : ENNReal) ∧
        (refinement.refined.pointMultiplicity point : ENNReal) <
          (2 ^ (finalLevel + 1) : ENNReal)

def WZ2PropStickyPreparedOneParentSelectionStatement : Prop :=
  ∀ {delta sourceLoss stableLoss : ℝ},
    ∀ {source : Kakeya.Streamlined.TubeFamily delta},
      ∀ {shading : WZ1PaperTubeShading source},
        ∀ {caller : Kakeya.Streamlined.AdmissibleScale delta},
          ∀ {preparationExponent : ℕ},
            ∀ (prepared :
                WZ2PaperCallerStrictPreparationData
                  (sourceLoss := sourceLoss)
                  (stableLoss := stableLoss)
                  shading caller preparationExponent),
              ∀ parent : Fin prepared.callerStrict.coarse.card,
                delta ≤ 1 / 10000 →
                wz1PaperRefinementFraction delta 2 *
                      (packingConstant10000 : ENNReal) ≤
                    1 →
                let branchLoss : ENNReal :=
                  (2 : ENNReal) ^
                    (wz2PaperPreparedOneParentFineScaleCount
                      prepared parent)
                let bandLoss : ENNReal :=
                  (Nat.log 2
                      (wz2PaperPreparedOneParentFiber
                        prepared parent).family.card +
                    1 : ENNReal)
                wz1PaperRefinementFraction delta 2 *
                      (branchLoss * bandLoss) ≤
                    1 →
                  Nonempty
                    (WZ2PaperPreparedOneParentSelectionData
                      prepared parent)

end Kakeya.Assouad

end
