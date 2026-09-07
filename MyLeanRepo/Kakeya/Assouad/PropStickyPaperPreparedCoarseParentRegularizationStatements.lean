import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedParentwiseStructuralProducerStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMergedParentMassLower
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperExternalWeightRegularizationStatements

/-!
# Coarse-parent regularization before global whole-cell balancing

The paper first completes the one-parent refinements, then pigeonholes the
caller-scale parents while retaining complete parent fibers.  The external
weight of one caller parent is the mass of its merged structural full fiber.
Regularizing these weights on the canonical caller coarse family preserves
the caller's nearby-scale Convex-Wolff structure without appealing to
inheritance by an arbitrary coarse subfamily.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPreparedCoarseParentRegularizationData
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
    (ambientConstant outputConstant normalizationWeight weightUpper :
      ENNReal)
    (levelCount : ℕ) where
  regularized :
    WZ2PaperExternalWeightRegularizationData
      (family := prepared.callerStrict.coarse)
      ambientConstant outputConstant normalizationWeight weightUpper
      levelCount
      (wz2PaperPreparedMergedParentMass structural)
  selectedParentMass :
    Fin regularized.selected.family.card → ENNReal
  selectedParentMass_eq :
    ∀ parent,
      selectedParentMass parent =
        wz2PaperPreparedMergedParentMass structural
          (regularized.selected.embedding parent)
  total_weight_eq :
    (∑ parent : Fin prepared.callerStrict.coarse.card,
        wz2PaperPreparedMergedParentMass structural parent) =
      structural.merged.merged.refinement.refined.mass
  selected_weight_eq :
    regularized.selectedWeight =
      ∑ parent : Fin regularized.selected.family.card,
        selectedParentMass parent
  selectedParentMassLevel : ENNReal
  selectedParentMassLevel_pos :
    0 < selectedParentMassLevel
  selectedParentMassLevel_ne_top :
    selectedParentMassLevel ≠ ⊤
  selected_parent_mass_band :
    ∀ parent,
      selectedParentMassLevel ≤ selectedParentMass parent ∧
        selectedParentMass parent ≤ 2 * selectedParentMassLevel
  selected_parent_mass_pos :
    ∀ parent, 0 < selectedParentMass parent
  selected_parent_mass_upper :
    ∀ parent, selectedParentMass parent ≤ weightUpper

end Kakeya.Assouad

end
