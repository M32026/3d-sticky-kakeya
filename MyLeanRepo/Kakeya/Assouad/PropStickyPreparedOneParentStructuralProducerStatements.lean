import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentStructuralAssemblyStatements

/-!
# Complete structural producer for one prepared caller parent

This package performs every non-global operation inside one complete caller
fiber: fixed-polylog source selection, quantitative retention, literal CWA,
literal image construction, and the critical-floor multiplicity estimate.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPreparedOneParentStructuralProducerData
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
    (parent : Fin prepared.callerStrict.coarse.card)
    (critical :
      WZ2PaperCriticalFloorSelectionData
        sigma floorLoss strongLoss) where
  selection :
    WZ2PaperPreparedOneParentSelectionData prepared parent
  quantitative :
    WZ2PaperPreparedOneParentQuantitativeData
      prepared parent selection
  restrictedConstant : ENNReal
  restrictedConstant_eq :
    restrictedConstant =
      max 1
        (max quantitative.selectedUniformConstant
          ((quantitative.weight⁻¹ *
              (prepared.structuralConstant *
                quantitative.cardinalityRetentionConstant *
                quantitative.selectedUniformConstant)) *
            prepared.structuralConstant))
  targetConstant : ENNReal
  targetConstant_eq :
    targetConstant =
      Kakeya.realRpowENN
        (delta / caller.1) (-critical.structuralLoss)
  literalCWA :
    WZ2PaperPreparedOneParentLiteralCWAData
      prepared parent selection quantitative
      restrictedConstant targetConstant
  image :
    WZ2PaperPreparedOneParentLiteralImageData
      prepared parent selection quantitative literalCWA
  structural :
    WZ2PaperLiteralLemma3_3StructuralData
      (rho := caller.1)
      (sigma := sigma)
      (strongLoss := strongLoss)
      (outputLoss := outputLoss)
      (wz2PaperPreparedOneParentShading prepared parent)
      (prepared.callerStrict.coarse.tube parent)
      prepared.callerStrict.rho_pos 4
  structural_refinement_eq :
    structural.refinement = selection.refinement
  structural_familyData_eq :
    HEq structural.familyData
      literalCWA.rootSetup.selectedLiteralFamily
  structural_selected_card_eq :
    structural.refinement.selected.family.card =
      selection.refinement.selected.family.card

def WZ2PropStickyPreparedOneParentStructuralProducerStatement : Prop :=
  ∀ {delta sourceLoss stableLoss sigma floorLoss strongLoss outputLoss : ℝ},
    ∀ {source : Kakeya.Streamlined.TubeFamily delta},
      ∀ {shading : WZ1PaperTubeShading source},
        ∀ {caller : Kakeya.Streamlined.AdmissibleScale delta},
          ∀ {preparationExponent : ℕ},
            ∀ (prepared :
                WZ2PaperCallerStrictPreparationData
                  (sourceLoss := sourceLoss)
                  (stableLoss := stableLoss)
                  shading caller preparationExponent),
              ∀ (parent : Fin prepared.callerStrict.coarse.card),
                ∀ (critical :
                    WZ2PaperCriticalFloorSelectionData
                      sigma floorLoss strongLoss),
                  delta ≤ 1 / 10000 →
                  delta / caller.1 ≤ 1 / 24 →
                  delta / caller.1 ≤ critical.delta₀ →
                  0 < floorLoss →
                  floorLoss < strongLoss →
                  0 < strongLoss →
                  3 * strongLoss ≤ outputLoss →
                  wz1PaperRefinementFraction delta 2 *
                        (packingConstant10000 : ENNReal) ≤
                      1 →
                  (let branchLoss : ENNReal :=
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
                      1) →
                  (∀ (selection :
                      WZ2PaperPreparedOneParentSelectionData
                        prepared parent),
                    ∀ (quantitative :
                        WZ2PaperPreparedOneParentQuantitativeData
                          prepared parent selection),
                      let restrictedConstant : ENNReal :=
                        max 1
                          (max quantitative.selectedUniformConstant
                            ((quantitative.weight⁻¹ *
                                (prepared.structuralConstant *
                                  quantitative.cardinalityRetentionConstant *
                                  quantitative.selectedUniformConstant)) *
                              prepared.structuralConstant))
                      let targetConstant : ENNReal :=
                        Kakeya.realRpowENN
                          (delta / caller.1)
                          (-critical.structuralLoss)
                      let rootConstant : ENNReal :=
                        max 1
                          ((quantitative.weight⁻¹ *
                              quantitative.cardinalityRetentionConstant) *
                            prepared.structuralConstant)
                      (1000000 : ENNReal) * rootConstant ≤
                          targetConstant ∧
                        (1000000 : ENNReal) * restrictedConstant ≤
                          targetConstant ∧
                        (200 : ENNReal) * prepared.structuralConstant ≤
                          targetConstant ∧
                        Kakeya.realRpowENN
                              (delta / caller.1)
                              critical.structuralLoss *
                            (55296 * Kakeya.deltaTubeVolume 1) ≤
                          ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
                            (wz1PaperRefinementFraction delta 4 *
                              ((1 / 2 : ENNReal) *
                                Kakeya.realRpowENN delta sourceLoss)) ∧
                        55296 * Kakeya.deltaTubeVolume 1 ≤
                          Kakeya.realRpowENN
                            (delta / caller.1) (-strongLoss) ∧
                        2 * (55296 * Kakeya.deltaTubeVolume 1) ≤
                          Kakeya.realRpowENN
                            (delta / caller.1)
                            (-(strongLoss - floorLoss))) →
                    Nonempty
                      (WZ2PaperPreparedOneParentStructuralProducerData
                        (outputLoss := outputLoss)
                        prepared parent critical)

end Kakeya.Assouad

end
