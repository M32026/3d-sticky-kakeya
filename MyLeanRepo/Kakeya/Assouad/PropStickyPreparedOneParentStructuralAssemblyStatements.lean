import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentLiteralImageStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralOneParentStructuralStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCriticalFloorSelectionStatements

/-!
# Structural one-parent assembly from prepared selected data

This is the paper-faithful end of the one-parent step before global
balanced-cover comparison.  The only volume premise is the critical lower
bound used to control the dyadic point-multiplicity level.  No small
union-volume upper bound is assumed or concluded.
-/

noncomputable section

namespace Kakeya.Assouad

def WZ2PropStickyPreparedOneParentStructuralAssemblyStatement : Prop :=
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
              ∀ parent : Fin prepared.callerStrict.coarse.card,
                ∀ (selection :
                    WZ2PaperPreparedOneParentSelectionData
                      prepared parent),
                  ∀ (quantitative :
                      WZ2PaperPreparedOneParentQuantitativeData
                        prepared parent selection),
                    ∀ {restrictedConstant targetConstant : ENNReal},
                      ∀ (literalCWA :
                          WZ2PaperPreparedOneParentLiteralCWAData
                            prepared parent selection quantitative
                            restrictedConstant targetConstant),
                        ∀ (image :
                            WZ2PaperPreparedOneParentLiteralImageData
                              prepared parent selection quantitative
                              literalCWA),
                        ∀ (critical :
                            WZ2PaperCriticalFloorSelectionData
                              sigma floorLoss strongLoss),
                        delta / caller.1 ≤ 1 / 24 →
                        delta / caller.1 ≤ critical.delta₀ →
                        0 < floorLoss →
                        floorLoss < strongLoss →
                        0 < strongLoss →
                        3 * strongLoss ≤ outputLoss →
                          Kakeya.realRpowENN
                                (delta / caller.1)
                                critical.structuralLoss *
                              (55296 * Kakeya.deltaTubeVolume 1) ≤
                            ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
                              (wz1PaperRefinementFraction delta 4 *
                                ((1 / 2 : ENNReal) *
                                  Kakeya.realRpowENN delta sourceLoss)) →
                          targetConstant ≤
                            Kakeya.realRpowENN
                              (delta / caller.1)
                              (-critical.structuralLoss) →
                          (100 : ENNReal) * literalCWA.rootConstant ≤
                            Kakeya.realRpowENN
                              (delta / caller.1)
                              (-critical.structuralLoss) →
                          55296 * Kakeya.deltaTubeVolume 1 ≤
                            Kakeya.realRpowENN
                              (delta / caller.1) (-strongLoss) →
                          2 * (55296 * Kakeya.deltaTubeVolume 1) ≤
                            Kakeya.realRpowENN
                              (delta / caller.1)
                              (-(strongLoss - floorLoss)) →
                          Nonempty
                            { data :
                                WZ2PaperLiteralLemma3_3StructuralData
                                  (rho := caller.1)
                                  (sigma := sigma)
                                  (strongLoss := strongLoss)
                                  (outputLoss := outputLoss)
                                  (wz2PaperPreparedOneParentShading
                                    prepared parent)
                                  (prepared.callerStrict.coarse.tube parent)
                                  prepared.callerStrict.rho_pos 4 //
                              data.refinement = selection.refinement ∧
                                HEq data.familyData
                                  literalCWA.rootSetup.selectedLiteralFamily }

end Kakeya.Assouad

end
