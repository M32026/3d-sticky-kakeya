import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentStructuralProducerStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentSelectionAbsorptionStatements

/-!
# Uniform numerical absorption for every prepared caller parent

All thresholds are selected after the critical structural loss is known but
before `delta`, the source family, the caller scale, or a caller parent.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPreparedOneParentUniformAbsorptionData
    (sourceLoss stableLoss floorLoss strongLoss outputLoss : ℝ)
    {sigma : ℝ}
    (critical :
      WZ2PaperCriticalFloorSelectionData sigma floorLoss strongLoss) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorb :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ∀ {source : Kakeya.Streamlined.TubeFamily delta},
        ∀ {shading : WZ1PaperTubeShading source},
          ∀ {caller : Kakeya.Streamlined.AdmissibleScale delta},
            Real.rpow delta (1 - outputLoss) ≤ caller.1 →
            caller.1 ≤ Real.rpow delta outputLoss →
            ∀ {preparationExponent : ℕ},
              ∀ (prepared :
                  WZ2PaperCallerStrictPreparationData
                    (sourceLoss := sourceLoss)
                    (stableLoss := stableLoss)
                    shading caller preparationExponent),
                ∀ parent : Fin prepared.callerStrict.coarse.card,
                  delta ≤ 1 / 10000 ∧
                    delta / caller.1 ≤ 1 / 24 ∧
                    delta / caller.1 ≤ critical.delta₀ ∧
                    wz1PaperRefinementFraction delta 2 *
                          (packingConstant10000 : ENNReal) ≤
                        1 ∧
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
                        1) ∧
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
                          (81000000 : ENNReal) * restrictedConstant ≤
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
                              (-(strongLoss - floorLoss)))

def WZ2PropStickyPreparedOneParentUniformAbsorptionStatement : Prop :=
  ∀ {sigma floorLoss strongLoss outputLoss : ℝ},
    ∀ (critical :
        WZ2PaperCriticalFloorSelectionData sigma floorLoss strongLoss),
      0 < floorLoss →
      floorLoss < strongLoss →
      3 * strongLoss ≤ outputLoss →
      ∀ sourceLoss stableLoss : ℝ,
        0 < sourceLoss →
        sourceLoss < stableLoss →
        5 * stableLoss < critical.structuralLoss ^ 2 →
          Nonempty
            (WZ2PaperPreparedOneParentUniformAbsorptionData
              sourceLoss stableLoss floorLoss strongLoss outputLoss
              critical)

end Kakeya.Assouad

end
