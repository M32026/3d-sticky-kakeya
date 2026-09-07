import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentQuantitativeStatements

/-!
# Uniform envelope for prepared one-parent constants

All constants below depend only on the fixed loss parameters and the finite
tree depth selected before `delta`.  They do not depend on the caller parent.
-/

noncomputable section

namespace Kakeya.Assouad

def wz2PaperPreparedOneParentEnvelope (sourceLoss : ℝ) : ENNReal :=
  let finiteLoss := wz2PaperPreparedOneParentFiniteLoss sourceLoss
  let geometry := 55296 * Kakeya.deltaTubeVolume 1
  (81000000 : ENNReal) *
    max 1
      (max
        (4 * finiteLoss * geometry)
        (8 * (finiteLoss * geometry) ^ 2))

def WZ2PropStickyPreparedOneParentQuantitativeEnvelopeStatement : Prop :=
  ∀ {delta sourceLoss stableLoss : ℝ},
    0 < delta →
    delta ≤ 1 →
    0 < stableLoss →
    sourceLoss < stableLoss →
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
                ∀ (selection :
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
                    let rootConstant : ENNReal :=
                      max 1
                        ((quantitative.weight⁻¹ *
                            quantitative.cardinalityRetentionConstant) *
                          prepared.structuralConstant)
                    let bound : ENNReal :=
                      wz2PaperPreparedOneParentEnvelope sourceLoss *
                        Kakeya.realRpowENN delta (-5 * stableLoss)
                    (1000000 : ENNReal) * rootConstant ≤ bound ∧
                      (1000000 : ENNReal) * restrictedConstant ≤ bound ∧
                      (81000000 : ENNReal) * restrictedConstant ≤ bound ∧
                      (200 : ENNReal) * prepared.structuralConstant ≤ bound

end Kakeya.Assouad

end
