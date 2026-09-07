import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentRestrictedScheduleStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralFixedRootSetupStatements

/-!
# Literal nearby-scale CWA for one prepared selected caller fiber

The selected family is fixed once.  Its historical rescaled image supplies
the top-level normalized Convex--Wolff bound; the restricted caller-tail
schedule supplies all low scales; and the actual unit root supplies the high
scale branch.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPreparedOneParentLiteralCWAData
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
    (parent : Fin prepared.callerStrict.coarse.card)
    (selection :
      WZ2PaperPreparedOneParentSelectionData prepared parent)
    (quantitative :
      WZ2PaperPreparedOneParentQuantitativeData
        prepared parent selection)
    (restrictedConstant targetConstant : ENNReal) where
  historical :
    WZ2PaperUnitRescaledFamilyData
      prepared.callerStrict.cover parent
      prepared.callerStrict.rho_pos
      prepared.structuralConstant
  rootConstant : ENNReal
  rootConstant_eq :
    rootConstant =
      max 1
        ((quantitative.weight⁻¹ *
            quantitative.cardinalityRetentionConstant) *
          prepared.structuralConstant)
  rootSetup :
    WZ2PaperLiteralFixedRootSetupData
      (selectedConstant := rootConstant)
      historical selection.refinement.selected
      ⟨(div_le_one prepared.callerStrict.rho_pos).mpr caller.2.1,
        le_rfl⟩
  restricted :
    WZ2PaperPreparedOneParentRestrictedScheduleData
      prepared parent selection restrictedConstant
  target_cwa_nearby :
    WZ2PaperCWAAtNearbyScales
      rootSetup.selectedLiteralFamily.targetFamily targetConstant

def WZ2PropStickyPreparedOneParentLiteralCWAStatement : Prop :=
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
                ∀ (selection :
                    WZ2PaperPreparedOneParentSelectionData
                      prepared parent),
                  ∀ (quantitative :
                      WZ2PaperPreparedOneParentQuantitativeData
                        prepared parent selection),
                    ∀ (restrictedConstant targetConstant : ENNReal),
                      1 ≤ restrictedConstant →
                      max quantitative.selectedUniformConstant
                          ((quantitative.weight⁻¹ *
                              (prepared.structuralConstant *
                                quantitative.cardinalityRetentionConstant *
                                quantitative.selectedUniformConstant)) *
                            prepared.structuralConstant) ≤
                        restrictedConstant →
                      (1000000 : ENNReal) *
                          max 1
                            ((quantitative.weight⁻¹ *
                                quantitative.cardinalityRetentionConstant) *
                              prepared.structuralConstant) ≤
                        targetConstant →
                      (1000000 : ENNReal) * restrictedConstant ≤
                        targetConstant →
                      (200 : ENNReal) * prepared.structuralConstant ≤
                        targetConstant →
                      Nonempty
                        (WZ2PaperPreparedOneParentLiteralCWAData
                          prepared parent selection quantitative
                          restrictedConstant targetConstant)

end Kakeya.Assouad

end
