import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentQuantitativeStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyCallerFiberScaleStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyStatements
import MyLeanRepo.Kakeya.Assouad.PropStickySelectedScaleCover

/-!
# Restricted strict schedule for one selected caller fiber

The one-parent selection retains a fixed subfamily of one complete caller
fiber.  At every strict tree coordinate, restrict the caller-fiber exact
scale witness to the selected family using:

* the selected/source cardinality retention;
* the selected occupied-fiber uniformity;
* the ambient complete-fiber CWA.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPreparedOneParentRestrictedScheduleData
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
    (outputConstant : ENNReal) where
  callerFiberData :
    ∀ coordinate :
        Fin (wz2PaperPreparedOneParentFineScaleCount
          prepared parent),
        WZ2PaperCallerFiberScaleData
        prepared parent
          (wz2PaperPreparedOneParentFineCoordinate
            prepared parent coordinate)
  scaleData :
    ∀ coordinate :
        Fin (wz2PaperPreparedOneParentFineScaleCount
          prepared parent),
      WZ2PaperScaleCoverData
        selection.refinement.selected.family
        (prepared.strictScale
          (wz2PaperPreparedOneParentFineCoordinate
            prepared parent coordinate))
        outputConstant
  coarse_eq :
    ∀ coordinate,
      (scaleData coordinate).coarse =
        (((callerFiberData coordinate).scaleData.cover
          |>.hitParentSubfamily
            selection.refinement.selected)).family
  cover_eq :
    ∀ coordinate,
      HEq (scaleData coordinate).cover
        ((callerFiberData coordinate).scaleData.cover
          |>.restrictToHitParents selection.refinement.selected)
  coarse_strongly_separated :
    ∀ coordinate,
      ∀ first second : Fin (scaleData coordinate).coarse.card,
        first ≠ second →
          wz2PaperLiteralSourceSeparationFactor *
              (prepared.strictScale
                (wz2PaperPreparedOneParentFineCoordinate
                  prepared parent coordinate)).1 <
            wz1PaperLineDistance
              ((scaleData coordinate).coarse.tube first)
              ((scaleData coordinate).coarse.tube second)

def WZ2PropStickyPreparedOneParentRestrictedScheduleStatement : Prop :=
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
                    ∀ outputConstant : ENNReal,
                    max quantitative.selectedUniformConstant
                        ((quantitative.weight⁻¹ *
                            (prepared.structuralConstant *
                              quantitative.cardinalityRetentionConstant *
                              quantitative.selectedUniformConstant)) *
                          prepared.structuralConstant) ≤
                      outputConstant →
                    Nonempty
                      (WZ2PaperPreparedOneParentRestrictedScheduleData
                        prepared parent selection outputConstant)

end Kakeya.Assouad

end
