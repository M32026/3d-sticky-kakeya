import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPreparedCoarseRegularizedMainlineStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMergedParentMassUniform

/-!
# Reference-parent coarse regularization after structural Lemma 3.3

The paper pigeonholes the complete caller parents by shaded mass.  The active
quantitative normalization uses one fixed caller parent and the closed
two-sided parent-mass comparison, rather than the much coarser total-mass
upper bound.

The lower normalization and upper weight are therefore separated only by the
fixed/polylogarithmic parent-mass comparison constant.  This is the
paper-faithful route that can be absorbed into the requested caller-scale
Convex-Wolff loss.
-/

noncomputable section

namespace Kakeya.Assouad

noncomputable def wz2PaperPreparedReferenceParent
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {totalExponent globalBalancingExponent : ℕ}
    {parameters :
      WZ2PaperFinalParameterSelectionData
        sigma outputLoss totalExponent globalBalancingExponent}
    {preparationSourceLoss : ℝ}
    (mainline :
      WZ2PaperPreparedStructuralMainlineData
        shading caller totalExponent globalBalancingExponent
        parameters preparationSourceLoss) :
    Fin mainline.prepared.callerStrict.coarse.card :=
  mainline.prepared.callerStrict.cover.parent
    ⟨0, mainline.prepared.selected_card_pos⟩

def wz2PaperPreparedReferenceParentMass
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {totalExponent globalBalancingExponent : ℕ}
    {parameters :
      WZ2PaperFinalParameterSelectionData
        sigma outputLoss totalExponent globalBalancingExponent}
    {preparationSourceLoss : ℝ}
    (mainline :
      WZ2PaperPreparedStructuralMainlineData
        shading caller totalExponent globalBalancingExponent
        parameters preparationSourceLoss) : ENNReal :=
  wz2PaperPreparedMergedParentMass mainline.structural
    (wz2PaperPreparedReferenceParent mainline)

def wz2PaperPreparedReferenceNormalizationWeight
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {totalExponent globalBalancingExponent : ℕ}
    {parameters :
      WZ2PaperFinalParameterSelectionData
        sigma outputLoss totalExponent globalBalancingExponent}
    {preparationSourceLoss : ℝ}
    (mainline :
      WZ2PaperPreparedStructuralMainlineData
        shading caller totalExponent globalBalancingExponent
        parameters preparationSourceLoss) : ENNReal :=
  wz2PaperPreparedMergedParentMassWeight
      delta preparationSourceLoss *
    wz2PaperPreparedReferenceParentMass mainline /
      wz2PaperPreparedMergedParentMassConstant mainline.prepared

def wz2PaperPreparedReferenceWeightUpper
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {totalExponent globalBalancingExponent : ℕ}
    {parameters :
      WZ2PaperFinalParameterSelectionData
        sigma outputLoss totalExponent globalBalancingExponent}
    {preparationSourceLoss : ℝ}
    (mainline :
      WZ2PaperPreparedStructuralMainlineData
        shading caller totalExponent globalBalancingExponent
        parameters preparationSourceLoss) : ENNReal :=
  wz2PaperPreparedMergedParentMassConstant mainline.prepared *
    wz2PaperPreparedReferenceParentMass mainline /
      wz2PaperPreparedMergedParentMassWeight
        delta preparationSourceLoss

structure WZ2PaperPreparedReferenceCoarseCertificate
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {totalExponent globalBalancingExponent : ℕ}
    {parameters :
      WZ2PaperFinalParameterSelectionData
        sigma outputLoss totalExponent globalBalancingExponent}
    {preparationSourceLoss : ℝ}
    (mainline :
      WZ2PaperPreparedStructuralMainlineData
        shading caller totalExponent globalBalancingExponent
        parameters preparationSourceLoss) where
  levelCount : ℕ
  parentExponent : ℕ
  schedule_power :
    ENNReal.ofReal (1 / caller.1) ≤
      mainline.prepared.closureConstant ^ levelCount
  output_absorption :
    mainline.prepared.closureConstant *
        mainline.prepared.closureConstant ≤
      wz2PaperPreparedCoarseOutputConstant mainline
  regularization_absorption :
    let degreeConstant :=
      16 * ((levelCount + 1 : ℕ) : ENNReal) *
        (Nat.log 2
            (2 * mainline.prepared.callerStrict.coarse.card) + 1 :
          ENNReal) ^ (levelCount + 1)
    let regularizationLoss :=
      (8 : ENNReal) *
        (Nat.log 2
            (2 * mainline.prepared.callerStrict.coarse.card) + 1 :
          ENNReal) ^ (levelCount + 2)
    max degreeConstant
        (((wz2PaperPreparedReferenceNormalizationWeight mainline)⁻¹ *
            (mainline.prepared.closureConstant *
              (regularizationLoss *
                wz2PaperPreparedReferenceWeightUpper mainline) *
              degreeConstant)) *
          mainline.prepared.closureConstant) ≤
      wz2PaperPreparedCoarseOutputConstant mainline
  pullback_absorption :
    let regularizationLoss :=
      (8 : ENNReal) *
        (Nat.log 2
            (2 * mainline.prepared.callerStrict.coarse.card) + 1 :
          ENNReal) ^ (levelCount + 2)
    wz1PaperRefinementFraction delta parentExponent *
        regularizationLoss ≤
      1

structure WZ2PaperPreparedReferenceCoarseMainlineData
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {totalExponent globalBalancingExponent : ℕ}
    {parameters :
      WZ2PaperFinalParameterSelectionData
        sigma outputLoss totalExponent globalBalancingExponent}
    {preparationSourceLoss : ℝ}
    (mainline :
      WZ2PaperPreparedStructuralMainlineData
        shading caller totalExponent globalBalancingExponent
        parameters preparationSourceLoss)
    (certificate :
      WZ2PaperPreparedReferenceCoarseCertificate mainline) where
  regularization :
    WZ2PaperPreparedCoarseParentRegularizationData
      mainline.prepared parameters.critical mainline.structural
      mainline.prepared.closureConstant
      (wz2PaperPreparedCoarseOutputConstant mainline)
      (wz2PaperPreparedReferenceNormalizationWeight mainline)
      (wz2PaperPreparedReferenceWeightUpper mainline)
      certificate.levelCount
  pullback :
    WZ2PaperPreparedCoarseParentPullbackData
      regularization certificate.parentExponent

end Kakeya.Assouad

end
