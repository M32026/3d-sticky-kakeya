import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPreparedStructuralMainlineStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPreparedCoarseParentRegularizationStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPreparedCoarseParentPullbackStatements

/-!
# Canonical coarse-parent regularization inputs after structural Lemma 3.3

The paper next pigeonholes the caller-scale parents by the shaded mass of
their complete merged fibers.  The normalization is canonical: average merged
parent mass.  The weight upper bound is the total merged mass, so no separate
parent-weight hypothesis is exposed.

Only the genuinely quantitative small-scale absorptions remain as input.
This stage still packages no extremality or union-volume upper bound.
-/

noncomputable section

namespace Kakeya.Assouad

def wz2PaperPreparedMergedTotalMass
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
  mainline.structural.merged.merged.refinement.refined.mass

def wz2PaperPreparedCoarseNormalizationWeight
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
  wz2PaperPreparedMergedTotalMass mainline /
    mainline.prepared.callerStrict.coarse.enncard

def wz2PaperPreparedCoarseOutputConstant
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {totalExponent globalBalancingExponent : ℕ}
    {parameters :
      WZ2PaperFinalParameterSelectionData
        sigma outputLoss totalExponent globalBalancingExponent}
    {preparationSourceLoss : ℝ}
    (_mainline :
      WZ2PaperPreparedStructuralMainlineData
        shading caller totalExponent globalBalancingExponent
        parameters preparationSourceLoss) : ENNReal :=
  Kakeya.realRpowENN caller.1 (-parameters.critical.structuralLoss)

structure WZ2PaperPreparedCoarseRegularizationCertificate
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
    let normalizationWeight :=
      wz2PaperPreparedCoarseNormalizationWeight mainline
    let totalMass := wz2PaperPreparedMergedTotalMass mainline
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
        ((normalizationWeight⁻¹ *
            (mainline.prepared.closureConstant *
              (regularizationLoss * totalMass) *
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

structure WZ2PaperPreparedCoarseRegularizedMainlineData
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
      WZ2PaperPreparedCoarseRegularizationCertificate mainline) where
  regularization :
    WZ2PaperPreparedCoarseParentRegularizationData
      mainline.prepared parameters.critical mainline.structural
      mainline.prepared.closureConstant
      (wz2PaperPreparedCoarseOutputConstant mainline)
      (wz2PaperPreparedCoarseNormalizationWeight mainline)
      (wz2PaperPreparedMergedTotalMass mainline)
      certificate.levelCount
  pullback :
    WZ2PaperPreparedCoarseParentPullbackData
      regularization certificate.parentExponent

end Kakeya.Assouad

end
