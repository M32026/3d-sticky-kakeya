import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalSelectedLayerCoefficient

/-!
# Selected-layer bounds at the faithful canonical scales

This module combines the exact positive and singleton coefficient
normalizations with the canonical scale ledger and the representative-scale
geometric cancellation.
-/

namespace Kakeya.Cinematic

lemma positive_layer_canonical_local_coefficient_le
    (delta tRep DeltaRep C_R C_shading C_KT areaConstant
      outerLoss fiberCoefficient logTail parentScale retention A
      parentConstant retentionConstant clusterConstant D metricExponent
      coverExponent C_positive tangency parentArea cardUpper : ℝ)
    (layerCount fiberLoss massFactor selectedCard degreeLoss supportCard
      ambientCard fineCard centers mu : ℕ)
    (hdelta : 0 < delta)
    (htRep : 0 < tRep)
    (hDeltaRep : 0 < DeltaRep)
    (hC_R : 0 < C_R)
    (hC_shading : 0 < C_shading)
    (hC_KT : 0 < C_KT)
    (hareaConstant : 0 < areaConstant)
    (hparentArea : 0 ≤ parentArea)
    (hcardUpper : 0 ≤ cardUpper)
    (hparentAreaBound :
      parentArea ≤ areaConstant * DeltaRep *
        Real.sqrt (DeltaRep / (C_R * tRep)))
    (hcardUpperBound :
      cardUpper ≤ C_KT * 3 * tRep / delta)
    (hparentScale : 0 ≤ parentScale)
    (hretention : 0 < retention)
    (hA : 0 ≤ A)
    (hparentConstant : 0 < parentConstant)
    (hretentionConstant : 0 < retentionConstant)
    (hclusterConstant : 0 < clusterConstant)
    (hD : 0 < D)
    (hcoverExponent : 0 ≤ coverExponent)
    (hC_positive : 0 ≤ C_positive)
    (htangency : 0 ≤ tangency)
    (hcentersPos : 0 < centers)
    (hparentBound :
      parentScale ≤ parentConstant *
        Real.rpow delta
          (-faithfulCanonicalParentScaleLoss metricExponent))
    (hretentionBound :
      Real.rpow retention (-1) ≤ retentionConstant *
        Real.rpow delta
          (-(metricExponent + metricExponent ^ 2)))
    (hA_bound :
      A ≤ clusterConstant *
        Real.rpow delta
          (-(metricExponent + metricExponent ^ 2)))
    (hcenters :
      (centers : ℝ) ≤
        D * Real.rpow (48 * A) coverExponent)
    (houterLoss : 0 ≤ outerLoss)
    (hfiberCoefficient_le : fiberCoefficient ≤ 1)
    (hlogTail : 0 ≤ logTail)
    (hfiberLoss :
      fiberLoss = (Nat.log2 ambientCard + 1) ^ 2)
    (hmassFactor :
      massFactor = 4 * layerCount * fiberLoss)
    (hdegreeLoss :
      degreeLoss = Nat.log2 fineCard + 1)
    (hsupportCard : supportCard ≤ ambientCard)
    (hordinaryBound :
      faithfulCanonicalOrdinaryDyadicLoss outerLoss logTail
          layerCount ambientCard fineCard selectedCard ≤
        Real.rpow delta
          (-faithfulCanonicalOrdinaryLoss metricExponent)) :
    outerLoss *
        ambientRestrictedLayerLinearizedLocalCoefficient
          (ambientRestrictedPositiveLayerBaseCoefficientOfFiber
            fiberCoefficient
            (((Nat.log2 selectedCard + 1 : ℕ) : ℝ))
            (degreeLoss : ℝ)
            (((Nat.log2 supportCard + 1 : ℕ) : ℝ))
            retention parentScale centers C_positive tangency A mu)
          (8 * (centers : ℝ)) cardUpper logTail
          (((2 * massFactor : ℕ) : ℝ)) parentArea
          (ambientRestrictedSelectedFineGeometricArea
            C_shading delta C_R tRep DeltaRep) ≤
      faithfulCanonicalPositiveBranchConstant C_positive tangency *
          faithfulCanonicalFinalCoefficientConstant
            parentConstant retentionConstant clusterConstant D
            C_positive coverExponent *
          Real.rpow delta
            (-(faithfulCanonicalStructuredScaleLoss
                  (C_positive +
                    (7 / 2 : ℝ) * coverExponent)
                  metricExponent +
                faithfulCanonicalOrdinaryLoss metricExponent)) *
          ((Real.sqrt (3 * C_KT) *
              Real.rpow areaConstant (1 / 4 : ℝ) *
              Real.rpow
                (2 * C_shading * Real.sqrt C_shading)
                (3 / 4 : ℝ) /
              Real.sqrt C_R) * delta) *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
  let geometricFactor : ℝ :=
    Real.sqrt cardUpper *
      Real.rpow parentArea (1 / 4 : ℝ) *
      Real.rpow
        (ambientRestrictedSelectedFineGeometricArea
          C_shading delta C_R tRep DeltaRep)
        (3 / 4 : ℝ)
  let geometricConstant : ℝ :=
    Real.sqrt (3 * C_KT) *
      Real.rpow areaConstant (1 / 4 : ℝ) *
      Real.rpow
        (2 * C_shading * Real.sqrt C_shading)
        (3 / 4 : ℝ) /
      Real.sqrt C_R
  have hgeometric :
      geometricFactor ≤ geometricConstant * delta := by
    dsimp only [geometricFactor, geometricConstant]
    exact ambient_restricted_layer_geometric_cancellation
      delta tRep DeltaRep C_R C_shading C_KT areaConstant
      parentArea cardUpper hdelta htRep hDeltaRep hC_R hC_shading
      hC_KT hareaConstant hparentArea hcardUpper hparentAreaBound
      hcardUpperBound
  have hfineArea :
      0 ≤ ambientRestrictedSelectedFineGeometricArea
        C_shading delta C_R tRep DeltaRep := by
    dsimp only [ambientRestrictedSelectedFineGeometricArea]
    positivity
  have hgeometricFactor : 0 ≤ geometricFactor := by
    dsimp only [geometricFactor]
    exact mul_nonneg
      (mul_nonneg
        (Real.sqrt_nonneg cardUpper)
        (Real.rpow_nonneg hparentArea _))
      (Real.rpow_nonneg hfineArea _)
  have hbranch :
      0 ≤ faithfulCanonicalPositiveBranchConstant
        C_positive tangency := by
    dsimp only [faithfulCanonicalPositiveBranchConstant]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (show (0 : ℝ) ≤ 24 by norm_num)
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg 8)))
        hC_positive)
      (Real.rpow_nonneg htangency _)
  have hnormalization :
      ambientRestrictedLayerLinearizedLocalCoefficient
          (ambientRestrictedPositiveLayerBaseCoefficientOfFiber
            fiberCoefficient
            (((Nat.log2 selectedCard + 1 : ℕ) : ℝ))
            (degreeLoss : ℝ)
            (((Nat.log2 supportCard + 1 : ℕ) : ℝ))
            retention parentScale centers C_positive tangency A mu)
          (8 * (centers : ℝ)) cardUpper logTail
          (((2 * massFactor : ℕ) : ℝ)) parentArea
          (ambientRestrictedSelectedFineGeometricArea
            C_shading delta C_R tRep DeltaRep) =
        faithfulCanonicalPositiveBranchConstant C_positive tangency *
          ((fiberCoefficient *
                (((Nat.log2 selectedCard + 1 : ℕ) : ℝ)) *
                (degreeLoss : ℝ) *
                (((Nat.log2 supportCard + 1 : ℕ) : ℝ)) *
                logTail *
                (((2 * massFactor : ℕ) : ℝ))) *
            Real.rpow parentScale (3 / 4 : ℝ) *
            Real.rpow retention (-1) *
            (Real.rpow A C_positive *
              Real.rpow (centers : ℝ) (7 / 2 : ℝ))) *
          geometricFactor *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
    simpa only [geometricFactor] using
      positive_layer_coefficient_normalization
        fiberCoefficient
        (((Nat.log2 selectedCard + 1 : ℕ) : ℝ))
        (degreeLoss : ℝ)
        (((Nat.log2 supportCard + 1 : ℕ) : ℝ))
        retention parentScale C_positive tangency A logTail
        (((2 * massFactor : ℕ) : ℝ)) parentArea
        (ambientRestrictedSelectedFineGeometricArea
          C_shading delta C_R tRep DeltaRep)
        cardUpper centers mu hcentersPos
  simpa only [geometricFactor, geometricConstant] using
    selected_layer_canonical_local_coefficient_le
      delta outerLoss fiberCoefficient logTail parentScale retention A
      parentConstant retentionConstant clusterConstant D metricExponent
      C_positive coverExponent
      (ambientRestrictedLayerLinearizedLocalCoefficient
        (ambientRestrictedPositiveLayerBaseCoefficientOfFiber
          fiberCoefficient
          (((Nat.log2 selectedCard + 1 : ℕ) : ℝ))
          (degreeLoss : ℝ)
          (((Nat.log2 supportCard + 1 : ℕ) : ℝ))
          retention parentScale centers C_positive tangency A mu)
        (8 * (centers : ℝ)) cardUpper logTail
        (((2 * massFactor : ℕ) : ℝ)) parentArea
        (ambientRestrictedSelectedFineGeometricArea
          C_shading delta C_R tRep DeltaRep))
      (faithfulCanonicalPositiveBranchConstant C_positive tangency)
      geometricFactor geometricConstant
      (Real.rpow (mu : ℝ) (-3 / 2 : ℝ))
      layerCount fiberLoss massFactor selectedCard degreeLoss supportCard
      ambientCard fineCard centers hdelta hparentScale hretention hA
      hparentConstant hretentionConstant hclusterConstant hD hC_positive
      hcoverExponent hbranch hgeometricFactor
      (Real.rpow_nonneg (Nat.cast_nonneg mu) _) hnormalization
      hparentBound hretentionBound hA_bound hcenters houterLoss
      hfiberCoefficient_le hlogTail hfiberLoss hmassFactor hdegreeLoss
      hsupportCard hordinaryBound hgeometric

lemma singleton_layer_canonical_local_coefficient_le
    (delta tRep DeltaRep C_R C_shading C_KT areaConstant
      outerLoss fiberCoefficient logTail parentScale retention A
      parentConstant retentionConstant clusterConstant D metricExponent
      coverExponent C_singleton tangency parentArea cardUpper : ℝ)
    (layerCount fiberLoss massFactor selectedCard degreeLoss supportCard
      ambientCard fineCard centers mu : ℕ)
    (hdelta : 0 < delta)
    (htRep : 0 < tRep)
    (hDeltaRep : 0 < DeltaRep)
    (hC_R : 0 < C_R)
    (hC_shading : 0 < C_shading)
    (hC_KT : 0 < C_KT)
    (hareaConstant : 0 < areaConstant)
    (hparentArea : 0 ≤ parentArea)
    (hcardUpper : 0 ≤ cardUpper)
    (hparentAreaBound :
      parentArea ≤ areaConstant * DeltaRep *
        Real.sqrt (DeltaRep / (C_R * tRep)))
    (hcardUpperBound :
      cardUpper ≤ C_KT * 3 * tRep / delta)
    (hparentScale : 0 ≤ parentScale)
    (hretention : 0 < retention)
    (hA : 0 ≤ A)
    (hparentConstant : 0 < parentConstant)
    (hretentionConstant : 0 < retentionConstant)
    (hclusterConstant : 0 < clusterConstant)
    (hD : 0 < D)
    (hcoverExponent : 0 ≤ coverExponent)
    (hC_singleton : 0 ≤ C_singleton)
    (htangency : 0 ≤ tangency)
    (hcentersPos : 0 < centers)
    (hparentBound :
      parentScale ≤ parentConstant *
        Real.rpow delta
          (-faithfulCanonicalParentScaleLoss metricExponent))
    (hretentionBound :
      Real.rpow retention (-1) ≤ retentionConstant *
        Real.rpow delta
          (-(metricExponent + metricExponent ^ 2)))
    (hA_bound :
      A ≤ clusterConstant *
        Real.rpow delta
          (-(metricExponent + metricExponent ^ 2)))
    (hcenters :
      (centers : ℝ) ≤
        D * Real.rpow (48 * A) coverExponent)
    (houterLoss : 0 ≤ outerLoss)
    (hfiberCoefficient_le : fiberCoefficient ≤ 1)
    (hlogTail : 0 ≤ logTail)
    (hfiberLoss :
      fiberLoss = (Nat.log2 ambientCard + 1) ^ 2)
    (hmassFactor :
      massFactor = 4 * layerCount * fiberLoss)
    (hdegreeLoss :
      degreeLoss = Nat.log2 fineCard + 1)
    (hsupportCard : supportCard ≤ ambientCard)
    (hordinaryBound :
      faithfulCanonicalOrdinaryDyadicLoss outerLoss logTail
          layerCount ambientCard fineCard selectedCard ≤
        Real.rpow delta
          (-faithfulCanonicalOrdinaryLoss metricExponent)) :
    outerLoss *
        ambientRestrictedLayerLinearizedLocalCoefficient
          (ambientRestrictedSingletonLayerBaseCoefficientOfFiber
            fiberCoefficient
            (((Nat.log2 selectedCard + 1 : ℕ) : ℝ))
            (degreeLoss : ℝ)
            (((Nat.log2 supportCard + 1 : ℕ) : ℝ))
            retention parentScale centers C_singleton tangency A mu)
          2 cardUpper logTail
          (((2 * massFactor : ℕ) : ℝ)) parentArea
          (ambientRestrictedSelectedFineGeometricArea
            C_shading delta C_R tRep DeltaRep) ≤
      faithfulCanonicalSingletonBranchConstant C_singleton tangency *
          faithfulCanonicalFinalCoefficientConstant
            parentConstant retentionConstant clusterConstant D
            C_singleton coverExponent *
          Real.rpow delta
            (-(faithfulCanonicalStructuredScaleLoss
                  (C_singleton +
                    (7 / 2 : ℝ) * coverExponent)
                  metricExponent +
                faithfulCanonicalOrdinaryLoss metricExponent)) *
          ((Real.sqrt (3 * C_KT) *
              Real.rpow areaConstant (1 / 4 : ℝ) *
              Real.rpow
                (2 * C_shading * Real.sqrt C_shading)
                (3 / 4 : ℝ) /
              Real.sqrt C_R) * delta) *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
  let geometricFactor : ℝ :=
    Real.sqrt cardUpper *
      Real.rpow parentArea (1 / 4 : ℝ) *
      Real.rpow
        (ambientRestrictedSelectedFineGeometricArea
          C_shading delta C_R tRep DeltaRep)
        (3 / 4 : ℝ)
  let geometricConstant : ℝ :=
    Real.sqrt (3 * C_KT) *
      Real.rpow areaConstant (1 / 4 : ℝ) *
      Real.rpow
        (2 * C_shading * Real.sqrt C_shading)
        (3 / 4 : ℝ) /
      Real.sqrt C_R
  have hgeometric :
      geometricFactor ≤ geometricConstant * delta := by
    dsimp only [geometricFactor, geometricConstant]
    exact ambient_restricted_layer_geometric_cancellation
      delta tRep DeltaRep C_R C_shading C_KT areaConstant
      parentArea cardUpper hdelta htRep hDeltaRep hC_R hC_shading
      hC_KT hareaConstant hparentArea hcardUpper hparentAreaBound
      hcardUpperBound
  have hfineArea :
      0 ≤ ambientRestrictedSelectedFineGeometricArea
        C_shading delta C_R tRep DeltaRep := by
    dsimp only [ambientRestrictedSelectedFineGeometricArea]
    positivity
  have hgeometricFactor : 0 ≤ geometricFactor := by
    dsimp only [geometricFactor]
    exact mul_nonneg
      (mul_nonneg
        (Real.sqrt_nonneg cardUpper)
        (Real.rpow_nonneg hparentArea _))
      (Real.rpow_nonneg hfineArea _)
  have hbranch :
      0 ≤ faithfulCanonicalSingletonBranchConstant
        C_singleton tangency := by
    have hfixed :
        0 ≤
          24 *
            (2 * Real.sqrt 2 *
              Real.rpow 2 (3 / 2 : ℝ)) := by
      exact mul_nonneg (by norm_num) <|
        mul_nonneg
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2))
          (Real.rpow_nonneg (by norm_num) _)
    dsimp only [faithfulCanonicalSingletonBranchConstant]
    exact mul_nonneg
      (mul_nonneg hfixed hC_singleton)
      (Real.rpow_nonneg htangency _)
  have hnormalization :
      ambientRestrictedLayerLinearizedLocalCoefficient
          (ambientRestrictedSingletonLayerBaseCoefficientOfFiber
            fiberCoefficient
            (((Nat.log2 selectedCard + 1 : ℕ) : ℝ))
            (degreeLoss : ℝ)
            (((Nat.log2 supportCard + 1 : ℕ) : ℝ))
            retention parentScale centers C_singleton tangency A mu)
          2 cardUpper logTail
          (((2 * massFactor : ℕ) : ℝ)) parentArea
          (ambientRestrictedSelectedFineGeometricArea
            C_shading delta C_R tRep DeltaRep) =
        faithfulCanonicalSingletonBranchConstant C_singleton tangency *
          ((fiberCoefficient *
                (((Nat.log2 selectedCard + 1 : ℕ) : ℝ)) *
                (degreeLoss : ℝ) *
                (((Nat.log2 supportCard + 1 : ℕ) : ℝ)) *
                logTail *
                (((2 * massFactor : ℕ) : ℝ))) *
            Real.rpow parentScale (3 / 4 : ℝ) *
            Real.rpow retention (-1) *
            (Real.rpow A C_singleton *
              Real.rpow (centers : ℝ) (7 / 2 : ℝ))) *
          geometricFactor *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
    simpa only [geometricFactor] using
      singleton_layer_coefficient_normalization
        fiberCoefficient
        (((Nat.log2 selectedCard + 1 : ℕ) : ℝ))
        (degreeLoss : ℝ)
        (((Nat.log2 supportCard + 1 : ℕ) : ℝ))
        retention parentScale C_singleton tangency A logTail
        (((2 * massFactor : ℕ) : ℝ)) parentArea
        (ambientRestrictedSelectedFineGeometricArea
          C_shading delta C_R tRep DeltaRep)
        cardUpper centers mu hcentersPos
  simpa only [geometricFactor, geometricConstant] using
    selected_layer_canonical_local_coefficient_le
      delta outerLoss fiberCoefficient logTail parentScale retention A
      parentConstant retentionConstant clusterConstant D metricExponent
      C_singleton coverExponent
      (ambientRestrictedLayerLinearizedLocalCoefficient
        (ambientRestrictedSingletonLayerBaseCoefficientOfFiber
          fiberCoefficient
          (((Nat.log2 selectedCard + 1 : ℕ) : ℝ))
          (degreeLoss : ℝ)
          (((Nat.log2 supportCard + 1 : ℕ) : ℝ))
          retention parentScale centers C_singleton tangency A mu)
        2 cardUpper logTail
        (((2 * massFactor : ℕ) : ℝ)) parentArea
        (ambientRestrictedSelectedFineGeometricArea
          C_shading delta C_R tRep DeltaRep))
      (faithfulCanonicalSingletonBranchConstant C_singleton tangency)
      geometricFactor geometricConstant
      (Real.rpow (mu : ℝ) (-3 / 2 : ℝ))
      layerCount fiberLoss massFactor selectedCard degreeLoss supportCard
      ambientCard fineCard centers hdelta hparentScale hretention hA
      hparentConstant hretentionConstant hclusterConstant hD hC_singleton
      hcoverExponent hbranch hgeometricFactor
      (Real.rpow_nonneg (Nat.cast_nonneg mu) _) hnormalization
      hparentBound hretentionBound hA_bound hcenters houterLoss
      hfiberCoefficient_le hlogTail hfiberLoss hmassFactor hdegreeLoss
      hsupportCard hordinaryBound hgeometric

end Kakeya.Cinematic
