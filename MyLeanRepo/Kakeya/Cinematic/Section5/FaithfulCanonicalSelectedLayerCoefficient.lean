import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedLayerGeometricCancellation
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalFinalCoefficientBound
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalOrdinaryLoss
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedPaperClusterScale

/-!
# Selected-layer coefficients at the faithful canonical scales

This module rewrites both selected-layer branches into the same structured
coefficient.  The positive and singleton branches differ only by a fixed
branch constant and the Proposition 26 exponent.  In both cases the center
cardinality occurs with exponent `7 / 2`.
-/

namespace Kakeya.Cinematic

lemma ambientRestrictedPaperFiberCoefficient_le_one
    (t epsilon logLoss fiberRatio : ℝ)
    (ht : 0 < t)
    (hepsilon : 0 < epsilon)
    (hlogLoss : 1 ≤ logLoss)
    (hfiberRatio : 0 < fiberRatio) :
    ambientRestrictedPaperFiberCoefficient
        t epsilon logLoss fiberRatio ≤ 1 := by
  rw [ambientRestrictedPaperFiberCoefficient_eq_inv_six_logLoss
    t epsilon logLoss fiberRatio ht hepsilon
    (lt_of_lt_of_le zero_lt_one hlogLoss) hfiberRatio]
  have hdenominator : 1 ≤ 6 * logLoss := by
    nlinarith
  exact (div_le_one (by positivity)).2 hdenominator

noncomputable def faithfulCanonicalPositiveBranchConstant
    (C_positive tangency : ℝ) : ℝ :=
  24 * (8 * Real.sqrt 8) *
    C_positive * Real.rpow tangency C_positive

noncomputable def faithfulCanonicalSingletonBranchConstant
    (C_singleton tangency : ℝ) : ℝ :=
  24 *
    (2 * Real.sqrt 2 *
      Real.rpow 2 (3 / 2 : ℝ)) *
    C_singleton * Real.rpow tangency C_singleton

lemma positive_centers_factor_eq
    (centers : ℕ)
    (hcenters : 0 < centers) :
    (centers : ℝ) ^ 2 *
          (8 * (centers : ℝ)) *
          Real.sqrt (8 * (centers : ℝ)) =
      (8 * Real.sqrt 8) *
        Real.rpow (centers : ℝ) (7 / 2 : ℝ) := by
  have hcentersReal : 0 < (centers : ℝ) := by
    exact_mod_cast hcenters
  have hsqrt :
      Real.sqrt (8 * (centers : ℝ)) =
        Real.sqrt 8 * Real.sqrt (centers : ℝ) := by
    rw [Real.sqrt_mul (by norm_num)]
  have hpower :
      (centers : ℝ) ^ 3 * Real.sqrt (centers : ℝ) =
        Real.rpow (centers : ℝ) (7 / 2 : ℝ) := by
    calc
      (centers : ℝ) ^ 3 * Real.sqrt (centers : ℝ) =
          Real.rpow (centers : ℝ) (3 : ℝ) *
            Real.rpow (centers : ℝ) (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        congr 1
        exact (Real.rpow_natCast (centers : ℝ) 3).symm
      _ =
          Real.rpow (centers : ℝ)
            ((3 : ℝ) + (1 / 2 : ℝ)) :=
        (Real.rpow_add hcentersReal 3 (1 / 2 : ℝ)).symm
      _ =
          Real.rpow (centers : ℝ) (7 / 2 : ℝ) := by
        norm_num
  rw [hsqrt, ← hpower]
  ring

lemma singleton_centers_factor_eq
    (centers : ℕ)
    (hcenters : 0 < centers) :
    (centers : ℝ) ^ 2 *
          2 * Real.sqrt (2 : ℝ) *
          Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) =
      (2 * Real.sqrt 2 *
          Real.rpow 2 (3 / 2 : ℝ)) *
        Real.rpow (centers : ℝ) (7 / 2 : ℝ) := by
  have hcentersReal : 0 < (centers : ℝ) := by
    exact_mod_cast hcenters
  have hmul :
      Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) =
        Real.rpow 2 (3 / 2 : ℝ) *
          Real.rpow (centers : ℝ) (3 / 2 : ℝ) := by
    exact Real.mul_rpow (by norm_num) hcentersReal.le
  have hpower :
      (centers : ℝ) ^ 2 *
          Real.rpow (centers : ℝ) (3 / 2 : ℝ) =
        Real.rpow (centers : ℝ) (7 / 2 : ℝ) := by
    calc
      (centers : ℝ) ^ 2 *
            Real.rpow (centers : ℝ) (3 / 2 : ℝ) =
          Real.rpow (centers : ℝ) (2 : ℝ) *
            Real.rpow (centers : ℝ) (3 / 2 : ℝ) := by
        congr 1
        exact (Real.rpow_natCast (centers : ℝ) 2).symm
      _ =
          Real.rpow (centers : ℝ)
            ((2 : ℝ) + (3 / 2 : ℝ)) :=
        (Real.rpow_add hcentersReal 2 (3 / 2 : ℝ)).symm
      _ =
          Real.rpow (centers : ℝ) (7 / 2 : ℝ) := by
        norm_num
  rw [hmul, ← hpower]
  ring

lemma positive_layer_coefficient_normalization
    (fiberCoefficient parentLoss degreeLoss supportLoss
      retention parentScale C_positive tangency A logTail
      layerFactor parentArea fineArea cardUpper : ℝ)
    (centers mu : ℕ)
    (hcenters : 0 < centers) :
    ambientRestrictedLayerLinearizedLocalCoefficient
        (ambientRestrictedPositiveLayerBaseCoefficientOfFiber
          fiberCoefficient parentLoss degreeLoss supportLoss
          retention parentScale centers C_positive tangency A mu)
        (8 * (centers : ℝ)) cardUpper logTail layerFactor
        parentArea fineArea =
      faithfulCanonicalPositiveBranchConstant
          C_positive tangency *
        ((fiberCoefficient * parentLoss * degreeLoss *
              supportLoss * logTail * layerFactor) *
          Real.rpow parentScale (3 / 4 : ℝ) *
          Real.rpow retention (-1) *
          (Real.rpow A C_positive *
            Real.rpow (centers : ℝ) (7 / 2 : ℝ))) *
        (Real.sqrt cardUpper *
          Real.rpow parentArea (1 / 4 : ℝ) *
          Real.rpow fineArea (3 / 4 : ℝ)) *
        Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
  rw [ambientRestrictedLayerLinearizedLocalCoefficient,
    ambientRestrictedPositiveLayerBaseCoefficientOfFiber,
    Real.sqrt_mul (by positivity :
      0 ≤ 8 * (centers : ℝ))]
  have hfactor :=
    positive_centers_factor_eq centers hcenters
  dsimp only [faithfulCanonicalPositiveBranchConstant]
  calc
    ((24 * fiberCoefficient * parentLoss * degreeLoss *
                supportLoss * Real.rpow retention (-1)) *
              Real.rpow parentScale (3 / 4 : ℝ) *
              ((centers : ℝ) ^ 2 *
                (C_positive * Real.rpow tangency C_positive *
                  Real.rpow A C_positive)) *
              Real.rpow (mu : ℝ) (-3 / 2 : ℝ) *
            (8 * (centers : ℝ)) *
            (Real.sqrt (8 * (centers : ℝ)) *
              Real.sqrt cardUpper) *
            logTail *
          layerFactor) *
        Real.rpow parentArea (1 / 4 : ℝ) *
        Real.rpow fineArea (3 / 4 : ℝ) =
      (24 * C_positive * Real.rpow tangency C_positive) *
        (fiberCoefficient * parentLoss * degreeLoss *
          supportLoss * logTail * layerFactor) *
        Real.rpow parentScale (3 / 4 : ℝ) *
        Real.rpow retention (-1) *
        Real.rpow A C_positive *
        ((centers : ℝ) ^ 2 *
          (8 * (centers : ℝ)) *
          Real.sqrt (8 * (centers : ℝ))) *
        (Real.sqrt cardUpper *
          Real.rpow parentArea (1 / 4 : ℝ) *
          Real.rpow fineArea (3 / 4 : ℝ)) *
        Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by ring
    _ =
      24 * (8 * Real.sqrt 8) *
            C_positive * Real.rpow tangency C_positive *
          ((fiberCoefficient * parentLoss * degreeLoss *
                supportLoss * logTail * layerFactor) *
            Real.rpow parentScale (3 / 4 : ℝ) *
            Real.rpow retention (-1) *
            (Real.rpow A C_positive *
              Real.rpow (centers : ℝ) (7 / 2 : ℝ))) *
          (Real.sqrt cardUpper *
            Real.rpow parentArea (1 / 4 : ℝ) *
            Real.rpow fineArea (3 / 4 : ℝ)) *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
      rw [hfactor]
      ring

lemma singleton_layer_coefficient_normalization
    (fiberCoefficient parentLoss degreeLoss supportLoss
      retention parentScale C_singleton tangency A logTail
      layerFactor parentArea fineArea cardUpper : ℝ)
    (centers mu : ℕ)
    (hcenters : 0 < centers) :
    ambientRestrictedLayerLinearizedLocalCoefficient
        (ambientRestrictedSingletonLayerBaseCoefficientOfFiber
          fiberCoefficient parentLoss degreeLoss supportLoss
          retention parentScale centers C_singleton tangency A mu)
        2 cardUpper logTail layerFactor parentArea fineArea =
      faithfulCanonicalSingletonBranchConstant
          C_singleton tangency *
        ((fiberCoefficient * parentLoss * degreeLoss *
              supportLoss * logTail * layerFactor) *
          Real.rpow parentScale (3 / 4 : ℝ) *
          Real.rpow retention (-1) *
          (Real.rpow A C_singleton *
            Real.rpow (centers : ℝ) (7 / 2 : ℝ))) *
        (Real.sqrt cardUpper *
          Real.rpow parentArea (1 / 4 : ℝ) *
          Real.rpow fineArea (3 / 4 : ℝ)) *
        Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
  rw [ambientRestrictedLayerLinearizedLocalCoefficient,
    ambientRestrictedSingletonLayerBaseCoefficientOfFiber,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hfactor :=
    singleton_centers_factor_eq centers hcenters
  dsimp only [faithfulCanonicalSingletonBranchConstant]
  calc
    ((24 * fiberCoefficient * parentLoss * degreeLoss *
                  supportLoss * Real.rpow retention (-1)) *
                Real.rpow parentScale (3 / 4 : ℝ) *
                ((centers : ℝ) ^ 2 *
                  (C_singleton * Real.rpow tangency C_singleton *
                    Real.rpow A C_singleton)) *
                Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) *
                Real.rpow (mu : ℝ) (-3 / 2 : ℝ) *
              2 *
              (Real.sqrt 2 * Real.sqrt cardUpper) *
              logTail *
            layerFactor) *
          Real.rpow parentArea (1 / 4 : ℝ) *
        Real.rpow fineArea (3 / 4 : ℝ) =
      (24 * C_singleton * Real.rpow tangency C_singleton) *
        (fiberCoefficient * parentLoss * degreeLoss *
          supportLoss * logTail * layerFactor) *
        Real.rpow parentScale (3 / 4 : ℝ) *
        Real.rpow retention (-1) *
        Real.rpow A C_singleton *
        ((centers : ℝ) ^ 2 * 2 * Real.sqrt 2 *
          Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ)) *
        (Real.sqrt cardUpper *
          Real.rpow parentArea (1 / 4 : ℝ) *
          Real.rpow fineArea (3 / 4 : ℝ)) *
        Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by ring
    _ =
      24 *
            (2 * Real.sqrt 2 *
              Real.rpow 2 (3 / 2 : ℝ)) *
            C_singleton * Real.rpow tangency C_singleton *
          ((fiberCoefficient * parentLoss * degreeLoss *
                supportLoss * logTail * layerFactor) *
            Real.rpow parentScale (3 / 4 : ℝ) *
            Real.rpow retention (-1) *
            (Real.rpow A C_singleton *
              Real.rpow (centers : ℝ) (7 / 2 : ℝ))) *
          (Real.sqrt cardUpper *
            Real.rpow parentArea (1 / 4 : ℝ) *
            Real.rpow fineArea (3 / 4 : ℝ)) *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
      rw [hfactor]
      ring

lemma selected_layer_ordinary_factor_le
    (outerLoss fiberCoefficient logTail : ℝ)
    (layerCount fiberLoss massFactor selectedCard degreeLoss
      supportCard ambientCard fineCard : ℕ)
    (houterLoss : 0 ≤ outerLoss)
    (hfiberCoefficient_le : fiberCoefficient ≤ 1)
    (hlogTail : 0 ≤ logTail)
    (hfiberLoss :
      fiberLoss = (Nat.log2 ambientCard + 1) ^ 2)
    (hmassFactor :
      massFactor = 4 * layerCount * fiberLoss)
    (hdegreeLoss :
      degreeLoss = Nat.log2 fineCard + 1)
    (hsupportCard : supportCard ≤ ambientCard) :
    outerLoss *
        (fiberCoefficient *
          ((Nat.log2 selectedCard + 1 : ℕ) : ℝ) *
          (degreeLoss : ℝ) *
          ((Nat.log2 supportCard + 1 : ℕ) : ℝ) *
          logTail *
          ((2 * massFactor : ℕ) : ℝ)) ≤
      faithfulCanonicalOrdinaryDyadicLoss
        outerLoss logTail layerCount ambientCard fineCard selectedCard := by
  have hsupportLogNat :
      Nat.log2 supportCard + 1 ≤
        Nat.log2 ambientCard + 1 := by
    gcongr
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right hsupportCard
  have hsupportLog2 :
      Nat.log2 supportCard ≤ Nat.log2 ambientCard := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right hsupportCard
  have hsupportLog :
      (((Nat.log2 supportCard + 1 : ℕ) : ℝ)) ≤
        (((Nat.log2 ambientCard + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hsupportLogNat
  rw [hmassFactor, hfiberLoss, hdegreeLoss]
  dsimp only [faithfulCanonicalOrdinaryDyadicLoss]
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
    Nat.cast_ofNat]
  calc
    outerLoss *
          (fiberCoefficient *
            ((Nat.log2 selectedCard : ℝ) + 1) *
            ((Nat.log2 fineCard : ℝ) + 1) *
            ((Nat.log2 supportCard : ℝ) + 1) *
            logTail *
            (2 *
              (4 * (layerCount : ℝ) *
                ((Nat.log2 ambientCard : ℝ) + 1) ^ 2))) ≤
        outerLoss *
          (1 *
            ((Nat.log2 selectedCard : ℝ) + 1) *
            ((Nat.log2 fineCard : ℝ) + 1) *
            ((Nat.log2 ambientCard : ℝ) + 1) *
            logTail *
            (2 *
              (4 * (layerCount : ℝ) *
                ((Nat.log2 ambientCard : ℝ) + 1) ^ 2))) := by
      gcongr
    _ =
        outerLoss *
          (8 * (layerCount : ℝ) *
              ((Nat.log2 ambientCard : ℝ) + 1) ^ 2 *
            ((Nat.log2 selectedCard : ℝ) + 1) *
            ((Nat.log2 fineCard : ℝ) + 1) *
            ((Nat.log2 ambientCard : ℝ) + 1) *
            logTail) := by ring

lemma selected_layer_canonical_structured_factor_le
    (delta outerLoss fiberCoefficient logTail parentScale retention A
      parentConstant retentionConstant clusterConstant D metricExponent
      propositionExponent coverExponent : ℝ)
    (layerCount fiberLoss massFactor selectedCard degreeLoss supportCard
      ambientCard fineCard centers : ℕ)
    (hdelta : 0 < delta)
    (hparentScale : 0 ≤ parentScale)
    (hretention : 0 < retention)
    (hA : 0 ≤ A)
    (hparentConstant : 0 < parentConstant)
    (hretentionConstant : 0 < retentionConstant)
    (hclusterConstant : 0 < clusterConstant)
    (hD : 0 < D)
    (hpropositionExponent : 0 ≤ propositionExponent)
    (hcoverExponent : 0 ≤ coverExponent)
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
          (fiberCoefficient *
            (((Nat.log2 selectedCard + 1 : ℕ) : ℝ)) *
            (degreeLoss : ℝ) *
            (((Nat.log2 supportCard + 1 : ℕ) : ℝ)) *
            logTail *
            (((2 * massFactor : ℕ) : ℝ))) *
          Real.rpow parentScale (3 / 4 : ℝ) *
          Real.rpow retention (-1) *
          (Real.rpow A propositionExponent *
            Real.rpow (centers : ℝ) (7 / 2 : ℝ)) ≤
      faithfulCanonicalFinalCoefficientConstant
          parentConstant retentionConstant clusterConstant D
          propositionExponent coverExponent *
        Real.rpow delta
          (-(faithfulCanonicalStructuredScaleLoss
                (propositionExponent +
                  (7 / 2 : ℝ) * coverExponent)
                metricExponent +
              faithfulCanonicalOrdinaryLoss metricExponent)) := by
  have hactualOrdinary :=
    selected_layer_ordinary_factor_le
      outerLoss fiberCoefficient logTail layerCount fiberLoss massFactor
      selectedCard degreeLoss supportCard ambientCard fineCard
      houterLoss hfiberCoefficient_le hlogTail hfiberLoss hmassFactor
      hdegreeLoss hsupportCard
  have hactualBound :
      outerLoss *
          (fiberCoefficient *
            (((Nat.log2 selectedCard + 1 : ℕ) : ℝ)) *
            (degreeLoss : ℝ) *
            (((Nat.log2 supportCard + 1 : ℕ) : ℝ)) *
            logTail *
            (((2 * massFactor : ℕ) : ℝ))) ≤
        Real.rpow delta
          (-faithfulCanonicalOrdinaryLoss metricExponent) :=
    hactualOrdinary.trans hordinaryBound
  exact canonical_structured_coefficient_le
    delta parentScale (Real.rpow retention (-1)) A
    (outerLoss *
      (fiberCoefficient *
        (((Nat.log2 selectedCard + 1 : ℕ) : ℝ)) *
        (degreeLoss : ℝ) *
        (((Nat.log2 supportCard + 1 : ℕ) : ℝ)) *
        logTail *
        (((2 * massFactor : ℕ) : ℝ))))
    parentConstant retentionConstant clusterConstant D metricExponent
    propositionExponent coverExponent centers hdelta hparentScale
    (Real.rpow_nonneg hretention.le _) hA hparentConstant
    hretentionConstant hclusterConstant hD hpropositionExponent
    hcoverExponent hparentBound hretentionBound hA_bound hcenters
    hactualBound

lemma selected_layer_coefficient_after_geometric_cancellation
    (branchConstant structuredFactor geometricFactor
      geometricConstant delta muPower : ℝ)
    (hbranchConstant : 0 ≤ branchConstant)
    (hstructuredFactor : 0 ≤ structuredFactor)
    (hgeometricFactor : 0 ≤ geometricFactor)
    (hmuPower : 0 ≤ muPower)
    (hgeometric :
      geometricFactor ≤ geometricConstant * delta) :
    branchConstant * structuredFactor *
          geometricFactor * muPower ≤
      branchConstant * structuredFactor *
          (geometricConstant * delta) * muPower := by
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hgeometric
      (mul_nonneg hbranchConstant hstructuredFactor))
    hmuPower

lemma selected_layer_canonical_local_coefficient_le
    (delta outerLoss fiberCoefficient logTail parentScale retention A
      parentConstant retentionConstant clusterConstant D metricExponent
      propositionExponent coverExponent localCoefficient branchConstant
      geometricFactor geometricConstant muPower : ℝ)
    (layerCount fiberLoss massFactor selectedCard degreeLoss supportCard
      ambientCard fineCard centers : ℕ)
    (hdelta : 0 < delta)
    (hparentScale : 0 ≤ parentScale)
    (hretention : 0 < retention)
    (hA : 0 ≤ A)
    (hparentConstant : 0 < parentConstant)
    (hretentionConstant : 0 < retentionConstant)
    (hclusterConstant : 0 < clusterConstant)
    (hD : 0 < D)
    (hpropositionExponent : 0 ≤ propositionExponent)
    (hcoverExponent : 0 ≤ coverExponent)
    (hbranchConstant : 0 ≤ branchConstant)
    (hgeometricFactor : 0 ≤ geometricFactor)
    (hmuPower : 0 ≤ muPower)
    (hnormalization :
      localCoefficient =
        branchConstant *
          ((fiberCoefficient *
                (((Nat.log2 selectedCard + 1 : ℕ) : ℝ)) *
                (degreeLoss : ℝ) *
                (((Nat.log2 supportCard + 1 : ℕ) : ℝ)) *
                logTail *
                (((2 * massFactor : ℕ) : ℝ))) *
            Real.rpow parentScale (3 / 4 : ℝ) *
            Real.rpow retention (-1) *
            (Real.rpow A propositionExponent *
              Real.rpow (centers : ℝ) (7 / 2 : ℝ))) *
          geometricFactor * muPower)
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
          (-faithfulCanonicalOrdinaryLoss metricExponent))
    (hgeometric :
      geometricFactor ≤ geometricConstant * delta) :
    outerLoss * localCoefficient ≤
      branchConstant *
          faithfulCanonicalFinalCoefficientConstant
            parentConstant retentionConstant clusterConstant D
            propositionExponent coverExponent *
          Real.rpow delta
            (-(faithfulCanonicalStructuredScaleLoss
                  (propositionExponent +
                    (7 / 2 : ℝ) * coverExponent)
                  metricExponent +
                faithfulCanonicalOrdinaryLoss metricExponent)) *
          (geometricConstant * delta) * muPower := by
  have hstructured :=
    selected_layer_canonical_structured_factor_le
      delta outerLoss fiberCoefficient logTail parentScale retention A
      parentConstant retentionConstant clusterConstant D metricExponent
      propositionExponent coverExponent layerCount fiberLoss massFactor
      selectedCard degreeLoss supportCard ambientCard fineCard centers
      hdelta hparentScale hretention hA hparentConstant
      hretentionConstant hclusterConstant hD hpropositionExponent
      hcoverExponent hparentBound hretentionBound hA_bound hcenters
      houterLoss hfiberCoefficient_le hlogTail hfiberLoss hmassFactor
      hdegreeLoss hsupportCard hordinaryBound
  let upper : ℝ :=
    faithfulCanonicalFinalCoefficientConstant
        parentConstant retentionConstant clusterConstant D
        propositionExponent coverExponent *
      Real.rpow delta
        (-(faithfulCanonicalStructuredScaleLoss
              (propositionExponent +
                (7 / 2 : ℝ) * coverExponent)
              metricExponent +
            faithfulCanonicalOrdinaryLoss metricExponent))
  have hupper : 0 ≤ upper := by
    dsimp only [upper, faithfulCanonicalFinalCoefficientConstant]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (Real.rpow_nonneg hparentConstant.le _)
          hretentionConstant.le)
        (mul_nonneg
          (Real.rpow_nonneg hclusterConstant.le _)
          (Real.rpow_nonneg
            (mul_nonneg hD.le
              (Real.rpow_nonneg
                (mul_nonneg (by norm_num) hclusterConstant.le) _)) _)))
      (Real.rpow_nonneg hdelta.le _)
  have hfirst :
      branchConstant *
          (outerLoss *
              (fiberCoefficient *
                  (((Nat.log2 selectedCard + 1 : ℕ) : ℝ)) *
                  (degreeLoss : ℝ) *
                  (((Nat.log2 supportCard + 1 : ℕ) : ℝ)) *
                  logTail *
                  (((2 * massFactor : ℕ) : ℝ))) *
              Real.rpow parentScale (3 / 4 : ℝ) *
              Real.rpow retention (-1) *
              (Real.rpow A propositionExponent *
                Real.rpow (centers : ℝ) (7 / 2 : ℝ))) *
          geometricFactor * muPower ≤
        branchConstant * upper * geometricFactor * muPower := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hstructured hbranchConstant)
        hgeometricFactor)
      hmuPower
  have hsecond :
      branchConstant * upper * geometricFactor * muPower ≤
        branchConstant * upper *
          (geometricConstant * delta) * muPower := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgeometric
        (mul_nonneg hbranchConstant hupper))
      hmuPower
  calc
    outerLoss * localCoefficient =
      branchConstant *
          (outerLoss *
              (fiberCoefficient *
                  (((Nat.log2 selectedCard + 1 : ℕ) : ℝ)) *
                  (degreeLoss : ℝ) *
                  (((Nat.log2 supportCard + 1 : ℕ) : ℝ)) *
                  logTail *
                  (((2 * massFactor : ℕ) : ℝ))) *
              Real.rpow parentScale (3 / 4 : ℝ) *
              Real.rpow retention (-1) *
              (Real.rpow A propositionExponent *
                Real.rpow (centers : ℝ) (7 / 2 : ℝ))) *
        geometricFactor * muPower := by
      rw [hnormalization]
      ring
    _ ≤ branchConstant * upper * geometricFactor * muPower := hfirst
    _ ≤ branchConstant * upper *
          (geometricConstant * delta) * muPower := hsecond
    _ =
      branchConstant *
          faithfulCanonicalFinalCoefficientConstant
            parentConstant retentionConstant clusterConstant D
            propositionExponent coverExponent *
          Real.rpow delta
            (-(faithfulCanonicalStructuredScaleLoss
                  (propositionExponent +
                    (7 / 2 : ℝ) * coverExponent)
                  metricExponent +
                faithfulCanonicalOrdinaryLoss metricExponent)) *
          (geometricConstant * delta) * muPower := by
      dsimp only [upper]
      ring

end Kakeya.Cinematic
