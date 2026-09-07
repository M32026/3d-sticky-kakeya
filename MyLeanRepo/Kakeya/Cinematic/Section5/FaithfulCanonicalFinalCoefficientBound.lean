import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalClusterScaleBound
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalScaleLoss

/-!
# Final structured coefficient bound for the faithful canonical scales

This module combines the parent tangency scale, inverse retention, paper
cluster parameter, tangent-ball cover cardinality, and one budget for all
remaining ordinary losses.
-/

namespace Kakeya.Cinematic

noncomputable def faithfulCanonicalFinalCoefficientConstant
    (parentConstant retentionConstant clusterConstant D
      propositionExponent coverExponent : ℝ) : ℝ :=
  Real.rpow parentConstant (3 / 4 : ℝ) *
    retentionConstant *
    (Real.rpow clusterConstant propositionExponent *
      Real.rpow
        (D * Real.rpow (48 * clusterConstant) coverExponent)
        (7 / 2 : ℝ))

lemma canonical_structured_coefficient_le
    (delta parentScale retentionInverse A ordinaryLoss
      parentConstant retentionConstant clusterConstant D
      metricExponent propositionExponent coverExponent : ℝ)
    (centers : ℕ)
    (hdelta : 0 < delta)
    (hparentScale : 0 ≤ parentScale)
    (hretentionInverse : 0 ≤ retentionInverse)
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
      retentionInverse ≤ retentionConstant *
        Real.rpow delta
          (-(metricExponent + metricExponent ^ 2)))
    (hA_bound :
      A ≤ clusterConstant *
        Real.rpow delta
          (-(metricExponent + metricExponent ^ 2)))
    (hcenters :
      (centers : ℝ) ≤
        D * Real.rpow (48 * A) coverExponent)
    (hordinaryBound :
      ordinaryLoss ≤
        Real.rpow delta
          (-faithfulCanonicalOrdinaryLoss metricExponent)) :
    ordinaryLoss *
          Real.rpow parentScale (3 / 4 : ℝ) *
          retentionInverse *
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
  have hparentPower :=
    rpow_polynomial_upper_bound
      parentScale parentConstant delta
      (faithfulCanonicalParentScaleLoss metricExponent)
      (3 / 4 : ℝ)
      hparentScale hparentConstant.le hdelta (by norm_num)
      hparentBound
  have hcluster :=
    canonical_cluster_and_cover_power_le
      delta D A clusterConstant
      (metricExponent + metricExponent ^ 2)
      propositionExponent coverExponent
      hdelta hD hA hclusterConstant
      hpropositionExponent hcoverExponent
      hA_bound centers hcenters
  have hfirst :
      ordinaryLoss * Real.rpow parentScale (3 / 4 : ℝ) ≤
        Real.rpow delta
            (-faithfulCanonicalOrdinaryLoss metricExponent) *
          (Real.rpow parentConstant (3 / 4 : ℝ) *
            Real.rpow delta
              (-(faithfulCanonicalParentScaleLoss metricExponent *
                (3 / 4 : ℝ)))) := by
    exact mul_le_mul hordinaryBound hparentPower
      (Real.rpow_nonneg hparentScale _)
      (Real.rpow_nonneg hdelta.le _)
  have hsecond :
      ordinaryLoss * Real.rpow parentScale (3 / 4 : ℝ) *
          retentionInverse ≤
        (Real.rpow delta
              (-faithfulCanonicalOrdinaryLoss metricExponent) *
            (Real.rpow parentConstant (3 / 4 : ℝ) *
              Real.rpow delta
                (-(faithfulCanonicalParentScaleLoss metricExponent *
                  (3 / 4 : ℝ))))) *
          (retentionConstant *
            Real.rpow delta
              (-(metricExponent + metricExponent ^ 2))) := by
    exact mul_le_mul hfirst hretentionBound
      hretentionInverse
      (mul_nonneg
        (Real.rpow_nonneg hdelta.le _)
        (mul_nonneg
          (Real.rpow_nonneg hparentConstant.le _)
          (Real.rpow_nonneg hdelta.le _)))
  have hthird :
      ordinaryLoss * Real.rpow parentScale (3 / 4 : ℝ) *
          retentionInverse *
          (Real.rpow A propositionExponent *
            Real.rpow (centers : ℝ) (7 / 2 : ℝ)) ≤
        ((Real.rpow delta
                (-faithfulCanonicalOrdinaryLoss metricExponent) *
              (Real.rpow parentConstant (3 / 4 : ℝ) *
                Real.rpow delta
                  (-(faithfulCanonicalParentScaleLoss metricExponent *
                    (3 / 4 : ℝ))))) *
            (retentionConstant *
              Real.rpow delta
                (-(metricExponent + metricExponent ^ 2)))) *
          ((Real.rpow clusterConstant propositionExponent *
              Real.rpow
                (D * Real.rpow (48 * clusterConstant) coverExponent)
                (7 / 2 : ℝ)) *
            Real.rpow delta
              (-((propositionExponent +
                    (7 / 2 : ℝ) * coverExponent) *
                  (metricExponent + metricExponent ^ 2)))) := by
    exact mul_le_mul hsecond hcluster
      (mul_nonneg
        (Real.rpow_nonneg hA _)
        (Real.rpow_nonneg (Nat.cast_nonneg centers) _))
      (mul_nonneg
        (mul_nonneg
          (Real.rpow_nonneg hdelta.le _)
          (mul_nonneg
            (Real.rpow_nonneg hparentConstant.le _)
            (Real.rpow_nonneg hdelta.le _)))
        (mul_nonneg hretentionConstant.le
          (Real.rpow_nonneg hdelta.le _)))
  have hpowers :
      Real.rpow delta
            (-faithfulCanonicalOrdinaryLoss metricExponent) *
          Real.rpow delta
            (-(faithfulCanonicalParentScaleLoss metricExponent *
              (3 / 4 : ℝ))) *
          Real.rpow delta
            (-(metricExponent + metricExponent ^ 2)) *
          Real.rpow delta
            (-((propositionExponent +
                  (7 / 2 : ℝ) * coverExponent) *
                (metricExponent + metricExponent ^ 2))) =
        Real.rpow delta
          (-(faithfulCanonicalStructuredScaleLoss
                (propositionExponent +
                  (7 / 2 : ℝ) * coverExponent)
                metricExponent +
              faithfulCanonicalOrdinaryLoss metricExponent)) := by
    calc
      Real.rpow delta
            (-faithfulCanonicalOrdinaryLoss metricExponent) *
          Real.rpow delta
            (-(faithfulCanonicalParentScaleLoss metricExponent *
              (3 / 4 : ℝ))) *
          Real.rpow delta
            (-(metricExponent + metricExponent ^ 2)) *
          Real.rpow delta
            (-((propositionExponent +
                  (7 / 2 : ℝ) * coverExponent) *
                (metricExponent + metricExponent ^ 2))) =
        Real.rpow delta
            (-faithfulCanonicalOrdinaryLoss metricExponent +
              -(faithfulCanonicalParentScaleLoss metricExponent *
                (3 / 4 : ℝ))) *
          Real.rpow delta
            (-(metricExponent + metricExponent ^ 2)) *
          Real.rpow delta
            (-((propositionExponent +
                  (7 / 2 : ℝ) * coverExponent) *
                (metricExponent + metricExponent ^ 2))) := by
        apply congrArg
          (fun z : ℝ =>
            z *
              Real.rpow delta
                (-(metricExponent + metricExponent ^ 2)) *
              Real.rpow delta
                (-((propositionExponent +
                      (7 / 2 : ℝ) * coverExponent) *
                    (metricExponent + metricExponent ^ 2))))
        exact
          (Real.rpow_add hdelta
            (-faithfulCanonicalOrdinaryLoss metricExponent)
            (-(faithfulCanonicalParentScaleLoss metricExponent *
              (3 / 4 : ℝ)))).symm
      _ =
        Real.rpow delta
            ((-faithfulCanonicalOrdinaryLoss metricExponent +
                -(faithfulCanonicalParentScaleLoss metricExponent *
                  (3 / 4 : ℝ))) +
              -(metricExponent + metricExponent ^ 2)) *
          Real.rpow delta
            (-((propositionExponent +
                  (7 / 2 : ℝ) * coverExponent) *
                (metricExponent + metricExponent ^ 2))) := by
        apply congrArg
          (fun z : ℝ =>
            z *
              Real.rpow delta
                (-((propositionExponent +
                      (7 / 2 : ℝ) * coverExponent) *
                    (metricExponent + metricExponent ^ 2))))
        exact
          (Real.rpow_add hdelta
            (-faithfulCanonicalOrdinaryLoss metricExponent +
              -(faithfulCanonicalParentScaleLoss metricExponent *
                (3 / 4 : ℝ)))
            (-(metricExponent + metricExponent ^ 2))).symm
      _ =
        Real.rpow delta
          (((-faithfulCanonicalOrdinaryLoss metricExponent +
                -(faithfulCanonicalParentScaleLoss metricExponent *
                  (3 / 4 : ℝ))) +
              -(metricExponent + metricExponent ^ 2)) +
            -((propositionExponent +
                  (7 / 2 : ℝ) * coverExponent) *
                (metricExponent + metricExponent ^ 2))) := by
        exact
          (Real.rpow_add hdelta
            ((-faithfulCanonicalOrdinaryLoss metricExponent +
                -(faithfulCanonicalParentScaleLoss metricExponent *
                  (3 / 4 : ℝ))) +
              -(metricExponent + metricExponent ^ 2))
            (-((propositionExponent +
                  (7 / 2 : ℝ) * coverExponent) *
                (metricExponent + metricExponent ^ 2)))).symm
      _ =
        Real.rpow delta
          (-(faithfulCanonicalStructuredScaleLoss
                (propositionExponent +
                  (7 / 2 : ℝ) * coverExponent)
                metricExponent +
              faithfulCanonicalOrdinaryLoss metricExponent)) := by
        congr 1
        dsimp only [faithfulCanonicalStructuredScaleLoss]
        ring
  calc
    ordinaryLoss *
          Real.rpow parentScale (3 / 4 : ℝ) *
          retentionInverse *
          (Real.rpow A propositionExponent *
            Real.rpow (centers : ℝ) (7 / 2 : ℝ)) ≤
        ((Real.rpow delta
                (-faithfulCanonicalOrdinaryLoss metricExponent) *
              (Real.rpow parentConstant (3 / 4 : ℝ) *
                Real.rpow delta
                  (-(faithfulCanonicalParentScaleLoss metricExponent *
                    (3 / 4 : ℝ))))) *
            (retentionConstant *
              Real.rpow delta
                (-(metricExponent + metricExponent ^ 2)))) *
          ((Real.rpow clusterConstant propositionExponent *
              Real.rpow
                (D * Real.rpow (48 * clusterConstant) coverExponent)
                (7 / 2 : ℝ)) *
            Real.rpow delta
              (-((propositionExponent +
                    (7 / 2 : ℝ) * coverExponent) *
                  (metricExponent + metricExponent ^ 2)))) :=
      hthird
    _ =
      faithfulCanonicalFinalCoefficientConstant
          parentConstant retentionConstant clusterConstant D
          propositionExponent coverExponent *
        Real.rpow delta
          (-(faithfulCanonicalStructuredScaleLoss
                (propositionExponent +
                  (7 / 2 : ℝ) * coverExponent)
                metricExponent +
              faithfulCanonicalOrdinaryLoss metricExponent)) := by
      rw [← hpowers]
      dsimp only [faithfulCanonicalFinalCoefficientConstant]
      ring

end Kakeya.Cinematic
