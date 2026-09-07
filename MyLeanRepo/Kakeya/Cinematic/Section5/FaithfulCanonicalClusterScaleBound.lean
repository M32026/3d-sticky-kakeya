import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalParentScaleBound
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedPaperClusterScale
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedSupportTangentBallCover

/-!
# Polynomial bounds for the faithful canonical cluster scale

This module bounds the paper cluster parameter and the combined powers of
that parameter and the tangent-ball cover cardinality. For internal metric
exponent `a`, both losses are controlled by `a + a^2`.
-/

namespace Kakeya.Cinematic

noncomputable def faithfulCanonicalClusterConstant
    (T C_R metricExponent : ℝ) : ℝ :=
  22 * C_R *
    Real.rpow
      (96 *
        Real.rpow (2 * T) (metricExponent ^ 2))
      (1 / metricExponent)

lemma canonical_cluster_base_le
    (delta t Delta T heavyLogLoss metricExponent : ℝ)
    (hdelta : 0 < delta)
    (hDelta : 0 < Delta)
    (hT : 0 < T)
    (hdeltaDelta : delta ≤ Delta)
    (hDeltaT : Delta ≤ t)
    (htT : t ≤ T)
    (hlogLoss :
      heavyLogLoss ≤
        Real.rpow delta (-(metricExponent ^ 3))) :
    24 * heavyLogLoss *
          (4 *
            Real.rpow (2 * t / Delta)
              (metricExponent ^ 2)) ≤
      (96 *
          Real.rpow (2 * T)
            (metricExponent ^ 2)) *
        Real.rpow delta
          (-(metricExponent ^ 3 +
            metricExponent ^ 2)) := by
  have ht : 0 < t := hDelta.trans_le hDeltaT
  have hfiber :=
    canonical_fiber_ratio_le
      delta t Delta T metricExponent
      hdelta hDelta hT hdeltaDelta hDeltaT htT
  have hfiberNonneg :
      0 ≤
        4 *
          Real.rpow (2 * t / Delta)
            (metricExponent ^ 2) := by
    exact mul_nonneg (by norm_num)
      (Real.rpow_nonneg (by positivity) _)
  have hproduct :
      heavyLogLoss *
          (4 *
            Real.rpow (2 * t / Delta)
              (metricExponent ^ 2)) ≤
        Real.rpow delta (-(metricExponent ^ 3)) *
          ((4 *
              Real.rpow (2 * T)
                (metricExponent ^ 2)) *
            Real.rpow delta
              (-(metricExponent ^ 2))) :=
    mul_le_mul hlogLoss hfiber hfiberNonneg
      (Real.rpow_nonneg hdelta.le _)
  have hpowers :
      Real.rpow delta (-(metricExponent ^ 3)) *
          Real.rpow delta (-(metricExponent ^ 2)) =
        Real.rpow delta
          (-(metricExponent ^ 3 +
            metricExponent ^ 2)) := by
    calc
      Real.rpow delta (-(metricExponent ^ 3)) *
            Real.rpow delta (-(metricExponent ^ 2)) =
          Real.rpow delta
            (-(metricExponent ^ 3) +
              -(metricExponent ^ 2)) :=
        (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta
            (-(metricExponent ^ 3 +
              metricExponent ^ 2)) := by
        congr 1
        ring
  have hscaled :=
    mul_le_mul_of_nonneg_left hproduct
      (show (0 : ℝ) ≤ 24 by norm_num)
  calc
    24 * heavyLogLoss *
          (4 *
            Real.rpow (2 * t / Delta)
              (metricExponent ^ 2)) ≤
      24 *
        (Real.rpow delta (-(metricExponent ^ 3)) *
          ((4 *
              Real.rpow (2 * T)
                (metricExponent ^ 2)) *
            Real.rpow delta
              (-(metricExponent ^ 2)))) := by
      simpa only [mul_assoc] using hscaled
    _ =
      (96 *
          Real.rpow (2 * T)
            (metricExponent ^ 2)) *
        Real.rpow delta
          (-(metricExponent ^ 3 +
            metricExponent ^ 2)) := by
      rw [← hpowers]
      ring

lemma canonical_paper_cluster_parameter_le
    (delta t Delta T C_R heavyLogLoss metricExponent : ℝ)
    (hdelta : 0 < delta)
    (hDelta : 0 < Delta)
    (hT : 0 < T)
    (hC_R : 0 < C_R)
    (hH : 0 < heavyLogLoss)
    (hmetric : 0 < metricExponent)
    (hdeltaDelta : delta ≤ Delta)
    (hDeltaT : Delta ≤ t)
    (htT : t ≤ T)
    (hlogLoss :
      heavyLogLoss ≤
        Real.rpow delta (-(metricExponent ^ 3))) :
    ambientRestrictedPaperClusterParameter
        C_R t metricExponent heavyLogLoss
          (4 *
            Real.rpow (2 * t / Delta)
              (metricExponent ^ 2)) ≤
      faithfulCanonicalClusterConstant
          T C_R metricExponent *
        Real.rpow delta
          (-(metricExponent + metricExponent ^ 2)) := by
  let fiberRatio : ℝ :=
    4 *
      Real.rpow (2 * t / Delta)
        (metricExponent ^ 2)
  let baseConstant : ℝ :=
    96 *
      Real.rpow (2 * T)
        (metricExponent ^ 2)
  have ht : 0 < t := hDelta.trans_le hDeltaT
  have hfiberRatio : 0 < fiberRatio := by
    dsimp only [fiberRatio]
    exact mul_pos (by norm_num)
      (Real.rpow_pos_of_pos (by positivity) _)
  have hbaseConstant : 0 < baseConstant := by
    dsimp only [baseConstant]
    exact mul_pos (by norm_num)
      (Real.rpow_pos_of_pos (mul_pos (by norm_num) hT) _)
  have hbase :
      24 * heavyLogLoss * fiberRatio ≤
        baseConstant *
          Real.rpow delta
            (-(metricExponent ^ 3 +
              metricExponent ^ 2)) := by
    dsimp only [fiberRatio, baseConstant]
    exact canonical_cluster_base_le
      delta t Delta T heavyLogLoss metricExponent
      hdelta hDelta hT hdeltaDelta hDeltaT htT
      hlogLoss
  have hpower :=
    rpow_polynomial_upper_bound
      (24 * heavyLogLoss * fiberRatio)
      baseConstant delta
      (metricExponent ^ 3 + metricExponent ^ 2)
      (1 / metricExponent)
      (by positivity) hbaseConstant.le hdelta
      (by positivity) hbase
  have hexponent :
      (metricExponent ^ 3 + metricExponent ^ 2) *
          (1 / metricExponent) =
        metricExponent + metricExponent ^ 2 := by
    field_simp [hmetric.ne']
    ring
  rw [ambientRestrictedPaperClusterParameter_eq
    C_R t metricExponent heavyLogLoss fiberRatio
    ht hmetric hH hfiberRatio]
  have hscaled :=
    mul_le_mul_of_nonneg_left hpower
      (mul_nonneg hC_R.le (show (0 : ℝ) ≤ 22 by norm_num))
  dsimp only [faithfulCanonicalClusterConstant]
  dsimp only [baseConstant] at hscaled
  rw [hexponent] at hscaled
  simpa only [mul_assoc, mul_left_comm, mul_comm, fiberRatio]
    using hscaled

lemma canonical_cluster_cover_power_le
    (delta D A clusterConstant branchExponent coverExponent : ℝ)
    (hdelta : 0 < delta)
    (hD : 0 < D)
    (hA : 0 ≤ A)
    (hclusterConstant : 0 < clusterConstant)
    (hcoverExponent : 0 ≤ coverExponent)
    (hA_bound :
      A ≤ clusterConstant *
        Real.rpow delta (-branchExponent))
    (centers : ℕ)
    (hcenters :
      (centers : ℝ) ≤
        D *
          Real.rpow (48 * A) coverExponent) :
    Real.rpow (centers : ℝ) (7 / 2 : ℝ) ≤
      Real.rpow
          (D *
            Real.rpow (48 * clusterConstant)
              coverExponent)
          (7 / 2 : ℝ) *
        Real.rpow delta
          (-((7 / 2 : ℝ) *
            coverExponent * branchExponent)) := by
  have hA48 :
      48 * A ≤
        (48 * clusterConstant) *
          Real.rpow delta (-branchExponent) := by
    calc
      48 * A ≤
          48 *
            (clusterConstant *
              Real.rpow delta (-branchExponent)) :=
        mul_le_mul_of_nonneg_left hA_bound
          (show (0 : ℝ) ≤ 48 by norm_num)
      _ =
          (48 * clusterConstant) *
            Real.rpow delta (-branchExponent) := by ring
  have hA48Nonneg : 0 ≤ 48 * A := by positivity
  have hcover :=
    rpow_polynomial_upper_bound
      (48 * A) (48 * clusterConstant) delta
      branchExponent coverExponent
      hA48Nonneg (by positivity) hdelta
      hcoverExponent hA48
  have hcentersBound :
      (centers : ℝ) ≤
        (D *
          Real.rpow (48 * clusterConstant)
            coverExponent) *
          Real.rpow delta
            (-(branchExponent * coverExponent)) := by
    calc
      (centers : ℝ) ≤
          D * Real.rpow (48 * A) coverExponent :=
        hcenters
      _ ≤
          D *
            (Real.rpow (48 * clusterConstant) coverExponent *
              Real.rpow delta
                (-(branchExponent * coverExponent))) := by
        exact mul_le_mul_of_nonneg_left hcover hD.le
      _ =
          (D *
            Real.rpow (48 * clusterConstant)
              coverExponent) *
            Real.rpow delta
              (-(branchExponent * coverExponent)) := by ring
  have hfinal :=
    rpow_polynomial_upper_bound
      (centers : ℝ)
      (D *
        Real.rpow (48 * clusterConstant)
          coverExponent)
      delta (branchExponent * coverExponent)
      (7 / 2 : ℝ)
      (Nat.cast_nonneg centers)
      (mul_nonneg hD.le
        (Real.rpow_nonneg
          (mul_nonneg (by norm_num) hclusterConstant.le) _))
      hdelta
      (by norm_num) hcentersBound
  convert hfinal using 1
  ring_nf

lemma canonical_cluster_cover_card_le
    (delta D A clusterConstant branchExponent coverExponent : ℝ)
    (hdelta : 0 < delta)
    (hD : 0 < D)
    (hA : 0 ≤ A)
    (hclusterConstant : 0 < clusterConstant)
    (hcoverExponent : 0 ≤ coverExponent)
    (hA_bound :
      A ≤ clusterConstant *
        Real.rpow delta (-branchExponent))
    (centers : ℕ)
    (hcenters :
      (centers : ℝ) ≤
        D *
          Real.rpow (48 * A) coverExponent) :
    (centers : ℝ) ≤
      (D *
        Real.rpow (48 * clusterConstant)
          coverExponent) *
        Real.rpow delta
          (-(branchExponent * coverExponent)) := by
  have hA48 :
      48 * A ≤
        (48 * clusterConstant) *
          Real.rpow delta (-branchExponent) := by
    calc
      48 * A ≤
          48 *
            (clusterConstant *
              Real.rpow delta (-branchExponent)) :=
        mul_le_mul_of_nonneg_left hA_bound
          (show (0 : ℝ) ≤ 48 by norm_num)
      _ =
          (48 * clusterConstant) *
            Real.rpow delta (-branchExponent) := by ring
  have hA48Nonneg : 0 ≤ 48 * A := by positivity
  have hcover :=
    rpow_polynomial_upper_bound
      (48 * A) (48 * clusterConstant) delta
      branchExponent coverExponent
      hA48Nonneg (by positivity) hdelta
      hcoverExponent hA48
  have hcentersBound :
      (centers : ℝ) ≤
        (D *
          Real.rpow (48 * clusterConstant)
            coverExponent) *
          Real.rpow delta
            (-(branchExponent * coverExponent)) := by
    calc
      (centers : ℝ) ≤
          D * Real.rpow (48 * A) coverExponent :=
        hcenters
      _ ≤
          D *
            (Real.rpow (48 * clusterConstant) coverExponent *
              Real.rpow delta
                (-(branchExponent * coverExponent))) := by
        exact mul_le_mul_of_nonneg_left hcover hD.le
      _ =
          (D *
            Real.rpow (48 * clusterConstant)
              coverExponent) *
            Real.rpow delta
              (-(branchExponent * coverExponent)) := by ring
  exact hcentersBound

lemma canonical_cluster_and_cover_power_le
    (delta D A clusterConstant branchExponent
      propositionExponent coverExponent : ℝ)
    (hdelta : 0 < delta)
    (hD : 0 < D)
    (hA : 0 ≤ A)
    (hclusterConstant : 0 < clusterConstant)
    (hpropositionExponent : 0 ≤ propositionExponent)
    (hcoverExponent : 0 ≤ coverExponent)
    (hA_bound :
      A ≤ clusterConstant *
        Real.rpow delta (-branchExponent))
    (centers : ℕ)
    (hcenters :
      (centers : ℝ) ≤
        D *
          Real.rpow (48 * A) coverExponent) :
    Real.rpow A propositionExponent *
        Real.rpow (centers : ℝ) (7 / 2 : ℝ) ≤
      (Real.rpow clusterConstant propositionExponent *
        Real.rpow
          (D *
            Real.rpow (48 * clusterConstant)
              coverExponent)
          (7 / 2 : ℝ)) *
        Real.rpow delta
          (-((propositionExponent +
              (7 / 2 : ℝ) * coverExponent) *
            branchExponent)) := by
  have hA_power :=
    rpow_polynomial_upper_bound
      A clusterConstant delta branchExponent
      propositionExponent hA hclusterConstant.le hdelta
      hpropositionExponent hA_bound
  have hcenters_power :=
    canonical_cluster_cover_power_le
      delta D A clusterConstant branchExponent coverExponent
      hdelta hD hA hclusterConstant
      hcoverExponent hA_bound centers hcenters
  have hproduct :=
    mul_le_mul hA_power hcenters_power
      (Real.rpow_nonneg (by positivity) _)
      (mul_nonneg
        (Real.rpow_nonneg hclusterConstant.le _)
        (Real.rpow_nonneg hdelta.le _))
  have hpowers :
      Real.rpow delta
            (-(branchExponent * propositionExponent)) *
          Real.rpow delta
            (-((7 / 2 : ℝ) *
              coverExponent * branchExponent)) =
        Real.rpow delta
          (-((propositionExponent +
              (7 / 2 : ℝ) * coverExponent) *
            branchExponent)) := by
    calc
      Real.rpow delta
            (-(branchExponent * propositionExponent)) *
          Real.rpow delta
            (-((7 / 2 : ℝ) *
              coverExponent * branchExponent)) =
        Real.rpow delta
          (-(branchExponent * propositionExponent) +
            -((7 / 2 : ℝ) *
              coverExponent * branchExponent)) :=
        (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta
          (-((propositionExponent +
              (7 / 2 : ℝ) * coverExponent) *
            branchExponent)) := by
        congr 1
        ring
  calc
    Real.rpow A propositionExponent *
        Real.rpow (centers : ℝ) (7 / 2 : ℝ) ≤
      (Real.rpow clusterConstant propositionExponent *
          Real.rpow delta
            (-(branchExponent * propositionExponent))) *
        (Real.rpow
            (D *
              Real.rpow (48 * clusterConstant)
                coverExponent)
            (7 / 2 : ℝ) *
          Real.rpow delta
            (-((7 / 2 : ℝ) *
              coverExponent * branchExponent))) :=
      hproduct
    _ =
      (Real.rpow clusterConstant propositionExponent *
        Real.rpow
          (D *
            Real.rpow (48 * clusterConstant)
              coverExponent)
          (7 / 2 : ℝ)) *
        Real.rpow delta
          (-((propositionExponent +
              (7 / 2 : ℝ) * coverExponent) *
            branchExponent)) := by
      rw [← hpowers]
      ring

end Kakeya.Cinematic
