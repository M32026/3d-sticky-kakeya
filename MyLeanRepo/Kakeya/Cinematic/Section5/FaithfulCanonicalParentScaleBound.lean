import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalRetentionBound

/-!
# Polynomial bound for the faithful canonical parent scale

This module combines the canonical cutoff incidence bound, three copies of
the heavy logarithmic loss, and the inverse-cube retention bound occurring in
`ambientRestrictedParentTangencyScale`.

For internal metric exponent `a`, the resulting parent tangency scale loses

`4 * a + (7 / 2) * a^2 + 3 * a^3`.
-/

namespace Kakeya.Cinematic

noncomputable def faithfulCanonicalIncidenceConstant
    (T C_R C_inc metricExponent : ℝ) : ℝ :=
  C_inc *
      Real.sqrt
        (32 * C_R *
          Real.rpow
            (96 *
              Real.rpow (2 * T)
                (metricExponent ^ 2))
            (1 / metricExponent) *
          Real.rpow 24
            (1 / (metricExponent ^ 2))) +
    1

noncomputable def faithfulCanonicalRetentionConstant
    (diameter T metricExponent : ℝ) : ℝ :=
  Real.rpow (8 * diameter) (3 * metricExponent) *
    Real.rpow (2 * T) (3 * metricExponent ^ 2)

noncomputable def faithfulCanonicalParentScaleConstant
    (diameter T C_R C_inc metricExponent : ℝ) : ℝ :=
  165888 *
    faithfulCanonicalIncidenceConstant
      T C_R C_inc metricExponent *
    faithfulCanonicalRetentionConstant
      diameter T metricExponent

noncomputable def faithfulCanonicalParentScaleLoss
    (metricExponent : ℝ) : ℝ :=
  4 * metricExponent +
    (7 / 2 : ℝ) * metricExponent ^ 2 +
    3 * metricExponent ^ 3

lemma heavy_log_cube_le
    (delta heavyLogLoss metricExponent : ℝ)
    (hdelta : 0 < delta)
    (hH : 0 ≤ heavyLogLoss)
    (hlogLoss :
      heavyLogLoss ≤
        Real.rpow delta (-(metricExponent ^ 3))) :
    heavyLogLoss ^ 3 ≤
      Real.rpow delta (-(3 * metricExponent ^ 3)) := by
  have hcube :
      heavyLogLoss ^ 3 ≤
        (Real.rpow delta (-(metricExponent ^ 3))) ^ 3 := by
    gcongr
  have hpower :
      (Real.rpow delta (-(metricExponent ^ 3))) ^ 3 =
        Real.rpow delta (-(3 * metricExponent ^ 3)) := by
    calc
      (Real.rpow delta (-(metricExponent ^ 3))) ^ 3 =
          Real.rpow
            (Real.rpow delta (-(metricExponent ^ 3)))
            (3 : ℝ) := by
        exact
          (Real.rpow_natCast
            (Real.rpow delta (-(metricExponent ^ 3))) 3).symm
      _ =
          Real.rpow delta
            (-(metricExponent ^ 3) * 3) := by
        exact
          (Real.rpow_mul hdelta.le
            (-(metricExponent ^ 3)) 3).symm
      _ =
          Real.rpow delta
            (-(3 * metricExponent ^ 3)) := by
        congr 1
        ring
  exact hcube.trans_eq hpower

lemma canonical_parent_tangency_scale_le
    (delta t Delta diameter T C_R C_inc heavyLogLoss
      metricExponent : ℝ)
    (degreeLoss : ℕ)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hDelta : 0 < Delta)
    (hdiameter : 0 < diameter)
    (hT : 0 < T)
    (hC_R : 0 < C_R)
    (hC_inc : 0 < C_inc)
    (hH : 0 < heavyLogLoss)
    (hmetric : 0 < metricExponent)
    (hdeltaDelta : delta ≤ Delta)
    (hDeltaT : Delta ≤ t)
    (htT : t ≤ T)
    (hdegreeLoss : (degreeLoss : ℝ) ≤ heavyLogLoss)
    (hlogLoss :
      heavyLogLoss ≤
        Real.rpow delta (-(metricExponent ^ 3))) :
    ambientRestrictedParentTangencyScale
        (C_inc *
              Real.sqrt
                (delta * (C_R * t * Delta / delta) /
                  ((selectedIncidenceMetricCut
                          heavyLogLoss
                          (4 *
                            Real.rpow (2 * t / Delta)
                              (metricExponent ^ 2))
                          metricExponent *
                        t / 8) *
                    (selectedIncidenceTangencyCut
                          heavyLogLoss (metricExponent ^ 2) *
                        Delta / 2))) +
            1)
        4 degreeLoss heavyLogLoss
        (Real.rpow (t / (8 * diameter)) metricExponent *
          Real.rpow (Delta / (2 * t)) (metricExponent ^ 2)) ≤
      faithfulCanonicalParentScaleConstant
          diameter T C_R C_inc metricExponent *
        Real.rpow delta
          (-faithfulCanonicalParentScaleLoss metricExponent) := by
  let incidenceScale : ℝ :=
    C_inc *
          Real.sqrt
            (delta * (C_R * t * Delta / delta) /
              ((selectedIncidenceMetricCut
                      heavyLogLoss
                      (4 *
                        Real.rpow (2 * t / Delta)
                          (metricExponent ^ 2))
                      metricExponent *
                    t / 8) *
                (selectedIncidenceTangencyCut
                      heavyLogLoss (metricExponent ^ 2) *
                    Delta / 2))) +
      1
  let incidenceConstant : ℝ :=
    faithfulCanonicalIncidenceConstant
      T C_R C_inc metricExponent
  let retention : ℝ :=
    Real.rpow (t / (8 * diameter)) metricExponent *
      Real.rpow (Delta / (2 * t)) (metricExponent ^ 2)
  let retentionConstant : ℝ :=
    faithfulCanonicalRetentionConstant
      diameter T metricExponent
  let incidenceLoss : ℝ :=
    metricExponent + metricExponent ^ 2 / 2
  let retentionLoss : ℝ :=
    3 * metricExponent + 3 * metricExponent ^ 2
  let logLoss : ℝ := 3 * metricExponent ^ 3
  have hincidenceConstant : 0 < incidenceConstant := by
    dsimp only [incidenceConstant,
      faithfulCanonicalIncidenceConstant]
    positivity
  have hretentionConstant : 0 < retentionConstant := by
    dsimp only [retentionConstant,
      faithfulCanonicalRetentionConstant]
    exact mul_pos
      (Real.rpow_pos_of_pos
        (mul_pos (by norm_num) hdiameter) _)
      (Real.rpow_pos_of_pos
        (mul_pos (by norm_num) hT) _)
  have hincidence :
      incidenceScale ≤
        incidenceConstant *
          Real.rpow delta (-incidenceLoss) := by
    dsimp only [incidenceScale, incidenceConstant,
      incidenceLoss, faithfulCanonicalIncidenceConstant]
    exact canonical_representative_incidence_scale_le
      delta t Delta T C_R C_inc heavyLogLoss metricExponent
      hdelta hdeltaOne hDelta hT hC_R hC_inc hH hmetric
      hdeltaDelta hDeltaT htT hlogLoss
  have hretention :
      Real.rpow retention (-3) ≤
        retentionConstant *
          Real.rpow delta (-retentionLoss) := by
    dsimp only [retention, retentionConstant, retentionLoss,
      faithfulCanonicalRetentionConstant]
    exact canonical_retention_inv_cube_le
      delta t Delta diameter T metricExponent
      hdelta hdiameter hT hmetric.le hdeltaDelta hDeltaT htT
  have hlog :
      heavyLogLoss ^ 3 ≤
        Real.rpow delta (-logLoss) := by
    dsimp only [logLoss]
    exact heavy_log_cube_le
      delta heavyLogLoss metricExponent hdelta hH.le hlogLoss
  have hdegree :
      (2 * (degreeLoss : ℝ)) * heavyLogLoss ^ 2 ≤
        2 * heavyLogLoss ^ 3 := by
    nlinarith [sq_nonneg heavyLogLoss]
  have hraw :
      ambientRestrictedParentTangencyScale
          incidenceScale 4 degreeLoss heavyLogLoss retention ≤
        165888 * incidenceScale *
          heavyLogLoss ^ 3 *
          Real.rpow retention (-3) := by
    dsimp only [ambientRestrictedParentTangencyScale]
    have hincidenceNonneg : 0 ≤ incidenceScale := by
      dsimp only [incidenceScale]
      positivity
    have hretentionPos : 0 < retention := by
      have ht : 0 < t :=
        hdelta.trans_le (hdeltaDelta.trans hDeltaT)
      have hDeltaPos : 0 < Delta :=
        hdelta.trans_le hdeltaDelta
      dsimp only [retention]
      exact mul_pos
        (Real.rpow_pos_of_pos (by positivity) _)
        (Real.rpow_pos_of_pos (by positivity) _)
    have hretentionPower :
        0 ≤ Real.rpow retention (-3) := by
      exact Real.rpow_nonneg hretentionPos.le _
    have hprefix :
        0 ≤ 5184 * (4 * incidenceScale) * 4 := by
      positivity
    calc
      5184 * (4 * incidenceScale) * 4 *
            (2 * (degreeLoss : ℝ)) *
            heavyLogLoss ^ 2 *
            Real.rpow retention (-3) =
          (5184 * (4 * incidenceScale) * 4) *
            ((2 * (degreeLoss : ℝ)) * heavyLogLoss ^ 2) *
            Real.rpow retention (-3) := by ring
      _ ≤
          (5184 * (4 * incidenceScale) * 4) *
            (2 * heavyLogLoss ^ 3) *
            Real.rpow retention (-3) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdegree hprefix)
          hretentionPower
      _ =
          165888 * incidenceScale *
            heavyLogLoss ^ 3 *
            Real.rpow retention (-3) := by ring
  have hproduct :
      incidenceScale * heavyLogLoss ^ 3 *
          Real.rpow retention (-3) ≤
        (incidenceConstant * Real.rpow delta (-incidenceLoss)) *
          Real.rpow delta (-logLoss) *
          (retentionConstant *
            Real.rpow delta (-retentionLoss)) := by
    have hretentionPos : 0 < retention := by
      have ht : 0 < t :=
        hdelta.trans_le (hdeltaDelta.trans hDeltaT)
      have hDeltaPos : 0 < Delta :=
        hdelta.trans_le hdeltaDelta
      dsimp only [retention]
      exact mul_pos
        (Real.rpow_pos_of_pos (by positivity) _)
        (Real.rpow_pos_of_pos (by positivity) _)
    have hfirst :
        incidenceScale * heavyLogLoss ^ 3 ≤
          (incidenceConstant * Real.rpow delta (-incidenceLoss)) *
            Real.rpow delta (-logLoss) :=
      mul_le_mul hincidence hlog
        (pow_nonneg hH.le 3)
        (mul_nonneg hincidenceConstant.le
          (Real.rpow_nonneg hdelta.le _))
    have hfirstUpperNonneg :
        0 ≤
          (incidenceConstant *
              Real.rpow delta (-incidenceLoss)) *
            Real.rpow delta (-logLoss) := by
      exact mul_nonneg
        (mul_nonneg hincidenceConstant.le
          (Real.rpow_nonneg hdelta.le _))
        (Real.rpow_nonneg hdelta.le _)
    exact mul_le_mul hfirst hretention
      (Real.rpow_nonneg hretentionPos.le _)
      hfirstUpperNonneg
  have hpowers :
      Real.rpow delta (-incidenceLoss) *
          Real.rpow delta (-logLoss) *
          Real.rpow delta (-retentionLoss) =
        Real.rpow delta
          (-(incidenceLoss + logLoss + retentionLoss)) := by
    calc
      Real.rpow delta (-incidenceLoss) *
            Real.rpow delta (-logLoss) *
            Real.rpow delta (-retentionLoss) =
          Real.rpow delta
              (-incidenceLoss + -logLoss) *
            Real.rpow delta (-retentionLoss) := by
        exact congrArg
          (fun z : ℝ =>
            z * Real.rpow delta (-retentionLoss))
          (Real.rpow_add hdelta
            (-incidenceLoss) (-logLoss)).symm
      _ = Real.rpow delta
            ((-incidenceLoss + -logLoss) +
              -retentionLoss) := by
        exact
          (Real.rpow_add hdelta
            (-incidenceLoss + -logLoss)
            (-retentionLoss)).symm
      _ = Real.rpow delta
            (-(incidenceLoss + logLoss + retentionLoss)) := by
        congr 1
        ring
  have hloss :
      incidenceLoss + logLoss + retentionLoss =
        faithfulCanonicalParentScaleLoss metricExponent := by
    dsimp only [incidenceLoss, logLoss, retentionLoss,
      faithfulCanonicalParentScaleLoss]
    ring
  calc
    ambientRestrictedParentTangencyScale
        incidenceScale 4 degreeLoss heavyLogLoss retention ≤
      165888 * incidenceScale *
        heavyLogLoss ^ 3 *
        Real.rpow retention (-3) := hraw
    _ ≤
      165888 *
        ((incidenceConstant * Real.rpow delta (-incidenceLoss)) *
          Real.rpow delta (-logLoss) *
          (retentionConstant *
            Real.rpow delta (-retentionLoss))) := by
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hproduct
          (show (0 : ℝ) ≤ 165888 by norm_num))
    _ =
      faithfulCanonicalParentScaleConstant
          diameter T C_R C_inc metricExponent *
        Real.rpow delta
          (-faithfulCanonicalParentScaleLoss metricExponent) := by
      dsimp only [faithfulCanonicalParentScaleConstant,
        incidenceConstant, retentionConstant]
      rw [← hloss, ← hpowers]
      ring

end Kakeya.Cinematic
