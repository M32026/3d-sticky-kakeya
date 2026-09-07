import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedCutoffParentTangencyScale

/-!
# Polynomial bound for the faithful canonical cutoffs

The selected metric and tangency cutoffs contain negative powers of the
dyadic logarithmic loss.  This module converts their exact definitions into
one polynomial bound at the physical scale.

If the internal metric exponent is `a`, the tangency exponent is `a^2`, and
the heavy logarithmic loss is bounded by `delta^(-a^3)`, then the inverse
cutoff product loses `delta^(-(2a + a^2))`.  Consequently the canonical
incidence scale, after its square root, loses only
`delta^(-(a + a^2 / 2))`.
-/

namespace Kakeya.Cinematic

lemma selectedIncidence_cutoff_product_inv_eq
    (heavyLogLoss fiberRatio epsilon eta : ℝ)
    (hH : 0 < heavyLogLoss)
    (hF : 0 < fiberRatio) :
    (selectedIncidenceMetricCut
          heavyLogLoss fiberRatio epsilon *
        selectedIncidenceTangencyCut heavyLogLoss eta)⁻¹ =
      2 *
          Real.rpow
            (24 * heavyLogLoss * fiberRatio)
            (1 / epsilon) *
        Real.rpow (24 * heavyLogLoss) (1 / eta) := by
  have hx : 0 < 24 * heavyLogLoss * fiberRatio := by positivity
  have hy : 0 < 24 * heavyLogLoss := by positivity
  have hmetric :
      (Real.rpow
          (1 / (24 * heavyLogLoss * fiberRatio))
          (1 / epsilon))⁻¹ =
        Real.rpow
          (24 * heavyLogLoss * fiberRatio)
          (1 / epsilon) := by
    rw [one_div]
    calc
      (Real.rpow
          (24 * heavyLogLoss * fiberRatio)⁻¹
          (1 / epsilon))⁻¹ =
          ((Real.rpow
            (24 * heavyLogLoss * fiberRatio)
            (1 / epsilon))⁻¹)⁻¹ := by
        exact congrArg (fun z : ℝ => z⁻¹)
          (Real.inv_rpow hx.le (1 / epsilon))
      _ = Real.rpow
          (24 * heavyLogLoss * fiberRatio)
          (1 / epsilon) := inv_inv _
  have htangency :
      (Real.rpow
          (1 / (24 * heavyLogLoss))
          (1 / eta))⁻¹ =
        Real.rpow (24 * heavyLogLoss) (1 / eta) := by
    rw [one_div]
    calc
      (Real.rpow
          (24 * heavyLogLoss)⁻¹
          (1 / eta))⁻¹ =
          ((Real.rpow
            (24 * heavyLogLoss)
            (1 / eta))⁻¹)⁻¹ := by
        exact congrArg (fun z : ℝ => z⁻¹)
          (Real.inv_rpow hy.le (1 / eta))
      _ = Real.rpow
          (24 * heavyLogLoss)
          (1 / eta) := inv_inv _
  dsimp only [selectedIncidenceMetricCut,
    selectedIncidenceTangencyCut]
  rw [mul_inv_rev, mul_inv_rev, hmetric, htangency]
  norm_num
  ring

lemma canonical_fiber_ratio_le
    (delta t Delta T metricExponent : ℝ)
    (hdelta : 0 < delta)
    (hDelta : 0 < Delta)
    (hT : 0 < T)
    (hdeltaDelta : delta ≤ Delta)
    (hDeltaT : Delta ≤ t)
    (htT : t ≤ T) :
    4 * Real.rpow (2 * t / Delta) (metricExponent ^ 2) ≤
      4 * Real.rpow (2 * T) (metricExponent ^ 2) *
        Real.rpow delta (-(metricExponent ^ 2)) := by
  have hbase :
      2 * t / Delta ≤ 2 * T / delta := by
    apply (div_le_div_iff₀ hDelta hdelta).2
    nlinarith
  have hbase_nonneg : 0 ≤ 2 * t / Delta := by
    have ht : 0 < t := hDelta.trans_le hDeltaT
    positivity
  have hpower :
      Real.rpow (2 * t / Delta) (metricExponent ^ 2) ≤
        Real.rpow (2 * T / delta) (metricExponent ^ 2) :=
    Real.rpow_le_rpow hbase_nonneg hbase (sq_nonneg metricExponent)
  have hdivPower :
      Real.rpow (2 * T / delta) (metricExponent ^ 2) =
        Real.rpow (2 * T) (metricExponent ^ 2) /
          Real.rpow delta (metricExponent ^ 2) :=
    Real.div_rpow (by positivity) hdelta.le _
  have hinversePower :
      (Real.rpow delta (metricExponent ^ 2))⁻¹ =
        Real.rpow delta (-(metricExponent ^ 2)) := by
    exact (Real.rpow_neg hdelta.le _).symm
  calc
    4 * Real.rpow (2 * t / Delta) (metricExponent ^ 2) ≤
        4 * Real.rpow (2 * T / delta) (metricExponent ^ 2) := by
      gcongr
    _ =
        4 * Real.rpow (2 * T) (metricExponent ^ 2) *
          Real.rpow delta (-(metricExponent ^ 2)) := by
      rw [hdivPower]
      rw [div_eq_mul_inv, hinversePower]
      ring

lemma rpow_polynomial_upper_bound
    (source constant delta loss exponent : ℝ)
    (hsource : 0 ≤ source)
    (hconstant : 0 ≤ constant)
    (hdelta : 0 < delta)
    (hexponent : 0 ≤ exponent)
    (hbound :
      source ≤
        constant * Real.rpow delta (-loss)) :
    Real.rpow source exponent ≤
      Real.rpow constant exponent *
        Real.rpow delta (-(loss * exponent)) := by
  calc
    Real.rpow source exponent ≤
        Real.rpow
          (constant * Real.rpow delta (-loss))
          exponent :=
      Real.rpow_le_rpow hsource hbound hexponent
    _ =
        Real.rpow constant exponent *
          Real.rpow (Real.rpow delta (-loss)) exponent := by
      exact Real.mul_rpow hconstant
        (Real.rpow_nonneg hdelta.le _)
    _ =
        Real.rpow constant exponent *
          Real.rpow delta (-(loss * exponent)) := by
      apply congrArg
        (fun z : ℝ => Real.rpow constant exponent * z)
      calc
        Real.rpow (Real.rpow delta (-loss)) exponent =
            Real.rpow delta ((-loss) * exponent) :=
          (Real.rpow_mul hdelta.le (-loss) exponent).symm
        _ = Real.rpow delta (-(loss * exponent)) := by
          congr 1
          ring

lemma canonical_cutoff_product_inv_le
    (delta t Delta T heavyLogLoss metricExponent : ℝ)
    (hdelta : 0 < delta)
    (hDelta : 0 < Delta)
    (hT : 0 < T)
    (hH : 0 < heavyLogLoss)
    (hmetric : 0 < metricExponent)
    (hdeltaDelta : delta ≤ Delta)
    (hDeltaT : Delta ≤ t)
    (htT : t ≤ T)
    (hlogLoss :
      heavyLogLoss ≤
        Real.rpow delta (-(metricExponent ^ 3))) :
    (selectedIncidenceMetricCut
          heavyLogLoss
          (4 *
            Real.rpow (2 * t / Delta)
              (metricExponent ^ 2))
          metricExponent *
        selectedIncidenceTangencyCut
          heavyLogLoss (metricExponent ^ 2))⁻¹ ≤
      (2 *
          Real.rpow
            (96 *
              Real.rpow (2 * T)
                (metricExponent ^ 2))
            (1 / metricExponent) *
          Real.rpow 24
            (1 / (metricExponent ^ 2))) *
        Real.rpow delta
          (-(2 * metricExponent +
            metricExponent ^ 2)) := by
  let fiberRatio :=
    4 *
      Real.rpow (2 * t / Delta)
        (metricExponent ^ 2)
  let fiberConstant :=
    4 *
      Real.rpow (2 * T)
        (metricExponent ^ 2)
  have ht : 0 < t := hDelta.trans_le hDeltaT
  have hfiberRatioPos : 0 < fiberRatio := by
    dsimp only [fiberRatio]
    exact mul_pos (by norm_num)
      (Real.rpow_pos_of_pos
        (div_pos (mul_pos (by norm_num) ht) hDelta) _)
  have hfiberConstantPos : 0 < fiberConstant := by
    dsimp only [fiberConstant]
    exact mul_pos (by norm_num)
      (Real.rpow_pos_of_pos
        (mul_pos (by norm_num) hT) _)
  have hfiber :
      fiberRatio ≤
        fiberConstant *
          Real.rpow delta (-(metricExponent ^ 2)) := by
    dsimp only [fiberRatio, fiberConstant]
    exact canonical_fiber_ratio_le
      delta t Delta T metricExponent hdelta hDelta hT
      hdeltaDelta hDeltaT htT
  have hmetricBase :
      24 * heavyLogLoss * fiberRatio ≤
        (24 * fiberConstant) *
          Real.rpow delta
            (-(metricExponent ^ 3 +
              metricExponent ^ 2)) := by
    have hproduct :
        heavyLogLoss * fiberRatio ≤
          Real.rpow delta (-(metricExponent ^ 3)) *
            (fiberConstant *
              Real.rpow delta (-(metricExponent ^ 2))) :=
      mul_le_mul hlogLoss hfiber hfiberRatioPos.le
        (Real.rpow_nonneg hdelta.le _)
    have hscaled :
        24 * (heavyLogLoss * fiberRatio) ≤
          24 *
            (Real.rpow delta (-(metricExponent ^ 3)) *
              (fiberConstant *
                Real.rpow delta (-(metricExponent ^ 2)))) :=
      mul_le_mul_of_nonneg_left hproduct (by norm_num)
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
    calc
      24 * heavyLogLoss * fiberRatio ≤
          24 *
            Real.rpow delta (-(metricExponent ^ 3)) *
            (fiberConstant *
              Real.rpow delta (-(metricExponent ^ 2))) := by
        simpa only [mul_assoc] using hscaled
      _ =
          (24 * fiberConstant) *
            Real.rpow delta
              (-(metricExponent ^ 3 +
                metricExponent ^ 2)) := by
        rw [← hpowers]
        ring
  have htangencyBase :
      24 * heavyLogLoss ≤
        24 *
          Real.rpow delta (-(metricExponent ^ 3)) := by
    gcongr
  have hmetricPower :=
    rpow_polynomial_upper_bound
      (24 * heavyLogLoss * fiberRatio)
      (24 * fiberConstant) delta
      (metricExponent ^ 3 + metricExponent ^ 2)
      (1 / metricExponent)
      (by positivity) (by positivity) hdelta
      (by positivity) hmetricBase
  have htangencyPower :=
    rpow_polynomial_upper_bound
      (24 * heavyLogLoss) 24 delta
      (metricExponent ^ 3)
      (1 / (metricExponent ^ 2))
      (by positivity) (by norm_num) hdelta
      (by positivity) htangencyBase
  have hexponentMetric :
      (metricExponent ^ 3 + metricExponent ^ 2) *
          (1 / metricExponent) =
        metricExponent ^ 2 + metricExponent := by
    field_simp [hmetric.ne']
  have hexponentTangency :
      metricExponent ^ 3 *
          (1 / (metricExponent ^ 2)) =
        metricExponent := by
    field_simp [hmetric.ne']
  have hpowerProduct :
      Real.rpow delta
            (-((metricExponent ^ 3 +
                metricExponent ^ 2) *
              (1 / metricExponent))) *
          Real.rpow delta
            (-(metricExponent ^ 3 *
              (1 / (metricExponent ^ 2)))) =
        Real.rpow delta
          (-(2 * metricExponent +
            metricExponent ^ 2)) := by
    calc
      Real.rpow delta
            (-((metricExponent ^ 3 +
                metricExponent ^ 2) *
              (1 / metricExponent))) *
          Real.rpow delta
            (-(metricExponent ^ 3 *
              (1 / (metricExponent ^ 2)))) =
        Real.rpow delta
          (-((metricExponent ^ 3 +
                metricExponent ^ 2) *
              (1 / metricExponent)) +
            -(metricExponent ^ 3 *
              (1 / (metricExponent ^ 2)))) :=
        (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta
          (-(2 * metricExponent +
            metricExponent ^ 2)) := by
        rw [hexponentMetric, hexponentTangency]
        congr 1
        ring
  rw [selectedIncidence_cutoff_product_inv_eq
    heavyLogLoss fiberRatio metricExponent
    (metricExponent ^ 2) hH hfiberRatioPos]
  calc
    2 *
          Real.rpow
            (24 * heavyLogLoss * fiberRatio)
            (1 / metricExponent) *
        Real.rpow
          (24 * heavyLogLoss)
          (1 / (metricExponent ^ 2)) ≤
      2 *
          (Real.rpow (24 * fiberConstant)
              (1 / metricExponent) *
            Real.rpow delta
              (-((metricExponent ^ 3 +
                  metricExponent ^ 2) *
                (1 / metricExponent)))) *
        (Real.rpow 24
              (1 / (metricExponent ^ 2)) *
            Real.rpow delta
              (-(metricExponent ^ 3 *
                (1 / (metricExponent ^ 2))))) := by
      have hproduct :=
        mul_le_mul hmetricPower htangencyPower
          (Real.rpow_nonneg (by positivity) _)
          (mul_nonneg
            (Real.rpow_nonneg (by positivity) _)
            (Real.rpow_nonneg hdelta.le _))
      have hscaled :=
        mul_le_mul_of_nonneg_left hproduct
          (show (0 : ℝ) ≤ 2 by norm_num)
      simpa only [mul_assoc] using hscaled
    _ =
      (2 *
          Real.rpow (24 * fiberConstant)
            (1 / metricExponent) *
          Real.rpow 24
            (1 / (metricExponent ^ 2))) *
        Real.rpow delta
          (-(2 * metricExponent +
            metricExponent ^ 2)) := by
      rw [← hpowerProduct]
      ring
    _ =
      (2 *
          Real.rpow
            (96 *
              Real.rpow (2 * T)
                (metricExponent ^ 2))
            (1 / metricExponent) *
          Real.rpow 24
            (1 / (metricExponent ^ 2))) *
        Real.rpow delta
          (-(2 * metricExponent +
            metricExponent ^ 2)) := by
      dsimp only [fiberConstant]
      ring_nf

lemma sqrt_polynomial_upper_bound
    (source constant delta loss : ℝ)
    (hsource : 0 ≤ source)
    (hconstant : 0 ≤ constant)
    (hdelta : 0 < delta)
    (hbound :
      source ≤
        constant * Real.rpow delta (-loss)) :
    Real.sqrt source ≤
      Real.sqrt constant *
        Real.rpow delta (-(loss / 2)) := by
  have hpower :=
    rpow_polynomial_upper_bound
      source constant delta loss (1 / 2 : ℝ)
      hsource hconstant hdelta (by norm_num) hbound
  calc
    Real.sqrt source =
        Real.rpow source (1 / 2 : ℝ) :=
      Real.sqrt_eq_rpow source
    _ ≤
        Real.rpow constant (1 / 2 : ℝ) *
          Real.rpow delta (-(loss * (1 / 2 : ℝ))) :=
      hpower
    _ =
        Real.sqrt constant *
          Real.rpow delta (-(loss / 2)) := by
      rw [Real.sqrt_eq_rpow constant]
      congr 2
      ring

lemma canonical_cutoff_incidence_scale_le
    (delta t Delta T C_R C_inc heavyLogLoss metricExponent : ℝ)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hDelta : 0 < Delta)
    (hT : 0 < T)
    (hC_R : 0 < C_R)
    (hC_inc : 0 < C_inc)
    (hH : 0 < heavyLogLoss)
    (hmetric : 0 < metricExponent)
    (hdeltaDelta : delta ≤ Delta)
    (hDeltaT : Delta ≤ t)
    (htT : t ≤ T)
    (hlogLoss :
      heavyLogLoss ≤
        Real.rpow delta (-(metricExponent ^ 3))) :
    C_inc *
          Real.sqrt
            (16 * C_R /
              (selectedIncidenceMetricCut
                    heavyLogLoss
                    (4 *
                      Real.rpow (2 * t / Delta)
                        (metricExponent ^ 2))
                    metricExponent *
                selectedIncidenceTangencyCut
                  heavyLogLoss (metricExponent ^ 2))) +
        1 ≤
      (C_inc *
            Real.sqrt
              (32 * C_R *
                Real.rpow
                  (96 *
                    Real.rpow (2 * T)
                      (metricExponent ^ 2))
                  (1 / metricExponent) *
                Real.rpow 24
                  (1 / (metricExponent ^ 2))) +
          1) *
        Real.rpow delta
          (-(metricExponent +
            metricExponent ^ 2 / 2)) := by
  let cutoffConstant : ℝ :=
    2 *
        Real.rpow
          (96 *
            Real.rpow (2 * T)
              (metricExponent ^ 2))
          (1 / metricExponent) *
      Real.rpow 24
        (1 / (metricExponent ^ 2))
  let cutoffLoss : ℝ :=
    2 * metricExponent + metricExponent ^ 2
  have hfixedBase :
      0 <
        96 *
          Real.rpow (2 * T)
            (metricExponent ^ 2) := by
    exact mul_pos (by norm_num)
      (Real.rpow_pos_of_pos
        (mul_pos (by norm_num) hT) _)
  have hcutoffConstant : 0 < cutoffConstant := by
    dsimp only [cutoffConstant]
    exact mul_pos
      (mul_pos (by norm_num)
        (Real.rpow_pos_of_pos hfixedBase _))
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hcutoffLoss : 0 < cutoffLoss := by
    dsimp only [cutoffLoss]
    nlinarith [sq_nonneg metricExponent]
  have hcutoff :=
    canonical_cutoff_product_inv_le
      delta t Delta T heavyLogLoss metricExponent
      hdelta hDelta hT hH hmetric hdeltaDelta hDeltaT htT
      hlogLoss
  have hcutoff' :
      (selectedIncidenceMetricCut
            heavyLogLoss
            (4 *
              Real.rpow (2 * t / Delta)
                (metricExponent ^ 2))
            metricExponent *
          selectedIncidenceTangencyCut
            heavyLogLoss (metricExponent ^ 2))⁻¹ ≤
        cutoffConstant *
          Real.rpow delta (-cutoffLoss) := by
    simpa only [cutoffConstant, cutoffLoss] using hcutoff
  have hdenominatorPos :
      0 <
        selectedIncidenceMetricCut
              heavyLogLoss
              (4 *
                Real.rpow (2 * t / Delta)
                  (metricExponent ^ 2))
              metricExponent *
            selectedIncidenceTangencyCut
              heavyLogLoss (metricExponent ^ 2) := by
    have ht : 0 < t := hDelta.trans_le hDeltaT
    have hfiberRatio :
        0 <
          4 *
            Real.rpow (2 * t / Delta)
              (metricExponent ^ 2) := by
      exact mul_pos (by norm_num)
        (Real.rpow_pos_of_pos
          (div_pos (mul_pos (by norm_num) ht) hDelta) _)
    have hmetricCut :
        0 <
          selectedIncidenceMetricCut
            heavyLogLoss
            (4 *
              Real.rpow (2 * t / Delta)
                (metricExponent ^ 2))
            metricExponent := by
      dsimp only [selectedIncidenceMetricCut]
      exact mul_pos (by norm_num)
        (Real.rpow_pos_of_pos (by positivity) _)
    have htangencyCut :
        0 <
          selectedIncidenceTangencyCut
            heavyLogLoss (metricExponent ^ 2) := by
      dsimp only [selectedIncidenceTangencyCut]
      exact Real.rpow_pos_of_pos (by positivity) _
    exact mul_pos hmetricCut htangencyCut
  have hsourceNonneg :
      0 ≤
        16 * C_R /
          (selectedIncidenceMetricCut
                heavyLogLoss
                (4 *
                  Real.rpow (2 * t / Delta)
                    (metricExponent ^ 2))
                metricExponent *
              selectedIncidenceTangencyCut
                heavyLogLoss (metricExponent ^ 2)) := by
    exact div_nonneg
      (mul_nonneg (by norm_num) hC_R.le)
      hdenominatorPos.le
  have hsource :
      16 * C_R /
            (selectedIncidenceMetricCut
                  heavyLogLoss
                  (4 *
                    Real.rpow (2 * t / Delta)
                      (metricExponent ^ 2))
                  metricExponent *
                selectedIncidenceTangencyCut
                  heavyLogLoss (metricExponent ^ 2)) ≤
        (16 * C_R * cutoffConstant) *
          Real.rpow delta (-cutoffLoss) := by
    have hscaled :=
      mul_le_mul_of_nonneg_left hcutoff'
        (mul_nonneg
          (show (0 : ℝ) ≤ 16 by norm_num)
          hC_R.le)
    simpa [div_eq_mul_inv, mul_assoc] using hscaled
  have hsqrt :=
    sqrt_polynomial_upper_bound
      (16 * C_R /
        (selectedIncidenceMetricCut
              heavyLogLoss
              (4 *
                Real.rpow (2 * t / Delta)
                  (metricExponent ^ 2))
              metricExponent *
            selectedIncidenceTangencyCut
              heavyLogLoss (metricExponent ^ 2)))
      (16 * C_R * cutoffConstant) delta cutoffLoss
      hsourceNonneg
      (mul_nonneg (mul_nonneg (by norm_num) hC_R.le)
        hcutoffConstant.le)
      hdelta hsource
  have hlossHalf :
      cutoffLoss / 2 =
        metricExponent + metricExponent ^ 2 / 2 := by
    dsimp only [cutoffLoss]
    ring
  have hdeltaPower :
      1 ≤ Real.rpow delta (-(cutoffLoss / 2)) := by
    have h :=
      Real.rpow_le_rpow_of_exponent_ge
        hdelta hdeltaOne
        (show -(cutoffLoss / 2) ≤ 0 by
          linarith [hcutoffLoss])
    simpa using h
  have hscaledSqrt :=
    mul_le_mul_of_nonneg_left hsqrt hC_inc.le
  calc
    C_inc *
          Real.sqrt
            (16 * C_R /
              (selectedIncidenceMetricCut
                    heavyLogLoss
                    (4 *
                      Real.rpow (2 * t / Delta)
                        (metricExponent ^ 2))
                    metricExponent *
                selectedIncidenceTangencyCut
                  heavyLogLoss (metricExponent ^ 2))) +
        1 ≤
      C_inc *
            (Real.sqrt (16 * C_R * cutoffConstant) *
              Real.rpow delta (-(cutoffLoss / 2))) +
          Real.rpow delta (-(cutoffLoss / 2)) := by
      exact add_le_add hscaledSqrt hdeltaPower
    _ =
      (C_inc *
            Real.sqrt (16 * C_R * cutoffConstant) +
          1) *
        Real.rpow delta (-(cutoffLoss / 2)) := by ring
    _ =
      (C_inc *
            Real.sqrt
              (32 * C_R *
                Real.rpow
                  (96 *
                    Real.rpow (2 * T)
                      (metricExponent ^ 2))
                  (1 / metricExponent) *
                Real.rpow 24
                  (1 / (metricExponent ^ 2))) +
          1) *
        Real.rpow delta
          (-(metricExponent +
            metricExponent ^ 2 / 2)) := by
      dsimp only [cutoffConstant]
      rw [hlossHalf]
      ring_nf

lemma canonical_representative_incidence_scale_le
    (delta t Delta T C_R C_inc heavyLogLoss metricExponent : ℝ)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hDelta : 0 < Delta)
    (hT : 0 < T)
    (hC_R : 0 < C_R)
    (hC_inc : 0 < C_inc)
    (hH : 0 < heavyLogLoss)
    (hmetric : 0 < metricExponent)
    (hdeltaDelta : delta ≤ Delta)
    (hDeltaT : Delta ≤ t)
    (htT : t ≤ T)
    (hlogLoss :
      heavyLogLoss ≤
        Real.rpow delta (-(metricExponent ^ 3))) :
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
        1 ≤
      (C_inc *
            Real.sqrt
              (32 * C_R *
                Real.rpow
                  (96 *
                    Real.rpow (2 * T)
                      (metricExponent ^ 2))
                  (1 / metricExponent) *
                Real.rpow 24
                  (1 / (metricExponent ^ 2))) +
          1) *
        Real.rpow delta
          (-(metricExponent +
            metricExponent ^ 2 / 2)) := by
  have ht : 0 < t := hDelta.trans_le hDeltaT
  have hfiberRatio :
      0 <
        4 *
          Real.rpow (2 * t / Delta)
            (metricExponent ^ 2) := by
    exact mul_pos (by norm_num)
      (Real.rpow_pos_of_pos
        (div_pos (mul_pos (by norm_num) ht) hDelta) _)
  have hmetricCut :
      0 <
        selectedIncidenceMetricCut
          heavyLogLoss
          (4 *
            Real.rpow (2 * t / Delta)
              (metricExponent ^ 2))
          metricExponent := by
    dsimp only [selectedIncidenceMetricCut]
    exact mul_pos (by norm_num)
      (Real.rpow_pos_of_pos (by positivity) _)
  have htangencyCut :
      0 <
        selectedIncidenceTangencyCut
          heavyLogLoss (metricExponent ^ 2) := by
    dsimp only [selectedIncidenceTangencyCut]
    exact Real.rpow_pos_of_pos (by positivity) _
  rw [cutoff_incidence_scale_eq hdelta ht hDelta
    hmetricCut htangencyCut]
  exact canonical_cutoff_incidence_scale_le
    delta t Delta T C_R C_inc heavyLogLoss metricExponent
    hdelta hdeltaOne hDelta hT hC_R hC_inc hH hmetric
    hdeltaDelta hDeltaT htT hlogLoss

end Kakeya.Cinematic
