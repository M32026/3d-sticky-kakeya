import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicFineAssignmentData

/-!
# Metric-to-retained fiber ratio from one dyadic retained level

The tangency two-ends retention inequality compares each metric fiber to its
retained tangency fiber.  Once the retained cardinality has a common dyadic
upper scale, this gives the uniform ratio needed by the paper-radius choice.
-/

namespace Kakeya.Cinematic

lemma representative_metric_to_retained_fiber
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R)
    (hdelta : 0 < delta)
    (p : E) :
    Real.rpow (DeltaRep / (2 * tRep)) eta *
          ((data.metricFiber p).card : ℝ) ≤
      2 * ((data.assignment.fiber p).card : ℝ) := by
  have hexactT : 0 < data.exactT p :=
    hdelta.trans_le (data.certificate p).delta_le_t
  have hexactDelta : 0 < data.exactDelta p :=
    hdelta.trans_le (data.certificate p).delta_le_Delta
  have htRep : 0 < tRep := data.tRep_pos
  have hDeltaRep : 0 < DeltaRep :=
    hdelta.trans_le data.delta_le_DeltaRep
  have htangency_ratio :
      DeltaRep / (2 * tRep) ≤
        data.exactDelta p / (4 * data.exactT p) := by
    have hfirst :
        DeltaRep / (2 * tRep) ≤
          data.exactDelta p / tRep := by
      calc
        DeltaRep / (2 * tRep) =
            (DeltaRep / 2) / tRep := by ring
        _ ≤ data.exactDelta p / tRep := by
          apply (div_le_div_iff_of_pos_right htRep).2
          have hrep := data.repDelta_le_two_exactDelta p
          linarith
    have hsecond :
        data.exactDelta p / tRep ≤
          data.exactDelta p / (4 * data.exactT p) := by
      apply div_le_div_of_nonneg_left hexactDelta.le
        (by positivity)
      exact data.four_exactT_le_rep p
    exact hfirst.trans hsecond
  have htangency_rpow :
      Real.rpow (DeltaRep / (2 * tRep)) eta ≤
        Real.rpow
          (data.exactDelta p / (4 * data.exactT p)) eta :=
    Real.rpow_le_rpow
      (by positivity) htangency_ratio data.eta_pos.le
  have hmetric_nonneg :
      0 ≤ ((data.metricFiber p).card : ℝ) := by
    positivity
  calc
    Real.rpow (DeltaRep / (2 * tRep)) eta *
          ((data.metricFiber p).card : ℝ) ≤
        Real.rpow
            (data.exactDelta p / (4 * data.exactT p)) eta *
          ((data.metricFiber p).card : ℝ) :=
      mul_le_mul_of_nonneg_right htangency_rpow hmetric_nonneg
    _ ≤ 2 * ((data.tangencyFiber p).card : ℝ) :=
      (data.certificate p).tangency_retention
    _ = 2 * ((data.assignment.fiber p).card : ℝ) := by
      rw [data.assignment_fiber p]

lemma metric_card_le_four_div_mul_retained_scale
    {metricCard retainedCard retainedScale : ℕ}
    {factor : ℝ}
    (hfactor : 0 < factor)
    (hretainedUpper : retainedCard < 2 * retainedScale)
    (hretention :
      factor * (metricCard : ℝ) ≤
        2 * (retainedCard : ℝ)) :
    (metricCard : ℝ) ≤
      (4 / factor) * (retainedScale : ℝ) := by
  have hretained :
      (retainedCard : ℝ) ≤
        2 * (retainedScale : ℝ) := by
    exact_mod_cast Nat.le_of_lt hretainedUpper
  have hscaled :
      factor * (metricCard : ℝ) ≤
        factor * ((4 / factor) * (retainedScale : ℝ)) := by
    calc
      factor * (metricCard : ℝ) ≤
          2 * (retainedCard : ℝ) :=
        hretention
      _ ≤ 2 * (2 * (retainedScale : ℝ)) := by
        gcongr
      _ = factor * ((4 / factor) * (retainedScale : ℝ)) := by
        field_simp [hfactor.ne']
        ring
  exact le_of_mul_le_mul_left hscaled hfactor

lemma representative_metric_card_le_retained_scale
    {metricCard retainedCard retainedScale : ℕ}
    {tRep DeltaRep eta : ℝ}
    (htRep : 0 < tRep)
    (hDeltaRep : 0 < DeltaRep)
    (heta : 0 < eta)
    (hretainedUpper : retainedCard < 2 * retainedScale)
    (hretention :
      Real.rpow (DeltaRep / (2 * tRep)) eta *
          (metricCard : ℝ) ≤
        2 * (retainedCard : ℝ)) :
    (metricCard : ℝ) ≤
      (4 *
        Real.rpow (2 * tRep / DeltaRep) eta) *
        (retainedScale : ℝ) := by
  have hratio : 0 < DeltaRep / (2 * tRep) := by
    positivity
  have hfactor :
      0 < Real.rpow (DeltaRep / (2 * tRep)) eta :=
    Real.rpow_pos_of_pos hratio eta
  have hmain :=
    metric_card_le_four_div_mul_retained_scale
      hfactor hretainedUpper hretention
  have hinverse :
      4 / Real.rpow (DeltaRep / (2 * tRep)) eta =
        4 * Real.rpow (2 * tRep / DeltaRep) eta := by
    have hreciprocal :
        2 * tRep / DeltaRep =
          (DeltaRep / (2 * tRep))⁻¹ := by
      field_simp [htRep.ne', hDeltaRep.ne']
    have hrpow_reciprocal :
        Real.rpow (2 * tRep / DeltaRep) eta =
          (Real.rpow (DeltaRep / (2 * tRep)) eta)⁻¹ := by
      rw [hreciprocal]
      exact Real.inv_rpow hratio.le eta
    rw [hrpow_reciprocal]
    simp [div_eq_mul_inv]
  rw [hinverse] at hmain
  exact hmain

end Kakeya.Cinematic
