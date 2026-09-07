import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9NestedGlobalCost

/-! # Power bound for the final M9 mild-rescaling scale -/

noncomputable section
namespace Kakeya.Assouad.PureWZ2
namespace Proposition63M9RobustInitialPreliminaryData

variable
    {sigma outputLoss : ℝ}
    {critical : PureWZ2CriticalPackage sigma}
    {schedule : Proposition63M9NestedScheduleData sigma outputLoss critical}
    {externalCutoff : ℝ}
    (data : Proposition63M9RobustInitialPreliminaryData critical
      schedule.inner schedule.innerCutoff externalCutoff)

private abbrev q : ℝ :=
  (schedule.innerCutoff.twoCall.secondQRequested data.r_pos
    data.r_le_robustCutoff).1

/-- The Lemma-4.12 plane-map constant is below the final source-loss power
at the exact second scale. -/
theorem outerPlaneLipschitz_le_preGrainPower
    {hqOuter : data.q ≤ schedule.outerCutoff.outerScaleCeiling}
    (first : Proposition63GenericFirstRichBoundaryData
      (reentryLoss := schedule.outerCutoff.firstRichSchedule.sourceLoss)
      (data.outerRoot hqOuter) (data.outerPreliminaryOnRoot hqOuter)
      schedule.outerCutoff.firstRichSchedule) :
    Real.toNNReal (Real.rpow first.power.Delta
        (-schedule.outer.lemma47Loss)) ≤
      Real.toNNReal (Real.rpow first.power.Delta
        (-schedule.outer.preGrainLoss)) := by
  have DeltaPos : 0 < first.power.Delta := by
    rw [first.power.Delta_eq]
    exact Real.rpow_pos_of_pos
      first.current.normalization.final_extremal.delta_pos _
  have DeltaOne : first.power.Delta ≤ 1 :=
    by simpa only [first.power.requested_eq] using first.power.requested.2.2
  apply Real.toNNReal_le_toNNReal
  exact Real.rpow_le_rpow_of_exponent_ge DeltaPos DeltaOne
    (by linarith [schedule.outer.lemma47Loss_lt_preGrain])

/-- The normalized global-slope constant also fits below the same final
source-loss power.  The fixed factor and inherited coefficient are precisely
the two local-loss factors already dominated by the four-loss global cutoff. -/
theorem outerSlopeLipschitz_le_preGrainPower
    {hqOuter : data.q ≤ schedule.outerCutoff.outerScaleCeiling}
    (first : Proposition63GenericFirstRichBoundaryData
      (reentryLoss := schedule.outerCutoff.firstRichSchedule.sourceLoss)
      (data.outerRoot hqOuter) (data.outerPreliminaryOnRoot hqOuter)
      schedule.outerCutoff.firstRichSchedule)
    (coefficient : NNReal)
    (coefficientLe : (coefficient : ENNReal) ≤
      Kakeya.realRpowENN data.q
        (-schedule.outerCutoff.initial.localLoss)) :
    252000 * coefficient ≤
      Real.toNNReal (Real.rpow first.power.Delta
        (-schedule.outer.preGrainLoss)) := by
  apply (ENNReal.coe_le_coe).mp
  have qPos : 0 < data.q :=
    first.current.normalization.final_extremal.delta_pos
  have qGlobal : data.q ≤ schedule.outerCutoff.globalADAbsorption.delta₀ :=
    hqOuter.trans
      schedule.outerCutoff.outerScaleCeiling_le_globalADAbsorption
  have fixedLe : (252000 : ENNReal) ≤
      Kakeya.realRpowENN data.q
        (-schedule.outerCutoff.initial.localLoss) := by
    have numeric : (252000 : ENNReal) ≤
        Proposition63ChartSelectionData.proposition63M9CoarseGlobalPolynomialConstant := by
      unfold Proposition63ChartSelectionData.proposition63M9CoarseGlobalPolynomialConstant
      norm_num
    exact numeric.trans
        (schedule.outerCutoff.globalADAbsorption.constant_absorb qPos qGlobal)
  have productLe :
      (252000 : ENNReal) * (coefficient : ENNReal) ≤
        Kakeya.realRpowENN data.q
          (-(2 * schedule.outerCutoff.initial.localLoss)) := by
    calc
      _ ≤ Kakeya.realRpowENN data.q
            (-schedule.outerCutoff.initial.localLoss) *
          Kakeya.realRpowENN data.q
            (-schedule.outerCutoff.initial.localLoss) := by gcongr
      _ = _ := by
        rw [← Kakeya.Assouad.realRpowENN_add qPos]
        congr 1
        ring
  have exponentLt :
      2 * schedule.outerCutoff.initial.localLoss <
        (sigma / (2 + sigma)) * schedule.outer.preGrainLoss := by
    linarith [schedule.outerCutoff.initial_local_global_gap,
      schedule.outerCutoff.initial.sticky_pos.trans
        schedule.outerCutoff.initial.sticky_lt_local]
  have powerLe : Kakeya.realRpowENN data.q
        (-(2 * schedule.outerCutoff.initial.localLoss)) ≤
      Kakeya.realRpowENN first.power.Delta
        (-schedule.outer.preGrainLoss) := by
    have targetEq : Kakeya.realRpowENN first.power.Delta
          (-schedule.outer.preGrainLoss) =
        Kakeya.realRpowENN data.q
          (-(sigma / (2 + sigma) * schedule.outer.preGrainLoss)) := by
      unfold Kakeya.realRpowENN
      rw [first.power.Delta_eq]
      congr 1
      calc
        (Real.rpow data.q (sigma / (2 + sigma))).rpow
              (-schedule.outer.preGrainLoss) =
            Real.rpow data.q
              ((sigma / (2 + sigma)) *
                (-schedule.outer.preGrainLoss)) :=
          (Real.rpow_mul qPos.le _ _).symm
        _ = Real.rpow data.q
              (-(sigma / (2 + sigma) * schedule.outer.preGrainLoss)) := by
          congr 1
          ring
    rw [targetEq]
    exact ENNReal.ofReal_mono <| Real.rpow_le_rpow_of_exponent_ge qPos
      (hqOuter.trans schedule.outerCutoff.outerScaleCeiling_le_one) (by
        linarith)
  have result :
      ((252000 * coefficient : NNReal) : ENNReal) ≤
        (Real.toNNReal (Real.rpow first.power.Delta
          (-schedule.outer.preGrainLoss)) : ENNReal) := by
    have DeltaPos : 0 < first.power.Delta := by
      rw [first.power.Delta_eq]
      exact Real.rpow_pos_of_pos qPos _
    have leftEq :
        ((252000 * coefficient : NNReal) : ENNReal) =
          (252000 : ENNReal) *
            (coefficient : ENNReal) := by
      norm_num
    have rightEq :
        (Real.toNNReal (Real.rpow first.power.Delta
          (-schedule.outer.preGrainLoss)) : ENNReal) =
            Kakeya.realRpowENN first.power.Delta
              (-schedule.outer.preGrainLoss) := by
      rw [ENNReal.coe_nnreal_eq]
      congr 1
      exact Real.coe_toNNReal _ (Real.rpow_nonneg DeltaPos.le _)
    rw [leftEq, rightEq]
    exact productLe.trans powerLe
  exact result

end Proposition63M9RobustInitialPreliminaryData
end Kakeya.Assouad.PureWZ2
end
