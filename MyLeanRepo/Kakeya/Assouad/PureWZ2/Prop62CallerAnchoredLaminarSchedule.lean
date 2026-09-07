import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CallerAnchoredRequestedScaleSchedule

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2Prop62CallerAnchoredLaminarScheduleData
    {delta rho K R : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant (ENNReal.ofReal R)) where
  requestedSchedule :
    PureWZ2Prop62RequestedScaleSchedule
      delta ambientConstant (ENNReal.ofReal (R ^ 2))
  anchorCoordinate : Fin requestedSchedule.levelCount
  q0 : WZ2PaperRequestedScale delta
  q0_eq :
    q0.1 = rho / (K * ambientConstant.toReal)
  requested_anchor :
    requestedSchedule.requested anchorCoordinate = q0
  requested_antitone :
    ∀ first second : Fin requestedSchedule.levelCount,
      first.1 ≤ second.1 →
        requestedSchedule.requested second ≤
          requestedSchedule.requested first
  levelCount_le :
    requestedSchedule.levelCount ≤ base.levelCount + 1
  q0_le_actualScale :
    q0.1 ≤
      (ambient.toProp62LaminarSchedule requestedSchedule).actualScale
        anchorCoordinate
  actualScale_lt_rho_div_K :
    (ambient.toProp62LaminarSchedule requestedSchedule).actualScale
        anchorCoordinate <
      rho / K

namespace PureWZ2Prop62CallerAnchoredLaminarScheduleData

variable
    {delta rho K R : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    {ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant}
    {base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant (ENNReal.ofReal R)}
    (data :
      PureWZ2Prop62CallerAnchoredLaminarScheduleData
        (rho := rho) (K := K) (R := R) ambient base)

noncomputable def schedule :
    PureWZ2Prop62LaminarPureSchedule
      fine ambientConstant
        (ambientConstant * ENNReal.ofReal (R ^ 2)) :=
  ambient.toProp62LaminarSchedule data.requestedSchedule

def packetCoordinate : Fin data.schedule.levelCount :=
  data.anchorCoordinate

def packetScale : ℝ :=
  data.schedule.actualScale data.packetCoordinate

theorem q0_literal :
    data.q0.1 = rho / (K * ambientConstant.toReal) :=
  data.q0_eq

theorem requested_at_packetCoordinate :
    data.requestedSchedule.requested data.packetCoordinate = data.q0 :=
  data.requested_anchor

theorem packetScale_eq_actualScale :
    data.packetScale =
      data.schedule.actualScale data.packetCoordinate :=
  rfl

theorem packetScale_eq_directNearby :
    data.packetScale =
      (pureWZ2Prop62DirectNearbyFamily
        ambient data.requestedSchedule data.anchorCoordinate).rho :=
  rfl

theorem packetScaleData_eq_directNearby :
    HEq
      (data.schedule.scaleData data.packetCoordinate)
      (pureWZ2Prop62DirectNearbyFamily
        ambient data.requestedSchedule data.anchorCoordinate).scaleData :=
  by
    rfl

theorem packetScale_bounds :
    data.q0.1 ≤ data.packetScale ∧
      data.packetScale < rho / K :=
  ⟨data.q0_le_actualScale, data.actualScale_lt_rho_div_K⟩

theorem literal_packetScale_bounds :
    rho / (K * ambientConstant.toReal) ≤ data.packetScale ∧
      data.packetScale < rho / K := by
  rw [← data.q0_literal]
  exact data.packetScale_bounds

theorem schedule_levelCount_le :
    data.schedule.levelCount ≤ base.levelCount + 1 :=
  data.levelCount_le

end PureWZ2Prop62CallerAnchoredLaminarScheduleData

noncomputable def
    PureWZ2Prop62CallerAnchoredScheduleData.toCallerAnchoredLaminarSchedule
    {delta rho K R : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    {ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant}
    {base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant (ENNReal.ofReal R)}
    (data :
      PureWZ2Prop62CallerAnchoredScheduleData
        (rho := rho) (K := K) (R := R) ambient base)
    (KPos : 0 < K)
    (q0Lower :
      delta ≤ pureWZ2Prop62CallerAnchorValue rho K ambientConstant)
    (q0Upper :
      pureWZ2Prop62CallerAnchorValue rho K ambientConstant ≤ 1) :
    PureWZ2Prop62CallerAnchoredLaminarScheduleData
      (rho := rho) (K := K) (R := R) ambient base := by
  have requestedAnchor :
      data.requestedSchedule.requested data.anchorCoordinate =
        pureWZ2Prop62CallerAnchorRequestedScale
          delta rho K ambientConstant q0Lower q0Upper :=
    Subtype.ext data.requested_anchor
  have anchorBounds :=
    ambient.toProp62LaminarSchedule_anchor_bounds
      data.requestedSchedule data.anchorCoordinate KPos
        q0Lower q0Upper requestedAnchor
  exact
    {
      requestedSchedule := data.requestedSchedule
      anchorCoordinate := data.anchorCoordinate
      q0 := data.requestedSchedule.requested data.anchorCoordinate
      q0_eq := by
        simpa [pureWZ2Prop62CallerAnchorValue] using
          data.requested_anchor
      requested_anchor := rfl
      requested_antitone := data.requested_antitone
      levelCount_le := data.levelCount_le
      q0_le_actualScale := by
        rw [data.requested_anchor]
        exact anchorBounds.1
      actualScale_lt_rho_div_K := anchorBounds.2
    }

theorem pureWZ2_prop62_caller_anchored_laminar_schedule
    {delta rho K R : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant (ENNReal.ofReal R))
    (KPos : 0 < K)
    (RPos : 0 < R)
    (ratioLe :
      4 * ambientConstant.toReal ≤ R)
    (q0Lower :
      delta ≤ pureWZ2Prop62CallerAnchorValue rho K ambientConstant)
    (q0Upper :
      pureWZ2Prop62CallerAnchorValue rho K ambientConstant ≤ 1)
    (topGap :
      4 * ambientConstant.toReal *
          pureWZ2Prop62CallerAnchorValue rho K ambientConstant ≤ 1) :
    Nonempty
      (PureWZ2Prop62CallerAnchoredLaminarScheduleData
        (rho := rho) (K := K) (R := R) ambient base) := by
  rcases
      pureWZ2_prop62_caller_anchored_schedule
        ambient base KPos RPos ratioLe q0Lower q0Upper topGap with
    ⟨data⟩
  exact
    ⟨data.toCallerAnchoredLaminarSchedule
      KPos q0Lower q0Upper⟩

end Kakeya.Assouad

end
