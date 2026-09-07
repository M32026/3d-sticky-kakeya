import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CallerAnchoredLaminarSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientUpperEnvelope
import Mathlib.Tactic

/-!
# Proposition 6.2 quotient upper-envelope rounding

If the inserted packet scale is strictly below `rho`, every application of the
ambient laminar rounding theorem to a requested scale in `[rho, 1]` lands at an
old coordinate strictly before the packet coordinate.  Thus it is a genuine
`ProxyUpperCoordinate`.

Multiplying the selected actual scale by the fixed upper-envelope factor
preserves the lower rounding inequality.  The upper inequality costs exactly
one factor `pureWZ2Prop62UpperEnvelopeFactor`.  The argument also covers the
top endpoint `1`, so no additional singleton scale is required.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2Prop62LaminarPureSchedule

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)

/--
Rounding by the upper-envelope scales
`pureWZ2Prop62UpperEnvelopeFactor * schedule.actualScale coordinate`.
-/
theorem proxyUpperEnvelope_rounding
    (packetCoordinate : Fin schedule.levelCount)
    (packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho)
    (outputConstant : ENNReal)
    (envelope_absorption :
      (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) * scaleWindow ≤
        outputConstant) :
    ∀ requested : WZ2PaperRequestedScale rho,
      ∃ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        requested.1 ≤
            pureWZ2Prop62UpperEnvelopeFactor *
              schedule.actualScale coordinate.1 ∧
          ENNReal.ofReal
              (pureWZ2Prop62UpperEnvelopeFactor *
                schedule.actualScale coordinate.1) <
            outputConstant * ENNReal.ofReal requested.1 := by
  intro requested
  have deltaLeRho :
      delta ≤ rho := by
    exact
      (schedule.delta_le_actualScale packetCoordinate).trans
        packetScaleLtRho.le
  let ambientRequested : WZ2PaperRequestedScale delta :=
    ⟨requested.1, deltaLeRho.trans requested.2.1, requested.2.2⟩
  rcases schedule.rounding ambientRequested with
    ⟨coordinate, requestedLe, within⟩
  have rhoLeActual :
      rho ≤ schedule.actualScale coordinate :=
    requested.2.1.trans requestedLe
  have coordinateBefore :
      coordinate.1 < packetCoordinate.1 := by
    by_contra notBefore
    have packetLeCoordinate :
        packetCoordinate.1 ≤ coordinate.1 :=
      Nat.le_of_not_gt notBefore
    have actualLePacket :
        schedule.actualScale coordinate ≤
          schedule.actualScale packetCoordinate :=
      schedule.actualScale_antitone
        packetCoordinate coordinate packetLeCoordinate
    linarith
  let upperCoordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate :=
    ⟨coordinate, rhoLeActual, coordinateBefore⟩
  refine ⟨upperCoordinate, ?_, ?_⟩
  · have actualPos :
        0 < schedule.actualScale coordinate :=
      (schedule.scaleData coordinate).rho_pos
    have factorOne :
        (1 : ℝ) ≤ pureWZ2Prop62UpperEnvelopeFactor := by
      norm_num [pureWZ2Prop62UpperEnvelopeFactor]
    exact requestedLe.trans <| by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right factorOne actualPos.le
  · have factorENNZero :
        (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) ≠ 0 := by
      norm_num [pureWZ2Prop62UpperEnvelopeFactor]
    have factorENNTop :
        (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) ≠ ⊤ := by
      exact ENNReal.coe_ne_top
    have scaledWithin :
        (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) *
              ENNReal.ofReal (schedule.actualScale coordinate) <
            (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) *
              (scaleWindow * ENNReal.ofReal requested.1) := by
      change
        (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) *
              ENNReal.ofReal (schedule.actualScale coordinate) <
            (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) *
              (scaleWindow * ENNReal.ofReal ambientRequested.1)
      simpa only [mul_comm] using
        ENNReal.mul_lt_mul_left factorENNZero factorENNTop within
    calc
      ENNReal.ofReal
          (pureWZ2Prop62UpperEnvelopeFactor *
            schedule.actualScale coordinate) =
          (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) *
            ENNReal.ofReal (schedule.actualScale coordinate) := by
        rw [ENNReal.ofReal_mul
          (by norm_num : (0 : ℝ) ≤
            pureWZ2Prop62UpperEnvelopeFactor)]
        simp only [ENNReal.ofReal_natCast]
      _ <
          (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) *
            (scaleWindow * ENNReal.ofReal requested.1) :=
        scaledWithin
      _ =
          ((pureWZ2Prop62UpperEnvelopeFactor : ENNReal) *
            scaleWindow) * ENNReal.ofReal requested.1 := by
        ring
      _ ≤
          outputConstant * ENNReal.ofReal requested.1 := by
        gcongr

/-- The upper-coordinate family is inhabited whenever `[rho, 1]` is nonempty. -/
theorem proxyUpperCoordinate_nonempty
    (packetCoordinate : Fin schedule.levelCount)
    (packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho)
    (rhoLeOne : rho ≤ 1) :
    Nonempty (schedule.ProxyUpperCoordinate rho packetCoordinate) := by
  let requested : WZ2PaperRequestedScale rho :=
    ⟨rho, le_rfl, rhoLeOne⟩
  rcases
      schedule.proxyUpperEnvelope_rounding packetCoordinate
        packetScaleLtRho
        ((pureWZ2Prop62UpperEnvelopeFactor : ENNReal) * scaleWindow)
        le_rfl requested
    with ⟨coordinate, _⟩
  exact ⟨coordinate⟩

end PureWZ2Prop62LaminarPureSchedule

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

/--
The anchored specialization.  The caller only proves the already chosen
parameter satisfies `1 ≤ K`; the final rounding conclusion is derived here.
-/
theorem proxyUpperEnvelope_rounding
    (rhoPos : 0 < rho)
    (oneLeK : 1 ≤ K)
    (outputConstant : ENNReal)
    (envelope_absorption :
      (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) *
          (ambientConstant * ENNReal.ofReal (R ^ 2)) ≤
        outputConstant) :
    ∀ requested : WZ2PaperRequestedScale rho,
      ∃ coordinate :
          data.schedule.ProxyUpperCoordinate rho data.packetCoordinate,
        requested.1 ≤
            pureWZ2Prop62UpperEnvelopeFactor *
              data.schedule.actualScale coordinate.1 ∧
          ENNReal.ofReal
              (pureWZ2Prop62UpperEnvelopeFactor *
                data.schedule.actualScale coordinate.1) <
            outputConstant * ENNReal.ofReal requested.1 := by
  have packetScaleLtRho :
      data.schedule.actualScale data.packetCoordinate < rho := by
    exact data.actualScale_lt_rho_div_K.trans_le <|
      div_le_self rhoPos.le oneLeK
  exact
    data.schedule.proxyUpperEnvelope_rounding
      data.packetCoordinate packetScaleLtRho outputConstant
      envelope_absorption

end PureWZ2Prop62CallerAnchoredLaminarScheduleData

end Kakeya.Assouad

end
