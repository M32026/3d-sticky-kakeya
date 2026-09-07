import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TreePureSchedule

/-!
# Proposition 6.2: requested-scale descendant-or-top dichotomy

The old simultaneous schedule is rounded at the physical requested scale
`max (100 * delta) (rho * requested)`.  Scale antitonicity then gives the
paper's exact dichotomy:

* if the rounded coordinate is after the selected packet coordinate, it is
  an old descendant scale between `100 * delta` and `rho`;
* otherwise the packet scale lies below the rounded actual scale, and one
  scalar packet-window inequality forces the rescaled top branch.

The scalar `topGate` is the exact numerical premise consumed by the top
branch.  It may be discharged either from the paper estimate
`rho / (K₀ C*) ≤ s` or by enlarging the finite route constant.  No geometric
or fiber input is hidden in this module.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2Prop62PureSchedule

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow)

/--
Round one normalized requested scale either to an old descendant coordinate
or to the rescaled top window.
-/
theorem requested_descendant_or_top
    (packetCoordinate : Fin schedule.levelCount)
    {rho : ℝ}
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (scaleSeparation : 100 * delta ≤ rho)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sourceConstant : ENNReal)
    (sourceConstantFinite :
      WZ2PaperFiniteErrorConstant sourceConstant)
    (windowAbsorption :
      (100 : ENNReal) * scaleWindow ≤
        (81000000 : ENNReal) * sourceConstant)
    (topGate :
      (4 : ENNReal) *
          ((100 : ENNReal) * scaleWindow *
            ENNReal.ofReal rho) ≤
        ((81000000 : ENNReal) * sourceConstant) *
          ENNReal.ofReal
            (schedule.actualScale packetCoordinate)) :
    ∀ requested : WZ2PaperRequestedScale (delta / rho),
      (∃ coordinate : Fin schedule.levelCount,
        packetCoordinate.val < coordinate.val ∧
          100 * delta ≤ schedule.actualScale coordinate ∧
          schedule.actualScale coordinate ≤ rho ∧
          requested.1 ≤ schedule.actualScale coordinate / rho ∧
          ENNReal.ofReal
              (schedule.actualScale coordinate / rho) <
            ((81000000 : ENNReal) * sourceConstant) *
              ENNReal.ofReal requested.1) ∨
      (4 : ENNReal) <
        ((81000000 : ENNReal) * sourceConstant) *
          ENNReal.ofReal requested.1 := by
  intro requested
  have deltaPos : 0 < delta :=
    (schedule.scaleData packetCoordinate).delta_pos
  have requestedPos : 0 < requested.1 :=
    (div_pos deltaPos rhoPos).trans_le requested.2.1
  have deltaLeRhoRequested :
      delta ≤ rho * requested.1 := by
    have raw :=
      (div_le_iff₀ rhoPos).mp requested.2.1
    simpa only [mul_comm] using raw
  let physicalRequested : WZ2PaperRequestedScale delta :=
    ⟨max (100 * delta) (rho * requested.1),
      by
        constructor
        · exact
            (show delta ≤ 100 * delta by nlinarith).trans
              (le_max_left _ _)
        · apply max_le
          · exact scaleSeparation.trans rhoLeOne
          · nlinarith [requested.2.2]⟩
  have physicalLe :
      physicalRequested.1 ≤
        100 * rho * requested.1 := by
    dsimp only [physicalRequested]
    apply max_le
    · nlinarith
    · have rhoRequestedPos : 0 < rho * requested.1 :=
        mul_pos rhoPos requestedPos
      nlinarith
  rcases schedule.rounding physicalRequested with
    ⟨coordinate, physicalLeActual, actualWindow⟩
  let targetConstant : ENNReal :=
    (81000000 : ENNReal) * sourceConstant
  let windowDenominator : ENNReal :=
    (100 : ENNReal) * scaleWindow * ENNReal.ofReal rho
  have physicalWindow :
      ENNReal.ofReal physicalRequested.1 ≤
        (100 : ENNReal) * ENNReal.ofReal rho *
          ENNReal.ofReal requested.1 := by
    have rightNonnegative :
        0 ≤ 100 * rho * requested.1 := by positivity
    have raw :
        ENNReal.ofReal physicalRequested.1 ≤
          ENNReal.ofReal (100 * rho * requested.1) :=
      (ENNReal.ofReal_le_ofReal_iff rightNonnegative).mpr
        physicalLe
    calc
      ENNReal.ofReal physicalRequested.1 ≤
          ENNReal.ofReal (100 * rho * requested.1) := raw
      _ =
          (100 : ENNReal) * ENNReal.ofReal rho *
            ENNReal.ofReal requested.1 := by
        calc
          ENNReal.ofReal (100 * rho * requested.1) =
              ENNReal.ofReal (100 * rho) *
                ENNReal.ofReal requested.1 := by
            rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 100 * rho)]
          _ =
              ((100 : ENNReal) * ENNReal.ofReal rho) *
                ENNReal.ofReal requested.1 := by
            rw [ENNReal.ofReal_mul
              (by norm_num : (0 : ℝ) ≤ 100)]
            norm_num
  have actualWindow' :
      ENNReal.ofReal (schedule.actualScale coordinate) <
        ((100 : ENNReal) * scaleWindow) *
          ENNReal.ofReal rho *
            ENNReal.ofReal requested.1 := by
    calc
      ENNReal.ofReal (schedule.actualScale coordinate) <
          scaleWindow * ENNReal.ofReal physicalRequested.1 :=
        actualWindow
      _ ≤
          scaleWindow *
            ((100 : ENNReal) * ENNReal.ofReal rho *
              ENNReal.ofReal requested.1) := by
        gcongr
      _ =
          ((100 : ENNReal) * scaleWindow) *
            ENNReal.ofReal rho *
              ENNReal.ofReal requested.1 := by
        ring
  by_cases descendant :
      packetCoordinate.val < coordinate.val
  · left
    have actualLePacket :
        schedule.actualScale coordinate ≤
          schedule.actualScale packetCoordinate :=
      schedule.actualScale_antitone packetCoordinate coordinate
        descendant.le
    have treeSafe :
        100 * delta ≤ schedule.actualScale coordinate :=
      (le_max_left _ _).trans physicalLeActual
    have actualLeRho :
        schedule.actualScale coordinate ≤ rho :=
      actualLePacket.trans packetScaleLeRho
    have requestedLe :
        requested.1 ≤
          schedule.actualScale coordinate / rho := by
      apply (le_div_iff₀ rhoPos).mpr
      have rhoRequestedLePhysical :
          requested.1 * rho ≤ physicalRequested.1 := by
        dsimp only [physicalRequested]
        simpa only [mul_comm] using
          (le_max_right (100 * delta) (rho * requested.1))
      exact rhoRequestedLePhysical.trans physicalLeActual
    have rescaledWindow :
        ENNReal.ofReal
            (schedule.actualScale coordinate / rho) <
          targetConstant * ENNReal.ofReal requested.1 := by
      rw [ENNReal.ofReal_div_of_pos rhoPos]
      apply ENNReal.div_lt_of_lt_mul
      calc
        ENNReal.ofReal (schedule.actualScale coordinate) <
            ((100 : ENNReal) * scaleWindow) *
              ENNReal.ofReal rho *
                ENNReal.ofReal requested.1 :=
          actualWindow'
        _ ≤
            targetConstant *
              ENNReal.ofReal requested.1 *
                ENNReal.ofReal rho := by
          dsimp only [targetConstant]
          calc
            ((100 : ENNReal) * scaleWindow) *
                  ENNReal.ofReal rho *
                ENNReal.ofReal requested.1 =
                ((100 : ENNReal) * scaleWindow) *
                  ENNReal.ofReal requested.1 *
                    ENNReal.ofReal rho := by
              ring
            _ ≤
                ((81000000 : ENNReal) * sourceConstant) *
                  ENNReal.ofReal requested.1 *
                    ENNReal.ofReal rho := by
              gcongr
    exact
      ⟨coordinate, descendant, treeSafe, actualLeRho,
        requestedLe, by
          simpa only [targetConstant] using rescaledWindow⟩
  · right
    have coordinateLePacket :
        coordinate.val ≤ packetCoordinate.val := by
      omega
    have packetLeActual :
        schedule.actualScale packetCoordinate ≤
          schedule.actualScale coordinate :=
      schedule.actualScale_antitone coordinate packetCoordinate
        coordinateLePacket
    have packetWindow :
        ENNReal.ofReal (schedule.actualScale packetCoordinate) <
          windowDenominator * ENNReal.ofReal requested.1 := by
      calc
        ENNReal.ofReal (schedule.actualScale packetCoordinate) ≤
            ENNReal.ofReal (schedule.actualScale coordinate) :=
          ENNReal.ofReal_mono packetLeActual
        _ <
            ((100 : ENNReal) * scaleWindow) *
              ENNReal.ofReal rho *
                ENNReal.ofReal requested.1 :=
          actualWindow'
        _ =
            windowDenominator * ENNReal.ofReal requested.1 := by
          rfl
    have targetNeZero : targetConstant ≠ 0 := by
      dsimp only [targetConstant]
      exact mul_ne_zero (by norm_num)
        (ne_of_gt (zero_lt_one.trans_le sourceConstantFinite.1))
    have targetNeTop : targetConstant ≠ ⊤ := by
      dsimp only [targetConstant]
      exact ENNReal.mul_ne_top (by norm_num)
        sourceConstantFinite.2
    have denominatorNeZero : windowDenominator ≠ 0 := by
      dsimp only [windowDenominator]
      exact mul_ne_zero
        (mul_ne_zero (by norm_num)
          (ne_of_gt (zero_lt_one.trans_le
            schedule.scaleWindow_finite.1)))
        (ENNReal.ofReal_ne_zero_iff.mpr rhoPos)
    have denominatorNeTop : windowDenominator ≠ ⊤ := by
      dsimp only [windowDenominator]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num)
          schedule.scaleWindow_finite.2)
        ENNReal.ofReal_ne_top
    have multipliedWindow :
        targetConstant *
              ENNReal.ofReal
                (schedule.actualScale packetCoordinate) <
          targetConstant *
            (windowDenominator *
              ENNReal.ofReal requested.1) :=
      ENNReal.mul_lt_mul_right targetNeZero targetNeTop packetWindow
    have cancelled :
        (4 : ENNReal) * windowDenominator <
          (targetConstant * ENNReal.ofReal requested.1) *
            windowDenominator := by
      calc
        (4 : ENNReal) * windowDenominator ≤
            targetConstant *
              ENNReal.ofReal
                (schedule.actualScale packetCoordinate) := by
          simpa only [targetConstant, windowDenominator] using topGate
        _ <
            targetConstant *
              (windowDenominator *
                ENNReal.ofReal requested.1) :=
          multipliedWindow
        _ =
            (targetConstant * ENNReal.ofReal requested.1) *
              windowDenominator := by
          ring
    have topWindow :
        (4 : ENNReal) <
          targetConstant * ENNReal.ofReal requested.1 :=
      (ENNReal.mul_lt_mul_iff_left
        denominatorNeZero denominatorNeTop).mp cancelled
    simpa only [targetConstant] using topWindow

end PureWZ2Prop62PureSchedule

end Kakeya.Assouad

end
