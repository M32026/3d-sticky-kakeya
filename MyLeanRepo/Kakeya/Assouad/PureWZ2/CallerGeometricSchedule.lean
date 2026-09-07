import MyLeanRepo.Kakeya.Assouad.PureWZ2.DegreeUniformRestrictedCWA

/-!
# Caller-relative geometric schedule

The complete-parent regularizer uses a full `[delta, 1]` schedule.  The
caller-center coarse assembly instead needs every scheduled witness to lie
above the caller scale.  These schedules may share their coordinate count but
must not be identified.

This module supplies the caller-relative schedule and its rounded ambient
Definition 2.12 witnesses.
-/

noncomputable section

namespace Kakeya.Assouad

def pureWZ2CallerGeometricRequestedScales
    {delta epsilon : ℝ}
    (caller : WZ2PaperRequestedScale delta)
    (hcallerPos : 0 < caller.1)
    (hcallerLtOne : caller.1 < 1)
    (hepsilonPos : 0 < epsilon)
    (coordinateCount : ℕ)
    (coordinate : Fin coordinateCount) :
    WZ2PaperRequestedScale delta :=
  let callerScale :=
    geometricRequestedScales
      caller.1 epsilon hcallerPos hcallerLtOne hepsilonPos
      coordinateCount coordinate
  ⟨callerScale.1,
    caller.2.1.trans callerScale.2.1,
    callerScale.2.2⟩

@[simp]
theorem pureWZ2CallerGeometricRequestedScales_val
    {delta epsilon : ℝ}
    (caller : WZ2PaperRequestedScale delta)
    (hcallerPos : 0 < caller.1)
    (hcallerLtOne : caller.1 < 1)
    (hepsilonPos : 0 < epsilon)
    (coordinateCount : ℕ)
    (coordinate : Fin coordinateCount) :
    (pureWZ2CallerGeometricRequestedScales
      caller hcallerPos hcallerLtOne hepsilonPos
      coordinateCount coordinate).1 =
      (geometricRequestedScales
        caller.1 epsilon hcallerPos hcallerLtOne hepsilonPos
        coordinateCount coordinate).1 := by
  rfl

theorem pureWZ2CallerGeometricRequestedScales_caller_le
    {delta epsilon : ℝ}
    (caller : WZ2PaperRequestedScale delta)
    (hcallerPos : 0 < caller.1)
    (hcallerLtOne : caller.1 < 1)
    (hepsilonPos : 0 < epsilon)
    (coordinateCount : ℕ)
    (coordinate : Fin coordinateCount) :
    caller.1 ≤
      (pureWZ2CallerGeometricRequestedScales
        caller hcallerPos hcallerLtOne hepsilonPos
        coordinateCount coordinate).1 := by
  exact
    (geometricRequestedScales
      caller.1 epsilon hcallerPos hcallerLtOne hepsilonPos
      coordinateCount coordinate).2.1

theorem pureWZ2_caller_geometric_requested_scale_rounding
    {delta epsilon : ℝ}
    (caller : WZ2PaperRequestedScale delta)
    (hcallerPos : 0 < caller.1)
    (hcallerLtOne : caller.1 < 1)
    (hepsilonPos : 0 < epsilon)
    {coordinateCount : ℕ}
    (hCount : coordinateCount = geometricScaleCount epsilon)
    (requested : WZ2PaperRequestedScale caller.1) :
    ∃ coordinate : Fin coordinateCount,
      requested.1 ≤
          (pureWZ2CallerGeometricRequestedScales
            caller hcallerPos hcallerLtOne hepsilonPos
            coordinateCount coordinate).1 ∧
        ENNReal.ofReal
            (pureWZ2CallerGeometricRequestedScales
              caller hcallerPos hcallerLtOne hepsilonPos
              coordinateCount coordinate).1 <
          ENNReal.ofReal (Real.rpow caller.1 (-epsilon)) *
            ENNReal.ofReal requested.1 := by
  simpa only [pureWZ2CallerGeometricRequestedScales_val] using
    geometricRequestedScale_rounding
      hcallerPos hcallerLtOne hepsilonPos hCount requested

noncomputable def pureWZ2CallerGeometricScheduled
    {delta epsilon : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (caller : WZ2PaperRequestedScale delta)
    (hcallerPos : 0 < caller.1)
    (hcallerLtOne : caller.1 < 1)
    (hepsilonPos : 0 < epsilon)
    (coordinateCount : ℕ)
    (coordinate : Fin coordinateCount) :
    WZ2PaperPureNearbyScaleCoverData
      fine
      (pureWZ2CallerGeometricRequestedScales
        caller hcallerPos hcallerLtOne hepsilonPos
        coordinateCount coordinate)
      ambientConstant :=
  Classical.choice <|
    ambient.2.2.2
      (pureWZ2CallerGeometricRequestedScales
        caller hcallerPos hcallerLtOne hepsilonPos
        coordinateCount coordinate)

theorem pureWZ2CallerGeometricScheduled_caller_le
    {delta epsilon : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (caller : WZ2PaperRequestedScale delta)
    (hcallerPos : 0 < caller.1)
    (hcallerLtOne : caller.1 < 1)
    (hepsilonPos : 0 < epsilon)
    (coordinateCount : ℕ)
    (coordinate : Fin coordinateCount) :
    caller.1 ≤
      (pureWZ2CallerGeometricScheduled
        ambient caller hcallerPos hcallerLtOne hepsilonPos
        coordinateCount coordinate).rho := by
  exact
    (pureWZ2CallerGeometricRequestedScales_caller_le
      caller hcallerPos hcallerLtOne hepsilonPos
      coordinateCount coordinate).trans
      (pureWZ2CallerGeometricScheduled
        ambient caller hcallerPos hcallerLtOne hepsilonPos
        coordinateCount coordinate).requested_le

theorem pureWZ2_caller_geometric_scheduled_rounding
    {delta epsilon : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (caller : WZ2PaperRequestedScale delta)
    (hcallerPos : 0 < caller.1)
    (hcallerLtOne : caller.1 < 1)
    (hepsilonPos : 0 < epsilon)
    {coordinateCount : ℕ}
    (hCount : coordinateCount = geometricScaleCount epsilon)
    (absorption :
      (19 : ENNReal) *
          ambientConstant *
          ENNReal.ofReal (Real.rpow caller.1 (-epsilon)) ≤
        outputConstant)
    (requested : WZ2PaperRequestedScale caller.1) :
    ∃ coordinate : Fin coordinateCount,
      requested.1 ≤
          19 *
            (pureWZ2CallerGeometricScheduled
              ambient caller hcallerPos hcallerLtOne hepsilonPos
              coordinateCount coordinate).rho ∧
        ENNReal.ofReal
            (19 *
              (pureWZ2CallerGeometricScheduled
                ambient caller hcallerPos hcallerLtOne hepsilonPos
                coordinateCount coordinate).rho) <
          outputConstant * ENNReal.ofReal requested.1 := by
  rcases
      pureWZ2_caller_geometric_requested_scale_rounding
        caller hcallerPos hcallerLtOne hepsilonPos
        hCount requested
    with
    ⟨coordinate, hrequested, hrounding⟩
  let scheduled :=
    pureWZ2CallerGeometricScheduled
      ambient caller hcallerPos hcallerLtOne hepsilonPos
      coordinateCount coordinate
  have scheduledPos : 0 < scheduled.rho :=
    scheduled.scaleData.rho_pos
  have requestPos : 0 < requested.1 :=
    hcallerPos.trans_le requested.2.1
  have hscheduledUpper :
      ENNReal.ofReal scheduled.rho <
        ambientConstant *
          ENNReal.ofReal
            (pureWZ2CallerGeometricRequestedScales
              caller hcallerPos hcallerLtOne hepsilonPos
              coordinateCount coordinate).1 :=
    scheduled.within_factor
  have ambientZero : ambientConstant ≠ 0 := by
    exact ne_of_gt (zero_lt_one.trans_le ambient.2.1.1)
  have ambientTop : ambientConstant ≠ ⊤ :=
    ambient.2.1.2
  have factorZero :
      (19 : ENNReal) * ambientConstant ≠ 0 :=
    mul_ne_zero (by norm_num) ambientZero
  have factorTop :
      (19 : ENNReal) * ambientConstant ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ambientTop
  refine ⟨coordinate, ?_, ?_⟩
  · exact hrequested.trans <| by
      calc
        (pureWZ2CallerGeometricRequestedScales
            caller hcallerPos hcallerLtOne hepsilonPos
            coordinateCount coordinate).1 ≤
            scheduled.rho :=
          scheduled.requested_le
        _ ≤ 19 * scheduled.rho := by
          nlinarith
  · have hnineteen :
        ENNReal.ofReal (19 * scheduled.rho) =
          (19 : ENNReal) * ENNReal.ofReal scheduled.rho := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 19)]
      norm_num
    rw [hnineteen]
    calc
      (19 : ENNReal) * ENNReal.ofReal scheduled.rho <
          (19 : ENNReal) *
            (ambientConstant *
              ENNReal.ofReal
                (pureWZ2CallerGeometricRequestedScales
                  caller hcallerPos hcallerLtOne hepsilonPos
                  coordinateCount coordinate).1) := by
        have hscaled :=
          ENNReal.mul_lt_mul_left
            (show (19 : ENNReal) ≠ 0 by norm_num)
            (show (19 : ENNReal) ≠ ⊤ by norm_num)
            hscheduledUpper
        simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
      _ <
          (19 : ENNReal) *
            (ambientConstant *
              (ENNReal.ofReal (Real.rpow caller.1 (-epsilon)) *
                ENNReal.ofReal requested.1)) := by
        have hfactor :=
          ENNReal.mul_lt_mul_left factorZero factorTop hrounding
        simpa [mul_comm, mul_left_comm, mul_assoc] using hfactor
      _ =
          ((19 : ENNReal) * ambientConstant *
            ENNReal.ofReal (Real.rpow caller.1 (-epsilon))) *
              ENNReal.ofReal requested.1 := by
        ring
      _ ≤ outputConstant * ENNReal.ofReal requested.1 := by
        gcongr

end Kakeya.Assouad

end
