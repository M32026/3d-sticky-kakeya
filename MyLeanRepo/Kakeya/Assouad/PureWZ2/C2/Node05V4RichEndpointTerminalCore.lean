import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightEndpointInvocation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ExactMultiplicityTruncation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.RichEndpointScalarSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentLocalVolume

/-!
# Direct-rich endpoint terminal core

This module turns the one direct-rich endpoint call into the exact
literal-cell multiplicity input used by the terminal paper-order geometry.
No second sticky call or independently selected family occurs here.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

namespace PureWZ2.Proposition63RichTerminalStickyData

/-- At the square-root endpoint, the coarse-union floor and the balanced
cell-mass floor combine to give a lower bound for the literal rich fine union.
The common active-cell count is retained throughout the calculation. -/
theorem refined_union_power_lower_of_sqrt
    {delta sigma outputLoss sourceLoss normalizationLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (hrho : rho.1 = Real.sqrt delta)
    (hrhoSmall : rho.1 ≤ 1 / 12) :
    Kakeya.realRpowENN delta
        (sigma + outputLoss + rich.terminalLoss) ≤
      volume rich.data.refined.union := by
  let balanced := rich.terminal.balanced.toWZ1PaperBalancedCoverData
  let count : ENNReal := balanced.activeCells.card
  let cubeVolume : ENNReal :=
    volume (wz1PaperGridCube rho.1 (0, 0, 0))
  have hcoarse :
      Kakeya.realRpowENN rho.1 (sigma + 2 * outputLoss) ≤
        volume rich.data.croppedCoarseShading.union :=
    proposition63_sticky_coarse_union_volume_lower rich.data hrhoSmall
  have hcoarseEq : volume rich.data.croppedCoarseShading.union =
      count * cubeVolume := by
    exact balanced.coarse_union_volume rich.data.coarse_extremal.delta_pos
  have hfineEq : volume rich.data.refined.union =
      count * balanced.cellMass := by
    exact balanced.fine_union_volume
  have hcube : cubeVolume = Kakeya.realRpowENN rho.1 3 := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact
      rich.data.coarse_extremal.delta_pos]
    simp only [Kakeya.realRpowENN]
    congr 1
    norm_num [Real.rpow_natCast]
  have hproduct :
      Kakeya.realRpowENN rho.1 (sigma + 2 * outputLoss) *
          Kakeya.realRpowENN (delta / rho.1)
            (sigma + 2 * rich.terminalLoss) ≤
        volume rich.data.refined.union := by
    calc
      _ ≤ (count * cubeVolume) *
          Kakeya.realRpowENN (delta / rho.1)
            (sigma + 2 * rich.terminalLoss) :=
        mul_le_mul_right' (hcoarse.trans_eq hcoarseEq) _
      _ = count *
          (Kakeya.realRpowENN rho.1 3 *
            Kakeya.realRpowENN (delta / rho.1)
              (sigma + 2 * rich.terminalLoss)) := by
        rw [hcube]
        ring
      _ ≤ count * balanced.cellMass := by
        gcongr
        exact rich.terminal_cellMass_power_lower
      _ = volume rich.data.refined.union := hfineEq.symm
  have hdelta : 0 < delta := rich.terminal.delta_pos
  have hratio : delta / Real.sqrt delta = Real.sqrt delta := by
    apply (div_eq_iff (Real.sqrt_pos.2 hdelta).ne').2
    nlinarith [Real.sq_sqrt hdelta.le]
  have hsqrtPower (exponent : ℝ) :
      Kakeya.realRpowENN (Real.sqrt delta) exponent =
        Kakeya.realRpowENN delta (exponent / 2) := by
    simp only [Kakeya.realRpowENN, Real.sqrt_eq_rpow]
    apply congrArg ENNReal.ofReal
    calc
      (Real.rpow delta (1 / 2 : ℝ)).rpow exponent =
          Real.rpow delta ((1 / 2 : ℝ) * exponent) :=
        (Real.rpow_mul hdelta.le (1 / 2 : ℝ) exponent).symm
      _ = Real.rpow delta (exponent / 2) := by
        congr 1
        ring
  have hleft :
      Kakeya.realRpowENN rho.1 (sigma + 2 * outputLoss) *
          Kakeya.realRpowENN (delta / rho.1)
            (sigma + 2 * rich.terminalLoss) =
        Kakeya.realRpowENN delta
          (sigma + outputLoss + rich.terminalLoss) := by
    rw [hrho, hratio, hsqrtPower, hsqrtPower, ← realRpowENN_add hdelta]
    congr 1
    ring
  rw [← hleft]
  exact hproduct

end PureWZ2.Proposition63RichTerminalStickyData

namespace PureWZ2C2OrdinaryGlobalSchedule.ActualJointHeightEndpointInvocationData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2OrdinaryGlobalSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ActualJointHeightPrefixData initial}

/-- The exact multiplicity retained from the unique direct-rich endpoint
witness. -/
noncomputable def lowerFloorExactTruncation
    (endpoint : schedule.ActualJointHeightEndpointInvocationData actual) :
    PureWZ2Node05LowerFloorExactTruncationData endpoint.rich.data.refined
      endpoint.rich.terminal.delta_pos
      (endpoint.rich.terminal.fineDegreeFloor *
        endpoint.rich.terminal.muFine) :=
  pureWZ2Node05_lowerFloorExactTruncation endpoint.rich.data.refined
    endpoint.rich.terminal.delta_pos endpoint.rich.data.refined_cubical
    (endpoint.rich.terminal.fineDegreeFloor *
      endpoint.rich.terminal.muFine)
    (Nat.mul_pos endpoint.rich.terminal.fineDegreeFloor_pos
      endpoint.rich.terminal.muFine_pos)
    (fun point hpoint =>
      endpoint.rich.terminal.fine_pointMultiplicity_floor_on_union hpoint)

/-- The rich regularity band is exactly the mass cost of the lower-floor
literal-cell truncation. -/
theorem lowerFloorExactTruncation_mass_retention
    (endpoint : schedule.ActualJointHeightEndpointInvocationData actual) :
    endpoint.rich.data.refined.mass ≤
      (endpoint.rich.terminal.regularity : ENNReal) *
        endpoint.lowerFloorExactTruncation.truncated.mass := by
  apply endpoint.lowerFloorExactTruncation.mass_retention_of_upper
  intro point
  have hupper := endpoint.rich.terminal.fine_pointMultiplicity_upper point
  have hupperNat : endpoint.rich.data.refined.pointMultiplicity point ≤
      endpoint.rich.terminal.regularity *
        endpoint.rich.terminal.fineDegreeFloor *
          endpoint.rich.terminal.muFine := by
    exact_mod_cast hupper
  simpa only [mul_assoc] using hupperNat

/-- Package the unique rich endpoint as the terminal geometry input after
paying only a preselected logarithmic refinement cost. -/
noncomputable def toTerminalScaleStickyData
    (endpoint : schedule.ActualJointHeightEndpointInvocationData actual)
    (terminalLoss : ℝ) (logExponent : ℕ)
    (hendpointLoss : schedule.endpointOutputLoss ≤ terminalLoss)
    (hvolumeLoss : schedule.endpointOutputLoss +
      endpoint.rich.terminalLoss ≤ terminalLoss)
    (hrhoSmall : endpoint.sqrtRequested.1 ≤ 1 / 12)
    (hrefinement :
      (endpoint.rich.terminal.regularity : ENNReal) *
          wz2PaperPureRefinementFraction sourceDelta logExponent ≤
        wz2PaperPureRefinementFraction sourceDelta 61) :
    PureWZ2TerminalScaleStickyData actual.chain.finalSource.2.grain
      terminalLoss logExponent := by
  let truncation := endpoint.lowerFloorExactTruncation
  let balancedBase := truncation.toBalancedBase endpoint.rich.terminal.balanced
  let balanced := truncation.toNode5Balanced endpoint.rich.terminal.balanced
    (Nat.mul_pos endpoint.rich.terminal.fineDegreeFloor_pos
      endpoint.rich.terminal.muFine_pos)
    endpoint.rich.terminal.fine_cell_nested
  have hregularityZero :
      (endpoint.rich.terminal.regularity : ENNReal) ≠ 0 := by
    exact_mod_cast endpoint.rich.terminal.regularity_pos.ne'
  have hregularityTop :
      (endpoint.rich.terminal.regularity : ENNReal) ≠ ⊤ := by simp
  have hretainedScaled :
      (endpoint.rich.terminal.regularity : ENNReal) *
          (wz2PaperPureRefinementFraction sourceDelta logExponent *
            actual.chain.finalSource.2.grain.shading.mass) ≤
        (endpoint.rich.terminal.regularity : ENNReal) *
          truncation.truncated.mass := by
    calc
      _ = ((endpoint.rich.terminal.regularity : ENNReal) *
            wz2PaperPureRefinementFraction sourceDelta logExponent) *
          actual.chain.finalSource.2.grain.shading.mass := by ring
      _ ≤ wz2PaperPureRefinementFraction sourceDelta 61 *
          actual.chain.finalSource.2.grain.shading.mass := by gcongr
      _ ≤ endpoint.rich.data.refined.mass := endpoint.rich.data.retained_mass
      _ ≤ (endpoint.rich.terminal.regularity : ENNReal) *
          truncation.truncated.mass :=
        endpoint.lowerFloorExactTruncation_mass_retention
  have hretained :
      wz2PaperPureRefinementFraction sourceDelta logExponent *
          actual.chain.finalSource.2.grain.shading.mass ≤
        truncation.truncated.mass :=
    (ENNReal.mul_le_mul_iff_left hregularityZero hregularityTop).mp <| by
      simpa [mul_comm] using hretainedScaled
  have hvolumeRich :=
    endpoint.rich.refined_union_power_lower_of_sqrt
      endpoint.sqrtRequested_eq hrhoSmall
  have hdeltaOne : sourceDelta ≤ 1 :=
    actual.chain.finalSource.2.grain.extremal.delta_le_one
  have hvolumePower :
      Kakeya.realRpowENN sourceDelta (sigma + terminalLoss) ≤
        Kakeya.realRpowENN sourceDelta
          (sigma + schedule.endpointOutputLoss +
            endpoint.rich.terminalLoss) :=
    realRpowENN_antitone endpoint.rich.terminal.delta_pos hdeltaOne
      (by linarith)
  have hexactBand : truncation.truncated.HasConstantMultiplicity
      (endpoint.rich.terminal.fineDegreeFloor *
        endpoint.rich.terminal.muFine)
      (2 * (endpoint.rich.terminal.fineDegreeFloor *
        endpoint.rich.terminal.muFine)) := by
    intro point hpoint
    have hexact := truncation.exact_multiplicity point hpoint
    exact ⟨hexact.1, hexact.2.trans (by omega)⟩
  exact {
    sqrtRequested := endpoint.sqrtRequested
    sqrtRequested_eq := endpoint.sqrtRequested_eq
    sticky := {
      selected := endpoint.rich.data.selected
      selected_nonempty := endpoint.rich.data.selected_nonempty
      refined := truncation.truncated
      subshading := fun index point hpoint =>
        endpoint.rich.data.subshading index (truncation.subshading index hpoint)
      retained_mass := hretained
      refined_cubical := truncation.cubical
      coarse := endpoint.rich.data.coarse
      cover := endpoint.rich.data.cover
      croppedCoarseShading := endpoint.rich.data.croppedCoarseShading
      balancedBase := balancedBase
      balanced := balanced
      coarse_extremal :=
        endpoint.rich.data.coarse_extremal.mono_loss hendpointLoss
      fineMultiplicity := endpoint.rich.terminal.fineDegreeFloor *
        endpoint.rich.terminal.muFine
      fineMultiplicity_pos := Nat.mul_pos
        endpoint.rich.terminal.fineDegreeFloor_pos
        endpoint.rich.terminal.muFine_pos
      refined_multiplicity_band := hexactBand
      refined_volume_lower := by
        rw [truncation.union_eq]
        exact hvolumePower.trans hvolumeRich } }

end PureWZ2C2OrdinaryGlobalSchedule.ActualJointHeightEndpointInvocationData

end Kakeya.Assouad

end
