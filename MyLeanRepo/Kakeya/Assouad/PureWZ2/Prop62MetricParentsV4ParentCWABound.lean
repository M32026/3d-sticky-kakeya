import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TerminalParentCWABound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4PacketCellAdapter

/-!
# Proposition 6.2 V4 terminal-parent CWA bound

This file contains only the frozen V4 wrapper around the generic terminal-parent
cardinality and CWA-constant ledger.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace Prop62PaperAudit.V4

open Kakeya.Assouad

/-- V4 CWA loss budget for the fourth paper lemma. -/
def pureWZ2Prop62FourDegreeCWALossExponent
    (inputDensityExponent inputCWAExponent : ℕ) : ℕ :=
  inputDensityExponent + 2 * inputCWAExponent + 4

@[simp] theorem pureWZ2Prop62FourDegreeCWALossExponent_eq
    (inputDensityExponent inputCWAExponent : ℕ) :
    pureWZ2Prop62FourDegreeCWALossExponent
        inputDensityExponent inputCWAExponent =
      inputDensityExponent + 2 * inputCWAExponent + 4 :=
  rfl

/-- The frozen CWA target corresponding to the budget `D + 2 * B + 4`. -/
def pureWZ2Prop62FourDegreeCWATarget
    (delta eta : ℝ)
    (inputDensityExponent inputCWAExponent : ℕ) : ENNReal :=
  Kakeya.realRpowENN delta
    (-((pureWZ2Prop62FourDegreeCWALossExponent
      inputDensityExponent inputCWAExponent : ℕ) : ℝ) * eta)

private theorem metricParentsV4_realRpowENN_inv
    {delta exponent : ℝ}
    (deltaPos : 0 < delta) :
    (Kakeya.realRpowENN delta exponent)⁻¹ =
      Kakeya.realRpowENN delta (-exponent) := by
  simp only [Kakeya.realRpowENN]
  calc
    (ENNReal.ofReal (Real.rpow delta exponent))⁻¹ =
        ENNReal.ofReal ((Real.rpow delta exponent)⁻¹) :=
      (ENNReal.ofReal_inv_of_pos
        (Real.rpow_pos_of_pos deltaPos exponent)).symm
    _ = ENNReal.ofReal (Real.rpow delta (-exponent)) :=
      congrArg ENNReal.ofReal
        (Real.rpow_neg deltaPos.le exponent).symm

variable
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {metric :
      MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
          parentConstant fiberConstant}
    (localInput : MetricParentsV4PacketCellLocalInput metric)
    {scheduleAmbientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        metric.scaleData.coarse scheduleAmbientConstant scaleWindow)
    (prefixData :
      localInput.toPacketCellInput.FourDegreePrefixData schedule)

/--
Frozen-data form of the terminal parent CWA bound.

The displayed scalar absorption is the only remaining threshold obligation.
It contains the parent input power twice: once for complete-fiber uniformity
and once in the schedule ambient CWA constant, with one additional `eta` loss
in the latter.
-/
theorem MetricParentsV4PacketCellLocalInput.terminalParentCWA_power_bound
    {A0 : ℕ}
    (core :
      localInput.toPacketCellInput.FourDegreeCoreAssemblyData
        prefixData.multiplicity prefixData.parentClass prefixData.treeCleanup
          prefixData.exactification prefixData.parentDegree prefixData.bins A0)
    (families :
      localInput.toPacketCellInput.TerminalCompleteFamiliesData
        prefixData.multiplicity prefixData.parentClass prefixData.treeCleanup
          prefixData.exactification core.ranges)
    (eta : ℝ)
    (inputDensityExponent inputCWAExponent : ℕ)
    (densityConstant_eq :
      localInput.densityConstant =
        Kakeya.realRpowENN delta
          ((inputDensityExponent : ℝ) * eta))
    (parentConstant_le :
      parentConstant ≤
        Kakeya.realRpowENN delta
          (-(inputCWAExponent : ℝ) * eta))
    (scheduleAmbientConstant_le :
      scheduleAmbientConstant ≤
        Kakeya.realRpowENN delta
          (-((inputCWAExponent : ℝ) + 1) * eta))
    (scaleWindowPower :
      scaleWindow ≤
        pureWZ2Prop62FourDegreeCWATarget delta eta
          inputDensityExponent inputCWAExponent)
    (structuralAbsorption :
      ((2 ^ schedule.levelCount * A0 : ℕ) : ENNReal) *
          (2 *
            localInput.toPacketCellInput.terminalParentSelectionLoss
              prefixData.multiplicity prefixData.parentClass *
            (55296 * Kakeya.deltaTubeVolume 1)) ≤
        Kakeya.realRpowENN delta ((-3 : ℝ) * eta)) :
    localInput.toPacketCellInput.terminalParentOutputConstant
          prefixData.multiplicity prefixData.parentClass prefixData.treeCleanup
            prefixData.exactification prefixData.parentDegree core ≤
        pureWZ2Prop62FourDegreeCWATarget delta eta
          inputDensityExponent inputCWAExponent ∧
      WZ2PaperPureCWAAtNearbyScales
        families.restriction.coarseSelected.family
        (pureWZ2Prop62FourDegreeCWATarget delta eta
          inputDensityExponent inputCWAExponent) := by
  have density :
      localInput.densityConstant *
          metric.refinement.selected.family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        metric.refinement.refined.mass := by
    have bodyLower :=
      pureWZ2_prop62_paper_body_mass_lower
        localInput.delta_pos
        (localInput.delta_le_one_hundred.trans (by norm_num))
        metric.scaleData.section6Cover.fine_line_class
    exact
      (calc
        localInput.densityConstant *
              metric.refinement.selected.family.enncard *
              Kakeya.realRpowENN delta 2 =
            localInput.densityConstant *
              (metric.refinement.selected.family.enncard *
                Kakeya.realRpowENN delta 2) := by ring
        _ ≤
            localInput.densityConstant *
              (wz1PaperBodyFamily
                metric.refinement.selected.family).mass := by
          gcongr
        _ ≤ metric.refinement.refined.mass :=
          localInput.refined_dense)
  have densityConstantPos : 0 < localInput.densityConstant :=
    localInput.densityConstant_pos
  have densityConstantFinite : localInput.densityConstant ≠ ⊤ := by
    rw [densityConstant_eq]
    simp [Kakeya.realRpowENN]
  have fullFiberUniform :
      ∀ first second : Fin metric.scaleData.coarse.card,
        (localInput.toPacketCellInput.parentFiberCard first : ENNReal) ≤
          parentConstant *
            (localInput.toPacketCellInput.parentFiberCard second : ENNReal) := by
    intro first second
    simpa only [
      PureWZ2Prop62PacketCellInput.parentFiberCard,
      wz2PaperFullFiberCount
    ] using metric.scaleData.full_fiber_uniform first second
  have selectedParentMassUpper :
      ∀ parent ∈ prefixData.parentClass.selectedParents,
        localInput.toPacketCellInput.parentClassMass
            prefixData.multiplicity parent ≤
          localInput.toPacketCellInput.parentFiberCard parent *
            (55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN delta 2 := by
    intro parent parentMem
    exact
      localInput.toPacketCellInput
        |>.selectedParentMass_le_completeFiberTubeMass
          prefixData.multiplicity prefixData.parentClass
          (localInput.delta_le_one_hundred.trans (by norm_num))
          parent parentMem
  let inputCWAPower :=
    Kakeya.realRpowENN delta
      (-(inputCWAExponent : ℝ) * eta)
  let scheduleAmbientPower :=
    Kakeya.realRpowENN delta
      (-((inputCWAExponent : ℝ) + 1) * eta)
  let structuralPower :=
    Kakeya.realRpowENN delta ((-3 : ℝ) * eta)
  have exactCoefficientBound :
      localInput.toPacketCellInput.terminalParentExactCoefficient
          prefixData.multiplicity prefixData.parentClass parentConstant
            (55296 * Kakeya.deltaTubeVolume 1) prefixData.treeCleanup
            prefixData.exactification prefixData.parentDegree core ≤
        structuralPower * inputCWAPower * scheduleAmbientPower := by
    unfold PureWZ2Prop62PacketCellInput.terminalParentExactCoefficient
    calc
      ((2 ^ schedule.levelCount * A0 : ℕ) : ENNReal) *
            (2 *
              localInput.toPacketCellInput.terminalParentSelectionLoss
                prefixData.multiplicity prefixData.parentClass *
              parentConstant *
              (55296 * Kakeya.deltaTubeVolume 1)) *
            scheduleAmbientConstant =
          (((2 ^ schedule.levelCount * A0 : ℕ) : ENNReal) *
            (2 *
              localInput.toPacketCellInput.terminalParentSelectionLoss
                prefixData.multiplicity prefixData.parentClass *
              (55296 * Kakeya.deltaTubeVolume 1))) *
            parentConstant * scheduleAmbientConstant := by ring
      _ ≤
          structuralPower * parentConstant * scheduleAmbientConstant := by
        gcongr
      _ ≤
          structuralPower * inputCWAPower * scheduleAmbientConstant := by
        gcongr
      _ ≤ structuralPower * inputCWAPower * scheduleAmbientPower := by
        gcongr
  have densityInverse :
      localInput.densityConstant⁻¹ =
        Kakeya.realRpowENN delta
          (-((inputDensityExponent : ℝ) * eta)) := by
    rw [densityConstant_eq]
    exact metricParentsV4_realRpowENN_inv localInput.delta_pos
  have exactPowerAbsorption :
      localInput.toPacketCellInput.terminalParentExactCoefficient
            prefixData.multiplicity prefixData.parentClass parentConstant
              (55296 * Kakeya.deltaTubeVolume 1)
              prefixData.treeCleanup prefixData.exactification
              prefixData.parentDegree core *
          localInput.densityConstant⁻¹ ≤
        pureWZ2Prop62FourDegreeCWATarget delta eta
          inputDensityExponent inputCWAExponent := by
    calc
      localInput.toPacketCellInput.terminalParentExactCoefficient
              prefixData.multiplicity prefixData.parentClass parentConstant
                (55296 * Kakeya.deltaTubeVolume 1)
                prefixData.treeCleanup prefixData.exactification
                prefixData.parentDegree core *
            localInput.densityConstant⁻¹ ≤
          (structuralPower * inputCWAPower * scheduleAmbientPower) *
            localInput.densityConstant⁻¹ := by
        gcongr
      _ =
          structuralPower * inputCWAPower * scheduleAmbientPower *
            Kakeya.realRpowENN delta
              (-((inputDensityExponent : ℝ) * eta)) := by
        rw [densityInverse]
      _ =
          pureWZ2Prop62FourDegreeCWATarget delta eta
            inputDensityExponent inputCWAExponent := by
        dsimp only [structuralPower, inputCWAPower, scheduleAmbientPower]
        unfold pureWZ2Prop62FourDegreeCWATarget
        rw [← realRpowENN_add localInput.delta_pos,
          ← realRpowENN_add localInput.delta_pos,
          ← realRpowENN_add localInput.delta_pos]
        congr 1
        simp only [pureWZ2Prop62FourDegreeCWALossExponent]
        push_cast
        ring
  have constantBound :=
    localInput.toPacketCellInput.terminalParentOutputConstant_le_power
      prefixData.multiplicity prefixData.parentClass prefixData.treeCleanup
      prefixData.exactification prefixData.parentDegree core eta
      (pureWZ2Prop62FourDegreeCWALossExponent
        inputDensityExponent inputCWAExponent)
      localInput.densityConstant parentConstant
      (55296 * Kakeya.deltaTubeVolume 1)
      densityConstantPos densityConstantFinite fullFiberUniform density
      selectedParentMassUpper scaleWindowPower exactPowerAbsorption
  refine ⟨constantBound, ?_⟩
  exact
    (localInput.toPacketCellInput.terminalParentCWA
      prefixData.multiplicity prefixData.parentClass prefixData.treeCleanup
        prefixData.exactification prefixData.parentDegree core families).mono
      constantBound
      (by simp [pureWZ2Prop62FourDegreeCWATarget,
        Kakeya.realRpowENN])

end Prop62PaperAudit.V4

end Kakeya.Assouad

end
