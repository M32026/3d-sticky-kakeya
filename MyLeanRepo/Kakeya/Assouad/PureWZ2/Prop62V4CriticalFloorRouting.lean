import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedCriticalFloorBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedCriticalFloorSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCriticalFloorSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperAudit.StatementsV4
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParameterSelection

/-!
# Proposition 6.2 V4 critical-floor routing

The ordinary critical package, the cropped Section 6 floor, and the
historical carrier floor are different interfaces.  This module deliberately
does not assert a global implication from the first two interfaces to the
historical one.

Instead, it records the parameter choices which are independent of the
carrier model and retains either the pure or cropped critical witness.  The
final lemmas apply those witnesses only when the concrete V4 family carries
the matching pure Definition 2.12 CWA certificate.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open Kakeya.Assouad
open MeasureTheory

def prop62V4CriticalExponentSum
    (cwaPower packetDensityExponent cwaLossExponent : ℕ) : ℝ :=
  (cwaPower : ℝ) + packetDensityExponent + cwaLossExponent + 1

def prop62V4CriticalStructuralBudget
    (cwaPower packetDensityExponent cwaLossExponent : ℕ)
    (outputLoss : ℝ) : ℝ :=
  min (wz2PaperInternalStrongLoss outputLoss)
    (outputLoss /
      (1000 *
        prop62V4CriticalExponentSum
          cwaPower packetDensityExponent cwaLossExponent))

/--
The part of the V4 final-parameter package which depends only on the selected
structural loss, not on the carrier model of the critical floor.
-/
structure Prop62V4CriticalFloorNumerics
    (polylogExponent cwaPower packetDensityExponent
      cwaLossExponent : ℕ)
    (outputLoss structuralLoss : ℝ) where
  hierarchy :
    WZ2PaperFinalLossHierarchyData outputLoss structuralLoss
  component :
    WZ2PaperFinalComponentAbsorptionData
      hierarchy.sourceLoss structuralLoss hierarchy.capLoss
      hierarchy.componentLoss outputLoss (61 + polylogExponent)
  density :
    WZ2PaperFinalFiberDensityAbsorptionData
      hierarchy.sourceLoss structuralLoss hierarchy.capLoss
      hierarchy.componentLoss hierarchy.fiberDensityLoss
      outputLoss (61 + polylogExponent)
  cap :
    WZ2PaperFinalCapAbsorptionData
      hierarchy.internalStrongLoss hierarchy.capLoss polylogExponent
  fiber :
    WZ2PaperFinalFiberGeometricAbsorptionData
      hierarchy.fiberDensityLoss hierarchy.finalStrongLoss
  metric_loss :
    (cwaPower : ℝ) * hierarchy.stableLoss ≤ outputLoss / 100
  packet_loss :
    (packetDensityExponent : ℝ) * hierarchy.stableLoss < 1
  cwa_critical_gap :
    (cwaLossExponent : ℝ) * hierarchy.stableLoss <
      outputLoss * structuralLoss
  packet_critical_gap :
    (packetDensityExponent : ℝ) * hierarchy.stableLoss <
      outputLoss * structuralLoss
  structural_final :
    structuralLoss < hierarchy.finalStrongLoss
  cwa_final_gap :
    4 * ((cwaLossExponent : ℝ) * hierarchy.stableLoss) <
      outputLoss * hierarchy.finalStrongLoss

theorem prop62V4_critical_floor_numerics
    (polylogExponent cwaPower packetDensityExponent
      cwaLossExponent : ℕ)
    (outputLoss structuralLoss : ℝ)
    (outputLossPos : 0 < outputLoss)
    (outputLossLeOne : outputLoss ≤ 1)
    (structuralLossPos : 0 < structuralLoss)
    (structuralLossInternal :
      structuralLoss ≤ wz2PaperInternalStrongLoss outputLoss)
    (structuralLossExponent :
      structuralLoss ≤
        outputLoss /
          (1000 *
            prop62V4CriticalExponentSum
              cwaPower packetDensityExponent cwaLossExponent)) :
    Nonempty
      (Prop62V4CriticalFloorNumerics
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        outputLoss structuralLoss) := by
  rcases
      wz2_paper_final_loss_hierarchy
        outputLoss structuralLoss outputLossPos outputLossLeOne
        structuralLossPos structuralLossInternal
    with ⟨hierarchy⟩
  rcases
      wz2_paper_final_component_absorption
        hierarchy.sourceLoss structuralLoss hierarchy.capLoss
        hierarchy.componentLoss outputLoss
        (61 + polylogExponent) hierarchy.component_gap_pos
    with ⟨component⟩
  rcases
      wz2_paper_final_fiber_density_absorption
        hierarchy.sourceLoss structuralLoss hierarchy.capLoss
        hierarchy.componentLoss hierarchy.fiberDensityLoss
        outputLoss (61 + polylogExponent)
        (by
          simpa [wz2PaperFinalFiberDensityGap] using
            hierarchy.density_gap_pos)
    with ⟨density⟩
  rcases
      wz2_paper_final_cap_absorption
        hierarchy.internalStrongLoss hierarchy.capLoss
        polylogExponent hierarchy.internal_cap hierarchy.capLoss_pos
    with ⟨cap⟩
  rcases
      wz2_paper_final_fiber_geometric_absorption
        hierarchy.fiberDensityLoss hierarchy.finalStrongLoss
        hierarchy.density_final
    with ⟨fiber⟩
  let exponentSum :=
    prop62V4CriticalExponentSum
      cwaPower packetDensityExponent cwaLossExponent
  have exponentSumPos : 0 < exponentSum := by
    dsimp only [exponentSum, prop62V4CriticalExponentSum]
    positivity
  have denominatorPos : 0 < (1000 : ℝ) * exponentSum :=
    mul_pos (by norm_num) exponentSumPos
  have sumBound :
      exponentSum * structuralLoss ≤ outputLoss / 1000 := by
    change
      structuralLoss ≤ outputLoss / (1000 * exponentSum)
      at structuralLossExponent
    rw [le_div_iff₀ denominatorPos] at structuralLossExponent
    dsimp only [exponentSum]
    nlinarith
  have cwaNonneg : (0 : ℝ) ≤ cwaPower := by
    exact_mod_cast Nat.zero_le cwaPower
  have packetNonneg : (0 : ℝ) ≤ packetDensityExponent := by
    exact_mod_cast Nat.zero_le packetDensityExponent
  have cwaLossNonneg : (0 : ℝ) ≤ cwaLossExponent := by
    exact_mod_cast Nat.zero_le cwaLossExponent
  have cwaLe : (cwaPower : ℝ) ≤ exponentSum := by
    dsimp only [exponentSum, prop62V4CriticalExponentSum]
    linarith
  have packetLe :
      (packetDensityExponent : ℝ) ≤ exponentSum := by
    dsimp only [exponentSum, prop62V4CriticalExponentSum]
    linarith
  have cwaLossLe :
      (cwaLossExponent : ℝ) ≤ exponentSum := by
    dsimp only [exponentSum, prop62V4CriticalExponentSum]
    linarith
  have cwaTimes :
      (cwaPower : ℝ) * structuralLoss ≤ outputLoss / 1000 :=
    (mul_le_mul_of_nonneg_right cwaLe structuralLossPos.le).trans
      sumBound
  have packetTimes :
      (packetDensityExponent : ℝ) * structuralLoss ≤
        outputLoss / 1000 :=
    (mul_le_mul_of_nonneg_right packetLe structuralLossPos.le).trans
      sumBound
  have cwaLossTimes :
      (cwaLossExponent : ℝ) * structuralLoss ≤ outputLoss / 1000 :=
    (mul_le_mul_of_nonneg_right cwaLossLe structuralLossPos.le).trans
      sumBound
  have structuralLossOne : structuralLoss ≤ 1 := by
    calc
      structuralLoss ≤ wz2PaperInternalStrongLoss outputLoss :=
        structuralLossInternal
      _ ≤ 1 := by
        dsimp only [wz2PaperInternalStrongLoss]
        nlinarith
  have stableEq :
      hierarchy.stableLoss = structuralLoss ^ 2 / 10 :=
    hierarchy.stableLoss_eq
  have structuralFinal :
      structuralLoss < hierarchy.finalStrongLoss := by
    rw [hierarchy.finalStrongLoss_eq]
    dsimp only [wz2PaperFinalStrongLoss]
    have oneLeSum : (1 : ℝ) ≤ exponentSum := by
      dsimp only [exponentSum, prop62V4CriticalExponentSum]
      linarith
    nlinarith
  refine
    ⟨{
      hierarchy := hierarchy
      component := component
      density := density
      cap := cap
      fiber := fiber
      metric_loss := ?_
      packet_loss := ?_
      cwa_critical_gap := ?_
      packet_critical_gap := ?_
      structural_final := structuralFinal
      cwa_final_gap := ?_
    }⟩
  · rw [stableEq]
    calc
      (cwaPower : ℝ) * (structuralLoss ^ 2 / 10) =
          ((cwaPower : ℝ) * structuralLoss) * structuralLoss / 10 := by
        ring
      _ ≤ (outputLoss / 1000) * structuralLoss / 10 := by
        gcongr
      _ ≤ outputLoss / 100 := by
        nlinarith
  · rw [stableEq]
    calc
      (packetDensityExponent : ℝ) * (structuralLoss ^ 2 / 10) =
          ((packetDensityExponent : ℝ) * structuralLoss) *
            structuralLoss / 10 := by
        ring
      _ ≤ (outputLoss / 1000) * structuralLoss / 10 := by
        gcongr
      _ < 1 := by
        nlinarith
  · rw [stableEq]
    calc
      (cwaLossExponent : ℝ) * (structuralLoss ^ 2 / 10) =
          ((cwaLossExponent : ℝ) * structuralLoss) *
            structuralLoss / 10 := by
        ring
      _ ≤ (outputLoss / 1000) * structuralLoss / 10 := by
        gcongr
      _ < outputLoss * structuralLoss := by
        nlinarith
  · rw [stableEq]
    calc
      (packetDensityExponent : ℝ) * (structuralLoss ^ 2 / 10) =
          ((packetDensityExponent : ℝ) * structuralLoss) *
            structuralLoss / 10 := by
        ring
      _ ≤ (outputLoss / 1000) * structuralLoss / 10 := by
        gcongr
      _ < outputLoss * structuralLoss := by
        nlinarith
  · have criticalGap :
        4 * ((cwaLossExponent : ℝ) * hierarchy.stableLoss) <
          outputLoss * structuralLoss := by
      rw [stableEq]
      calc
        4 * ((cwaLossExponent : ℝ) *
              (structuralLoss ^ 2 / 10)) =
            4 * (((cwaLossExponent : ℝ) * structuralLoss) *
              structuralLoss / 10) := by
          ring
        _ ≤ 4 * ((outputLoss / 1000) * structuralLoss / 10) := by
          gcongr
        _ < outputLoss * structuralLoss := by
          nlinarith
    exact
      criticalGap.trans
        (mul_lt_mul_of_pos_left structuralFinal outputLossPos)

/--
V4 parameter selection retaining the ordinary pure critical-floor witness
from Node 2.
-/
structure Prop62V4PureCriticalFloorRoutingData
    (polylogExponent cwaPower packetDensityExponent
      cwaLossExponent : ℕ)
    (sigma outputLoss : ℝ) where
  critical :
    PureWZ2CriticalFloorSelectionData sigma
      (wz2PaperCriticalFloorLoss outputLoss)
      (prop62V4CriticalStructuralBudget
        cwaPower packetDensityExponent cwaLossExponent outputLoss)
  numerics :
    Prop62V4CriticalFloorNumerics
      polylogExponent cwaPower packetDensityExponent cwaLossExponent
      outputLoss critical.structuralLoss

/--
V4 parameter selection retaining the cropped Section 6 critical-floor
witness.  This is the receipt directly matched by a cubical WZ shading with
pure Definition 2.12 CWA.
-/
structure Prop62V4CroppedCriticalFloorRoutingData
    (polylogExponent cwaPower packetDensityExponent
      cwaLossExponent : ℕ)
    (sigma outputLoss : ℝ) where
  critical :
    PureWZ2CroppedCriticalFloorSelectionData sigma
      (wz2PaperCriticalFloorLoss outputLoss)
      (prop62V4CriticalStructuralBudget
        cwaPower packetDensityExponent cwaLossExponent outputLoss)
  numerics :
    Prop62V4CriticalFloorNumerics
      polylogExponent cwaPower packetDensityExponent cwaLossExponent
      outputLoss critical.structuralLoss

private theorem prop62V4_critical_exponent_sum_pos
    (cwaPower packetDensityExponent cwaLossExponent : ℕ) :
    0 <
      prop62V4CriticalExponentSum
        cwaPower packetDensityExponent cwaLossExponent := by
  dsimp only [prop62V4CriticalExponentSum]
  positivity

private theorem prop62V4_critical_structural_budget_pos
    (cwaPower packetDensityExponent cwaLossExponent : ℕ)
    {outputLoss : ℝ}
    (outputLossPos : 0 < outputLoss) :
    0 <
      prop62V4CriticalStructuralBudget
        cwaPower packetDensityExponent cwaLossExponent outputLoss := by
  dsimp only [prop62V4CriticalStructuralBudget]
  apply lt_min
  · dsimp only [wz2PaperInternalStrongLoss]
    positivity
  · exact div_pos outputLossPos <| mul_pos (by norm_num) <|
      prop62V4_critical_exponent_sum_pos
        cwaPower packetDensityExponent cwaLossExponent

theorem prop62V4_pure_critical_floor_routing
    (polylogExponent cwaPower packetDensityExponent
      cwaLossExponent : ℕ)
    (sigma outputLoss : ℝ)
    (outputLossPos : 0 < outputLoss)
    (outputLossLeOne : outputLoss ≤ 1)
    (criticalFloor : PureWZ2CriticalVolumeFloor sigma) :
    Nonempty
      (Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss) := by
  have floorPos :
      0 < wz2PaperCriticalFloorLoss outputLoss := by
    dsimp only [wz2PaperCriticalFloorLoss]
    positivity
  have budgetPos :
      0 <
        prop62V4CriticalStructuralBudget
          cwaPower packetDensityExponent cwaLossExponent outputLoss :=
    prop62V4_critical_structural_budget_pos
      cwaPower packetDensityExponent cwaLossExponent outputLossPos
  rcases
      criticalFloor
        (wz2PaperCriticalFloorLoss outputLoss)
        (prop62V4CriticalStructuralBudget
          cwaPower packetDensityExponent cwaLossExponent outputLoss)
        floorPos budgetPos
    with
    ⟨structuralLoss, delta₀, structuralLossPos, structuralLossBudget,
      delta₀Pos, delta₀LeOne, volumeFloor⟩
  let critical :
      PureWZ2CriticalFloorSelectionData sigma
        (wz2PaperCriticalFloorLoss outputLoss)
        (prop62V4CriticalStructuralBudget
          cwaPower packetDensityExponent cwaLossExponent outputLoss) :=
    {
      structuralLoss := structuralLoss
      structuralLoss_pos := structuralLossPos
      structuralLoss_le := structuralLossBudget
      delta₀ := delta₀
      delta₀_pos := delta₀Pos
      delta₀_le_one := delta₀LeOne
      volume_floor := volumeFloor
    }
  have structuralLossInternal :
      structuralLoss ≤ wz2PaperInternalStrongLoss outputLoss := by
    exact structuralLossBudget.trans <| by
      unfold prop62V4CriticalStructuralBudget
      exact min_le_left _ _
  have structuralLossExponent :
      structuralLoss ≤
        outputLoss /
          (1000 *
            prop62V4CriticalExponentSum
              cwaPower packetDensityExponent cwaLossExponent) := by
    exact structuralLossBudget.trans <| by
      unfold prop62V4CriticalStructuralBudget
      exact min_le_right _ _
  rcases
      prop62V4_critical_floor_numerics
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        outputLoss structuralLoss outputLossPos outputLossLeOne
        structuralLossPos structuralLossInternal structuralLossExponent
    with ⟨numerics⟩
  exact ⟨{ critical := critical, numerics := numerics }⟩

theorem prop62V4_cropped_critical_floor_routing
    (polylogExponent cwaPower packetDensityExponent
      cwaLossExponent : ℕ)
    (sigma outputLoss : ℝ)
    (outputLossPos : 0 < outputLoss)
    (outputLossLeOne : outputLoss ≤ 1)
    (criticalFloor : HasWZ2PaperCroppedCriticalVolumeFloor sigma) :
    Nonempty
      (Prop62V4CroppedCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss) := by
  have floorPos :
      0 < wz2PaperCriticalFloorLoss outputLoss := by
    dsimp only [wz2PaperCriticalFloorLoss]
    positivity
  have budgetPos :
      0 <
        prop62V4CriticalStructuralBudget
          cwaPower packetDensityExponent cwaLossExponent outputLoss :=
    prop62V4_critical_structural_budget_pos
      cwaPower packetDensityExponent cwaLossExponent outputLossPos
  rcases
      pureWZ2_select_cropped_critical_floor
        criticalFloor floorPos budgetPos
    with ⟨critical⟩
  have structuralLossInternal :
      critical.structuralLoss ≤
        wz2PaperInternalStrongLoss outputLoss := by
    exact critical.structuralLoss_le.trans <| by
      unfold prop62V4CriticalStructuralBudget
      exact min_le_left _ _
  have structuralLossExponent :
      critical.structuralLoss ≤
        outputLoss /
          (1000 *
            prop62V4CriticalExponentSum
              cwaPower packetDensityExponent cwaLossExponent) := by
    exact critical.structuralLoss_le.trans <| by
      unfold prop62V4CriticalStructuralBudget
      exact min_le_right _ _
  rcases
      prop62V4_critical_floor_numerics
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        outputLoss critical.structuralLoss outputLossPos outputLossLeOne
        critical.structuralLoss_pos structuralLossInternal
        structuralLossExponent
    with ⟨numerics⟩
  exact ⟨{ critical := critical, numerics := numerics }⟩

theorem PureWZ2CriticalPackage.prop62V4_pure_critical_floor_routing
    {sigma outputLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (polylogExponent cwaPower packetDensityExponent
      cwaLossExponent : ℕ)
    (outputLossPos : 0 < outputLoss)
    (outputLossLeOne : outputLoss ≤ 1) :
    Nonempty
      (Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss) :=
  Kakeya.Assouad.Prop62PaperAudit.V4.prop62V4_pure_critical_floor_routing
    polylogExponent cwaPower packetDensityExponent cwaLossExponent
    sigma outputLoss outputLossPos outputLossLeOne critical.critical_floor

theorem PureWZ2CriticalPackage.prop62V4_cropped_critical_floor_routing
    {sigma outputLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (reduction : PureWZ2CroppedFloorReductionStatement)
    (polylogExponent cwaPower packetDensityExponent
      cwaLossExponent : ℕ)
    (outputLossPos : 0 < outputLoss)
    (outputLossLeOne : outputLoss ≤ 1) :
    Nonempty
      (Prop62V4CroppedCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss) :=
  Kakeya.Assouad.Prop62PaperAudit.V4.prop62V4_cropped_critical_floor_routing
    polylogExponent cwaPower packetDensityExponent cwaLossExponent
    sigma outputLoss outputLossPos outputLossLeOne
    (critical.cropped_critical_floor_of_reduction reduction)

theorem PureWZ2CriticalFloorSelectionData.v4_volume_floor_of_constant_le
    {sigma floorLoss structuralBudget delta : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss structuralBudget)
    (deltaPos : 0 < delta)
    (deltaLe : delta ≤ critical.delta₀)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (familyNonempty : family.Nonempty)
    (shading : Kakeya.Streamlined.TubeShading family)
    {constant : ENNReal}
    (cwa : WZ2PaperPureCWAAtNearbyScales family constant)
    (constantLe :
      constant ≤
        Kakeya.realRpowENN delta (-critical.structuralLoss))
    (dense :
      shading.IsLambdaDense
        (Kakeya.realRpowENN delta critical.structuralLoss)) :
    Kakeya.realRpowENN delta (sigma + floorLoss) ≤
      volume shading.union := by
  exact
    critical.volume_floor delta deltaPos deltaLe family familyNonempty
      shading
      (cwa.mono constantLe (by simp [Kakeya.realRpowENN]))
      dense

theorem PureWZ2CroppedCriticalFloorSelectionData.v4_volume_floor_of_constant_le
    {sigma floorLoss structuralBudget delta : ℝ}
    (critical :
      PureWZ2CroppedCriticalFloorSelectionData
        sigma floorLoss structuralBudget)
    (deltaPos : 0 < delta)
    (deltaLe : delta ≤ critical.delta₀)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (familyNonempty : family.Nonempty)
    (shading : WZ1PaperTubeShading family)
    {constant : ENNReal}
    (cwa : WZ2PaperPureCWAAtNearbyScales family constant)
    (constantLe :
      constant ≤
        Kakeya.realRpowENN delta (-critical.structuralLoss))
    (cubical : WZ1PaperIsCubicalShading shading)
    (dense :
      shading.IsLambdaDense
        (Kakeya.realRpowENN delta critical.structuralLoss)) :
    Kakeya.realRpowENN delta (sigma + floorLoss) ≤
      volume shading.union := by
  exact
    critical.volume_floor delta deltaPos deltaLe family familyNonempty
      shading
      (cwa.mono constantLe (by simp [Kakeya.realRpowENN]))
      cubical dense

namespace FourDegreePacketCoreData

variable
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {eta : ℝ}
    {packetDensityExponent : ℕ}
    {hdelta : 0 < delta}
    {metric :
      MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
          parentConstant fiberConstant}
    {outputParentConstant outputFiberConstant : ENNReal}
    (output :
      FourDegreePacketCoreData
        (eta := eta)
        (packetDensityExponent := packetDensityExponent)
        hdelta metric outputParentConstant outputFiberConstant)

/--
Apply the cropped critical floor directly to the pure-CWA terminal coarse
family retained by the V4 implementation ABI.
-/
theorem cropped_coarse_volume_floor
    {sigma floorLoss structuralBudget : ℝ}
    (critical :
      PureWZ2CroppedCriticalFloorSelectionData
        sigma floorLoss structuralBudget)
    (rhoCritical : rho.1 ≤ critical.delta₀)
    (constantLe :
      outputParentConstant ≤
        Kakeya.realRpowENN rho.1 (-critical.structuralLoss))
    (dense :
      output.coarseShading.IsLambdaDense
        (Kakeya.realRpowENN rho.1 critical.structuralLoss)) :
    Kakeya.realRpowENN rho.1 (sigma + floorLoss) ≤
      volume output.coarseShading.union := by
  have coarseNonempty : output.coarse.family.Nonempty := by
    let sourceIndex : Fin output.refinement.selected.family.card :=
      ⟨0, output.refined_nonempty⟩
    exact
      Nat.zero_lt_of_lt
        (output.cover.toWZ1PaperTubeCover.parent sourceIndex).isLt
  exact
    PureWZ2CroppedCriticalFloorSelectionData.v4_volume_floor_of_constant_le
      critical
      metric.rho_pos rhoCritical coarseNonempty output.coarseShading
      output.parent_cwa constantLe output.balanced.coarse_cubical dense

end FourDegreePacketCoreData

namespace RescaledMetricFiberCWAData

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {parent : Fin coarse.card}
    {rhoPos : 0 < rho}
    {constant : ENNReal}
    (fiber :
      RescaledMetricFiberCWAData cover parent rhoPos constant)

/--
Apply the cropped critical floor to the exact public ordinary family carried
by one V4 rescaled-fiber CWA receipt.
-/
theorem cropped_volume_floor
    {sigma floorLoss structuralBudget : ℝ}
    (critical :
      PureWZ2CroppedCriticalFloorSelectionData
        sigma floorLoss structuralBudget)
    (ratioCritical : delta / rho ≤ critical.delta₀)
    (constantLe :
      constant ≤
        Kakeya.realRpowENN (delta / rho) (-critical.structuralLoss))
    (targetShading :
      WZ1PaperTubeShading fiber.rescalingCertificate.publicFamily)
    (targetNonempty :
      fiber.rescalingCertificate.publicFamily.Nonempty)
    (targetCubical : WZ1PaperIsCubicalShading targetShading)
    (targetDense :
      targetShading.IsLambdaDense
        (Kakeya.realRpowENN
          (delta / rho) critical.structuralLoss)) :
    Kakeya.realRpowENN (delta / rho) (sigma + floorLoss) ≤
      volume targetShading.union := by
  exact
    PureWZ2CroppedCriticalFloorSelectionData.v4_volume_floor_of_constant_le
      critical
      (div_pos fiber.rescalingInput.delta_pos rhoPos)
      ratioCritical targetNonempty targetShading fiber.cwa
      constantLe targetCubical targetDense

end RescaledMetricFiberCWAData

end Kakeya.Assouad.Prop62PaperAudit.V4

end
