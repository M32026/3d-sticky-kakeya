import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4PureScalarInputs
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FinalAssembly
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalComponentScale
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperParentCellMassUpper

/-!
# Pure V4 final inputs

This module translates the scalar receipt selected by
`Prop62V4PureScalarInputs` into the records used by the Proposition 6.2
implementation tail.

The coarse-density field is proved from the exact canonical packet output by
the paper's parentwise argument: packet density and the complete-fiber
cardinality band are compared with the tube--cell mass upper bound.  It is not
replaced by the false global comparison between `muFine`, `fiberFloor`,
`rho^2`, and `delta^2`.

The critical coarse-volume/fiber witnesses and terminal rescaling remain
explicit.  This file does not assert an ordinary-to-cropped critical-floor
reduction and does not perform the final universal assembly.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open MeasureTheory
open Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace Prop62V4PureScalarInputs

variable
    {polylogExponent cwaPower packetDensityExponent
      cwaLossExponent : ℕ}
    {sigma outputLoss : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss}
    (scalar :
      Prop62V4PureScalarInputs
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss routing)

/-- The source-volume factor which is cancelled exactly once by the generic
product and component records. -/
def sourceVolumePower (delta : ℝ) : ENNReal :=
  Kakeya.realRpowENN delta
    (sigma - routing.numerics.hierarchy.sourceLoss)

/-- The product threshold selected by the pure scalar receipt, before the
source-volume factor is cancelled. -/
def baseDesiredProduct (delta : ℝ) : ENNReal :=
  (4 * (55296 * Kakeya.deltaTubeVolume 1)) *
    logarithmicLoss delta ^ polylogExponent *
    Kakeya.realRpowENN delta
      (2 - routing.numerics.hierarchy.sourceLoss -
        routing.numerics.hierarchy.capLoss +
        outputLoss *
          (routing.numerics.hierarchy.componentLoss +
            routing.numerics.hierarchy.capLoss))

/-- The factorized product threshold consumed by
`ProductMultiplicityInputsData`. -/
def desiredProduct (delta : ℝ) : ENNReal :=
  baseDesiredProduct (routing := routing) delta /
    sourceVolumePower (routing := routing) delta

/-- The component floor used for every terminal fine fiber. -/
def desiredFine (delta rho : ℝ) : ENNReal :=
  (55296 * Kakeya.deltaTubeVolume 1) *
    Kakeya.realRpowENN (delta / rho)
      (2 - sigma + routing.numerics.hierarchy.finalStrongLoss)

/-- The component floor used for the terminal coarse family. -/
def desiredCoarse (rho : ℝ) : ENNReal :=
  (55296 * Kakeya.deltaTubeVolume 1) *
    Kakeya.realRpowENN rho
      (2 - sigma + routing.numerics.hierarchy.finalStrongLoss)

/--
Reindex the selected pure critical witness by the larger cap-loss budget.
The structural loss, threshold, and volume-floor theorem are unchanged.
-/
def criticalForCap :
    PureWZ2CriticalFloorSelectionData sigma
      (wz2PaperCriticalFloorLoss outputLoss)
      routing.numerics.hierarchy.capLoss where
  structuralLoss := routing.critical.structuralLoss
  structuralLoss_pos := routing.critical.structuralLoss_pos
  structuralLoss_le := by
    calc
      routing.critical.structuralLoss ≤
          prop62V4CriticalStructuralBudget
            cwaPower packetDensityExponent cwaLossExponent outputLoss :=
        routing.critical.structuralLoss_le
      _ ≤ wz2PaperInternalStrongLoss outputLoss := min_le_left _ _
      _ = routing.numerics.hierarchy.internalStrongLoss :=
        routing.numerics.hierarchy.internalStrongLoss_eq.symm
      _ ≤ routing.numerics.hierarchy.capLoss :=
        routing.numerics.hierarchy.internal_cap.le
  delta₀ := routing.critical.delta₀
  delta₀_pos := routing.critical.delta₀_pos
  delta₀_le_one := routing.critical.delta₀_le_one
  volume_floor := routing.critical.volume_floor

private theorem sourceVolumePower_ne_zero
    {delta : ℝ}
    (deltaPos : 0 < delta) :
    sourceVolumePower (routing := routing) delta ≠ 0 := by
  simp [sourceVolumePower, Kakeya.realRpowENN,
    Real.rpow_pos_of_pos deltaPos]

private theorem sourceVolumePower_ne_top
    (delta : ℝ) :
    sourceVolumePower (routing := routing) delta ≠ ⊤ := by
  simp [sourceVolumePower, Kakeya.realRpowENN]

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput cover sourceShading)
    (multiplicity : input.FineMultiplicityClassData)
    (parentClass : input.ParentClassData multiplicity)
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        coarse ambientConstant scaleWindow}
    (treeCleanup :
      input.ParentTreeCleanupData
        multiplicity parentClass schedule)
    (exactification :
      input.PacketCellExactificationData
        multiplicity parentClass treeCleanup)
    (parentDegree :
      input.ReferenceParentDegreeData
        multiplicity parentClass treeCleanup exactification)
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}
    {A0 : ℕ}
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup
        exactification parentDegree bins A0)
    {degreeLoss : ℕ}
    (good : core.ranges.GoodBalancingSampleData degreeLoss)
    (families :
      input.TerminalCompleteFamiliesData
        multiplicity parentClass treeCleanup exactification
          core.ranges)
    {fiberConstant : ENNReal}
    (output :
      input.FourDegreeLemmaOutputData
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          fiberConstant
          (Kakeya.realRpowENN delta
            ((packetDensityExponent : ℝ) *
              routing.numerics.hierarchy.stableLoss))
          50)

/--
Construct the generic product input from the pure scalar absorption and the
two source estimates that belong to the preceding normalization/refinement
ledger.
-/
theorem productMultiplicityInputs
    (deltaLe : delta ≤ scalar.delta₀)
    (rhoLower : Real.rpow delta (1 - outputLoss) ≤ rho)
    (rhoUpper : rho ≤ Real.rpow delta outputLoss)
    (regularity :
      (output.coarseLoss : ENNReal) ≤
        logarithmicLoss delta ^ polylogExponent)
    (sourceMassLower :
      wz1PaperRefinementFraction delta 11 *
            Kakeya.realRpowENN delta
              routing.numerics.hierarchy.sourceLoss *
            families.restriction.fineSelected.family.enncard *
            Kakeya.realRpowENN delta 2 ≤
        sourceShading.mass)
    (sourceVolumeUpper :
      volume sourceShading.union ≤
        sourceVolumePower (routing := routing) delta) :
    PureWZ2Prop62PacketCellInput.FourDegreeLemmaOutputData.ProductMultiplicityInputsData
      input multiplicity parentClass treeCleanup exactification
        parentDegree core families
        (logExponent := 50)
        (desiredProduct (routing := routing) delta)
        (wz1PaperRefinementFraction delta 11 *
          Kakeya.realRpowENN delta
            routing.numerics.hierarchy.sourceLoss *
          families.restriction.fineSelected.family.enncard *
          Kakeya.realRpowENN delta 2)
        (sourceVolumePower (routing := routing) delta) := by
  have volumeZero :
      sourceVolumePower (routing := routing) delta ≠ 0 :=
    sourceVolumePower_ne_zero (routing := routing) input.delta_pos
  have volumeTop :
      sourceVolumePower (routing := routing) delta ≠ ⊤ :=
    sourceVolumePower_ne_top (routing := routing) delta
  have productAbsorption :
      baseDesiredProduct (routing := routing) delta ≤
        wz1PaperRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            routing.numerics.hierarchy.sourceLoss *
          Kakeya.realRpowENN delta 2 := by
    simpa [baseDesiredProduct] using
      scalar.product_absorption input.delta_pos deltaLe input.rho_pos
        rhoLower rhoUpper regularity
  refine
    {
      mass_lower := sourceMassLower
      source_volume_upper := sourceVolumeUpper
      volume_ne_zero := volumeZero
      volume_ne_top := volumeTop
      desired_product_power := ?_
    }
  calc
    (desiredProduct (routing := routing) delta *
          families.restriction.fineSelected.family.enncard) *
          sourceVolumePower (routing := routing) delta =
        baseDesiredProduct (routing := routing) delta *
          families.restriction.fineSelected.family.enncard := by
      rw [desiredProduct]
      calc
        ((baseDesiredProduct (routing := routing) delta /
              sourceVolumePower (routing := routing) delta) *
            families.restriction.fineSelected.family.enncard) *
            sourceVolumePower (routing := routing) delta =
          (baseDesiredProduct (routing := routing) delta /
              sourceVolumePower (routing := routing) delta) *
            sourceVolumePower (routing := routing) delta *
            families.restriction.fineSelected.family.enncard := by ring
        _ =
          baseDesiredProduct (routing := routing) delta *
            families.restriction.fineSelected.family.enncard := by
          rw [ENNReal.div_mul_cancel volumeZero volumeTop]
    _ ≤
        (wz1PaperRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            routing.numerics.hierarchy.sourceLoss *
          Kakeya.realRpowENN delta 2) *
          families.restriction.fineSelected.family.enncard := by
      gcongr
    _ ≤
        wz2PaperPureRefinementFraction delta 50 *
          (wz1PaperRefinementFraction delta 11 *
            Kakeya.realRpowENN delta
              routing.numerics.hierarchy.sourceLoss *
            families.restriction.fineSelected.family.enncard *
            Kakeya.realRpowENN delta 2) := by
      simp only [wz2PaperPureRefinementFraction,
        wz1PaperRefinementFraction]
      rw [show 61 = 50 + 11 by norm_num, pow_add]
      exact le_of_eq (by ring)

/--
Construct the factorized component floors by cancelling the same positive,
finite source-volume power used in `desiredProduct`.
-/
theorem componentMultiplicityFloorInputs
    (deltaLe : delta ≤ scalar.delta₀)
    (rhoLower : Real.rpow delta (1 - outputLoss) ≤ rho)
    (rhoUpper : rho ≤ Real.rpow delta outputLoss)
    (regularity :
      (output.coarseLoss : ENNReal) ≤
        logarithmicLoss delta ^ polylogExponent) :
    output.ComponentMultiplicityFloorInputsData
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families
        (criticalForCap (routing := routing))
        (desiredProduct (routing := routing) delta)
        (desiredFine (routing := routing) delta rho)
        (desiredCoarse (routing := routing) rho) := by
  have deltaOne : delta ≤ 1 :=
    deltaLe.trans <| scalar.delta₀_le_one_hundred.trans (by norm_num)
  have lossNonnegative :
      0 ≤
        routing.numerics.hierarchy.finalStrongLoss +
          routing.numerics.hierarchy.capLoss := by
    linarith [
      routing.numerics.hierarchy.finalStrongLoss_pos,
      routing.numerics.hierarchy.capLoss_pos
    ]
  have componentLtFinal :
      routing.numerics.hierarchy.componentLoss <
        routing.numerics.hierarchy.finalStrongLoss := by
    have componentLtDensity :
        routing.numerics.hierarchy.componentLoss <
          routing.numerics.hierarchy.fiberDensityLoss := by
      have outputLossPos : 0 < outputLoss := by
        nlinarith [
          routing.numerics.hierarchy.finalStrongLoss_pos,
          routing.numerics.hierarchy.final_output_budget
        ]
      nlinarith [
        routing.numerics.hierarchy.density_gap_pos,
        routing.numerics.hierarchy.sourceLoss_pos,
        routing.critical.structuralLoss_pos,
        routing.numerics.hierarchy.capLoss_pos
      ]
    exact componentLtDensity.trans
      routing.numerics.hierarchy.density_final
  have exponentComparison :
      2 - routing.numerics.hierarchy.sourceLoss -
            routing.numerics.hierarchy.capLoss +
            outputLoss *
              (routing.numerics.hierarchy.componentLoss +
                routing.numerics.hierarchy.capLoss) ≤
        2 - routing.numerics.hierarchy.sourceLoss -
            routing.numerics.hierarchy.capLoss +
            outputLoss *
              (routing.numerics.hierarchy.finalStrongLoss +
                routing.numerics.hierarchy.capLoss) := by
    have outputLossPos : 0 < outputLoss := by
      nlinarith [
        routing.numerics.hierarchy.finalStrongLoss_pos,
        routing.numerics.hierarchy.final_output_budget
      ]
    nlinarith
  have finalPowerLeComponentPower :
      Kakeya.realRpowENN delta
          (2 - routing.numerics.hierarchy.sourceLoss -
            routing.numerics.hierarchy.capLoss +
            outputLoss *
              (routing.numerics.hierarchy.finalStrongLoss +
                routing.numerics.hierarchy.capLoss)) ≤
        Kakeya.realRpowENN delta
          (2 - routing.numerics.hierarchy.sourceLoss -
            routing.numerics.hierarchy.capLoss +
            outputLoss *
              (routing.numerics.hierarchy.componentLoss +
                routing.numerics.hierarchy.capLoss)) :=
    pure_wz2_rpowENN_antitone
      input.delta_pos deltaOne exponentComparison
  have coefficientBound :
      (2 : ENNReal) * output.coarseLoss ≤
        4 * logarithmicLoss delta ^ polylogExponent := by
    calc
      (2 : ENNReal) * output.coarseLoss ≤
          2 * logarithmicLoss delta ^ polylogExponent := by
        gcongr
      _ ≤ 4 * logarithmicLoss delta ^ polylogExponent := by
        exact mul_le_mul_right' (by norm_num : (2 : ENNReal) ≤ 4) _
  have fineScale :=
    wz2_paper_final_fine_component_scale
      (sigma := sigma)
      (sourceLoss := routing.numerics.hierarchy.sourceLoss)
      (capLoss := routing.numerics.hierarchy.capLoss)
      (componentFloorLoss :=
        routing.numerics.hierarchy.finalStrongLoss)
      (outputLoss := outputLoss)
      input.delta_pos input.rho_pos rhoLower lossNonnegative
  have coarseScale :=
    wz2_paper_final_coarse_component_scale
      (sigma := sigma)
      (sourceLoss := routing.numerics.hierarchy.sourceLoss)
      (capLoss := routing.numerics.hierarchy.capLoss)
      (componentFloorLoss :=
        routing.numerics.hierarchy.finalStrongLoss)
      (outputLoss := outputLoss)
      input.delta_pos input.rho_pos rhoUpper lossNonnegative
  have fineUncancelled :
      ((desiredFine (routing := routing) delta rho * 2) *
          ((output.coarseLoss : ENNReal) *
            Kakeya.realRpowENN rho
              (2 - sigma -
                routing.numerics.hierarchy.capLoss))) *
          sourceVolumePower (routing := routing) delta ≤
        baseDesiredProduct (routing := routing) delta := by
    calc
      _ =
          ((2 : ENNReal) * output.coarseLoss) *
            ((55296 * Kakeya.deltaTubeVolume 1) *
              (Kakeya.realRpowENN (delta / rho)
                  (2 - sigma +
                    routing.numerics.hierarchy.finalStrongLoss) *
                Kakeya.realRpowENN rho
                  (2 - sigma -
                    routing.numerics.hierarchy.capLoss) *
                Kakeya.realRpowENN delta
                  (sigma -
                    routing.numerics.hierarchy.sourceLoss))) := by
        simp only [desiredFine, sourceVolumePower]
        ring
      _ ≤
          (4 * logarithmicLoss delta ^ polylogExponent) *
            ((55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN delta
                (2 - routing.numerics.hierarchy.sourceLoss -
                  routing.numerics.hierarchy.capLoss +
                  outputLoss *
                    (routing.numerics.hierarchy.finalStrongLoss +
                      routing.numerics.hierarchy.capLoss))) := by
        exact mul_le_mul coefficientBound
          (mul_le_mul_left' fineScale _) bot_le bot_le
      _ ≤
          (4 * logarithmicLoss delta ^ polylogExponent) *
            ((55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN delta
                (2 - routing.numerics.hierarchy.sourceLoss -
                  routing.numerics.hierarchy.capLoss +
                  outputLoss *
                    (routing.numerics.hierarchy.componentLoss +
                      routing.numerics.hierarchy.capLoss))) := by
        exact mul_le_mul_left'
          (mul_le_mul_left' finalPowerLeComponentPower _) _
      _ = baseDesiredProduct (routing := routing) delta := by
        simp only [baseDesiredProduct]
        ring
  have coarseUncancelled :
      (desiredCoarse (routing := routing) rho *
          (((output.coarseLoss : ENNReal) *
            Kakeya.realRpowENN (delta / rho)
              (2 - sigma -
                routing.numerics.hierarchy.capLoss)) * 2)) *
          sourceVolumePower (routing := routing) delta ≤
        baseDesiredProduct (routing := routing) delta := by
    calc
      _ =
          ((2 : ENNReal) * output.coarseLoss) *
            ((55296 * Kakeya.deltaTubeVolume 1) *
              (Kakeya.realRpowENN rho
                  (2 - sigma +
                    routing.numerics.hierarchy.finalStrongLoss) *
                Kakeya.realRpowENN (delta / rho)
                  (2 - sigma -
                    routing.numerics.hierarchy.capLoss) *
                Kakeya.realRpowENN delta
                  (sigma -
                    routing.numerics.hierarchy.sourceLoss))) := by
        simp only [desiredCoarse, sourceVolumePower]
        ring
      _ ≤
          (4 * logarithmicLoss delta ^ polylogExponent) *
            ((55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN delta
                (2 - routing.numerics.hierarchy.sourceLoss -
                  routing.numerics.hierarchy.capLoss +
                  outputLoss *
                    (routing.numerics.hierarchy.finalStrongLoss +
                      routing.numerics.hierarchy.capLoss))) := by
        exact mul_le_mul coefficientBound
          (mul_le_mul_left' coarseScale _) bot_le bot_le
      _ ≤
          (4 * logarithmicLoss delta ^ polylogExponent) *
            ((55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN delta
                (2 - routing.numerics.hierarchy.sourceLoss -
                  routing.numerics.hierarchy.capLoss +
                  outputLoss *
                    (routing.numerics.hierarchy.componentLoss +
                      routing.numerics.hierarchy.capLoss))) := by
        exact mul_le_mul_left'
          (mul_le_mul_left' finalPowerLeComponentPower _) _
      _ = baseDesiredProduct (routing := routing) delta := by
        simp only [baseDesiredProduct]
        ring
  refine
    {
      fine_scalar := ?_
      coarse_scalar := ?_
    }
  · exact
      (ENNReal.le_div_iff_mul_le
        (Or.inl <| sourceVolumePower_ne_zero
          (routing := routing) input.delta_pos)
        (Or.inl <| sourceVolumePower_ne_top
          (routing := routing) delta)).2
        fineUncancelled
  · exact
      (ENNReal.le_div_iff_mul_le
        (Or.inl <| sourceVolumePower_ne_zero
          (routing := routing) input.delta_pos)
        (Or.inl <| sourceVolumePower_ne_top
          (routing := routing) delta)).2
        coarseUncancelled

/--
The canonical component floors absorb the quadratic tube-volume constants
exactly.  No critical-floor or CWA input is used here.
-/
theorem extremalVolumeAbsorption
    (_deltaLe : delta ≤ scalar.delta₀)
    (deltaPos : 0 < delta)
    (rhoPos : 0 < rho) :
    PureWZ2Prop62PacketCellInput.FourDegreeLemmaOutputData.ExtremalVolumeAbsorptionData
      (delta := delta) (rho := rho)
      (desiredFine (routing := routing) delta rho)
      (desiredCoarse (routing := routing) rho)
      (Kakeya.realRpowENN (delta / rho)
        (sigma - routing.numerics.hierarchy.finalStrongLoss))
      (Kakeya.realRpowENN rho
        (sigma - routing.numerics.hierarchy.finalStrongLoss)) := by
  have ratioPos : 0 < delta / rho :=
    div_pos deltaPos rhoPos
  refine
    {
      coarse_scalar := ?_
      fine_scalar := ?_
    }
  · apply le_of_eq
    calc
      (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN rho 2 =
          (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN rho
              ((2 - sigma +
                routing.numerics.hierarchy.finalStrongLoss) +
                (sigma -
                  routing.numerics.hierarchy.finalStrongLoss)) := by
        congr 2
        ring
      _ =
          (55296 * Kakeya.deltaTubeVolume 1) *
            (Kakeya.realRpowENN rho
                (2 - sigma +
                  routing.numerics.hierarchy.finalStrongLoss) *
              Kakeya.realRpowENN rho
                (sigma -
                  routing.numerics.hierarchy.finalStrongLoss)) := by
        rw [realRpowENN_add rhoPos]
      _ =
          desiredCoarse (routing := routing) rho *
            Kakeya.realRpowENN rho
              (sigma -
                routing.numerics.hierarchy.finalStrongLoss) := by
        simp only [desiredCoarse]
        ring
  · apply le_of_eq
    calc
      (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN (delta / rho) 2 =
          (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN (delta / rho)
              ((2 - sigma +
                routing.numerics.hierarchy.finalStrongLoss) +
                (sigma -
                  routing.numerics.hierarchy.finalStrongLoss)) := by
        congr 2
        ring
      _ =
          (55296 * Kakeya.deltaTubeVolume 1) *
            (Kakeya.realRpowENN (delta / rho)
                (2 - sigma +
                  routing.numerics.hierarchy.finalStrongLoss) *
              Kakeya.realRpowENN (delta / rho)
                (sigma -
                  routing.numerics.hierarchy.finalStrongLoss)) := by
        rw [realRpowENN_add ratioPos]
      _ =
          desiredFine (routing := routing) delta rho *
            Kakeya.realRpowENN (delta / rho)
              (sigma -
                routing.numerics.hierarchy.finalStrongLoss) := by
        simp only [desiredFine]
        ring

private def coarseDensityParentActiveCells
    (parent : Fin families.restriction.coarseSelected.family.card) :
    Finset WZ2PaperCellIndex :=
  output.balanced.activeCells.filter fun cell =>
    wz1PaperGridCube rho cell ⊆
      output.coarseShading.carrier parent

private theorem coarseDensity_coarseCarrier_eq
    (parent : Fin families.restriction.coarseSelected.family.card) :
    output.coarseShading.carrier parent =
      ⋃ cell ∈
          coarseDensityParentActiveCells
            input multiplicity parentClass treeCleanup exactification
              parentDegree core good families output parent,
        wz1PaperGridCube rho cell := by
  ext point
  constructor
  · intro pointMem
    have pointUnion : point ∈ output.coarseShading.union :=
      ⟨parent, pointMem⟩
    rw [output.balanced.coarse_union_eq] at pointUnion
    rcases Set.mem_iUnion₂.mp pointUnion with
      ⟨cell, cellActive, pointCell⟩
    have cellIndex :
        wz1PaperGridIndex rho point = cell :=
      (mem_wz1PaperGridCube rho cell point).mp pointCell
    have wholeCell :
        wz1PaperGridCube rho cell ⊆
          output.coarseShading.carrier parent := by
      simpa only [cellIndex] using
        output.balanced.coarse_cubical parent point pointMem
    exact
      Set.mem_iUnion₂.mpr
        ⟨cell, Finset.mem_filter.mpr ⟨cellActive, wholeCell⟩,
          pointCell⟩
  · intro pointMem
    rcases Set.mem_iUnion₂.mp pointMem with
      ⟨cell, cellMem, pointCell⟩
    exact (Finset.mem_filter.mp cellMem).2 pointCell

private theorem coarseDensity_fullFiber_support
    (parent : Fin families.restriction.coarseSelected.family.card)
    (index :
      Fin
        (families.terminalFiber
          input multiplicity parentClass treeCleanup exactification
            parentDegree core parent).family.card) :
    (output.terminalFiberShading
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent).carrier index ⊆
      ⋃ cell ∈
          coarseDensityParentActiveCells
            input multiplicity parentClass treeCleanup exactification
              parentDegree core good families output parent,
        wz1PaperGridCube rho cell := by
  intro point pointMem
  let fiber :=
    families.terminalFiber
      input multiplicity parentClass treeCleanup exactification
        parentDegree core parent
  have sourceCovered :
      WZ1PaperTubeCovers
        (families.restriction.fineSelected.family.tube
          (fiber.embedding index))
        (families.restriction.coarseSelected.family.tube parent) := by
    simpa only [fiber, fiber.tube_eq] using
      output.terminalFiber_covered
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent index
  have ambientPoint :
      point ∈ output.fineShading.carrier (fiber.embedding index) :=
    pointMem
  have coarseMem :
      point ∈ output.coarseShading.carrier parent :=
    output.balanced.point_compatibility
      (fiber.embedding index) parent sourceCovered point ambientPoint
  rw [
    coarseDensity_coarseCarrier_eq
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families output parent
  ] at coarseMem
  exact coarseMem

private theorem coarseDensity_fullFiber_mass_upper
    (parent : Fin families.restriction.coarseSelected.family.card) :
    (output.terminalFiberShading
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent).mass ≤
      (families.terminalFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core parent).family.enncard *
        ((coarseDensityParentActiveCells
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families output parent).card :
          ENNReal) *
        ENNReal.ofReal (288 * delta ^ 2 * rho) := by
  let fiber :=
    families.terminalFiber
      input multiplicity parentClass treeCleanup exactification
        parentDegree core parent
  let fiberShading :=
    output.terminalFiberShading
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent
  let cells :=
    coarseDensityParentActiveCells
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families output parent
  let cellBound := ENNReal.ofReal (288 * delta ^ 2 * rho)
  have carrierMass :
      ∀ index : Fin fiber.family.card,
        volume (fiberShading.carrier index) ≤
          (cells.card : ENNReal) * cellBound := by
    intro index
    have carrierPartition :
        fiberShading.carrier index =
          ⋃ cell ∈ cells,
            fiberShading.carrier index ∩
              wz1PaperGridCube rho cell := by
      ext point
      constructor
      · intro pointMem
        rcases
            Set.mem_iUnion₂.mp
              (coarseDensity_fullFiber_support
                input multiplicity parentClass treeCleanup exactification
                  parentDegree core good families output parent index
                  pointMem)
          with ⟨cell, cellMem, pointCell⟩
        exact
          Set.mem_iUnion₂.mpr
            ⟨cell, cellMem, pointMem, pointCell⟩
      · intro pointCells
        rcases Set.mem_iUnion₂.mp pointCells with
          ⟨_cell, _cellMem, pointMem, _pointCell⟩
        exact pointMem
    calc
      volume (fiberShading.carrier index) =
          volume
            (⋃ cell ∈ cells,
              fiberShading.carrier index ∩
                wz1PaperGridCube rho cell) :=
        congrArg volume carrierPartition
      _ ≤
          ∑ cell ∈ cells,
            volume
              (fiberShading.carrier index ∩
                wz1PaperGridCube rho cell) :=
        MeasureTheory.measure_biUnion_finset_le cells _
      _ ≤ ∑ _cell ∈ cells, cellBound := by
        exact Finset.sum_le_sum fun cell _ => by
          have carrierSubset :
              fiberShading.carrier index ⊆
                wz1PaperTubeCarrier (fiber.family.tube index) :=
            fiberShading.subset_body index
          exact
            (measure_mono
              (Set.inter_subset_inter
                carrierSubset Set.Subset.rfl)).trans
              (wz2_paper_tube_cell_intersection_volume
                input.delta_pos input.rho_pos
                (fiber.family.tube index) cell)
      _ = (cells.card : ENNReal) * cellBound := by
        simp [Finset.sum_const]
  calc
    fiberShading.mass =
        ∑ index : Fin fiber.family.card,
          volume (fiberShading.carrier index) := rfl
    _ ≤
        ∑ _index : Fin fiber.family.card,
          (cells.card : ENNReal) * cellBound :=
      Finset.sum_le_sum fun index _ => carrierMass index
    _ =
        fiber.family.enncard * (cells.card : ENNReal) *
          cellBound := by
      simp [Kakeya.Streamlined.TubeFamily.enncard,
        Finset.sum_const]
      ring

private theorem coarseDensity_coarseCarrier_volume
    (parent : Fin families.restriction.coarseSelected.family.card) :
    volume (output.coarseShading.carrier parent) =
      ((coarseDensityParentActiveCells
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families output parent).card :
        ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  rw [
    coarseDensity_coarseCarrier_eq
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families output parent
  ]
  exact
    wz1PaperGridCube_volume_biUnion input.rho_pos
      (coarseDensityParentActiveCells
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families output parent)

/--
The paper's coarse-density argument on the exact canonical output.

The only scalar input is the reduced estimate at the requested exponent.
The geometric part is proved parent by parent from the packet-density lower
bound and the `288 * delta^2 * rho` tube--cell intersection estimate.
-/
theorem coarseDensityOfReduced
    (rhoSmall : rho ≤ 1 / 24)
    (coarseLoss : ℝ)
    (reduced :
      (576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) *
          Kakeya.realRpowENN rho coarseLoss ≤
        Kakeya.realRpowENN delta
          ((packetDensityExponent : ℝ) *
            routing.numerics.hierarchy.stableLoss)) :
    output.coarseShading.IsLambdaDense
      (Kakeya.realRpowENN rho coarseLoss) := by
  let lambda := Kakeya.realRpowENN rho coarseLoss
  let fiberFloor : ENNReal := output.fiberFloor
  let cellBound : ENNReal :=
    ENNReal.ofReal (288 * delta ^ 2 * rho)
  let cellVolume : ENNReal :=
    volume (wz1PaperGridCube rho (0, 0, 0))
  let bodyBound : ENNReal :=
    (55296 * Kakeya.deltaTubeVolume 1) *
      Kakeya.realRpowENN rho 2
  let packetCoefficient : ENNReal :=
    Kakeya.realRpowENN delta
        ((packetDensityExponent : ℝ) *
          routing.numerics.hierarchy.stableLoss) *
      Kakeya.realRpowENN delta 2
  have fiberFloorZero : fiberFloor ≠ 0 := by
    dsimp only [fiberFloor]
    exact_mod_cast output.fiberFloor_pos.ne'
  have factorZero : 2 * cellBound ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · change ENNReal.ofReal (288 * delta ^ 2 * rho) ≠ 0
      apply (ENNReal.ofReal_pos.mpr ?_).ne'
      exact
        mul_pos
          (mul_pos (by norm_num) (sq_pos_of_pos input.delta_pos))
          input.rho_pos
  have factorTop : 2 * cellBound ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have deltaSquare :
      ENNReal.ofReal (delta ^ 2) =
        Kakeya.realRpowENN delta 2 := by
    simp [Kakeya.realRpowENN]
  have rhoPower :
      ENNReal.ofReal (rho ^ 3) = cellVolume := by
    dsimp only [cellVolume]
    exact (wz1PaperGridCube_volume_exact input.rho_pos).symm
  have cellBoundEq :
      cellBound =
        (288 : ENNReal) *
          Kakeya.realRpowENN delta 2 *
          ENNReal.ofReal rho := by
    dsimp only [cellBound]
    rw [ENNReal.ofReal_mul
      (by positivity : 0 ≤ 288 * delta ^ 2)]
    rw [ENNReal.ofReal_mul
      (by norm_num : (0 : ℝ) ≤ 288), deltaSquare]
    norm_num
  have rhoCube :
      ENNReal.ofReal rho *
          Kakeya.realRpowENN rho 2 =
        ENNReal.ofReal (rho ^ 3) := by
    simp [Kakeya.realRpowENN,
      ← ENNReal.ofReal_mul input.rho_pos.le]
    ring
  have packetScalar :
      (2 * cellBound) * (lambda * bodyBound) ≤
        packetCoefficient * cellVolume := by
    calc
      (2 * cellBound) * (lambda * bodyBound) =
          ((576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) *
              lambda) *
            Kakeya.realRpowENN delta 2 *
            (ENNReal.ofReal rho *
              Kakeya.realRpowENN rho 2) := by
        rw [cellBoundEq]
        dsimp only [bodyBound]
        norm_num
        ring
      _ =
          ((576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) *
              lambda) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (rho ^ 3) := by
        rw [rhoCube]
      _ ≤
          Kakeya.realRpowENN delta
              ((packetDensityExponent : ℝ) *
                routing.numerics.hierarchy.stableLoss) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (rho ^ 3) := by
        gcongr
      _ = packetCoefficient * cellVolume := by
        rw [rhoPower]
  have parentDensity :
      ∀ parent :
          Fin families.restriction.coarseSelected.family.card,
        lambda *
            volume
              (wz1PaperTubeCarrier
                (families.restriction.coarseSelected.family.tube
                  parent)) ≤
          volume (output.coarseShading.carrier parent) := by
    intro parent
    let cells :=
      coarseDensityParentActiveCells
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families output parent
    let fiber :=
      families.terminalFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core parent
    have bodyUpper :
        volume
            (wz1PaperTubeCarrier
              (families.restriction.coarseSelected.family.tube
                parent)) ≤
          bodyBound :=
      (wz2PaperTubeCarrier_convex_and_volume_quadratic
        wz2_paper_tube_carrier_geometry input.rho_pos rhoSmall
        (families.restriction.coarseSelected.family.tube parent)
        (families.restriction.section6Cover.coarse_line_class
          parent)).2
    have packetLower :
        packetCoefficient * fiberFloor ≤
          (output.terminalFiberShading
            input multiplicity parentClass treeCleanup exactification
              parentDegree core good families parent).mass := by
      rw [
        output.terminalFiberShading_mass
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families parent
      ]
      calc
        packetCoefficient * fiberFloor =
            Kakeya.realRpowENN delta
                ((packetDensityExponent : ℝ) *
                  routing.numerics.hierarchy.stableLoss) *
              (output.fiberFloor : ENNReal) *
              Kakeya.realRpowENN delta 2 := by
          dsimp only [packetCoefficient, fiberFloor]
          ring
        _ ≤ _ := output.packet_density parent
    have fiberMassUpper :
        (output.terminalFiberShading
            input multiplicity parentClass treeCleanup exactification
              parentDegree core good families parent).mass ≤
          (2 * fiberFloor * cellBound) *
            (cells.card : ENNReal) := by
      calc
        _ ≤
            fiber.family.enncard *
              (cells.card : ENNReal) * cellBound :=
          coarseDensity_fullFiber_mass_upper
            input multiplicity parentClass treeCleanup exactification
              parentDegree core good families output parent
        _ ≤
            (2 * fiberFloor) *
              (cells.card : ENNReal) * cellBound := by
          gcongr
          change
            ((wz2PaperFullFiberIndices
              families.restriction.fineSelected.family
              families.restriction.coarseSelected.family
              parent).card : ENNReal) ≤
                2 * (output.fiberFloor : ENNReal)
          exact_mod_cast (output.fiber_cardinality parent).2.le
        _ =
            (2 * fiberFloor * cellBound) *
              (cells.card : ENNReal) := by
          ring
    have packetLe :
        packetCoefficient ≤
          2 * cellBound * (cells.card : ENNReal) := by
      apply
        (ENNReal.mul_le_mul_iff_right
          fiberFloorZero (ENNReal.natCast_ne_top _)).mp
      calc
        fiberFloor * packetCoefficient =
            packetCoefficient * fiberFloor := by ring
        _ ≤ _ := packetLower
        _ ≤ _ := fiberMassUpper
        _ =
            fiberFloor *
              (2 * cellBound * (cells.card : ENNReal)) := by
          ring
    have scaled :
        (2 * cellBound) *
            (lambda *
              volume
                (wz1PaperTubeCarrier
                  (families.restriction.coarseSelected.family.tube
                    parent))) ≤
          (2 * cellBound) *
            ((cells.card : ENNReal) * cellVolume) := by
      calc
        _ ≤ (2 * cellBound) * (lambda * bodyBound) := by
          gcongr
        _ ≤ packetCoefficient * cellVolume := packetScalar
        _ ≤
            (2 * cellBound * (cells.card : ENNReal)) *
              cellVolume := by
          gcongr
        _ =
            (2 * cellBound) *
              ((cells.card : ENNReal) * cellVolume) := by
          ring
    apply
      (ENNReal.mul_le_mul_iff_left factorZero factorTop).mp
    rw [
      coarseDensity_coarseCarrier_volume
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families output parent
    ]
    simpa [mul_comm] using scaled
  rw [Kakeya.Streamlined.Shading.IsLambdaDense]
  change
    lambda *
        (∑ parent :
            Fin families.restriction.coarseSelected.family.card,
          volume
            (wz1PaperTubeCarrier
              (families.restriction.coarseSelected.family.tube
                parent))) ≤
      output.coarseShading.mass
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun parent _ => parentDensity parent

/-- The final-strong-loss specialization used by the V4 final output. -/
theorem finalCoarseDensity
    (deltaLe : delta ≤ scalar.delta₀)
    (rhoLeOne : rho ≤ 1)
    (rhoUpper : rho ≤ Real.rpow delta outputLoss) :
    output.coarseShading.IsLambdaDense
      (Kakeya.realRpowENN rho
        routing.numerics.hierarchy.finalStrongLoss) := by
  have densityPower :
      Kakeya.realRpowENN rho
          routing.numerics.hierarchy.finalStrongLoss ≤
        Kakeya.realRpowENN rho
          routing.critical.structuralLoss :=
    pure_wz2_rpowENN_antitone
      input.rho_pos rhoLeOne scalar.structural_to_final
  apply
    coarseDensityOfReduced
      (routing := routing)
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families output
      (scalar.rho_small input.delta_pos deltaLe rhoUpper)
      routing.numerics.hierarchy.finalStrongLoss
  calc
    (576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) *
          Kakeya.realRpowENN rho
            routing.numerics.hierarchy.finalStrongLoss ≤
        (576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) *
          Kakeya.realRpowENN rho
            routing.critical.structuralLoss := by
      gcongr
    _ ≤ _ :=
      scalar.coarse_density
        input.delta_pos deltaLe input.rho_pos rhoUpper

/-- V4 final inputs with coarse density proved directly from packet geometry. -/
structure Prop62V4FinalAssemblyInputsData
    {floorLoss capLoss : ℝ}
    (assemblyLoss : ℝ)
    (critical :
      PureWZ2CriticalFloorSelectionData sigma floorLoss capLoss)
    (criticalInputs :
      output.CriticalMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families critical)
    {desiredProduct massLower sourceVolumeUpper
      desiredFine desiredCoarse : ENNReal}
    (productInputs :
      PureWZ2Prop62PacketCellInput.FourDegreeLemmaOutputData.ProductMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families
          (logExponent := 50)
          desiredProduct massLower sourceVolumeUpper)
    (componentInputs :
      output.ComponentMultiplicityFloorInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          critical desiredProduct desiredFine desiredCoarse)
    (volumeAbsorption :
      PureWZ2Prop62PacketCellInput.FourDegreeLemmaOutputData.ExtremalVolumeAbsorptionData
        (delta := delta) (rho := rho)
        desiredFine desiredCoarse
        (Kakeya.realRpowENN (delta / rho) (sigma - assemblyLoss))
        (Kakeya.realRpowENN rho (sigma - assemblyLoss)))
    (sourceFiberConstant : ENNReal) where
  delta_le_rho : delta ≤ rho
  rho_le_one : rho ≤ 1
  coarse_cwa_absorption :
    output.parentConstant ≤
      Kakeya.realRpowENN rho (-assemblyLoss)
  coarse_density :
    output.coarseShading.IsLambdaDense
      (Kakeya.realRpowENN rho assemblyLoss)
  fine_density_absorption :
    output.FineDensityAbsorptionData
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families
        (Kakeya.realRpowENN (delta / rho) assemblyLoss)
  public_multiplicity_absorption :
    output.PublicMultiplicityAbsorptionData
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families sigma capLoss assemblyLoss
  terminal_rescaling :
    families.TerminalPublicRescalingData
      input multiplicity parentClass treeCleanup exactification
        parentDegree core rho_le_one sourceFiberConstant
  fiber_cwa_absorption :
    (81000000 : ENNReal) * sourceFiberConstant ≤
      Kakeya.realRpowENN (delta / rho) (-assemblyLoss)

/--
Forget the V4 provenance while retaining the exact generic terminal inputs.
The V4 wrapper stores coarse density as the proved conclusion rather than as
one particular sufficient scalar inequality.
-/
noncomputable def Prop62V4FinalAssemblyInputsData.toFinalAssemblyInputsData
    {floorLoss capLoss assemblyLoss : ℝ}
    {critical :
      PureWZ2CriticalFloorSelectionData sigma floorLoss capLoss}
    {criticalInputs :
      output.CriticalMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families critical}
    {desiredProduct massLower sourceVolumeUpper
      desiredFine desiredCoarse : ENNReal}
    {productInputs :
      PureWZ2Prop62PacketCellInput.FourDegreeLemmaOutputData.ProductMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families
          (logExponent := 50)
          desiredProduct massLower sourceVolumeUpper}
    {componentInputs :
      output.ComponentMultiplicityFloorInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          critical desiredProduct desiredFine desiredCoarse}
    {volumeAbsorption :
      PureWZ2Prop62PacketCellInput.FourDegreeLemmaOutputData.ExtremalVolumeAbsorptionData
        (delta := delta) (rho := rho)
        desiredFine desiredCoarse
        (Kakeya.realRpowENN (delta / rho) (sigma - assemblyLoss))
        (Kakeya.realRpowENN rho (sigma - assemblyLoss))}
    {sourceFiberConstant : ENNReal}
    (assembly :
      Prop62V4FinalAssemblyInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families output assemblyLoss critical
          criticalInputs productInputs componentInputs volumeAbsorption
          sourceFiberConstant) :
    output.FinalAssemblyInputsData
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families critical criticalInputs
        productInputs componentInputs volumeAbsorption
        sourceFiberConstant where
  delta_le_rho := assembly.delta_le_rho
  rho_le_one := assembly.rho_le_one
  coarse_cwa_absorption := assembly.coarse_cwa_absorption
  coarse_density := assembly.coarse_density
  fine_density_absorption := assembly.fine_density_absorption
  public_multiplicity_absorption :=
    assembly.public_multiplicity_absorption
  terminal_rescaling := assembly.terminal_rescaling
  fiber_cwa_absorption := assembly.fiber_cwa_absorption

/--
Assemble the generic final-input record from the pure scalar receipt.

`criticalInputs` contains the actual coarse volume floor and rescaled-fiber
witnesses.  Coarse density is proved internally by the parentwise
tube--cell argument above; terminal rescaling remains explicit.  This theorem
does not run the final Proposition 6.2 assembly.
-/
noncomputable def finalAssemblyInputs
    (deltaLe : delta ≤ scalar.delta₀)
    (deltaLeRho : delta ≤ rho)
    (rhoLeOne : rho ≤ 1)
    (rhoLower : Real.rpow delta (1 - outputLoss) ≤ rho)
    (rhoUpper : rho ≤ Real.rpow delta outputLoss)
    (regularity :
      (output.coarseLoss : ENNReal) ≤
        logarithmicLoss delta ^ polylogExponent)
    (parentConstantLe :
      output.parentConstant ≤
        Kakeya.realRpowENN delta
          (-(cwaLossExponent : ℝ) *
            routing.numerics.hierarchy.stableLoss))
    (criticalInputs :
      output.CriticalMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          (criticalForCap (routing := routing)))
    (productInputs :
      PureWZ2Prop62PacketCellInput.FourDegreeLemmaOutputData.ProductMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families
          (logExponent := 50)
          (desiredProduct (routing := routing) delta)
          (wz1PaperRefinementFraction delta 11 *
            Kakeya.realRpowENN delta
              routing.numerics.hierarchy.sourceLoss *
            families.restriction.fineSelected.family.enncard *
            Kakeya.realRpowENN delta 2)
          (sourceVolumePower (routing := routing) delta))
    (componentInputs :
      output.ComponentMultiplicityFloorInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          (criticalForCap (routing := routing))
          (desiredProduct (routing := routing) delta)
          (desiredFine (routing := routing) delta rho)
          (desiredCoarse (routing := routing) rho))
    (volumeAbsorption :
      PureWZ2Prop62PacketCellInput.FourDegreeLemmaOutputData.ExtremalVolumeAbsorptionData
        (delta := delta) (rho := rho)
        (desiredFine (routing := routing) delta rho)
        (desiredCoarse (routing := routing) rho)
        (Kakeya.realRpowENN (delta / rho)
          (sigma - routing.numerics.hierarchy.finalStrongLoss))
        (Kakeya.realRpowENN rho
          (sigma - routing.numerics.hierarchy.finalStrongLoss)))
    (sourceFiberConstant : ENNReal)
    (terminalRescaling :
      families.TerminalPublicRescalingData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core rhoLeOne sourceFiberConstant)
    (sourceFiberConstantLe :
      (81000000 : ENNReal) * sourceFiberConstant ≤
        Kakeya.realRpowENN delta
          (-(cwaLossExponent : ℝ) *
            routing.numerics.hierarchy.stableLoss)) :
    Prop62V4FinalAssemblyInputsData
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families output
        routing.numerics.hierarchy.finalStrongLoss
        (criticalForCap (routing := routing)) criticalInputs
        productInputs componentInputs volumeAbsorption sourceFiberConstant := by
  have ratioPos : 0 < delta / rho :=
    div_pos input.delta_pos input.rho_pos
  have ratioLeOne : delta / rho ≤ 1 :=
    criticalInputs.ratio_small.trans (by norm_num)
  have fineDensityPower :
      Kakeya.realRpowENN (delta / rho)
          routing.numerics.hierarchy.finalStrongLoss ≤
        Kakeya.realRpowENN (delta / rho)
          routing.critical.structuralLoss :=
    pure_wz2_rpowENN_antitone
      ratioPos ratioLeOne scalar.structural_to_final
  have fineDensityAbsorption :
      output.FineDensityAbsorptionData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          (Kakeya.realRpowENN (delta / rho)
            routing.numerics.hierarchy.finalStrongLoss) := by
    refine ⟨?_⟩
    calc
      Kakeya.realRpowENN (delta / rho)
            routing.numerics.hierarchy.finalStrongLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        Kakeya.realRpowENN (delta / rho)
            routing.critical.structuralLoss *
          (55296 * Kakeya.deltaTubeVolume 1) := by
        gcongr
      _ ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ((2 : ENNReal)⁻¹ *
            Kakeya.realRpowENN delta
              ((packetDensityExponent : ℝ) *
                routing.numerics.hierarchy.stableLoss)) :=
        scalar.fiber_density input.delta_pos deltaLe input.rho_pos rhoLower
      _ =
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          output.terminalFiberSourceDensity
            input multiplicity parentClass treeCleanup exactification
              parentDegree core good families := rfl
  have publicMultiplicity :
      output.PublicMultiplicityAbsorptionData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          sigma routing.numerics.hierarchy.capLoss
            routing.numerics.hierarchy.finalStrongLoss := by
    exact
      {
        coarse_scalar :=
          scalar.final_coarse_multiplicity
            input.delta_pos deltaLe input.rho_pos rhoLower rhoUpper
              regularity
        fine_scalar :=
          scalar.final_fiber_multiplicity
            input.delta_pos deltaLe input.rho_pos rhoLower
      }
  have parentPower :
      Kakeya.realRpowENN rho
          (-(routing.numerics.hierarchy.finalStrongLoss / 4)) ≤
        Kakeya.realRpowENN rho
          (-routing.numerics.hierarchy.finalStrongLoss) := by
    apply pure_wz2_rpowENN_antitone input.rho_pos rhoLeOne
    linarith [routing.numerics.hierarchy.finalStrongLoss_pos]
  exact
    {
      delta_le_rho := deltaLeRho
      rho_le_one := rhoLeOne
      coarse_cwa_absorption :=
        parentConstantLe.trans <|
          (scalar.final_cwa_parent_nearby
            input.delta_pos deltaLe input.rho_pos rhoUpper).trans
              parentPower
      coarse_density :=
        scalar.finalCoarseDensity
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families output
            deltaLe rhoLeOne rhoUpper
      fine_density_absorption := fineDensityAbsorption
      public_multiplicity_absorption := publicMultiplicity
      terminal_rescaling := terminalRescaling
      fiber_cwa_absorption :=
        sourceFiberConstantLe.trans <|
          scalar.final_cwa_fiber
            input.delta_pos deltaLe input.rho_pos rhoLower
    }

end Prop62V4PureScalarInputs

end Kakeya.Assouad.Prop62PaperAudit.V4

end
