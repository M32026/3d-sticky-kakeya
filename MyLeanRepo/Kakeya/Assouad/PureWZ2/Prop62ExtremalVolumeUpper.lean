import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ComponentMultiplicityFloors

/-!
# Proposition 6.2: extremal union-volume upper bounds

This module formalizes the two displays immediately after the component
multiplicity floors.

For the coarse pair, the frozen `muCoarse` multiplicity floor and the
quadratic paper-carrier mass upper bound give the union-volume estimate.
For one fine fiber, exact `muFine` multiplicity transfers to the canonical
literal cubical image, where the same argument applies at scale
`delta / rho`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62PacketCellInput

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
    {fiberConstant densityConstant : ENNReal}
    {logExponent : ℕ}
    (output :
      input.FourDegreeLemmaOutputData
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          fiberConstant densityConstant logExponent)

namespace FourDegreeLemmaOutputData

structure ExtremalVolumeAbsorptionData
    (desiredFine desiredCoarse fineVolumeUpper coarseVolumeUpper :
      ENNReal) : Prop where
  coarse_scalar :
    (55296 * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN rho 2 ≤
      desiredCoarse * coarseVolumeUpper
  fine_scalar :
    (55296 * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN (delta / rho) 2 ≤
      desiredFine * fineVolumeUpper

theorem coarse_volume_upper_of_component_floor
    {sigma floorLoss capLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss)
    (criticalInputs :
      output.CriticalMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families critical)
    {desiredProduct massLower sourceVolumeUpper : ENNReal}
    (productInputs :
      ProductMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families
          (logExponent := logExponent)
          desiredProduct massLower sourceVolumeUpper)
    {desiredFine desiredCoarse : ENNReal}
    (componentInputs :
      output.ComponentMultiplicityFloorInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          critical desiredProduct desiredFine desiredCoarse)
    {fineVolumeUpper coarseVolumeUpper : ENNReal}
    (volumeAbsorption :
      ExtremalVolumeAbsorptionData
        (delta := delta) (rho := rho)
        desiredFine desiredCoarse fineVolumeUpper coarseVolumeUpper) :
    volume output.coarseShading.union ≤ coarseVolumeUpper := by
  have multiplicityFloor :
      (output.muCoarse : ENNReal) *
          volume output.coarseShading.union ≤
        output.coarseShading.mass :=
    multiplicity_floor_le_mass <| by
      intro point pointMem
      exact
        output.coarse_pointMultiplicity_lower
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families pointMem
  have massUpper :
      output.coarseShading.mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN rho 2 *
          families.restriction.coarseSelected.family.enncard :=
    wz2_paper_shading_mass_upper
      input.rho_pos criticalInputs.rho_small
      families.restriction.section6Cover.coarse_line_class
      output.coarseShading
  have componentFloor :=
    output.coarse_multiplicity_lower
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families
        critical criticalInputs productInputs componentInputs
  have muCoarseZero : (output.muCoarse : ENNReal) ≠ 0 := by
    exact_mod_cast output.muCoarse_pos.ne'
  have muCoarseTop : (output.muCoarse : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply
    (ENNReal.mul_le_mul_iff_left
      muCoarseZero muCoarseTop).mp
  calc
    volume output.coarseShading.union *
          (output.muCoarse : ENNReal) =
        (output.muCoarse : ENNReal) *
          volume output.coarseShading.union := by
      ring
    _ ≤ output.coarseShading.mass :=
      multiplicityFloor
    _ ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN rho 2 *
          families.restriction.coarseSelected.family.enncard :=
      massUpper
    _ ≤
        (desiredCoarse * coarseVolumeUpper) *
          families.restriction.coarseSelected.family.enncard := by
      exact
        mul_le_mul_right'
          volumeAbsorption.coarse_scalar
          families.restriction.coarseSelected.family.enncard
    _ =
        (desiredCoarse *
          families.restriction.coarseSelected.family.enncard) *
          coarseVolumeUpper := by
      ring
    _ ≤
        (output.muCoarse : ENNReal) * coarseVolumeUpper := by
      gcongr
    _ =
        coarseVolumeUpper * (output.muCoarse : ENNReal) := by
      ring

theorem terminalFiberLiteral_volume_upper_of_component_floor
    (rho_le_one : rho ≤ 1)
    {sigma floorLoss capLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss)
    (criticalInputs :
      output.CriticalMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families critical)
    {desiredProduct massLower sourceVolumeUpper : ENNReal}
    (productInputs :
      ProductMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families
          (logExponent := logExponent)
          desiredProduct massLower sourceVolumeUpper)
    {desiredFine desiredCoarse : ENNReal}
    (componentInputs :
      output.ComponentMultiplicityFloorInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          critical desiredProduct desiredFine desiredCoarse)
    {fineVolumeUpper coarseVolumeUpper : ENNReal}
    (volumeAbsorption :
      ExtremalVolumeAbsorptionData
        (delta := delta) (rho := rho)
        desiredFine desiredCoarse fineVolumeUpper coarseVolumeUpper) :
    ∀ parent :
        Fin families.restriction.coarseSelected.family.card,
      volume
          (output.terminalFiberLiteralShading
            input multiplicity parentClass treeCleanup exactification
              parentDegree core good families
              rho_le_one criticalInputs.ratio_small parent
            ).targetShading.union ≤
        fineVolumeUpper := by
  intro parent
  let sourceFamily :=
    (families.terminalFiber
      input multiplicity parentClass treeCleanup exactification
        parentDegree core parent).family
  let sourceFiberShading :=
    output.terminalFiberShading
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent
  let literalFamily :=
    output.terminalFiberLiteral
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families rho_le_one parent
  let literalShading :=
    output.terminalFiberLiteralShading
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families
        rho_le_one criticalInputs.ratio_small parent
  have sourceFloor :
      ∀ point ∈ sourceFiberShading.union,
        (output.muFine : ENNReal) ≤
          (sourceFiberShading.pointMultiplicity point : ENNReal) := by
    intro point pointMem
    exact
      output.terminalFiberShading_multiplicity_lower
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent pointMem
  have targetFloor :
      ∀ point ∈ literalShading.targetShading.union,
        (output.muFine : ENNReal) ≤
          (literalShading.targetShading.pointMultiplicity point :
            ENNReal) :=
    wz2_paper_literal_image_multiplicity_floor
      wz2_paper_literal_image_multiplicity
      literalFamily sourceFiberShading literalShading
      output.muFine sourceFloor
  have multiplicityFloor :
      (output.muFine : ENNReal) *
          volume literalShading.targetShading.union ≤
        literalShading.targetShading.mass :=
    multiplicity_floor_le_mass targetFloor
  have targetCardinality :
      literalFamily.targetFamily.enncard =
        sourceFamily.enncard :=
    (wz2_paper_literal_image_multiplicity
      (familyData := literalFamily)
      (sourceShading := sourceFiberShading)
      (shadingData := literalShading)).1
  have ratioPos : 0 < delta / rho :=
    div_pos input.delta_pos input.rho_pos
  have massUpper :
      literalShading.targetShading.mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN (delta / rho) 2 *
          sourceFamily.enncard := by
    have raw :=
      wz2_paper_shading_mass_upper
        ratioPos criticalInputs.ratio_small
        literalFamily.target_line_class
        literalShading.targetShading
    simpa [targetCardinality] using raw
  have componentFloor :=
    output.fine_multiplicity_lower
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families
        critical criticalInputs productInputs componentInputs parent
  have muFineZero : (output.muFine : ENNReal) ≠ 0 := by
    exact_mod_cast output.muFine_pos.ne'
  have muFineTop : (output.muFine : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply
    (ENNReal.mul_le_mul_iff_left
      muFineZero muFineTop).mp
  calc
    volume literalShading.targetShading.union *
          (output.muFine : ENNReal) =
        (output.muFine : ENNReal) *
          volume literalShading.targetShading.union := by
      ring
    _ ≤ literalShading.targetShading.mass :=
      multiplicityFloor
    _ ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN (delta / rho) 2 *
          sourceFamily.enncard :=
      massUpper
    _ ≤
        (desiredFine * fineVolumeUpper) *
          sourceFamily.enncard := by
      exact
        mul_le_mul_right'
          volumeAbsorption.fine_scalar
          sourceFamily.enncard
    _ =
        (desiredFine * sourceFamily.enncard) *
          fineVolumeUpper := by
      ring
    _ ≤
        (output.muFine : ENNReal) * fineVolumeUpper := by
      gcongr
    _ =
        fineVolumeUpper * (output.muFine : ENNReal) := by
      ring

end FourDegreeLemmaOutputData

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
