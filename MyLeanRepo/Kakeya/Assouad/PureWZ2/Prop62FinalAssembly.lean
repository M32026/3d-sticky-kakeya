import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ExtremalVolumeUpper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricFiberRescaling

/-!
# Proposition 6.2: final frozen-output assembly

This module assembles the terminal four-degree configuration into the frozen
`PureWZ2PropStickyData` ABI.

All scalar and incidence conclusions are already proved upstream.  The sole
remaining per-fiber geometric input is pure nearby-scale CWA on the canonical
ordinary public family attached to the same canonical literal rescaling.
That input is explicit below; it is not replaced by CWA on an unrelated
family.
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

/-- The canonical ordinary/public rescaling certificate of one final fiber. -/
noncomputable def terminalFiberCertificate
    (rho_le_one : rho ≤ 1)
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    WZ2PaperAssouadToLiteralRescalingCertificate
      input.rho_pos
      (WZ2PaperAssouadUnitRescalingData.ofTube
        (families.restriction.coarseSelected.family.tube parent)
        input.rho_pos)
      (output.terminalFiberLiteral
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families rho_le_one parent)
      4000000 :=
  wz2PaperLiteralOrdinaryRescaledFamilyCertificate
    input.delta_pos input.rho_pos rho_le_one
    (families.terminalFiber
      input multiplicity parentClass treeCleanup exactification
        parentDegree core parent).family
    (families.restriction.coarseSelected.family.tube parent)
    (output.terminalFiber_line_class
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent)
    (families.restriction.section6Cover.coarse_line_class parent)
    (output.terminalFiber_covered
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent)

structure FinalAssemblyInputsData
    {sigma floorLoss capLoss outputLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss)
    (criticalInputs :
      output.CriticalMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families critical)
    {desiredProduct massLower sourceVolumeUpper
      desiredFine desiredCoarse : ENNReal}
    (productInputs :
      ProductMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families
          (logExponent := logExponent)
          desiredProduct massLower sourceVolumeUpper)
    (componentInputs :
      output.ComponentMultiplicityFloorInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          critical desiredProduct desiredFine desiredCoarse)
    (volumeAbsorption :
      ExtremalVolumeAbsorptionData
        (delta := delta) (rho := rho)
        desiredFine desiredCoarse
        (Kakeya.realRpowENN (delta / rho) (sigma - outputLoss))
        (Kakeya.realRpowENN rho (sigma - outputLoss)))
    (sourceFiberConstant : ENNReal) where
  delta_le_rho : delta ≤ rho
  rho_le_one : rho ≤ 1
  coarse_cwa_absorption :
    output.parentConstant ≤
      Kakeya.realRpowENN rho (-outputLoss)
  coarse_density :
    output.coarseShading.IsLambdaDense
      (Kakeya.realRpowENN rho outputLoss)
  fine_density_absorption :
    output.FineDensityAbsorptionData
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families
        (Kakeya.realRpowENN (delta / rho) outputLoss)
  public_multiplicity_absorption :
    output.PublicMultiplicityAbsorptionData
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families
        sigma capLoss outputLoss
  terminal_rescaling :
    families.TerminalPublicRescalingData
      input multiplicity parentClass treeCleanup exactification
        parentDegree core rho_le_one sourceFiberConstant
  fiber_cwa_absorption :
    (81000000 : ENNReal) * sourceFiberConstant ≤
      Kakeya.realRpowENN (delta / rho) (-outputLoss)

noncomputable def terminalFiberRescaledOutput
    {sigma floorLoss capLoss outputLoss : ℝ}
    {sourceFiberConstant : ENNReal}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss)
    (criticalInputs :
      output.CriticalMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families critical)
    {desiredProduct massLower sourceVolumeUpper
      desiredFine desiredCoarse : ENNReal}
    (productInputs :
      ProductMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families
          (logExponent := logExponent)
          desiredProduct massLower sourceVolumeUpper)
    (componentInputs :
      output.ComponentMultiplicityFloorInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          critical desiredProduct desiredFine desiredCoarse)
    (volumeAbsorption :
      ExtremalVolumeAbsorptionData
        (delta := delta) (rho := rho)
        desiredFine desiredCoarse
        (Kakeya.realRpowENN (delta / rho) (sigma - outputLoss))
        (Kakeya.realRpowENN rho (sigma - outputLoss)))
    (assembly :
      output.FinalAssemblyInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          critical criticalInputs productInputs
          componentInputs volumeAbsorption sourceFiberConstant)
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := outputLoss)
      (output.terminalFiberShading
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent)
      (families.restriction.coarseSelected.family.tube parent)
      input.rho_pos := by
  let sourceFamily :=
    (families.terminalFiber
      input multiplicity parentClass treeCleanup exactification
        parentDegree core parent).family
  let sourceFiberShading :=
    output.terminalFiberShading
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent
  let literal :=
    output.terminalFiberLiteral
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families assembly.rho_le_one parent
  let literalShading :=
    output.terminalFiberLiteralShading
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families
        assembly.rho_le_one criticalInputs.ratio_small parent
  let certificate :=
    output.terminalFiberCertificate
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families assembly.rho_le_one parent
  let publicShading :=
    certificate.publicShading literalShading.targetShading
  have fiberPublicCWA :
      WZ2PaperPureCWAAtNearbyScales
        certificate.publicFamily
        (Kakeya.realRpowENN (delta / rho) (-outputLoss)) := by
    let terminalReindex :=
      TerminalCompleteFamiliesData.TerminalPublicRescalingData.reindexData
        (input := input)
        (multiplicity := multiplicity)
        (parentClass := parentClass)
        (treeCleanup := treeCleanup)
        (exactification := exactification)
        (parentDegree := parentDegree)
        (core := core)
        (families := families)
        assembly.terminal_rescaling parent
    have canonical :=
      TerminalCompleteFamiliesData.TerminalPublicRescalingData.publicPureCWA
        (input := input)
        (multiplicity := multiplicity)
        (parentClass := parentClass)
        (treeCleanup := treeCleanup)
        (exactification := exactification)
        (parentDegree := parentDegree)
        (core := core)
        (families := families)
        assembly.terminal_rescaling parent
    have weakened :
        WZ2PaperPureCWAAtNearbyScales
          terminalReindex.targetCertificate.publicFamily
          (Kakeya.realRpowENN (delta / rho) (-outputLoss)) :=
      canonical.mono assembly.fiber_cwa_absorption <| by
        simp [Kakeya.realRpowENN]
    have certificateEq :
        terminalReindex.targetCertificate.publicFamily =
          certificate.publicFamily := by
      rfl
    rw [certificateEq] at weakened
    exact weakened
  have literalDense :
      literalShading.targetShading.IsLambdaDense
        (Kakeya.realRpowENN (delta / rho) outputLoss) :=
    output.terminalFiber_literal_dense
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families
        assembly.rho_le_one criticalInputs.ratio_small
        assembly.fine_density_absorption parent
  have literalVolume :
      volume literalShading.targetShading.union ≤
        Kakeya.realRpowENN (delta / rho) (sigma - outputLoss) :=
    output.terminalFiberLiteral_volume_upper_of_component_floor
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families
        assembly.rho_le_one critical criticalInputs
        productInputs componentInputs volumeAbsorption parent
  have publicDense :
      publicShading.IsLambdaDense
        (Kakeya.realRpowENN (delta / rho) outputLoss) := by
    rw [Kakeya.Streamlined.Shading.IsLambdaDense]
    rw [certificate.publicBody_mass_eq,
      certificate.publicShading_mass_eq]
    exact literalDense
  have publicVolume :
      volume publicShading.union ≤
        Kakeya.realRpowENN (delta / rho) (sigma - outputLoss) := by
    rw [certificate.publicShading_union_eq]
    exact literalVolume
  have sourceNonempty : sourceFamily.Nonempty := by
    change
      0 <
        (wz2PaperFullFiberIndices
          families.restriction.fineSelected.family
          families.restriction.coarseSelected.family parent).card
    exact
      lt_of_lt_of_le output.fiberFloor_pos
        (output.fiber_cardinality parent).1
  have literalCardinality :
      literal.targetFamily.enncard = sourceFamily.enncard :=
    (wz2_paper_literal_image_multiplicity
      (familyData := literal)
      (sourceShading := sourceFiberShading)
      (shadingData := literalShading)).1
  have literalNonempty : literal.targetFamily.Nonempty := by
    change 0 < literal.targetFamily.card
    have sourceCardPos : 0 < sourceFamily.card := sourceNonempty
    have cardEq :
        literal.targetFamily.card = sourceFamily.card := by
      simpa [Kakeya.Streamlined.TubeFamily.enncard] using
        literalCardinality
    rwa [cardEq]
  let publicExtremal :
      WZ2PaperCroppedIsExtremal
        sigma outputLoss certificate.publicFamily publicShading :=
    {
      delta_pos := div_pos input.delta_pos input.rho_pos
      delta_le_one :=
        (div_le_one input.rho_pos).mpr assembly.delta_le_rho
      nonempty :=
        certificate.publicFamily_nonempty literalNonempty
      cwa_nearby_scales := fiberPublicCWA
      cubical :=
        certificate.publicShading_cubical
          literalShading.target_cubical
      dense := publicDense
      volume_upper := publicVolume
    }
  exact
    {
      familyData := literal
      literalShading := literalShading
      jacobianConstant := 4000000
      jacobianConstant_one := by norm_num
      jacobianConstant_finite := by norm_num
      rescalingCertificate := certificate
      extremal := publicExtremal
      source_cardinality_eq := by
        calc
          certificate.publicFamily.enncard =
              literal.targetFamily.enncard :=
            certificate.publicFamily_enncard_eq
          _ = sourceFamily.enncard := literalCardinality
    }

noncomputable def assemblePropSticky
    {sigma floorLoss capLoss outputLoss : ℝ}
    {sourceFiberConstant : ENNReal}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss)
    (criticalInputs :
      output.CriticalMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families critical)
    {desiredProduct massLower sourceVolumeUpper
      desiredFine desiredCoarse : ENNReal}
    (productInputs :
      ProductMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families
          (logExponent := logExponent)
          desiredProduct massLower sourceVolumeUpper)
    (componentInputs :
      output.ComponentMultiplicityFloorInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          critical desiredProduct desiredFine desiredCoarse)
    (volumeAbsorption :
      ExtremalVolumeAbsorptionData
        (delta := delta) (rho := rho)
        desiredFine desiredCoarse
        (Kakeya.realRpowENN (delta / rho) (sigma - outputLoss))
        (Kakeya.realRpowENN rho (sigma - outputLoss)))
    (assembly :
      output.FinalAssemblyInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          critical criticalInputs productInputs
          componentInputs volumeAbsorption sourceFiberConstant) :
    PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading
      ⟨rho, assembly.delta_le_rho, assembly.rho_le_one⟩
      logExponent := by
  have coarseNonempty :
      families.restriction.coarseSelected.family.Nonempty :=
    finalCoarse_card_pos
      input multiplicity parentClass treeCleanup exactification
        parentDegree core families
  have coarsePure :
      WZ2PaperPureCWAAtNearbyScales
        families.restriction.coarseSelected.family
        (Kakeya.realRpowENN rho (-outputLoss)) :=
    output.parent_cwa.mono
      assembly.coarse_cwa_absorption
      (by simp [Kakeya.realRpowENN])
  have coarseDense :
      output.coarseShading.IsLambdaDense
        (Kakeya.realRpowENN rho outputLoss) :=
    assembly.coarse_density
  have coarseVolume :
      volume output.coarseShading.union ≤
        Kakeya.realRpowENN rho (sigma - outputLoss) :=
    output.coarse_volume_upper_of_component_floor
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families
        critical criticalInputs productInputs
        componentInputs volumeAbsorption
  let coarseExtremal :
      WZ2PaperCroppedIsExtremal
        sigma outputLoss
        families.restriction.coarseSelected.family
        output.coarseShading :=
    {
      delta_pos := input.rho_pos
      delta_le_one := assembly.rho_le_one
      nonempty := coarseNonempty
      cwa_nearby_scales := coarsePure
      cubical := output.balanced.coarse_cubical
      dense := coarseDense
      volume_upper := coarseVolume
    }
  exact
    {
      selected := families.restriction.fineSelected
      selected_nonempty := by
        change 0 < families.restriction.fineSelected.family.card
        rw [families.restriction.fineSelected_eq]
        change 0 < families.terminalFine.card
        exact families.terminalFine_nonempty.card_pos
      refined := output.fineShading
      subshading := by
        intro source
        rw [output.fineShading_eq]
        exact
          TerminalFineShading.subshading
            input multiplicity parentClass treeCleanup exactification
              core.ranges good families source
      retained_mass := output.retained_mass
      refined_cubical := by
        rw [output.fineShading_eq]
        exact
          TerminalFineShading.cubical
            input multiplicity parentClass treeCleanup exactification
              core.ranges good families
      coarse := families.restriction.coarseSelected.family
      cover := families.restriction.section6Cover
      croppedCoarseShading := output.coarseShading
      balanced := output.balanced
      coarse_extremal := coarseExtremal
      rescaledFiber := by
        intro parent
        exact
          ⟨output.terminalFiberRescaledOutput
            input multiplicity parentClass treeCleanup exactification
              parentDegree core good families
              critical criticalInputs productInputs
              componentInputs volumeAbsorption assembly parent⟩
      coarse_multiplicity_upper :=
        output.coarse_pointMultiplicity_upper_of_critical_inputs
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families
            critical criticalInputs
            assembly.public_multiplicity_absorption
      fiber_multiplicity_upper :=
        output.fine_pointMultiplicity_upper_of_critical_inputs
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families
            critical criticalInputs
            assembly.public_multiplicity_absorption
    }

end FourDegreeLemmaOutputData

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
