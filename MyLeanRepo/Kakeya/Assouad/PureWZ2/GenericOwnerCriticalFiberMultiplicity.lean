import MyLeanRepo.Kakeya.Assouad.PureWZ2.GenericOwnerMultiplicity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CriticalRescaledFiberWitness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureRescaledFiberWeakening
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperExternalWeightRelativeMultiplicity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageMultiplicity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageMultiplicityFloor
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRelativeMultiplicityNormalization
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper

/-!
# Critical-floor multiplicity on generic owner fibers

For each final complete owner fiber, first construct the public rescaled
configuration at the critical structural loss.  The pure critical-volume
floor, literal image multiplicity floor, and quadratic target mass upper
bound then give the strong cardinality-normalized source multiplicity.
The public loss is obtained only at the final monotone weakening step.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2GenericOwnerSelectedData

variable
    {delta rho sigma floorLoss strongLoss outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) fineShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover fineShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover fineShading coarseCells availableFineCells
        balancing coarseData}
    {owner : WZ2PaperDirectOwnerPreparationData producer}
    {outputConstant : ENNReal}
    (data : PureWZ2GenericOwnerSelectedData owner outputConstant)
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss strongLoss)

theorem critical_rescaled_fiber_public_output
    (strongLoss_pos : 0 < strongLoss)
    (loss_budget : 3 * strongLoss ≤ outputLoss)
    (criticalRescaled :
      ∀ parent : Fin data.selectedPacked.family.card,
        Nonempty
          (PureWZ2CriticalRescaledFiberWitness
            (sigma := sigma) (loss := critical.structuralLoss)
            (restrictPaperShading
              (data.internalCover.fullFiberSubfamily parent)
              data.finalFineShading)
            (data.selectedPacked.family.tube parent) hrho)) :
    ∀ parent : Fin data.selectedPacked.family.card,
      Nonempty
        (WZ2PaperPureRescaledFullFiberOutput
          (sigma := sigma) (loss := outputLoss)
          (restrictPaperShading
            (data.internalCover.fullFiberSubfamily parent)
            data.finalFineShading)
          (data.selectedPacked.family.tube parent) hrho) := by
  intro parent
  let witness := Classical.choice (criticalRescaled parent)
  have critical_le_output :
      critical.structuralLoss ≤ outputLoss := by
    have strong_le_output : strongLoss ≤ outputLoss := by
      linarith
    exact critical.structuralLoss_le.trans strong_le_output
  exact ⟨witness.output.mono_loss critical_le_output⟩

theorem fiber_multiplicity_of_critical_rescaled
    (ratio_pos : 0 < delta / rho)
    (ratio_le_one : delta / rho ≤ 1)
    (ratio_small : delta / rho ≤ 1 / 24)
    (ratio_critical : delta / rho ≤ critical.delta₀)
    (floor_strong : floorLoss < strongLoss)
    (strongLoss_pos : 0 < strongLoss)
    (loss_budget : 3 * strongLoss ≤ outputLoss)
    (multiplicity_absorption :
      2 * (55296 * Kakeya.deltaTubeVolume 1) ≤
        Kakeya.realRpowENN (delta / rho)
          (-(strongLoss - floorLoss)))
    (criticalRescaled :
      ∀ parent : Fin data.selectedPacked.family.card,
        Nonempty
          (PureWZ2CriticalRescaledFiberWitness
            (sigma := sigma) (loss := critical.structuralLoss)
            (restrictPaperShading
              (data.internalCover.fullFiberSubfamily parent)
              data.finalFineShading)
            (data.selectedPacked.family.tube parent) hrho)) :
    ∀ parent point,
      (((wz2PaperFullFiberIndices
          data.selectedFine.family data.selectedPacked.family parent).filter
          fun index =>
            point ∈ data.finalFineShading.carrier index).card : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - outputLoss) *
          ((wz2PaperFullFiberIndices
            data.selectedFine.family
            data.selectedPacked.family parent).card : ENNReal) := by
  intro parent point
  let sourceFamily :=
    (data.internalCover.fullFiberSubfamily parent).family
  let sourceShading :=
    restrictPaperShading
      (data.internalCover.fullFiberSubfamily parent)
      data.finalFineShading
  let witness := Classical.choice (criticalRescaled parent)
  let output := witness.output
  let targetShading := output.literalShading.targetShading
  let publicShading :=
    output.rescalingCertificate.publicShading targetShading
  let multiplicity : ℕ := 2 ^ producer.fiberBand.level
  have sourceLower :
      ∀ sourcePoint ∈ sourceShading.union,
        (multiplicity : ENNReal) ≤
          (sourceShading.pointMultiplicity sourcePoint : ENNReal) := by
    intro sourcePoint sourcePointMem
    simpa [multiplicity, sourceShading] using
      (data.final_fiber_shading_multiplicity_band
        parent sourcePoint sourcePointMem).1
  have sourceUpper :
      ∀ sourcePoint,
        (sourceShading.pointMultiplicity sourcePoint : ENNReal) ≤
          (2 * multiplicity : ENNReal) := by
    intro sourcePoint
    by_cases sourcePointMem : sourcePoint ∈ sourceShading.union
    · have upper :=
        (data.final_fiber_shading_multiplicity_band
          parent sourcePoint sourcePointMem).2
      simpa [multiplicity, pow_succ, mul_comm] using upper
    · have zero :
          sourceShading.pointMultiplicity sourcePoint = 0 := by
        simp [Kakeya.Streamlined.Shading.pointMultiplicity,
          show ∀ index,
              sourcePoint ∉ sourceShading.carrier index by
            intro index indexMem
            exact sourcePointMem ⟨index, indexMem⟩]
      rw [zero]
      simp
  have targetFloor :
      ∀ targetPoint ∈ targetShading.union,
        (multiplicity : ENNReal) ≤
          (targetShading.pointMultiplicity targetPoint : ENNReal) :=
    wz2_paper_literal_image_multiplicity_floor
      wz2_paper_literal_image_multiplicity
      output.familyData sourceShading output.literalShading
      multiplicity sourceLower
  have criticalFloorOrdinary :
      Kakeya.realRpowENN (delta / rho) (sigma + floorLoss) ≤
        volume witness.ordinaryShading.union :=
    critical.volume_floor
      (delta / rho) ratio_pos ratio_critical
      witness.ordinaryFamily witness.ordinary_nonempty
      witness.ordinaryShading witness.ordinary_cwa
      witness.ordinary_dense
  have criticalFloorTarget :
      Kakeya.realRpowENN (delta / rho) (sigma + floorLoss) ≤
        volume targetShading.union := by
    exact criticalFloorOrdinary.trans
      (measure_mono witness.ordinary_union_subset_target)
  have targetMassUpper :
      targetShading.mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN (delta / rho) 2 *
          sourceFamily.enncard := by
    have raw :=
      wz2_paper_shading_mass_upper
        ratio_pos ratio_small
        output.familyData.target_line_class targetShading
    calc
      targetShading.mass ≤
          (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN (delta / rho) 2 *
            output.familyData.targetFamily.enncard := raw
      _ =
          (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN (delta / rho) 2 *
            sourceFamily.enncard := by
        rw [← output.rescalingCertificate.publicFamily_enncard_eq,
          output.source_cardinality_eq]
  have strongBound :
      ∀ currentPoint,
        (sourceShading.pointMultiplicity currentPoint : ENNReal) ≤
          Kakeya.realRpowENN (delta / rho)
              (2 - sigma - strongLoss) *
            sourceFamily.enncard := by
    intro currentPoint
    exact
      wz2_paper_external_weight_relative_multiplicity
        ratio_pos ratio_le_one floor_strong
        sourceShading sourceShading
        targetShading targetShading multiplicity
        (fun _ => le_rfl)
        sourceUpper targetFloor Set.Subset.rfl
        criticalFloorTarget
        (55296 * Kakeya.deltaTubeVolume 1) 1 1
        targetMassUpper
        (by norm_num) (by norm_num)
        (by simp)
        (by simpa using multiplicity_absorption)
        currentPoint
  have publicBound :
      ∀ currentPoint,
        (sourceShading.pointMultiplicity currentPoint : ENNReal) ≤
          Kakeya.realRpowENN (delta / rho)
              (2 - sigma - outputLoss) *
            sourceFamily.enncard :=
    wz2_paper_relative_multiplicity_normalization
      ratio_pos ratio_le_one strongLoss_pos.le loss_budget
      strongBound
  have sourceCardinality :
      sourceFamily.enncard =
        ((wz2PaperFullFiberIndices
          data.selectedFine.family
          data.selectedPacked.family parent).card : ENNReal) := by
    rfl
  rw [data.raw_fiber_pointMultiplicity_eq parent point]
  rw [← sourceCardinality]
  exact publicBound point

end PureWZ2GenericOwnerSelectedData

end Kakeya.Assouad

end
