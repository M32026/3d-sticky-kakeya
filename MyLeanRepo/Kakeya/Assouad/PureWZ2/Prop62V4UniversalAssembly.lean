import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FinalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4CriticalInputsAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4PureFinalAssemblyInputs
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4PureRefinementComposition
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureRescaledFiberWeakening

/-!
# Proposition 6.2 V4 universal assembly

This module contains the final dependent-record assembly for the pure V4
route.  The geometric and scalar leaves are constructed in separate modules;
the lemmas here only reconnect their exact witnesses to the normalized
source.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2PropStickyData

/-- Compatibility name for the canonical loss weakening now owned by the
public re-entry module. -/
noncomputable abbrev mono_loss
    {delta sigma firstLoss secondLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data :
      Kakeya.Assouad.PureWZ2PropStickyData
        (sigma := sigma) (outputLoss := firstLoss)
        sourceShading rho logExponent)
    (loss_le : firstLoss ≤ secondLoss) :
    Kakeya.Assouad.PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := secondLoss)
      sourceShading rho logExponent :=
  Kakeya.Assouad.PureWZ2PropStickyData.mono_loss data loss_le

end PureWZ2PropStickyData

namespace Prop62V4RichCertificateCompanionData

variable
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent}
    {rho : WZ2PaperRequestedScale delta}
    {hdelta : 0 < delta}
    {preparation :
      FixedGridPreparationData
        (rho := rho.1) normalized.croppedRefined hdelta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {metricCertificate :
      PureWZ2Prop62MetricParentsV4Certificate
        preparation.cleanup.refined rho fineParentDistanceConstant
          parentConstant fiberConstant}
    {eta : ℝ}
    {packetDensityExponent cwaLossExponent polylogExponent : ℕ}
    (rich :
      Prop62V4RichCertificateCompanionData
        (eta := eta)
        (packetDensityExponent := packetDensityExponent)
        (cwaLossExponent := cwaLossExponent)
        (polylogExponent := polylogExponent)
        hdelta
        (prop62V4FixedGridMetricCompanionOfCertificate
          normalized preparation metricCertificate))

/--
Replace the generic fifty-log source refinement by the exact
fixed-grid/metric/four-degree `1 + 10 + 50 = 61` refinement of the normalized
source.  Every terminal family, cover, shading, extremality, and multiplicity
certificate is reused definitionally.
-/
noncomputable def repackagePropStickySixtyOne
    {outputLoss : ℝ}
    (assembled :
      PureWZ2PropStickyData
        (sigma := sigma)
        (outputLoss := outputLoss)
        (prop62V4FixedGridMetricCompanionOfCertificate
          normalized preparation metricCertificate
        ).metric.refinement.refined
        rho 50)
    (selected_eq :
      assembled.selected =
        rich.outputCertificate.refinement.selected)
    (refined_eq :
      HEq assembled.refined
        rich.outputCertificate.refinement.refined) :
    PureWZ2PropStickyData
      (sigma := sigma)
      (outputLoss := outputLoss)
      normalized.croppedRefined rho 61 := by
  rcases assembled with
    ⟨assembledSelected, selectedNonempty, assembledRefined,
      subshading, _retainedMass, refinedCubical, coarse, cover,
      coarseShading, balanced, coarseExtremal, rescaledFiber,
      coarseMultiplicity, fiberMultiplicity⟩
  dsimp only at selected_eq refined_eq
  subst assembledSelected
  cases refined_eq
  exact
    {
      selected := rich.fixedGridComposedSelected
      selected_nonempty := selectedNonempty
      refined := rich.fixedGridComposedShading
      subshading := rich.fixedGridComposed_subshading
      retained_mass := rich.fixedGridComposed_retained_mass_pure
      refined_cubical := rich.fixedGridComposed_cubical
      coarse := coarse
      cover := cover
      croppedCoarseShading := coarseShading
      balanced := balanced
      coarse_extremal := coarseExtremal
      rescaledFiber := rescaledFiber
      coarse_multiplicity_upper := coarseMultiplicity
      fiber_multiplicity_upper := fiberMultiplicity
    }

/--
Run the generic terminal assembly on the exact canonical producer retained by
`rich`, then replace its fifty-log source refinement by the full
one-plus-ten-plus-fifty-log refinement of the normalized source.
-/
noncomputable def assemblePurePropStickySixtyOne
    {floorLoss capLoss outputLoss : ℝ}
    {sourceFiberConstant : ENNReal}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss)
    (criticalInputs :
      rich.canonicalOutput.CriticalMultiplicityInputsData
        rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
          rich.exactification rich.parentDegree rich.core rich.good
          rich.families critical)
    {desiredProduct massLower sourceVolumeUpper
      desiredFine desiredCoarse : ENNReal}
    (productInputs :
      PureWZ2Prop62PacketCellInput.FourDegreeLemmaOutputData.ProductMultiplicityInputsData
        rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
          rich.exactification rich.parentDegree rich.core rich.families
          (logExponent := 50)
          desiredProduct massLower sourceVolumeUpper)
    (componentInputs :
      rich.canonicalOutput.ComponentMultiplicityFloorInputsData
        rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
          rich.exactification rich.parentDegree rich.core rich.good
          rich.families critical desiredProduct desiredFine desiredCoarse)
    (volumeAbsorption :
      PureWZ2Prop62PacketCellInput.FourDegreeLemmaOutputData.ExtremalVolumeAbsorptionData
        (delta := delta) (rho := rho.1)
        desiredFine desiredCoarse
        (Kakeya.realRpowENN (delta / rho.1) (sigma - outputLoss))
        (Kakeya.realRpowENN rho.1 (sigma - outputLoss)))
    (assembly :
      rich.canonicalOutput.FinalAssemblyInputsData
        rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
          rich.exactification rich.parentDegree rich.core rich.good
          rich.families critical criticalInputs productInputs
          componentInputs volumeAbsorption sourceFiberConstant) :
    PureWZ2PropStickyData
      (sigma := sigma)
      (outputLoss := outputLoss)
      normalized.croppedRefined rho 61 := by
  let assembled :=
    rich.canonicalOutput.assemblePropSticky
      rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
        rich.exactification rich.parentDegree rich.core rich.good
        rich.families critical criticalInputs productInputs componentInputs
        volumeAbsorption assembly
  exact
    rich.repackagePropStickySixtyOne assembled rfl HEq.rfl

end Prop62V4RichCertificateCompanionData

end Kakeya.Assouad.Prop62PaperAudit.V4

end
