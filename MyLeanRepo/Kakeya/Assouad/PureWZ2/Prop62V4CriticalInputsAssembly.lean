import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4FinalCoarseCriticalWitness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4FinalFiberCriticalWitness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4PureScalarInputs

/-!
# Proposition 6.2 V4 critical-input assembly

This module packages the exact terminal coarse and complete-fiber critical
floors into `CriticalMultiplicityInputsData`.

The coarse floor remains an explicit parameter.  In particular, this module
does not assume density of the canonical final coarse ordinary trace.  A
caller may instead supply any `Prop62V4FinalCoarseCriticalWitness` whose
ordinary shaded union lies in the exact terminal coarse shaded union.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open Kakeya.Assouad
open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace Prop62V4CriticalInputsAssembly

/--
Reindex the selected pure critical witness by the final cap-loss budget.
The structural loss, threshold, and volume-floor theorem are unchanged.
-/
def criticalForCap
    {polylogExponent cwaPower packetDensityExponent
      cwaLossExponent : ℕ}
    {sigma outputLoss : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss} :
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

end Prop62V4CriticalInputsAssembly

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
    {packetDensityExponent cwaLossExponent polylogExponent cwaPower : ℕ}
    {outputLoss : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss}
    (rich :
      Prop62V4RichCertificateCompanionData
        (eta := eta)
        (packetDensityExponent := packetDensityExponent)
        (cwaLossExponent := cwaLossExponent)
        (polylogExponent := polylogExponent)
        hdelta
        (prop62V4FixedGridMetricCompanionOfCertificate
          normalized preparation metricCertificate))
    (scalar :
      Prop62V4PureScalarInputs
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss routing)

/--
Package an already established coarse volume floor and the exact parentwise
final-fiber witnesses.  All remaining fields are scalar consequences of the
common V4 threshold.
-/
theorem criticalMultiplicityInputsOfVolumeFloor
    (deltaLe : delta ≤ scalar.delta₀)
    (rhoLower : Real.rpow delta (1 - outputLoss) ≤ rho.1)
    (rhoUpper : rho.1 ≤ Real.rpow delta outputLoss)
    (coarseVolumeFloor :
      Kakeya.realRpowENN rho.1
          (sigma + wz2PaperCriticalFloorLoss outputLoss) ≤
        volume rich.outputCertificate.coarseShading.union)
    (fiberWitnesses :
      ∀ parent : Fin rich.families.restriction.coarseSelected.family.card,
        Nonempty
          (PureWZ2Prop62CriticalRescaledFiberFloorWitness
            (loss := routing.critical.structuralLoss)
            (rich.canonicalOutput.terminalFiberShading
              rich.packetInput rich.multiplicity rich.parentClass
                rich.treeCleanup rich.exactification rich.parentDegree
                rich.core rich.good rich.families parent)
            (rich.families.restriction.coarseSelected.family.tube parent)
            rich.packetInput.rho_pos)) :
    rich.canonicalOutput.CriticalMultiplicityInputsData
      rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
        rich.exactification rich.parentDegree rich.core rich.good rich.families
        (Prop62V4CriticalInputsAssembly.criticalForCap
          (routing := routing)) := by
  refine
    {
      rho_small :=
        scalar.rho_small hdelta deltaLe rhoUpper
      ratio_small :=
        scalar.ratio_small hdelta deltaLe metricCertificate.rho_pos rhoLower
      ratio_critical :=
        scalar.ratio_critical
          hdelta deltaLe metricCertificate.rho_pos rhoLower
      coarse_volume_floor := ?_
      fiber_witness := ?_
      coarse_constant_absorption := ?_
      fine_constant_absorption := ?_
    }
  · exact coarseVolumeFloor
  · exact fiberWitnesses
  · simpa [routing.numerics.hierarchy.criticalFloorLoss_eq] using
      scalar.coarse_constant
        hdelta deltaLe metricCertificate.rho_pos rhoUpper
  · simpa [routing.numerics.hierarchy.criticalFloorLoss_eq] using
      scalar.fiber_constant
        hdelta deltaLe metricCertificate.rho_pos rhoLower

/--
Exact fixed-grid V4 specialization.  The coarse witness is supplied by the
caller, while the complete-fiber witnesses are the existing normalization
trace witnesses on the unchanged terminal fibers.
-/
theorem criticalMultiplicityInputs
    (deltaLe : delta ≤ scalar.delta₀)
    (rhoLower : Real.rpow delta (1 - outputLoss) ≤ rho.1)
    (rhoUpper : rho.1 ≤ Real.rpow delta outputLoss)
    (sourceLoss_le :
      sourceLoss ≤ routing.numerics.hierarchy.sourceLoss)
    (eta_eq : eta = routing.numerics.hierarchy.stableLoss)
    (coarseWitness :
      Prop62V4FinalCoarseCriticalWitness
        rich.outputCertificate routing.critical.structuralLoss) :
    rich.canonicalOutput.CriticalMultiplicityInputsData
      rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
        rich.exactification rich.parentDegree rich.core rich.good rich.families
        (Prop62V4CriticalInputsAssembly.criticalForCap
          (routing := routing)) :=
  rich.criticalMultiplicityInputsOfVolumeFloor scalar
    deltaLe rhoLower rhoUpper
    (Prop62V4FinalCoarseCriticalWitness.volume_floor
      (Prop62V4CriticalInputsAssembly.criticalForCap (routing := routing))
      coarseWitness
      (scalar.rho_critical
        hdelta deltaLe rhoUpper))
    (by
      have witnesses :=
        FixedGridPureScalar.critical_witnesses
          rich scalar deltaLe rhoLower sourceLoss_le eta_eq
      intro parent
      have witness := witnesses parent
      change
        Nonempty
          (PureWZ2Prop62CriticalRescaledFiberFloorWitness
            (loss := routing.critical.structuralLoss)
            (rich.canonicalOutput.terminalFiberShading
              rich.packetInput rich.multiplicity rich.parentClass
                rich.treeCleanup rich.exactification rich.parentDegree
                rich.core rich.good rich.families parent)
            (rich.families.restriction.coarseSelected.family.tube parent)
            rich.packetInput.rho_pos)
        at witness
      exact witness)

end Prop62V4RichCertificateCompanionData

end Kakeya.Assouad.Prop62PaperAudit.V4

end
