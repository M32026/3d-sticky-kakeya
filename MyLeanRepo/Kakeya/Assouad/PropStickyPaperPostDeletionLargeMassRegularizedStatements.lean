import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRegularizedSynchronizedFineMultiplicity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPostDeletionFiberMassBalanced
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentDeletionMassRetentionStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGeometricReferenceFiberMass

/-!
# Final `largeMass` deletion and nearby-CWA recovery

Paper source:

> “There is a number `mu_fine` so that for each `T̃` ...”
>
> “each `delta`-cube is either preserved or deleted from all shadings in
> `𝕋_5[T̃]`.”
>
> “To fix this problem, we define `T̃_6 ⊂ T̃_5` to be the set of tubes for
> which [largeMass] holds.”

The input has already synchronized `mu_fine` and restored nearby CWA on the
complete-parent family `T̃_5`.  The output performs the final whole-cell
balancing, deletes parents that fail the absolute `largeMass` threshold, and
then repeats finite nearby-scale regularization on the surviving complete
parents.  This second regularization is explicit because an arbitrary parent
subfamily does not inherit normalized nearby CWA with the same constant.
-/

noncomputable section

namespace Kakeya.Assouad

def wz2PaperLargeMassPostDeletionTopLevelConstant
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambient : Kakeya.Streamlined.TubeFamily rho}
    {packed : Kakeya.Streamlined.TubeSubfamily ambient}
    {cover : WZ2PaperPartitioningCover fine packed.family}
    {fineShading : WZ1PaperTubeShading fine}
    {packedCoarseShading : WZ1PaperTubeShading packed.family}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    (joint :
      WZ2PaperPostDeletionFiberMassRegularizationData
        packed cover fineShading packedCoarseShading
        ambientConstant outputConstant normalizationWeight weightUpper
        packedConstant levelCount)
    (deletionWeight deletionRetentionConstant : ENNReal) : ENNReal :=
  (deletionWeight⁻¹ * deletionRetentionConstant) *
    ((normalizationWeight⁻¹ *
        (joint.regularized.regularizationLoss * weightUpper)) *
      packedConstant)

structure WZ2PaperLargeMassFinalFiberMassData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (threshold : ENNReal) : Type where
  final_fiber_mass_lower :
    ∀ parent : Fin coarse.card,
      threshold *
            (cover.fullFiberSubfamily parent).family.enncard *
            Kakeya.realRpowENN delta 2 ≤
        (restrictPaperShading
          (cover.fullFiberSubfamily parent) shading).mass

/-
This first monolithic draft is retained temporarily for local comparison.
The active API below splits the same fields along the paper's four steps so
Lean does not have to elaborate one very large dependent structure.

structure WZ2PaperPostDeletionLargeMassRegularizedInputData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    {synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    (regularized :
      WZ2PaperRegularizedSynchronizedFineMultiplicityData
        synchronized ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount) : Type where
  hdelta : 0 < delta
  hrho : 0 < rho
  hrho_le_one : rho ≤ 1
  scale_separation : 18 * delta ≤ rho
  fine_line :
    WZ1PaperIsLineClass
      regularized.joint.pullback.selectedFine.family
  coarse_line :
    WZ1PaperIsLineClass
      regularized.joint.regularized.selected.family
  boundary_absorption :
    ∀ bandData :
        WZ2PaperGlobalMultiplicityBandData
          regularized.joint.pullback.selectedFineShading,
      (2 ^ (bandData.level + 1) : ENNReal) *
            ENNReal.ofReal (1000 * delta / rho) <
        bandData.band.mass
  crop_absorption :
    ∀ bandData :
        WZ2PaperGlobalMultiplicityBandData
          regularized.joint.pullback.selectedFineShading,
      ∀ boundaryPruning :
          WZ2PaperBoundaryCellPruningData
            (rho := rho) bandData.band hdelta
            (2 ^ (bandData.level + 1) : ENNReal),
        ∀ initialBalancing :
            WZ2PaperExactCellBalancingData
              (rho := rho)
              boundaryPruning.pruned
              boundaryPruning.coarseCells
              boundaryPruning.availableFineCells,
          (2 ^ (bandData.level + 1) : ENNReal) *
              ENNReal.ofReal (48 * rho) <
            initialBalancing.refined.mass
  finalLogExponent : ℕ
  final_absorption :
    ∀ bandData :
        WZ2PaperGlobalMultiplicityBandData
          regularized.joint.pullback.selectedFineShading,
      ∀ rebalancing :
          WZ2PaperWholeCellRebalancingRepairedData
            regularized.joint.pullback.restrictedCover
            regularized.joint.pullback.selectedFineShading
            bandData hdelta hrho,
        ∀ producer :
            WZ2PaperFinalBalancedCoverProducerData
              (hdelta := hdelta) (hrho := hrho)
              regularized.joint.pullback.restrictedCover
              rebalancing.cropPruning.refined
              rebalancing.cropPruning.retainedCoarseCells
              rebalancing.cropPruning.selectedFineCells
              rebalancing.cropPruning.croppedBalancing
              rebalancing.coarseData,
          wz1PaperRefinementFraction delta finalLogExponent *
                wz2PaperFinalBalancedCoverLoss producer ≤
            1
  threshold : ENNReal
  deletionExponent : ℕ
  deletionWeight : ENNReal
  deletionRetentionConstant : ENNReal
  secondAmbientConstant : ENNReal
  secondOutputConstant : ENNReal
  secondNormalizationWeight : ENNReal
  secondWeightUpper : ENNReal
  secondLevelCount : ℕ
  deletionWeight_ne_zero : deletionWeight ≠ 0
  deletionWeight_ne_top : deletionWeight ≠ ⊤
  secondNormalizationWeight_ne_zero :
    secondNormalizationWeight ≠ 0
  secondNormalizationWeight_ne_top :
    secondNormalizationWeight ≠ ⊤
  secondWeightUpper_ne_top : secondWeightUpper ≠ ⊤
  secondAmbient_gt_two : 2 < secondAmbientConstant
  secondAmbient_ne_top : secondAmbientConstant ≠ ⊤
  second_levels_reach_one :
    ENNReal.ofReal (1 / rho) ≤
      secondAmbientConstant ^ secondLevelCount
  second_window :
    secondAmbientConstant * secondAmbientConstant ≤
      secondOutputConstant
  deletion_small :
    ∀ balanced :
        WZ2PaperPostDeletionFiberMassBalancedData
          regularized.joint hdelta hrho finalLogExponent,
      ∀ exactAdapter :
          WZ2PaperFinalBalancedCoverExactAdapterData
            balanced.finalData.producer,
        2 *
              (wz2PaperBalancedParentDegreeCap
                exactAdapter.exact
                balanced.finalData.producer.finalFine.fineLevel :
                ENNReal) *
              threshold *
              (∑ parent :
                  Fin regularized.joint.regularized.selected.family.card,
                wz2PaperGeometricReferenceFiberMass
                  regularized.joint.pullback.restrictedCover parent) <
          exactAdapter.exact.cellMass *
            exactAdapter.exact.retainedCoarseCells.card
  deletion_mass_budget :
    ∀ balanced :
        WZ2PaperPostDeletionFiberMassBalancedData
          regularized.joint hdelta hrho finalLogExponent,
      ∀ deletion :
          WZ2PaperFinalParentDeletionData
            balanced.finalData.producer
            (wz2PaperGeometricReferenceFiberMass
              regularized.joint.pullback.restrictedCover)
            threshold,
        let fineCap : ENNReal :=
          (2 ^ (balanced.finalData.producer.finalFine.fineLevel + 1) :
            ENNReal)
        let degreeCap : ENNReal :=
          wz2PaperBalancedParentDegreeCap
            deletion.exactAdapter.exact
            balanced.finalData.producer.finalFine.fineLevel
        fineCap *
              (2 * degreeCap * threshold *
                ∑ parent :
                    Fin regularized.joint.regularized.selected.family.card,
                  wz2PaperGeometricReferenceFiberMass
                    regularized.joint.pullback.restrictedCover parent) ≤
            (1 / 2 : ENNReal) *
              deletion.exactAdapter.exact.refined.mass
  deletion_fraction :
    wz1PaperRefinementFraction delta deletionExponent ≤
      (1 / 2 : ENNReal)
  deletion_cardinality :
    ∀ balanced :
        WZ2PaperPostDeletionFiberMassBalancedData
          regularized.joint hdelta hrho finalLogExponent,
      ∀ deletion :
          WZ2PaperFinalParentDeletionData
            balanced.finalData.producer
            (wz2PaperGeometricReferenceFiberMass
              regularized.joint.pullback.restrictedCover)
            threshold,
        deletionWeight *
              regularized.joint.regularized.selected.family.enncard ≤
          deletionRetentionConstant *
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              regularized.joint.regularized.selected.family
              deletion.deletion.retainedParents).family.enncard
  second_total_lower :
    ∀ balanced :
        WZ2PaperPostDeletionFiberMassBalancedData
          regularized.joint hdelta hrho finalLogExponent,
      ∀ deletion :
          WZ2PaperFinalParentDeletionData
            balanced.finalData.producer
            (wz2PaperGeometricReferenceFiberMass
              regularized.joint.pullback.restrictedCover)
            threshold,
        secondNormalizationWeight *
              regularized.joint.regularized.selected.family.enncard ≤
          deletion.restriction.selectedFineShading.mass
  second_weight_upper :
    ∀ balanced :
        WZ2PaperPostDeletionFiberMassBalancedData
          regularized.joint hdelta hrho finalLogExponent,
      ∀ deletion :
          WZ2PaperFinalParentDeletionData
            balanced.finalData.producer
            (wz2PaperGeometricReferenceFiberMass
              regularized.joint.pullback.restrictedCover)
            threshold,
        ∀ parent,
          (restrictPaperShading
            (deletion.restriction.restrictedCover.fullFiberSubfamily
              parent)
            deletion.restriction.selectedFineShading).mass ≤
              secondWeightUpper
  second_absorption :
    ∀ balanced :
        WZ2PaperPostDeletionFiberMassBalancedData
          regularized.joint hdelta hrho finalLogExponent,
      ∀ deletion :
          WZ2PaperFinalParentDeletionData
            balanced.finalData.producer
            (wz2PaperGeometricReferenceFiberMass
              regularized.joint.pullback.restrictedCover)
            threshold,
        let degreeConstant :=
          16 * ((secondLevelCount + 1 : ℕ) : ENNReal) *
            (Nat.log 2
              (2 * regularized.joint.regularized.selected.family.card) +
              1 : ENNReal) ^ (secondLevelCount + 1)
        let regularizationLoss :=
          (8 : ENNReal) *
            (Nat.log 2
              (2 * regularized.joint.regularized.selected.family.card) +
              1 : ENNReal) ^ (secondLevelCount + 2)
        max degreeConstant
            ((secondNormalizationWeight⁻¹ *
                (secondAmbientConstant *
                  (regularizationLoss * secondWeightUpper) *
                  degreeConstant)) *
              secondAmbientConstant) ≤
          secondOutputConstant

def WZ2PaperPostDeletionLargeMassRegularizedOutputData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    {synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    {regularized :
      WZ2PaperRegularizedSynchronizedFineMultiplicityData
        synchronized ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount}
    (input :
      WZ2PaperPostDeletionLargeMassRegularizedInputData regularized) :
    Type :=
  Σ balanced :
      WZ2PaperPostDeletionFiberMassBalancedData
        regularized.joint input.hdelta input.hrho
        input.finalLogExponent,
    Σ deletion :
        WZ2PaperFinalParentDeletionData
          balanced.finalData.producer
          (wz2PaperGeometricReferenceFiberMass
            regularized.joint.pullback.restrictedCover)
          input.threshold,
      Σ massRetention :
          WZ2PaperFinalParentDeletionMassRetentionData
            deletion input.deletionExponent,
        Σ finalRegularized :
            WZ2PaperPostDeletionFiberMassRegularizationData
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                regularized.joint.regularized.selected.family
                deletion.deletion.retainedParents)
              deletion.restriction.restrictedCover
              deletion.restriction.selectedFineShading
              deletion.restriction.selectedCoarseShading
              input.secondAmbientConstant
              input.secondOutputConstant
              input.secondNormalizationWeight
              input.secondWeightUpper
              (wz2PaperLargeMassPostDeletionTopLevelConstant
                regularized.joint input.deletionWeight
                input.deletionRetentionConstant)
              input.secondLevelCount,
          WZ2PaperLargeMassFinalFiberMassData
            finalRegularized.pullback.restrictedCover
            finalRegularized.pullback.selectedFineShading
            input.threshold

structure WZ2PaperPostDeletionLargeMassRegularizedStatement : Prop where
  run :
    ∀ {delta rho : ℝ}
      {fine : Kakeya.Streamlined.TubeFamily delta}
      {coarse : Kakeya.Streamlined.TubeFamily rho}
      {cover : WZ2PaperPartitioningCover fine coarse}
      {fineShading : WZ1PaperTubeShading fine}
      {coarseShading : WZ1PaperTubeShading coarse}
      {sourceDensity : ENNReal}
      {synchronized :
        WZ2PaperSynchronizedFineMultiplicityData
          cover fineShading coarseShading sourceDensity}
      {ambientConstant outputConstant normalizationWeight weightUpper
        packedConstant : ENNReal}
      {levelCount : ℕ}
      (regularized :
        WZ2PaperRegularizedSynchronizedFineMultiplicityData
          synchronized ambientConstant outputConstant normalizationWeight
          weightUpper packedConstant levelCount)
      (input :
        WZ2PaperPostDeletionLargeMassRegularizedInputData regularized),
      Nonempty
        (WZ2PaperPostDeletionLargeMassRegularizedOutputData input)
-/

structure WZ2PaperPostDeletionBalancingInputData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    {synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    (regularized :
      WZ2PaperRegularizedSynchronizedFineMultiplicityData
        synchronized ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount) : Type where
  hdelta : 0 < delta
  hrho : 0 < rho
  hrho_le_one : rho ≤ 1
  scale_separation : 18 * delta ≤ rho
  fine_line :
    WZ1PaperIsLineClass
      regularized.joint.pullback.selectedFine.family
  coarse_line :
    WZ1PaperIsLineClass
      regularized.joint.regularized.selected.family
  boundary_absorption :
    ∀ bandData :
        WZ2PaperGlobalMultiplicityBandData
          regularized.joint.pullback.selectedFineShading,
      (2 ^ (bandData.level + 1) : ENNReal) *
            ENNReal.ofReal (1000 * delta / rho) <
        bandData.band.mass
  crop_absorption :
    ∀ bandData :
        WZ2PaperGlobalMultiplicityBandData
          regularized.joint.pullback.selectedFineShading,
      ∀ boundaryPruning :
          WZ2PaperBoundaryCellPruningData
            (rho := rho) bandData.band hdelta
            (2 ^ (bandData.level + 1) : ENNReal),
        ∀ initialBalancing :
            WZ2PaperExactCellBalancingData
              (rho := rho)
              boundaryPruning.pruned
              boundaryPruning.coarseCells
              boundaryPruning.availableFineCells,
          (2 ^ (bandData.level + 1) : ENNReal) *
              ENNReal.ofReal (48 * rho) <
            initialBalancing.refined.mass
  finalLogExponent : ℕ
  final_absorption :
    ∀ bandData :
        WZ2PaperGlobalMultiplicityBandData
          regularized.joint.pullback.selectedFineShading,
      ∀ rebalancing :
          WZ2PaperWholeCellRebalancingRepairedData
            regularized.joint.pullback.restrictedCover
            regularized.joint.pullback.selectedFineShading
            bandData hdelta hrho,
        ∀ producer :
            WZ2PaperFinalBalancedCoverProducerData
              (hdelta := hdelta) (hrho := hrho)
              regularized.joint.pullback.restrictedCover
              rebalancing.cropPruning.refined
              rebalancing.cropPruning.retainedCoarseCells
              rebalancing.cropPruning.selectedFineCells
              rebalancing.cropPruning.croppedBalancing
              rebalancing.coarseData,
          wz1PaperRefinementFraction delta finalLogExponent *
                wz2PaperFinalBalancedCoverLoss producer ≤
            1

def WZ2PaperFinalDeletionSmall
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    {synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    {regularized :
      WZ2PaperRegularizedSynchronizedFineMultiplicityData
        synchronized ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount}
    (balancingInput :
      WZ2PaperPostDeletionBalancingInputData regularized)
    (threshold : ENNReal) : Prop :=
  ∀ balanced :
      WZ2PaperPostDeletionFiberMassBalancedData
        regularized.joint balancingInput.hdelta balancingInput.hrho
        balancingInput.finalLogExponent,
    ∀ exactAdapter :
        WZ2PaperFinalBalancedCoverExactAdapterData
          balanced.finalData.producer,
      2 *
            (wz2PaperBalancedParentDegreeCap
              exactAdapter.exact
              balanced.finalData.producer.finalFine.fineLevel :
              ENNReal) *
            threshold *
            (∑ parent :
                Fin regularized.joint.regularized.selected.family.card,
              wz2PaperGeometricReferenceFiberMass
                regularized.joint.pullback.restrictedCover parent) <
        exactAdapter.exact.cellMass *
          exactAdapter.exact.retainedCoarseCells.card

def WZ2PaperFinalDeletionMassBudget
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    {synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    {regularized :
      WZ2PaperRegularizedSynchronizedFineMultiplicityData
        synchronized ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount}
    (balancingInput :
      WZ2PaperPostDeletionBalancingInputData regularized)
    (threshold : ENNReal) : Prop :=
  ∀ balanced :
      WZ2PaperPostDeletionFiberMassBalancedData
        regularized.joint balancingInput.hdelta balancingInput.hrho
        balancingInput.finalLogExponent,
    ∀ deletion :
        WZ2PaperFinalParentDeletionData
          balanced.finalData.producer
          (wz2PaperGeometricReferenceFiberMass
            regularized.joint.pullback.restrictedCover)
          threshold,
      let fineCap : ENNReal :=
        (2 ^ (balanced.finalData.producer.finalFine.fineLevel + 1) :
          ENNReal)
      let degreeCap : ENNReal :=
        wz2PaperBalancedParentDegreeCap
          deletion.exactAdapter.exact
          balanced.finalData.producer.finalFine.fineLevel
      fineCap *
            (2 * degreeCap * threshold *
              ∑ parent :
                  Fin regularized.joint.regularized.selected.family.card,
                wz2PaperGeometricReferenceFiberMass
                  regularized.joint.pullback.restrictedCover parent) ≤
          (1 / 2 : ENNReal) *
            deletion.exactAdapter.exact.refined.mass

structure WZ2PaperPostDeletionLargeMassInputData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    {synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    {regularized :
      WZ2PaperRegularizedSynchronizedFineMultiplicityData
        synchronized ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount}
    (balancingInput :
      WZ2PaperPostDeletionBalancingInputData regularized) : Type where
  threshold : ENNReal
  deletionExponent : ℕ
  deletion_small :
    WZ2PaperFinalDeletionSmall balancingInput threshold
  deletion_mass_budget :
    WZ2PaperFinalDeletionMassBudget balancingInput threshold
  deletion_fraction :
    wz1PaperRefinementFraction delta deletionExponent ≤
      (1 / 2 : ENNReal)

structure WZ2PaperPostDeletionSecondParametersData
    (sourceAmbientConstant : ENNReal) : Type where
  deletionWeight : ENNReal
  deletionRetentionConstant : ENNReal
  ambientConstant : ENNReal
  outputConstant : ENNReal
  normalizationWeight : ENNReal
  weightUpper : ENNReal
  levelCount : ℕ
  deletionWeight_ne_zero : deletionWeight ≠ 0
  deletionWeight_ne_top : deletionWeight ≠ ⊤
  normalizationWeight_ne_zero : normalizationWeight ≠ 0
  normalizationWeight_ne_top : normalizationWeight ≠ ⊤
  weightUpper_ne_top : weightUpper ≠ ⊤
  ambient_gt_two : 2 < ambientConstant
  ambient_ne_top : ambientConstant ≠ ⊤
  sourceAmbient_le : sourceAmbientConstant ≤ ambientConstant

def WZ2PaperPostDeletionCardinalityBound
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    {synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    {regularized :
      WZ2PaperRegularizedSynchronizedFineMultiplicityData
        synchronized ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount}
    {balancingInput :
      WZ2PaperPostDeletionBalancingInputData regularized}
    (largeMass :
      WZ2PaperPostDeletionLargeMassInputData balancingInput)
    (parameters :
      WZ2PaperPostDeletionSecondParametersData outputConstant) : Prop :=
  ∀ balanced :
      WZ2PaperPostDeletionFiberMassBalancedData
        regularized.joint balancingInput.hdelta balancingInput.hrho
        balancingInput.finalLogExponent,
    ∀ deletion :
        WZ2PaperFinalParentDeletionData
          balanced.finalData.producer
          (wz2PaperGeometricReferenceFiberMass
            regularized.joint.pullback.restrictedCover)
          largeMass.threshold,
      parameters.deletionWeight *
            regularized.joint.regularized.selected.family.enncard ≤
        parameters.deletionRetentionConstant *
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            regularized.joint.regularized.selected.family
            deletion.deletion.retainedParents).family.enncard

def WZ2PaperPostDeletionTotalLowerBound
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    {synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    {regularized :
      WZ2PaperRegularizedSynchronizedFineMultiplicityData
        synchronized ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount}
    {balancingInput :
      WZ2PaperPostDeletionBalancingInputData regularized}
    (largeMass :
      WZ2PaperPostDeletionLargeMassInputData balancingInput)
    (parameters :
      WZ2PaperPostDeletionSecondParametersData outputConstant) : Prop :=
  ∀ balanced :
      WZ2PaperPostDeletionFiberMassBalancedData
        regularized.joint balancingInput.hdelta balancingInput.hrho
        balancingInput.finalLogExponent,
    ∀ deletion :
        WZ2PaperFinalParentDeletionData
          balanced.finalData.producer
          (wz2PaperGeometricReferenceFiberMass
            regularized.joint.pullback.restrictedCover)
          largeMass.threshold,
      parameters.normalizationWeight *
            regularized.joint.regularized.selected.family.enncard ≤
        deletion.restriction.selectedFineShading.mass

def WZ2PaperPostDeletionWeightUpperBound
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    {synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    {regularized :
      WZ2PaperRegularizedSynchronizedFineMultiplicityData
        synchronized ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount}
    {balancingInput :
      WZ2PaperPostDeletionBalancingInputData regularized}
    (largeMass :
      WZ2PaperPostDeletionLargeMassInputData balancingInput)
    (parameters :
      WZ2PaperPostDeletionSecondParametersData outputConstant) : Prop :=
  ∀ balanced :
      WZ2PaperPostDeletionFiberMassBalancedData
        regularized.joint balancingInput.hdelta balancingInput.hrho
        balancingInput.finalLogExponent,
    ∀ deletion :
        WZ2PaperFinalParentDeletionData
          balanced.finalData.producer
          (wz2PaperGeometricReferenceFiberMass
            regularized.joint.pullback.restrictedCover)
          largeMass.threshold,
      ∀ parent,
        (restrictPaperShading
          (deletion.restriction.restrictedCover.fullFiberSubfamily parent)
          deletion.restriction.selectedFineShading).mass ≤
            parameters.weightUpper

def WZ2PaperPostDeletionSecondAbsorption
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    {synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    {regularized :
      WZ2PaperRegularizedSynchronizedFineMultiplicityData
        synchronized ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount}
    {balancingInput :
      WZ2PaperPostDeletionBalancingInputData regularized}
    (largeMass :
      WZ2PaperPostDeletionLargeMassInputData balancingInput)
    (parameters :
      WZ2PaperPostDeletionSecondParametersData outputConstant) : Prop :=
  ∀ balanced :
      WZ2PaperPostDeletionFiberMassBalancedData
        regularized.joint balancingInput.hdelta balancingInput.hrho
        balancingInput.finalLogExponent,
    ∀ deletion :
        WZ2PaperFinalParentDeletionData
          balanced.finalData.producer
          (wz2PaperGeometricReferenceFiberMass
            regularized.joint.pullback.restrictedCover)
          largeMass.threshold,
      let degreeConstant :=
        16 * ((parameters.levelCount + 1 : ℕ) : ENNReal) *
          (Nat.log 2
            (2 * regularized.joint.regularized.selected.family.card) +
            1 : ENNReal) ^ (parameters.levelCount + 1)
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2
            (2 * regularized.joint.regularized.selected.family.card) +
            1 : ENNReal) ^ (parameters.levelCount + 2)
      max degreeConstant
          ((parameters.normalizationWeight⁻¹ *
              (parameters.ambientConstant *
                (regularizationLoss * parameters.weightUpper) *
                degreeConstant)) *
            parameters.ambientConstant) ≤
        parameters.outputConstant

structure WZ2PaperPostDeletionSecondBoundsData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    {synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    {regularized :
      WZ2PaperRegularizedSynchronizedFineMultiplicityData
        synchronized ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount}
    {balancingInput :
      WZ2PaperPostDeletionBalancingInputData regularized}
    (largeMass :
      WZ2PaperPostDeletionLargeMassInputData balancingInput)
    (parameters :
      WZ2PaperPostDeletionSecondParametersData outputConstant) : Type where
  levels_reach_one :
    ENNReal.ofReal (1 / rho) ≤
      parameters.ambientConstant ^ parameters.levelCount
  scale_window :
    parameters.ambientConstant * parameters.ambientConstant ≤
      parameters.outputConstant
  deletion_cardinality :
    WZ2PaperPostDeletionCardinalityBound largeMass parameters
  total_lower :
    WZ2PaperPostDeletionTotalLowerBound largeMass parameters
  weight_upper :
    WZ2PaperPostDeletionWeightUpperBound largeMass parameters
  absorption :
    WZ2PaperPostDeletionSecondAbsorption largeMass parameters

def WZ2PaperPostDeletionLargeMassRegularizedOutputData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    {synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    {regularized :
      WZ2PaperRegularizedSynchronizedFineMultiplicityData
        synchronized ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount}
    (balancingInput :
      WZ2PaperPostDeletionBalancingInputData regularized)
    (largeMass :
      WZ2PaperPostDeletionLargeMassInputData balancingInput)
    (parameters :
      WZ2PaperPostDeletionSecondParametersData outputConstant) : Type :=
  Σ balanced :
      WZ2PaperPostDeletionFiberMassBalancedData
        regularized.joint balancingInput.hdelta balancingInput.hrho
        balancingInput.finalLogExponent,
    Σ deletion :
        WZ2PaperFinalParentDeletionData
          balanced.finalData.producer
          (wz2PaperGeometricReferenceFiberMass
            regularized.joint.pullback.restrictedCover)
          largeMass.threshold,
      Σ massRetention :
          WZ2PaperFinalParentDeletionMassRetentionData
            deletion largeMass.deletionExponent,
        Σ finalRegularized :
            WZ2PaperPostDeletionFiberMassRegularizationData
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                regularized.joint.regularized.selected.family
                deletion.deletion.retainedParents)
              deletion.restriction.restrictedCover
              deletion.restriction.selectedFineShading
              deletion.restriction.selectedCoarseShading
              parameters.ambientConstant parameters.outputConstant
              parameters.normalizationWeight parameters.weightUpper
              (wz2PaperLargeMassPostDeletionTopLevelConstant
                regularized.joint parameters.deletionWeight
                parameters.deletionRetentionConstant)
              parameters.levelCount,
          WZ2PaperLargeMassFinalFiberMassData
            finalRegularized.pullback.restrictedCover
            finalRegularized.pullback.selectedFineShading
            largeMass.threshold

namespace WZ2PaperPostDeletionLargeMassRegularizedOutputData

def balanced
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    {synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    {regularized :
      WZ2PaperRegularizedSynchronizedFineMultiplicityData
        synchronized ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount}
    {balancingInput :
      WZ2PaperPostDeletionBalancingInputData regularized}
    {largeMass :
      WZ2PaperPostDeletionLargeMassInputData balancingInput}
    {parameters :
      WZ2PaperPostDeletionSecondParametersData outputConstant}
    (output :
      WZ2PaperPostDeletionLargeMassRegularizedOutputData
        balancingInput largeMass parameters) :=
  output.1

def deletion
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    {synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    {regularized :
      WZ2PaperRegularizedSynchronizedFineMultiplicityData
        synchronized ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount}
    {balancingInput :
      WZ2PaperPostDeletionBalancingInputData regularized}
    {largeMass :
      WZ2PaperPostDeletionLargeMassInputData balancingInput}
    {parameters :
      WZ2PaperPostDeletionSecondParametersData outputConstant}
    (output :
      WZ2PaperPostDeletionLargeMassRegularizedOutputData
        balancingInput largeMass parameters) :=
  output.2.1

def massRetention
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    {synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    {regularized :
      WZ2PaperRegularizedSynchronizedFineMultiplicityData
        synchronized ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount}
    {balancingInput :
      WZ2PaperPostDeletionBalancingInputData regularized}
    {largeMass :
      WZ2PaperPostDeletionLargeMassInputData balancingInput}
    {parameters :
      WZ2PaperPostDeletionSecondParametersData outputConstant}
    (output :
      WZ2PaperPostDeletionLargeMassRegularizedOutputData
        balancingInput largeMass parameters) :=
  output.2.2.1

def finalRegularized
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    {synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    {regularized :
      WZ2PaperRegularizedSynchronizedFineMultiplicityData
        synchronized ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount}
    {balancingInput :
      WZ2PaperPostDeletionBalancingInputData regularized}
    {largeMass :
      WZ2PaperPostDeletionLargeMassInputData balancingInput}
    {parameters :
      WZ2PaperPostDeletionSecondParametersData outputConstant}
    (output :
      WZ2PaperPostDeletionLargeMassRegularizedOutputData
        balancingInput largeMass parameters) :=
  output.2.2.2.1

def massCertificate
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    {synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    {regularized :
      WZ2PaperRegularizedSynchronizedFineMultiplicityData
        synchronized ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount}
    {balancingInput :
      WZ2PaperPostDeletionBalancingInputData regularized}
    {largeMass :
      WZ2PaperPostDeletionLargeMassInputData balancingInput}
    {parameters :
      WZ2PaperPostDeletionSecondParametersData outputConstant}
    (output :
      WZ2PaperPostDeletionLargeMassRegularizedOutputData
        balancingInput largeMass parameters) :=
  output.2.2.2.2

end WZ2PaperPostDeletionLargeMassRegularizedOutputData

structure WZ2PaperPostDeletionLargeMassRegularizedStatement : Prop where
  run :
    ∀ {delta rho : ℝ}
      {fine : Kakeya.Streamlined.TubeFamily delta}
      {coarse : Kakeya.Streamlined.TubeFamily rho}
      {cover : WZ2PaperPartitioningCover fine coarse}
      {fineShading : WZ1PaperTubeShading fine}
      {coarseShading : WZ1PaperTubeShading coarse}
      {sourceDensity : ENNReal}
      {synchronized :
        WZ2PaperSynchronizedFineMultiplicityData
          cover fineShading coarseShading sourceDensity}
      {ambientConstant outputConstant normalizationWeight weightUpper
        packedConstant : ENNReal}
      {levelCount : ℕ}
      (regularized :
        WZ2PaperRegularizedSynchronizedFineMultiplicityData
          synchronized ambientConstant outputConstant normalizationWeight
          weightUpper packedConstant levelCount)
      (balancingInput :
        WZ2PaperPostDeletionBalancingInputData regularized)
      (largeMass :
        WZ2PaperPostDeletionLargeMassInputData balancingInput)
      (parameters :
        WZ2PaperPostDeletionSecondParametersData outputConstant)
      (bounds :
        WZ2PaperPostDeletionSecondBoundsData largeMass parameters),
      Nonempty
        (WZ2PaperPostDeletionLargeMassRegularizedOutputData
          balancingInput largeMass parameters)

end Kakeya.Assouad

end
