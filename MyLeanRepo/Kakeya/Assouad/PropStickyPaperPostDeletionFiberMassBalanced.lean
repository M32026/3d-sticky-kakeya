import MyLeanRepo.Kakeya.Assouad.PropStickyPaperInitialBalancing
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalMultiplicityComparison
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPostDeletionFiberMassRegularization
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRepairedFinalBalancedCover

/-!
# Balanced cover after complete-fiber-mass CWA regularization

After the faithful second coarse-parent selection, rerun the paper's finite
whole-cell balancing on exactly the pulled-back complete fibers.  The final
coarse family is unchanged, so its restored nearby-scale CWA remains
available, while the final shadings acquire the synchronized common
`mu_fine` and `mu_coarse` bands required by the last product comparison.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPostDeletionFiberMassBalancedData
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
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (finalLogExponent : ℕ) where
  bandData :
    WZ2PaperGlobalMultiplicityBandData
      joint.pullback.selectedFineShading
  rebalancing :
    WZ2PaperWholeCellRebalancingRepairedData
      joint.pullback.restrictedCover
      joint.pullback.selectedFineShading
      bandData hdelta hrho
  finalData :
    WZ2PaperRepairedFinalBalancedCoverData
      joint.pullback.restrictedCover
      joint.pullback.selectedFineShading
      bandData hdelta hrho rebalancing finalLogExponent

structure WZ2PaperPostDeletionFiberMassComparisonData
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
    {joint :
      WZ2PaperPostDeletionFiberMassRegularizationData
        packed cover fineShading packedCoarseShading
        ambientConstant outputConstant normalizationWeight weightUpper
        packedConstant levelCount}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {finalLogExponent : ℕ}
    (balanced :
      WZ2PaperPostDeletionFiberMassBalancedData
        joint hdelta hrho finalLogExponent)
    (massLower volumeUpper : ENNReal) where
  comparison :
    WZ2PaperFinalMultiplicityComparisonData
      joint.pullback.restrictedCover
      balanced.finalData.producer.coarseBand.selectedFineShading
      balanced.finalData.producer.coarseBand.selectedCoarseShading
      balanced.finalData.producer.finalCover.balanced
      balanced.finalData.producer.coarseBand.level
      balanced.finalData.producer.fiberBand.level
      massLower volumeUpper

/--
The quantitative fiber part of the synchronized final core.

The density is a final output parameter.  It is not asserted to equal the
input fiber density before the global whole-cell refinements.
-/
structure WZ2PaperPostDeletionSynchronizedFiberMassData
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
    {joint :
      WZ2PaperPostDeletionFiberMassRegularizationData
        packed cover fineShading packedCoarseShading
        ambientConstant outputConstant normalizationWeight weightUpper
        packedConstant levelCount}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {finalLogExponent : ℕ}
    (balanced :
      WZ2PaperPostDeletionFiberMassBalancedData
        joint hdelta hrho finalLogExponent)
    (finalDensity : ENNReal) : Type where
  fiber_mass_lower :
    ∀ parent : Fin joint.regularized.selected.family.card,
      finalDensity *
            (joint.pullback.restrictedCover.fullFiberSubfamily
              parent).family.enncard *
            Kakeya.realRpowENN delta 2 ≤
        (restrictPaperShading
          (joint.pullback.restrictedCover.fullFiberSubfamily parent)
          balanced.finalData.producer.coarseBand.selectedFineShading).mass

theorem wz2_paper_post_deletion_fiber_mass_balanced
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hScale : 18 * delta ≤ rho)
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
    (fineLine :
      WZ1PaperIsLineClass joint.pullback.selectedFine.family)
    (coarseLine :
      WZ1PaperIsLineClass joint.regularized.selected.family)
    (hBoundary :
      ∀ bandData :
          WZ2PaperGlobalMultiplicityBandData
            joint.pullback.selectedFineShading,
        (2 ^ (bandData.level + 1) : ENNReal) *
              ENNReal.ofReal (1000 * delta / rho) <
            bandData.band.mass)
    (hCrop :
      ∀ bandData :
          WZ2PaperGlobalMultiplicityBandData
            joint.pullback.selectedFineShading,
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
              initialBalancing.refined.mass)
    (finalLogExponent : ℕ)
    (hFinal :
      ∀ bandData :
          WZ2PaperGlobalMultiplicityBandData
            joint.pullback.selectedFineShading,
        ∀ rebalancing :
            WZ2PaperWholeCellRebalancingRepairedData
              joint.pullback.restrictedCover
              joint.pullback.selectedFineShading
              bandData hdelta hrho,
          ∀ producer :
              WZ2PaperFinalBalancedCoverProducerData
                (hdelta := hdelta) (hrho := hrho)
                joint.pullback.restrictedCover
                rebalancing.cropPruning.refined
                rebalancing.cropPruning.retainedCoarseCells
                rebalancing.cropPruning.selectedFineCells
                rebalancing.cropPruning.croppedBalancing
                rebalancing.coarseData,
            wz1PaperRefinementFraction delta finalLogExponent *
                  wz2PaperFinalBalancedCoverLoss producer ≤
                1) :
    Nonempty
      (WZ2PaperPostDeletionFiberMassBalancedData
        joint hdelta hrho finalLogExponent) := by
  rcases
      wz2_paper_global_multiplicity_band
        joint.pullback.selectedFineShading
        joint.pullback.selectedFine_cubical
    with ⟨bandData⟩
  rcases
      wz2_paper_repaired_final_balanced_cover
        hdelta hrho
        (by nlinarith)
        hrhoOne hScale
        joint.pullback.restrictedCover
        fineLine coarseLine
        joint.pullback.selectedFineShading bandData
        (hBoundary bandData)
        (hCrop bandData)
        finalLogExponent
        (hFinal bandData)
    with ⟨rebalancing, finalData⟩
  exact
    ⟨{
      bandData := bandData
      rebalancing := rebalancing
      finalData := finalData
    }⟩

theorem wz2_paper_post_deletion_fiber_mass_comparison
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
    {joint :
      WZ2PaperPostDeletionFiberMassRegularizationData
        packed cover fineShading packedCoarseShading
        ambientConstant outputConstant normalizationWeight weightUpper
        packedConstant levelCount}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {finalLogExponent : ℕ}
    (balanced :
      WZ2PaperPostDeletionFiberMassBalancedData
        joint hdelta hrho finalLogExponent)
    (massLower volumeUpper : ENNReal)
    (hMass :
      massLower ≤
        balanced.finalData.producer.coarseBand.selectedFineShading.mass)
    (hVolume :
      MeasureTheory.volume
          balanced.finalData.producer.coarseBand.selectedFineShading.union ≤
        volumeUpper) :
    Nonempty
      (WZ2PaperPostDeletionFiberMassComparisonData
        balanced massLower volumeUpper) := by
  rcases
      wz2_paper_final_multiplicity_comparison
        joint.pullback.restrictedCover
        balanced.finalData.producer.coarseBand.selectedFineShading
        balanced.finalData.producer.coarseBand.selectedCoarseShading
        balanced.finalData.producer.finalCover.balanced
        balanced.finalData.producer.coarseBand.level
        balanced.finalData.producer.fiberBand.level
        balanced.finalData.producer.finalCover.coarse_multiplicity_band
        balanced.finalData.producer.finalCover.fiber_multiplicity_band
        massLower volumeUpper hMass hVolume
    with ⟨comparison⟩
  exact ⟨{ comparison := comparison }⟩

theorem
    WZ2PaperPostDeletionFiberMassBalancedData.final_subshading
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
    {joint :
      WZ2PaperPostDeletionFiberMassRegularizationData
        packed cover fineShading packedCoarseShading
        ambientConstant outputConstant normalizationWeight weightUpper
        packedConstant levelCount}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {finalLogExponent : ℕ}
    (balanced :
      WZ2PaperPostDeletionFiberMassBalancedData
        joint hdelta hrho finalLogExponent) :
    ∀ index,
      balanced.finalData.producer.coarseBand.selectedFineShading.carrier
          index ⊆
        joint.pullback.selectedFineShading.carrier index := by
  intro index
  have hFinal :
      balanced.finalData.producer.coarseBand.selectedFineShading.carrier
            index ⊆
        balanced.rebalancing.cropPruning.croppedBalancing.refined.carrier
          index :=
    balanced.finalData.finalRefinement.subshading index
  have hCrop :
      balanced.rebalancing.cropPruning.croppedBalancing.refined.carrier
            index ⊆
        balanced.rebalancing.initialBalancing.refined.carrier index := by
    rw [
      balanced.rebalancing.cropPruning.croppedBalancing_refined_eq
    ]
    exact balanced.rebalancing.cropPruning.refined_subshading index
  have hInitial :
      balanced.rebalancing.initialBalancing.refined.carrier index ⊆
        balanced.rebalancing.boundaryPruning.pruned.carrier index :=
    balanced.rebalancing.initialBalancing.refined_subshading index
  have hBoundary :
      balanced.rebalancing.boundaryPruning.pruned.carrier index ⊆
        balanced.bandData.band.carrier index :=
    balanced.rebalancing.boundaryPruning.pruned_subshading index
  have hBand :
      balanced.bandData.band.carrier index ⊆
        joint.pullback.selectedFineShading.carrier index := by
    rw [balanced.bandData.band_eq]
    exact
      wz1PaperDyadicBandSubshading_isSubshading
        joint.pullback.selectedFineShading
        balanced.bandData.level index
  exact hFinal.trans
    (hCrop.trans (hInitial.trans (hBoundary.trans hBand)))

end Kakeya.Assouad

end
