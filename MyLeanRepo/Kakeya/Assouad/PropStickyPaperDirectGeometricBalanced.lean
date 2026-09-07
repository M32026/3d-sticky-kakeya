import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDirectGeometricBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPostBalancingRefinementStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperInitialBalancing
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRepairedFinalBalancedCover

/-!
# Direct geometric balancing on the structural merged family

The paper chooses the caller-scale coarse family before refining the fine
shading.  This package runs the aggregate boundary deletion and final
whole-cell balancing directly on that fixed cover.  In particular, its
types contain no second coarse-parent regularization.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

structure WZ2PaperDirectGeometricAbsorptionData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta)
    (hrho : 0 < rho) : Prop where
  crossing_absorption :
    ∀ bandData : WZ2PaperGlobalMultiplicityBandData shading,
      2 *
          (∑ index : Fin fine.card,
            volume
              (bandData.band.carrier index ∩
                wz2PaperBoundaryCrossingRegion
                  (rho := rho) bandData.band hdelta)) <
        bandData.band.mass
  crop_absorption :
    ∀ bandData : WZ2PaperGlobalMultiplicityBandData shading,
      ∀ {multiplicityCap : ENNReal},
        ∀ boundaryPruning :
            WZ2PaperBoundaryCellPruningData
              (rho := rho) bandData.band hdelta multiplicityCap,
          ∀ initialBalancing :
              WZ2PaperExactCellBalancingData
                (rho := rho)
                boundaryPruning.pruned
                boundaryPruning.coarseCells
                boundaryPruning.availableFineCells,
            2 *
                (∑ index : Fin fine.card,
                  volume
                    (initialBalancing.refined.carrier index ∩
                      wz2PaperCropBoundaryRegion rho)) <
              initialBalancing.refined.mass
  post_balancing_absorption :
    ∀ bandData : WZ2PaperGlobalMultiplicityBandData shading,
      ∀ {multiplicityCap : ENNReal},
        ∀ boundaryPruning :
            WZ2PaperBoundaryCellPruningData
              (rho := rho) bandData.band hdelta multiplicityCap,
          wz1PaperRefinementFraction delta 2 *
              wz2PaperPostBalancingLoss boundaryPruning ≤
            1

structure WZ2PaperDirectGeometricInputData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta)
    (hrho : 0 < rho) where
  rho_le_one : rho ≤ 1
  scale_separation : 18 * delta ≤ rho
  refined_cubical : WZ1PaperIsCubicalShading shading
  fine_line : WZ1PaperIsLineClass fine
  coarse_line : WZ1PaperIsLineClass coarse
  geometric :
    WZ2PaperDirectGeometricAbsorptionData
      cover shading hdelta hrho
  final_absorption :
    ∀ bandData : WZ2PaperGlobalMultiplicityBandData shading,
      ∀ rebalancing :
          WZ2PaperWholeCellRebalancingRepairedData
            cover shading bandData hdelta hrho,
        ∀ producer :
            WZ2PaperFinalBalancedCoverProducerData
              (hdelta := hdelta) (hrho := hrho)
              cover rebalancing.cropPruning.refined
              rebalancing.cropPruning.retainedCoarseCells
              rebalancing.cropPruning.selectedFineCells
              rebalancing.cropPruning.croppedBalancing
              rebalancing.coarseData,
          wz1PaperRefinementFraction delta 14 *
                wz2PaperFinalBalancedCoverLoss producer ≤
            1

theorem wz2_paper_direct_geometric_from_scaled_floors
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    (hPeriodicScale : 50 * delta ≤ rho)
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    (ambientNonempty : ambient.Nonempty)
    (ambientLine : WZ1PaperIsLineClass ambient)
    (selected : Kakeya.Streamlined.TubeSubfamily ambient)
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover selected.family coarse)
    (shading : WZ1PaperTubeShading selected.family)
    {topLevelConstant : ENNReal}
    (topLevel :
      WZ2PaperConvexWolffBound ambient topLevelConstant)
    (bandFactor scalarFloor : ENNReal)
    (hCrossingScalar :
      2 * bandFactor * 24000000 *
            (topLevelConstant *
                wz2PaperBoundaryGeometryConstant + 1) *
            ENNReal.ofReal (Real.sqrt (delta / rho)) <
        scalarFloor)
    (hBandFloor :
      ∀ bandData : WZ2PaperGlobalMultiplicityBandData shading,
        scalarFloor *
              (Kakeya.realRpowENN delta 2 * ambient.enncard) ≤
          bandFactor * bandData.band.mass)
    (hBandFactorPos : 0 < bandFactor)
    (hBandFactorTop : bandFactor ≠ ⊤)
    (hCropScalar :
      ∀ bandData : WZ2PaperGlobalMultiplicityBandData shading,
        ∀ {multiplicityCap : ENNReal},
          ∀ boundaryPruning :
              WZ2PaperBoundaryCellPruningData
                (rho := rho) bandData.band hdelta multiplicityCap,
            let availableLog : ENNReal :=
              ((Nat.log 2
                  (∑ coarseCell ∈ boundaryPruning.coarseCells,
                    (boundaryPruning.availableFineCells coarseCell).card) +
                    1 : ℕ) : ENNReal)
            2 * (bandFactor * (8 * availableLog)) *
                  wz2PaperCropBoundaryMassConstant *
                  (topLevelConstant + 1) *
                  ENNReal.ofReal (Real.sqrt rho) <
              scalarFloor)
    (hPostBalancing :
      ∀ bandData : WZ2PaperGlobalMultiplicityBandData shading,
        ∀ {multiplicityCap : ENNReal},
          ∀ boundaryPruning :
              WZ2PaperBoundaryCellPruningData
                (rho := rho) bandData.band hdelta multiplicityCap,
            wz1PaperRefinementFraction delta 2 *
                wz2PaperPostBalancingLoss boundaryPruning ≤
              1) :
    WZ2PaperDirectGeometricAbsorptionData
      cover shading hdelta hrho := by
  have hCrossing :
      ∀ bandData : WZ2PaperGlobalMultiplicityBandData shading,
        2 *
            (∑ index : Fin selected.family.card,
              volume
                (bandData.band.carrier index ∩
                  wz2PaperBoundaryCrossingRegion
                    (rho := rho) bandData.band hdelta)) <
          bandData.band.mass := by
    intro bandData
    exact
      wz2_paper_direct_subfamily_crossing_absorption_from_scaled_floor
        hdelta hdeltaSmall hrho hrhoOne hPeriodicScale
        ambientNonempty ambientLine selected shading topLevel bandData
        bandFactor scalarFloor hCrossingScalar (hBandFloor bandData)
        hBandFactorPos hBandFactorTop
  exact
    {
      crossing_absorption := hCrossing
      crop_absorption := by
        intro bandData multiplicityCap boundaryPruning initialBalancing
        let availableLog : ENNReal :=
          ((Nat.log 2
              (∑ coarseCell ∈ boundaryPruning.coarseCells,
                (boundaryPruning.availableFineCells coarseCell).card) + 1 :
            ℕ) : ENNReal)
        let balancingFactor : ENNReal := 8 * availableLog
        let lossFactor : ENNReal := bandFactor * balancingFactor
        have hCrossingPruning :
            2 *
                (∑ index : Fin selected.family.card,
                  volume
                    (bandData.band.carrier index ∩
                      boundaryPruning.crossingRegion)) <
              bandData.band.mass := by
          rw [boundaryPruning.crossingRegion_eq_source]
          exact hCrossing bandData
        have hBalancingFloor :
            bandData.band.mass ≤
              balancingFactor * initialBalancing.refined.mass := by
          simpa only [balancingFactor, availableLog] using
            wz2_paper_direct_exact_balancing_scaled_floor
              hdelta bandData boundaryPruning initialBalancing
                hCrossingPruning
        have hScaledFloor :
            scalarFloor *
                  (Kakeya.realRpowENN delta 2 * ambient.enncard) ≤
              lossFactor * initialBalancing.refined.mass := by
          calc
            _ ≤ bandFactor * bandData.band.mass :=
              hBandFloor bandData
            _ ≤ bandFactor *
                (balancingFactor * initialBalancing.refined.mass) := by
              gcongr
            _ = lossFactor * initialBalancing.refined.mass := by
              dsimp only [lossFactor]
              ring
        have hAvailableLogPos : 0 < availableLog := by
          dsimp only [availableLog]
          positivity
        have hAvailableLogTop : availableLog ≠ ⊤ := by
          dsimp only [availableLog]
          simp
        have hBalancingFactorPos : 0 < balancingFactor := by
          dsimp only [balancingFactor]
          positivity
        have hBalancingFactorTop : balancingFactor ≠ ⊤ := by
          dsimp only [balancingFactor]
          exact ENNReal.mul_ne_top (by norm_num) hAvailableLogTop
        have hLossFactorPos : 0 < lossFactor :=
          ENNReal.mul_pos hBandFactorPos.ne' hBalancingFactorPos.ne'
        have hLossFactorTop : lossFactor ≠ ⊤ :=
          ENNReal.mul_ne_top hBandFactorTop hBalancingFactorTop
        exact
          wz2_paper_direct_subfamily_crop_absorption_from_scaled_floor
            hdelta hdeltaSmall hrho hrhoOne hdeltaRho
            ambientNonempty ambientLine selected initialBalancing.refined
            topLevel lossFactor scalarFloor
            (by
              simpa only [lossFactor, balancingFactor] using
                hCropScalar bandData boundaryPruning)
            hScaledFloor hLossFactorPos hLossFactorTop
      post_balancing_absorption := hPostBalancing
    }

structure WZ2PaperDirectBalancedData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (finalLogExponent : ℕ) where
  bandData : WZ2PaperGlobalMultiplicityBandData shading
  rebalancing :
    WZ2PaperWholeCellRebalancingRepairedData
      cover shading bandData hdelta hrho
  finalData :
    WZ2PaperRepairedFinalBalancedCoverData
      cover shading bandData hdelta hrho rebalancing finalLogExponent

theorem wz2_paper_direct_balanced_from_geometric_absorption
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hScale : 18 * delta ≤ rho)
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (refinedCubical : WZ1PaperIsCubicalShading shading)
    (fineLine : WZ1PaperIsLineClass fine)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (geometric :
      WZ2PaperDirectGeometricAbsorptionData
        cover shading hdelta hrho)
    (finalLogExponent : ℕ)
    (hFinal :
      ∀ bandData : WZ2PaperGlobalMultiplicityBandData shading,
        ∀ rebalancing :
            WZ2PaperWholeCellRebalancingRepairedData
              cover shading bandData hdelta hrho,
          ∀ producer :
              WZ2PaperFinalBalancedCoverProducerData
                (hdelta := hdelta) (hrho := hrho)
                cover rebalancing.cropPruning.refined
                rebalancing.cropPruning.retainedCoarseCells
                rebalancing.cropPruning.selectedFineCells
                rebalancing.cropPruning.croppedBalancing
                rebalancing.coarseData,
            wz1PaperRefinementFraction delta finalLogExponent *
                  wz2PaperFinalBalancedCoverLoss producer ≤
              1) :
    Nonempty
      (WZ2PaperDirectBalancedData
        cover shading hdelta hrho finalLogExponent) := by
  rcases wz2_paper_global_multiplicity_band shading refinedCubical with
    ⟨bandData⟩
  have hBoundary :
      (∑ index : Fin fine.card,
        volume
          (bandData.band.carrier index ∩
            wz2PaperBoundaryCrossingRegion
              (rho := rho) bandData.band hdelta)) <
        bandData.band.mass :=
    (le_mul_of_one_le_left' (by norm_num)).trans_lt
      (geometric.crossing_absorption bandData)
  have hdeltaRho : delta ≤ rho := by
    nlinarith
  rcases
      wz2_paper_whole_cell_rebalancing_from_boundary_mass
        hdelta hrho hdeltaRho hrhoOne hScale cover fineLine coarseLine
        shading bandData hBoundary
        (by
          intro boundaryPruning initialBalancing
          exact
            (le_mul_of_one_le_left' (by norm_num)).trans_lt
              (geometric.crop_absorption
                bandData boundaryPruning initialBalancing))
    with ⟨rebalancing⟩
  rcases
      wz2_paper_repaired_final_balanced_cover_from_rebalancing
        hdelta hrho hScale cover fineLine coarseLine shading bandData
        rebalancing finalLogExponent (hFinal bandData rebalancing)
    with ⟨finalData⟩
  exact
    ⟨{
      bandData := bandData
      rebalancing := rebalancing
      finalData := finalData
    }⟩

theorem wz2_paper_direct_balanced_from_geometric_input
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (input :
      WZ2PaperDirectGeometricInputData
        cover shading hdelta hrho) :
    Nonempty
      (WZ2PaperDirectBalancedData cover shading hdelta hrho 14) :=
  wz2_paper_direct_balanced_from_geometric_absorption
    hdelta hrho input.rho_le_one input.scale_separation cover shading
    input.refined_cubical input.fine_line input.coarse_line
    input.geometric 14 input.final_absorption

end Kakeya.Assouad

end
