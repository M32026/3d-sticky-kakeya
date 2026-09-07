import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSubfamilyBoundaryMass
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCropBoundaryNormalized
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperExactBalancingMassRetention
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperInitialBalancingStatements

/-!
# Direct geometric balancing helpers

Closed aggregate boundary-absorption and exact-balancing estimates used by
the direct geometric balancing route.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

theorem wz2_paper_direct_subfamily_crossing_absorption_from_scaled_floor
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hPeriodicScale : 50 * delta ≤ rho)
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    (ambientNonempty : ambient.Nonempty)
    (ambientLine : WZ1PaperIsLineClass ambient)
    (selected : Kakeya.Streamlined.TubeSubfamily ambient)
    (shading : WZ1PaperTubeShading selected.family)
    {topLevelConstant : ENNReal}
    (topLevel :
      WZ2PaperConvexWolffBound ambient topLevelConstant)
    (bandData : WZ2PaperGlobalMultiplicityBandData shading)
    (bandFactor scalarFloor : ENNReal)
    (hScalar :
      2 * bandFactor * 24000000 *
            (topLevelConstant * wz2PaperBoundaryGeometryConstant + 1) *
            ENNReal.ofReal (Real.sqrt (delta / rho)) <
        scalarFloor)
    (hFloor :
      scalarFloor *
            (Kakeya.realRpowENN delta 2 * ambient.enncard) ≤
        bandFactor * bandData.band.mass)
    (hBandFactorPos : 0 < bandFactor)
    (hBandFactorTop : bandFactor ≠ ⊤) :
    2 *
        (∑ index : Fin selected.family.card,
          volume
            (bandData.band.carrier index ∩
              wz2PaperBoundaryCrossingRegion
                (rho := rho) bandData.band hdelta)) <
      bandData.band.mass := by
  let crossingCells :=
    wz2PaperBoundaryCrossingFineCells
      (rho := rho) bandData.band hdelta
  have hCrossingData :
      ∀ cell ∈ crossingCells,
        cell ∈ wz1PaperActiveCells bandData.band hdelta ∧
          ¬ (wz1PaperGridCube delta cell ⊆
            wz1PaperGridCube rho
              (wz1PaperGridIndex rho
                (cellCorner delta cell))) := by
    classical
    intro cell hcell
    have hsplit := Finset.mem_sdiff.mp hcell
    refine ⟨hsplit.1, ?_⟩
    rw [wz2PaperBoundarySafeFineCells, Finset.mem_filter] at hsplit
    intro hcontain
    exact hsplit.2 ⟨hsplit.1, hcontain⟩
  have hCrossingSubset :
      wz2PaperBoundaryCrossingRegion
          (rho := rho) bandData.band hdelta ⊆
        wz2PaperGridBoundaryRegion delta rho := by
    dsimp only [wz2PaperBoundaryCrossingRegion]
    exact
      wz2_paper_crossing_region_subset_grid_boundary
        bandData.band_cubical hdelta hrho crossingCells hCrossingData
  have hGridMass :=
    wz2_paper_subfamily_grid_boundary_mass_normalized
      hdelta hdeltaSmall hrho hrhoOne hPeriodicScale
      ambientLine selected bandData.band topLevel
  let crossingMass : ENNReal :=
    ∑ index : Fin selected.family.card,
      volume
        (bandData.band.carrier index ∩
          wz2PaperBoundaryCrossingRegion
            (rho := rho) bandData.band hdelta)
  have hCrossingRaw :
      crossingMass ≤
        ambient.enncard *
          ((24000000 : ENNReal) *
            (topLevelConstant * wz2PaperBoundaryGeometryConstant + 1) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (Real.sqrt (delta / rho))) := by
    calc
      crossingMass ≤
          ∑ index : Fin selected.family.card,
            volume
              (bandData.band.carrier index ∩
                wz2PaperGridBoundaryRegion delta rho) := by
        dsimp only [crossingMass]
        exact Finset.sum_le_sum fun index _ =>
          measure_mono
            (Set.inter_subset_inter_right _ hCrossingSubset)
      _ ≤
          ambient.enncard *
            ((24000000 : ENNReal) *
              (topLevelConstant * wz2PaperBoundaryGeometryConstant + 1) *
              Kakeya.realRpowENN delta 2 *
              ENNReal.ofReal (Real.sqrt (delta / rho))) :=
        hGridMass
  have hAmbientCardPos : 0 < ambient.enncard := by
    change 0 < (ambient.card : ENNReal)
    exact_mod_cast ambientNonempty
  have hScaleFactorPos :
      0 <
        Kakeya.realRpowENN delta 2 * ambient.enncard :=
    ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hdelta 2)).ne'
      hAmbientCardPos.ne'
  have hScaleFactorTop :
      Kakeya.realRpowENN delta 2 * ambient.enncard ≠ ⊤ :=
    ENNReal.mul_ne_top
      (by simp [Kakeya.realRpowENN])
      (ENNReal.natCast_ne_top _)
  have hScaled :
      (2 * bandFactor * 24000000 *
          (topLevelConstant * wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (delta / rho))) *
          (Kakeya.realRpowENN delta 2 * ambient.enncard) <
        scalarFloor *
          (Kakeya.realRpowENN delta 2 * ambient.enncard) :=
    ENNReal.mul_lt_mul_left
      hScaleFactorPos.ne' hScaleFactorTop hScalar
  have hProduct :
      bandFactor * (2 * crossingMass) <
        bandFactor * bandData.band.mass := by
    calc
      bandFactor * (2 * crossingMass) ≤
          bandFactor *
            (2 *
              (ambient.enncard *
                ((24000000 : ENNReal) *
                  (topLevelConstant *
                      wz2PaperBoundaryGeometryConstant + 1) *
                  Kakeya.realRpowENN delta 2 *
                  ENNReal.ofReal (Real.sqrt (delta / rho))))) := by
        gcongr
      _ =
          (2 * bandFactor * 24000000 *
            (topLevelConstant *
                wz2PaperBoundaryGeometryConstant + 1) *
            ENNReal.ofReal (Real.sqrt (delta / rho))) *
            (Kakeya.realRpowENN delta 2 * ambient.enncard) := by
        ring
      _ <
          scalarFloor *
            (Kakeya.realRpowENN delta 2 * ambient.enncard) :=
        hScaled
      _ ≤ bandFactor * bandData.band.mass :=
        hFloor
  exact
    (ENNReal.mul_lt_mul_iff_right
      hBandFactorPos.ne' hBandFactorTop).mp hProduct

theorem wz2_paper_direct_subfamily_crop_absorption_from_scaled_floor
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    (ambientNonempty : ambient.Nonempty)
    (ambientLine : WZ1PaperIsLineClass ambient)
    (selected : Kakeya.Streamlined.TubeSubfamily ambient)
    (shading : WZ1PaperTubeShading selected.family)
    {topLevelConstant : ENNReal}
    (topLevel :
      WZ2PaperConvexWolffBound ambient topLevelConstant)
    (lossFactor scalarFloor : ENNReal)
    (hScalar :
      2 * lossFactor * wz2PaperCropBoundaryMassConstant *
            (topLevelConstant + 1) *
            ENNReal.ofReal (Real.sqrt rho) <
        scalarFloor)
    (hFloor :
      scalarFloor *
            (Kakeya.realRpowENN delta 2 * ambient.enncard) ≤
        lossFactor * shading.mass)
    (hLossFactorPos : 0 < lossFactor)
    (hLossFactorTop : lossFactor ≠ ⊤) :
    2 *
        (∑ index : Fin selected.family.card,
          volume
            (shading.carrier index ∩
              wz2PaperCropBoundaryRegion rho)) <
      shading.mass := by
  have hCropRaw :=
    wz2_paper_subfamily_crop_boundary_mass_normalized
      hdelta hdeltaSmall hrho hrhoOne hdeltaRho
      ambientLine selected shading topLevel
  let cropMass : ENNReal :=
    ∑ index : Fin selected.family.card,
      volume
        (shading.carrier index ∩
          wz2PaperCropBoundaryRegion rho)
  have hAmbientCardPos : 0 < ambient.enncard := by
    change 0 < (ambient.card : ENNReal)
    exact_mod_cast ambientNonempty
  have hScaleFactorPos :
      0 <
        Kakeya.realRpowENN delta 2 * ambient.enncard :=
    ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hdelta 2)).ne'
      hAmbientCardPos.ne'
  have hScaleFactorTop :
      Kakeya.realRpowENN delta 2 * ambient.enncard ≠ ⊤ :=
    ENNReal.mul_ne_top
      (by simp [Kakeya.realRpowENN])
      (ENNReal.natCast_ne_top _)
  have hScaled :
      (2 * lossFactor * wz2PaperCropBoundaryMassConstant *
          (topLevelConstant + 1) *
          ENNReal.ofReal (Real.sqrt rho)) *
          (Kakeya.realRpowENN delta 2 * ambient.enncard) <
        scalarFloor *
          (Kakeya.realRpowENN delta 2 * ambient.enncard) :=
    ENNReal.mul_lt_mul_left
      hScaleFactorPos.ne' hScaleFactorTop hScalar
  have hProduct :
      lossFactor * (2 * cropMass) <
        lossFactor * shading.mass := by
    calc
      lossFactor * (2 * cropMass) ≤
          lossFactor *
            (2 *
              (wz2PaperCropBoundaryMassConstant *
                (topLevelConstant + 1) *
                Kakeya.realRpowENN delta 2 *
                ENNReal.ofReal (Real.sqrt rho) *
                ambient.enncard)) := by
        dsimp only [cropMass]
        gcongr
      _ =
          (2 * lossFactor * wz2PaperCropBoundaryMassConstant *
            (topLevelConstant + 1) *
            ENNReal.ofReal (Real.sqrt rho)) *
            (Kakeya.realRpowENN delta 2 * ambient.enncard) := by
        ring
      _ <
          scalarFloor *
            (Kakeya.realRpowENN delta 2 * ambient.enncard) :=
        hScaled
      _ ≤ lossFactor * shading.mass :=
        hFloor
  exact
    (ENNReal.mul_lt_mul_iff_right
      hLossFactorPos.ne' hLossFactorTop).mp hProduct

theorem wz2_paper_direct_exact_balancing_scaled_floor
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    (hdelta : 0 < delta)
    (bandData : WZ2PaperGlobalMultiplicityBandData shading)
    {multiplicityCap : ENNReal}
    (pruning :
      WZ2PaperBoundaryCellPruningData
        (rho := rho) bandData.band hdelta multiplicityCap)
    (balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) pruning.pruned pruning.coarseCells
        pruning.availableFineCells)
    (hCrossingHalf :
      2 *
          (∑ index : Fin fine.card,
            volume
              (bandData.band.carrier index ∩
                pruning.crossingRegion)) <
        bandData.band.mass) :
    let availableLog : ENNReal :=
      ((Nat.log 2
          (∑ coarseCell ∈ pruning.coarseCells,
            (pruning.availableFineCells coarseCell).card) + 1 : ℕ) :
        ENNReal)
    bandData.band.mass ≤
      (8 * availableLog) * balancing.refined.mass := by
  dsimp only
  let crossingMass : ENNReal :=
    ∑ index : Fin fine.card,
      volume
        (bandData.band.carrier index ∩ pruning.crossingRegion)
  have hCrossingFinite : crossingMass ≠ ⊤ := by
    apply ne_top_of_lt
    calc
      crossingMass ≤ 2 * crossingMass := by
        exact le_mul_of_one_le_left' (by norm_num)
      _ < bandData.band.mass := hCrossingHalf
  have hCrossingLtPruned :
      crossingMass < pruning.pruned.mass := by
    apply (ENNReal.add_lt_add_iff_right hCrossingFinite).mp
    calc
      crossingMass + crossingMass = 2 * crossingMass := by ring
      _ < bandData.band.mass := hCrossingHalf
      _ = pruning.pruned.mass + crossingMass := by
        simpa [crossingMass] using pruning.source_mass_eq_crossing
  have hBandHalf :
      bandData.band.mass ≤ 2 * pruning.pruned.mass := by
    calc
      bandData.band.mass =
          pruning.pruned.mass + crossingMass := by
        simpa [crossingMass] using pruning.source_mass_eq_crossing
      _ ≤ pruning.pruned.mass + pruning.pruned.mass := by
        exact add_le_add_right hCrossingLtPruned.le _
      _ = 2 * pruning.pruned.mass := by ring
  rcases
      wz2_paper_exact_balancing_mass_retention
        hdelta bandData.band bandData.level
        bandData.band_multiplicity multiplicityCap pruning balancing
    with ⟨retention⟩
  let availableLog : ENNReal :=
    ((Nat.log 2
        (∑ coarseCell ∈ pruning.coarseCells,
          (pruning.availableFineCells coarseCell).card) + 1 : ℕ) :
      ENNReal)
  calc
    bandData.band.mass ≤ 2 * pruning.pruned.mass := hBandHalf
    _ ≤
        2 * ((4 * availableLog) * balancing.refined.mass) := by
      gcongr
      simpa [availableLog] using retention.mass_retention
    _ = (8 * availableLog) * balancing.refined.mass := by ring

end Kakeya.Assouad

end
