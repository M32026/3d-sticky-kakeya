import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantOwnerRefinementStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCellIncidenceMassSum

/-! # Global refinement through dominant-owner exactification -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_dominant_owner_mass_comparison
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {active :
      WZ2PaperBalancedActiveParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData hdelta hrho}
    {multiplicityLevel : ℕ}
    (degree :
      WZ2PaperBalancedParentDegreeData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel)
    (dominant :
      WZ2PaperDominantParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree)
    {owned :
      WZ2PaperDominantParentFineCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree dominant}
    (exactified :
      WZ2PaperDominantOwnerExactificationData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree
        dominant owned) :
    balancing.refined.mass ≤
      wz2PaperDominantOwnerLoss exactified *
        exactified.refined.mass := by
  let incidenceLoss : ENNReal :=
    (2 ^ (multiplicityLevel + 1) : ENNReal) *
      (2 *
        (wz2PaperBalancedParentDegreeCap
          balancing multiplicityLevel : ENNReal))
  let dominantBinLoss : ENNReal :=
    2 *
      ((Nat.log 2
          (2 * balancing.retainedCoarseCells.card) + 1 : ℕ) :
        ENNReal)
  let exactificationLoss : ENNReal :=
    4 * (2 ^ (multiplicityLevel + 1) : ENNReal) *
      (exactified.countBins : ENNReal)
  have hIncidence :
      balancing.refined.mass ≤
        incidenceLoss *
          (∑ cell ∈ balancing.retainedCoarseCells,
            dominant.dominantMass cell) := by
    rw [wz2_paper_cell_incidence_mass_sum balancing]
    calc
      (∑ cell ∈ balancing.retainedCoarseCells,
          wz2PaperCellIncidenceMass
            (rho := rho) balancing.refined cell) ≤
          ∑ cell ∈ balancing.retainedCoarseCells,
            (2 ^ (multiplicityLevel + 1) : ENNReal) *
              balancing.cellMass := by
        apply Finset.sum_le_sum
        intro cell cell_mem
        exact degree.cell_incidence_upper cell cell_mem
      _ ≤
          ∑ cell ∈ balancing.retainedCoarseCells,
            (2 ^ (multiplicityLevel + 1) : ENNReal) *
              ((2 *
                (wz2PaperBalancedParentDegreeCap
                  balancing multiplicityLevel : ENNReal)) *
                dominant.dominantMass cell) := by
        apply Finset.sum_le_sum
        intro cell cell_mem
        gcongr
        exact dominant.dominant_lower cell cell_mem
      _ =
          incidenceLoss *
            (∑ cell ∈ balancing.retainedCoarseCells,
              dominant.dominantMass cell) := by
        rw [Finset.mul_sum]
        simp [incidenceLoss, mul_assoc]
  have hDominant :
      (∑ cell ∈ balancing.retainedCoarseCells,
          dominant.dominantMass cell) ≤
        dominantBinLoss *
          (∑ cell ∈ dominant.selectedCells,
            dominant.dominantMass cell) := by
    let denominator : ENNReal :=
      2 *
        ((Nat.log 2
            (2 * balancing.retainedCoarseCells.card) + 1 : ℕ) :
          ENNReal)
    have denominator_ne_zero : denominator ≠ 0 := by
      dsimp only [denominator]
      positivity
    have denominator_ne_top : denominator ≠ ⊤ := by
      dsimp only [denominator]
      exact ENNReal.mul_ne_top (by norm_num) (by simp)
    have hdiv :
        (∑ cell ∈ balancing.retainedCoarseCells,
            dominant.dominantMass cell) / denominator ≤
          ∑ cell ∈ dominant.selectedCells,
            dominant.dominantMass cell := by
      simpa [denominator] using dominant.selected_mass_retention
    rw [ENNReal.div_le_iff denominator_ne_zero denominator_ne_top] at hdiv
    simpa [dominantBinLoss, denominator, mul_comm] using hdiv
  have hExactification :
      (∑ cell ∈ dominant.selectedCells,
          dominant.dominantMass cell) ≤
        exactificationLoss * exactified.refined.mass := by
    simpa [exactificationLoss] using
      exactified.dominant_mass_retention
  calc
    balancing.refined.mass ≤
        incidenceLoss *
          (∑ cell ∈ balancing.retainedCoarseCells,
            dominant.dominantMass cell) :=
      hIncidence
    _ ≤
        incidenceLoss *
          (dominantBinLoss *
            (∑ cell ∈ dominant.selectedCells,
              dominant.dominantMass cell)) := by
      gcongr
    _ ≤
        incidenceLoss *
          (dominantBinLoss *
            (exactificationLoss * exactified.refined.mass)) := by
      gcongr
    _ =
        wz2PaperDominantOwnerLoss exactified *
          exactified.refined.mass := by
      simp only [wz2PaperDominantOwnerLoss, incidenceLoss,
        dominantBinLoss, exactificationLoss]
      ring

theorem wz2_paper_dominant_owner_refinement :
    WZ2PaperDominantOwnerRefinementStatement := by
  intro delta rho fine coarse cover sourceShading coarseCells
    availableFineCells balancing coarseData hdelta hrho active
    multiplicityLevel degree dominant owned exactified
    logExponent hAbsorb
  have hSource :
      balancing.refined.mass ≤
        wz2PaperDominantOwnerLoss exactified *
          exactified.refined.mass :=
    wz2_paper_dominant_owner_mass_comparison
      degree dominant exactified
  have hRetained :
      wz1PaperRefinementFraction delta logExponent *
          balancing.refined.mass ≤
        exactified.refined.mass := by
    calc
      wz1PaperRefinementFraction delta logExponent *
            balancing.refined.mass ≤
          wz1PaperRefinementFraction delta logExponent *
            (wz2PaperDominantOwnerLoss exactified *
              exactified.refined.mass) := by
        gcongr
      _ =
          (wz1PaperRefinementFraction delta logExponent *
            wz2PaperDominantOwnerLoss exactified) *
              exactified.refined.mass := by
        rw [mul_assoc]
      _ ≤ 1 * exactified.refined.mass := by
        gcongr
      _ = exactified.refined.mass := by simp
  exact ⟨{ source_mass_le := hSource, retained_mass := hRetained }⟩

end Kakeya.Assouad

end
