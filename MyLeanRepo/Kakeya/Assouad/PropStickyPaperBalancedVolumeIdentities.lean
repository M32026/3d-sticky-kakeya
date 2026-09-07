import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers

/-!
# Volume identities for a literal paper balanced cover

The coarse shaded union is the disjoint union of its active literal
`rho`-cubes.  The fine shaded union is partitioned by the same cubes, and
balancedness gives the same fine mass in every active cube.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem WZ1PaperBalancedCoverData.coarse_union_volume
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ1PaperTubeCover fine coarse}
    {refined : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      WZ1PaperBalancedCoverData
        cover refined coarseShading)
    (hrho : 0 < rho) :
    MeasureTheory.volume coarseShading.union =
      (balanced.activeCells.card : ENNReal) *
        MeasureTheory.volume
          (wz1PaperGridCube rho (0, 0, 0)) := by
  rw [balanced.coarse_union_eq]
  exact wz1PaperGridCube_volume_biUnion hrho balanced.activeCells

theorem WZ1PaperBalancedCoverData.refined_union_subset_coarse
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ1PaperTubeCover fine coarse}
    {refined : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      WZ1PaperBalancedCoverData
        cover refined coarseShading) :
    refined.union ⊆ coarseShading.union := by
  intro point hpoint
  rcases hpoint with ⟨source, hsource⟩
  exact
    ⟨cover.parent source,
      balanced.point_compatibility source point hsource⟩

theorem WZ1PaperBalancedCoverData.fine_cell_partition
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ1PaperTubeCover fine coarse}
    {refined : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      WZ1PaperBalancedCoverData
        cover refined coarseShading) :
    refined.union =
      ⋃ cell ∈ balanced.activeCells,
        refined.union ∩ wz1PaperGridCube rho cell := by
  ext point
  constructor
  · intro hpoint
    have hcoarse :
        point ∈ coarseShading.union :=
      balanced.refined_union_subset_coarse hpoint
    rw [balanced.coarse_union_eq] at hcoarse
    rcases Set.mem_iUnion₂.mp hcoarse with
      ⟨cell, hcell, hpointCell⟩
    exact Set.mem_iUnion₂.mpr
      ⟨cell, hcell, hpoint, hpointCell⟩
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨_cell, _hcell, hpointRefined, _⟩
    exact hpointRefined

theorem WZ1PaperBalancedCoverData.fine_union_volume
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ1PaperTubeCover fine coarse}
    {refined : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      WZ1PaperBalancedCoverData
        cover refined coarseShading) :
    MeasureTheory.volume refined.union =
      (balanced.activeCells.card : ENNReal) *
        balanced.cellMass := by
  rw [balanced.fine_cell_partition]
  have hDisjoint :
      (balanced.activeCells : Set WZ2PaperCellIndex).PairwiseDisjoint
        (fun cell =>
          refined.union ∩ wz1PaperGridCube rho cell) := by
    intro first _ second _ hne
    exact
      (wz1PaperGridCube_disjoint hne).mono
        Set.inter_subset_right Set.inter_subset_right
  have hMeasurable :
      ∀ cell ∈ balanced.activeCells,
        MeasurableSet
          (refined.union ∩ wz1PaperGridCube rho cell) := by
    intro cell _
    exact
      (measurableSet_shading_union refined).inter
        (wz1PaperGridCube_measurable cell)
  rw [MeasureTheory.measure_biUnion_finset
    hDisjoint hMeasurable]
  calc
    (∑ cell ∈ balanced.activeCells,
        MeasureTheory.volume
          (refined.union ∩ wz1PaperGridCube rho cell)) =
        ∑ _cell ∈ balanced.activeCells,
          balanced.cellMass := by
      apply Finset.sum_congr rfl
      intro cell hcell
      exact balanced.fine_cell_mass cell hcell
    _ =
        (balanced.activeCells.card : ENNReal) *
          balanced.cellMass := by
      simp [Finset.sum_const]

theorem WZ1PaperBalancedCoverData.coarse_union_volume_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ1PaperTubeCover fine coarse}
    {refined : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      WZ1PaperBalancedCoverData
        cover refined coarseShading)
    (hrho : 0 < rho)
    (upper : ENNReal)
    (hNumerical :
      MeasureTheory.volume refined.union *
          MeasureTheory.volume
            (wz1PaperGridCube rho (0, 0, 0)) ≤
        upper * balanced.cellMass) :
    MeasureTheory.volume coarseShading.union ≤ upper := by
  let count : ENNReal := balanced.activeCells.card
  let cubeVolume : ENNReal :=
    MeasureTheory.volume
      (wz1PaperGridCube rho (0, 0, 0))
  have hProduct :
      MeasureTheory.volume coarseShading.union *
          balanced.cellMass =
        MeasureTheory.volume refined.union * cubeVolume := by
    rw [balanced.coarse_union_volume hrho,
      balanced.fine_union_volume]
    ring
  have hScaled :
      MeasureTheory.volume coarseShading.union *
          balanced.cellMass ≤
        upper * balanced.cellMass := by
    rw [hProduct]
    exact hNumerical
  have hCellZero : balanced.cellMass ≠ 0 :=
    balanced.cellMass_pos.ne'
  have hCellTop : balanced.cellMass ≠ ⊤ :=
    balanced.cellMass_ne_top
  have h :=
    mul_le_mul_right' hScaled balanced.cellMass⁻¹
  simpa [ENNReal.mul_inv_cancel hCellZero hCellTop,
    mul_assoc] using h

end Kakeya.Assouad

end
