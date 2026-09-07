import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RebalancedFiniteRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SourceWitnessCoarseShading
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers

/-!
# Complete fine-fiber mass behind source-witness coarse cells

Every coarse cell retained for one source-witness parent contains an actual
point of that parent's complete fine fiber.  Exact rebalancing makes the
fine shading cubical and puts the whole fine cube through that point inside
the same coarse cell.  Summing the resulting disjoint parent-cell incidence
masses compares the sampled coarse carrier with the complete fine-fiber
shaded mass.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Fine shaded incidence mass of one complete parent fiber inside one
literal coarse grid cell. -/
def sourceWitnessFineFiberCellMass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card)
    (cell : ℤ × ℤ × ℤ) : ENNReal :=
  ∑ source ∈ cover.toPaperTubeCover.fiberIndices parent,
    volume
      (fineShading.carrier source ∩
        wz1PaperGridCube rho cell)

/-- Every point of an exactly rebalanced fine shading lies in a fine cube
which is wholly contained in its literal coarse cell. -/
lemma PureWZ2RebalancedFiniteRefinementData.fine_cube_subset_coarse_cube
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading candidate : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    {hdelta : 0 < delta}
    (rebalanced :
      PureWZ2RebalancedFiniteRefinementData original candidate hdelta)
    (source : Fin fine.card) (point : Point3)
    (hpoint : point ∈ rebalanced.balancing.refined.carrier source) :
    wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
      wz1PaperGridCube rho (wz1PaperGridIndex rho point) := by
  have hpointUnion : point ∈ rebalanced.balancing.refined.union :=
    ⟨source, hpoint⟩
  rw [rebalanced.balancing.refined_union_eq] at hpointUnion
  rcases Set.mem_iUnion₂.mp hpointUnion with
    ⟨fineCell, hfineCell, hpointFineCell⟩
  have hfineIndex : wz1PaperGridIndex delta point = fineCell :=
    (mem_wz1PaperGridCube delta fineCell point).mp hpointFineCell
  rw [rebalanced.balancing.retainedFineCells_eq] at hfineCell
  rcases Finset.mem_biUnion.mp hfineCell with
    ⟨coarseCell, hcoarseCell, hselected⟩
  have hcontainment :=
    rebalanced.balancing.fine_cell_containment
      coarseCell hcoarseCell fineCell hselected
  have hpointCoarseCell : point ∈ wz1PaperGridCube rho coarseCell :=
    hcontainment hpointFineCell
  have hcoarseIndex : wz1PaperGridIndex rho point = coarseCell :=
    (mem_wz1PaperGridCube rho coarseCell point).mp hpointCoarseCell
  simpa [hfineIndex, hcoarseIndex] using hcontainment

/-- A retained source-witness parent/cell pair contributes at least one whole
fine cube to the complete fine-fiber incidence mass in that coarse cell. -/
theorem source_witness_fine_fiber_cell_mass_lower
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (sourceWitness : PureWZ2SourceWitnessCoarseShadingData balanced)
    (hdelta : 0 < delta)
    (hfineCubical : WZ1PaperIsCubicalShading fineShading)
    (hfineInside : ∀ source point, point ∈ fineShading.carrier source →
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        wz1PaperGridCube rho (wz1PaperGridIndex rho point))
    (parent : Fin coarse.card) (cell : ℤ × ℤ × ℤ)
    (hcell : cell ∈ sourceWitness.parentCells parent) :
    volume (wz1PaperGridCube delta (0, 0, 0)) ≤
      sourceWitnessFineFiberCellMass
        cover fineShading parent cell := by
  rcases sourceWitness.source_witness parent cell hcell with
    ⟨source, point, hparent, hpointFine, hpointCell⟩
  let fineCell := wz1PaperGridIndex delta point
  have hwholeFine : wz1PaperGridCube delta fineCell ⊆
      fineShading.carrier source :=
    hfineCubical source point hpointFine
  have hcoarseIndex : wz1PaperGridIndex rho point = cell :=
    (mem_wz1PaperGridCube rho cell point).mp hpointCell
  have hwholeCoarse : wz1PaperGridCube delta fineCell ⊆
      wz1PaperGridCube rho cell := by
    simpa [fineCell, hcoarseIndex] using
      hfineInside source point hpointFine
  have hsourceFiber :
      source ∈ cover.toPaperTubeCover.fiberIndices parent := by
    simp [WZ1PaperTubeCover.fiberIndices, hparent]
  have hcubeSubset : wz1PaperGridCube delta fineCell ⊆
      fineShading.carrier source ∩ wz1PaperGridCube rho cell :=
    fun other hother => ⟨hwholeFine hother, hwholeCoarse hother⟩
  have hterm : volume (wz1PaperGridCube delta fineCell) ≤
      volume
        (fineShading.carrier source ∩
          wz1PaperGridCube rho cell) :=
    measure_mono hcubeSubset
  calc
    volume (wz1PaperGridCube delta (0, 0, 0)) =
        volume (wz1PaperGridCube delta fineCell) :=
      (wz1PaperGridCube_volume_eq hdelta fineCell (0, 0, 0)).symm
    _ ≤ volume
        (fineShading.carrier source ∩
          wz1PaperGridCube rho cell) := hterm
    _ ≤ sourceWitnessFineFiberCellMass
          cover fineShading parent cell := by
      exact Finset.single_le_sum
        (fun index (_ : index ∈
          cover.toPaperTubeCover.fiberIndices parent) =>
            (show (0 : ENNReal) ≤ volume
              (fineShading.carrier index ∩
                wz1PaperGridCube rho cell) from bot_le))
        hsourceFiber

/-- Summing complete-fiber incidence over any finite set of distinct coarse
cells never exceeds that fiber's total shaded mass. -/
theorem sum_source_witness_fine_fiber_cell_mass_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card)
    (cells : Finset (ℤ × ℤ × ℤ)) :
    (∑ cell ∈ cells,
        sourceWitnessFineFiberCellMass
          cover fineShading parent cell) ≤
      cover.toPaperTubeCover.fiberShadedMass
        fineShading parent := by
  rw [show (∑ cell ∈ cells,
      sourceWitnessFineFiberCellMass cover fineShading parent cell) =
      ∑ source ∈ cover.toPaperTubeCover.fiberIndices parent,
        ∑ cell ∈ cells,
          volume (fineShading.carrier source ∩
            wz1PaperGridCube rho cell) by
    simp only [sourceWitnessFineFiberCellMass]
    rw [Finset.sum_comm]]
  apply Finset.sum_le_sum
  intro source hsource
  have hdisjoint :
      Set.PairwiseDisjoint (↑cells)
        (fun cell =>
          fineShading.carrier source ∩
            wz1PaperGridCube rho cell) := by
    intro first _ second _ hne
    exact (wz1PaperGridCube_disjoint hne).mono
      Set.inter_subset_right Set.inter_subset_right
  have hmeasurable : ∀ cell ∈ cells, MeasurableSet
      (fineShading.carrier source ∩
        wz1PaperGridCube rho cell) := by
    intro cell _
    exact (fineShading.measurable_carrier source).inter
      (wz1PaperGridCube_measurable cell)
  have hunionSubset :
      (⋃ cell ∈ cells,
        fineShading.carrier source ∩
          wz1PaperGridCube rho cell) ⊆
        fineShading.carrier source := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, _hcell, hpoint⟩
    exact hpoint.1
  calc
    (∑ cell ∈ cells,
        volume (fineShading.carrier source ∩
          wz1PaperGridCube rho cell)) =
        volume (⋃ cell ∈ cells,
          fineShading.carrier source ∩
            wz1PaperGridCube rho cell) := by
      symm
      exact MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable
    _ ≤ volume (fineShading.carrier source) :=
      measure_mono hunionSubset

/-- Parentwise sampled-coarse versus complete-fine mass comparison.  This is
the division-free form used by later external-weight regularization. -/
theorem source_witness_parent_carrier_mul_fineCube_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (sourceWitness : PureWZ2SourceWitnessCoarseShadingData balanced)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hfineCubical : WZ1PaperIsCubicalShading fineShading)
    (hfineInside : ∀ source point, point ∈ fineShading.carrier source →
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        wz1PaperGridCube rho (wz1PaperGridIndex rho point))
    (parent : Fin coarse.card) :
    volume (sourceWitness.shading.carrier parent) *
          volume (wz1PaperGridCube delta (0, 0, 0)) ≤
      volume (wz1PaperGridCube rho (0, 0, 0)) *
        cover.toPaperTubeCover.fiberShadedMass fineShading parent := by
  have hcellLower :
      (sourceWitness.parentCells parent).card *
          volume (wz1PaperGridCube delta (0, 0, 0)) ≤
        ∑ cell ∈ sourceWitness.parentCells parent,
          sourceWitnessFineFiberCellMass
            cover fineShading parent cell := by
    calc
      (sourceWitness.parentCells parent).card *
          volume (wz1PaperGridCube delta (0, 0, 0)) =
          ∑ _cell ∈ sourceWitness.parentCells parent,
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
        simp [Finset.sum_const]
      _ ≤ ∑ cell ∈ sourceWitness.parentCells parent,
          sourceWitnessFineFiberCellMass
            cover fineShading parent cell := by
        apply Finset.sum_le_sum
        intro cell hcell
        exact source_witness_fine_fiber_cell_mass_lower
          sourceWitness hdelta hfineCubical hfineInside parent cell hcell
  have hcountLower :
      (sourceWitness.parentCells parent).card *
          volume (wz1PaperGridCube delta (0, 0, 0)) ≤
        cover.toPaperTubeCover.fiberShadedMass fineShading parent :=
    hcellLower.trans <|
      sum_source_witness_fine_fiber_cell_mass_le
        cover fineShading parent (sourceWitness.parentCells parent)
  have hcoarseVolume :
      volume (sourceWitness.shading.carrier parent) =
        (sourceWitness.parentCells parent).card *
          volume (wz1PaperGridCube rho (0, 0, 0)) := by
    rw [sourceWitness.shading_carrier_eq parent]
    exact wz1PaperGridCube_volume_biUnion
      hrho (sourceWitness.parentCells parent)
  rw [hcoarseVolume]
  calc
    ((sourceWitness.parentCells parent).card *
        volume (wz1PaperGridCube rho (0, 0, 0))) *
          volume (wz1PaperGridCube delta (0, 0, 0)) =
        volume (wz1PaperGridCube rho (0, 0, 0)) *
          ((sourceWitness.parentCells parent).card *
            volume (wz1PaperGridCube delta (0, 0, 0))) := by ring
    _ ≤ volume (wz1PaperGridCube rho (0, 0, 0)) *
        cover.toPaperTubeCover.fiberShadedMass fineShading parent := by
      gcongr

/-- Specialization of the parentwise bridge to an exactly rebalanced fine
shading. -/
theorem rebalanced_source_witness_parent_carrier_mul_fineCube_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading candidate : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    {hdelta : 0 < delta}
    (rebalanced :
      PureWZ2RebalancedFiniteRefinementData original candidate hdelta)
    (sourceWitness :
      PureWZ2SourceWitnessCoarseShadingData rebalanced.balanced)
    (hrho : 0 < rho) (parent : Fin coarse.card) :
    volume (sourceWitness.shading.carrier parent) *
          volume (wz1PaperGridCube delta (0, 0, 0)) ≤
      volume (wz1PaperGridCube rho (0, 0, 0)) *
        cover.toPaperTubeCover.fiberShadedMass
          rebalanced.balancing.refined parent := by
  exact source_witness_parent_carrier_mul_fineCube_le
    sourceWitness hdelta hrho rebalanced.balancing.refined_cubical
      (fun source point hpoint =>
        rebalanced.fine_cube_subset_coarse_cube source point hpoint)
    parent

end Kakeya.Assouad.PureWZ2

end
