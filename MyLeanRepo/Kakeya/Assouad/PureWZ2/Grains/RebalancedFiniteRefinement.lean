import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WholeCellBalancedRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalRefinement
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperInitialBalancing
import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruning
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancing
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperExactBalancingMassRetention

/-!
# Rebalancing a finite plane-map refinement

A finite plane-map construction may delete individual tube memberships, so
its output is not automatically a balanced-cover restriction.  This module
repairs that mismatch without a hereditary-sticky assumption.

First put the cubical refinement in one point-multiplicity band.  Delete the
fixed-origin fine cells crossing the chosen coarse grid, and apply the closed
exact whole-cell balancing theorem.  Finally restrict the *existing* coarse
shading to the retained whole coarse cells.  The original balanced cover then
supplies parent compatibility, while the new exact balancing supplies the
common positive fine-cell mass.

The only quantitative premise is the displayed boundary-mass absorption.  It
is deliberately left outside this structural producer.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Restrict every carrier of a coarse shading by a finite union of whole
coarse cells. -/
def coarseWholeCellRestriction
    {rho : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (source : WZ1PaperTubeShading coarse)
    (cells : Finset (ℤ × ℤ × ℤ)) :
    WZ1PaperTubeShading coarse where
  carrier parent := source.carrier parent ∩
    ⋃ cell ∈ cells, wz1PaperGridCube rho cell
  measurable_carrier parent :=
    (source.measurable_carrier parent).inter <| by
      apply MeasurableSet.biUnion (Finset.countable_toSet cells)
      intro cell _
      exact wz1PaperGridCube_measurable cell
  subset_body parent :=
    Set.inter_subset_left.trans (source.subset_body parent)

lemma coarseWholeCellRestriction_subshading
    {rho : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (source : WZ1PaperTubeShading coarse)
    (cells : Finset (ℤ × ℤ × ℤ)) :
    PaperIsSubshading (coarseWholeCellRestriction source cells) source :=
  fun _ => Set.inter_subset_left

lemma coarseWholeCellRestriction_cubical
    {rho : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {source : WZ1PaperTubeShading coarse}
    (hcubical : WZ1PaperIsCubicalShading source)
    (cells : Finset (ℤ × ℤ × ℤ)) :
    WZ1PaperIsCubicalShading
      (coarseWholeCellRestriction source cells) := by
  intro parent point hpoint other hother
  refine ⟨hcubical parent point hpoint.1 hother, ?_⟩
  rcases Set.mem_iUnion₂.mp hpoint.2 with ⟨cell, hcell, hpointCell⟩
  have hindex : wz1PaperGridIndex rho point = cell :=
    (mem_wz1PaperGridCube rho cell point).mp hpointCell
  exact Set.mem_iUnion₂.mpr
    ⟨cell, hcell, by rwa [← hindex]⟩

/-- Structural output after rebalancing an arbitrary cubical fine
subshading.  `exactRetention` records the second logarithmic loss instead of
hiding it in the statement. -/
structure PureWZ2RebalancedFiniteRefinementData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (original :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (candidate : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta) where
  bandData : WZ2PaperGlobalMultiplicityBandData candidate
  multiplicityCap : ENNReal :=
    (2 ^ (bandData.level + 1) : ENNReal)
  pruning : WZ2PaperBoundaryCellPruningData
    (rho := rho) bandData.band hdelta multiplicityCap
  balancing : WZ2PaperExactCellBalancingData
    (rho := rho) pruning.pruned pruning.coarseCells
      pruning.availableFineCells
  refined_subshading :
    PaperIsSubshading balancing.refined candidate
  coarse : WZ1PaperTubeShading coarse :=
    coarseWholeCellRestriction coarseShading
      balancing.retainedCoarseCells
  coarse_subshading : PaperIsSubshading coarse coarseShading
  balanced : PureWZ2BalancedCoverData cover balancing.refined coarse
  band_mass_le_two_pruned :
    bandData.band.mass ≤ 2 * pruning.pruned.mass
  exactRetention : WZ2PaperExactBalancingMassRetentionData
    bandData.band hdelta multiplicityCap pruning balancing bandData.level

/-- A literal `delta`-grid cube lies in one literal `rho`-grid cube whenever
`rho` is a positive integral multiple of `delta`. -/
lemma aligned_fine_grid_cube_subset_coarse_grid_cube
    {delta rho : ℝ} (hdelta : 0 < delta)
    (K : ℕ) (hK : 0 < K)
    (hrho : rho = (K : ℝ) * delta)
    (fineCell : WZ2PaperCellIndex) :
    wz1PaperGridCube delta fineCell ⊆
      wz1PaperGridCube rho
        (wz1PaperGridIndex rho (cellCorner delta fineCell)) := by
  intro point hpoint
  have hcorner :
      cellCorner delta fineCell ∈ wz1PaperGridCube delta fineCell :=
    cellCorner_mem_gridCube hdelta fineCell
  have hfineIndex :
      wz1PaperGridIndex delta point =
        wz1PaperGridIndex delta (cellCorner delta fineCell) := by
    exact ((mem_wz1PaperGridCube delta fineCell point).mp hpoint).trans
      ((mem_wz1PaperGridCube delta fineCell
        (cellCorner delta fineCell)).mp hcorner).symm
  exact (mem_wz1PaperGridCube rho _ point).mpr
    (wz1PaperGridIndex_fine_to_coarse K hK hrho hfineIndex)

/-- Finish exact rebalancing once a multiplicity band, a boundary-pruning
package, and an exact cell balancing have already been prepared.  Separating
this common tail lets the non-aligned route use a boundary estimate while the
integer-aligned route proves that the crossing region is empty. -/
theorem rebalanced_finite_refinement_of_prepared
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading candidate : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (original :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hcandidateSub : PaperIsSubshading candidate fineShading)
    (hdelta : 0 < delta)
    (bandData : WZ2PaperGlobalMultiplicityBandData candidate)
    (pruning : WZ2PaperBoundaryCellPruningData
      (rho := rho) bandData.band hdelta
        (2 ^ (bandData.level + 1) : ENNReal))
    (balancing : WZ2PaperExactCellBalancingData
      (rho := rho) pruning.pruned pruning.coarseCells
        pruning.availableFineCells)
    (hbandHalf : bandData.band.mass ≤ 2 * pruning.pruned.mass) :
    Nonempty
      (PureWZ2RebalancedFiniteRefinementData
        original candidate hdelta) := by
  let retainedUnion : Set Point3 :=
    ⋃ cell ∈ balancing.retainedCoarseCells,
      wz1PaperGridCube rho cell
  let restrictedCoarse : WZ1PaperTubeShading coarse :=
    coarseWholeCellRestriction coarseShading
      balancing.retainedCoarseCells

  have hrefinedBand : PaperIsSubshading balancing.refined bandData.band :=
    fun index =>
      (balancing.refined_subshading index).trans
        (pruning.pruned_subshading index)
  have hbandCandidate : PaperIsSubshading bandData.band candidate := by
    intro index point hpoint
    rw [bandData.band_eq] at hpoint
    exact hpoint.1
  have hrefinedCandidate :
      PaperIsSubshading balancing.refined candidate := fun index =>
    (hrefinedBand index).trans (hbandCandidate index)
  have hrefinedOriginal :
      PaperIsSubshading balancing.refined fineShading := fun index =>
    (hrefinedCandidate index).trans (hcandidateSub index)

  have hretainedSubsetOriginal : retainedUnion ⊆ coarseShading.union := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨cell, hcell, hpointCell⟩
    have hmass := balancing.fine_cell_mass cell hcell
    have hpositive :
        0 < volume
          (balancing.refined.union ∩ wz1PaperGridCube rho cell) := by
      rw [hmass]
      exact balancing.cellMass_pos
    have hnonempty :
        (balancing.refined.union ∩
          wz1PaperGridCube rho cell).Nonempty := by
      by_contra hempty
      have heq : balancing.refined.union ∩
          wz1PaperGridCube rho cell = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hempty
      rw [heq, measure_empty] at hpositive
      exact (lt_irrefl 0) hpositive
    rcases hnonempty with ⟨witness, hwitnessFine, hwitnessCell⟩
    rcases hwitnessFine with ⟨source, hsource⟩
    let parent := cover.toPaperTubeCover.parent source
    have hwitnessCoarse : witness ∈ coarseShading.carrier parent :=
      original.point_compatibility source parent
        (cover.toPaperTubeCover.parent_covers source) witness
        (hrefinedOriginal source hsource)
    have hwhole := original.coarse_cubical parent witness
      hwitnessCoarse
    have hindex : wz1PaperGridIndex rho witness = cell :=
      (mem_wz1PaperGridCube rho cell witness).mp hwitnessCell
    exact ⟨parent, hwhole (by rwa [hindex])⟩

  have hcoarseUnion : restrictedCoarse.union = retainedUnion := by
    apply Set.Subset.antisymm
    · rintro point ⟨parent, hpoint⟩
      exact hpoint.2
    · intro point hpoint
      rcases hretainedSubsetOriginal hpoint with ⟨parent, hparent⟩
      exact ⟨parent, hparent, hpoint⟩

  have hpointCompatibility : ∀ source parent,
      WZ1PaperTubeCovers (fine.tube source) (coarse.tube parent) →
      ∀ point, point ∈ balancing.refined.carrier source →
        point ∈ restrictedCoarse.carrier parent := by
    intro source parent hcover point hpoint
    have horiginal : point ∈ coarseShading.carrier parent :=
      original.point_compatibility source parent hcover point
        (hrefinedOriginal source hpoint)
    have hpointUnion : point ∈ balancing.refined.union :=
      ⟨source, hpoint⟩
    rw [balancing.refined_union_eq] at hpointUnion
    rcases Set.mem_iUnion₂.mp hpointUnion with
      ⟨fineCell, hfineCell, hpointFineCell⟩
    rw [balancing.retainedFineCells_eq] at hfineCell
    rcases Finset.mem_biUnion.mp hfineCell with
      ⟨coarseCell, hcoarseCell, hselected⟩
    have hpointCoarseCell :
        point ∈ wz1PaperGridCube rho coarseCell :=
      balancing.fine_cell_containment coarseCell hcoarseCell
        fineCell hselected hpointFineCell
    exact ⟨horiginal, Set.mem_iUnion₂.mpr
      ⟨coarseCell, hcoarseCell, hpointCoarseCell⟩⟩

  let newBalanced : PureWZ2BalancedCoverData cover
      balancing.refined restrictedCoarse :=
    { point_compatibility := hpointCompatibility
      coarse_cubical :=
        coarseWholeCellRestriction_cubical
          original.coarse_cubical balancing.retainedCoarseCells
      activeCells := balancing.retainedCoarseCells
      coarse_union_eq := by
        simpa [retainedUnion, restrictedCoarse] using hcoarseUnion
      cellMass := balancing.cellMass
      cellMass_pos := balancing.cellMass_pos
      cellMass_ne_top := balancing.cellMass_ne_top
      fine_cell_mass := balancing.fine_cell_mass }

  rcases wz2_paper_exact_balancing_mass_retention
      hdelta bandData.band bandData.level
      bandData.band_multiplicity
      (2 ^ (bandData.level + 1) : ENNReal) pruning balancing with
    ⟨exactRetention⟩
  exact ⟨{
    bandData := bandData
    multiplicityCap := (2 ^ (bandData.level + 1) : ENNReal)
    pruning := pruning
    balancing := balancing
    refined_subshading := hrefinedCandidate
    coarse := restrictedCoarse
    coarse_subshading :=
      coarseWholeCellRestriction_subshading _ _
    balanced := newBalanced
    band_mass_le_two_pruned := hbandHalf
    exactRetention := exactRetention
  }⟩

/-- Rebuild a genuine balanced cover after a tube-dependent finite
refinement.  No sticky property is inherited by fiat: only the old parent
compatibility and the newly balanced whole cells are used. -/
theorem rebalanced_finite_refinement
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading candidate : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (original :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hcandidateSub : PaperIsSubshading candidate fineShading)
    (hcandidateCubical : WZ1PaperIsCubicalShading candidate)
    (hdelta : 0 < delta)
    (hdeltaRho : delta ≤ rho)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hboundary : ∀ bandData :
      WZ2PaperGlobalMultiplicityBandData candidate,
      let cap : ENNReal :=
        (2 ^ (bandData.level + 1) : ENNReal)
      2 * (cap * ENNReal.ofReal (1000 * delta / rho)) <
        bandData.band.mass) :
    Nonempty
      (PureWZ2RebalancedFiniteRefinementData
        original candidate hdelta) := by
  rcases wz2_paper_global_multiplicity_band candidate
      hcandidateCubical with ⟨bandData⟩
  let cap : ENNReal :=
    (2 ^ (bandData.level + 1) : ENNReal)
  have hcap : ∀ point,
      (bandData.band.pointMultiplicity point : ENNReal) ≤ cap := by
    intro point
    by_cases hpoint : point ∈ bandData.band.union
    · exact (bandData.band_multiplicity point hpoint).2.le
    · have hzero : bandData.band.pointMultiplicity point = 0 := by
        simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
        apply Finset.card_eq_zero.mpr
        rw [Finset.filter_eq_empty_iff]
        intro index _ hindex
        exact hpoint ⟨index, hindex⟩
      rw [hzero]
      norm_num
  have hboundaryOne :
      cap * ENNReal.ofReal (1000 * delta / rho) <
        bandData.band.mass := by
    exact (le_mul_of_one_le_left' (by norm_num)).trans_lt
      (hboundary bandData)
  rcases wz2_prop_sticky_boundary_cell_pruning
      hdelta hdeltaRho hrho hrhoOne bandData.band
      bandData.band_cubical cap hcap hboundaryOne with
    ⟨pruning⟩
  rcases wz2_prop_sticky_exact_cell_balancing
      hdelta hrho pruning.pruned pruning.pruned_cubical
      pruning.coarseCells pruning.coarseCells_nonempty
      pruning.availableFineCells pruning.availableFineCells_nonempty
      pruning.availableFineCells_ready with
    ⟨balancing⟩

  let retainedUnion : Set Point3 :=
    ⋃ cell ∈ balancing.retainedCoarseCells,
      wz1PaperGridCube rho cell
  let restrictedCoarse : WZ1PaperTubeShading coarse :=
    coarseWholeCellRestriction coarseShading
      balancing.retainedCoarseCells

  have hrefinedBand : PaperIsSubshading balancing.refined bandData.band :=
    fun index =>
      (balancing.refined_subshading index).trans
        (pruning.pruned_subshading index)
  have hbandCandidate : PaperIsSubshading bandData.band candidate := by
    intro index point hpoint
    rw [bandData.band_eq] at hpoint
    exact hpoint.1
  have hrefinedCandidate :
      PaperIsSubshading balancing.refined candidate := fun index =>
    (hrefinedBand index).trans (hbandCandidate index)
  have hrefinedOriginal :
      PaperIsSubshading balancing.refined fineShading := fun index =>
    (hrefinedCandidate index).trans (hcandidateSub index)

  have hretainedSubsetOriginal : retainedUnion ⊆ coarseShading.union := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨cell, hcell, hpointCell⟩
    have hmass := balancing.fine_cell_mass cell hcell
    have hpositive :
        0 < volume
          (balancing.refined.union ∩ wz1PaperGridCube rho cell) := by
      rw [hmass]
      exact balancing.cellMass_pos
    have hnonempty :
        (balancing.refined.union ∩
          wz1PaperGridCube rho cell).Nonempty := by
      by_contra hempty
      have heq : balancing.refined.union ∩
          wz1PaperGridCube rho cell = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hempty
      rw [heq, measure_empty] at hpositive
      exact (lt_irrefl 0) hpositive
    rcases hnonempty with ⟨witness, hwitnessFine, hwitnessCell⟩
    rcases hwitnessFine with ⟨source, hsource⟩
    let parent := cover.toPaperTubeCover.parent source
    have hwitnessCoarse : witness ∈ coarseShading.carrier parent :=
      original.point_compatibility source parent
        (cover.toPaperTubeCover.parent_covers source) witness
        (hrefinedOriginal source hsource)
    have hwhole := original.coarse_cubical parent witness
      hwitnessCoarse
    have hindex : wz1PaperGridIndex rho witness = cell :=
      (mem_wz1PaperGridCube rho cell witness).mp hwitnessCell
    exact ⟨parent, hwhole (by rwa [hindex])⟩

  have hcoarseUnion : restrictedCoarse.union = retainedUnion := by
    apply Set.Subset.antisymm
    · rintro point ⟨parent, hpoint⟩
      exact hpoint.2
    · intro point hpoint
      rcases hretainedSubsetOriginal hpoint with ⟨parent, hparent⟩
      exact ⟨parent, hparent, hpoint⟩

  have hpointCompatibility : ∀ source parent,
      WZ1PaperTubeCovers (fine.tube source) (coarse.tube parent) →
      ∀ point, point ∈ balancing.refined.carrier source →
        point ∈ restrictedCoarse.carrier parent := by
    intro source parent hcover point hpoint
    have horiginal : point ∈ coarseShading.carrier parent :=
      original.point_compatibility source parent hcover point
        (hrefinedOriginal source hpoint)
    have hpointUnion : point ∈ balancing.refined.union :=
      ⟨source, hpoint⟩
    rw [balancing.refined_union_eq] at hpointUnion
    rcases Set.mem_iUnion₂.mp hpointUnion with
      ⟨fineCell, hfineCell, hpointFineCell⟩
    rw [balancing.retainedFineCells_eq] at hfineCell
    rcases Finset.mem_biUnion.mp hfineCell with
      ⟨coarseCell, hcoarseCell, hselected⟩
    have hpointCoarseCell :
        point ∈ wz1PaperGridCube rho coarseCell :=
      balancing.fine_cell_containment coarseCell hcoarseCell
        fineCell hselected hpointFineCell
    exact ⟨horiginal, Set.mem_iUnion₂.mpr
      ⟨coarseCell, hcoarseCell, hpointCoarseCell⟩⟩

  let newBalanced : PureWZ2BalancedCoverData cover
      balancing.refined restrictedCoarse :=
    { point_compatibility := hpointCompatibility
      coarse_cubical :=
        coarseWholeCellRestriction_cubical
          original.coarse_cubical balancing.retainedCoarseCells
      activeCells := balancing.retainedCoarseCells
      coarse_union_eq := by
        simpa [retainedUnion, restrictedCoarse] using hcoarseUnion
      cellMass := balancing.cellMass
      cellMass_pos := balancing.cellMass_pos
      cellMass_ne_top := balancing.cellMass_ne_top
      fine_cell_mass := balancing.fine_cell_mass }

  have hhalf : bandData.band.mass ≤ 2 * pruning.pruned.mass := by
    let crossing : ENNReal :=
      cap * ENNReal.ofReal (1000 * delta / rho)
    have hcrossing : 2 * crossing < bandData.band.mass := by
      simpa [crossing, cap] using hboundary bandData
    have hcrossingTop : crossing ≠ ⊤ := by
      apply ne_top_of_lt
      calc
        crossing ≤ 2 * crossing := by
          exact le_mul_of_one_le_left' (by norm_num)
        _ < bandData.band.mass := hcrossing
    calc
      bandData.band.mass ≤ pruning.pruned.mass + crossing := by
        simpa [crossing, cap] using pruning.source_mass_le_explicit
      _ ≤ pruning.pruned.mass + pruning.pruned.mass := by
        gcongr
        by_contra hnot
        have hprunedCrossing : pruning.pruned.mass < crossing :=
          lt_of_not_ge hnot
        have hsource : bandData.band.mass < 2 * crossing := by
          calc
            bandData.band.mass ≤
                pruning.pruned.mass + crossing := by
              simpa [crossing, cap] using
                pruning.source_mass_le_explicit
            _ < crossing + crossing := by
              exact ENNReal.add_lt_add_right hcrossingTop
                hprunedCrossing
            _ = 2 * crossing := by ring
        exact (not_lt_of_ge hcrossing.le) hsource
      _ = 2 * pruning.pruned.mass := by ring

  rcases wz2_paper_exact_balancing_mass_retention
      hdelta bandData.band bandData.level
      bandData.band_multiplicity cap pruning balancing with
    ⟨exactRetention⟩
  exact ⟨{
    bandData := bandData
    multiplicityCap := cap
    pruning := pruning
    balancing := balancing
    refined_subshading := hrefinedCandidate
    coarse := restrictedCoarse
    coarse_subshading :=
      coarseWholeCellRestriction_subshading _ _
    balanced := newBalanced
    band_mass_le_two_pruned := hhalf
    exactRetention := exactRetention
  }⟩

/-- Rebuild a genuine balanced cover at an integer-aligned coarse scale.
Every active fine cell is already contained in its literal coarse cell, so
the boundary-crossing region is empty and no boundary-mass absorption is
needed. -/
theorem aligned_rebalanced_finite_refinement
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading candidate : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (original :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hcandidateSub : PaperIsSubshading candidate fineShading)
    (hcandidateCubical : WZ1PaperIsCubicalShading candidate)
    (hcandidateMass : 0 < candidate.mass)
    (hdelta : 0 < delta)
    (hdeltaRho : delta ≤ rho)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (K : ℕ) (hK : 0 < K)
    (hrhoAligned : rho = (K : ℝ) * delta) :
    Nonempty
      (PureWZ2RebalancedFiniteRefinementData
        original candidate hdelta) := by
  rcases wz2_paper_global_multiplicity_band candidate
      hcandidateCubical with ⟨bandData⟩
  let cap : ENNReal :=
    (2 ^ (bandData.level + 1) : ENNReal)
  have hcap : ∀ point,
      (bandData.band.pointMultiplicity point : ENNReal) ≤ cap := by
    intro point
    by_cases hpoint : point ∈ bandData.band.union
    · exact (bandData.band_multiplicity point hpoint).2.le
    · have hzero : bandData.band.pointMultiplicity point = 0 := by
        simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
        apply Finset.card_eq_zero.mpr
        rw [Finset.filter_eq_empty_iff]
        intro index _ hindex
        exact hpoint ⟨index, hindex⟩
      rw [hzero]
      norm_num
  have hbandMassPos : 0 < bandData.band.mass := by
    let bandLoss : ENNReal :=
      ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal)
    have hbandLossTop : bandLoss ≠ ⊤ := by simp [bandLoss]
    have hquotient : 0 < candidate.mass / bandLoss :=
      ENNReal.div_pos hcandidateMass.ne' hbandLossTop
    exact hquotient.trans_le (by
      simpa [bandLoss] using bandData.band_mass_retention)
  have hsafe :
      wz2PaperBoundarySafeFineCells
          (rho := rho) bandData.band hdelta =
        wz1PaperActiveCells bandData.band hdelta := by
    apply Finset.filter_eq_self.2
    intro fineCell _
    exact aligned_fine_grid_cube_subset_coarse_grid_cube
      hdelta K hK hrhoAligned fineCell
  have hcrossingCells :
      wz2PaperBoundaryCrossingFineCells
          (rho := rho) bandData.band hdelta = ∅ := by
    simp only [wz2PaperBoundaryCrossingFineCells]
    rw [hsafe]
    exact Finset.sdiff_self _
  have hcrossingRegion :
      wz2PaperBoundaryCrossingRegion
          (rho := rho) bandData.band hdelta = ∅ := by
    simp [wz2PaperBoundaryCrossingRegion, hcrossingCells]
  have hcrossingMass :
      (∑ index : Fin fine.card,
        volume
          (bandData.band.carrier index ∩
            wz2PaperBoundaryCrossingRegion
              (rho := rho) bandData.band hdelta)) <
        bandData.band.mass := by
    rw [hcrossingRegion]
    simpa using hbandMassPos
  rcases wz2_paper_boundary_cell_pruning_of_crossing_mass
      hdelta hdeltaRho hrho hrhoOne bandData.band
      bandData.band_cubical cap hcap hcrossingMass with
    ⟨pruning⟩
  rcases wz2_prop_sticky_exact_cell_balancing
      hdelta hrho pruning.pruned pruning.pruned_cubical
      pruning.coarseCells pruning.coarseCells_nonempty
      pruning.availableFineCells pruning.availableFineCells_nonempty
      pruning.availableFineCells_ready with
    ⟨balancing⟩
  have hbandPruned : bandData.band.mass = pruning.pruned.mass := by
    have hmass := pruning.source_mass_eq_crossing
    have hpruningCrossing : pruning.crossingRegion =
        wz2PaperBoundaryCrossingRegion
          (rho := rho) bandData.band hdelta := by
      rw [pruning.crossingRegion_eq_source]
      rfl
    rw [hpruningCrossing, hcrossingRegion] at hmass
    simpa using hmass
  have hbandHalf : bandData.band.mass ≤ 2 * pruning.pruned.mass := by
    rw [hbandPruned]
    exact le_mul_of_one_le_left' (by norm_num)
  exact rebalanced_finite_refinement_of_prepared original
    hcandidateSub hdelta bandData pruning balancing hbandHalf

end Kakeya.Assouad.PureWZ2

end
