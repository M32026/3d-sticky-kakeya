import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedParentDeletionRepairedStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperQuantitativeParentDeletion
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantOwnerExactificationHelpers

/-! # Repaired whole-cell deletion of low-mass parent fibers -/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem wz2_paper_balanced_parent_deletion_repaired :
    WZ2PaperBalancedParentDeletionRepairedStatement := by
  intro delta rho hdelta hrho fine coarse cover sourceShading
    coarseCells availableFineCells balancing coarseData active
    degreeCap hDegree hCellMass referenceFiberMass threshold hSmall
  let ambientCells := balancing.retainedCoarseCells
  let cellEquiv :
      Fin ambientCells.card ≃ ambientCells :=
    (finCongr (Fintype.card_coe ambientCells).symm).trans
      (Fintype.equivFin ambientCells).symm
  let cellIndex : Fin ambientCells.card → WZ2PaperCellIndex :=
    fun index => (cellEquiv index).1
  have cellIndex_injective : Function.Injective cellIndex := by
    intro first second heq
    apply cellEquiv.injective
    exact Subtype.ext heq
  let activeParents :
      Fin ambientCells.card → Finset (Fin coarse.card) :=
    fun index => active.activeParents (cellIndex index)
  let cellMass : Fin ambientCells.card → ENNReal :=
    fun _ => balancing.cellMass
  have indexedDegree :
      ∀ index ∈ (Finset.univ : Finset (Fin ambientCells.card)),
        (activeParents index).card ≤ 2 * degreeCap := by
    intro index _
    apply hDegree (cellIndex index)
    exact (cellEquiv index).2
  have indexedCellMass :
      ∀ index ∈ (Finset.univ : Finset (Fin ambientCells.card)),
        cellMass index ≤
          2 * (degreeCap : ENNReal) * active.fiberCellMass := by
    intro index _
    exact hCellMass
  have cellMassSum :
      (∑ index : Fin ambientCells.card, cellMass index) =
        balancing.cellMass * ambientCells.card := by
    simp [cellMass, mul_comm]
  have indexedSmall :
      2 * (degreeCap : ENNReal) * threshold *
            ∑ parent : Fin coarse.card, referenceFiberMass parent <
        ∑ index : Fin ambientCells.card, cellMass index := by
    rw [cellMassSum]
    simpa [ambientCells] using hSmall
  rcases
      iterative_deletion_quantitative_nonempty
        (Finset.univ : Finset (Fin ambientCells.card))
        activeParents referenceFiberMass active.fiberCellMass
        cellMass degreeCap threshold
        indexedDegree indexedCellMass indexedSmall
    with
      ⟨goodCellIndices, _goodIndicesSubset,
        goodCellIndicesNonempty, goodCondition, deletedMass⟩
  let goodCells : Finset WZ2PaperCellIndex :=
    goodCellIndices.image cellIndex
  have goodCellsNonempty : goodCells.Nonempty := by
    rcases goodCellIndicesNonempty with ⟨index, hindex⟩
    exact
      ⟨cellIndex index,
        Finset.mem_image.mpr ⟨index, hindex, rfl⟩⟩
  have goodCellsSubset :
      goodCells ⊆ balancing.retainedCoarseCells := by
    intro cell hcell
    rcases Finset.mem_image.mp hcell with ⟨index, _, rfl⟩
    exact (cellEquiv index).2
  let retainedParents : Finset (Fin coarse.card) :=
    goodCells.biUnion active.activeParents
  have retainedParentsNonempty : retainedParents.Nonempty := by
    rcases goodCellsNonempty with ⟨cell, hcell⟩
    rcases active.activeParents_nonempty cell (goodCellsSubset hcell) with
      ⟨parent, hparent⟩
    exact
      ⟨parent,
        Finset.mem_biUnion.mpr ⟨cell, hcell, hparent⟩⟩
  let retainedFineCells : Finset WZ2PaperCellIndex :=
    goodCells.biUnion balancing.selectedFineCells
  let refined : WZ1PaperTubeShading fine :=
    wz2RefinedShading balancing.refined retainedFineCells
  have retainedFineActive' :
      ∀ fineCell ∈ retainedFineCells,
        fineCell ∈ wz1PaperActiveCells balancing.refined hdelta := by
    intro fineCell hfine
    rcases Finset.mem_biUnion.mp hfine with
      ⟨cell, hcell, hfineCell⟩
    have hcellAmbient :
        cell ∈ balancing.retainedCoarseCells :=
      goodCellsSubset hcell
    have hselected :
        fineCell ∈ balancing.selectedFineCells cell :=
      hfineCell
    have hcubeNonempty :
        (wz1PaperGridCube delta fineCell).Nonempty :=
      MeasureTheory.nonempty_of_measure_ne_zero
        (wz1PaperGridCube_volume_pos hdelta fineCell).ne'
    rcases hcubeNonempty with ⟨point, hpoint⟩
    have hbalancedUnion :
        point ∈ balancing.refined.union := by
      rw [balancing.refined_union_eq]
      apply Set.mem_iUnion₂.mpr
      have hfineRetained :
          fineCell ∈ balancing.retainedFineCells := by
        rw [balancing.retainedFineCells_eq]
        exact
          Finset.mem_biUnion.mpr
            ⟨cell, hcellAmbient, hselected⟩
      exact ⟨fineCell, hfineRetained, hpoint⟩
    rw [mem_wz1PaperActiveCells balancing.refined hdelta fineCell]
    refine ⟨?_, ⟨point, hbalancedUnion, hpoint⟩⟩
    rcases hbalancedUnion with ⟨source, hsource⟩
    have hbody :=
      balancing.refined.subset_body source hsource
    have hindex :
        wz1PaperGridIndex delta point = fineCell :=
      (mem_wz1PaperGridCube delta fineCell point).mp hpoint
    rw [← hindex]
    exact
      paper_point_gridIndex_in_window
        hdelta hbody.2
  have refinedCubical :
      WZ1PaperIsCubicalShading refined :=
    wz2RefinedShading_cubical balancing.refined_cubical
  have refinedUnion :
      refined.union =
        ⋃ fineCell ∈ retainedFineCells,
          wz1PaperGridCube delta fineCell := by
    exact
      wz2RefinedShading_union_eq
        balancing.refined_cubical hdelta retainedFineActive'
  have retainedCellMass :
      ∀ cell ∈ goodCells,
        volume
            (refined.union ∩ wz1PaperGridCube rho cell) =
          balancing.cellMass := by
    intro cell hcell
    have hintersection :
        (wz2RetainedCellsUnion delta retainedFineCells) ∩
              wz1PaperGridCube rho cell =
            ⋃ fineCell ∈ balancing.selectedFineCells cell,
              wz1PaperGridCube delta fineCell := by
      exact
        wz2RefinedUnion_inter_coarseCube
          (by rfl)
          (fun coarseCell hcoarse fineCell hfine =>
            balancing.fine_cell_containment
              coarseCell (goodCellsSubset hcoarse)
              fineCell hfine)
          hcell
    have hrefined :
        refined.union =
          wz2RetainedCellsUnion delta retainedFineCells := by
      exact
        wz2RefinedShading_union_eq
          balancing.refined_cubical hdelta retainedFineActive'
    rw [hrefined, hintersection]
    rw [wz1PaperGridCube_volume_biUnion
      hdelta (balancing.selectedFineCells cell)]
    rw [balancing.selectedFineCells_card
      cell (goodCellsSubset hcell)]
    exact balancing.cellMass_eq.symm
  have parentFiberMassFloor :
      ∀ parent ∈ retainedParents,
        threshold * referenceFiberMass parent ≤
          (restrictPaperShading
            (cover.fullFiberSubfamily parent)
            refined).mass := by
    intro parent hparent
    rcases Finset.mem_biUnion.mp hparent with
      ⟨cell, hcell, hparentActive⟩
    rcases Finset.mem_image.mp hcell with
      ⟨index, hindex, hcellEq⟩
    have indexedParent :
        parent ∈ activeParents index := by
      simpa [activeParents, cellIndex, hcellEq] using hparentActive
    have hgood :=
      goodCondition index hindex parent indexedParent
    have hsumLe :
        (∑ other ∈ goodCellIndices,
            if parent ∈ activeParents other then
              active.fiberCellMass
            else 0) ≤
          (restrictPaperShading
            (cover.fullFiberSubfamily parent)
            refined).mass := by
      have hcellwise :
          ∀ other ∈ goodCellIndices,
            (if parent ∈ activeParents other then
                active.fiberCellMass
              else 0) ≤
              volume
                ((restrictPaperShading
                    (cover.fullFiberSubfamily parent)
                    refined).union ∩
                  wz1PaperGridCube rho (cellIndex other)) := by
        intro other hother
        by_cases hactive : parent ∈ activeParents other
        · rw [if_pos hactive]
          have hsourceLower :=
            active.fiber_cell_mass_lower
              (cellIndex other) (cellEquiv other).2
              parent hactive
          have hmono :
              volume
                  ((restrictPaperShading
                      (cover.fullFiberSubfamily parent)
                      balancing.refined).union ∩
                    wz1PaperGridCube rho (cellIndex other)) ≤
                volume
                  ((restrictPaperShading
                      (cover.fullFiberSubfamily parent)
                      refined).union ∩
                    wz1PaperGridCube rho (cellIndex other)) := by
            apply measure_mono
            intro point hpoint
            rcases hpoint.1 with ⟨source, hsource⟩
            have hbalancedPoint :
                point ∈ balancing.refined.union ∩
                  wz1PaperGridCube rho (cellIndex other) := by
              exact
                ⟨⟨(cover.fullFiberSubfamily parent).embedding source,
                    hsource⟩,
                  hpoint.2⟩
            have hbalancedIntersection :
                balancing.refined.union ∩
                    wz1PaperGridCube rho (cellIndex other) =
                  ⋃ fineCell ∈
                      balancing.selectedFineCells (cellIndex other),
                    wz1PaperGridCube delta fineCell := by
              rw [balancing.refined_union_eq]
              exact
                wz2RefinedUnion_inter_coarseCube
                  balancing.retainedFineCells_eq
                  balancing.fine_cell_containment
                  (cellEquiv other).2
            have hselectedPoint :
                point ∈
                  ⋃ fineCell ∈
                      balancing.selectedFineCells (cellIndex other),
                    wz1PaperGridCube delta fineCell := by
              rwa [← hbalancedIntersection]
            have hpointRetained :
                point ∈ wz2RetainedCellsUnion
                  delta retainedFineCells := by
              rcases Set.mem_iUnion₂.mp hselectedPoint with
                ⟨fineCell, hfineCell, hpointFineCell⟩
              exact Set.mem_iUnion₂.mpr
                ⟨fineCell,
                  Finset.mem_biUnion.mpr
                    ⟨cellIndex other,
                      Finset.mem_image.mpr
                        ⟨other, hother, rfl⟩,
                      hfineCell⟩,
                  hpointFineCell⟩
            have hrefinedCarrier :
                point ∈ refined.carrier
                  ((cover.fullFiberSubfamily parent).embedding source) := by
              exact ⟨hsource, hpointRetained⟩
            exact ⟨⟨source, hrefinedCarrier⟩, hpoint.2⟩
          exact hsourceLower.trans hmono
        · rw [if_neg hactive]
          simp
      have hsumIntersections :
          (∑ other ∈ goodCellIndices,
              volume
                ((restrictPaperShading
                    (cover.fullFiberSubfamily parent)
                    refined).union ∩
                  wz1PaperGridCube rho (cellIndex other))) ≤
            (restrictPaperShading
              (cover.fullFiberSubfamily parent)
              refined).mass := by
        calc
          (∑ other ∈ goodCellIndices,
              volume
                ((restrictPaperShading
                    (cover.fullFiberSubfamily parent)
                    refined).union ∩
                  wz1PaperGridCube rho (cellIndex other))) ≤
              volume
                (restrictPaperShading
                  (cover.fullFiberSubfamily parent)
                  refined).union := by
            have hdisjoint :
                Set.PairwiseDisjoint
                  (↑goodCellIndices)
                  (fun other =>
                    (restrictPaperShading
                      (cover.fullFiberSubfamily parent)
                      refined).union ∩
                    wz1PaperGridCube rho (cellIndex other)) := by
              intro first hfirst second hsecond hne
              apply Disjoint.mono_right Set.inter_subset_right
              apply Disjoint.mono_left Set.inter_subset_right
              exact wz1PaperGridCube_disjoint
                (fun heq =>
                  hne (cellIndex_injective heq))
            have hmeasure :
                volume
                    (⋃ other ∈ goodCellIndices,
                      (restrictPaperShading
                        (cover.fullFiberSubfamily parent)
                        refined).union ∩
                      wz1PaperGridCube rho (cellIndex other)) =
                  ∑ other ∈ goodCellIndices,
                    volume
                      ((restrictPaperShading
                        (cover.fullFiberSubfamily parent)
                        refined).union ∩
                      wz1PaperGridCube rho (cellIndex other)) := by
              rw [MeasureTheory.measure_biUnion_finset]
              · exact hdisjoint
              · intro other _
                exact
                  (measurableSet_shading_union _).inter
                    (wz1PaperGridCube_measurable _)
            rw [← hmeasure]
            exact measure_mono
              (Set.iUnion₂_subset fun _ _ =>
                Set.inter_subset_left)
          _ ≤
              (restrictPaperShading
                (cover.fullFiberSubfamily parent)
                refined).mass :=
            paperShading_union_volume_le_mass _
      exact
        (Finset.sum_le_sum fun other hother =>
          hcellwise other hother).trans hsumIntersections
    exact hgood.trans hsumLe
  have deletedCellMass :
      (balancing.retainedCoarseCells.card -
          goodCells.card : ℕ) * balancing.cellMass ≤
        2 * (degreeCap : ENNReal) * threshold *
          ∑ parent : Fin coarse.card, referenceFiberMass parent := by
    have deletedCard :
        ((Finset.univ : Finset (Fin ambientCells.card)) \
            goodCellIndices).card =
          balancing.retainedCoarseCells.card -
            goodCells.card := by
      have hgoodCard :
          goodCells.card = goodCellIndices.card :=
        Finset.card_image_iff.mpr
          (Set.injOn_of_injective cellIndex_injective)
      calc
        ((Finset.univ : Finset (Fin ambientCells.card)) \
            goodCellIndices).card =
            (Finset.univ : Finset (Fin ambientCells.card)).card -
              goodCellIndices.card :=
          Finset.card_sdiff_of_subset (Finset.subset_univ _)
        _ = ambientCells.card - goodCellIndices.card := by simp
        _ =
            balancing.retainedCoarseCells.card -
              goodCells.card := by
          rw [hgoodCard]
    have hdeleted :
        (∑ index ∈
            (Finset.univ : Finset (Fin ambientCells.card)) \
              goodCellIndices,
            cellMass index) ≤
          2 * (degreeCap : ENNReal) * threshold *
            ∑ parent : Fin coarse.card, referenceFiberMass parent :=
      deletedMass
    have hsum :
        (∑ index ∈
            (Finset.univ : Finset (Fin ambientCells.card)) \
              goodCellIndices,
            cellMass index) =
          (((Finset.univ : Finset (Fin ambientCells.card)) \
              goodCellIndices).card : ENNReal) *
            balancing.cellMass := by
      simp [cellMass, mul_comm]
    rw [hsum, deletedCard] at hdeleted
    simpa using hdeleted
  exact
    ⟨{
      goodCells := goodCells
      goodCells_nonempty := goodCellsNonempty
      goodCells_subset := goodCellsSubset
      retainedParents := retainedParents
      retainedParents_eq := rfl
      retainedParents_nonempty := retainedParentsNonempty
      retainedFineCells := retainedFineCells
      retainedFineCells_eq := rfl
      refined := refined
      refined_eq := rfl
      refined_subshading := wz2RefinedShading_subshading
      refined_cubical := refinedCubical
      refined_union_eq := refinedUnion
      retained_cell_mass := retainedCellMass
      parent_fiber_mass_floor := parentFiberMassFloor
      deleted_cell_mass := deletedCellMass
    }⟩

end Kakeya.Assouad

end
