import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentMultiplicityBandsStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCompleteFiberReindex
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers

/-! # Preserve multiplicity bands through final parent deletion -/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem wz2_paper_final_parent_multiplicity_bands :
    WZ2PaperFinalParentMultiplicityBandsStatement := by
  intro delta rho fine coarse cover sourceShading coarseCells
    availableFineCells balancing coarseData hdelta hrho producer
    referenceFiberMass threshold finalDeletion
  let exactAdapter := finalDeletion.exactAdapter
  let active := finalDeletion.active
  let deletion := finalDeletion.deletion
  let restriction := finalDeletion.restriction
  let selected := restriction.selected
  let coarseSub :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      coarse deletion.retainedParents
  have hCoarseBand :
      ∀ point ∈ restriction.selectedCoarseShading.union,
        (2 ^ producer.coarseBand.level : ENNReal) ≤
            (restriction.selectedCoarseShading.pointMultiplicity point :
              ENNReal) ∧
          (restriction.selectedCoarseShading.pointMultiplicity point :
              ENNReal) <
            (2 ^ (producer.coarseBand.level + 1) : ENNReal) := by
    intro point hpoint
    rcases hpoint with ⟨localParent, hpointParent⟩
    rw [restriction.selectedCoarseShading_carrier_eq] at hpointParent
    rcases Set.mem_iUnion₂.mp hpointParent with
      ⟨cell, hcellParent, hpointCell⟩
    rw [restriction.parentCells_eq] at hcellParent
    have hcellGood : cell ∈ deletion.goodCells :=
      (Finset.mem_filter.mp hcellParent).1
    have hcellExact :
        cell ∈ exactAdapter.exact.retainedCoarseCells :=
      deletion.goodCells_subset hcellGood
    have hNewCard :
        restriction.selectedCoarseShading.pointMultiplicity point =
          (active.activeParents cell).card := by
      let localActive :
          Finset (Fin coarseSub.family.card) :=
        Finset.univ.filter fun parent =>
          point ∈ restriction.selectedCoarseShading.carrier parent
      let ambientActive :=
        active.activeParents cell
      have hCard : localActive.card = ambientActive.card := by
        apply Finset.card_bij
          (fun parent _ => coarseSub.embedding parent)
        · intro parent hparent
          have hpointLocal :
              point ∈
                restriction.selectedCoarseShading.carrier parent :=
            (Finset.mem_filter.mp hparent).2
          rw [restriction.selectedCoarseShading_carrier_eq] at hpointLocal
          rcases Set.mem_iUnion₂.mp hpointLocal with
            ⟨otherCell, hotherParent, hpointOther⟩
          rw [restriction.parentCells_eq] at hotherParent
          have hotherActive :=
            (Finset.mem_filter.mp hotherParent).2
          have hcellEq : otherCell = cell := by
            have hfirst :
                wz1PaperGridIndex rho point = otherCell :=
              (mem_wz1PaperGridCube rho otherCell point).mp hpointOther
            have hsecond :
                wz1PaperGridIndex rho point = cell :=
              (mem_wz1PaperGridCube rho cell point).mp hpointCell
            exact hfirst.symm.trans hsecond
          simpa [ambientActive, hcellEq] using hotherActive
        · intro first _ second _ h
          exact coarseSub.embedding.injective h
        · intro ambientParent hparent
          have hactive :
              ambientParent ∈ active.activeParents cell :=
            hparent
          have hretained :
              ambientParent ∈ deletion.retainedParents := by
            rw [deletion.retainedParents_eq]
            exact Finset.mem_biUnion.mpr
              ⟨cell, hcellGood, hactive⟩
          let parentSubtype : deletion.retainedParents :=
            ⟨ambientParent, hretained⟩
          let parent : Fin coarseSub.family.card :=
            (deletion.retainedParents.orderIsoOfFin rfl).symm
              parentSubtype
          have hEmbedding :
              coarseSub.embedding parent = ambientParent :=
            congrArg Subtype.val
              (deletion.retainedParents.orderIsoOfFin rfl
                |>.apply_symm_apply parentSubtype)
          refine ⟨parent, ?_, hEmbedding⟩
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [restriction.selectedCoarseShading_carrier_eq]
          exact Set.mem_iUnion₂.mpr
            ⟨cell,
              by
                rw [restriction.parentCells_eq, Finset.mem_filter]
                refine ⟨hcellGood, ?_⟩
                rw [hEmbedding]
                exact hactive,
              hpointCell⟩
      change localActive.card = ambientActive.card at hCard
      exact hCard
    have hRepresentativeUnion :
        active.representative cell ∈
          exactAdapter.coarseData.coarseShading.union := by
      rcases
          exactAdapter.coarseData.retained_cell_owned
            cell hcellExact
        with ⟨parent, hparent⟩
      exact
        ⟨parent, by
          rw [exactAdapter.coarseData.coarseShading_carrier_eq]
          exact Set.mem_iUnion₂.mpr
            ⟨cell, hparent, active.representative_mem cell⟩⟩
    have hOldBand :
        (2 ^ producer.coarseBand.level : ENNReal) ≤
            (exactAdapter.coarseData.coarseShading.pointMultiplicity
              (active.representative cell) : ENNReal) ∧
          (exactAdapter.coarseData.coarseShading.pointMultiplicity
              (active.representative cell) : ENNReal) <
            (2 ^ (producer.coarseBand.level + 1) : ENNReal) := by
      have h :=
        producer.finalCover.coarse_multiplicity_band
          (active.representative cell)
          (by
            rw [← exactAdapter.coarseData_coarseShading_eq]
            exact hRepresentativeUnion)
      simpa [exactAdapter.coarseData_coarseShading_eq] using h
    have hActiveCard :
        (active.activeParents cell).card =
          exactAdapter.coarseData.coarseShading.pointMultiplicity
            (active.representative cell) :=
      active.activeParents_card_eq cell hcellExact
    exact_mod_cast
      (show
        (2 ^ producer.coarseBand.level : ENNReal) ≤
            (restriction.selectedCoarseShading.pointMultiplicity point :
              ENNReal) ∧
          (restriction.selectedCoarseShading.pointMultiplicity point :
              ENNReal) <
            (2 ^ (producer.coarseBand.level + 1) : ENNReal) by
        rw [hNewCard, hActiveCard]
        exact hOldBand)
  have hFiberBand :
      ∀ parent point,
        point ∈
            (restrictPaperShading
              (restriction.restrictedCover.fullFiberSubfamily parent)
              restriction.selectedFineShading).union →
          (2 ^ producer.fiberBand.level : ENNReal) ≤
              ((restrictPaperShading
                (restriction.restrictedCover.fullFiberSubfamily parent)
                restriction.selectedFineShading).pointMultiplicity point :
                ENNReal) ∧
            ((restrictPaperShading
              (restriction.restrictedCover.fullFiberSubfamily parent)
              restriction.selectedFineShading).pointMultiplicity point :
              ENNReal) <
              (2 ^ (producer.fiberBand.level + 1) : ENNReal) := by
    intro parent point hpoint
    let ambientParent := coarseSub.embedding parent
    rcases
        wz2_paper_complete_fiber_reindex
          cover selected restriction.restrictedCover
          parent ambientParent
          (restriction.full_fiber_complete parent)
      with ⟨reindex⟩
    let localFiber :=
      restriction.restrictedCover.fullFiberSubfamily parent
    let ambientFiber :=
      cover.fullFiberSubfamily ambientParent
    let newFiberShading :=
      restrictPaperShading localFiber
        restriction.selectedFineShading
    let deletedFiberShading :=
      restrictPaperShading ambientFiber deletion.refined
    let oldFiberShading :=
      restrictPaperShading ambientFiber exactAdapter.exact.refined
    have hNewDeleted :
        newFiberShading.pointMultiplicity point =
          deletedFiberShading.pointMultiplicity point := by
      let localActive :
          Finset (Fin localFiber.family.card) :=
        Finset.univ.filter fun index =>
          point ∈ newFiberShading.carrier index
      let ambientActive :
          Finset (Fin ambientFiber.family.card) :=
        Finset.univ.filter fun index =>
          point ∈ deletedFiberShading.carrier index
      have hCard : localActive.card = ambientActive.card := by
        apply Finset.card_bij
          (fun index _ => reindex.localIndex index)
        · intro index hindex
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          have hpointLocal :=
            (Finset.mem_filter.mp hindex).2
          change point ∈
            restriction.selectedFineShading.carrier
              (localFiber.embedding index) at hpointLocal
          rw [restriction.selectedFineShading_eq] at hpointLocal
          change point ∈
            deletion.refined.carrier
              (selected.embedding (localFiber.embedding index))
              at hpointLocal
          change point ∈
            deletion.refined.carrier
              (ambientFiber.embedding (reindex.localIndex index))
          rw [← reindex.ambient_eq index]
          exact hpointLocal
        · intro first _ second _ h
          exact reindex.localIndex_bijective.1 h
        · intro ambientIndex hindex
          rcases reindex.localIndex_bijective.2 ambientIndex with
            ⟨localIndex, hlocal⟩
          refine ⟨localIndex, ?_, hlocal⟩
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          have hpointAmbient :=
            (Finset.mem_filter.mp hindex).2
          change point ∈
            restriction.selectedFineShading.carrier
              (localFiber.embedding localIndex)
          rw [restriction.selectedFineShading_eq]
          change point ∈
            deletion.refined.carrier
              (selected.embedding (localFiber.embedding localIndex))
          rw [reindex.ambient_eq localIndex, hlocal]
          exact hpointAmbient
      change localActive.card = ambientActive.card at hCard
      exact hCard
    have hpointDeleted :
        point ∈ deletedFiberShading.union := by
      rcases hpoint with ⟨localIndex, hpointLocal⟩
      exact
        ⟨reindex.localIndex localIndex, by
          change point ∈
            restriction.selectedFineShading.carrier
              (localFiber.embedding localIndex) at hpointLocal
          rw [restriction.selectedFineShading_eq] at hpointLocal
          change point ∈
            deletion.refined.carrier
              (ambientFiber.embedding (reindex.localIndex localIndex))
          rw [← reindex.ambient_eq localIndex]
          exact hpointLocal⟩
    have hDeletedOld :
        deletedFiberShading.pointMultiplicity point =
          oldFiberShading.pointMultiplicity point := by
      exact
        wholeCellRestriction_fiberPointMultiplicity_eq
          (S := exactAdapter.exact.refined)
          (T := deletion.refined)
          (U := wz2RetainedCellsUnion
            delta deletion.retainedFineCells)
          (fun index => by
            rw [deletion.refined_eq]
            rfl)
          ambientFiber
          (by simpa [deletedFiberShading] using hpointDeleted)
    have hpointOld :
        point ∈ oldFiberShading.union := by
      rcases hpointDeleted with ⟨index, hpointDeleted⟩
      exact
        ⟨index, deletion.refined_subshading
          (ambientFiber.embedding index) hpointDeleted⟩
    have hpointProducer :
        point ∈
          (restrictPaperShading ambientFiber
            producer.coarseBand.selectedFineShading).union := by
      simpa [oldFiberShading,
        exactAdapter.exact_refined_eq] using hpointOld
    have hOldBand :=
      producer.finalCover.fiber_multiplicity_band
        ambientParent point hpointProducer
    change
      (2 ^ producer.fiberBand.level : ENNReal) ≤
          (newFiberShading.pointMultiplicity point : ENNReal) ∧
        (newFiberShading.pointMultiplicity point : ENNReal) <
          (2 ^ (producer.fiberBand.level + 1) : ENNReal)
    rw [hNewDeleted, hDeletedOld]
    simpa [oldFiberShading,
      exactAdapter.exact_refined_eq] using hOldBand
  exact
    ⟨{
      coarse_band := hCoarseBand
      fiber_band := hFiberBand
    }⟩

end Kakeya.Assouad

end
