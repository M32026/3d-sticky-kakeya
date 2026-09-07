import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedActiveParentCells
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedParentDegree
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantOwnerExactification
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantOwnerFiberMultiplicity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantParentCells
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantParentFineCells
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalBalancedCoverExactAdapter

/-!
# Direct dominant-owner preparation after the final balanced producer

Repackage the final balanced cover as exact-cell data, choose one dominant
coarse parent in every retained literal `rho`-cell, and exactify by retaining
the same number of whole owned `delta`-cells in every surviving cell.

This is the paper-order replacement for the historical route through a
separate pre-owner parent deletion.  No nearby-scale regularizer occurs here.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperDirectOwnerPreparationData
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
    (producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover sourceShading coarseCells availableFineCells
        balancing coarseData) where
  exactAdapter :
    WZ2PaperFinalBalancedCoverExactAdapterData producer
  active :
    WZ2PaperBalancedActiveParentCellsData
      cover producer.coarseBand.selectedFineShading
      producer.coarseBand.selectedCells
      producer.finalFine.exact.selectedFineCells
      exactAdapter.exact exactAdapter.coarseData hdelta hrho
  degree :
    WZ2PaperBalancedParentDegreeData
      cover producer.coarseBand.selectedFineShading
      producer.coarseBand.selectedCells
      producer.finalFine.exact.selectedFineCells
      exactAdapter.exact exactAdapter.coarseData active
      producer.finalFine.fineLevel
  dominant :
    WZ2PaperDominantParentCellsData
      cover producer.coarseBand.selectedFineShading
      producer.coarseBand.selectedCells
      producer.finalFine.exact.selectedFineCells
      exactAdapter.exact exactAdapter.coarseData active
      producer.finalFine.fineLevel degree
  owned :
    WZ2PaperDominantParentFineCellsData
      cover producer.coarseBand.selectedFineShading
      producer.coarseBand.selectedCells
      producer.finalFine.exact.selectedFineCells
      exactAdapter.exact exactAdapter.coarseData active
      producer.finalFine.fineLevel degree dominant
  exactified :
    WZ2PaperDominantOwnerExactificationData
      cover producer.coarseBand.selectedFineShading
      producer.coarseBand.selectedCells
      producer.finalFine.exact.selectedFineCells
      exactAdapter.exact exactAdapter.coarseData active
      producer.finalFine.fineLevel degree dominant owned

theorem wz2_paper_direct_owner_preparation
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
    (producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover sourceShading coarseCells availableFineCells
        balancing coarseData) :
    Nonempty (WZ2PaperDirectOwnerPreparationData producer) := by
  rcases
      wz2_paper_final_balanced_cover_exact_adapter producer
    with ⟨exactAdapter⟩
  rcases
      wz2_paper_balanced_active_parent_cells
        hdelta hrho cover producer.coarseBand.selectedFineShading
        producer.coarseBand.selectedCells
        producer.finalFine.exact.selectedFineCells
        exactAdapter.exact exactAdapter.coarseData
    with ⟨active⟩
  rcases
      wz2_paper_balanced_parent_degree
        hdelta hrho cover producer.coarseBand.selectedFineShading
        producer.coarseBand.selectedCells
        producer.finalFine.exact.selectedFineCells
        exactAdapter.exact exactAdapter.coarseData active
        producer.finalFine.fineLevel
        (fun point hpoint =>
          (exactAdapter.fine_multiplicity_band point hpoint).2)
    with ⟨degree⟩
  rcases
      wz2_paper_dominant_parent_cells
        hdelta hrho cover producer.coarseBand.selectedFineShading
        producer.coarseBand.selectedCells
        producer.finalFine.exact.selectedFineCells
        exactAdapter.exact exactAdapter.coarseData active
        producer.finalFine.fineLevel degree
    with ⟨dominant⟩
  rcases
      wz2_paper_dominant_parent_fine_cells
        hdelta hrho cover producer.coarseBand.selectedFineShading
        producer.coarseBand.selectedCells
        producer.finalFine.exact.selectedFineCells
        exactAdapter.exact exactAdapter.coarseData active
        producer.finalFine.fineLevel
        (fun point hpoint =>
          (exactAdapter.fine_multiplicity_band point hpoint).2)
        degree dominant
    with ⟨owned⟩
  rcases
      wz2_paper_dominant_owner_exactification
        hdelta hrho cover producer.coarseBand.selectedFineShading
        producer.coarseBand.selectedCells
        producer.finalFine.exact.selectedFineCells
        exactAdapter.exact exactAdapter.coarseData active
        producer.finalFine.fineLevel degree dominant owned
    with ⟨exactified⟩
  exact
    ⟨{
      exactAdapter := exactAdapter
      active := active
      degree := degree
      dominant := dominant
      owned := owned
      exactified := exactified
    }⟩

theorem WZ2PaperDirectOwnerPreparationData.fiber_multiplicity_band
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
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover sourceShading coarseCells availableFineCells
        balancing coarseData}
    (data : WZ2PaperDirectOwnerPreparationData producer) :
    ∀ parent :
        Fin
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            coarse data.exactified.retainedParents).family.card,
      ∀ point,
        point ∈
            (restrictPaperShading
              (data.exactified.restrictedCover.fullFiberSubfamily
                parent)
              data.exactified.refined).union →
          (2 ^ producer.fiberBand.level : ENNReal) ≤
              ((restrictPaperShading
                (data.exactified.restrictedCover.fullFiberSubfamily
                  parent)
                data.exactified.refined).pointMultiplicity point :
                ENNReal) ∧
            ((restrictPaperShading
              (data.exactified.restrictedCover.fullFiberSubfamily
                parent)
              data.exactified.refined).pointMultiplicity point :
              ENNReal) <
                (2 ^ (producer.fiberBand.level + 1) : ENNReal) := by
  intro parent point hpoint
  have hMultiplicity :=
    data.exactified.full_fiber_pointMultiplicity_eq
      parent point hpoint
  have hAmbientPoint :
      point ∈
        (restrictPaperShading
          (cover.fullFiberSubfamily
            ((Kakeya.Streamlined.TubeSubfamily.fromFinset
              coarse data.exactified.retainedParents).embedding
                parent))
          data.exactAdapter.exact.refined).union := by
    let packed :=
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        coarse data.exactified.retainedParents
    let localFiber :=
      data.exactified.restrictedCover.fullFiberSubfamily parent
    let ambientFiber :=
      cover.fullFiberSubfamily (packed.embedding parent)
    rcases hpoint with ⟨index, hindex⟩
    have hImage :
        data.exactified.selected.embedding
            (localFiber.embedding index) ∈
          Finset.image data.exactified.selected.embedding
            (wz2PaperFullFiberIndices
              data.exactified.selected.family packed.family parent) :=
      Finset.mem_image.mpr
        ⟨localFiber.embedding index,
          data.exactified.restrictedCover.fullFiberSubfamily_mem
            parent index,
          rfl⟩
    rw [data.exactified.full_fiber_complete parent] at hImage
    let ambientMember :
        wz2PaperFullFiberIndices fine coarse
          (packed.embedding parent) :=
      ⟨data.exactified.selected.embedding
          (localFiber.embedding index),
        hImage⟩
    let ambientIndex : Fin ambientFiber.family.card :=
      (wz2PaperFullFiberIndices fine coarse
        (packed.embedding parent)).orderIsoOfFin rfl |>.symm
        ambientMember
    have hEmbedding :
        ambientFiber.embedding ambientIndex =
          data.exactified.selected.embedding
            (localFiber.embedding index) :=
      congrArg Subtype.val <|
        (wz2PaperFullFiberIndices fine coarse
          (packed.embedding parent)).orderIsoOfFin rfl
          |>.apply_symm_apply ambientMember
    refine ⟨ambientIndex, ?_⟩
    change
      point ∈
        data.exactAdapter.exact.refined.carrier
          (ambientFiber.embedding ambientIndex)
    rw [hEmbedding]
    exact
      (data.exactified.refined_carrier_eq
        (localFiber.embedding index)) ▸ hindex |>.1
  have hAmbientBand :=
    producer.finalCover.fiber_multiplicity_band
      ((Kakeya.Streamlined.TubeSubfamily.fromFinset
        coarse data.exactified.retainedParents).embedding parent)
      point
  rw [data.exactAdapter.exact_refined_eq] at hAmbientPoint hMultiplicity
  have hBand := hAmbientBand hAmbientPoint
  rw [hMultiplicity]
  simpa using hBand

theorem WZ2PaperDirectOwnerPreparationData.exactified_subshading
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
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover sourceShading coarseCells availableFineCells
        balancing coarseData}
    (data : WZ2PaperDirectOwnerPreparationData producer) :
    ∀ index,
      data.exactified.refined.carrier index ⊆
        producer.coarseBand.selectedFineShading.carrier
          (data.exactified.selected.embedding index) := by
  intro index
  rw [data.exactified.refined_carrier_eq index]
  refine Set.inter_subset_left.trans ?_
  rw [data.exactAdapter.exact_refined_eq]

end Kakeya.Assouad

end
