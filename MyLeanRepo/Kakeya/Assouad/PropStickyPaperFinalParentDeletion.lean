import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentDeletionStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalBalancedCoverExactAdapter
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedActiveParentCells
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedParentDegree
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedParentDeletionRepaired
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedParentDeletionRestriction

/-! # Final quantitative parent deletion -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_final_parent_deletion :
    WZ2PaperFinalParentDeletionStatement := by
  intro delta rho fine coarse cover sourceShading coarseCells
    availableFineCells balancing coarseData hdelta hrho producer
    referenceFiberMass threshold hSmall
  rcases wz2_paper_final_balanced_cover_exact_adapter producer with
    ⟨exactAdapter⟩
  rcases
      wz2_paper_balanced_active_parent_cells
        hdelta hrho cover
        producer.coarseBand.selectedFineShading
        producer.coarseBand.selectedCells
        producer.finalFine.exact.selectedFineCells
        exactAdapter.exact exactAdapter.coarseData
    with ⟨active⟩
  rcases
      wz2_paper_balanced_parent_degree
        hdelta hrho cover
        producer.coarseBand.selectedFineShading
        producer.coarseBand.selectedCells
        producer.finalFine.exact.selectedFineCells
        exactAdapter.exact exactAdapter.coarseData active
        producer.finalFine.fineLevel
        (fun point hpoint =>
          (exactAdapter.fine_multiplicity_band point hpoint).2)
    with ⟨degree⟩
  let degreeCap :=
    wz2PaperBalancedParentDegreeCap
      exactAdapter.exact producer.finalFine.fineLevel
  rcases
      wz2_paper_balanced_parent_deletion_repaired
        hdelta hrho cover
        producer.coarseBand.selectedFineShading
        producer.coarseBand.selectedCells
        producer.finalFine.exact.selectedFineCells
        exactAdapter.exact exactAdapter.coarseData active degreeCap
        degree.active_parent_degree degree.cell_mass_upper
        referenceFiberMass threshold (hSmall exactAdapter)
    with ⟨deletion⟩
  rcases
      wz2_paper_balanced_parent_deletion_restriction
        cover producer.coarseBand.selectedFineShading
        producer.coarseBand.selectedCells
        producer.finalFine.exact.selectedFineCells
        exactAdapter.exact exactAdapter.coarseData active
        degreeCap referenceFiberMass threshold deletion
    with ⟨restriction⟩
  have hFinalSubshading :
      ∀ index,
        restriction.selectedFineShading.carrier index ⊆
          producer.coarseBand.selectedFineShading.carrier
            (restriction.selected.embedding index) := by
    intro index
    have hSelected :
        restriction.selectedFineShading.carrier index ⊆
          exactAdapter.exact.refined.carrier
            (restriction.selected.embedding index) :=
      restriction.selectedFine_subshading index
    rw [exactAdapter.exact_refined_eq] at hSelected
    exact hSelected
  exact
    ⟨{
      exactAdapter := exactAdapter
      active := active
      degree := degree
      deletion := deletion
      restriction := restriction
      final_subshading := hFinalSubshading
    }⟩

end Kakeya.Assouad

end
