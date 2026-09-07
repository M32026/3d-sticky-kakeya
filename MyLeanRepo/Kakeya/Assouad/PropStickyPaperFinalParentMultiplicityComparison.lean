import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentMultiplicityComparisonStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalMultiplicityComparison

/-! # Compare multiplicities on the final retained cover -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_final_parent_multiplicity_comparison :
    WZ2PaperFinalParentMultiplicityComparisonStatement := by
  intro delta rho fine coarse cover sourceShading coarseCells
    availableFineCells balancing coarseData hdelta hrho producer
    referenceFiberMass threshold finalDeletion bands
    massLower volumeUpper hMass hVolume
  rcases
      wz2_paper_final_multiplicity_comparison
        finalDeletion.restriction.restrictedCover
        finalDeletion.restriction.selectedFineShading
        finalDeletion.restriction.selectedCoarseShading
        finalDeletion.restriction.balanced
        producer.coarseBand.level producer.fiberBand.level
        bands.coarse_band bands.fiber_band
        massLower volumeUpper hMass hVolume
    with ⟨comparison⟩
  exact ⟨{ comparison := comparison }⟩

end Kakeya.Assouad

end
