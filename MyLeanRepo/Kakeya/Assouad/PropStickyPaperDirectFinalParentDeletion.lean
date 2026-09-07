import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDirectGeometricBalanced
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentDeletion
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentDeletionMassRetention
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGeometricReferenceFiberMass

/-!
# Final complete-parent deletion on the direct balanced route

This is the paper's final low-mass parent pigeonholing, not another
nearby-scale coarse regularization.  It deletes whole coarse cells, keeps
complete fibers of the surviving parents, and pays one explicit fixed paper
refinement exponent.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperDirectFinalParentDeletionData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (balanced :
      WZ2PaperDirectBalancedData cover shading hdelta hrho 14)
    (threshold : ENNReal)
    (deletionExponent : ℕ) where
  deletion :
    WZ2PaperFinalParentDeletionData
      balanced.finalData.producer
      (wz2PaperGeometricReferenceFiberMass cover)
      threshold
  massRetention :
    WZ2PaperFinalParentDeletionMassRetentionData
      deletion deletionExponent

theorem wz2_paper_direct_final_parent_deletion
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (balanced :
      WZ2PaperDirectBalancedData cover shading hdelta hrho 14)
    (threshold : ENNReal)
    (hDeletion :
      ∀ exactAdapter :
          WZ2PaperFinalBalancedCoverExactAdapterData
            balanced.finalData.producer,
        2 *
              (wz2PaperBalancedParentDegreeCap
                exactAdapter.exact
                balanced.finalData.producer.finalFine.fineLevel :
                ENNReal) *
              threshold *
              (∑ parent : Fin coarse.card,
                wz2PaperGeometricReferenceFiberMass cover parent) <
          exactAdapter.exact.cellMass *
            exactAdapter.exact.retainedCoarseCells.card)
    (hMassRetention :
      ∀ deletion :
          WZ2PaperFinalParentDeletionData
            balanced.finalData.producer
            (wz2PaperGeometricReferenceFiberMass cover)
            threshold,
        let fineCap : ENNReal :=
          (2 ^
            (balanced.finalData.producer.finalFine.fineLevel + 1) :
            ENNReal)
        let degreeCap : ENNReal :=
          wz2PaperBalancedParentDegreeCap
            deletion.exactAdapter.exact
            balanced.finalData.producer.finalFine.fineLevel
        fineCap *
              (2 * degreeCap * threshold *
                ∑ parent : Fin coarse.card,
                  wz2PaperGeometricReferenceFiberMass cover parent) ≤
            (1 / 2 : ENNReal) *
              deletion.exactAdapter.exact.refined.mass)
    (deletionExponent : ℕ)
    (hFraction :
      wz1PaperRefinementFraction delta deletionExponent ≤
        (1 / 2 : ENNReal)) :
    Nonempty
      (WZ2PaperDirectFinalParentDeletionData
        balanced threshold deletionExponent) := by
  rcases
      wz2_paper_final_parent_deletion
        balanced.finalData.producer
        (wz2PaperGeometricReferenceFiberMass cover)
        threshold hDeletion
    with ⟨deletion⟩
  rcases
      wz2_paper_final_parent_deletion_mass_retention
        deletion (hMassRetention deletion)
        deletionExponent hFraction
    with ⟨massRetention⟩
  exact
    ⟨{
      deletion := deletion
      massRetention := massRetention
    }⟩

end Kakeya.Assouad

end
