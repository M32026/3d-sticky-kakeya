import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDirectPositiveFinalComparison

/-!
# Half-mass retention for the direct positive deletion
-/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_direct_positive_half_mass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {balanced :
      WZ2PaperDirectBalancedData cover shading hdelta hrho 14}
    {deletionExponent : ℕ}
    (post :
      WZ2PaperDirectPositiveFinalComparisonData
        balanced deletionExponent) :
    balanced.finalData.producer.coarseBand.selectedFineShading.mass ≤
      2 *
        post.postDeletion.deletion.restriction.selectedFineShading.mass := by
  have hSource := post.postDeletion.massRetention.source_mass_le
  rw [post.postDeletion.deletion.exactAdapter.exact_refined_eq] at hSource
  exact hSource

end Kakeya.Assouad

end
