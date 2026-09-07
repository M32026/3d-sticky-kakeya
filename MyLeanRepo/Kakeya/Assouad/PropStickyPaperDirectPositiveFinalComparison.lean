import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDirectPositiveFinalParentDeletion
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentMultiplicityBands
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentMultiplicityComparison

/-!
# Multiplicity comparison after direct positive parent deletion

The positive whole-parent deletion retains the fixed paper-refinement
fraction of the pre-deletion final shading.  Its selected fine shading is a
subshading of that same final shading, so the pre-deletion union volume is a
valid upper bound.  The two dyadic multiplicity bands therefore give the
paper's global `mu_coarse * mu_fine` comparison on the surviving cover.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

structure WZ2PaperDirectPositiveFinalComparisonData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (balanced :
      WZ2PaperDirectBalancedData cover shading hdelta hrho 14)
    (deletionExponent : ℕ) where
  postDeletion :
    WZ2PaperDirectFinalParentDeletionData
      balanced
      (wz2PaperDirectFinalParentDeletionThreshold balanced)
      deletionExponent
  bands :
    WZ2PaperFinalParentMultiplicityBandsData postDeletion.deletion
  comparison :
    WZ2PaperFinalParentMultiplicityComparisonData
      postDeletion.deletion bands
      (wz1PaperRefinementFraction delta deletionExponent *
        balanced.finalData.producer.coarseBand.selectedFineShading.mass)
      (volume
        balanced.finalData.producer.coarseBand.selectedFineShading.union)

theorem wz2_paper_direct_positive_final_comparison
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (balanced :
      WZ2PaperDirectBalancedData cover shading hdelta hrho 14)
    (deletionExponent : ℕ)
    (hFraction :
      wz1PaperRefinementFraction delta deletionExponent ≤
        (1 / 2 : ENNReal)) :
    Nonempty
      (WZ2PaperDirectPositiveFinalComparisonData
        balanced deletionExponent) := by
  rcases
      wz2_paper_direct_positive_final_parent_deletion
        balanced deletionExponent hFraction
    with ⟨postDeletion⟩
  rcases
      wz2_paper_final_parent_multiplicity_bands
        postDeletion.deletion
    with ⟨bands⟩
  have hMass :
      wz1PaperRefinementFraction delta deletionExponent *
            balanced.finalData.producer.coarseBand.selectedFineShading.mass ≤
        postDeletion.deletion.restriction.selectedFineShading.mass := by
    simpa only [
      postDeletion.deletion.exactAdapter.exact_refined_eq
    ] using postDeletion.massRetention.retained_mass_to_selected
  have hUnionSubset :
      postDeletion.deletion.restriction.selectedFineShading.union ⊆
        balanced.finalData.producer.coarseBand.selectedFineShading.union := by
    rintro point ⟨index, hpoint⟩
    exact
      ⟨postDeletion.deletion.restriction.selected.embedding index,
        postDeletion.deletion.final_subshading index hpoint⟩
  have hVolume :
      volume
          postDeletion.deletion.restriction.selectedFineShading.union ≤
        volume
          balanced.finalData.producer.coarseBand.selectedFineShading.union :=
    measure_mono hUnionSubset
  rcases
      wz2_paper_final_parent_multiplicity_comparison
        postDeletion.deletion bands
        (wz1PaperRefinementFraction delta deletionExponent *
          balanced.finalData.producer.coarseBand.selectedFineShading.mass)
        (volume
          balanced.finalData.producer.coarseBand.selectedFineShading.union)
        hMass hVolume
    with ⟨comparison⟩
  exact
    ⟨{
      postDeletion := postDeletion
      bands := bands
      comparison := comparison
    }⟩

end Kakeya.Assouad

end
