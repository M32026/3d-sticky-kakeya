import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicRepresentativeParent
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperCenteredWeightedSelection
import MyLeanRepo.Kakeya.Assouad.WZ1.PaperPackingRefinement

/-!
# Essentially-distinct cleanup after the final positive similarity

The source family is paper-essentially-distinct.  A target centered conflict
pulls back to a fixed-radius source line-metric ball, so the existing
five-dimensional packing theorem gives a finite conflict degree.  Weighted
independent selection then supplies the ordinary distinctness required by the
representative-parent construction.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Exact finite packing bound for final-isotropic centered conflicts. -/
def pureWZ2IsotropicCenteredConflictDegree
    (sourceDelta targetDelta : ℝ) : ℕ :=
  (2 * Nat.ceil
      (8 * (42 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
        targetDelta) / ((2 / 3 : ℝ) * sourceDelta)) + 1) ^ 5

/-- Weighted cleanup of the midpoint-centered isotropic image family. -/
theorem pureWZ2_isotropic_centered_distinct_selection
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (center : Point3) {scale : ℝ} (hscale : 1 ≤ scale)
    (hcenter : |center 2| ≤ 1)
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : 0 < targetDelta)
    (hsourcePackingDistinct : WZ1PaperIsEssentiallyDistinct
      (pureWZ2CenteredPackingFamily sourceFamily))
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hisotropicLine : WZ1PaperIsLineClass
      (pureWZ2IsotropicPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale))
    (targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)) :
    ∃ selected : Finset (Fin sourceFamily.card),
      let subfamily := Kakeya.Streamlined.TubeSubfamily.fromFinset
        (pureWZ2IsotropicCenteredPaperFamily
          (targetDelta := targetDelta) sourceFamily center scale) selected
      WZ2PaperOrdinaryIsEssentiallyDistinct subfamily.family ∧
        (∀ index : Fin sourceFamily.card, index ∈ selected ∨
          ∃ representative ∈ selected,
            pureWZ2PaperCenteredConflict
              (pureWZ2IsotropicCenteredPaperFamily
                (targetDelta := targetDelta) sourceFamily center scale)
              index representative) ∧
        targetShading.mass ≤
          (pureWZ2IsotropicCenteredConflictDegree sourceDelta targetDelta + 1 :
            ENNReal) *
          (restrictPaperShading subfamily targetShading).mass := by
  let targetFamily := pureWZ2IsotropicCenteredPaperFamily
    (targetDelta := targetDelta) sourceFamily center scale
  have htargetLine : WZ1PaperIsLineClass targetFamily := by
    intro index
    exact pureWZ2PaperCenteredTube_lineClass (hisotropicLine index)
  have hdegree : ∀ reference : Fin targetFamily.card,
      ((Finset.univ : Finset (Fin targetFamily.card)).filter
        (pureWZ2PaperCenteredConflict targetFamily reference)).card ≤
      pureWZ2IsotropicCenteredConflictDegree sourceDelta targetDelta := by
    intro reference
    change Fin sourceFamily.card at reference
    have hpackingLine : WZ1PaperIsLineClass
        (pureWZ2CenteredPackingFamily sourceFamily) := by
      intro index
      exact wz2PaperRelabelTube_lineClass
        (pureWZ2PaperCenteredTube_lineClass (hsourceLine index))
    have hpacking := tube_packing_bound_general hsourcePackingDistinct
      hpackingLine
      (mul_pos (by norm_num) hsourceDelta)
      (42 * wz2PaperLocalizedDoubledFiberLineDistanceConstant * targetDelta)
      (by
        unfold wz2PaperLocalizedDoubledFiberLineDistanceConstant
        positivity) reference
    let targetConflict :=
      (Finset.univ : Finset (Fin sourceFamily.card)).filter
        (pureWZ2PaperCenteredConflict targetFamily reference)
    let sourceBall := (Finset.univ : Finset (Fin sourceFamily.card)).filter
      (fun other => wz1PaperLineDistance
        ((pureWZ2CenteredPackingFamily sourceFamily).tube other)
        ((pureWZ2CenteredPackingFamily sourceFamily).tube reference) ≤
          42 * wz2PaperLocalizedDoubledFiberLineDistanceConstant * targetDelta)
    have hsubset : targetConflict ⊆ sourceBall := by
      intro other hother
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change wz1PaperLineDistance
          (wz2PaperRelabelTube
            (pureWZ2PaperCenteredTube (sourceFamily.tube other)))
          (wz2PaperRelabelTube
            (pureWZ2PaperCenteredTube (sourceFamily.tube reference))) ≤ _
      rw [wz2PaperRelabelTube_lineDistance_both,
        pureWZ2PaperCenteredTube_lineDistance _ _
          (hsourceLine other) (hsourceLine reference)]
      rw [← wz1PaperLineDistance_symm]
      exact source_lineDistance_le_of_isotropic_centered_conflict
        sourceFamily center hscale hcenter htargetDelta hsourceLine
        hisotropicLine htargetLine reference other
        (Finset.mem_filter.mp hother).2
    exact (Finset.card_le_card hsubset).trans <| by
      change sourceBall.card ≤
        pureWZ2IsotropicCenteredConflictDegree sourceDelta targetDelta
      change
        ((Finset.univ : Finset (Fin sourceFamily.card)).filter
          (fun other => wz1PaperLineDistance
            ((pureWZ2CenteredPackingFamily sourceFamily).tube other)
            ((pureWZ2CenteredPackingFamily sourceFamily).tube reference) ≤
              42 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
                targetDelta)).card ≤ _
      exact hpacking
  exact pureWZ2_paper_weighted_centered_distinct_selection
    targetFamily targetShading
    (pureWZ2IsotropicCenteredConflictDegree sourceDelta targetDelta) hdegree

/-- The final-isotropic cleanup together with the exact retained target
subfamily and its quantitative shading loss.  Keeping this as data, rather
than only an existential finset, lets the subsequent source-side nearby-CWA
regularization use precisely the same support. -/
structure PureWZ2IsotropicDistinctCleanupData
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (center : Point3) (scale : ℝ)
    (targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)) where
  selected : Finset (Fin sourceFamily.card)
  distinct : WZ2PaperOrdinaryIsEssentiallyDistinct
    (Kakeya.Streamlined.TubeSubfamily.fromFinset
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale) selected).family
  maximal : ∀ index : Fin sourceFamily.card, index ∈ selected ∨
    ∃ representative ∈ selected,
      pureWZ2PaperCenteredConflict
        (pureWZ2IsotropicCenteredPaperFamily
          (targetDelta := targetDelta) sourceFamily center scale)
        index representative
  mass_lower : targetShading.mass ≤
    (pureWZ2IsotropicCenteredConflictDegree sourceDelta targetDelta + 1 :
      ENNReal) *
      (restrictPaperShading
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          (pureWZ2IsotropicCenteredPaperFamily
            (targetDelta := targetDelta) sourceFamily center scale) selected)
        targetShading).mass

/-- Package the weighted final-isotropic cleanup as reusable data. -/
theorem pureWZ2_isotropic_distinct_cleanup
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (center : Point3) {scale : ℝ} (hscale : 1 ≤ scale)
    (hcenter : |center 2| ≤ 1)
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : 0 < targetDelta)
    (hsourcePackingDistinct : WZ1PaperIsEssentiallyDistinct
      (pureWZ2CenteredPackingFamily sourceFamily))
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hisotropicLine : WZ1PaperIsLineClass
      (pureWZ2IsotropicPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale))
    (targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)) :
    Nonempty (PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading) := by
  rcases pureWZ2_isotropic_centered_distinct_selection sourceFamily center
      hscale hcenter hsourceDelta htargetDelta hsourcePackingDistinct
      hsourceLine hisotropicLine targetShading with
    ⟨selected, hdistinct, hmaximal, hmass⟩
  exact ⟨{
    selected := selected
    distinct := hdistinct
    maximal := hmaximal
    mass_lower := hmass
  }⟩

namespace PureWZ2IsotropicDistinctCleanupData

/-- The retained target family of a packaged final-isotropic cleanup. -/
def targetSubfamily
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    (data : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading) :
    Kakeya.Streamlined.TubeSubfamily
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale) :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset _ data.selected

/-- Literal target shading retained by the final-isotropic cleanup. -/
def restrictedShading
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    (data : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading) :
    WZ1PaperTubeShading data.targetSubfamily.family :=
  restrictPaperShading data.targetSubfamily targetShading

/-- The source indices retained by the target centered cleanup. -/
def sourceSubfamily
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    (data : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading) :
    Kakeya.Streamlined.TubeSubfamily sourceFamily :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset sourceFamily data.selected

end PureWZ2IsotropicDistinctCleanupData

end Kakeya.Assouad

end
