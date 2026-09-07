import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPreparedSelectedTotalRefinement
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierVolumeLower
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingHEq
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound

/-!
# Canonical mass and volume inputs after the final paper refinement

The source pair is `sourceLoss`-extremal.  Its density and the quadratic
lower volume of every cropped paper tube give a canonical total shaded-mass
lower bound.  The composed final paper refinement retains its explicit
polylogarithmic fraction of that mass, while its union remains inside the
source union.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

def wz2PaperCanonicalPostMassLower
    (delta sourceLoss : ℝ)
    (totalExponent : ℕ)
    (sourceCardinality : ENNReal) : ENNReal :=
  wz1PaperRefinementFraction delta totalExponent *
    Kakeya.realRpowENN delta sourceLoss *
    Kakeya.realRpowENN delta 2 *
    sourceCardinality

theorem wz2_paper_source_extremal_mass_lower
    {delta sigma sourceLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading source)
    (extremal :
      WZ2PaperExactScaleExtremal
        sigma sourceLoss source shading)
    (hdeltaSmall : delta ≤ 1 / 12) :
    Kakeya.realRpowENN delta sourceLoss *
          Kakeya.realRpowENN delta 2 *
          source.enncard ≤
      shading.mass := by
  have hBodyMass :
      Kakeya.realRpowENN delta 2 * source.enncard ≤
        (wz1PaperBodyFamily source).mass := by
    calc
      Kakeya.realRpowENN delta 2 * source.enncard =
          ∑ _index : Fin source.card,
            Kakeya.realRpowENN delta 2 := by
        simp [Kakeya.Streamlined.TubeFamily.enncard,
          Finset.sum_const, mul_comm]
      _ ≤
          ∑ index : Fin source.card,
            volume (wz1PaperTubeCarrier (source.tube index)) := by
        apply Finset.sum_le_sum
        intro index _
        simpa [Kakeya.realRpowENN, Real.rpow_two] using
          (canonical_volume_lower extremal.delta_pos).trans
            (wz2PaperTubeCarrier_volume_lower
              extremal.delta_pos hdeltaSmall
              (source.tube index)
              (extremal.cwa_exact_scales.2.1 index))
      _ = (wz1PaperBodyFamily source).mass := rfl
  calc
    Kakeya.realRpowENN delta sourceLoss *
          Kakeya.realRpowENN delta 2 *
          source.enncard =
        Kakeya.realRpowENN delta sourceLoss *
          (Kakeya.realRpowENN delta 2 * source.enncard) := by
      ring
    _ ≤
        Kakeya.realRpowENN delta sourceLoss *
          (wz1PaperBodyFamily source).mass := by
      gcongr
    _ ≤ shading.mass := extremal.dense

theorem wz2_paper_prepared_selected_canonical_post_mass_lower
    {delta sourceLoss stableLoss sigma floorLoss strongLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    {critical :
      WZ2PaperCriticalFloorSelectionData
        sigma floorLoss strongLoss}
    {structural :
      WZ2PaperPreparedParentwiseStructuralProducerData
        (outputLoss := outputLoss) prepared critical}
    {ambientConstant outputConstant normalizationWeight weightUpper :
      ENNReal}
    {levelCount parentExponent : ℕ}
    {regularization :
      WZ2PaperPreparedCoarseParentRegularizationData
        prepared critical structural
        ambientConstant outputConstant normalizationWeight weightUpper
        levelCount}
    {pullback :
      WZ2PaperPreparedCoarseParentPullbackData
        regularization parentExponent}
    {selectedRebalancing :
      WZ2PaperPreparedSelectedRebalancingData pullback}
    {finalLogExponent : ℕ}
    {selectedFinal :
      WZ2PaperPreparedSelectedFinalData
        selectedRebalancing finalLogExponent}
    {massLower volumeUpper threshold : ENNReal}
    {selectedComparison :
      WZ2PaperPreparedSelectedComparisonData
        selectedFinal massLower volumeUpper}
    {deletionExponent : ℕ}
    {post :
      WZ2PaperPreparedSelectedPostDeletionData
        selectedComparison threshold deletionExponent}
    {globalBalancingExponent : ℕ}
    (total :
      WZ2PaperPreparedSelectedTotalRefinementData
        post globalBalancingExponent)
    (sourceExtremal :
      WZ2PaperExactScaleExtremal
        sigma sourceLoss source shading)
    (hdeltaSmall : delta ≤ 1 / 12) :
    wz2PaperCanonicalPostMassLower delta sourceLoss
          ((((preparationExponent + 4) + parentExponent) +
            globalBalancingExponent) + deletionExponent)
          source.enncard ≤
      post.deletion.restriction.selectedFineShading.mass := by
  have hSource :=
    wz2_paper_source_extremal_mass_lower
      shading sourceExtremal hdeltaSmall
  have hRetained :
      wz2PaperCanonicalPostMassLower delta sourceLoss
            ((((preparationExponent + 4) + parentExponent) +
              globalBalancingExponent) + deletionExponent)
            source.enncard ≤
        total.refinement.refined.mass := by
    calc
      wz2PaperCanonicalPostMassLower delta sourceLoss
            ((((preparationExponent + 4) + parentExponent) +
              globalBalancingExponent) + deletionExponent)
            source.enncard =
          wz1PaperRefinementFraction delta
              ((((preparationExponent + 4) + parentExponent) +
                globalBalancingExponent) + deletionExponent) *
            (Kakeya.realRpowENN delta sourceLoss *
              Kakeya.realRpowENN delta 2 * source.enncard) := by
        unfold wz2PaperCanonicalPostMassLower
        ring
      _ ≤
          wz1PaperRefinementFraction delta
              ((((preparationExponent + 4) + parentExponent) +
                globalBalancingExponent) + deletionExponent) *
            shading.mass := by
        exact mul_le_mul_left' hSource _
      _ ≤ total.refinement.refined.mass :=
        total.refinement.retained_mass
  have hMassEq :
      total.refinement.refined.mass =
        post.deletion.restriction.selectedFineShading.mass :=
    paperShading_mass_eq_of_heq
      total.selected_family_eq total.refined_heq
  exact hRetained.trans_eq hMassEq

theorem wz2_paper_prepared_selected_canonical_post_volume_upper
    {delta sourceLoss stableLoss sigma floorLoss strongLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    {critical :
      WZ2PaperCriticalFloorSelectionData
        sigma floorLoss strongLoss}
    {structural :
      WZ2PaperPreparedParentwiseStructuralProducerData
        (outputLoss := outputLoss) prepared critical}
    {ambientConstant outputConstant normalizationWeight weightUpper :
      ENNReal}
    {levelCount parentExponent : ℕ}
    {regularization :
      WZ2PaperPreparedCoarseParentRegularizationData
        prepared critical structural
        ambientConstant outputConstant normalizationWeight weightUpper
        levelCount}
    {pullback :
      WZ2PaperPreparedCoarseParentPullbackData
        regularization parentExponent}
    {selectedRebalancing :
      WZ2PaperPreparedSelectedRebalancingData pullback}
    {finalLogExponent : ℕ}
    {selectedFinal :
      WZ2PaperPreparedSelectedFinalData
        selectedRebalancing finalLogExponent}
    {massLower volumeUpper threshold : ENNReal}
    {selectedComparison :
      WZ2PaperPreparedSelectedComparisonData
        selectedFinal massLower volumeUpper}
    {deletionExponent : ℕ}
    {post :
      WZ2PaperPreparedSelectedPostDeletionData
        selectedComparison threshold deletionExponent}
    {globalBalancingExponent : ℕ}
    (total :
      WZ2PaperPreparedSelectedTotalRefinementData
        post globalBalancingExponent)
    (sourceExtremal :
      WZ2PaperExactScaleExtremal
        sigma sourceLoss source shading) :
    volume post.deletion.restriction.selectedFineShading.union ≤
      Kakeya.realRpowENN delta (sigma - sourceLoss) := by
  have hSubset :
      total.refinement.refined.union ⊆ shading.union := by
    intro point hpoint
    rcases hpoint with ⟨index, hindex⟩
    exact
      ⟨total.refinement.selected.embedding index,
        total.refinement.subshading index hindex⟩
  have hVolume :
      volume total.refinement.refined.union ≤
        Kakeya.realRpowENN delta (sigma - sourceLoss) :=
    (measure_mono hSubset).trans sourceExtremal.volume_upper
  have hVolumeEq :
      volume total.refinement.refined.union =
        volume post.deletion.restriction.selectedFineShading.union :=
    paperShading_union_volume_eq_of_heq
      total.selected_family_eq total.refined_heq
  rw [← hVolumeEq]
  exact hVolume

end Kakeya.Assouad

end
