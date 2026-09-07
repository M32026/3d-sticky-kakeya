import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedParentwiseStructuralProducerStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentQuantitativeEnvelopeStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyConvexWolffSubfamilyTransfer

/-!
# Top-level CWA after the parentwise structural merge

The complete caller fibers partition the strict-prepared fine family.  The
one-parent selections have one common weighted cardinality loss, so summing
their retention inequalities gives a global weighted cardinality retention
for the merged selected family.  The normalized top-level Convex--Wolff bound
stored by strict preparation then transfers to that merged family.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem WZ2PaperPartitioningCover.sum_fullFiberSubfamily_enncard
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse) :
    (∑ parent : Fin coarse.card,
        (cover.fullFiberSubfamily parent).family.enncard) =
      fine.enncard := by
  have hnatural :
      ∑ parent : Fin coarse.card,
          (cover.fiberIndices parent).card =
        fine.card := by
    have hfiberwise :=
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin fine.card))
        (Finset.univ : Finset (Fin coarse.card))
        cover.parent
    simpa [WZ1PaperTubeCover.fiberIndices] using hfiberwise
  calc
    (∑ parent : Fin coarse.card,
        (cover.fullFiberSubfamily parent).family.enncard)
        =
      ∑ parent : Fin coarse.card,
        ((cover.fiberIndices parent).card : ENNReal) := by
      apply Finset.sum_congr rfl
      intro parent _
      change
        ((wz2PaperFullFiberIndices fine coarse parent).card :
          ENNReal) =
        ((cover.fiberIndices parent).card : ENNReal)
      rw [cover.fullFiberIndices_eq]
    _ = (fine.card : ENNReal) := by
      rw [← Nat.cast_sum]
      exact_mod_cast hnatural
    _ = fine.enncard := by
      simp [Kakeya.Streamlined.TubeFamily.enncard]

theorem wz2_paper_prepared_parentwise_merged_cardinality_retention
    {delta sourceLoss stableLoss sigma floorLoss strongLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (critical :
      WZ2PaperCriticalFloorSelectionData
        sigma floorLoss strongLoss)
    (structural :
      WZ2PaperPreparedParentwiseStructuralProducerData
        (outputLoss := outputLoss) prepared critical) :
    let weight :=
      (1 / 2 : ENNReal) *
        Kakeya.realRpowENN delta sourceLoss
    let finiteLoss :=
      wz2PaperPreparedOneParentFiniteLoss sourceLoss
    let geometry :=
      55296 * Kakeya.deltaTubeVolume 1
    weight * prepared.refinement.selected.family.enncard ≤
      (finiteLoss * geometry) *
        structural.merged.merged.refinement.selected.family.enncard := by
  dsimp only
  let weight : ENNReal :=
    (1 / 2 : ENNReal) *
      Kakeya.realRpowENN delta sourceLoss
  let finiteLoss : ENNReal :=
    wz2PaperPreparedOneParentFiniteLoss sourceLoss
  let geometry : ENNReal :=
    55296 * Kakeya.deltaTubeVolume 1
  have hparent :
      ∀ parent : Fin prepared.callerStrict.coarse.card,
        weight *
            (wz2PaperPreparedOneParentFiber
              prepared parent).family.enncard ≤
          (finiteLoss * geometry) *
            ((structural.fiberProducer parent).selection
              |>.refinement.selected.family.enncard) := by
    intro parent
    let selection :=
      (structural.fiberProducer parent).selection
    let quantitative :=
      (structural.fiberProducer parent).quantitative
    have hdepth :
        wz2PaperPreparedOneParentFineScaleCount prepared parent ≤
          wz2PaperPreparedOneParentDepth sourceLoss := by
      dsimp only [wz2PaperPreparedOneParentFineScaleCount,
        wz2PaperPreparedOneParentDepth]
      calc
        prepared.strictScaleCount - prepared.callerLevel.val ≤
            prepared.strictScaleCount := Nat.sub_le _ _
        _ ≤ prepared.levelCount + 1 :=
          prepared.strictScaleCount_le
        _ = Nat.ceil (1 / sourceLoss) + 2 := by
          rw [prepared.levelCount_eq]
    have hmassConstant :
        quantitative.massRetentionConstant ≤ finiteLoss := by
      rw [quantitative.massRetentionConstant_eq]
      dsimp only [finiteLoss,
        wz2PaperPreparedOneParentFiniteLoss]
      gcongr
      exact (by norm_num : (1 : ENNReal) ≤ 2)
    have hcardinalityConstant :
        quantitative.cardinalityRetentionConstant ≤
          finiteLoss * geometry := by
      rw [quantitative.cardinalityRetentionConstant_eq]
      exact mul_le_mul_right' hmassConstant geometry
    calc
      weight *
            (wz2PaperPreparedOneParentFiber
              prepared parent).family.enncard =
          quantitative.weight *
            (wz2PaperPreparedOneParentFiber
              prepared parent).family.enncard := by
        rw [quantitative.weight_eq]
      _ ≤
          quantitative.cardinalityRetentionConstant *
            selection.refinement.selected.family.enncard :=
        quantitative.global_retention
      _ ≤
          (finiteLoss * geometry) *
            selection.refinement.selected.family.enncard := by
        gcongr
  have hsum :
      (∑ parent : Fin prepared.callerStrict.coarse.card,
          weight *
            (wz2PaperPreparedOneParentFiber
              prepared parent).family.enncard) ≤
        ∑ parent : Fin prepared.callerStrict.coarse.card,
          (finiteLoss * geometry) *
            ((structural.fiberProducer parent).selection
              |>.refinement.selected.family.enncard) := by
    exact Finset.sum_le_sum fun parent _ => hparent parent
  have hsourceSum :
      (∑ parent : Fin prepared.callerStrict.coarse.card,
          (wz2PaperPreparedOneParentFiber
            prepared parent).family.enncard) =
        prepared.refinement.selected.family.enncard := by
    exact
      prepared.callerStrict.cover.sum_fullFiberSubfamily_enncard
  have htargetSum :
      (∑ parent : Fin prepared.callerStrict.coarse.card,
          ((structural.fiberProducer parent).selection
            |>.refinement.selected.family.enncard)) =
        structural.merged.merged.refinement.selected.family.enncard := by
    change
      (∑ parent : Fin prepared.callerStrict.coarse.card,
          ((structural.fiberProducer parent).selection
            |>.refinement.selected.family.card : ENNReal)) =
        (structural.merged.merged.refinement.selected.family.card :
          ENNReal)
    rw [← Nat.cast_sum]
    exact_mod_cast structural.merged_selected_card_eq.symm
  calc
    weight * prepared.refinement.selected.family.enncard =
        ∑ parent : Fin prepared.callerStrict.coarse.card,
          weight *
            (wz2PaperPreparedOneParentFiber
              prepared parent).family.enncard := by
      rw [← Finset.mul_sum, hsourceSum]
    _ ≤
        ∑ parent : Fin prepared.callerStrict.coarse.card,
          (finiteLoss * geometry) *
            ((structural.fiberProducer parent).selection
              |>.refinement.selected.family.enncard) := hsum
    _ =
        (finiteLoss * geometry) *
          structural.merged.merged.refinement.selected.family.enncard := by
      rw [← Finset.mul_sum, htargetSum]

theorem wz2_paper_prepared_parentwise_merged_top_level_cwa
    {delta sourceLoss stableLoss sigma floorLoss strongLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (critical :
      WZ2PaperCriticalFloorSelectionData
        sigma floorLoss strongLoss)
    (structural :
      WZ2PaperPreparedParentwiseStructuralProducerData
        (outputLoss := outputLoss) prepared critical) :
    let weight :=
      (1 / 2 : ENNReal) *
        Kakeya.realRpowENN delta sourceLoss
    let finiteLoss :=
      wz2PaperPreparedOneParentFiniteLoss sourceLoss
    let geometry :=
      55296 * Kakeya.deltaTubeVolume 1
    WZ2PaperConvexWolffBound
      structural.merged.merged.refinement.selected.family
      ((weight⁻¹ * (finiteLoss * geometry)) *
        prepared.selectedTopLevelConstant) := by
  dsimp only
  let weight : ENNReal :=
    (1 / 2 : ENNReal) *
      Kakeya.realRpowENN delta sourceLoss
  have hweightZero : weight ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · exact
        (ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos prepared.delta_pos sourceLoss)).ne'
  have hweightTop : weight ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN])
  apply
    prepared.selected_top_level_convex_wolff
      |>.subfamily_of_weighted_cardinality
        structural.merged.merged.refinement.selected
        hweightZero hweightTop
  exact
    wz2_paper_prepared_parentwise_merged_cardinality_retention
      prepared critical structural

theorem wz2_paper_prepared_parentwise_merged_top_level_cwa_canonical
    {delta sourceLoss stableLoss sigma floorLoss strongLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (critical :
      WZ2PaperCriticalFloorSelectionData
        sigma floorLoss strongLoss)
    (structural :
      WZ2PaperPreparedParentwiseStructuralProducerData
        (outputLoss := outputLoss) prepared critical) :
    WZ2PaperConvexWolffBound
      structural.merged.merged.refinement.selected.family
      prepared.boundaryMergedTopLevelConstant := by
  rw [prepared.boundaryMergedTopLevelConstant_eq]
  simpa using
    wz2_paper_prepared_parentwise_merged_top_level_cwa
      prepared critical structural

theorem wz2_paper_prepared_parentwise_merged_card_pos
    {delta sourceLoss stableLoss sigma floorLoss strongLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (critical :
      WZ2PaperCriticalFloorSelectionData
        sigma floorLoss strongLoss)
    (structural :
      WZ2PaperPreparedParentwiseStructuralProducerData
        (outputLoss := outputLoss) prepared critical) :
    0 <
      structural.merged.merged.refinement.selected.family.card := by
  let sourceIndex :
      Fin prepared.refinement.selected.family.card :=
    ⟨0, prepared.selected_card_pos⟩
  let parent : Fin prepared.callerStrict.coarse.card :=
    prepared.callerStrict.cover.parent sourceIndex
  let producer := structural.fiberProducer parent
  have hstructural :
      0 < producer.structural.refinement.selected.family.card := by
    by_contra hzero
    have hcardZero :
        producer.structural.refinement.selected.family.card = 0 := by
      omega
    have henncardZero :
        producer.structural.refinement.selected.family.enncard = 0 := by
      simp [Kakeya.Streamlined.TubeFamily.enncard, hcardZero]
    have htargetZero :
        producer.structural.familyData.targetFamily.enncard = 0 := by
      rw [producer.structural.source_cardinality_eq, henncardZero]
    have htargetCardZero :
        producer.structural.familyData.targetFamily.card = 0 := by
      simpa [Kakeya.Streamlined.TubeFamily.enncard] using htargetZero
    exact
      (Nat.ne_of_gt producer.structural.target_nonempty)
        htargetCardZero
  have hlocal :
      0 <
        producer.selection.refinement.selected.family.card := by
    rw [← producer.structural_selected_card_eq]
    exact hstructural
  rw [structural.merged_selected_card_eq]
  exact
    Finset.sum_pos_iff.mpr
      ⟨parent, Finset.mem_univ _, hlocal⟩

end Kakeya.Assouad

end
