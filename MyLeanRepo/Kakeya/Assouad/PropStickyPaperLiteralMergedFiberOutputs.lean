import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralMergedFiberOutputsStatements

/-! # Literal one-parent outputs on all merged global fibers -/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

lemma paper_refinement_mass_monotone
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {logExponent : ℕ}
    (refinement : WZ1PaperRefinement shading logExponent) :
    refinement.refined.mass ≤ shading.mass := by
  have hCarrier :
      ∀ index : Fin refinement.selected.family.card,
        volume (refinement.refined.carrier index) ≤
          volume
            (shading.carrier
              (refinement.selected.embedding index)) := by
    intro index
    exact measure_mono (refinement.subshading index)
  have hSelectedSum :
      ∑ index : Fin refinement.selected.family.card,
          volume (refinement.refined.carrier index) ≤
        ∑ index : Fin refinement.selected.family.card,
          volume
            (shading.carrier
              (refinement.selected.embedding index)) := by
    apply Finset.sum_le_sum
    intro index _
    exact hCarrier index
  have hInjective :
      Set.InjOn refinement.selected.embedding
        (Finset.univ :
          Finset (Fin refinement.selected.family.card)) := by
    intro first _ second _ h
    exact refinement.selected.embedding.inj' h
  have hImageSum :
      ∑ index : Fin refinement.selected.family.card,
          volume
            (shading.carrier
              (refinement.selected.embedding index)) =
        ∑ index ∈
            Finset.image refinement.selected.embedding Finset.univ,
          volume (shading.carrier index) := by
    rw [Finset.sum_image hInjective]
  have hNonnegative :
      ∀ index : Fin fine.card,
        (0 : ENNReal) ≤ volume (shading.carrier index) := by
    intro index
    exact bot_le
  have hAmbientSum :
      ∑ index ∈
            Finset.image refinement.selected.embedding Finset.univ,
          volume (shading.carrier index) ≤
        ∑ index : Fin fine.card,
          volume (shading.carrier index) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _)
      (fun index _ _ => hNonnegative index)
  calc
    refinement.refined.mass =
        ∑ index : Fin refinement.selected.family.card,
          volume (refinement.refined.carrier index) := by
      rfl
    _ ≤
        ∑ index : Fin refinement.selected.family.card,
          volume
            (shading.carrier
              (refinement.selected.embedding index)) :=
      hSelectedSum
    _ =
        ∑ index ∈
            Finset.image refinement.selected.embedding Finset.univ,
          volume (shading.carrier index) :=
      hImageSum
    _ ≤
        ∑ index : Fin fine.card,
          volume (shading.carrier index) :=
      hAmbientSum
    _ = shading.mass := by
      rfl

lemma paper_refinement_fraction_le_self
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {logExponent : ℕ}
    (refinement : WZ1PaperRefinement shading logExponent) :
    wz1PaperRefinementFraction delta logExponent *
        refinement.refined.mass ≤
      refinement.refined.mass := by
  set fraction :=
    wz1PaperRefinementFraction delta logExponent
  have hMass : refinement.refined.mass ≤ shading.mass :=
    paper_refinement_mass_monotone refinement
  have hRetention :
      fraction * shading.mass ≤ refinement.refined.mass :=
    refinement.retained_mass
  have hSource :
      fraction * shading.mass ≤ shading.mass :=
    hRetention.trans hMass
  by_cases hTop : shading.mass = ⊤
  · by_cases hFraction : fraction = 0
    · rw [hFraction]
      simp
    · have hRefinedTop : refinement.refined.mass = ⊤ := by
        rw [hTop] at hRetention
        have h :
            fraction * (⊤ : ENNReal) = ⊤ :=
          ENNReal.mul_top hFraction
        rw [h] at hRetention
        exact top_le_iff.mp hRetention
      rw [hRefinedTop]
      rw [ENNReal.mul_top hFraction]
  · by_cases hZero : shading.mass = 0
    · have hRefinedZero : refinement.refined.mass = 0 := by
        rw [hZero] at hMass
        simpa using hMass
      rw [hRefinedZero]
      simp
    · have hFractionOne : fraction ≤ 1 := by
        have h :
            fraction * shading.mass ≤ 1 * shading.mass := by
          simpa using hSource
        exact
          (ENNReal.mul_le_mul_iff_left hZero hTop).mp h
      have h :
          refinement.refined.mass * fraction ≤
            refinement.refined.mass * 1 :=
        mul_le_mul_right hFractionOne refinement.refined.mass
      simpa [mul_comm] using h

def identityPaperRefinement
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (logExponent : ℕ)
    (hRetention :
      wz1PaperRefinementFraction delta logExponent *
          shading.mass ≤
        shading.mass) :
    WZ1PaperRefinement shading logExponent where
  selected :=
    { family := fine
      embedding := Equiv.toEmbedding (Equiv.refl (Fin fine.card))
      tube_eq := fun _ => rfl }
  refined := shading
  subshading := fun _ => by simp
  retained_mass := hRetention

def WZ2PaperLiteralLemma3_3Data.to_refined_shading
    {delta rho sigma strongLoss outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {coarse : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    {logExponent : ℕ}
    (data :
      WZ2PaperLiteralLemma3_3Data
        (sigma := sigma)
        (strongLoss := strongLoss)
        (outputLoss := outputLoss)
        shading coarse hrho logExponent) :
    WZ2PaperLiteralLemma3_3Data
      (sigma := sigma)
      (strongLoss := strongLoss)
      (outputLoss := outputLoss)
      data.refinement.refined coarse hrho logExponent :=
  let reindexedRefinement :
      WZ1PaperRefinement data.refinement.refined logExponent :=
    identityPaperRefinement
      data.refinement.refined logExponent
      (paper_refinement_fraction_le_self data.refinement)
  { refinement := reindexedRefinement
    refined_cubical := data.refined_cubical
    refined_nonempty := data.refined_nonempty
    familyData := data.familyData
    literalShading := data.literalShading
    strongLoss_pos := data.strongLoss_pos
    strongLoss_budget := data.strongLoss_budget
    extremal_strong := data.extremal_strong
    extremal := data.extremal
    target_cardinality_lower := data.target_cardinality_lower
    source_cardinality_eq := data.source_cardinality_eq
    source_multiplicity_upper_strong :=
      data.source_multiplicity_upper_strong
    source_cardinality_lower := data.source_cardinality_lower }

theorem wz2_paper_literal_merged_fiber_outputs :
    WZ2PaperLiteralMergedFiberOutputsStatement := by
  intro reindex delta rho sigma strongLoss outputLoss fine coarse cover
    shading hrho logExponent fiberData merged fiberReindex
  have hOutputs :
      ∀ parent : Fin coarse.card,
        Nonempty
          (WZ2PaperLiteralLemma3_3Data
            (sigma := sigma)
            (strongLoss := strongLoss)
            (outputLoss := outputLoss)
            (restrictPaperShading
              (merged.restrictedCover.fullFiberSubfamily parent)
              merged.merged.refinement.refined)
            (coarse.tube parent) hrho logExponent) := by
    intro parent
    let reindexData := fiberReindex parent
    let localData := fiberData parent
    let refinedData := localData.to_refined_shading
    let indexEquiv :
        Fin
            (merged.restrictedCover.fullFiberSubfamily
              parent).family.card ≃
          Fin localData.refinement.selected.family.card :=
      Equiv.ofBijective
        reindexData.localIndex
        reindexData.localIndex_bijective
    exact
      reindex
        (firstShading := localData.refinement.refined)
        (secondShading :=
          restrictPaperShading
            (merged.restrictedCover.fullFiberSubfamily parent)
            merged.merged.refinement.refined)
        (coarse := coarse.tube parent)
        (hrho := hrho)
        (logExponent := logExponent)
        (indexEquiv := indexEquiv)
        (fun index => reindexData.tube_eq index)
        (fun index => reindexData.carrier_eq index)
        refinedData
  let globalFiberData :
      ∀ parent : Fin coarse.card,
        WZ2PaperLiteralLemma3_3Data
          (sigma := sigma)
          (strongLoss := strongLoss)
          (outputLoss := outputLoss)
          (restrictPaperShading
            (merged.restrictedCover.fullFiberSubfamily parent)
            merged.merged.refinement.refined)
          (coarse.tube parent) hrho logExponent :=
    fun parent => (hOutputs parent).some
  exact ⟨{ globalFiberData := globalFiberData }⟩

end Kakeya.Assouad

end
