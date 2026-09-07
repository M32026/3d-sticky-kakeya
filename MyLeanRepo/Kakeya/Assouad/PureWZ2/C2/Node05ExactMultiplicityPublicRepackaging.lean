import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ExactMultiplicityPostRefinement

/-!
# Repackage an exact-multiplicity truncation as public sticky data

The exact-multiplicity truncation changes only the fine shading.  This module
composes the seed selection with its identity-family paper refinement, while
retaining the seed coarse family, cover, and coarse shading definitionally.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Rebuild the public sticky record after a same-family exact-multiplicity
truncation.  Coarse data and multiplicity upper bounds are inherited from the
seed after weakening the loss. -/
noncomputable def PureWZ2ReentrantPropStickyData.repackageExactMultiplicity
    {delta sigma seedLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent seedLogExponent : ℕ}
    (seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading rho normalizationExponent seedLogExponent)
    (hdelta : 0 < delta)
    {m : ℕ}
    (truncation : PureWZ2Node05ExactMultiplicityTruncationData
      seed.data.refined hdelta m)
    (fineExponent : ℕ)
    (refinementScalar :
      2 * wz1PaperRefinementFraction delta fineExponent ≤ 1)
    (loss_le : seedLoss ≤ outputLoss)
    (balanced : PureWZ2BalancedCoverData
      seed.data.cover truncation.truncated
        seed.data.croppedCoarseShading)
    (rescaledFiber :
      ∀ parent : Fin seed.data.coarse.card,
        Nonempty
          (WZ2PaperPureRescaledFullFiberOutput
            (sigma := sigma) (loss := outputLoss)
            (restrictPaperShading
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                seed.data.selected.family
                (wz2PaperFullFiberIndices
                  seed.data.selected.family seed.data.coarse parent))
              truncation.truncated)
            (seed.data.coarse.tube parent)
            seed.data.coarse_extremal.delta_pos)) :
    PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho (seedLogExponent + fineExponent) := by
  let fineRefinement :=
    truncation.toPaperRefinement fineExponent refinementScalar
  let weakened := seed.data.mono_loss loss_le
  have retainedMass :
      wz2PaperPureRefinementFraction delta
            (seedLogExponent + fineExponent) *
          sourceShading.mass ≤
        truncation.truncated.mass := by
    calc
      wz2PaperPureRefinementFraction delta
            (seedLogExponent + fineExponent) * sourceShading.mass =
          wz1PaperRefinementFraction delta fineExponent *
            (wz2PaperPureRefinementFraction delta seedLogExponent *
              sourceShading.mass) := by
        simp only [wz2PaperPureRefinementFraction,
          wz1PaperRefinementFraction, pow_add]
        ring
      _ ≤ wz1PaperRefinementFraction delta fineExponent *
            seed.data.refined.mass := by
        exact mul_le_mul_right seed.data.retained_mass _
      _ ≤ truncation.truncated.mass := fineRefinement.retained_mass
  exact
    { selected := seed.data.selected.comp fineRefinement.selected
      selected_nonempty := seed.data.selected_nonempty
      refined := truncation.truncated
      subshading := fun index =>
        (truncation.subshading index).trans (seed.data.subshading index)
      retained_mass := retainedMass
      refined_cubical := truncation.cubical
      coarse := seed.data.coarse
      cover := seed.data.cover
      croppedCoarseShading := seed.data.croppedCoarseShading
      balanced := balanced
      coarse_extremal := weakened.coarse_extremal
      rescaledFiber := rescaledFiber
      coarse_multiplicity_upper := weakened.coarse_multiplicity_upper
      fiber_multiplicity_upper := by
        intro parent point
        have hsubset :
            (wz2PaperFullFiberIndices
                seed.data.selected.family seed.data.coarse parent).filter
                (fun index => point ∈ truncation.truncated.carrier index) ⊆
              (wz2PaperFullFiberIndices
                seed.data.selected.family seed.data.coarse parent).filter
                (fun index => point ∈ seed.data.refined.carrier index) := by
          intro index hindex
          rw [Finset.mem_filter] at hindex ⊢
          exact ⟨hindex.1, truncation.subshading index hindex.2⟩
        have hcard := Finset.card_le_card hsubset
        exact (by exact_mod_cast hcard :
          (((wz2PaperFullFiberIndices
              seed.data.selected.family seed.data.coarse parent).filter
              fun index => point ∈ truncation.truncated.carrier index).card :
            ENNReal) ≤
          (((wz2PaperFullFiberIndices
              seed.data.selected.family seed.data.coarse parent).filter
              fun index => point ∈ seed.data.refined.carrier index).card :
            ENNReal)).trans
          (weakened.fiber_multiplicity_upper parent point) }

@[simp] theorem PureWZ2ReentrantPropStickyData.repackageExactMultiplicity_selected
    {delta sigma seedLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent seedLogExponent : ℕ}
    (seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading rho normalizationExponent seedLogExponent)
    (hdelta : 0 < delta) {m : ℕ}
    (truncation : PureWZ2Node05ExactMultiplicityTruncationData
      seed.data.refined hdelta m)
    (fineExponent : ℕ)
    (refinementScalar :
      2 * wz1PaperRefinementFraction delta fineExponent ≤ 1)
    (loss_le : seedLoss ≤ outputLoss)
    (balanced : PureWZ2BalancedCoverData
      seed.data.cover truncation.truncated
        seed.data.croppedCoarseShading)
    (rescaledFiber :
      ∀ parent : Fin seed.data.coarse.card,
        Nonempty
          (WZ2PaperPureRescaledFullFiberOutput
            (sigma := sigma) (loss := outputLoss)
            (restrictPaperShading
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                seed.data.selected.family
                (wz2PaperFullFiberIndices
                  seed.data.selected.family seed.data.coarse parent))
              truncation.truncated)
            (seed.data.coarse.tube parent)
            seed.data.coarse_extremal.delta_pos)) :
    (seed.repackageExactMultiplicity hdelta truncation fineExponent
      refinementScalar loss_le balanced rescaledFiber).selected =
        seed.data.selected.comp
          (truncation.toPaperRefinement
            fineExponent refinementScalar).selected := rfl

@[simp] theorem PureWZ2ReentrantPropStickyData.repackageExactMultiplicity_refined
    {delta sigma seedLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent seedLogExponent : ℕ}
    (seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading rho normalizationExponent seedLogExponent)
    (hdelta : 0 < delta) {m : ℕ}
    (truncation : PureWZ2Node05ExactMultiplicityTruncationData
      seed.data.refined hdelta m)
    (fineExponent : ℕ)
    (refinementScalar :
      2 * wz1PaperRefinementFraction delta fineExponent ≤ 1)
    (loss_le : seedLoss ≤ outputLoss)
    (balanced : PureWZ2BalancedCoverData
      seed.data.cover truncation.truncated
        seed.data.croppedCoarseShading)
    (rescaledFiber :
      ∀ parent : Fin seed.data.coarse.card,
        Nonempty
          (WZ2PaperPureRescaledFullFiberOutput
            (sigma := sigma) (loss := outputLoss)
            (restrictPaperShading
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                seed.data.selected.family
                (wz2PaperFullFiberIndices
                  seed.data.selected.family seed.data.coarse parent))
              truncation.truncated)
            (seed.data.coarse.tube parent)
            seed.data.coarse_extremal.delta_pos)) :
    (seed.repackageExactMultiplicity hdelta truncation fineExponent
      refinementScalar loss_le balanced rescaledFiber).refined =
        truncation.truncated := rfl

@[simp] theorem PureWZ2ReentrantPropStickyData.repackageExactMultiplicity_coarse
    {delta sigma seedLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent seedLogExponent : ℕ}
    (seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading rho normalizationExponent seedLogExponent)
    (hdelta : 0 < delta) {m : ℕ}
    (truncation : PureWZ2Node05ExactMultiplicityTruncationData
      seed.data.refined hdelta m)
    (fineExponent : ℕ)
    (refinementScalar :
      2 * wz1PaperRefinementFraction delta fineExponent ≤ 1)
    (loss_le : seedLoss ≤ outputLoss)
    (balanced : PureWZ2BalancedCoverData
      seed.data.cover truncation.truncated
        seed.data.croppedCoarseShading)
    (rescaledFiber :
      ∀ parent : Fin seed.data.coarse.card,
        Nonempty
          (WZ2PaperPureRescaledFullFiberOutput
            (sigma := sigma) (loss := outputLoss)
            (restrictPaperShading
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                seed.data.selected.family
                (wz2PaperFullFiberIndices
                  seed.data.selected.family seed.data.coarse parent))
              truncation.truncated)
            (seed.data.coarse.tube parent)
            seed.data.coarse_extremal.delta_pos)) :
    (seed.repackageExactMultiplicity hdelta truncation fineExponent
      refinementScalar loss_le balanced rescaledFiber).coarse =
        seed.data.coarse := rfl

@[simp] theorem PureWZ2ReentrantPropStickyData.repackageExactMultiplicity_cover
    {delta sigma seedLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent seedLogExponent : ℕ}
    (seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading rho normalizationExponent seedLogExponent)
    (hdelta : 0 < delta) {m : ℕ}
    (truncation : PureWZ2Node05ExactMultiplicityTruncationData
      seed.data.refined hdelta m)
    (fineExponent : ℕ)
    (refinementScalar :
      2 * wz1PaperRefinementFraction delta fineExponent ≤ 1)
    (loss_le : seedLoss ≤ outputLoss)
    (balanced : PureWZ2BalancedCoverData
      seed.data.cover truncation.truncated
        seed.data.croppedCoarseShading)
    (rescaledFiber :
      ∀ parent : Fin seed.data.coarse.card,
        Nonempty
          (WZ2PaperPureRescaledFullFiberOutput
            (sigma := sigma) (loss := outputLoss)
            (restrictPaperShading
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                seed.data.selected.family
                (wz2PaperFullFiberIndices
                  seed.data.selected.family seed.data.coarse parent))
              truncation.truncated)
            (seed.data.coarse.tube parent)
            seed.data.coarse_extremal.delta_pos)) :
    (seed.repackageExactMultiplicity hdelta truncation fineExponent
      refinementScalar loss_le balanced rescaledFiber).cover =
        seed.data.cover := rfl

@[simp] theorem
    PureWZ2ReentrantPropStickyData.repackageExactMultiplicity_croppedCoarseShading
    {delta sigma seedLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent seedLogExponent : ℕ}
    (seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading rho normalizationExponent seedLogExponent)
    (hdelta : 0 < delta) {m : ℕ}
    (truncation : PureWZ2Node05ExactMultiplicityTruncationData
      seed.data.refined hdelta m)
    (fineExponent : ℕ)
    (refinementScalar :
      2 * wz1PaperRefinementFraction delta fineExponent ≤ 1)
    (loss_le : seedLoss ≤ outputLoss)
    (balanced : PureWZ2BalancedCoverData
      seed.data.cover truncation.truncated
        seed.data.croppedCoarseShading)
    (rescaledFiber :
      ∀ parent : Fin seed.data.coarse.card,
        Nonempty
          (WZ2PaperPureRescaledFullFiberOutput
            (sigma := sigma) (loss := outputLoss)
            (restrictPaperShading
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                seed.data.selected.family
                (wz2PaperFullFiberIndices
                  seed.data.selected.family seed.data.coarse parent))
              truncation.truncated)
            (seed.data.coarse.tube parent)
            seed.data.coarse_extremal.delta_pos)) :
    (seed.repackageExactMultiplicity hdelta truncation fineExponent
      refinementScalar loss_le balanced rescaledFiber).croppedCoarseShading =
        seed.data.croppedCoarseShading := rfl

end Kakeya.Assouad

end
