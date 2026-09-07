import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05OwnerReentryCompanion
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05OwnerExactMultiplicity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ExactMultiplicityPublicRepackaging
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ExactMultiplicityExtremality
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05OwnerRescaledFiberRefresh
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05OwnerFullFiberUniformity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedCriticalFloorLocalReduction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCriticalFloorSelection

/-!
# Concrete Node 5 call for the deterministic owner output

This module is the callable boundary from an owner-selected universal input to
the exact-multiplicity Node 5 object.  The fine truncation is the canonical
owner truncation; the coarse refinement is the identity refinement.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private noncomputable def identityPaperRefinement
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) :
    WZ1PaperRefinement shading 0 where
  selected :=
    { family := family
      embedding := Equiv.toEmbedding (Equiv.refl (Fin family.card))
      tube_eq := fun _ => rfl }
  refined := shading
  subshading := fun _ => Set.Subset.rfl
  retained_mass := by
    simp [wz1PaperRefinementFraction]

/-- Turn the deterministic owner output and its exact coarse re-entry receipt
into the reduced exact-multiplicity Node 5 wrapper. -/
noncomputable def pureWZ2Node05OwnerConcretePostRefinement
    {delta sigma sourceLoss normalizationLoss seedLoss outputLoss
      sourceFineLoss structuralBudget : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent seedLogExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (input : PureWZ2CroppedPropStickyUniversalInput
      (outputLoss := seedLoss) normalized callerRequested seedLogExponent)
    (companion : PureWZ2Node05OwnerReentryCompanion input)
    (fineExponent : ℕ)
    (refinementScalar :
      2 * wz1PaperRefinementFraction delta fineExponent ≤ 1)
    (sourceFineExtremal :
      WZ2PaperCroppedIsExtremal sigma sourceFineLoss
        companion.toReentrant.data.selected.family
        input.data.finalFineShading)
    (criticalFloor : PureWZ2CroppedCriticalFloorSelectionData
      sigma outputLoss structuralBudget)
    (seed_le_structural : seedLoss ≤ criticalFloor.structuralLoss)
    (source_le_structural :
      sourceFineLoss ≤ criticalFloor.structuralLoss)
    (structural_le_output : criticalFloor.structuralLoss ≤ outputLoss)
    (absorption :
      2 * Kakeya.realRpowENN delta criticalFloor.structuralLoss ≤
        Kakeya.realRpowENN delta sourceFineLoss)
    (delta_cutoff : delta ≤ criticalFloor.delta₀)
    (rho_cutoff : callerRequested.1 ≤ criticalFloor.delta₀)
    (ratioSmall : delta / callerRequested.1 ≤ 1 / 24)
    (densityAbsorption :
      ∀ parent : Fin input.data.selectedPacked.family.card,
        Kakeya.realRpowENN (delta / callerRequested.1) outputLoss *
              (55296 * Kakeya.deltaTubeVolume 1) ≤
          ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            (((restrictPaperShading
                  (input.data.internalCover.fullFiberSubfamily parent)
                  input.data.finalFineShading).mass / 2) /
              ((input.data.internalCover.fullFiberSubfamily parent).family.enncard *
                Kakeya.realRpowENN delta 2)))
    (ownerUniform :
      ∀ first second : Fin input.data.selectedPacked.family.card,
        ((wz2PaperFullFiberIndices
            input.data.selectedFine.family
            input.data.selectedPacked.family first).card : ENNReal) ≤
          Kakeya.realRpowENN callerRequested.1 (-outputLoss) *
            ((wz2PaperFullFiberIndices
              input.data.selectedFine.family
              input.data.selectedPacked.family second).card : ENNReal)) :
    PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      normalized.croppedRefined callerRequested normalizationExponent
        seedLogExponent (seedLogExponent + fineExponent) := by
  let seed := companion.toReentrant
  let exact := input.data.toExactMultiplicityData
  let rescaledFiber :
      ∀ parent : Fin seed.data.coarse.card,
        Nonempty
          (WZ2PaperPureRescaledFullFiberOutput
            (sigma := sigma) (loss := outputLoss)
            (restrictPaperShading
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                seed.data.selected.family
                (wz2PaperFullFiberIndices seed.data.selected.family
                  seed.data.coarse parent))
              exact.truncation.truncated)
            (seed.data.coarse.tube parent)
            seed.data.coarse_extremal.delta_pos) := by
    intro parent
    let oldOutput :=
      (Classical.choice (seed.data.rescaledFiber parent)).mono_loss
        (seed_le_structural.trans structural_le_output)
    exact ⟨input.data.refreshExactFiberOfOldDensity parent ratioSmall oldOutput
      (densityAbsorption parent)⟩
  let data := seed.repackageExactMultiplicity
    source.extremal.delta_pos exact.truncation fineExponent refinementScalar
    (seed_le_structural.trans structural_le_output)
      exact.truncatedBalanced rescaledFiber
  let coarseRefinement :=
    identityPaperRefinement seed.data.croppedCoarseShading
  have fullFiberUniform := pureWZ2Node05Owner_fullFiberUniformity
    input companion fineExponent refinementScalar ownerUniform
  have fineConclusion :=
    exact.truncation.extremal_and_volume_lower_of_critical_floor
      sourceFineExtremal criticalFloor source_le_structural
      structural_le_output absorption delta_cutoff
  have coarseStructural : WZ2PaperCroppedIsExtremal
      sigma criticalFloor.structuralLoss seed.data.coarse
        seed.data.croppedCoarseShading :=
    seed.data.coarse_extremal.mono_loss seed_le_structural
  have coarseVolumeLower :
      Kakeya.realRpowENN callerRequested.1 (sigma + outputLoss) ≤
        volume seed.data.croppedCoarseShading.union :=
    criticalFloor.volume_floor callerRequested.1 coarseStructural.delta_pos
      rho_cutoff seed.data.coarse coarseStructural.nonempty
      seed.data.croppedCoarseShading coarseStructural.cwa_nearby_scales
      coarseStructural.cubical coarseStructural.dense
  exact
    { seed := seed
      post :=
        { fineRefinementExponent := fineExponent
          coarseRefinementExponent := 0
          coarseRefinement := coarseRefinement
          data := data
          refined_extremal := fineConclusion.1
          exactMultiplicity := exact.m
          exactMultiplicity_pos := exact.m_pos
          delta_pos := source.extremal.delta_pos
          truncation := exact.truncation
          refinementScalar := refinementScalar
          logExponent_eq := rfl
          selected_eq := rfl
          refined_eq := HEq.rfl
          coarse_eq := rfl
          croppedCoarseShading_eq := HEq.rfl
          fineCellNested := exact.node5Balanced.fine_cell_nested
          refined_volume_lower := fineConclusion.2
          full_fiber_uniform := fullFiberUniform
          coarse_volume_lower := coarseVolumeLower } }

/-- Owner exactification with both volume floors routed through the exact
root/coarse re-entry traces and Node 2's ordinary critical floor.  The fine
and coarse public objects are unchanged; only the source of their lower-volume
certificates differs from `pureWZ2Node05OwnerConcretePostRefinement`. -/
noncomputable def pureWZ2Node05OwnerConcretePostRefinementOfReentryTrace
    {delta sigma sourceLoss normalizationLoss seedLoss outputLoss
      sourceFineLoss fineDensityLoss coarseDensityLoss
      fineStructuralBudget coarseStructuralBudget : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent seedLogExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (input : PureWZ2CroppedPropStickyUniversalInput
      (outputLoss := seedLoss) normalized callerRequested seedLogExponent)
    (companion : PureWZ2Node05OwnerReentryCompanion input)
    (fineExponent : ℕ)
    (refinementScalar :
      2 * wz1PaperRefinementFraction delta fineExponent ≤ 1)
    (sourceFineExtremal :
      WZ2PaperCroppedIsExtremal sigma sourceFineLoss
        companion.toReentrant.data.selected.family
        input.data.finalFineShading)
    (fineFloor : PureWZ2CriticalFloorSelectionData
      sigma outputLoss fineStructuralBudget)
    (coarseFloor : PureWZ2CriticalFloorSelectionData
      sigma outputLoss coarseStructuralBudget)
    (fineLossConstant coarseLossConstant : ENNReal)
    (fineLossConstantOne : 1 ≤ fineLossConstant)
    (fineLossConstantTop : fineLossConstant ≠ ⊤)
    (coarseLossConstantOne : 1 ≤ coarseLossConstant)
    (coarseLossConstantTop : coarseLossConstant ≠ ⊤)
    (seed_le_coarseDensity : seedLoss ≤ coarseDensityLoss)
    (coarseDensity_le_output : coarseDensityLoss ≤ outputLoss)
    (sourceFine_le_density : sourceFineLoss ≤ fineDensityLoss)
    (fineDensity_le_output : fineDensityLoss ≤ outputLoss)
    (fineExtremalAbsorption :
      2 * Kakeya.realRpowENN delta fineDensityLoss ≤
        Kakeya.realRpowENN delta sourceFineLoss)
    (fineTraceAbsorption : fineLossConstant⁻¹ ≤
      (100 : ENNReal)⁻¹ *
        (Kakeya.realRpowENN delta sourceLoss / 2))
    (fineCWAAbsorption :
      fineLossConstant * Kakeya.realRpowENN delta (-fineDensityLoss) ≤
        Kakeya.realRpowENN delta (-fineFloor.structuralLoss))
    (fineDensityAbsorption :
      Kakeya.realRpowENN delta fineFloor.structuralLoss ≤
        fineLossConstant⁻¹ * Kakeya.realRpowENN delta fineDensityLoss)
    (fineCutoff : delta ≤ fineFloor.delta₀)
    (deltaSmall : delta ≤ 1 / 12)
    (coarseTraceAbsorption : coarseLossConstant⁻¹ ≤
      (100 : ENNReal)⁻¹ *
        (Kakeya.realRpowENN callerRequested.1
          companion.toReentrant.coarseSourceLoss / 2))
    (coarseCWAAbsorption :
      coarseLossConstant *
          Kakeya.realRpowENN callerRequested.1 (-coarseDensityLoss) ≤
        Kakeya.realRpowENN callerRequested.1
          (-coarseFloor.structuralLoss))
    (coarseDensityAbsorption :
      Kakeya.realRpowENN callerRequested.1
          coarseFloor.structuralLoss ≤
        coarseLossConstant⁻¹ *
          Kakeya.realRpowENN callerRequested.1 coarseDensityLoss)
    (coarseCutoff : callerRequested.1 ≤ coarseFloor.delta₀)
    (coarseSmall : callerRequested.1 ≤ 1 / 12)
    (ratioSmall : delta / callerRequested.1 ≤ 1 / 24)
    (densityAbsorption :
      ∀ parent : Fin input.data.selectedPacked.family.card,
        Kakeya.realRpowENN (delta / callerRequested.1) outputLoss *
              (55296 * Kakeya.deltaTubeVolume 1) ≤
          ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            (((restrictPaperShading
                  (input.data.internalCover.fullFiberSubfamily parent)
                  input.data.finalFineShading).mass / 2) /
              ((input.data.internalCover.fullFiberSubfamily parent).family.enncard *
                Kakeya.realRpowENN delta 2)))
    (ownerUniform :
      ∀ first second : Fin input.data.selectedPacked.family.card,
        ((wz2PaperFullFiberIndices
            input.data.selectedFine.family
            input.data.selectedPacked.family first).card : ENNReal) ≤
          Kakeya.realRpowENN callerRequested.1 (-outputLoss) *
            ((wz2PaperFullFiberIndices
              input.data.selectedFine.family
              input.data.selectedPacked.family second).card : ENNReal)) :
    PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      normalized.croppedRefined callerRequested normalizationExponent
        seedLogExponent (seedLogExponent + fineExponent) := by
  let seed := companion.toReentrant
  let exact := input.data.toExactMultiplicityData
  have fineAtDensity : WZ2PaperCroppedIsExtremal sigma fineDensityLoss
      seed.data.selected.family exact.truncation.truncated :=
    exact.truncation.extremal_of_loss_absorption sourceFineExtremal
      sourceFine_le_density fineExtremalAbsorption
  have fineConclusion : WZ2PaperCroppedIsExtremal sigma outputLoss
      seed.data.selected.family exact.truncation.truncated :=
    fineAtDensity.mono_loss fineDensity_le_output
  have fineSubset : ∀ index, exact.truncation.truncated.carrier index ⊆
      normalized.croppedRefined.carrier
        (seed.data.selected.embedding index) := by
    intro index point hpoint
    exact seed.data.subshading index
      (exact.truncation.subshading index hpoint)
  have fineVolumeLower :
      Kakeya.realRpowENN delta (sigma + outputLoss) ≤
        volume exact.truncation.truncated.union :=
    normalized.volume_lower_of_trace_and_pure_floor seed.data.selected
      exact.truncation.truncated seed.data.selected_nonempty
      exact.truncation.cubical fineSubset
      (Kakeya.realRpowENN delta sourceLoss / 2)
      fineLossConstant
      (fun index => normalized.framed_ordinary_per_tube
        seed.data.selected index)
      fineFloor fineLossConstantOne fineLossConstantTop
      fineTraceAbsorption fineAtDensity.cwa_nearby_scales
      fineAtDensity.dense fineCWAAbsorption fineDensityAbsorption
      deltaSmall fineCutoff
  have seed_le_output : seedLoss ≤ outputLoss :=
    seed_le_coarseDensity.trans coarseDensity_le_output
  let rescaledFiber :
      ∀ parent : Fin seed.data.coarse.card,
        Nonempty
          (WZ2PaperPureRescaledFullFiberOutput
            (sigma := sigma) (loss := outputLoss)
            (restrictPaperShading
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                seed.data.selected.family
                (wz2PaperFullFiberIndices seed.data.selected.family
                  seed.data.coarse parent))
              exact.truncation.truncated)
            (seed.data.coarse.tube parent)
            seed.data.coarse_extremal.delta_pos) := by
    intro parent
    let oldOutput :=
      (Classical.choice (seed.data.rescaledFiber parent)).mono_loss
        seed_le_output
    exact ⟨input.data.refreshExactFiberOfOldDensity parent ratioSmall oldOutput
      (densityAbsorption parent)⟩
  let data := seed.repackageExactMultiplicity
    source.extremal.delta_pos exact.truncation fineExponent refinementScalar
    seed_le_output exact.truncatedBalanced rescaledFiber
  let coarseRefinement :=
    identityPaperRefinement seed.data.croppedCoarseShading
  have fullFiberUniform := pureWZ2Node05Owner_fullFiberUniformity
    input companion fineExponent refinementScalar ownerUniform
  let coarseNormalized := seed.coarseReentry.toNormalizationData
  let coarseSelected : Kakeya.Streamlined.TubeSubfamily seed.data.coarse :=
    { family := seed.data.coarse
      embedding := Function.Embedding.refl _
      tube_eq := fun _ => rfl }
  have coarseAtDensity :=
    seed.data.coarse_extremal.mono_loss seed_le_coarseDensity
  have coarseFinal := coarseAtDensity.mono_loss coarseDensity_le_output
  have coarseVolumeLower :
      Kakeya.realRpowENN callerRequested.1 (sigma + outputLoss) ≤
        volume seed.data.croppedCoarseShading.union :=
    coarseNormalized.volume_lower_of_trace_and_pure_floor coarseSelected
      seed.data.croppedCoarseShading coarseFinal.nonempty coarseFinal.cubical
      (fun _ => Set.Subset.rfl)
      (Kakeya.realRpowENN callerRequested.1 seed.coarseSourceLoss / 2)
      coarseLossConstant
      (fun index => by
        exact coarseNormalized.framed_ordinary_per_tube coarseSelected index)
      coarseFloor coarseLossConstantOne coarseLossConstantTop
      coarseTraceAbsorption coarseAtDensity.cwa_nearby_scales
      coarseAtDensity.dense
      coarseCWAAbsorption coarseDensityAbsorption coarseSmall coarseCutoff
  exact
    { seed := seed
      post :=
        { fineRefinementExponent := fineExponent
          coarseRefinementExponent := 0
          coarseRefinement := coarseRefinement
          data := data
          refined_extremal := fineConclusion
          exactMultiplicity := exact.m
          exactMultiplicity_pos := exact.m_pos
          delta_pos := source.extremal.delta_pos
          truncation := exact.truncation
          refinementScalar := refinementScalar
          logExponent_eq := rfl
          selected_eq := rfl
          refined_eq := HEq.rfl
          coarse_eq := rfl
          croppedCoarseShading_eq := HEq.rfl
          fineCellNested := exact.node5Balanced.fine_cell_nested
          refined_volume_lower := fineVolumeLower
          full_fiber_uniform := fullFiberUniform
          coarse_volume_lower := coarseVolumeLower } }

/-- Direct callable owner constructor for the public Node 5 data. -/
noncomputable def pureWZ2Node05OwnerConcreteCall
    {delta sigma sourceLoss normalizationLoss seedLoss outputLoss
      sourceFineLoss structuralBudget : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent seedLogExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (input : PureWZ2CroppedPropStickyUniversalInput
      (outputLoss := seedLoss) normalized callerRequested seedLogExponent)
    (companion : PureWZ2Node05OwnerReentryCompanion input)
    (fineExponent : ℕ)
    (refinementScalar :
      2 * wz1PaperRefinementFraction delta fineExponent ≤ 1)
    (sourceFineExtremal :
      WZ2PaperCroppedIsExtremal sigma sourceFineLoss
        companion.toReentrant.data.selected.family
        input.data.finalFineShading)
    (criticalFloor : PureWZ2CroppedCriticalFloorSelectionData
      sigma outputLoss structuralBudget)
    (seed_le_structural : seedLoss ≤ criticalFloor.structuralLoss)
    (source_le_structural :
      sourceFineLoss ≤ criticalFloor.structuralLoss)
    (structural_le_output : criticalFloor.structuralLoss ≤ outputLoss)
    (absorption :
      2 * Kakeya.realRpowENN delta criticalFloor.structuralLoss ≤
        Kakeya.realRpowENN delta sourceFineLoss)
    (delta_cutoff : delta ≤ criticalFloor.delta₀)
    (rho_cutoff : callerRequested.1 ≤ criticalFloor.delta₀)
    (ratioSmall : delta / callerRequested.1 ≤ 1 / 24)
    (densityAbsorption :
      ∀ parent : Fin input.data.selectedPacked.family.card,
        Kakeya.realRpowENN (delta / callerRequested.1) outputLoss *
              (55296 * Kakeya.deltaTubeVolume 1) ≤
          ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            (((restrictPaperShading
                  (input.data.internalCover.fullFiberSubfamily parent)
                  input.data.finalFineShading).mass / 2) /
              ((input.data.internalCover.fullFiberSubfamily parent).family.enncard *
                Kakeya.realRpowENN delta 2)))
    (ownerUniform :
      ∀ first second : Fin input.data.selectedPacked.family.card,
        ((wz2PaperFullFiberIndices
            input.data.selectedFine.family
            input.data.selectedPacked.family first).card : ENNReal) ≤
          Kakeya.realRpowENN callerRequested.1 (-outputLoss) *
            ((wz2PaperFullFiberIndices
              input.data.selectedFine.family
              input.data.selectedPacked.family second).card : ENNReal)) :
    PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := outputLoss)
      normalized.croppedRefined callerRequested
        (seedLogExponent + fineExponent) :=
  (pureWZ2Node05OwnerConcretePostRefinement input companion fineExponent
    refinementScalar sourceFineExtremal criticalFloor seed_le_structural
    source_le_structural structural_le_output absorption delta_cutoff
    rho_cutoff ratioSmall densityAbsorption ownerUniform).toNode5StickyData

end Kakeya.Assouad

end
