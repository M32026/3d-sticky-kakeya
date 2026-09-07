import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64ExactChildActualJohnCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64OwnerPairCardinality
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BodyCWAFiberwiseAssembly

/-!
# Exact-child owner-block actual-John assembly

This is the local-fanout owner decomposition used by Proposition 6.4, with
the parent-midpoint geometric kernel replaced by the exact childwise
Proposition-6.4 affine envelope.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem
    pureWZ2Proposition64_actualJohnFiber_cwa_of_exactChildOwnerBlocks
    {sourceDelta sourceRho targetDelta targetRho
      halfHeight normalization scale factor : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {targetCoarse : Kakeya.Streamlined.TubeFamily targetRho}
    {sourceConstant weight retentionConstant pairConstant
      targetMultiplicity inverseVolumeConstant : ENNReal}
    (sourceScale : WZ2PaperPureScaleCoverData
      sourceFine sourceRho sourceConstant)
    (sourceParentCountPos : 0 < sourceScale.coarse.card)
    (targetCover : WZ2PaperPurePartitioningCover targetFine targetCoarse)
    (sourceIndex : Fin targetFine.card → Fin sourceFine.card)
    (sourceIndex_injective : Function.Injective sourceIndex)
    (sourceOwner : Fin targetFine.card → Fin sourceScale.coarse.card)
    (targetParent : Fin targetCoarse.card)
    (source_mem : ∀ index, sourceIndex
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1 ∈
      wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceScale.coarse
          (sourceOwner
            ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1))
    (weight_ne_zero : weight ≠ 0)
    (weight_ne_top : weight ≠ ⊤)
    (globalRetention :
      weight * sourceFine.enncard ≤
        retentionConstant * targetFine.enncard)
    (pairUniform :
      ∀ first second :
          Fin targetCoarse.card × Fin sourceScale.coarse.card,
        0 < pureWZ2Proposition64OwnerPairCount
            targetCover sourceOwner first →
        0 < pureWZ2Proposition64OwnerPairCount
            targetCover sourceOwner second →
        pureWZ2Proposition64OwnerPairCount
            targetCover sourceOwner first ≤
          pairConstant *
            pureWZ2Proposition64OwnerPairCount
              targetCover sourceOwner second)
    (localFanout : ∀ sourceParent : Fin sourceScale.coarse.card,
      (((Finset.univ : Finset (Fin targetCoarse.card)).filter fun targetParent =>
          0 < pureWZ2Proposition64OwnerPairCount targetCover sourceOwner
            (targetParent, sourceParent)).card : ENNReal) ≤
        targetMultiplicity)
    (targetJohn : WZ2PaperAssouadUnitRescalingData
      (targetCoarse.tube targetParent))
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    (translation isotropicCenter : Point3)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceDeltaOne : sourceDelta ≤ 1)
    (htargetDelta : 0 < targetDelta)
    (htargetRho : 0 ≤ targetRho)
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 1 ≤ normalization)
    (hscale : 0 < scale)
    (htranslationHeight : translation 2 = 0)
    (hslabCenter : |slabCenter| ≤ 1)
    (hisotropicCenter : |isotropicCenter 2| ≤ 1)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hsourceBase : ∀ index, ‖(sourceFine.tube index).base‖ ≤ 4)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (htargetLine : WZ1PaperIsLineClass targetFine)
    (htargetCentered : ∀ index,
      wz2PaperTubeMidpoint (targetFine.tube index) =
        wz1TubeAxisZeroPoint (targetFine.tube index))
    (haxis : ∀ index,
      tubeAxisLine (targetFine.tube index) =
        pureWZ2Proposition64IsotropicMap isotropicCenter scale ''
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation ''
              tubeAxisLine (sourceFine.tube (sourceIndex index))))
    (hfactorOne : 1 ≤ factor)
    (hfactorAxial : 40 * scale / halfHeight ≤ factor)
    (hfactorTransverse :
      20 * scale * sourceDelta ≤ factor * targetDelta)
    (inverse_volume_bound : ∀ owner,
      let sourceFiber := Classical.choice
        (sourceScale.rescaledFiber owner)
      ENNReal.ofReal
          |LinearMap.det
            ((sourceFiber.normalization.map.symm.trans
              ((pureWZ2Proposition64CombinedAffineEquiv
                g slabCenter anchorHeight halfHeight normalization translation
                isotropicCenter scale hhalfHeight
                (lt_of_lt_of_le zero_lt_one hnormalization) hscale).trans
                  targetJohn.map)).symm.linear :
                    Point3 →ₗ[ℝ] Point3)| ≤
        inverseVolumeConstant) :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := targetFine) (coarse := targetCoarse)
        targetParent targetJohn)
      ((inverseVolumeConstant *
          ENNReal.ofReal (27 * (2 * factor - 1) ^ 3)) *
        ((weight⁻¹ *
          (sourceConstant * retentionConstant * targetMultiplicity *
            pairConstant)) * sourceConstant)) := by
  let targetBodies := wz2PaperPureUnitRescaledFullFiberBodyFamily
    (fine := targetFine) (coarse := targetCoarse) targetParent targetJohn
  have blockCardinality : ∀ owner,
      0 <
          (wz2PaperBodyParentFiber targetBodies
            (fun index => sourceOwner
              ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1)
            owner).card →
        weight *
            ((wz2PaperOrdinaryFullFiberIndices
              sourceFine sourceScale.coarse owner).card : ENNReal) ≤
          (sourceConstant * retentionConstant * targetMultiplicity *
            pairConstant) *
            (wz2PaperBodyParentFiber targetBodies
              (fun index => sourceOwner
                ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1)
              owner).enncard := by
    intro owner hblock
    have hblockENN :
        (0 : ENNReal) <
          (wz2PaperBodyParentFiber targetBodies
            (fun index => sourceOwner
              ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1)
            owner).enncard := by
      change (0 : ENNReal) <
        ((wz2PaperBodyParentFiber targetBodies
          (fun index => sourceOwner
            ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1)
          owner).card : ENNReal)
      exact_mod_cast hblock
    have hpairPositive :
        0 < pureWZ2Proposition64OwnerPairCount
          targetCover sourceOwner (targetParent, owner) := by
      rw [pureWZ2Proposition64_ownerPairCount_eq_bodyParentFiber_enncard
        targetCover htargetRho sourceOwner targetParent targetJohn owner]
      exact hblockENN
    have hratio :
        weight *
            ((wz2PaperOrdinaryFullFiberIndices
              sourceFine sourceScale.coarse owner).card : ENNReal) ≤
          (sourceConstant * retentionConstant * targetMultiplicity *
            pairConstant) *
            pureWZ2Proposition64OwnerPairCount
              targetCover sourceOwner (targetParent, owner) :=
      pureWZ2Proposition64_sourceFiberCount_le_ownerPairCount_of_localFanout
        (sourceDelta := sourceDelta) (sourceRho := sourceRho)
        (targetDelta := targetDelta) (targetRho := targetRho)
        (sourceFine := sourceFine) (targetFine := targetFine)
        (targetCoarse := targetCoarse) (sourceConstant := sourceConstant)
        (weight := weight) (retentionConstant := retentionConstant)
        (pairConstant := pairConstant)
        (targetMultiplicity := targetMultiplicity)
        sourceScale sourceParentCountPos targetCover sourceOwner
        globalRetention pairUniform (fun sourceParent => by
          convert localFanout sourceParent using 1) targetParent owner
            hpairPositive
    rw [pureWZ2Proposition64_ownerPairCount_eq_bodyParentFiber_enncard
      targetCover htargetRho sourceOwner targetParent targetJohn owner]
      at hratio
    exact hratio
  apply wz2PaperBodyConvexWolffBound_of_parent_fibers
    sourceParentCountPos
    (fun index => sourceOwner
      ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1)
  intro owner
  let block := wz2PaperBodyParentFiber targetBodies
    (fun index => sourceOwner
      ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1) owner
  by_cases hblockZero : block.card = 0
  · intro convexSet _hconvex
    have hcontainedCard : (block.containedIndices convexSet).card = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpositive
      rcases Finset.card_pos.mp hpositive with ⟨index, _hindex⟩
      exact Fin.elim0 (hblockZero ▸ index)
    unfold Kakeya.Streamlined.BodyFamily.containedCount
    rw [hcontainedCard]
    simp
  · have hblockPos : 0 < block.card := Nat.pos_of_ne_zero hblockZero
    let blockIndices := (Finset.univ :
      Finset (Fin targetBodies.card)).filter fun index =>
        sourceOwner
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1 = owner
    let blockEmbedding : Fin block.card ↪ Fin targetBodies.card :=
      (blockIndices.orderEmbOfFin rfl).toEmbedding
    let targetFiberEquiv := wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := targetFine) (coarse := targetCoarse) targetParent
    let blockTargetIndex : Fin block.card → Fin targetFine.card := fun index =>
      (targetFiberEquiv (blockEmbedding index)).1
    let blockSourceIndex : Fin block.card → Fin sourceFine.card := fun index =>
      sourceIndex (blockTargetIndex index)
    have hblockSourceInjective : Function.Injective blockSourceIndex := by
      intro first second equality
      apply blockEmbedding.injective
      apply targetFiberEquiv.injective
      apply Subtype.ext
      exact sourceIndex_injective equality
    have hblockSourceMem : ∀ index, blockSourceIndex index ∈
        wz2PaperOrdinaryFullFiberIndices
          sourceFine sourceScale.coarse owner := by
      intro index
      have howner : sourceOwner (blockEmbedding index |> targetFiberEquiv) = owner :=
        (Finset.mem_filter.mp
          (Finset.orderEmbOfFin_mem blockIndices rfl index)).2
      rw [← howner]
      exact source_mem (blockEmbedding index)
    have hblockTargetMem : ∀ index, blockTargetIndex index ∈
        wz2PaperOrdinaryFullFiberIndices
          targetFine targetCoarse targetParent := by
      intro index
      exact (targetFiberEquiv (blockEmbedding index)).2
    have hblockCarrier : ∀ index,
        (block.body index).carrier =
          targetJohn.map '' (targetFine.tube (blockTargetIndex index)).carrier := by
      intro index
      rfl
    let sourceFiber := Classical.choice (sourceScale.rescaledFiber owner)
    exact pureWZ2Proposition64_exactChildIndexedPacket_cwa
      owner sourceFiber targetParent targetJohn block blockSourceIndex
      hblockSourceInjective hblockSourceMem blockTargetIndex hblockTargetMem
      hblockCarrier weight
      (sourceConstant * retentionConstant * targetMultiplicity * pairConstant)
      weight_ne_zero weight_ne_top (blockCardinality owner hblockPos)
      g slabCenter anchorHeight translation isotropicCenter hsourceDelta
      hsourceDeltaOne htargetDelta hhalfHeight hhalfHeightOne hnormalization
      hscale htranslationHeight hslabCenter hisotropicCenter hanchorSlope
      (fun index => hsourceBase (blockSourceIndex index))
      hsourceLine htargetLine htargetCentered
      (fun index => haxis (blockTargetIndex index))
      hfactorOne hfactorAxial hfactorTransverse inverseVolumeConstant
      (inverse_volume_bound owner)

end Kakeya.Assouad

end
