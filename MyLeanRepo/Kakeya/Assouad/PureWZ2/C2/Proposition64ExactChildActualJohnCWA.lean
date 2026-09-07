import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.AffineTubeHomotheticEnvelope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64CenteredActualJohnPacketCWA

/-!
# Exact-child actual-John CWA for Proposition 6.4

The physical map is the single combined Proposition-6.4 affine map.  Each
source child is compared with its exact transported target child through axis
provenance and an ordinary-carrier envelope; no parent-midpoint translation or
unit-segment half-length is introduced.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- Transport one target-indexed packet of a complete source actual-John fibre
through the exact childwise Proposition-6.4 map. -/
theorem pureWZ2Proposition64_exactChildIndexedPacket_cwa
    {sourceDelta sourceRho targetDelta targetRho
      halfHeight normalization scale factor : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {targetCoarse : Kakeya.Streamlined.TubeFamily targetRho}
    (sourceParent : Fin sourceCoarse.card)
    {sourceConstant : ENNReal}
    (sourceFiber : WZ2PaperPureUnitRescaledFullFiberData
      (fine := sourceFine) (coarse := sourceCoarse)
      sourceParent sourceConstant)
    (targetParent : Fin targetCoarse.card)
    (targetJohn : WZ2PaperAssouadUnitRescalingData
      (targetCoarse.tube targetParent))
    (targetBodies : Kakeya.Streamlined.BodyFamily)
    (sourceIndex : Fin targetBodies.card → Fin sourceFine.card)
    (sourceIndex_injective : Function.Injective sourceIndex)
    (source_mem : ∀ index, sourceIndex index ∈
      wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent)
    (targetIndex : Fin targetBodies.card → Fin targetFine.card)
    (target_mem : ∀ index, targetIndex index ∈
      wz2PaperOrdinaryFullFiberIndices
        targetFine targetCoarse targetParent)
    (target_carrier : ∀ index,
      (targetBodies.body index).carrier =
        targetJohn.map '' (targetFine.tube (targetIndex index)).carrier)
    (weight retentionConstant : ENNReal)
    (weight_ne_zero : weight ≠ 0)
    (weight_ne_top : weight ≠ ⊤)
    (cardinality_retention :
      weight *
          ((wz2PaperOrdinaryFullFiberIndices
            sourceFine sourceCoarse sourceParent).card : ENNReal) ≤
        retentionConstant * targetBodies.enncard)
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    (translation isotropicCenter : Point3)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceDeltaOne : sourceDelta ≤ 1)
    (htargetDelta : 0 < targetDelta)
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 1 ≤ normalization)
    (hscale : 0 < scale)
    (htranslationHeight : translation 2 = 0)
    (hslabCenter : |slabCenter| ≤ 1)
    (hisotropicCenter : |isotropicCenter 2| ≤ 1)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hsourceBase : ∀ index,
      ‖(sourceFine.tube (sourceIndex index)).base‖ ≤ 4)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (htargetLine : WZ1PaperIsLineClass targetFine)
    (htargetCentered : ∀ index,
      wz2PaperTubeMidpoint (targetFine.tube index) =
        wz1TubeAxisZeroPoint (targetFine.tube index))
    (haxis : ∀ index,
      tubeAxisLine (targetFine.tube (targetIndex index)) =
        pureWZ2Proposition64IsotropicMap isotropicCenter scale ''
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation ''
              tubeAxisLine (sourceFine.tube (sourceIndex index))))
    (hfactorOne : 1 ≤ factor)
    (hfactorAxial : 40 * scale / halfHeight ≤ factor)
    (hfactorTransverse :
      20 * scale * sourceDelta ≤ factor * targetDelta)
    (inverseVolumeConstant : ENNReal)
    (inverse_volume_bound :
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
    WZ2PaperBodyConvexWolffBound targetBodies
      ((inverseVolumeConstant *
          ENNReal.ofReal (27 * (2 * factor - 1) ^ 3)) *
        ((weight⁻¹ * retentionConstant) * sourceConstant)) := by
  let physical := pureWZ2Proposition64CombinedAffineEquiv
    g slabCenter anchorHeight halfHeight normalization translation
      isotropicCenter scale hhalfHeight
      (lt_of_lt_of_le zero_lt_one hnormalization) hscale
  let coordinateChange :=
    sourceFiber.normalization.map.symm.trans (physical.trans targetJohn.map)
  let center : Fin targetBodies.card → Point3 := fun index =>
    targetJohn.map (wz2PaperTubeMidpoint
      (targetFine.tube (targetIndex index)))
  apply pureWZ2Proposition64_actualJohnPacket_cwa
    sourceParent sourceFiber targetBodies sourceIndex sourceIndex_injective
    source_mem weight retentionConstant weight_ne_zero weight_ne_top
    cardinality_retention coordinateChange factor hfactorOne
    (center := center) (inverseVolumeConstant := inverseVolumeConstant)
  · intro index
    rw [target_carrier index]
    exact pureWZ2_actualJohn_tube_image_isConvexBody targetJohn
      htargetDelta _
  · intro index
    rw [target_carrier index]
    exact pureWZ2_actualJohn_child_image_subset_unitBall targetJohn
      ((mem_wz2PaperOrdinaryFullFiberIndices_iff targetParent
        (targetIndex index)).mp (target_mem index))
  · intro index
    rw [target_carrier index]
    exact pureWZ2_actualJohn_child_midpoint_mem targetJohn htargetDelta.le
  · intro index
    change Fin targetBodies.card at index
    let sourceChild := sourceFine.tube (sourceIndex index)
    let targetChild := targetFine.tube (targetIndex index)
    have hphysical :=
      pureWZ2Proposition64_combined_ordinaryCarrier_subset_homothety
        hsourceDelta hsourceDeltaOne htargetDelta g slabCenter anchorHeight
        translation isotropicCenter htranslationHeight hslabCenter
        hisotropicCenter hhalfHeight hhalfHeightOne hnormalization
        hanchorSlope hscale sourceChild targetChild (hsourceBase index)
        (hsourceLine (sourceIndex index)) (htargetLine (targetIndex index))
        (htargetCentered (targetIndex index)) (haxis index)
        hfactorOne hfactorAxial hfactorTransverse
    have hsourceBody :
        ((pureWZ2Proposition64ActualJohnSourcePacket
          sourceParent sourceFiber.normalization targetBodies
            sourceIndex source_mem).body index).carrier =
          sourceFiber.normalization.map '' sourceChild.carrier := by
      change sourceFiber.normalization.map ''
          (sourceFine.tube
            ((wz2PaperOrdinaryFullFiberIndexEquiv sourceParent)
              ((wz2PaperOrdinaryFullFiberIndexEquiv sourceParent).symm
                ⟨sourceIndex index, source_mem index⟩)).1).carrier =
        sourceFiber.normalization.map '' sourceChild.carrier
      have hindex :
          ((wz2PaperOrdinaryFullFiberIndexEquiv sourceParent)
            ((wz2PaperOrdinaryFullFiberIndexEquiv sourceParent).symm
              ⟨sourceIndex index, source_mem index⟩)).1 =
            sourceIndex index :=
        congrArg Subtype.val
          ((wz2PaperOrdinaryFullFiberIndexEquiv sourceParent).apply_symm_apply
            ⟨sourceIndex index, source_mem index⟩)
      rw [hindex]
    rw [hsourceBody, target_carrier index]
    rintro point ⟨sourceJohnPoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
    have hphysicalPoint : physical sourcePoint ∈
        AffineMap.homothety (wz2PaperTubeMidpoint targetChild) factor ''
          targetChild.carrier := by
      apply hphysical
      refine ⟨pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation sourcePoint,
        ⟨sourcePoint, hsourcePoint, rfl⟩, ?_⟩
      simp [physical, pureWZ2Proposition64CombinedAffineEquiv,
        AffineEquiv.trans_apply]
    rcases hphysicalPoint with ⟨targetPoint, htargetPoint, htargetEq⟩
    refine ⟨targetJohn.map targetPoint, ⟨targetPoint, htargetPoint, rfl⟩, ?_⟩
    symm
    simp only [coordinateChange, center, AffineEquiv.trans_apply]
    rw [sourceFiber.normalization.map.symm_apply_apply]
    change targetJohn.map (physical sourcePoint) =
      AffineMap.homothety
        (targetJohn.map (wz2PaperTubeMidpoint targetChild)) factor
          (targetJohn.map targetPoint)
    rw [← htargetEq]
    simpa [AffineMap.homothety_apply, AffineMap.lineMap_apply] using
      (targetJohn.map.apply_lineMap
        (wz2PaperTubeMidpoint targetChild) targetPoint factor)
  · intro targetSet
    rw [wz2PaperAffineEquiv_volume_image_eq]
    gcongr

end Kakeya.Assouad

end
