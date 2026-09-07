import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.AffineTubeHomotheticEnvelope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64ActualJohnPacketCWA

/-!
# Parent-centered actual-John packet transport

For one synchronized source-parent/target-parent pair, translate the full
Proposition-6.4 physical image so that the source-parent midpoint lands on the
target-parent midpoint.  This packet-dependent translation has unit Jacobian.
It removes any dependence on the arbitrary axial bases of the ordinary parent
representatives while retaining one common affine chart on the whole packet.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- The physical post-translation which aligns the two parent midpoints. -/
def pureWZ2Proposition64ParentCenteringShift
    {sourceRho targetRho : ℝ}
    (sourceParent : Kakeya.DeltaTube sourceRho)
    (targetParent : Kakeya.DeltaTube targetRho)
    (physical : Point3 ≃ᵃ[ℝ] Point3) : Point3 :=
  wz2PaperTubeMidpoint targetParent -
    physical (wz2PaperTubeMidpoint sourceParent)

/-- The parent-centered physical coordinate change. -/
noncomputable def pureWZ2Proposition64ParentCenteredPhysicalEquiv
    {sourceRho targetRho : ℝ}
    (sourceParent : Kakeya.DeltaTube sourceRho)
    (targetParent : Kakeya.DeltaTube targetRho)
    (physical : Point3 ≃ᵃ[ℝ] Point3) : Point3 ≃ᵃ[ℝ] Point3 :=
  physical.trans
    (AffineEquiv.constVAdd ℝ Point3
      (pureWZ2Proposition64ParentCenteringShift
        sourceParent targetParent physical))

@[simp] theorem pureWZ2Proposition64ParentCenteredPhysicalEquiv_apply
    {sourceRho targetRho : ℝ}
    (sourceParent : Kakeya.DeltaTube sourceRho)
    (targetParent : Kakeya.DeltaTube targetRho)
    (physical : Point3 ≃ᵃ[ℝ] Point3) (point : Point3) :
    pureWZ2Proposition64ParentCenteredPhysicalEquiv
        sourceParent targetParent physical point =
      physical point +
        pureWZ2Proposition64ParentCenteringShift
          sourceParent targetParent physical := by
  simp [pureWZ2Proposition64ParentCenteredPhysicalEquiv,
    AffineEquiv.trans_apply, add_comm]

/-- The parent-centered physical map conjugated by the two actual outer-John
charts. -/
noncomputable def pureWZ2Proposition64ParentCenteredActualJohnChange
    {sourceRho targetRho : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (physical : Point3 ≃ᵃ[ℝ] Point3) : Point3 ≃ᵃ[ℝ] Point3 :=
  sourceJohn.map.symm.trans
    ((pureWZ2Proposition64ParentCenteredPhysicalEquiv
      sourceParent targetParent physical).trans targetJohn.map)

@[simp] theorem
    pureWZ2Proposition64ParentCenteredActualJohnChange_apply_map
    {sourceRho targetRho : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (physical : Point3 ≃ᵃ[ℝ] Point3) (point : Point3) :
    pureWZ2Proposition64ParentCenteredActualJohnChange
        sourceJohn targetJohn physical (sourceJohn.map point) =
      targetJohn.map
        (physical point +
          pureWZ2Proposition64ParentCenteringShift
            sourceParent targetParent physical) := by
  simp [pureWZ2Proposition64ParentCenteredActualJohnChange,
    AffineEquiv.trans_apply]

/-- The parent-centered actual-John change has the same linear part as the
untranslated source-John/physical/target-John composition. -/
theorem pureWZ2Proposition64ParentCenteredActualJohnChange_linear
    {sourceRho targetRho : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (physical : Point3 ≃ᵃ[ℝ] Point3) :
    (pureWZ2Proposition64ParentCenteredActualJohnChange
      sourceJohn targetJohn physical).linear =
      (sourceJohn.map.symm.trans
        (physical.trans targetJohn.map)).linear := by
  ext point
  rfl

/-- Exact inverse-volume formula for a parent-centered actual-John change. -/
theorem pureWZ2Proposition64ParentCenteredActualJohnChange_inverse_volume_eq
    {sourceRho targetRho : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (physical : Point3 ≃ᵃ[ℝ] Point3)
    (targetSet : Set Point3) :
    volume
        ((pureWZ2Proposition64ParentCenteredActualJohnChange
          sourceJohn targetJohn physical).symm '' targetSet) =
      ENNReal.ofReal
          |LinearMap.det
            ((sourceJohn.map.symm.trans
              (physical.trans targetJohn.map)).symm.linear :
                Point3 →ₗ[ℝ] Point3)| *
        volume targetSet := by
  rw [wz2PaperAffineEquiv_volume_image_eq]
  congr 2

/-- Physical parent/child containment gives the exact actual-John carrier
envelope required by the packet CWA kernel. -/
theorem pureWZ2Proposition64_parentCenteredActualJohn_carrier_envelope
    {sourceDelta sourceRho targetDelta targetRho lipschitzFactor factor : ℝ}
    (hsourceRho : 0 ≤ sourceRho)
    (htargetDelta : 0 < targetDelta)
    (htargetRho : 0 ≤ targetRho)
    (sourceChild : Kakeya.DeltaTube sourceDelta)
    (sourceParent : Kakeya.DeltaTube sourceRho)
    (targetChild : Kakeya.DeltaTube targetDelta)
    (targetParent : Kakeya.DeltaTube targetRho)
    (hsourceChild : sourceChild.carrier ⊆ sourceParent.carrier)
    (htargetChild : targetChild.carrier ⊆ targetParent.carrier)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (physical : Point3 ≃ᵃ[ℝ] Point3)
    (hlipschitzFactor : 0 ≤ lipschitzFactor)
    (hlipschitz : ∀ first second,
      dist (physical first) (physical second) ≤
        lipschitzFactor * dist first second)
    (hfactorOne : 1 ≤ factor)
    (hfactorRadius :
      lipschitzFactor * (sourceRho + 1 / 2) +
          (targetRho + 1 / 2) ≤
        factor * targetDelta) :
    pureWZ2Proposition64ParentCenteredActualJohnChange
          sourceJohn targetJohn physical ''
        (sourceJohn.map '' sourceChild.carrier) ⊆
      AffineMap.homothety (targetJohn.map
          (wz2PaperTubeMidpoint targetChild)) factor ''
        (targetJohn.map '' targetChild.carrier) := by
  have hphysical :=
    pureWZ2_affine_parent_packet_subset_child_homothety
      hsourceRho htargetDelta htargetRho sourceChild sourceParent targetChild
      targetParent hsourceChild htargetChild physical hlipschitzFactor
      hlipschitz hfactorOne hfactorRadius
  rintro point ⟨sourceJohnPoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
  have hshifted :
      physical sourcePoint +
          pureWZ2Proposition64ParentCenteringShift
            sourceParent targetParent physical ∈
        AffineMap.homothety (wz2PaperTubeMidpoint targetChild) factor ''
          targetChild.carrier :=
    hphysical ⟨sourcePoint, hsourcePoint, rfl⟩
  rcases hshifted with ⟨targetPoint, htargetPoint, htargetEq⟩
  refine ⟨targetJohn.map targetPoint, ⟨targetPoint, htargetPoint, rfl⟩, ?_⟩
  rw [pureWZ2Proposition64ParentCenteredActualJohnChange_apply_map]
  rw [← htargetEq]
  simpa [AffineMap.homothety_apply, AffineMap.lineMap_apply] using
    (targetJohn.map.apply_lineMap
      (wz2PaperTubeMidpoint targetChild) targetPoint factor).symm

/-- A positive-radius actual-John image of an ordinary tube is a convex body. -/
theorem pureWZ2_actualJohn_tube_image_isConvexBody
    {delta rho : ℝ}
    {parent : Kakeya.DeltaTube rho}
    (normalization : WZ2PaperAssouadUnitRescalingData parent)
    (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta) :
    JohnEllipsoid.IsConvexBody (normalization.map '' tube.carrier) := by
  let sourceBody := wz2_paper_ordinary_tube_isConvexBody tube hdelta
  refine ⟨sourceBody.1.affine_image normalization.map.toAffineMap,
    sourceBody.2.1.image
      normalization.map.toHomeomorphOfFiniteDimensional.continuous, ?_⟩
  have hinterior :
      interior (normalization.map '' tube.carrier) =
        normalization.map '' interior tube.carrier :=
    (normalization.map.toHomeomorphOfFiniteDimensional.image_interior
      tube.carrier).symm
  rw [hinterior]
  exact sourceBody.2.2.image normalization.map

/-- A strict target fiber is contained in the target parent, hence every
actual-John target body lies in the closed unit ball. -/
theorem pureWZ2_actualJohn_child_image_subset_unitBall
    {delta rho : ℝ}
    {child : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube rho}
    (normalization : WZ2PaperAssouadUnitRescalingData parent)
    (hchild : child.carrier ⊆ parent.carrier) :
    normalization.map '' child.carrier ⊆
      Metric.closedBall (0 : Point3) 1 := by
  rw [← normalization.outerJohn_image]
  exact Set.image_mono
    (hchild.trans normalization.parent_convex_body.outerJohnEllipsoid_spec.1)

/-- The target-child midpoint is an internal center for its actual-John body. -/
theorem pureWZ2_actualJohn_child_midpoint_mem
    {delta rho : ℝ}
    {child : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube rho}
    (normalization : WZ2PaperAssouadUnitRescalingData parent)
    (hdelta : 0 ≤ delta) :
    normalization.map (wz2PaperTubeMidpoint child) ∈
      normalization.map '' child.carrier :=
  ⟨wz2PaperTubeMidpoint child,
    wz2_paper_tubeMidpoint_mem_carrier child hdelta, rfl⟩

/-- Parent-centered actual-John CWA for an arbitrary target-indexed packet.
The target packet may later be one fiber of an owner map inside a complete
target cover fiber. -/
theorem pureWZ2Proposition64_parentCenteredIndexedPacket_cwa
    {sourceDelta sourceRho targetDelta targetRho
      lipschitzFactor factor : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {targetCoarse : Kakeya.Streamlined.TubeFamily targetRho}
    (sourceParent : Fin sourceCoarse.card)
    (targetParent : Fin targetCoarse.card)
    {sourceConstant : ENNReal}
    (sourceFiber : WZ2PaperPureUnitRescaledFullFiberData
      (fine := sourceFine) (coarse := sourceCoarse)
      sourceParent sourceConstant)
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
    (physical : Point3 ≃ᵃ[ℝ] Point3)
    (hlipschitzFactor : 0 ≤ lipschitzFactor)
    (hlipschitz : ∀ first second,
      dist (physical first) (physical second) ≤
        lipschitzFactor * dist first second)
    (hsourceRho : 0 ≤ sourceRho)
    (htargetDelta : 0 < targetDelta)
    (htargetRho : 0 ≤ targetRho)
    (hfactorOne : 1 ≤ factor)
    (hfactorRadius :
      lipschitzFactor * (sourceRho + 1 / 2) +
          (targetRho + 1 / 2) ≤
        factor * targetDelta)
    (inverseVolumeConstant : ENNReal)
    (inverse_volume : ∀ targetSet : Set Point3,
      volume
          ((pureWZ2Proposition64ParentCenteredActualJohnChange
            sourceFiber.normalization targetJohn physical).symm '' targetSet) ≤
        inverseVolumeConstant * volume targetSet) :
    WZ2PaperBodyConvexWolffBound targetBodies
      ((inverseVolumeConstant *
          ENNReal.ofReal (27 * (2 * factor - 1) ^ 3)) *
        ((weight⁻¹ * retentionConstant) * sourceConstant)) := by
  let equivalence :=
    pureWZ2Proposition64ParentCenteredActualJohnChange
      sourceFiber.normalization targetJohn physical
  let center : Fin targetBodies.card → Point3 := fun index =>
    targetJohn.map
      (wz2PaperTubeMidpoint (targetFine.tube (targetIndex index)))
  apply pureWZ2Proposition64_actualJohnPacket_cwa
    sourceParent sourceFiber targetBodies sourceIndex sourceIndex_injective
      source_mem weight retentionConstant weight_ne_zero weight_ne_top
      cardinality_retention equivalence factor hfactorOne
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
    exact pureWZ2_actualJohn_child_midpoint_mem targetJohn
      htargetDelta.le
  · intro index
    let sourceChild := sourceFine.tube (sourceIndex index)
    let targetChild := targetFine.tube (targetIndex index)
    have hsourceChild : sourceChild.carrier ⊆
        (sourceCoarse.tube sourceParent).carrier :=
      (mem_wz2PaperOrdinaryFullFiberIndices_iff sourceParent
        (sourceIndex index)).mp (source_mem index)
    have htargetChild : targetChild.carrier ⊆
        (targetCoarse.tube targetParent).carrier :=
      (mem_wz2PaperOrdinaryFullFiberIndices_iff targetParent
        (targetIndex index)).mp (target_mem index)
    have henvelope :=
      pureWZ2Proposition64_parentCenteredActualJohn_carrier_envelope
        hsourceRho htargetDelta htargetRho sourceChild
        (sourceCoarse.tube sourceParent) targetChild
        (targetCoarse.tube targetParent) hsourceChild htargetChild
        sourceFiber.normalization targetJohn physical hlipschitzFactor
        hlipschitz hfactorOne hfactorRadius
    have hsourceBody :
        ((pureWZ2Proposition64ActualJohnSourcePacket
          sourceParent sourceFiber.normalization targetBodies
            sourceIndex source_mem).body index).carrier =
          sourceFiber.normalization.map '' sourceChild.carrier := by
      change sourceFiber.normalization.map ''
          (sourceFine.tube
            ((wz2PaperOrdinaryFullFiberIndexEquiv sourceParent)
              ((wz2PaperOrdinaryFullFiberIndexEquiv sourceParent).symm
                ⟨sourceIndex index, source_mem index⟩)).1).carrier = _
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
    simpa only [equivalence, center, targetChild] using henvelope
  · exact inverse_volume

/-- The complete packet theorem with the parent-centering translation, target
actual-John bodies, convexity, unit-ball localization, and inverse Jacobian
all discharged.  Its remaining inputs are exactly the synchronized source
index, weighted-cardinality retention, and the explicit parent-scale radius
budget. -/
theorem pureWZ2Proposition64_parentCenteredActualJohnPacket_cwa
    {sourceDelta sourceRho targetDelta targetRho
      lipschitzFactor factor : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {targetCoarse : Kakeya.Streamlined.TubeFamily targetRho}
    (sourceParent : Fin sourceCoarse.card)
    (targetParent : Fin targetCoarse.card)
    {sourceConstant : ENNReal}
    (sourceFiber : WZ2PaperPureUnitRescaledFullFiberData
      (fine := sourceFine) (coarse := sourceCoarse)
      sourceParent sourceConstant)
    (targetJohn : WZ2PaperAssouadUnitRescalingData
      (targetCoarse.tube targetParent))
    (sourceIndex :
      Fin (wz2PaperOrdinaryFullFiberIndices
        targetFine targetCoarse targetParent).card →
        Fin sourceFine.card)
    (sourceIndex_injective : Function.Injective sourceIndex)
    (source_mem : ∀ index, sourceIndex index ∈
      wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent)
    (weight retentionConstant : ENNReal)
    (weight_ne_zero : weight ≠ 0)
    (weight_ne_top : weight ≠ ⊤)
    (cardinality_retention :
      weight *
          ((wz2PaperOrdinaryFullFiberIndices
            sourceFine sourceCoarse sourceParent).card : ENNReal) ≤
        retentionConstant *
          ((wz2PaperOrdinaryFullFiberIndices
            targetFine targetCoarse targetParent).card : ENNReal))
    (physical : Point3 ≃ᵃ[ℝ] Point3)
    (hlipschitzFactor : 0 ≤ lipschitzFactor)
    (hlipschitz : ∀ first second,
      dist (physical first) (physical second) ≤
        lipschitzFactor * dist first second)
    (hsourceRho : 0 ≤ sourceRho)
    (htargetDelta : 0 < targetDelta)
    (htargetRho : 0 ≤ targetRho)
    (hfactorOne : 1 ≤ factor)
    (hfactorRadius :
      lipschitzFactor * (sourceRho + 1 / 2) +
          (targetRho + 1 / 2) ≤
        factor * targetDelta) :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := targetFine) (coarse := targetCoarse)
        targetParent targetJohn)
      ((ENNReal.ofReal
            |LinearMap.det
              ((sourceFiber.normalization.map.symm.trans
                (physical.trans targetJohn.map)).symm.linear :
                  Point3 →ₗ[ℝ] Point3)| *
          ENNReal.ofReal (27 * (2 * factor - 1) ^ 3)) *
        ((weight⁻¹ * retentionConstant) * sourceConstant)) := by
  let targetBodies := wz2PaperPureUnitRescaledFullFiberBodyFamily
    (fine := targetFine) (coarse := targetCoarse)
    targetParent targetJohn
  let equivalence :=
    pureWZ2Proposition64ParentCenteredActualJohnChange
      sourceFiber.normalization targetJohn physical
  let center : Fin targetBodies.card → Point3 := fun index =>
    targetJohn.map
      (wz2PaperTubeMidpoint
        (targetFine.tube
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1))
  apply pureWZ2Proposition64_actualJohnPacket_cwa
    sourceParent sourceFiber targetBodies sourceIndex sourceIndex_injective
      source_mem weight retentionConstant weight_ne_zero weight_ne_top
      cardinality_retention equivalence factor hfactorOne
      (center := center)
      (inverseVolumeConstant := ENNReal.ofReal
        |LinearMap.det
          ((sourceFiber.normalization.map.symm.trans
            (physical.trans targetJohn.map)).symm.linear :
              Point3 →ₗ[ℝ] Point3)|)
  · intro index
    apply pureWZ2_actualJohn_tube_image_isConvexBody targetJohn
      htargetDelta
  · intro index
    apply pureWZ2_actualJohn_child_image_subset_unitBall targetJohn
    exact (mem_wz2PaperOrdinaryFullFiberIndices_iff targetParent
      ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1).mp
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).2
  · intro index
    exact pureWZ2_actualJohn_child_midpoint_mem targetJohn
      htargetDelta.le
  · intro index
    let sourceChild := sourceFine.tube (sourceIndex index)
    let targetChild := targetFine.tube
      ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1
    have hsourceChild : sourceChild.carrier ⊆
        (sourceCoarse.tube sourceParent).carrier :=
      (mem_wz2PaperOrdinaryFullFiberIndices_iff sourceParent
        (sourceIndex index)).mp (source_mem index)
    have htargetChild : targetChild.carrier ⊆
        (targetCoarse.tube targetParent).carrier :=
      (mem_wz2PaperOrdinaryFullFiberIndices_iff targetParent
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1).mp
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).2
    have henvelope :=
      pureWZ2Proposition64_parentCenteredActualJohn_carrier_envelope
        hsourceRho htargetDelta htargetRho sourceChild
        (sourceCoarse.tube sourceParent) targetChild
        (targetCoarse.tube targetParent) hsourceChild htargetChild
        sourceFiber.normalization targetJohn physical hlipschitzFactor
        hlipschitz hfactorOne hfactorRadius
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
        sourceFiber.normalization.map ''
          (sourceFine.tube (sourceIndex index)).carrier
      have hindex :
          ((wz2PaperOrdinaryFullFiberIndexEquiv sourceParent)
            ((wz2PaperOrdinaryFullFiberIndexEquiv sourceParent).symm
              ⟨sourceIndex index, source_mem index⟩)).1 =
            sourceIndex index :=
        congrArg Subtype.val
          ((wz2PaperOrdinaryFullFiberIndexEquiv sourceParent).apply_symm_apply
            ⟨sourceIndex index, source_mem index⟩)
      rw [hindex]
    have htargetBody :
        (targetBodies.body index).carrier =
          targetJohn.map '' targetChild.carrier := rfl
    rw [hsourceBody, htargetBody]
    simpa only [equivalence, center, targetChild] using henvelope
  · intro targetSet
    exact le_of_eq <|
      pureWZ2Proposition64ParentCenteredActualJohnChange_inverse_volume_eq
        sourceFiber.normalization targetJohn physical targetSet

end Kakeya.Assouad

end
