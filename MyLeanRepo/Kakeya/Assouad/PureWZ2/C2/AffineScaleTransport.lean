import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12NestedJohnCWATransport
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureCWAReindex
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12QuotientBodyCWA

/-!
# Generic affine transport of one public pure scale witness

This module isolates the mechanical Assouad Definition 2.12 transport after
the actual target tube families and public partitioning cover have been
constructed.  Centered doubled-fiber disjointness remains an explicit field
of `targetCover`; it is never inferred from a weak line cover.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2AffineScaleTransportData
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {C inverseVolumeConstant : ENNReal}
    (sourceScale : WZ2PaperPureScaleCoverData sourceFine sourceRho C) where
  affine : Point3 ≃ᵃ[ℝ] Point3
  targetFine : Kakeya.Streamlined.TubeFamily targetDelta
  targetCoarse : Kakeya.Streamlined.TubeFamily targetRho
  fineIndex : Fin targetFine.card ≃ Fin sourceFine.card
  coarseIndex : Fin targetCoarse.card ≃ Fin sourceScale.coarse.card
  targetCover :
    WZ2PaperPurePartitioningCover targetFine targetCoarse
  fullFiber_source_indices :
    ∀ targetParent,
      Finset.image fineIndex
          (wz2PaperOrdinaryFullFiberIndices
            targetFine targetCoarse targetParent) =
        wz2PaperOrdinaryFullFiberIndices
          sourceFine sourceScale.coarse (coarseIndex targetParent)
  fine_image_subset :
    ∀ targetIndex,
      affine '' (sourceFine.tube (fineIndex targetIndex)).carrier ⊆
        (targetFine.tube targetIndex).carrier
  john_inverse_volume :
    ∀ targetParent,
      let sourceParent := coarseIndex targetParent
      let sourceFiber :=
        Classical.choice (sourceScale.rescaledFiber sourceParent)
      ∀ targetJohn : WZ2PaperAssouadUnitRescalingData
          (targetCoarse.tube targetParent),
        ∀ targetSet : Set Point3,
          MeasureTheory.volume
              ((sourceFiber.normalization.map.symm.trans
                (affine.trans targetJohn.map)).symm '' targetSet) ≤
            inverseVolumeConstant * MeasureTheory.volume targetSet

namespace PureWZ2AffineScaleTransportData

/-- Strict full-fiber counts are exactly preserved by the synchronized
index equivalences. -/
theorem fullFiberCount_eq
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {C inverseVolumeConstant : ENNReal}
    {sourceScale : WZ2PaperPureScaleCoverData sourceFine sourceRho C}
    (data :
      PureWZ2AffineScaleTransportData
        (targetDelta := targetDelta) (targetRho := targetRho)
        (inverseVolumeConstant := inverseVolumeConstant) sourceScale)
    (targetParent : Fin data.targetCoarse.card) :
    wz2PaperOrdinaryFullFiberCount
        data.targetFine data.targetCoarse targetParent =
      wz2PaperOrdinaryFullFiberCount
        sourceFine sourceScale.coarse (data.coarseIndex targetParent) := by
  unfold wz2PaperOrdinaryFullFiberCount
  rw [← data.fullFiber_source_indices targetParent]
  norm_cast
  exact
    (Finset.card_image_of_injective _ data.fineIndex.injective).symm

/-- The exact fiber equality induces the outer-John body index equivalence. -/
noncomputable def bodyIndexEquiv
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {C inverseVolumeConstant : ENNReal}
    {sourceScale : WZ2PaperPureScaleCoverData sourceFine sourceRho C}
    (data :
      PureWZ2AffineScaleTransportData
        (targetDelta := targetDelta) (targetRho := targetRho)
        (inverseVolumeConstant := inverseVolumeConstant) sourceScale)
    (targetParent : Fin data.targetCoarse.card) :
    Fin (wz2PaperOrdinaryFullFiberIndices
      data.targetFine data.targetCoarse targetParent).card ≃
      Fin (wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceScale.coarse
        (data.coarseIndex targetParent)).card := by
  let targetFiber := wz2PaperOrdinaryFullFiberIndices
    data.targetFine data.targetCoarse targetParent
  let sourceFiber := wz2PaperOrdinaryFullFiberIndices
    sourceFine sourceScale.coarse (data.coarseIndex targetParent)
  let targetSubtype :=
    (wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := data.targetFine) (coarse := data.targetCoarse)
      targetParent)
  let sourceSubtype :=
    (wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := sourceFine) (coarse := sourceScale.coarse)
      (data.coarseIndex targetParent))
  let map : {index // index ∈ targetFiber} →
      {index // index ∈ sourceFiber} := fun index =>
    ⟨data.fineIndex index.1, by
      change data.fineIndex index.1 ∈
        wz2PaperOrdinaryFullFiberIndices sourceFine sourceScale.coarse
          (data.coarseIndex targetParent)
      rw [← data.fullFiber_source_indices targetParent]
      exact Finset.mem_image.mpr ⟨index.1, index.2, rfl⟩⟩
  have hmap : Function.Bijective map := by
    constructor
    · intro first second heq
      apply Subtype.ext
      exact data.fineIndex.injective (congrArg Subtype.val heq)
    · intro sourceIndex
      have hsource : sourceIndex.1 ∈
          Finset.image data.fineIndex targetFiber := by
        rw [data.fullFiber_source_indices targetParent]
        exact sourceIndex.2
      rcases Finset.mem_image.mp hsource with
        ⟨targetIndex, htargetIndex, heq⟩
      refine ⟨⟨targetIndex, htargetIndex⟩, ?_⟩
      apply Subtype.ext
      exact heq
  exact (targetSubtype.trans (Equiv.ofBijective map hmap)).trans
    sourceSubtype.symm

theorem bodyIndexEquiv_source
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {C inverseVolumeConstant : ENNReal}
    {sourceScale : WZ2PaperPureScaleCoverData sourceFine sourceRho C}
    (data :
      PureWZ2AffineScaleTransportData
        (targetDelta := targetDelta) (targetRho := targetRho)
        (inverseVolumeConstant := inverseVolumeConstant) sourceScale)
    (targetParent : Fin data.targetCoarse.card)
    (targetIndex : Fin
      (wz2PaperOrdinaryFullFiberIndices
        data.targetFine data.targetCoarse targetParent).card) :
    ((wz2PaperOrdinaryFullFiberIndexEquiv
        (fine := sourceFine) (coarse := sourceScale.coarse)
        (data.coarseIndex targetParent))
      (data.bodyIndexEquiv targetParent targetIndex)).1 =
      data.fineIndex
        (((wz2PaperOrdinaryFullFiberIndexEquiv
          (fine := data.targetFine) (coarse := data.targetCoarse)
          targetParent) targetIndex).1) := by
  simp [bodyIndexEquiv]

/-- Transport one complete source outer-John fiber through the common affine
map and the synchronized target fine family. -/
theorem fiber_convexWolff
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {C inverseVolumeConstant : ENNReal}
    {sourceScale : WZ2PaperPureScaleCoverData sourceFine sourceRho C}
    (data :
      PureWZ2AffineScaleTransportData
        (targetDelta := targetDelta) (targetRho := targetRho)
        (inverseVolumeConstant := inverseVolumeConstant) sourceScale)
    (targetParent : Fin data.targetCoarse.card)
    (targetJohn : WZ2PaperAssouadUnitRescalingData
      (data.targetCoarse.tube targetParent)) :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := data.targetFine) (coarse := data.targetCoarse)
        targetParent targetJohn)
      (inverseVolumeConstant * C) := by
  let sourceParent := data.coarseIndex targetParent
  let sourceFiber := Classical.choice (sourceScale.rescaledFiber sourceParent)
  let coordinateChange :=
    sourceFiber.normalization.map.symm.trans
      (data.affine.trans targetJohn.map)
  let indexEquiv := data.bodyIndexEquiv targetParent
  let sourceBodies :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := sourceFine) (coarse := sourceScale.coarse)
      sourceParent sourceFiber.normalization
  let targetBodies :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := data.targetFine) (coarse := data.targetCoarse)
      targetParent targetJohn
  let hindex : Fin targetBodies.card ≃ Fin sourceBodies.card := indexEquiv
  apply wz2PaperBodyConvexWolffBound_of_affineTransport
    coordinateChange hindex
  · intro targetIndex
    let targetSource :=
      (wz2PaperOrdinaryFullFiberIndexEquiv targetParent) targetIndex
    change coordinateChange ''
        (sourceFiber.normalization.map ''
          (sourceFine.tube
            ((wz2PaperOrdinaryFullFiberIndexEquiv sourceParent)
              (hindex targetIndex)).1).carrier) ⊆
      targetJohn.map ''
        (data.targetFine.tube targetSource.1).carrier
    have hsource :
        ((wz2PaperOrdinaryFullFiberIndexEquiv sourceParent)
          (hindex targetIndex)).1 =
        data.fineIndex targetSource.1 := by
      exact data.bodyIndexEquiv_source targetParent targetIndex
    rw [hsource]
    rintro targetPoint ⟨sourceJohnPoint,
      ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
    refine ⟨data.affine sourcePoint,
      data.fine_image_subset targetSource.1
        ⟨sourcePoint, hsourcePoint, rfl⟩, ?_⟩
    simp [coordinateChange, AffineEquiv.trans_apply]
  · intro targetSet
    exact data.john_inverse_volume targetParent targetJohn targetSet
  · exact sourceFiber.convex_wolff

/-- Assemble the transported public pure scale witness. -/
noncomputable def toScaleData
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {C inverseVolumeConstant : ENNReal}
    {sourceScale : WZ2PaperPureScaleCoverData sourceFine sourceRho C}
    (data :
      PureWZ2AffineScaleTransportData
        (targetDelta := targetDelta) (targetRho := targetRho)
        (inverseVolumeConstant := inverseVolumeConstant) sourceScale)
    (htargetDelta : 0 < targetDelta)
    (htargetRho : 0 < targetRho) :
    WZ2PaperPureScaleCoverData
      data.targetFine targetRho
      (max C (inverseVolumeConstant * C)) where
  delta_pos := htargetDelta
  rho_pos := htargetRho
  coarse := data.targetCoarse
  cover := data.targetCover
  full_fiber_uniform first second := by
    rw [data.fullFiberCount_eq first, data.fullFiberCount_eq second]
    exact
      (sourceScale.full_fiber_uniform
        (data.coarseIndex first) (data.coarseIndex second)).trans (by
          gcongr
          exact le_max_left _ _)
  rescaledFiber targetParent := by
    let targetJohn := WZ2PaperAssouadUnitRescalingData.ofTube
      (data.targetCoarse.tube targetParent) htargetRho
    have hcwa := data.fiber_convexWolff targetParent targetJohn
    refine ⟨{ normalization := targetJohn, convex_wolff := ?_ }⟩
    intro convexSet hconvex
    exact (hcwa convexSet hconvex).trans (by
      gcongr
      exact le_max_right C (inverseVolumeConstant * C))

/-- A per-request affine transport producer lifts a complete source nearby-CWA
certificate to the target family.  The target actual scale and the requested
window are explicit because rediscretization may change the physical radius. -/
theorem nearbyCWA_of_affine_transports
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {C inverseVolumeConstant : ENNReal}
    (source : WZ2PaperPureCWAAtNearbyScales sourceFine C)
    (hinverseFinite : inverseVolumeConstant ≠ ⊤)
    (htargetDelta : 0 < targetDelta)
    (htargetEssential : WZ2PaperOrdinaryIsEssentiallyDistinct targetFine)
    (transport :
      ∀ requested : WZ2PaperRequestedScale targetDelta,
        ∃ sourceRequested : WZ2PaperRequestedScale sourceDelta,
          let sourceNearby := Classical.choice (source.2.2.2 sourceRequested)
          ∃ targetRho : ℝ,
            requested.1 ≤ targetRho ∧
            ENNReal.ofReal targetRho <
              max C (inverseVolumeConstant * C) *
                ENNReal.ofReal requested.1 ∧
            ∃ data : PureWZ2AffineScaleTransportData
                (targetDelta := targetDelta) (targetRho := targetRho)
                (inverseVolumeConstant := inverseVolumeConstant)
                sourceNearby.scaleData,
              data.targetFine = targetFine ∧
                0 < targetRho) :
    WZ2PaperPureCWAAtNearbyScales targetFine
      (max C (inverseVolumeConstant * C)) := by
  have hconstant :
      WZ2PaperFiniteErrorConstant
        (max C (inverseVolumeConstant * C)) := by
    refine ⟨source.2.1.1.trans (le_max_left _ _), ?_⟩
    exact max_ne_top source.2.1.2
      (ENNReal.mul_ne_top hinverseFinite source.2.1.2)
  refine ⟨htargetDelta, hconstant, htargetEssential, ?_⟩
  intro requested
  rcases transport requested with
    ⟨sourceRequested, targetRho, hrequested, hwithin,
      data, htargetFineEq, htargetRho⟩
  subst targetFine
  exact ⟨{
    rho := targetRho
    requested_le := hrequested
    within_factor := hwithin
    scaleData := data.toScaleData htargetDelta htargetRho }⟩

end PureWZ2AffineScaleTransportData

/-- Multi-child version of the affine scale transport.  A source outer-John
fiber is first transported one-to-one to `transportedBodies`; the actual
target full fiber is then obtained by a surjective uniform body cover. -/
structure PureWZ2AffineScaleBodyCoverData
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {C inverseVolumeConstant bodyConstant : ENNReal}
    (sourceScale : WZ2PaperPureScaleCoverData sourceFine sourceRho C) where
  targetFine : Kakeya.Streamlined.TubeFamily targetDelta
  targetCoarse : Kakeya.Streamlined.TubeFamily targetRho
  targetCover : WZ2PaperPurePartitioningCover targetFine targetCoarse
  coarseIndex : Fin targetCoarse.card → Fin sourceScale.coarse.card
  full_fiber_uniform :
    WZ2PaperPureFullFibersAreCUniform
      targetFine targetCoarse bodyConstant
  targetNormalization :
    ∀ parent, WZ2PaperAssouadUnitRescalingData
      (targetCoarse.tube parent)
  transportedBodies :
    ∀ parent, Kakeya.Streamlined.BodyFamily
  sourceBodyIndex :
    ∀ parent,
      Fin (transportedBodies parent).card ≃
        Fin (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := sourceFine) (coarse := sourceScale.coarse)
          (coarseIndex parent)
          (Classical.choice
            (sourceScale.rescaledFiber (coarseIndex parent))).normalization).card
  sourceBodyTransport :
    ∀ parent targetIndex,
      let sourceFiber := Classical.choice
        (sourceScale.rescaledFiber (coarseIndex parent))
      let sourceBodies := wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := sourceFine) (coarse := sourceScale.coarse)
        (coarseIndex parent) sourceFiber.normalization
      let coordinateChange : Point3 ≃ᵃ[ℝ] Point3 :=
        sourceFiber.normalization.map.symm.trans
          (targetNormalization parent).map
      coordinateChange ''
          (sourceBodies.body (sourceBodyIndex parent targetIndex)).carrier ⊆
        ((transportedBodies parent).body targetIndex).carrier
  sourceBodyInverseVolume :
    ∀ parent,
      let sourceFiber := Classical.choice
        (sourceScale.rescaledFiber (coarseIndex parent))
      let coordinateChange : Point3 ≃ᵃ[ℝ] Point3 :=
        sourceFiber.normalization.map.symm.trans
          (targetNormalization parent).map
      ∀ targetSet,
        MeasureTheory.volume (coordinateChange.symm '' targetSet) ≤
          inverseVolumeConstant * MeasureTheory.volume targetSet
  bodyCover :
    ∀ parent,
      WZ2PaperPureQuotientBodyCoverData
        (transportedBodies parent)
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := targetFine) (coarse := targetCoarse)
          parent (targetNormalization parent))
        bodyConstant

namespace PureWZ2AffineScaleBodyCoverData

noncomputable def toScaleData
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {C inverseVolumeConstant bodyConstant : ENNReal}
    {sourceScale : WZ2PaperPureScaleCoverData sourceFine sourceRho C}
    (data : PureWZ2AffineScaleBodyCoverData
      (targetDelta := targetDelta) (targetRho := targetRho)
      (inverseVolumeConstant := inverseVolumeConstant)
      (bodyConstant := bodyConstant) sourceScale)
    (htargetDelta : 0 < targetDelta)
    (htargetRho : 0 < targetRho) :
    WZ2PaperPureScaleCoverData data.targetFine targetRho
      (max bodyConstant
        (bodyConstant * (inverseVolumeConstant * C))) where
  delta_pos := htargetDelta
  rho_pos := htargetRho
  coarse := data.targetCoarse
  cover := data.targetCover
  full_fiber_uniform first second :=
    (data.full_fiber_uniform first second).trans (by
      gcongr
      exact le_max_left _ _)
  rescaledFiber parent := by
    let sourceFiber := Classical.choice
      (sourceScale.rescaledFiber (data.coarseIndex parent))
    let coordinateChange : Point3 ≃ᵃ[ℝ] Point3 :=
      sourceFiber.normalization.map.symm.trans
        (data.targetNormalization parent).map
    have htransported :
        WZ2PaperBodyConvexWolffBound
          (data.transportedBodies parent)
          (inverseVolumeConstant * C) :=
      wz2PaperBodyConvexWolffBound_of_affineTransport
        coordinateChange (data.sourceBodyIndex parent)
        (data.sourceBodyTransport parent)
        (data.sourceBodyInverseVolume parent)
        sourceFiber.convex_wolff
    have htarget := (data.bodyCover parent).convexWolff htransported
    exact ⟨{
      normalization := data.targetNormalization parent
      convex_wolff := fun convexSet hconvex =>
        (htarget convexSet hconvex).trans (by
          gcongr
          exact le_max_right bodyConstant
            (bodyConstant * (inverseVolumeConstant * C))) }⟩

end PureWZ2AffineScaleBodyCoverData

end Kakeya.Assouad

end
