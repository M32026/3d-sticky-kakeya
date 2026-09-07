import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineHomotheticBodyCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicCenteredMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicOrdinaryCarrierEnvelope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.BodyCWAFiberwiseAssembly

/-!
# Actual-John CWA on a selected source-parent packet

This module isolates the finite reindexing needed in Proposition 6.5.  A
target packet injects into one complete source actual fiber.  An explicit
weighted cardinality ratio first restricts the source actual-John CWA to that
packet.  A common affine coordinate change and a homothetic carrier envelope
then transfer the bound to the corresponding target bodies.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Index of a selected target packet inside the canonical enumeration of
one complete source strict fiber. -/
noncomputable def pureWZ2ActualJohnPacketSourceBodyIndex
    {sourceDelta sourceRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    (sourceParent : Fin sourceCoarse.card)
    {targetBodies : Kakeya.Streamlined.BodyFamily}
    (sourceIndex : Fin targetBodies.card → Fin sourceFine.card)
    (source_mem : ∀ index, sourceIndex index ∈
      wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent) :
    Fin targetBodies.card →
      Fin (wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent).card := fun index =>
  (wz2PaperOrdinaryFullFiberIndexEquiv sourceParent).symm
    ⟨sourceIndex index, source_mem index⟩

theorem pureWZ2ActualJohnPacketSourceBodyIndex_injective
    {sourceDelta sourceRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    (sourceParent : Fin sourceCoarse.card)
    {targetBodies : Kakeya.Streamlined.BodyFamily}
    (sourceIndex : Fin targetBodies.card → Fin sourceFine.card)
    (sourceIndex_injective : Function.Injective sourceIndex)
    (source_mem : ∀ index, sourceIndex index ∈
      wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent) :
    Function.Injective
      (pureWZ2ActualJohnPacketSourceBodyIndex
        sourceParent sourceIndex source_mem) := by
  intro first second heq
  apply sourceIndex_injective
  have hsubtype := congrArg
    (wz2PaperOrdinaryFullFiberIndexEquiv sourceParent) heq
  simpa [pureWZ2ActualJohnPacketSourceBodyIndex] using
    congrArg Subtype.val hsubtype

/-- The source actual-John bodies corresponding exactly to a selected target
packet. -/
noncomputable def pureWZ2ActualJohnSourcePacketBodyFamily
    {sourceDelta sourceRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    (sourceParent : Fin sourceCoarse.card)
    (sourceNormalization : WZ2PaperAssouadUnitRescalingData
      (sourceCoarse.tube sourceParent))
    (targetBodies : Kakeya.Streamlined.BodyFamily)
    (sourceIndex : Fin targetBodies.card → Fin sourceFine.card)
    (source_mem : ∀ index, sourceIndex index ∈
      wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent) :
    Kakeya.Streamlined.BodyFamily where
  card := targetBodies.card
  body index :=
    (wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := sourceFine) (coarse := sourceCoarse)
      sourceParent sourceNormalization).body
        (pureWZ2ActualJohnPacketSourceBodyIndex
          sourceParent sourceIndex source_mem index)

/-- Restrict one complete source actual-John CWA to a target-indexed packet
using an explicit weighted cardinality ratio. -/
theorem pureWZ2_actualJohnSourcePacket_cwa
    {sourceDelta sourceRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    (sourceParent : Fin sourceCoarse.card)
    {sourceConstant : ENNReal}
    (sourceFiber : WZ2PaperPureUnitRescaledFullFiberData
      (fine := sourceFine) (coarse := sourceCoarse)
      sourceParent sourceConstant)
    (targetBodies : Kakeya.Streamlined.BodyFamily)
    (sourceIndex : Fin targetBodies.card → Fin sourceFine.card)
    (sourceIndex_injective : Function.Injective sourceIndex)
    (source_mem : ∀ index, sourceIndex index ∈
      wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent)
    (weight K : ENNReal)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hcardinality :
      weight *
          ((wz2PaperOrdinaryFullFiberIndices
            sourceFine sourceCoarse sourceParent).card : ENNReal) ≤
        K * targetBodies.enncard) :
    WZ2PaperBodyConvexWolffBound
      (pureWZ2ActualJohnSourcePacketBodyFamily
        sourceParent sourceFiber.normalization targetBodies
          sourceIndex source_mem)
      ((weight⁻¹ * K) * sourceConstant) := by
  let sourceBodies := wz2PaperPureUnitRescaledFullFiberBodyFamily
    (fine := sourceFine) (coarse := sourceCoarse)
    sourceParent sourceFiber.normalization
  let sourceBodyIndex : Fin targetBodies.card ↪ Fin sourceBodies.card :=
    ⟨pureWZ2ActualJohnPacketSourceBodyIndex
        sourceParent sourceIndex source_mem,
      pureWZ2ActualJohnPacketSourceBodyIndex_injective
        sourceParent sourceIndex sourceIndex_injective source_mem⟩
  apply pureWZ2_bodyCWA_of_weighted_indexed_subfamily
    (source := sourceBodies)
    (target := pureWZ2ActualJohnSourcePacketBodyFamily
      sourceParent sourceFiber.normalization targetBodies
        sourceIndex source_mem)
    sourceBodyIndex (fun _ => rfl) hweightZero hweightTop
  · change weight *
        ((wz2PaperOrdinaryFullFiberIndices
          sourceFine sourceCoarse sourceParent).card : ENNReal) ≤
      K * (targetBodies.card : ENNReal)
    simpa [Kakeya.Streamlined.BodyFamily.enncard] using hcardinality
  · exact sourceFiber.convex_wolff

/-- Transfer a selected source actual-John packet to its target actual-John
packet through a common affine map and a pointwise homothetic envelope. -/
theorem pureWZ2_actualJohnPacket_cwa_of_affine_homothetic_envelope
    {sourceDelta sourceRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    (sourceParent : Fin sourceCoarse.card)
    {sourceConstant : ENNReal}
    (sourceFiber : WZ2PaperPureUnitRescaledFullFiberData
      (fine := sourceFine) (coarse := sourceCoarse)
      sourceParent sourceConstant)
    (targetBodies : Kakeya.Streamlined.BodyFamily)
    (sourceIndex : Fin targetBodies.card → Fin sourceFine.card)
    (sourceIndex_injective : Function.Injective sourceIndex)
    (source_mem : ∀ index, sourceIndex index ∈
      wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent)
    (weight K : ENNReal)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hcardinality :
      weight *
          ((wz2PaperOrdinaryFullFiberIndices
            sourceFine sourceCoarse sourceParent).card : ENNReal) ≤
        K * targetBodies.enncard)
    (coordinateChange : Point3 ≃ᵃ[ℝ] Point3)
    (factor radius : ℝ)
    (hfactor : 1 ≤ factor)
    (hradius : 0 ≤ radius)
    (htargetBody : ∀ index,
      JohnEllipsoid.IsConvexBody (targetBodies.body index).carrier)
    (htargetBound : ∀ index,
      (targetBodies.body index).carrier ⊆
        Metric.closedBall (0 : Point3) radius)
    (targetCenter : Fin targetBodies.card → Point3)
    (hcenter : ∀ index,
      targetCenter index ∈ (targetBodies.body index).carrier)
    (hcarrier : ∀ index,
      coordinateChange ''
          ((pureWZ2ActualJohnSourcePacketBodyFamily
            sourceParent sourceFiber.normalization targetBodies
              sourceIndex source_mem).body index).carrier ⊆
        AffineMap.homothety (targetCenter index) factor ''
          (targetBodies.body index).carrier) :
    WZ2PaperBodyConvexWolffBound targetBodies
      (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
        ENNReal.ofReal
          |LinearMap.det
            (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| *
        ((weight⁻¹ * K) * sourceConstant)) := by
  apply pureWZ2_bodyCWA_of_affine_homothetic_envelope
    (source := pureWZ2ActualJohnSourcePacketBodyFamily
      sourceParent sourceFiber.normalization targetBodies
        sourceIndex source_mem)
    (target := targetBodies)
    coordinateChange (Equiv.refl _) factor radius hfactor hradius
    htargetBody htargetBound targetCenter hcenter hcarrier
  exact pureWZ2_actualJohnSourcePacket_cwa sourceParent sourceFiber
    targetBodies sourceIndex sourceIndex_injective source_mem weight K
      hweightZero hweightTop hcardinality

/-- The source-John to target-John coordinate change induced by the exact
centered triangular map. -/
noncomputable def pureWZ2AnisotropicJohnCoordinateChange
    {sourceRho targetRho c d m : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (g : SlopeFunction) (center : Point3)
    (hcd : c < d) (hm : 0 < m)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  sourceJohn.map.symm.trans
    ((anisotropicCenteredRescalingAffineEquiv
      g c d m center hcd hm).trans targetJohn.map)

@[simp] theorem pureWZ2AnisotropicJohnCoordinateChange_apply_sourceMap
    {sourceRho targetRho c d m : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (g : SlopeFunction) (center : Point3)
    (hcd : c < d) (hm : 0 < m)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (point : Point3) :
    pureWZ2AnisotropicJohnCoordinateChange g center hcd hm
        sourceJohn targetJohn (sourceJohn.map point) =
      targetJohn.map
        (anisotropicCenteredRescalingMap g c d m center point) := by
  simp [pureWZ2AnisotropicJohnCoordinateChange, AffineEquiv.trans_apply]

/-- A source ordinary-carrier envelope becomes the required body envelope
after composing the source and target canonical John normalizations. -/
theorem pureWZ2AnisotropicJohnCoordinateChange_carrier
    {sourceRho targetRho c d m : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (g : SlopeFunction) (center : Point3)
    (hcd : c < d) (hm : 0 < m)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (factor : ℝ)
    (htargetCenter : Point3)
    (sourceSet targetSet : Set Point3)
    (hcarrier :
      anisotropicCenteredRescalingMap g c d m center ''
          sourceSet ⊆
        AffineMap.homothety htargetCenter factor ''
          targetSet) :
    pureWZ2AnisotropicJohnCoordinateChange g center hcd hm
          sourceJohn targetJohn ''
        (sourceJohn.map '' sourceSet) ⊆
      AffineMap.homothety (targetJohn.map htargetCenter) factor ''
        (targetJohn.map '' targetSet) := by
  rintro targetPoint ⟨sourceJohnPoint,
    ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
  rcases hcarrier ⟨sourcePoint, hsourcePoint, rfl⟩ with
    ⟨targetCarrierPoint, htargetCarrierPoint, hhomothety⟩
  refine ⟨targetJohn.map targetCarrierPoint,
    ⟨targetCarrierPoint, htargetCarrierPoint, rfl⟩, ?_⟩
  rw [pureWZ2AnisotropicJohnCoordinateChange_apply_sourceMap]
  rw [← hhomothety]
  change (AffineMap.lineMap
      (targetJohn.map htargetCenter)
      (targetJohn.map targetCarrierPoint)) factor =
    targetJohn.map
      ((AffineMap.lineMap htargetCenter targetCarrierPoint) factor)
  exact (targetJohn.map.apply_lineMap
    htargetCenter targetCarrierPoint factor).symm

/-- Concrete packet CWA for the exact triangular target tube family.

The caller supplies only the finite packet-to-source indexing facts and the
weighted cardinality ratio.  All geometric transport is discharged by the
ordinary-carrier envelope theorem above. -/
theorem pureWZ2_anisotropicPaperTargetPacket_cwa
    {sourceDelta sourceRho targetDelta targetRho c d m S : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    (sourceParent : Fin sourceCoarse.card)
    {sourceConstant : ENNReal}
    (sourceFiber : WZ2PaperPureUnitRescaledFullFiberData
      (fine := sourceFine) (coarse := sourceCoarse)
      sourceParent sourceConstant)
    (g : SlopeFunction) (center : Point3)
    (hcd : c < d) (hdc : d - c ≤ 1 / 25)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hg : g.IsNormalized)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hS : S = 2 / (d - c))
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : S * sourceDelta ≤ targetDelta)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (targetBodies : Kakeya.Streamlined.BodyFamily)
    (targetIndex : Fin targetBodies.card → Fin sourceFine.card)
    (targetIndex_injective : Function.Injective targetIndex)
    (target_mem : ∀ index, targetIndex index ∈
      wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent)
    (targetParent : Kakeya.DeltaTube targetRho)
    (targetNormalization : WZ2PaperAssouadUnitRescalingData
      targetParent)
    (target_mem_parent : ∀ index,
      (anisotropicPaperTargetTube g c d m center targetDelta hcd hm
        (sourceFine.tube (targetIndex index))).carrier ⊆
        targetParent.carrier)
    (target_body : ∀ index,
      (targetBodies.body index).carrier =
        targetNormalization.map ''
          (anisotropicPaperTargetTube g c d m center targetDelta hcd hm
            (sourceFine.tube (targetIndex index))).carrier)
    (weight K : ENNReal)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hcardinality :
      weight *
          ((wz2PaperOrdinaryFullFiberIndices
            sourceFine sourceCoarse sourceParent).card : ENNReal) ≤
        K * targetBodies.enncard) :
    WZ2PaperBodyConvexWolffBound targetBodies
      (ENNReal.ofReal (27 * (2 * (32 * S) - 1) ^ 3) *
        ENNReal.ofReal
          |LinearMap.det
            ((pureWZ2AnisotropicJohnCoordinateChange g center hcd hm
              sourceFiber.normalization targetNormalization).symm.linear :
                Point3 →ₗ[ℝ] Point3)| *
        ((weight⁻¹ * K) * sourceConstant)) := by
  let sourcePacket := pureWZ2ActualJohnSourcePacketBodyFamily
    sourceParent sourceFiber.normalization targetBodies targetIndex target_mem
  let affine := anisotropicCenteredRescalingAffineEquiv
    g c d m center hcd hm
  let coordinateChange := pureWZ2AnisotropicJohnCoordinateChange
    g center hcd hm sourceFiber.normalization targetNormalization
  have htargetDeltaPos : 0 < targetDelta :=
    (mul_pos (by rw [hS]; positivity) hsourceDelta).trans_le htargetDelta
  have hSOne : 1 ≤ S := by
    rw [hS]
    have hlength : 0 < d - c := sub_pos.mpr hcd
    apply (le_div_iff₀ hlength).2
    nlinarith
  have hfactor : 1 ≤ 32 * S := by nlinarith
  let targetCenter : Fin targetBodies.card → Point3 := fun index =>
    targetNormalization.map
      (wz2PaperTubeMidpoint
        (anisotropicPaperTargetTube g c d m center targetDelta hcd hm
          (sourceFine.tube (targetIndex index))))
  have htargetBody : ∀ index,
      JohnEllipsoid.IsConvexBody (targetBodies.body index).carrier := by
    intro index
    rw [target_body]
    let tube := anisotropicPaperTargetTube g c d m center targetDelta hcd hm
      (sourceFine.tube (targetIndex index))
    let sourceBody := wz2_paper_ordinary_tube_isConvexBody tube htargetDeltaPos
    let homeomorph := targetNormalization.map.toHomeomorphOfFiniteDimensional
    refine ⟨sourceBody.1.affine_image targetNormalization.map.toAffineMap, ?_, ?_⟩
    · change IsCompact (homeomorph '' tube.carrier)
      exact (homeomorph.isCompact_image).2 sourceBody.2.1
    · change (interior (homeomorph '' tube.carrier)).Nonempty
      rw [← homeomorph.image_interior]
      exact sourceBody.2.2.image homeomorph
  have htargetBound : ∀ index,
      (targetBodies.body index).carrier ⊆
        Metric.closedBall (0 : Point3) 1 := by
    intro index point hpoint
    rw [target_body] at hpoint
    rcases hpoint with ⟨targetPoint, htargetPoint, rfl⟩
    have hellipsoid :=
      targetNormalization.parent_convex_body.outerJohnEllipsoid_spec.1
        (target_mem_parent index htargetPoint)
    have himage : targetNormalization.map targetPoint ∈
        targetNormalization.map ''
          targetNormalization.parent_convex_body.outerJohnEllipsoid :=
      ⟨targetPoint, hellipsoid, rfl⟩
    rw [targetNormalization.outerJohn_image] at himage
    exact himage
  have hcenter : ∀ index,
      targetCenter index ∈ (targetBodies.body index).carrier := by
    intro index
    rw [target_body]
    change targetNormalization.map
        (wz2PaperTubeMidpoint
          (anisotropicPaperTargetTube g c d m center targetDelta hcd hm
            (sourceFine.tube (targetIndex index)))) ∈ _
    exact ⟨wz2PaperTubeMidpoint
        (anisotropicPaperTargetTube g c d m center targetDelta hcd hm
          (sourceFine.tube (targetIndex index))),
      wz2_paper_tubeMidpoint_mem_carrier _
        htargetDeltaPos.le, rfl⟩
  have hcarrier : ∀ index,
      coordinateChange ''
          ((pureWZ2ActualJohnSourcePacketBodyFamily
            sourceParent sourceFiber.normalization targetBodies
              targetIndex target_mem).body index).carrier ⊆
        AffineMap.homothety (targetCenter index) (32 * S) ''
          (targetBodies.body index).carrier := by
    intro index
    rw [target_body]
    have hordinary :=
      anisotropicCenteredRescalingMap_ordinaryCarrier_image_subset_homothety
        g hg hcd hdc hm hmOne hsub hS center
        (sourceFine.tube (targetIndex index)) hsourceDelta htargetDelta
        (hsourceLine _) (hsourceBase _)
    have hraw := pureWZ2AnisotropicJohnCoordinateChange_carrier
      g center hcd hm sourceFiber.normalization targetNormalization
        (32 * S)
        (wz2PaperTubeMidpoint
          (anisotropicPaperTargetTube g c d m center targetDelta hcd hm
            (sourceFine.tube (targetIndex index))))
        (sourceFine.tube (targetIndex index)).carrier
        (anisotropicPaperTargetTube g c d m center targetDelta hcd hm
          (sourceFine.tube (targetIndex index))).carrier hordinary
    have hsourceIndex :
        ((wz2PaperOrdinaryFullFiberIndexEquiv sourceParent)
          (pureWZ2ActualJohnPacketSourceBodyIndex
            sourceParent targetIndex target_mem index)).1 =
          targetIndex index := by
      simp [pureWZ2ActualJohnPacketSourceBodyIndex]
    simpa only [coordinateChange, targetCenter,
      pureWZ2ActualJohnSourcePacketBodyFamily,
      wz2PaperPureUnitRescaledFullFiberBodyFamily, hsourceIndex] using hraw
  have hresult := pureWZ2_actualJohnPacket_cwa_of_affine_homothetic_envelope
    sourceParent sourceFiber targetBodies targetIndex targetIndex_injective
      target_mem weight K hweightZero hweightTop hcardinality
      coordinateChange (32 * S) 1 hfactor (by norm_num)
      htargetBody htargetBound targetCenter hcenter hcarrier
  simpa [coordinateChange] using hresult

end Kakeya.Assouad

end
