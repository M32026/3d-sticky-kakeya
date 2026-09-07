import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.JohnVariableHomotheticEnvelope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingFiberRegularization
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12BodyReindex
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingBridge
import Mathlib.Analysis.Convex.Measure

/-!
# Bounded-fiber actual-body CWA for Proposition 6.3

This is the finite counting and outer-John step in the mild-rescaling lemma
used at the end of Proposition 6.3.  Target bodies may map many-to-one to
source bodies, but the multiplicity is explicit.  If a target body lies in a
convex test set, the corresponding transformed source body lies in a
controlled homothetic copy of that target body.  One outer-John envelope
contains all such copies, and the source actual-body CWA then gives the
target estimate.

No ordinary tube carrier is substituted for an actual John-normalized body.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Metric Set

attribute [local instance] Classical.propDecidable

/-- Coordinate change from a source full-fiber John chart to the target
full-fiber John chart after the common isotropic dilation. -/
noncomputable def proposition63MildRescalingJohnCoordinateChange
    {sourceRho scale targetRho : ℝ}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    (sourceParent : Fin sourceCoarse.card)
    (sourceNormalization : WZ2PaperAssouadUnitRescalingData
      (sourceCoarse.tube sourceParent))
    {targetCoarse : Kakeya.Streamlined.TubeFamily targetRho}
    (targetParent : Fin targetCoarse.card)
    (targetNormalization : WZ2PaperAssouadUnitRescalingData
      (targetCoarse.tube targetParent))
    (center : Point3) (hscale : 0 < scale) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  sourceNormalization.map.symm.trans <|
    (proposition63IsotropicAffineEquiv center scale hscale).trans
      targetNormalization.map

@[simp] theorem proposition63MildRescalingJohnCoordinateChange_apply_map
    {sourceRho scale targetRho : ℝ}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    (sourceParent : Fin sourceCoarse.card)
    (sourceNormalization : WZ2PaperAssouadUnitRescalingData
      (sourceCoarse.tube sourceParent))
    {targetCoarse : Kakeya.Streamlined.TubeFamily targetRho}
    (targetParent : Fin targetCoarse.card)
    (targetNormalization : WZ2PaperAssouadUnitRescalingData
      (targetCoarse.tube targetParent))
    (center : Point3) (hscale : 0 < scale) (point : Point3) :
    proposition63MildRescalingJohnCoordinateChange sourceParent
        sourceNormalization targetParent targetNormalization center hscale
        (sourceNormalization.map point) =
      targetNormalization.map
        (proposition63IsotropicAffineEquiv center scale hscale point) := by
  simp [proposition63MildRescalingJohnCoordinateChange,
    AffineEquiv.trans_apply]

/-- Physical homothetic containment transports through the target John
normalization without changing the homothety factor. -/
theorem proposition63_targetNormalization_image_homothety
    {targetRho : ℝ}
    {targetCoarse : Kakeya.Streamlined.TubeFamily targetRho}
    (targetParent : Fin targetCoarse.card)
    (targetNormalization : WZ2PaperAssouadUnitRescalingData
      (targetCoarse.tube targetParent))
    (physicalCenter : Point3) (factor : ℝ) (set : Set Point3) :
    targetNormalization.map ''
        (AffineMap.homothety physicalCenter factor '' set) =
      AffineMap.homothety (targetNormalization.map physicalCenter) factor ''
        (targetNormalization.map '' set) := by
  ext point
  constructor
  · rintro ⟨physicalPoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
    refine ⟨targetNormalization.map sourcePoint,
      ⟨sourcePoint, hsourcePoint, rfl⟩, ?_⟩
    simp only [AffineMap.homothety_apply]
    rw [targetNormalization.map.map_vadd,
      targetNormalization.map.linear.map_smul]
    exact congrArg
      (fun vector => factor • vector +ᵥ
        targetNormalization.map physicalCenter)
      (targetNormalization.map.toAffineMap.linearMap_vsub
        sourcePoint physicalCenter).symm
  · rintro ⟨normalizedPoint, ⟨sourcePoint, hsourcePoint, rfl⟩, heq⟩
    refine ⟨AffineMap.homothety physicalCenter factor sourcePoint,
      ⟨sourcePoint, hsourcePoint, rfl⟩, ?_⟩
    rw [AffineMap.homothety_apply]
    rw [targetNormalization.map.map_vadd,
      targetNormalization.map.linear.map_smul]
    have hlinear := targetNormalization.map.toAffineMap.linearMap_vsub
      sourcePoint physicalCenter
    exact hlinear ▸ heq

/-- Transfer normalized body CWA through a bounded-to-one index map and one
affine homothetic envelope.  The separate `cardinalityFactor` records the
ratio between the complete source and target fibers; `multiplicity` records
the number of target children that can come from one source body. -/
theorem proposition63_bodyCWA_of_bounded_fiber_affine_homothetic_envelope
    {source target : Kakeya.Streamlined.BodyFamily}
    (coordinateChange : Point3 ≃ᵃ[ℝ] Point3)
    (sourceIndex : Fin target.card → Fin source.card)
    (multiplicity : ℕ)
    (hsourceIndexFiber : ∀ sourceBody : Fin source.card,
      ((Finset.univ : Finset (Fin target.card)).filter
        (fun targetBody => sourceIndex targetBody = sourceBody)).card ≤
          multiplicity)
    (cardinalityFactor : ENNReal)
    (hcardinality :
      source.enncard ≤ cardinalityFactor * target.enncard)
    (factor radius : ℝ)
    (hfactor : 1 ≤ factor)
    (hradius : 0 ≤ radius)
    (htargetBody : ∀ index,
      JohnEllipsoid.IsConvexBody (target.body index).carrier)
    (htargetBound : ∀ index,
      (target.body index).carrier ⊆
        Metric.closedBall (0 : Point3) radius)
    (center : Fin target.card → Point3)
    (hcenter : ∀ index, center index ∈ (target.body index).carrier)
    (hcarrier : ∀ index,
      coordinateChange '' (source.body (sourceIndex index)).carrier ⊆
        AffineMap.homothety (center index) factor ''
          (target.body index).carrier)
    {sourceConstant : ENNReal}
    (hsource : WZ2PaperBodyConvexWolffBound source sourceConstant) :
    WZ2PaperBodyConvexWolffBound target
      (((multiplicity : ENNReal) *
          ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
          ENNReal.ofReal
            |LinearMap.det
              (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| *
          cardinalityFactor) * sourceConstant) := by
  intro targetSet htargetConvex
  by_cases heligible : ∃ index : Fin target.card,
      (target.body index).carrier ⊆ targetSet
  · rcases heligible with ⟨eligible, heligible⟩
    let boundedTarget :=
      targetSet ∩ Metric.closedBall (0 : Point3) radius
    let body := closure boundedTarget
    have hballConvex :
        Convex ℝ (Metric.closedBall (0 : Point3) radius) :=
      convex_closedBall (0 : Point3) radius
    have hboundedConvex : Convex ℝ boundedTarget :=
      htargetConvex.inter hballConvex
    have hbodyConvex : Convex ℝ body := hboundedConvex.closure
    have hbodyCompact : IsCompact body := by
      apply Metric.isCompact_of_isClosed_isBounded isClosed_closure
      exact (Metric.isBounded_closedBall.subset fun point hpoint =>
        closure_minimal (fun _ h => h.2) Metric.isClosed_closedBall hpoint)
    have heligibleBody : (target.body eligible).carrier ⊆ body := by
      intro point hpoint
      exact subset_closure ⟨heligible hpoint, htargetBound eligible hpoint⟩
    have hbodyInterior : (interior body).Nonempty := by
      rcases (htargetBody eligible).2.2 with ⟨point, hpoint⟩
      exact ⟨point, interior_mono heligibleBody hpoint⟩
    have hbody : JohnEllipsoid.IsConvexBody body :=
      ⟨hbodyConvex, hbodyCompact, hbodyInterior⟩
    rcases john_variable_homothetic_envelope body hbody factor hfactor with
      ⟨targetEnvelope, htargetEnvelopeConvex, htargetEnvelopeVolume,
        htargetEnvelope⟩
    let sourceEnvelope := coordinateChange.symm '' targetEnvelope
    have hsourceEnvelopeConvex : Convex ℝ sourceEnvelope :=
      Convex.affine_image coordinateChange.symm.toAffineMap
        htargetEnvelopeConvex
    have hbodyVolume : volume body ≤ volume targetSet := by
      have hbodySubset : body ⊆ closure targetSet :=
        closure_mono fun _ hpoint => hpoint.1
      have hfrontier : volume (frontier targetSet) = 0 :=
        Convex.addHaar_frontier volume htargetConvex
      calc
        volume body ≤ volume (closure targetSet) := measure_mono hbodySubset
        _ = volume targetSet := measure_closure_of_null_frontier hfrontier
    have hsourceEnvelopeVolume : volume sourceEnvelope ≤
        (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
          ENNReal.ofReal
            |LinearMap.det
              (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)|) *
          volume targetSet := by
      rw [wz2PaperAffineEquiv_volume_image_eq]
      calc
        ENNReal.ofReal
              |LinearMap.det
                (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| *
            volume targetEnvelope ≤
          ENNReal.ofReal
              |LinearMap.det
                (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| *
            (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
              volume body) := by gcongr
        _ ≤ ENNReal.ofReal
              |LinearMap.det
                (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| *
            (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
              volume targetSet) := by gcongr
        _ = (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
              ENNReal.ofReal
                |LinearMap.det
                  (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)|) *
              volume targetSet := by ring
    let targetContained := target.containedIndices targetSet
    let sourceContained := source.containedIndices sourceEnvelope
    have hmaps : ∀ targetIndex ∈ targetContained,
        sourceIndex targetIndex ∈ sourceContained := by
      intro targetIndex htargetIndex
      apply Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mpr
      intro sourcePoint hsourcePoint
      have htargetSubset : (target.body targetIndex).carrier ⊆ body := by
        intro point hpoint
        exact subset_closure ⟨
          (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mp
            htargetIndex) hpoint,
          htargetBound targetIndex hpoint⟩
      have hcenterBody : center targetIndex ∈ body :=
        htargetSubset (hcenter targetIndex)
      have himageHomothetic : coordinateChange sourcePoint ∈
          AffineMap.homothety (center targetIndex) factor '' body :=
        Set.image_mono htargetSubset
          (hcarrier targetIndex ⟨sourcePoint, hsourcePoint, rfl⟩)
      have himage : coordinateChange sourcePoint ∈ targetEnvelope :=
        htargetEnvelope (center targetIndex) hcenterBody himageHomothetic
      exact ⟨coordinateChange sourcePoint, himage,
        coordinateChange.symm_apply_apply sourcePoint⟩
    have hcountNat : targetContained.card ≤
        multiplicity * sourceContained.card := by
      have hpartition : targetContained.card =
          ∑ sourceBody ∈ sourceContained,
            (targetContained.filter
              (fun targetBody => sourceIndex targetBody = sourceBody)).card :=
        Finset.card_eq_sum_card_fiberwise
          (by intro targetIndex htargetIndex; exact hmaps targetIndex htargetIndex)
      rw [hpartition]
      calc
        (∑ sourceBody ∈ sourceContained,
            (targetContained.filter
              (fun targetBody => sourceIndex targetBody = sourceBody)).card) ≤
            ∑ _sourceBody ∈ sourceContained, multiplicity := by
          apply Finset.sum_le_sum
          intro sourceBody _
          exact (Finset.card_le_card (by
            intro targetBody htargetBody
            simp only [Finset.mem_filter] at htargetBody ⊢
            exact ⟨Finset.mem_univ _, htargetBody.2⟩)).trans
                (hsourceIndexFiber sourceBody)
        _ = multiplicity * sourceContained.card := by
          simp [Finset.sum_const, Nat.mul_comm]
    have hcount : target.containedCount targetSet ≤
        (multiplicity : ENNReal) *
          source.containedCount sourceEnvelope := by
      change (targetContained.card : ENNReal) ≤
        (multiplicity : ENNReal) * (sourceContained.card : ENNReal)
      exact_mod_cast hcountNat
    calc
      target.containedCount targetSet ≤
          (multiplicity : ENNReal) *
            source.containedCount sourceEnvelope := hcount
      _ ≤ (multiplicity : ENNReal) *
            (sourceConstant * volume sourceEnvelope * source.enncard) := by
        gcongr
        exact hsource sourceEnvelope hsourceEnvelopeConvex
      _ ≤ (multiplicity : ENNReal) *
            (sourceConstant *
              ((ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
                ENNReal.ofReal
                  |LinearMap.det
                    (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)|) *
                volume targetSet) *
              (cardinalityFactor * target.enncard)) := by
        gcongr
      _ = (((multiplicity : ENNReal) *
              ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
              ENNReal.ofReal
                |LinearMap.det
                  (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| *
              cardinalityFactor) * sourceConstant) *
            volume targetSet * target.enncard := by
        ring
  · have htargetCount : target.containedCount targetSet = 0 := by
      change ((target.containedIndices targetSet).card : ENNReal) = 0
      norm_cast
      apply Nat.eq_zero_of_not_pos
      intro hpositive
      rcases Finset.card_pos.mp hpositive with ⟨index, hindex⟩
      exact heligible ⟨index,
        Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mp hindex⟩
    rw [htargetCount]
    exact bot_le

/-- Package the bounded-fiber envelope theorem as genuine target
actual-John full-fiber data.  Both body families below are the canonical
Definition 2.12 families; the caller only supplies their finite index map,
its multiplicity/cardinality bounds, and the geometric comparison between
the two normalized bodies. -/
theorem proposition63_actualJohnFullFiber_of_bounded_source
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
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
    (htargetDelta : 0 < targetDelta)
    (targetNormalization : WZ2PaperAssouadUnitRescalingData
      (targetCoarse.tube targetParent))
    (sourceBodyIndex :
      Fin (wz2PaperOrdinaryFullFiberIndices
        targetFine targetCoarse targetParent).card →
      Fin (wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent).card)
    (multiplicity : ℕ)
    (hsourceBodyIndexFiber : ∀ sourceBody,
      ((Finset.univ : Finset
          (Fin (wz2PaperOrdinaryFullFiberIndices
            targetFine targetCoarse targetParent).card)).filter
        (fun targetBody => sourceBodyIndex targetBody = sourceBody)).card ≤
          multiplicity)
    (cardinalityFactor : ENNReal)
    (hcardinality :
      ((wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent).card : ENNReal) ≤
        cardinalityFactor *
          ((wz2PaperOrdinaryFullFiberIndices
            targetFine targetCoarse targetParent).card : ENNReal))
    (coordinateChange : Point3 ≃ᵃ[ℝ] Point3)
    (factor : ℝ)
    (hfactor : 1 ≤ factor)
    (hcarrier : ∀ index,
      coordinateChange ''
          ((wz2PaperPureUnitRescaledFullFiberBodyFamily
            (fine := sourceFine) (coarse := sourceCoarse)
            sourceParent sourceFiber.normalization).body
              (sourceBodyIndex index)).carrier ⊆
        AffineMap.homothety
            (targetNormalization.map
              (wz2PaperTubeMidpoint
                (targetFine.tube
                  ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
                    index).1)))
            factor ''
          ((wz2PaperPureUnitRescaledFullFiberBodyFamily
            (fine := targetFine) (coarse := targetCoarse)
            targetParent targetNormalization).body index).carrier) :
    Nonempty (WZ2PaperPureUnitRescaledFullFiberData
      (fine := targetFine) (coarse := targetCoarse) targetParent
      (((multiplicity : ENNReal) *
          ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
          ENNReal.ofReal
            |LinearMap.det
              (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| *
          cardinalityFactor) * sourceConstant)) := by
  let sourceBodies := wz2PaperPureUnitRescaledFullFiberBodyFamily
    (fine := sourceFine) (coarse := sourceCoarse)
    sourceParent sourceFiber.normalization
  let targetBodies := wz2PaperPureUnitRescaledFullFiberBodyFamily
    (fine := targetFine) (coarse := targetCoarse)
    targetParent targetNormalization
  let targetCenter : Fin targetBodies.card → Point3 := fun index =>
    targetNormalization.map
      (wz2PaperTubeMidpoint
        (targetFine.tube
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1))
  have htargetBody : ∀ index,
      JohnEllipsoid.IsConvexBody (targetBodies.body index).carrier := by
    intro index
    let tube := targetFine.tube
      ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1
    let tubeBody := wz2_paper_ordinary_tube_isConvexBody tube htargetDelta
    let homeomorph :=
      targetNormalization.map.toHomeomorphOfFiniteDimensional
    refine ⟨tubeBody.1.affine_image
        targetNormalization.map.toAffineMap, ?_, ?_⟩
    · change IsCompact (homeomorph '' tube.carrier)
      exact (homeomorph.isCompact_image).2 tubeBody.2.1
    · change (interior (homeomorph '' tube.carrier)).Nonempty
      rw [← homeomorph.image_interior]
      exact tubeBody.2.2.image homeomorph
  have htargetBound : ∀ index,
      (targetBodies.body index).carrier ⊆
        Metric.closedBall (0 : Point3) 1 := by
    intro index point hpoint
    change point ∈ targetNormalization.map ''
      (targetFine.tube
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1).carrier
        at hpoint
    rcases hpoint with ⟨targetPoint, htargetPoint, rfl⟩
    have htargetInParent : targetPoint ∈
        (targetCoarse.tube targetParent).carrier :=
      (mem_wz2PaperOrdinaryFullFiberIndices_iff targetParent
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1).mp
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).2
          htargetPoint
    have hellipsoid :=
      targetNormalization.parent_convex_body.outerJohnEllipsoid_spec.1
        htargetInParent
    have himage : targetNormalization.map targetPoint ∈
        targetNormalization.map ''
          targetNormalization.parent_convex_body.outerJohnEllipsoid :=
      ⟨targetPoint, hellipsoid, rfl⟩
    rw [targetNormalization.outerJohn_image] at himage
    exact himage
  have htargetCenter : ∀ index,
      targetCenter index ∈ (targetBodies.body index).carrier := by
    intro index
    change targetNormalization.map
        (wz2PaperTubeMidpoint
          (targetFine.tube
            ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1)) ∈
      targetNormalization.map ''
        (targetFine.tube
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1).carrier
    exact ⟨_, wz2_paper_tubeMidpoint_mem_carrier _ htargetDelta.le, rfl⟩
  refine ⟨{
    normalization := targetNormalization
    convex_wolff := ?_
  }⟩
  have hcardinality' :
      sourceBodies.enncard ≤ cardinalityFactor * targetBodies.enncard := by
    change
      ((wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent).card : ENNReal) ≤
        cardinalityFactor *
          ((wz2PaperOrdinaryFullFiberIndices
            targetFine targetCoarse targetParent).card : ENNReal)
    exact hcardinality
  exact proposition63_bodyCWA_of_bounded_fiber_affine_homothetic_envelope
    (source := sourceBodies) (target := targetBodies)
    (coordinateChange := coordinateChange)
    (sourceIndex := sourceBodyIndex)
    (multiplicity := multiplicity)
    (hsourceIndexFiber := hsourceBodyIndexFiber)
    (cardinalityFactor := cardinalityFactor)
    (hcardinality := hcardinality')
    (factor := factor) (radius := 1) hfactor (by norm_num)
    htargetBody htargetBound targetCenter htargetCenter
    (by
      intro index point hpoint
      exact hcarrier index hpoint)
    sourceFiber.convex_wolff

/-- The explicit loss in the source-to-target actual-John transfer for one
final strict fiber. -/
noncomputable def Proposition63MildRescalingFiniteParentScheduleData.actualJohnConstant
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    (data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule)
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (data.selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate => Fin (data.selectedParents selection coordinate).family.card)
      (data.selectedFiberParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin (data.fiberRegularizedParents
      regularized coordinate).family.card) : ENNReal :=
  let sourceScale := (sourceSchedule.witness coordinate).scaleData
  let sourceParent :=
    data.fiberRegularizedSourceParent regularized coordinate targetParent
  let sourceFiber := Classical.choice (sourceScale.rescaledFiber sourceParent)
  let targetNormalization := WZ2PaperAssouadUnitRescalingData.ofTube
    ((data.fiberRegularizedParents regularized coordinate).family.tube
      targetParent)
    (data.parentCover coordinate).target_rho_pos
  let coordinateChange := proposition63MildRescalingJohnCoordinateChange
    sourceParent sourceFiber.normalization targetParent targetNormalization
      center (lt_of_lt_of_le zero_lt_one hscale)
  ENNReal.ofReal (27 * (2 * (22 * scale + 3) - 1) ^ 3) *
    ENNReal.ofReal
      |LinearMap.det (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| *
    ((wz2PaperOrdinaryFullFiberIndices sourceFine sourceScale.coarse
      sourceParent).card : ENNReal) * sourceConstant

/-- Build the actual-John CWA certificate for one final target fiber directly
from the corresponding source fiber.  The target-to-source body map is
injective; the deliberately coarse cardinality factor is the complete source
fiber size and is absorbed later by the Proposition 6.3 parameter hierarchy. -/
theorem Proposition63MildRescalingFiniteParentScheduleData.actualJohnFullFiber
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    (data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule)
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (data.selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate => Fin (data.selectedParents selection coordinate).family.card)
      (data.selectedFiberParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin (data.fiberRegularizedParents
      regularized coordinate).family.card) :
    Nonempty (WZ2PaperPureUnitRescaledFullFiberData
      (fine := (data.fiberRegularizedSubfamily regularized).family)
      (coarse := (data.fiberRegularizedParents regularized coordinate).family)
      targetParent
      (ENNReal.ofReal
            (27 * (2 * (22 * scale + 3) - 1) ^ 3) *
          ENNReal.ofReal
            |LinearMap.det
              ((proposition63MildRescalingJohnCoordinateChange
                (data.fiberRegularizedSourceParent regularized coordinate
                  targetParent)
                (Classical.choice
                  ((sourceSchedule.witness coordinate).scaleData.rescaledFiber
                    (data.fiberRegularizedSourceParent regularized coordinate
                      targetParent))).normalization
                targetParent
                (WZ2PaperAssouadUnitRescalingData.ofTube
                  ((data.fiberRegularizedParents regularized coordinate).family.tube
                    targetParent)
                  (data.parentCover coordinate).target_rho_pos)
                center (lt_of_lt_of_le zero_lt_one hscale)).symm.linear :
                  Point3 →ₗ[ℝ] Point3)| *
          ((wz2PaperOrdinaryFullFiberIndices sourceFine
            (sourceSchedule.witness coordinate).scaleData.coarse
            (data.fiberRegularizedSourceParent regularized coordinate
              targetParent)).card : ENNReal) * sourceConstant)) := by
  let sourceScale := (sourceSchedule.witness coordinate).scaleData
  let targetFine := (data.fiberRegularizedSubfamily regularized).family
  let targetCoarse :=
    (data.fiberRegularizedParents regularized coordinate).family
  let sourceParent :=
    data.fiberRegularizedSourceParent regularized coordinate targetParent
  let sourceFiber := Classical.choice (sourceScale.rescaledFiber sourceParent)
  let targetNormalization := WZ2PaperAssouadUnitRescalingData.ofTube
    (targetCoarse.tube targetParent)
    (data.parentCover coordinate).target_rho_pos
  let targetIndex := wz2PaperOrdinaryFullFiberIndexEquiv
    (fine := targetFine) (coarse := targetCoarse) targetParent
  let sourceIndex := wz2PaperOrdinaryFullFiberIndexEquiv
    (fine := sourceFine) (coarse := sourceScale.coarse) sourceParent
  let sourceTubeIndex : Fin
      (wz2PaperOrdinaryFullFiberIndices targetFine targetCoarse
        targetParent).card ↪ Fin sourceFine.card :=
    { toFun := fun body =>
        (data.selectedTarget selection).embedding
          ((data.fiberRegularizedSubfamily regularized).embedding
            (targetIndex body).1)
      inj' := by
        intro first second heq
        apply targetIndex.injective
        apply Subtype.ext
        apply (data.fiberRegularizedSubfamily regularized).embedding.injective
        exact (data.selectedTarget selection).embedding.injective heq }
  have hsourceTubeMem : ∀ body, sourceTubeIndex body ∈
      wz2PaperOrdinaryFullFiberIndices sourceFine sourceScale.coarse
        sourceParent := by
    intro body
    let targetTube := (targetIndex body).1
    have htargetParent :
        (data.fiberRegularizedCover regularized coordinate).parent
            targetTube = targetParent :=
      ((data.fiberRegularizedCover regularized coordinate)
        |>.mem_fullFiber_iff_parent_eq
          (data.parentCover coordinate).target_rho_pos.le
          targetParent targetTube).mp (targetIndex body).2
    have hsourceParent := data.fiberRegularizedCover_parent_source
      regularized coordinate targetTube
    apply (sourceScale.cover.mem_fullFiber_iff_parent_eq
      sourceScale.rho_pos.le sourceParent (sourceTubeIndex body)).mpr
    have hsourceParent' := hsourceParent
    rw [htargetParent] at hsourceParent'
    simpa [sourceTubeIndex] using hsourceParent'.symm
  let sourceFullIndex : Fin
      (wz2PaperOrdinaryFullFiberIndices targetFine targetCoarse
        targetParent).card ↪
      {source : Fin sourceFine.card // source ∈
        wz2PaperOrdinaryFullFiberIndices sourceFine sourceScale.coarse
          sourceParent} :=
    { toFun := fun body => ⟨sourceTubeIndex body, hsourceTubeMem body⟩
      inj' := by
        intro first second heq
        apply sourceTubeIndex.injective
        simpa only using congrArg Subtype.val heq }
  let sourceBodyIndex : Fin
      (wz2PaperOrdinaryFullFiberIndices targetFine targetCoarse
        targetParent).card ↪
      Fin (wz2PaperOrdinaryFullFiberIndices sourceFine sourceScale.coarse
        sourceParent).card :=
    sourceFullIndex.trans sourceIndex.symm.toEmbedding
  have hsourceBodyIndex_value : ∀ body,
      (sourceIndex (sourceBodyIndex body)).1 = sourceTubeIndex body := by
    intro body
    have heq := sourceIndex.apply_symm_apply (sourceFullIndex body)
    exact congrArg Subtype.val heq
  have hsourceBodyIndexFiber : ∀ sourceBody,
      ((Finset.univ : Finset (Fin
        (wz2PaperOrdinaryFullFiberIndices targetFine targetCoarse
          targetParent).card)).filter
        (fun targetBody => sourceBodyIndex targetBody = sourceBody)).card ≤ 1 := by
    intro sourceBody
    apply Finset.card_le_one.mpr
    intro first hfirst second hsecond
    exact sourceBodyIndex.injective <|
      (Finset.mem_filter.mp hfirst).2.trans
        (Finset.mem_filter.mp hsecond).2.symm
  have htargetFiberNonempty :
      (wz2PaperOrdinaryFullFiberIndices targetFine targetCoarse
        targetParent).Nonempty := by
    let firstCover := data.selectedPartitioningCover selection coordinate
    let selected := data.fiberRegularizedSubfamily regularized
    let parents := firstCover.hitParentIndices selected
    have hparentMem : parents.orderEmbOfFin rfl targetParent ∈ parents :=
      Finset.orderEmbOfFin_mem parents rfl targetParent
    rcases Finset.mem_image.mp hparentMem with
      ⟨source, _hsource, hsourceParent⟩
    refine ⟨source, ?_⟩
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    rw [selected.tube_eq,
      (data.fiberRegularizedParents regularized coordinate).tube_eq]
    change
      ((selectedTarget selection).family.tube
        (selected.embedding source)).carrier ⊆
      ((selectedParents selection coordinate).family.tube
        ((data.fiberRegularizedParents regularized coordinate).embedding
          targetParent)).carrier
    have hsourceFull := firstCover.parent_mem_fullFiber
      (selected.embedding source)
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff] at hsourceFull
    have hparentEq : firstCover.parent (selected.embedding source) =
        (data.fiberRegularizedParents regularized coordinate).embedding
          targetParent := by
      change firstCover.parent (selected.embedding source) =
        parents.orderEmbOfFin rfl targetParent
      exact hsourceParent
    rw [← hparentEq]
    exact hsourceFull
  have hcardinality :
      ((wz2PaperOrdinaryFullFiberIndices sourceFine sourceScale.coarse
        sourceParent).card : ENNReal) ≤
        ((wz2PaperOrdinaryFullFiberIndices sourceFine sourceScale.coarse
          sourceParent).card : ENNReal) *
          ((wz2PaperOrdinaryFullFiberIndices targetFine targetCoarse
            targetParent).card : ENNReal) := by
    calc
      ((wz2PaperOrdinaryFullFiberIndices sourceFine sourceScale.coarse
        sourceParent).card : ENNReal) =
          ((wz2PaperOrdinaryFullFiberIndices sourceFine sourceScale.coarse
            sourceParent).card : ENNReal) * 1 := by simp
      _ ≤ _ * ((wz2PaperOrdinaryFullFiberIndices targetFine targetCoarse
          targetParent).card : ENNReal) := by
        gcongr
        exact_mod_cast Finset.one_le_card.mpr htargetFiberNonempty
  let coordinateChange := proposition63MildRescalingJohnCoordinateChange
    sourceParent sourceFiber.normalization targetParent targetNormalization
      center (lt_of_lt_of_le zero_lt_one hscale)
  have hresult := proposition63_actualJohnFullFiber_of_bounded_source
    sourceParent sourceFiber targetParent
    (mul_pos (lt_of_lt_of_le zero_lt_one hscale) sourceScale.delta_pos)
    targetNormalization sourceBodyIndex 1 hsourceBodyIndexFiber
    ((wz2PaperOrdinaryFullFiberIndices sourceFine sourceScale.coarse
      sourceParent).card : ENNReal) hcardinality coordinateChange
    (22 * scale + 3) (by linarith) (by
      intro body
      let targetTube := (targetIndex body).1
      let sourceTube := sourceTubeIndex body
      change coordinateChange ''
          (sourceFiber.normalization.map ''
            (sourceFine.tube ((sourceIndex (sourceBodyIndex body)).1)).carrier) ⊆
        AffineMap.homothety
          (targetNormalization.map
            (wz2PaperTubeMidpoint (targetFine.tube targetTube)))
          (22 * scale + 3) ''
          (targetNormalization.map '' (targetFine.tube targetTube).carrier)
      have hsourceIndexValue :
          (sourceIndex (sourceBodyIndex body)).1 = sourceTube := by
        exact hsourceBodyIndex_value body
      rw [hsourceIndexValue]
      have hphysical :=
        proposition63_isotropic_source_carrier_subset_target_homothety
          sourceScale.delta_pos hscale raw
          (data.parentCover coordinate).source_line_class
          (data.parentCover coordinate).raw_line_class
          (data.parentCover coordinate).source_midpoint_local
          (data.parentCover coordinate).center_height sourceTube
      have htargetTube : targetFine.tube targetTube =
          (proposition63MildRescalingFamily hscale raw).tube sourceTube := by
        rw [(data.fiberRegularizedSubfamily regularized).tube_eq,
          (data.selectedTarget selection).tube_eq]
        rfl
      rw [htargetTube]
      intro point hpoint
      rcases hpoint with ⟨sourceJohnPoint,
        ⟨physicalPoint, hphysicalPoint, rfl⟩, rfl⟩
      have hphysicalTarget := hphysical ⟨physicalPoint, hphysicalPoint, rfl⟩
      have hnormalizedTarget : targetNormalization.map
          (proposition63IsotropicAffineEquiv center scale
            (lt_of_lt_of_le zero_lt_one hscale) physicalPoint) ∈
          targetNormalization.map ''
            (AffineMap.homothety
              (wz2PaperTubeMidpoint
                ((proposition63MildRescalingFamily hscale raw).tube sourceTube))
              (22 * scale + 3) ''
              ((proposition63MildRescalingFamily hscale raw).tube
                sourceTube).carrier) :=
        ⟨_, hphysicalTarget, rfl⟩
      rw [proposition63_targetNormalization_image_homothety] at hnormalizedTarget
      simpa [coordinateChange,
        proposition63MildRescalingJohnCoordinateChange_apply_map] using
          hnormalizedTarget)
  simpa [sourceScale, sourceParent, sourceFiber, targetCoarse,
    targetNormalization, coordinateChange] using hresult

/-- One finite constant dominating every actual-John transfer in the finite
representative schedule. -/
noncomputable def Proposition63MildRescalingFiniteParentScheduleData.actualJohnScheduleConstant
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    (data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule)
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (data.selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate => Fin (data.selectedParents selection coordinate).family.card)
      (data.selectedFiberParent selection)) : ENNReal :=
  Finset.univ.sup fun coordinate : Fin sourceSchedule.scaleCount =>
    Finset.univ.sup fun parent : Fin
        (data.fiberRegularizedParents regularized coordinate).family.card =>
      data.actualJohnConstant regularized coordinate parent

theorem Proposition63MildRescalingFiniteParentScheduleData.actualJohnConstant_le_schedule
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    (data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule)
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (data.selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate => Fin (data.selectedParents selection coordinate).family.card)
      (data.selectedFiberParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (parent : Fin
      (data.fiberRegularizedParents regularized coordinate).family.card) :
    data.actualJohnConstant regularized coordinate parent ≤
      data.actualJohnScheduleConstant regularized := by
  exact (Finset.le_sup (s := Finset.univ)
    (f := fun parent : Fin
      (data.fiberRegularizedParents regularized coordinate).family.card =>
        data.actualJohnConstant regularized coordinate parent)
    (Finset.mem_univ parent)).trans <|
      Finset.le_sup (s := Finset.univ)
        (f := fun coordinate : Fin sourceSchedule.scaleCount =>
          Finset.univ.sup fun parent : Fin
            (data.fiberRegularizedParents regularized coordinate).family.card =>
              data.actualJohnConstant regularized coordinate parent)
        (Finset.mem_univ coordinate)

end Kakeya.Assouad.PureWZ2

end
