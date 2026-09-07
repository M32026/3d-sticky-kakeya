import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryUpperFiberCardinality
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62UpperMetricFiberEnvelope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ActualJohnToFactorNineteenJohnTransport

/-!
# Proposition 6.2: upper-parent CWA on the ancestry core

This module instantiates equation `prop62-upper-parent-cwa` on the final
genuine metric-parent family.

The public Section 6 relation remains a supporting-line relation.  The
ordinary axial ambiguity is handled by the common physical envelope from
`Prop62UpperMetricFiberEnvelope`, not by replacing complete metric fibers by
assigned or strict ordinary fibers.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Exact contained-count description of one actual-John full-fiber family. -/
theorem wz2PaperPureUnitRescaledFullFiber_containedCount_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (normalization :
      WZ2PaperAssouadUnitRescalingData (coarse.tube parent))
    (convexSet : Set Point3) :
    (wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := fine) (coarse := coarse)
      parent normalization).containedCount convexSet =
      (((wz2PaperOrdinaryFullFiberIndices fine coarse parent).filter
        fun source =>
          normalization.map '' (fine.tube source).carrier ⊆
            convexSet).card : ENNReal) := by
  let fiber :=
    wz2PaperOrdinaryFullFiberIndices fine coarse parent
  let equivalence :=
    wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := fine) (coarse := coarse) parent
  let bodyFamily :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := fine) (coarse := coarse)
      parent normalization
  have imageEq :
      Finset.image
          (fun target => (equivalence target).1)
          (bodyFamily.containedIndices convexSet) =
        fiber.filter fun source =>
          normalization.map '' (fine.tube source).carrier ⊆
            convexSet := by
    ext source
    constructor
    · intro sourceImage
      rcases Finset.mem_image.mp sourceImage with
        ⟨target, targetMem, rfl⟩
      have contained :=
        (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mp
          targetMem
      exact
        Finset.mem_filter.mpr
          ⟨(equivalence target).2, contained⟩
    · intro sourceMem
      rcases Finset.mem_filter.mp sourceMem with
        ⟨sourceFiber, sourceContained⟩
      let member : {source : Fin fine.card // source ∈ fiber} :=
        ⟨source, sourceFiber⟩
      let target := equivalence.symm member
      refine
        Finset.mem_image.mpr
          ⟨target, ?_, congrArg Subtype.val
            (equivalence.apply_symm_apply member)⟩
      apply
        (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mpr
      change
        normalization.map ''
            (fine.tube (equivalence target).1).carrier ⊆
          convexSet
      simpa [target, member] using sourceContained
  unfold Kakeya.Streamlined.BodyFamily.containedCount
  rw [← imageEq]
  norm_cast
  exact
    (Finset.card_image_of_injective
      (bodyFamily.containedIndices convexSet)
      (by
        intro first second equality
        exact equivalence.injective (Subtype.ext equality))).symm

/-- Affine images preserve a multiplicative volume comparison. -/
theorem volume_affineEquiv_image_le_of_le
    (equivalence : Point3 ≃ᵃ[ℝ] Point3)
    {source target : Set Point3}
    {constant : ENNReal}
    (volumeLe : volume source ≤ constant * volume target) :
    volume (equivalence '' source) ≤
      constant * volume (equivalence '' target) := by
  rw [wz2PaperAffineEquiv_volume_image_eq,
    wz2PaperAffineEquiv_volume_image_eq]
  calc
    ENNReal.ofReal
          |LinearMap.det
            (equivalence.linear : Point3 →ₗ[ℝ] Point3)| *
        volume source ≤
      ENNReal.ofReal
          |LinearMap.det
            (equivalence.linear : Point3 →ₗ[ℝ] Point3)| *
        (constant * volume target) := by
      gcongr
    _ =
      constant *
        (ENNReal.ofReal
            |LinearMap.det
              (equivalence.linear : Point3 →ₗ[ℝ] Point3)| *
          volume target) := by
      ring

namespace PureWZ2Prop62AncestryMetricPreliminaryOutput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow}
    {scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {coordinateCount : ℕ}
    {Color : Fin coordinateCount → Type*}
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    {color : ∀ coordinate, Fin fine.card → Color coordinate}
    {weight : Fin fine.card → ENNReal}
    {preliminary :
      PureWZ2Prop62AncestryPreliminarySelectionData
        schedule scheduled rho width packetCoordinate
        Color color weight}
    {M : ℝ}
    (output :
      PureWZ2Prop62AncestryMetricPreliminaryOutput
        schedule scheduled width packetCoordinate
        Color color weight preliminary M)

def finalUpperParentBodyConstant : ENNReal :=
  (185193 : ENNReal) * (212776173 : ENNReal) *
    output.ancestryDensityLoss *
      output.finalCoreConstant * 2

noncomputable def finalUpperNormalization
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ ancestryCoordinate :
          schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate ancestryCoordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate)
    (parent :
      Fin
        (output.finalUpperCoverData
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate
          |>.selectedParents.family.card)) :
    WZ2PaperAssouadUnitRescalingData
      (output.finalUpperCoverData
        coordinates rhoPos widthPos packetScaleLeRho
        sixWidthLe allAncestryCoordinatesUpper coordinate
        |>.selectedParents.family.tube parent) :=
  WZ2PaperAssouadUnitRescalingData.ofTube _
    (by
      exact mul_pos (by norm_num)
        (output.finalOldScaleData coordinate.1).rho_pos)

noncomputable def finalUpperOldFiberData
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ ancestryCoordinate :
          schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate ancestryCoordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate)
    (parent :
      Fin
        (output.finalUpperCoverData
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate
          |>.selectedParents.family.card)) :
    WZ2PaperPureUnitRescaledFullFiberData
      (fine :=
        output.finalMetricRestriction.fineSelected.family)
      (coarse :=
        (output.finalOldScaleData coordinate.1).coarse)
      (output.finalUpperOldParentIndex
        coordinates rhoPos widthPos packetScaleLeRho
        sixWidthLe allAncestryCoordinatesUpper coordinate parent)
      output.finalCoreConstant :=
  Classical.choice <|
    (output.finalOldScaleData coordinate.1).rescaledFiber
      (output.finalUpperOldParentIndex
        coordinates rhoPos widthPos packetScaleLeRho
        sixWidthLe allAncestryCoordinatesUpper coordinate parent)

theorem finalUpperParentFiberCWA
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ ancestryCoordinate :
          schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate ancestryCoordinate))
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.finalMetricRestriction.fineSelected.family.tube
          source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (coordinate : schedule.UpperCoordinate rho packetCoordinate)
    (parent :
      Fin
        (output.finalUpperCoverData
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate
          |>.selectedParents.family.card)) :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine :=
          output.finalMetricRestriction.coarseSelected.family)
        (coarse :=
          (output.finalUpperCoverData
            coordinates rhoPos widthPos packetScaleLeRho
            sixWidthLe allAncestryCoordinatesUpper coordinate
            |>.selectedParents.family))
        parent
        (output.finalUpperNormalization
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate parent))
      output.finalUpperParentBodyConstant := by
  intro targetConvexSet targetConvex
  let upperCover :=
    output.finalUpperCoverData
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate
  let targetJohn :=
    output.finalUpperNormalization
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate parent
  let oldParent :=
    output.finalUpperOldParentIndex
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate parent
  let oldFiber :=
    output.finalUpperOldFiberData
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate parent
  let targetBody :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine :=
        output.finalMetricRestriction.coarseSelected.family)
      (coarse := upperCover.selectedParents.family)
      parent targetJohn
  let activeChildren :=
    output.finalUpperChildrenFiber
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate parent
  let containedChildren : Finset
      (Fin output.finalMetricRestriction.coarseSelected.family.card) :=
    activeChildren.filter fun child =>
      targetJohn.map ''
          (output.finalMetricRestriction.coarseSelected.family.tube
            child).carrier ⊆
        targetConvexSet
  have targetCount :
      targetBody.containedCount targetConvexSet =
        (containedChildren.card : ENNReal) := by
    rw [wz2PaperPureUnitRescaledFullFiber_containedCount_eq]
    congr 1
  by_cases containedNonempty : containedChildren.Nonempty
  · let physicalConvexSet : Set Point3 :=
      targetJohn.map.symm '' targetConvexSet
    have physicalConvex : Convex ℝ physicalConvexSet := by
      dsimp only [physicalConvexSet]
      exact
        targetConvex.affine_image
          (targetJohn.map.symm : Point3 →ᵃ[ℝ] Point3)
    have selectedPhysical :
        ∀ child ∈ containedChildren,
          (output.finalMetricRestriction.coarseSelected.family.tube
            child).carrier ⊆ physicalConvexSet := by
      intro child childMem point pointMem
      have childContained :=
        (Finset.mem_filter.mp childMem).2
          ⟨point, pointMem, rfl⟩
      refine
        ⟨targetJohn.map point, childContained, ?_⟩
      simp
    rcases
        pureWZ2_prop62_metric_children_common_envelope
          (schedule.scaleData packetCoordinate).delta_pos
          rhoPos scaleGap
          output.finalMetricRestriction.section6Cover
          fineAxisBox
          output.finalMetricParents_centered
          containedChildren containedNonempty
          physicalConvexSet physicalConvex selectedPhysical
      with
      ⟨physicalEnvelope, physicalEnvelopeConvex,
        physicalEnvelopeVolume, physicalEnvelopeContains⟩
    let sourceConvexSet : Set Point3 :=
      oldFiber.normalization.map '' physicalEnvelope
    have sourceConvex : Convex ℝ sourceConvexSet := by
      dsimp only [sourceConvexSet]
      exact
        physicalEnvelopeConvex.affine_image
          (oldFiber.normalization.map : Point3 →ᵃ[ℝ] Point3)
    let containedLeaves :=
      (output.finalUpperOldLeafFiber
        coordinates rhoPos widthPos packetScaleLeRho
        sixWidthLe allAncestryCoordinatesUpper coordinate parent).filter
          fun leaf =>
            oldFiber.normalization.map ''
                (output.finalMetricRestriction.fineSelected.family.tube
                  leaf).carrier ⊆
              sourceConvexSet
    have containedLeavesCWA :
        (containedLeaves.card : ENNReal) ≤
          output.finalCoreConstant *
            volume sourceConvexSet *
            ((output.finalUpperOldLeafFiber
              coordinates rhoPos widthPos packetScaleLeRho
              sixWidthLe allAncestryCoordinatesUpper coordinate
              parent).card : ENNReal) := by
      have raw :=
        oldFiber.convex_wolff sourceConvexSet sourceConvex
      rw [wz2PaperPureUnitRescaledFullFiber_containedCount_eq]
        at raw
      exact raw
    have ownerAgreement :
        ∀ leaf,
          output.finalMetricRestriction.section6Cover.toWZ1PaperTubeCover.parent
              leaf =
            output.finalMetricRestriction.lineCover.parent leaf := by
      intro leaf
      exact
        (output.finalMetricRestriction.section6Cover.toWZ1PaperTubeCover
          |>.parent_unique
            leaf
            (output.finalMetricRestriction.lineCover.parent leaf)
            (output.finalMetricRestriction.lineCover.parent_covers
              leaf)).symm
    have packetContainment :
        ∀ leaf ∈
            output.finalUpperOldLeafFiber
              coordinates rhoPos widthPos packetScaleLeRho
              sixWidthLe allAncestryCoordinatesUpper coordinate parent,
          output.finalMetricRestriction.lineCover.parent leaf ∈
              containedChildren →
            leaf ∈ containedLeaves := by
      intro leaf leafMem ownerMem
      apply Finset.mem_filter.mpr
      refine ⟨leafMem, ?_⟩
      apply Set.image_mono
      apply physicalEnvelopeContains leaf
      rwa [ownerAgreement leaf]
    have fiberFloor :
        ∀ child ∈ activeChildren,
          (output.metricFiberCardinalityBin.fiberFloor : ENNReal) ≤
            output.ancestryDensityLoss *
              (((output.finalUpperOldLeafFiber
                coordinates rhoPos widthPos packetScaleLeRho
                sixWidthLe allAncestryCoordinatesUpper coordinate parent
                ).filter fun leaf =>
                  output.finalMetricRestriction.lineCover.parent leaf =
                    child).card : ENNReal) := by
      intro child childMem
      rw [output.finalUpperOldLeafFiber_filter_eq_metricFiber
        coordinates rhoPos widthPos packetScaleLeRho
        sixWidthLe allAncestryCoordinatesUpper coordinate parent
        child childMem]
      exact
        output.fiberFloor_le_ancestryDensityLoss_finalMetricFiber
          rhoPos widthPos packetScaleLeRho sixWidthLe
          schedule.parent_covers allAncestryCoordinatesUpper child
    have selectedUpperNat :=
      output.finalUpperOldLeafFiber_card_le
        coordinates rhoPos widthPos packetScaleLeRho
        sixWidthLe allAncestryCoordinatesUpper coordinate parent
    have selectedUpper :
        ((output.finalUpperOldLeafFiber
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate parent).card :
          ENNReal) ≤
        (2 : ENNReal) *
          (output.metricFiberCardinalityBin.fiberFloor : ENNReal) *
          (activeChildren.card : ENNReal) := by
      exact_mod_cast selectedUpperNat
    have counted :=
      pureWZ2_prop62_upper_parent_cwa_scaled_floor
        output.finalMetricRestriction.lineCover.parent
        (output.finalUpperOldLeafFiber
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate parent)
        activeChildren containedChildren containedLeaves
        output.metricFiberCardinalityBin.fiberFloor
        output.metricFiberCardinalityBin.fiberFloor_pos
        output.ancestryDensityLoss
        (Finset.filter_subset _ _)
        fiberFloor packetContainment
        ((output.finalUpperOldLeafFiber
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate parent).card :
          ENNReal)
        1 2 output.finalCoreConstant
        (volume sourceConvexSet)
        containedLeavesCWA
        (by simp)
        selectedUpper
    have targetEnvelopeVolume :
        volume (targetJohn.map '' physicalEnvelope) ≤
          (212776173 : ENNReal) *
            volume targetConvexSet := by
      have transported :=
        volume_affineEquiv_image_le_of_le
          targetJohn.map physicalEnvelopeVolume
      have physicalImage :
          targetJohn.map '' physicalConvexSet =
            targetConvexSet := by
        ext point
        constructor
        · rintro ⟨source, ⟨target, targetMem, rfl⟩, rfl⟩
          simpa using targetMem
        · intro pointMem
          refine
            ⟨targetJohn.map.symm point,
              ⟨point, pointMem, rfl⟩, ?_⟩
          simp
      rwa [physicalImage] at transported
    have sourceTargetImage :
        sourceConvexSet =
          (wz2PaperFactorNineteenJohnCoordinateChange
            oldFiber.normalization targetJohn).symm ''
            (targetJohn.map '' physicalEnvelope) := by
      let change :=
        wz2PaperFactorNineteenJohnCoordinateChange
          oldFiber.normalization targetJohn
      ext point
      constructor
      · rintro ⟨physicalPoint, physicalMem, rfl⟩
        refine
          ⟨targetJohn.map physicalPoint,
            ⟨physicalPoint, physicalMem, rfl⟩, ?_⟩
        apply change.injective
        rw [change.apply_symm_apply]
        exact
          wz2PaperFactorNineteenJohnCoordinateChange_apply_map
            oldFiber.normalization targetJohn physicalPoint |>.symm
      · rintro
          ⟨targetPoint, ⟨physicalPoint, physicalMem, targetEq⟩,
            pointEq⟩
        refine ⟨physicalPoint, physicalMem, ?_⟩
        rw [← pointEq, ← targetEq]
        apply change.injective
        rw [change.apply_symm_apply]
        exact
          wz2PaperFactorNineteenJohnCoordinateChange_apply_map
            oldFiber.normalization targetJohn physicalPoint
    have sourceVolume :
        volume sourceConvexSet ≤
          ((185193 : ENNReal) * 212776173) *
            volume targetConvexSet := by
      rw [sourceTargetImage]
      exact
        (wz2PaperFactorNineteenJohnCoordinateChange_inverse_volume
          (output.finalOldScaleData coordinate.1).rho_pos
          ((output.finalOldScaleData coordinate.1).coarse.tube
            oldParent)
          (upperCover.selectedParents.family.tube parent)
          oldFiber.normalization targetJohn
          (targetJohn.map '' physicalEnvelope)).trans <| by
            calc
              (185193 : ENNReal) *
                    volume (targetJohn.map '' physicalEnvelope) ≤
                  (185193 : ENNReal) *
                    ((212776173 : ENNReal) *
                      volume targetConvexSet) := by
                gcongr
              _ =
                  ((185193 : ENNReal) * 212776173) *
                    volume targetConvexSet := by ring
    rw [targetCount]
    exact counted.trans <| by
      simp only [finalUpperParentBodyConstant]
      have activeCard :
          targetBody.enncard = (activeChildren.card : ENNReal) := by
        rfl
      rw [activeCard]
      calc
        (((output.ancestryDensityLoss *
              output.finalCoreConstant) * 1 * 2) *
            volume sourceConvexSet *
            (activeChildren.card : ENNReal)) ≤
          (((output.ancestryDensityLoss *
              output.finalCoreConstant) * 1 * 2) *
            (((185193 : ENNReal) * 212776173) *
              volume targetConvexSet) *
            (activeChildren.card : ENNReal)) := by
          gcongr
        _ =
          ((185193 : ENNReal) * 212776173 *
              output.ancestryDensityLoss *
                output.finalCoreConstant * 2) *
            volume targetConvexSet *
            (activeChildren.card : ENNReal) := by
          ring
  · have containedEmpty : containedChildren = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp containedNonempty
    rw [targetCount, containedEmpty]
    simp

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
