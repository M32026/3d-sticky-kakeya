import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientUpperGeometryConstruction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62UpperMetricFiberEnvelopeBoundedSupport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4Certificate
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4Threshold
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4CleanupReceiptAdapter

/-!
# Bounded-base boundary for the Proposition 6.2 V4 pipeline

The closed metric-parent pipeline historically accepted
`source.IsInUnitBall`.  Inside that proof the hypothesis has only two uses:

* it gives the base bounds `HasBoundedBase source 4` and
  `‖(source.tube index).base‖ ≤ 5`;
* it places the selected fine ordinary carriers in `axisBox 2 2 2` for the
  upper common-envelope construction.

The first use is immediate from `HasBoundedBase source 4`.  The second is
replaced here by the bounded-support geometry in
`Prop62UpperMetricFiberEnvelopeBoundedSupport`, which uses
`axisBox 12 12 12` and preserves the same common-envelope volume constant.

This module deliberately leaves the old axis-box-two construction unchanged.
It supplies a parallel axis-box-twelve upper-geometry seam suitable for a
runtime pipeline whose boundary hypothesis is `HasBoundedBase source 4`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/--
Runtime certificate boundary obtained by replacing the historical
`source.IsInUnitBall` assumption with the normalization invariant
`HasBoundedBase source 4`.
-/
def PureWZ2Prop62MetricParentsV4BoundedBaseRuntimeCertificateProducer : Prop :=
  ∀ (cleanupOracle : PureWZ2Prop62CleanupOracle)
    (A : ℕ) (epsilon eta c0 delta : ℝ)
    (source : Kakeya.Streamlined.TubeFamily delta)
    (shading : WZ1PaperTubeShading source)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (thresholdInput :
      PureWZ2Prop62MetricParentsV4ThresholdInput A epsilon eta c0),
    0 < delta →
    delta ≤ thresholdInput.threshold →
    source.Nonempty →
    HasBoundedBase source 4 →
    WZ1PaperIsLineClass source →
    WZ1PaperIsCubicalShading shading →
    WZ2PaperPureCWAAtNearbyScales source
      (Kakeya.realRpowENN delta (-(A : ℝ) * eta)) →
    shading.IsLambdaDense
      (Kakeya.realRpowENN delta ((A : ℝ) * eta)) →
    Real.rpow delta (1 - epsilon) ≤ rho.1 →
    rho.1 ≤ Real.rpow delta epsilon →
      Nonempty
        (PureWZ2Prop62MetricParentsV4Certificate
          shading rho c0
            (Kakeya.realRpowENN delta
              (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta))
            (Kakeya.realRpowENN delta
              (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta)))

/--
The historical unit-ball runtime boundary, repeated locally so this module
does not depend on the stale paper-facing adapter while its exponent is being
updated elsewhere.
-/
def PureWZ2Prop62MetricParentsV4UnitBallRuntimeCertificateProducer : Prop :=
  ∀ (cleanupOracle : PureWZ2Prop62CleanupOracle)
    (A : ℕ) (epsilon eta c0 delta : ℝ)
    (source : Kakeya.Streamlined.TubeFamily delta)
    (shading : WZ1PaperTubeShading source)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (thresholdInput :
      PureWZ2Prop62MetricParentsV4ThresholdInput A epsilon eta c0),
    0 < delta →
    delta ≤ thresholdInput.threshold →
    source.Nonempty →
    source.IsInUnitBall →
    WZ1PaperIsLineClass source →
    WZ1PaperIsCubicalShading shading →
    WZ2PaperPureCWAAtNearbyScales source
      (Kakeya.realRpowENN delta (-(A : ℝ) * eta)) →
    shading.IsLambdaDense
      (Kakeya.realRpowENN delta ((A : ℝ) * eta)) →
    Real.rpow delta (1 - epsilon) ≤ rho.1 →
    rho.1 ≤ Real.rpow delta epsilon →
      Nonempty
        (PureWZ2Prop62MetricParentsV4Certificate
          shading rho c0
            (Kakeya.realRpowENN delta
              (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta))
            (Kakeya.realRpowENN delta
              (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta)))

/--
A bounded-base runtime producer is a drop-in replacement for the historical
unit-ball producer.  This direction uses unit-ball containment only to derive
the weaker base bound.
-/
theorem
    pureWZ2Prop62_boundedBaseRuntimeCertificateProducer_to_runtimeCertificateProducer
    (produce :
      PureWZ2Prop62MetricParentsV4BoundedBaseRuntimeCertificateProducer) :
    PureWZ2Prop62MetricParentsV4UnitBallRuntimeCertificateProducer := by
  intro cleanupOracle A epsilon eta c0 delta source shading rho
    thresholdInput deltaPos deltaLe sourceNonempty sourceUnitBall
    sourceLine sourceCubical sourceCWA sourceDense rhoLower rhoUpper
  have boundedBaseOne : HasBoundedBase source 1 :=
    hasBoundedBase_of_isInUnitBall deltaPos.le sourceUnitBall
  have boundedBaseFour : HasBoundedBase source 4 := by
    intro sourceIndex
    exact (boundedBaseOne sourceIndex).trans (by norm_num)
  exact
    produce cleanupOracle A epsilon eta c0 delta source shading rho
      thresholdInput deltaPos deltaLe sourceNonempty boundedBaseFour
      sourceLine sourceCubical sourceCWA sourceDense rhoLower rhoUpper

private theorem prop62V4BoundedBase_volume_affineEquiv_image_le_of_le
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

namespace PureWZ2Prop62ProxyQuotientMetricCoreOutput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (output :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    {SourceColor : Type*}
    [Fintype SourceColor] [DecidableEq SourceColor]
    [Nonempty SourceColor]
    {coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {sourceColor : Fin fine.card → SourceColor}
    (adapter :
      PureWZ2Prop62ProxyQuotientPreCoreAdapterData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight output.metric coloring SourceColor sourceColor)
    (preliminary_eq :
      output.cleanup.preliminary =
        adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)

include fineLine rhoPos

/--
The selected fine family inherits the fixed `axisBox 12` support supplied by
the ambient bounded-base source.
-/
theorem upperGeometry_selectedFine_axisBox_twelve
    (deltaNonnegative : 0 ≤ delta)
    (deltaLe : delta ≤ 1 / 100)
    (fineBoundedBase : HasBoundedBase fine 4) :
    ∀ source,
      (output.metric.selectedFine.tube source).carrier ⊆
        Kakeya.Streamlined.axisBox 12 12 12 := by
  intro source
  rw [output.metric.mesh.complete.selectedFine.tube_eq]
  exact
    pureWZ2Prop62_family_carrier_subset_axisBox_twelve
      deltaNonnegative deltaLe fineLine fineBoundedBase
      (output.metric.mesh.complete.selectedFine.embedding source)

/--
Physical common envelope for the quotient upper geometry under the larger
fixed support box forced by `HasBoundedBase fine 4`.
-/
theorem exists_upperGeometryPhysicalEnvelope_axisBox_twelve
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.metric.selectedFine.tube source).carrier ⊆
          Kakeya.Streamlined.axisBox 12 12 12)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (anchor : Fin fine.card)
    (convexSet : Set Point3)
    (convex : Convex ℝ convexSet) :
    ∃ envelope : Set Point3,
      Convex ℝ envelope ∧
      volume envelope ≤
        (212776173 : ENNReal) *
          volume
            ((upperGeometryNormalization
              (schedule := schedule) (quotient := quotient)
              coordinate anchor).map.symm '' convexSet) ∧
      ∀ source,
        output.metric.section6Cover.toWZ1PaperTubeCover.parent source ∈
            upperGeometryContainedMetricParents
              (output := output) (schedule := schedule)
              (quotient := quotient) coordinate anchor convexSet →
          (output.metric.selectedFine.tube source).carrier ⊆ envelope := by
  let normalization :=
    upperGeometryNormalization
      (schedule := schedule) (quotient := quotient) coordinate anchor
  let containedParents :=
    upperGeometryContainedMetricParents
      (output := output) (schedule := schedule)
      (quotient := quotient) coordinate anchor convexSet
  let physicalConvexSet : Set Point3 :=
    normalization.map.symm '' convexSet
  have physicalConvex : Convex ℝ physicalConvexSet :=
    convex.affine_image
      (normalization.map.symm : Point3 →ᵃ[ℝ] Point3)
  by_cases containedNonempty : containedParents.Nonempty
  · have selectedPhysical :
        ∀ parent ∈ containedParents,
          (output.metric.metricParents.tube parent).carrier ⊆
            physicalConvexSet := by
      intro parent parentMem point pointMem
      have parentContained :=
        (Finset.mem_filter.mp parentMem).2
          ⟨point, pointMem, rfl⟩
      exact
        ⟨normalization.map point, parentContained, by simp⟩
    exact
      pureWZ2_prop62_metric_children_common_envelope_of_axisBox_twelve
        (schedule.scaleData coordinate.1).delta_pos
        rhoPos scaleGap output.metric.section6Cover
        fineAxisBox
        (upperGeometry_metricParents_centered
          (output := output) (schedule := schedule)
          (fineNonempty := fineNonempty) fineLine)
        containedParents containedNonempty
        physicalConvexSet physicalConvex selectedPhysical
  · refine ⟨∅, convex_empty, by simp, ?_⟩
    intro source sourceParent
    exact
      (containedNonempty
        ⟨output.metric.section6Cover.toWZ1PaperTubeCover.parent source,
          sourceParent⟩).elim

/-- Total choice of the axis-box-twelve physical common envelope. -/
noncomputable def upperGeometryPhysicalEnvelopeAxisBoxTwelve
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.metric.selectedFine.tube source).carrier ⊆
          Kakeya.Streamlined.axisBox 12 12 12)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (anchor : Fin fine.card)
    (convexSet : Set Point3) : Set Point3 :=
  if convex : Convex ℝ convexSet then
    Classical.choose <|
      exists_upperGeometryPhysicalEnvelope_axisBox_twelve
        (output := output) (schedule := schedule)
        (quotient := quotient) fineLine rhoPos
        scaleGap fineAxisBox coordinate anchor convexSet convex
  else Set.univ

theorem upperGeometryPhysicalEnvelopeAxisBoxTwelve_spec
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.metric.selectedFine.tube source).carrier ⊆
          Kakeya.Streamlined.axisBox 12 12 12)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (anchor : Fin fine.card)
    (convexSet : Set Point3)
    (convex : Convex ℝ convexSet) :
    Convex ℝ
        (upperGeometryPhysicalEnvelopeAxisBoxTwelve
          (output := output) (schedule := schedule)
          (quotient := quotient) fineLine rhoPos
          scaleGap fineAxisBox coordinate anchor convexSet) ∧
      volume
          (upperGeometryPhysicalEnvelopeAxisBoxTwelve
            (output := output) (schedule := schedule)
            (quotient := quotient) fineLine rhoPos
            scaleGap fineAxisBox coordinate anchor convexSet) ≤
        (212776173 : ENNReal) *
          volume
            ((upperGeometryNormalization
              (schedule := schedule) (quotient := quotient)
              coordinate anchor).map.symm '' convexSet) ∧
      ∀ source,
        output.metric.section6Cover.toWZ1PaperTubeCover.parent source ∈
            upperGeometryContainedMetricParents
              (output := output) (schedule := schedule)
              (quotient := quotient) coordinate anchor convexSet →
          (output.metric.selectedFine.tube source).carrier ⊆
            upperGeometryPhysicalEnvelopeAxisBoxTwelve
              (output := output) (schedule := schedule)
              (quotient := quotient) fineLine rhoPos
              scaleGap fineAxisBox coordinate anchor convexSet := by
  rw [upperGeometryPhysicalEnvelopeAxisBoxTwelve, dif_pos convex]
  exact
    Classical.choose_spec <|
      exists_upperGeometryPhysicalEnvelope_axisBox_twelve
        (output := output) (schedule := schedule)
        (quotient := quotient) fineLine rhoPos
        scaleGap fineAxisBox coordinate anchor convexSet convex

/--
The canonical ambient leaf set using the axis-box-twelve physical envelope.
-/
def upperGeometryContainedLeafSetAxisBoxTwelve
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.metric.selectedFine.tube source).carrier ⊆
          Kakeya.Streamlined.axisBox 12 12 12)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (anchor : Fin fine.card)
    (convexSet : Set Point3) :
    Finset (Fin fine.card) :=
  (output.cleanup.auxiliary.prefixNodeAt
      (coordinate.1.1 + 1) anchor).filter fun leaf =>
    (fine.tube leaf).carrier ⊆
      upperGeometryPhysicalEnvelopeAxisBoxTwelve
        (output := output) (schedule := schedule)
        (quotient := quotient) fineLine rhoPos
        scaleGap fineAxisBox coordinate anchor convexSet

/--
Every whole packet over a contained metric child lies in the
axis-box-twelve ambient leaf set.
-/
theorem upperGeometryContainedLeafSetAxisBoxTwelve_contains_packet
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.metric.selectedFine.tube source).carrier ⊆
          Kakeya.Streamlined.axisBox 12 12 12)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (parent : Fin
      (output.finalUpperCover
        (adapter := adapter) (preliminary_eq := preliminary_eq)
        fineLine fineBase rhoPos coordinate).selectedParents.family.card)
    (anchor : Fin fine.card)
    (_anchorMem : anchor ∈ output.cleanup.core.core)
    (convexSet : Set Point3)
    (child : Fin output.metric.metricParents.card)
    (childMem :
      child ∈
        pureWZ2Prop62UpperCoverContainedAmbientFiber
          output.finalMetricParentsSubfamily
          (output.finalUpperCover
            (adapter := adapter) (preliminary_eq := preliminary_eq)
            fineLine fineBase rhoPos coordinate).selectedParents.family
          parent
          (output.finalUpperNormalization
            (adapter := adapter) (preliminary_eq := preliminary_eq)
            fineLine fineBase rhoPos coordinate parent)
          convexSet) :
    ((adapter.preCore.wholeLeaves ∩
      quotient.centerPacketIndices coordinate.1
        (quotient.leafCenter coordinate.1 anchor)).filter
      fun leaf =>
        output.metric.ambientMetricParentOf leaf = child) ⊆
      upperGeometryContainedLeafSetAxisBoxTwelve
        (output := output) (schedule := schedule)
        (quotient := quotient) fineLine rhoPos
        scaleGap fineAxisBox coordinate anchor convexSet := by
  intro leaf leafMem
  have packetData := Finset.mem_filter.mp leafMem
  have leafData := Finset.mem_inter.mp packetData.1
  have anchorWhole :
      anchor ∈ adapter.preCore.wholeLeaves := by
    apply adapter.preCore.preliminary_subset_whole_fibers
    rw [← preliminary_eq]
    exact output.cleanup.core.core_subset _anchorMem
  have centerPrefix :=
    coloring.monochromatic_centerPacket_inter_prefixNode
      fineLine fineBase adapter.preCore.wholeLeaves
      adapter.global.selectedColor
      (fun source sourceMem current =>
        adapter.leaf_monochromatic source
          (by
            rw [adapter.wholeLeaves_eq]
            exact sourceMem)
          current)
      output.cleanup.auxiliary anchor anchorWhole coordinate
  have leafPrefix :
      leaf ∈
        output.cleanup.auxiliary.prefixNodeAt
          (coordinate.1.1 + 1) anchor := by
    have leafIntersection :
        leaf ∈
          adapter.preCore.wholeLeaves ∩
            output.cleanup.auxiliary.prefixNodeAt
              (coordinate.1.1 + 1) anchor := by
      rw [← centerPrefix]
      exact packetData.1
    exact (Finset.mem_inter.mp leafIntersection).2
  have leafCenterEq :
      quotient.leafCenter coordinate.1 leaf =
        quotient.leafCenter coordinate.1 anchor := by
    simpa [
      PureWZ2Prop62ProxyQuotientScheduleData.centerPacketIndices
    ] using leafData.2
  rcases Finset.mem_image.mp childMem with
    ⟨selectedChild, selectedChildMem, childEq⟩
  have childActive :
      child ∈
        pureWZ2Prop62UpperCoverAmbientFiber
          output.finalMetricParentsSubfamily
          (output.finalUpperCover
            (adapter := adapter) (preliminary_eq := preliminary_eq)
            fineLine fineBase rhoPos coordinate).selectedParents.family
          parent :=
    Finset.mem_image.mpr
      ⟨selectedChild, (Finset.mem_filter.mp selectedChildMem).1, childEq⟩
  have parentTubeEq :=
    output.finalUpperParent_tube_eq_upperGeometryEnvelopeTube
      adapter preliminary_eq fineLine fineBase rhoPos
      widthPos packetScaleLeRho sixWidthLe coordinate parent
      anchor leaf leafData.1 leafCenterEq child packetData.2 childActive
  let parentNormalization :=
    output.finalUpperNormalization
      (adapter := adapter) (preliminary_eq := preliminary_eq)
      fineLine fineBase rhoPos coordinate parent
  let anchorNormalization :=
    upperGeometryNormalization
      (schedule := schedule) (quotient := quotient)
      coordinate anchor
  have normalizationMapEq :
      parentNormalization.map = anchorNormalization.map := by
    apply AffineEquiv.ext
    intro point
    simp only [WZ2PaperAssouadUnitRescalingData.map]
    congr
  have childContained :=
    (Finset.mem_filter.mp selectedChildMem).2
  have childContainedAmbient :
      parentNormalization.map ''
          (output.metric.metricParents.tube child).carrier ⊆
        convexSet := by
    rw [← childEq]
    simpa only [output.finalMetricParentsSubfamily.tube_eq] using
      childContained
  have childCanonicalContained :
      child ∈
        upperGeometryContainedMetricParents
          (output := output) coordinate anchor convexSet := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ child, ?_⟩
    rw [← normalizationMapEq]
    exact childContainedAmbient
  have leafSelected :
      leaf ∈ output.metric.mesh.complete.selectedFineIndices := by
    have leafAdapter : leaf ∈ adapter.wholeLeaves := by
      rw [adapter.wholeLeaves_eq]
      exact leafData.1
    have leafGlobal : leaf ∈ adapter.global.wholeLeaves :=
      adapter.wholeLeaves_subset_global leafAdapter
    rw [adapter.global.wholeLeaves_eq] at leafGlobal
    rcases Finset.mem_biUnion.mp leafGlobal with
      ⟨metricParent, _metricParentMem, leafFiber⟩
    exact
      (output.metric.mem_ambientCompleteMetricFiber_iff
        metricParent leaf).mp leafFiber |>.1
  rcases
      output.metric.mesh.complete.selectedFine_ambient_surjective
        leaf leafSelected
    with ⟨selectedSource, selectedSourceEq⟩
  have selectedParent :
      output.metric.section6Cover.toWZ1PaperTubeCover.parent
          selectedSource ∈
        upperGeometryContainedMetricParents
          (output := output) coordinate anchor convexSet := by
    change output.metric.metricParentOf selectedSource ∈ _
    rw [← output.metric.ambientMetricParentOf_embedding, selectedSourceEq,
      packetData.2]
    exact childCanonicalContained
  have sourceContained :=
    if convex : Convex ℝ convexSet then
      (upperGeometryPhysicalEnvelopeAxisBoxTwelve_spec
        (output := output) (schedule := schedule)
        (quotient := quotient) fineLine rhoPos
        scaleGap fineAxisBox coordinate anchor convexSet convex).2.2
        selectedSource selectedParent
    else by
      rw [upperGeometryPhysicalEnvelopeAxisBoxTwelve, dif_neg convex]
      exact Set.subset_univ _
  rw [upperGeometryContainedLeafSetAxisBoxTwelve, Finset.mem_filter]
  refine ⟨leafPrefix, ?_⟩
  rw [output.metric.mesh.complete.selectedFine.tube_eq,
    selectedSourceEq] at sourceContained
  exact sourceContained

/--
The axis-box-twelve contained-leaf set obeys the same ambient packet-count
bound as the historical axis-box-two construction.
-/
theorem upperGeometryContainedLeafSetAxisBoxTwelve_ambient_cwa
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.metric.selectedFine.tube source).carrier ⊆
          Kakeya.Streamlined.axisBox 12 12 12)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (anchor : Fin fine.card)
    (convexSet : Set Point3)
    (convex : Convex ℝ convexSet) :
    ((output.upperGeometryContainedLeafSetAxisBoxTwelve
      fineLine rhoPos scaleGap fineAxisBox
      coordinate anchor convexSet).card : ENNReal) ≤
      ambientConstant *
        (pureWZ2Prop62UpperEnvelopeGeometricLoss *
          volume convexSet) *
        ((output.cleanup.auxiliary.prefixNodeAt
          (coordinate.1.1 + 1) anchor).card : ENNReal) := by
  let oldData := schedule.scaleData coordinate.1
  let activePackets :=
    output.cleanup.auxiliary.prefixActualParents coordinate anchor
  let prefixLeaves :=
    output.cleanup.auxiliary.prefixNodeAt
      (coordinate.1.1 + 1) anchor
  let targetJohn :=
    upperGeometryNormalization
      (schedule := schedule) (quotient := quotient)
      coordinate anchor
  let physicalEnvelope :=
    upperGeometryPhysicalEnvelopeAxisBoxTwelve
      (output := output) (schedule := schedule)
      (quotient := quotient) fineLine rhoPos
      scaleGap fineAxisBox coordinate anchor convexSet
  let predicate : Fin fine.card → Prop :=
    fun leaf => (fine.tube leaf).carrier ⊆ physicalEnvelope
  have envelopeSpec :=
    upperGeometryPhysicalEnvelopeAxisBoxTwelve_spec
      (output := output) (schedule := schedule)
      (quotient := quotient) fineLine rhoPos
      scaleGap fineAxisBox coordinate anchor convexSet convex
  have prefixEq :
      prefixLeaves =
        Finset.univ.filter fun leaf =>
          oldData.cover.parent leaf ∈ activePackets := by
    rw [show prefixLeaves =
        activePackets.biUnion
          (wz2PaperOrdinaryFullFiberIndices fine oldData.coarse) by
      exact
        output.cleanup.auxiliary.prefixNodeAt_eq_actualParent_biUnion
          coordinate anchor]
    ext leaf
    simp only [Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨packet, packetMem, leafMem⟩
      have parentEq :=
        (oldData.cover.mem_fullFiber_iff_parent_eq
          oldData.rho_pos.le packet leaf).mp leafMem
      rwa [parentEq]
    · intro parentMem
      exact
        ⟨oldData.cover.parent leaf, parentMem,
          oldData.cover.parent_mem_fullFiber leaf⟩
  have containedEq :
      output.upperGeometryContainedLeafSetAxisBoxTwelve
          fineLine rhoPos scaleGap fineAxisBox
          coordinate anchor convexSet =
        Finset.univ.filter fun leaf =>
          oldData.cover.parent leaf ∈ activePackets ∧ predicate leaf := by
    rw [upperGeometryContainedLeafSetAxisBoxTwelve]
    change prefixLeaves.filter predicate = _
    rw [prefixEq]
    ext leaf
    simp [and_assoc]
  have targetEnvelopeVolume :
      volume (targetJohn.map '' physicalEnvelope) ≤
        (212776173 : ENNReal) * volume convexSet := by
    have transported :=
      prop62V4BoundedBase_volume_affineEquiv_image_le_of_le
        targetJohn.map envelopeSpec.2.1
    have physicalImage :
        targetJohn.map ''
            (targetJohn.map.symm '' convexSet) =
          convexSet := by
      ext point
      constructor
      · rintro ⟨source, ⟨target, targetMem, rfl⟩, rfl⟩
        simpa using targetMem
      · intro pointMem
        exact
          ⟨targetJohn.map.symm point,
            ⟨point, pointMem, rfl⟩, by simp⟩
    rwa [physicalImage] at transported
  apply
    pureWZ2_prop62_quotientPrefix_packet_sum
      oldData.cover.parent activePackets prefixLeaves
      (output.upperGeometryContainedLeafSetAxisBoxTwelve
        fineLine rhoPos scaleGap fineAxisBox
        coordinate anchor convexSet)
      predicate ambientConstant
      (pureWZ2Prop62UpperEnvelopeGeometricLoss *
        volume convexSet)
      prefixEq containedEq
  intro packet packetMem
  let actualFiber :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine) (coarse := oldData.coarse)
        packet ambientConstant :=
    Classical.choice (oldData.rescaledFiber packet)
  let sourceConvexSet : Set Point3 :=
    actualFiber.normalization.map '' physicalEnvelope
  have sourceConvex : Convex ℝ sourceConvexSet :=
    envelopeSpec.1.affine_image
      (actualFiber.normalization.map : Point3 →ᵃ[ℝ] Point3)
  have raw :=
    actualFiber.convex_wolff sourceConvexSet sourceConvex
  rw [pureWZ2_prop62_quotientUpperFullFiber_containedCount_eq]
    at raw
  have filteredEq :
      (Finset.univ.filter fun leaf =>
          oldData.cover.parent leaf = packet ∧ predicate leaf) =
        (wz2PaperOrdinaryFullFiberIndices
          fine oldData.coarse packet).filter fun leaf =>
            actualFiber.normalization.map ''
                (fine.tube leaf).carrier ⊆
              sourceConvexSet := by
    ext leaf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨parentEq, leafContained⟩
      refine
        ⟨(oldData.cover.mem_fullFiber_iff_parent_eq
            oldData.rho_pos.le packet leaf).mpr parentEq, ?_⟩
      exact
        (Set.image_subset_image_iff
          actualFiber.normalization.map.injective).mpr leafContained
    · rintro ⟨leafMem, leafContained⟩
      exact
        ⟨(oldData.cover.mem_fullFiber_iff_parent_eq
            oldData.rho_pos.le packet leaf).mp leafMem,
          (Set.image_subset_image_iff
            actualFiber.normalization.map.injective).mp leafContained⟩
  have sourceTargetImage :
      sourceConvexSet =
        (wz2PaperGeneralJohnToJohnCoordinateChange
          actualFiber.normalization targetJohn).symm ''
          (targetJohn.map '' physicalEnvelope) := by
    let change :=
      wz2PaperGeneralJohnToJohnCoordinateChange
        actualFiber.normalization targetJohn
    ext point
    constructor
    · rintro ⟨physicalPoint, physicalMem, rfl⟩
      refine
        ⟨targetJohn.map physicalPoint,
          ⟨physicalPoint, physicalMem, rfl⟩, ?_⟩
      apply change.injective
      rw [change.apply_symm_apply]
      exact
        (wz2PaperGeneralJohnToJohnCoordinateChange_apply_map
          actualFiber.normalization targetJohn physicalPoint).symm
    · rintro
        ⟨targetPoint, ⟨physicalPoint, physicalMem, targetEq⟩,
          pointEq⟩
      refine ⟨physicalPoint, physicalMem, ?_⟩
      rw [← pointEq, ← targetEq]
      apply change.injective
      rw [change.apply_symm_apply]
      exact
        wz2PaperGeneralJohnToJohnCoordinateChange_apply_map
          actualFiber.normalization targetJohn physicalPoint
  have outerJohnVolume :
      volume targetJohn.parent_convex_body.outerJohnEllipsoid ≤
        pureWZ2Prop62UpperEnvelopeJohnLoss *
          volume
            actualFiber.normalization.parent_convex_body.outerJohnEllipsoid := by
    simpa [pureWZ2Prop62UpperEnvelopeJohnLoss] using
      wz2PaperFactor_outerJohn_volume_le
        oldData.rho_pos
        (by
          norm_num [pureWZ2Prop62UpperEnvelopeFactor] :
            (1 : ℝ) ≤ pureWZ2Prop62UpperEnvelopeFactor)
        (oldData.coarse.tube packet)
        (upperGeometryEnvelopeTube
          (schedule := schedule) (quotient := quotient)
          coordinate anchor)
        actualFiber.normalization targetJohn
  have sourceVolume :
      volume sourceConvexSet ≤
        pureWZ2Prop62UpperEnvelopeGeometricLoss *
          volume convexSet := by
    rw [sourceTargetImage]
    exact
      (wz2PaperGeneralJohnToJohnCoordinateChange_inverse_volume
        actualFiber.normalization targetJohn
        pureWZ2Prop62UpperEnvelopeJohnLoss
        (by
          unfold pureWZ2Prop62UpperEnvelopeJohnLoss
          exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        outerJohnVolume
        (targetJohn.map '' physicalEnvelope)).trans <| by
          calc
            pureWZ2Prop62UpperEnvelopeJohnLoss *
                  volume (targetJohn.map '' physicalEnvelope) ≤
                pureWZ2Prop62UpperEnvelopeJohnLoss *
                  ((212776173 : ENNReal) * volume convexSet) := by
              gcongr
            _ =
                pureWZ2Prop62UpperEnvelopeGeometricLoss *
                  volume convexSet := by
              simp [pureWZ2Prop62UpperEnvelopeGeometricLoss]
              ring
  rw [filteredEq]
  have strictFiberEq :
      wz2PaperOrdinaryFullFiberIndices
          fine oldData.coarse packet =
        Finset.univ.filter fun leaf =>
          oldData.cover.parent leaf = packet := by
    ext leaf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact
      oldData.cover.mem_fullFiber_iff_parent_eq
        oldData.rho_pos.le packet leaf
  have bodyCard :
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := fine) (coarse := oldData.coarse)
        packet actualFiber.normalization).enncard =
      ((Finset.univ.filter fun leaf =>
        oldData.cover.parent leaf = packet).card : ENNReal) := by
    change
      ((wz2PaperOrdinaryFullFiberIndices
        fine oldData.coarse packet).card : ENNReal) = _
    rw [strictFiberEq]
  rw [bodyCard] at raw
  exact raw.trans <| by
    gcongr

/--
Complete quotient upper-geometry package with axis-box-twelve support.
-/
def upperGeometryDataAxisBoxTwelve
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.metric.selectedFine.tube source).carrier ⊆
          Kakeya.Streamlined.axisBox 12 12 12)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2) :
    PureWZ2Prop62ProxyQuotientUpperGeometryData
      (sourceConstant := ambientConstant)
      output adapter preliminary_eq fineLine fineBase rhoPos where
  containedLeafSet :=
    output.upperGeometryContainedLeafSetAxisBoxTwelve
      fineLine rhoPos scaleGap fineAxisBox
  contained_packet := by
    intro coordinate parent anchor anchorMem convexSet child childMem
    exact
      output.upperGeometryContainedLeafSetAxisBoxTwelve_contains_packet
        adapter preliminary_eq fineLine fineBase rhoPos
        scaleGap fineAxisBox widthPos packetScaleLeRho sixWidthLe
        coordinate parent anchor anchorMem convexSet child childMem
  ambient_cwa := by
    intro coordinate _parent anchor _anchorMem convexSet convex
    exact
      output.upperGeometryContainedLeafSetAxisBoxTwelve_ambient_cwa
        fineLine rhoPos scaleGap fineAxisBox
        coordinate anchor convexSet convex

/--
Pipeline-facing bounded-base producer.  No unit-ball containment is used.
-/
def upperGeometryDataOfBoundedBaseFour
    (deltaLe : delta ≤ 1 / 100)
    (fineBoundedBase : HasBoundedBase fine 4)
    (scaleGap : 4 * delta ≤ rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2) :
    PureWZ2Prop62ProxyQuotientUpperGeometryData
      (sourceConstant := ambientConstant)
      output adapter preliminary_eq fineLine fineBase rhoPos :=
  output.upperGeometryDataAxisBoxTwelve
    adapter preliminary_eq fineLine fineBase rhoPos scaleGap
    (output.upperGeometry_selectedFine_axisBox_twelve
      fineLine rhoPos
      (schedule.scaleData packetCoordinate).delta_pos.le
      deltaLe fineBoundedBase)
    widthPos packetScaleLeRho sixWidthLe

include adapter preliminary_eq fineBase in
/--
The complete upper nearby-scale CWA conclusion under bounded-base support.
This is the direct replacement for the unit-ball-dependent upper tail of the
historical runtime pipeline.
-/
theorem finalMetricParents_publicPureCWA_of_boundedBaseFour
    (deltaLe : delta ≤ 1 / 100)
    (fineBoundedBase : HasBoundedBase fine 4)
    (scaleGap : 4 * delta ≤ rho)
    (widthPos : 0 < width)
    (packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho)
    (rhoLeOne : rho ≤ 1)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (strongSeparation :
      360 * rho <
        (((strideBase + 1 : ℕ) : ℝ) - 1) * width)
    (Bcopy Cold Λ outputConstant : ENNReal)
    (centerCopyBound :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        ∀ center,
          ((quotient.centerActualParents
            coordinate.1 center).card : ENNReal) ≤ Bcopy)
    (ambientUniform :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        WZ2PaperPureFullFibersAreCUniform
          fine (schedule.scaleData coordinate.1).coarse Cold)
    (densityLossLe : output.quotientDensityLoss ≤ Λ)
    (outputFinite :
      WZ2PaperFiniteErrorConstant outputConstant)
    (coverAbsorption :
      2 * Bcopy * Cold * Λ ≤ outputConstant)
    (bodyAbsorption :
      finalUpperBodyConstant Λ ambientConstant ≤ outputConstant)
    (roundingAbsorption :
      (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) * scaleWindow ≤
        outputConstant) :
    WZ2PaperPureCWAAtNearbyScales
      output.restriction.coarseSelected.family outputConstant := by
  exact
    output.finalMetricParents_publicPureCWA_of_upperGeometryComponents
      adapter preliminary_eq fineLine fineBase rhoPos
      widthPos packetScaleLtRho rhoLeOne sixWidthLe strongSeparation
      Bcopy Cold Λ ambientConstant outputConstant
      centerCopyBound ambientUniform densityLossLe outputFinite
      coverAbsorption bodyAbsorption roundingAbsorption
      (output.upperGeometryDataOfBoundedBaseFour
        adapter preliminary_eq fineLine fineBase rhoPos
        deltaLe fineBoundedBase scaleGap widthPos
        packetScaleLtRho.le sixWidthLe)

end PureWZ2Prop62ProxyQuotientMetricCoreOutput

end Kakeya.Assouad

end
