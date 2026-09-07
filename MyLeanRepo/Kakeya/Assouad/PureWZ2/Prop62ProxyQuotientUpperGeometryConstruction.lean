import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientUpperGeometryBridge

/-!
# Proposition 6.2 quotient upper-geometry construction

This module fixes the canonical leaf set used by the quotient upper-body
argument.  A leaf is retained when it lies in the anchor's upper-center
packet and its metric parent is contained, after the canonical John
normalization, in the test convex set for some parent of the exact upper
cover.

The packet-containment field of the raw upper-geometry bridge is then
automatic.  Its ambient packet-count estimate follows from the original
scheduled-scale CWA, a common physical envelope, John-chart transport, and
the quotient-prefix packet sum.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

private theorem upperGeometry_centeredFamily_cast
    {rho : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily rho}
    (familyEq : source = target)
    (targetCentered :
      ∀ parent,
        wz2PaperCenteredLineTube (targetScale := rho)
            (target.tube parent) =
          target.tube parent) :
    ∀ parent,
      wz2PaperCenteredLineTube (targetScale := rho)
          (source.tube parent) =
        source.tube parent := by
  subst target
  exact targetCentered

private theorem upperGeometry_volume_affineEquiv_image_le_of_le
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

/-- The upper-envelope tube canonically determined by an anchor's center. -/
noncomputable def upperGeometryEnvelopeTube
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (anchor : Fin fine.card) :
    Kakeya.DeltaTube
      (pureWZ2Prop62UpperEnvelopeFactor *
        schedule.actualScale coordinate.1) :=
  wz2PaperCenteredLineTube
    (targetScale :=
      pureWZ2Prop62UpperEnvelopeFactor *
        schedule.actualScale coordinate.1)
    ((quotient.level coordinate.1).centerFamily.tube
      (quotient.leafCenter coordinate.1 anchor))

/-- Canonical John chart of the anchor-determined upper envelope. -/
noncomputable def upperGeometryNormalization
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (anchor : Fin fine.card) :
    WZ2PaperAssouadUnitRescalingData
      (upperGeometryEnvelopeTube
        (schedule := schedule) (quotient := quotient)
        coordinate anchor) :=
  WZ2PaperAssouadUnitRescalingData.ofTube _
    (mul_pos
      (by norm_num [pureWZ2Prop62UpperEnvelopeFactor])
      (schedule.scaleData coordinate.1).rho_pos)

/-- Metric parents contained in a test set in the anchor's canonical chart. -/
def upperGeometryContainedMetricParents
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (anchor : Fin fine.card)
    (convexSet : Set Point3) :
    Finset (Fin output.metric.metricParents.card) :=
  Finset.univ.filter fun child =>
    (upperGeometryNormalization
      (schedule := schedule) (quotient := quotient)
      coordinate anchor).map ''
        (output.metric.metricParents.tube child).carrier ⊆
      convexSet

include fineLine in
theorem upperGeometry_metricParents_centered
    (parent : Fin output.metric.metricParents.card) :
    wz2PaperCenteredLineTube (targetScale := rho)
        (output.metric.metricParents.tube parent) =
      output.metric.metricParents.tube parent := by
  exact
    upperGeometry_centeredFamily_cast output.metric.metric_coarse_eq
      (fun meshParent => by
        change
          wz2PaperCenteredLineTube (targetScale := rho)
              (wz2PaperCenteredLineTube
                (targetScale := rho)
                (schedule.coordinateProxyTube
                  fineNonempty packetCoordinate
                  (output.metric.mesh.representative
                    (output.metric.mesh.cellEquiv meshParent)))) =
            wz2PaperCenteredLineTube
              (targetScale := rho)
              (schedule.coordinateProxyTube
                fineNonempty packetCoordinate
                (output.metric.mesh.representative
                  (output.metric.mesh.cellEquiv meshParent)))
        exact
          wz2PaperCenteredLineTube_recenter
            (schedule.coordinateProxyTube_lineClass
              fineNonempty fineLine packetCoordinate
              (output.metric.mesh.representative
                (output.metric.mesh.cellEquiv meshParent))))
      parent

theorem upperEnvelopeOwner_tube_eq_upperGeometryEnvelopeTube
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (child : Fin output.metric.metricParents.card)
    (anchor : Fin fine.card)
    (centerEq :
      output.metric.upperQuotientCenter coordinate child =
        quotient.leafCenter coordinate.1 anchor) :
    (output.metric.upperEnvelopeFamily coordinate).tube
        (output.metric.upperEnvelopeOwner coordinate child) =
      upperGeometryEnvelopeTube
        (schedule := schedule) (quotient := quotient)
        coordinate anchor := by
  change
    wz2PaperCenteredLineTube
        ((output.metric.upperCenters coordinate).family.tube
          (output.metric.upperEnvelopeOwner coordinate child)) =
      wz2PaperCenteredLineTube
        ((quotient.level coordinate.1).centerFamily.tube
          (quotient.leafCenter coordinate.1 anchor))
  rw [(output.metric.upperCenters coordinate).tube_eq,
    output.metric.upperEnvelopeOwner_ambient, centerEq]

include fineLine rhoPos in
theorem exists_upperGeometryPhysicalEnvelope
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.metric.selectedFine.tube source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
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
      pureWZ2_prop62_metric_children_common_envelope
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

/-- A total choice of the common physical envelope. -/
noncomputable def upperGeometryPhysicalEnvelope
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.metric.selectedFine.tube source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (anchor : Fin fine.card)
    (convexSet : Set Point3) : Set Point3 :=
  if convex : Convex ℝ convexSet then
    Classical.choose <|
      exists_upperGeometryPhysicalEnvelope
        (output := output) (schedule := schedule)
        (quotient := quotient) fineLine rhoPos
        scaleGap fineAxisBox coordinate anchor convexSet convex
  else Set.univ

theorem upperGeometryPhysicalEnvelope_spec
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.metric.selectedFine.tube source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (anchor : Fin fine.card)
    (convexSet : Set Point3)
    (convex : Convex ℝ convexSet) :
    Convex ℝ
        (upperGeometryPhysicalEnvelope
          (output := output) (schedule := schedule)
          (quotient := quotient) fineLine rhoPos
          scaleGap fineAxisBox coordinate anchor convexSet) ∧
      volume
          (upperGeometryPhysicalEnvelope
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
            upperGeometryPhysicalEnvelope
              (output := output) (schedule := schedule)
              (quotient := quotient) fineLine rhoPos
              scaleGap fineAxisBox coordinate anchor convexSet := by
  rw [upperGeometryPhysicalEnvelope, dif_pos convex]
  exact
    Classical.choose_spec <|
      exists_upperGeometryPhysicalEnvelope
        (output := output) (schedule := schedule)
        (quotient := quotient) fineLine rhoPos
        scaleGap fineAxisBox coordinate anchor convexSet convex

theorem finalUpperParent_tube_eq_upperGeometryEnvelopeTube
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
    (anchor leaf : Fin fine.card)
    (leafWhole : leaf ∈ adapter.preCore.wholeLeaves)
    (leafCenter :
      quotient.leafCenter coordinate.1 leaf =
        quotient.leafCenter coordinate.1 anchor)
    (child : Fin output.metric.metricParents.card)
    (leafOwner : output.metric.ambientMetricParentOf leaf = child)
    (childMem :
      child ∈
        pureWZ2Prop62UpperCoverAmbientFiber
          output.finalMetricParentsSubfamily
          (output.finalUpperCover
            (adapter := adapter) (preliminary_eq := preliminary_eq)
            fineLine fineBase rhoPos coordinate).selectedParents.family
          parent) :
    (output.finalUpperCover
      (adapter := adapter) (preliminary_eq := preliminary_eq)
      fineLine fineBase rhoPos coordinate).selectedParents.family.tube
        parent =
      upperGeometryEnvelopeTube
        (schedule := schedule) (quotient := quotient)
        coordinate anchor := by
  let coverData :=
    output.finalUpperCover
      (adapter := adapter) (preliminary_eq := preliminary_eq)
      fineLine fineBase rhoPos coordinate
  rcases Finset.mem_image.mp childMem with
    ⟨selectedChild, selectedChildMem, childEq⟩
  have childOwner :
      output.metric.upperEnvelopeOwner coordinate child =
        coverData.selectedParents.embedding parent := by
    have selectedParentEq :
        coverData.cover.parent selectedChild = parent :=
      (coverData.cover.mem_fullFiber_iff_parent_eq
        (mul_pos
          (by norm_num [pureWZ2Prop62UpperEnvelopeFactor])
          (schedule.scaleData coordinate.1).rho_pos).le
        parent selectedChild).mp selectedChildMem
    calc
      output.metric.upperEnvelopeOwner coordinate child =
          output.metric.upperEnvelopeOwner coordinate
            (output.finalMetricParentsSubfamily.embedding selectedChild) :=
        congrArg (output.metric.upperEnvelopeOwner coordinate)
          childEq.symm
      _ = coverData.selectedParents.embedding parent := by
        rw [← selectedParentEq]
        exact (coverData.parent_owner_eq selectedChild).symm
  have childCenter :
      output.metric.upperQuotientCenter coordinate child =
        quotient.leafCenter coordinate.1 anchor := by
    calc
      output.metric.upperQuotientCenter coordinate child =
          quotient.leafCenter coordinate.1 leaf := by
        rw [← leafOwner]
        exact
          (output.wholeLeafCenter_eq_upperQuotientCenter
            (adapter := adapter) fineLine fineBase rhoPos widthPos
            packetScaleLeRho sixWidthLe leaf leafWhole coordinate).symm
      _ = quotient.leafCenter coordinate.1 anchor := leafCenter
  have ownerTube :
      (output.metric.upperEnvelopeFamily coordinate).tube
          (output.metric.upperEnvelopeOwner coordinate child) =
        upperGeometryEnvelopeTube
          (schedule := schedule) (quotient := quotient)
          coordinate anchor := by
    exact
      upperEnvelopeOwner_tube_eq_upperGeometryEnvelopeTube
        (output := output) (schedule := schedule)
        (quotient := quotient) coordinate child anchor childCenter
  rw [coverData.selectedParents.tube_eq, ← childOwner]
  exact ownerTube

/--
The canonical ambient leaf set relevant to one anchor and one normalized
upper test set.

On the monochromatic whole-leaf set the anchor's quotient center determines
the upper-envelope owner, so every relevant upper parent uses this same
canonical John chart.
-/
def upperGeometryContainedLeafSet
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.metric.selectedFine.tube source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (anchor : Fin fine.card)
    (convexSet : Set Point3) :
    Finset (Fin fine.card) :=
  (output.cleanup.auxiliary.prefixNodeAt
      (coordinate.1.1 + 1) anchor).filter fun leaf =>
    (fine.tube leaf).carrier ⊆
      upperGeometryPhysicalEnvelope
        (output := output) (schedule := schedule)
        (quotient := quotient) fineLine rhoPos
        scaleGap fineAxisBox coordinate anchor convexSet

/--
Every whole packet over a contained metric child lies in the canonical
ambient leaf set.
-/
theorem upperGeometryContainedLeafSet_contains_packet
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.metric.selectedFine.tube source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
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
      upperGeometryContainedLeafSet
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
      (upperGeometryPhysicalEnvelope_spec
        (output := output) (schedule := schedule)
        (quotient := quotient) fineLine rhoPos
        scaleGap fineAxisBox coordinate anchor convexSet convex).2.2
        selectedSource selectedParent
    else by
      rw [upperGeometryPhysicalEnvelope, dif_neg convex]
      exact Set.subset_univ _
  rw [upperGeometryContainedLeafSet, Finset.mem_filter]
  refine ⟨leafPrefix, ?_⟩
  rw [output.metric.mesh.complete.selectedFine.tube_eq,
    selectedSourceEq] at sourceContained
  exact sourceContained

/--
The canonical contained-leaf set satisfies the ambient packet-count estimate.
This is the exact composition of the old-scale packet CWA, the physical
common-envelope construction, factor-John volume transport, and the
quotient-prefix packet sum.
-/
theorem upperGeometryContainedLeafSet_ambient_cwa
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.metric.selectedFine.tube source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (anchor : Fin fine.card)
    (convexSet : Set Point3)
    (convex : Convex ℝ convexSet) :
    ((output.upperGeometryContainedLeafSet
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
    upperGeometryPhysicalEnvelope
      (output := output) (schedule := schedule)
      (quotient := quotient) fineLine rhoPos
      scaleGap fineAxisBox coordinate anchor convexSet
  let predicate : Fin fine.card → Prop :=
    fun leaf => (fine.tube leaf).carrier ⊆ physicalEnvelope
  have envelopeSpec :=
    upperGeometryPhysicalEnvelope_spec
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
      output.upperGeometryContainedLeafSet
          fineLine rhoPos scaleGap fineAxisBox
          coordinate anchor convexSet =
        Finset.univ.filter fun leaf =>
          oldData.cover.parent leaf ∈ activePackets ∧ predicate leaf := by
    rw [upperGeometryContainedLeafSet]
    change prefixLeaves.filter predicate = _
    rw [prefixEq]
    ext leaf
    simp [and_assoc]
  have targetEnvelopeVolume :
      volume (targetJohn.map '' physicalEnvelope) ≤
        (212776173 : ENNReal) * volume convexSet := by
    have transported :=
      upperGeometry_volume_affineEquiv_image_le_of_le
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
      (output.upperGeometryContainedLeafSet
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
Construct the raw three-field upper geometry package from the canonical leaf
set and the old-scale CWA data already carried by the laminar schedule.
-/
def upperGeometryData
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.metric.selectedFine.tube source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    :
    PureWZ2Prop62ProxyQuotientUpperGeometryData
      (sourceConstant := ambientConstant)
      output adapter preliminary_eq fineLine fineBase rhoPos where
  containedLeafSet :=
    output.upperGeometryContainedLeafSet
      fineLine rhoPos scaleGap fineAxisBox
  contained_packet := by
    intro coordinate parent anchor anchorMem convexSet child childMem
    exact
      output.upperGeometryContainedLeafSet_contains_packet
        adapter preliminary_eq fineLine fineBase rhoPos
        scaleGap fineAxisBox widthPos packetScaleLeRho sixWidthLe
        coordinate parent anchor anchorMem convexSet child childMem
  ambient_cwa := by
    intro coordinate _parent anchor anchorMem convexSet convex
    exact
      output.upperGeometryContainedLeafSet_ambient_cwa
        fineLine rhoPos scaleGap fineAxisBox
        coordinate anchor convexSet convex

end PureWZ2Prop62ProxyQuotientMetricCoreOutput

end Kakeya.Assouad

end
