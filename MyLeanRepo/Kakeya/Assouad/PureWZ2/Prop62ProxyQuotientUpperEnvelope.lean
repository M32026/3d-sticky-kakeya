import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyAncestryMetricOutput
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62UpperScaleCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.DirectCallerScaleNet
import MyLeanRepo.Kakeya.Assouad.WZ1.PaperPackingRefinement

/-!
# Proposition 6.2 quotient-center upper envelopes

The old Definition 2.12 parents may contain several longitudinal copies of
one affine line.  This module therefore assigns each metric parent directly
to the quotient center of its upper ancestor.  The resulting centered
envelopes and their conflict graph depend only on the separated quotient
centers, never on a bound for the number of actual-parent copies.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private theorem centeredFamily_cast
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

def pureWZ2Prop62UpperEnvelopeFactor : ℕ :=
  600002

def pureWZ2Prop62UpperEnvelopeConflictRadius : ℕ :=
  72000240

def pureWZ2Prop62UpperEnvelopeConflictDegree : ℕ :=
  4608015361 ^ 5

theorem wz2Paper_centered_carrier_subset_of_lineDistance_bound
    {sourceScale centerScale targetScale distanceBound : ℝ}
    (sourceScalePos : 0 < sourceScale)
    {sourceTube : Kakeya.DeltaTube sourceScale}
    {centerTube : Kakeya.DeltaTube centerScale}
    (lineDistance :
      wz1PaperLineDistance sourceTube centerTube ≤ distanceBound)
    (radiusBound :
      sourceScale + distanceBound ≤ targetScale) :
    (wz2PaperCenteredLineTube
        (targetScale := sourceScale) sourceTube).carrier ⊆
      (wz2PaperCenteredLineTube
        (targetScale := targetScale) centerTube).carrier := by
  intro point pointMem
  let sourceCentered :=
    wz2PaperCenteredLineTube
      (targetScale := sourceScale) sourceTube
  let targetCentered :=
    wz2PaperCenteredLineTube
      (targetScale := targetScale) centerTube
  have sourceSegmentCompact :
      IsCompact
        (Kakeya.unitSegment
          sourceCentered.base sourceCentered.direction) := by
    apply IsCompact.image isCompact_Icc
    fun_prop
  change
    point ∈
      Metric.cthickening sourceScale
        (Kakeya.unitSegment
          sourceCentered.base sourceCentered.direction) at pointMem
  rw [sourceSegmentCompact.cthickening_eq_biUnion_closedBall
    sourceScalePos.le] at pointMem
  rcases Set.mem_iUnion₂.mp pointMem with
    ⟨sourceAxisPoint, sourceAxisMem, pointSourceDistance⟩
  rcases sourceAxisMem with ⟨parameter, parameterMem, rfl⟩
  let targetAxisPoint :=
    targetCentered.base + parameter • targetCentered.direction
  have targetAxisMem :
      targetAxisPoint ∈
        Kakeya.unitSegment
          targetCentered.base targetCentered.direction :=
    ⟨parameter, parameterMem, rfl⟩
  have zeroDistance :
      dist (wz1TubeAxisZeroPoint sourceTube)
          (wz1TubeAxisZeroPoint centerTube) +
        InnerProductGeometry.angle
            (wz1PaperDirection sourceTube)
            (wz1PaperDirection centerTube) ≤
      distanceBound := by
    simpa [wz1PaperLineDistance] using lineDistance
  have directionDistance :
      ‖wz1PaperDirection sourceTube -
          wz1PaperDirection centerTube‖ ≤
        InnerProductGeometry.angle
          (wz1PaperDirection sourceTube)
          (wz1PaperDirection centerTube) :=
    unit_norm_sub_le_angle
      (wz1PaperDirection_norm sourceTube)
      (wz1PaperDirection_norm centerTube)
  have centeredParameter :
      |parameter - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [parameterMem.1, parameterMem.2]
  have axisDifference :
      (sourceCentered.base +
          parameter • sourceCentered.direction) -
        targetAxisPoint =
      (wz1TubeAxisZeroPoint sourceTube -
          wz1TubeAxisZeroPoint centerTube) +
        (parameter - 1 / 2) •
          (wz1PaperDirection sourceTube -
            wz1PaperDirection centerTube) := by
    dsimp only [sourceCentered, targetCentered, targetAxisPoint,
      wz2PaperCenteredLineTube]
    module
  have axisDistance :
      dist
          (sourceCentered.base +
            parameter • sourceCentered.direction)
          targetAxisPoint ≤
        distanceBound := by
    rw [dist_eq_norm, axisDifference]
    calc
      ‖(wz1TubeAxisZeroPoint sourceTube -
            wz1TubeAxisZeroPoint centerTube) +
          (parameter - 1 / 2) •
            (wz1PaperDirection sourceTube -
              wz1PaperDirection centerTube)‖ ≤
          ‖wz1TubeAxisZeroPoint sourceTube -
            wz1TubeAxisZeroPoint centerTube‖ +
          ‖(parameter - 1 / 2) •
            (wz1PaperDirection sourceTube -
              wz1PaperDirection centerTube)‖ :=
        norm_add_le _ _
      _ =
          dist (wz1TubeAxisZeroPoint sourceTube)
              (wz1TubeAxisZeroPoint centerTube) +
          |parameter - 1 / 2| *
            ‖wz1PaperDirection sourceTube -
              wz1PaperDirection centerTube‖ := by
        rw [dist_eq_norm, norm_smul, Real.norm_eq_abs]
      _ ≤
          dist (wz1TubeAxisZeroPoint sourceTube)
              (wz1TubeAxisZeroPoint centerTube) +
          (1 / 2) *
            InnerProductGeometry.angle
              (wz1PaperDirection sourceTube)
              (wz1PaperDirection centerTube) := by
        gcongr
      _ ≤
          dist (wz1TubeAxisZeroPoint sourceTube)
              (wz1TubeAxisZeroPoint centerTube) +
          InnerProductGeometry.angle
              (wz1PaperDirection sourceTube)
              (wz1PaperDirection centerTube) := by
        have angleNonnegative :
            0 ≤
              InnerProductGeometry.angle
                (wz1PaperDirection sourceTube)
                (wz1PaperDirection centerTube) :=
          InnerProductGeometry.angle_nonneg _ _
        linarith
      _ ≤ distanceBound := zeroDistance
  have pointTargetDistance :
      dist point targetAxisPoint ≤ targetScale := by
    calc
      dist point targetAxisPoint ≤
          dist point
              (sourceCentered.base +
                parameter • sourceCentered.direction) +
            dist
              (sourceCentered.base +
                parameter • sourceCentered.direction)
              targetAxisPoint :=
        dist_triangle _ _ _
      _ ≤ sourceScale + distanceBound := by
        gcongr
        simpa [Metric.mem_closedBall] using pointSourceDistance
      _ ≤ targetScale := radiusBound
  exact
    Metric.mem_cthickening_of_dist_le
      point targetAxisPoint targetScale
      (Kakeya.unitSegment
        targetCentered.base targetCentered.direction)
      targetAxisMem pointTargetDistance

namespace PureWZ2Prop62ProxyAncestryMetricOutput

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
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)

noncomputable def upperMetricParentRepresentative
    (parent : Fin output.metricParents.card) :
    Fin output.selectedFine.card :=
  Classical.choose <| output.section6Cover.parent_hit parent

theorem upperMetricParentRepresentative_covers
    (parent : Fin output.metricParents.card) :
    WZ1PaperTubeCovers
      (output.selectedFine.tube
        (output.upperMetricParentRepresentative parent))
      (output.metricParents.tube parent) :=
  Classical.choose_spec <| output.section6Cover.parent_hit parent

noncomputable def upperQuotientCenter
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (parent : Fin output.metricParents.card) :
    Fin (quotient.level coordinate.1).centerFamily.card :=
  quotient.leafCenter coordinate.1 <|
    output.mesh.complete.selectedFine.embedding <|
      output.upperMetricParentRepresentative parent

theorem upperQuotientCenter_source
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (parent : Fin output.metricParents.card)
    (source : Fin output.selectedFine.card)
    (sourceParent :
      output.section6Cover.toWZ1PaperTubeCover.parent source =
        parent) :
    quotient.leafCenter coordinate.1
        (output.mesh.complete.selectedFine.embedding source) =
      output.upperQuotientCenter coordinate parent := by
  let representative :=
    output.upperMetricParentRepresentative parent
  have representativeParent :
      output.section6Cover.toWZ1PaperTubeCover.parent representative =
        parent := by
    exact
      (output.section6Cover.toWZ1PaperTubeCover.parent_unique
        representative parent
        (output.upperMetricParentRepresentative_covers parent)).symm
  have metricParentEq :
      output.section6Cover.toWZ1PaperTubeCover.parent source =
        output.section6Cover.toWZ1PaperTubeCover.parent representative :=
    sourceParent.trans representativeParent.symm
  have sameCell :
      schedule.proxyPacketLineCell fineNonempty packetCoordinate width
          (output.mesh.complete.selectedFine.embedding source) =
        schedule.proxyPacketLineCell fineNonempty packetCoordinate width
          (output.mesh.complete.selectedFine.embedding representative) := by
    apply
      (output.metric_parent_eq_iff_proxyPacketLineCell_embedding_eq
        source representative).mp
    simpa only [section6Cover,
      output.metricInput.section6_parent_eq_packetParent] using metricParentEq
  have sourceMem :
      output.mesh.complete.selectedFine.embedding source ∈
        output.selection.selected := by
    rw [← output.selectedFineIndices_eq_selection]
    exact output.mesh.complete.selectedFine_embedding_mem source
  have representativeMem :
      output.mesh.complete.selectedFine.embedding representative ∈
        output.selection.selected := by
    rw [← output.selectedFineIndices_eq_selection]
    exact output.mesh.complete.selectedFine_embedding_mem representative
  have sourceColor :=
    output.selection.selected_monochromatic
      (output.mesh.complete.selectedFine.embedding source) sourceMem
  have representativeColor :=
    output.selection.selected_monochromatic
      (output.mesh.complete.selectedFine.embedding representative)
      representativeMem
  have packetCellEq :
      schedule.proxyPacketCell
          (schedule.proxyPacketLineCell
            fineNonempty packetCoordinate width)
          (output.mesh.complete.selectedFine.embedding source) =
        schedule.proxyPacketCell
          (schedule.proxyPacketLineCell
            fineNonempty packetCoordinate width)
          (output.mesh.complete.selectedFine.embedding representative) := by
    apply Subtype.ext
    exact sameCell
  rw [packetCellEq] at sourceColor
  have colorVectorEq :
      quotient.proxyUpperColorVector rho packetCoordinate
          (output.mesh.complete.selectedFine.embedding source) =
        quotient.proxyUpperColorVector rho packetCoordinate
          (output.mesh.complete.selectedFine.embedding representative) :=
    sourceColor.trans representativeColor.symm
  have ancestryEq :=
    quotient.proxyUpperAncestry_eq_of_sameCell_and_colorVector_eq
      fineLine fineBase rho width packetCoordinate rhoPos widthPos
      packetScaleLeRho sixWidthLe
      (output.mesh.complete.selectedFine.embedding source)
      (output.mesh.complete.selectedFine.embedding representative)
      sameCell colorVectorEq
  exact congrFun ancestryEq coordinate

theorem metricParent_upperQuotientCenter_lineDistance_le
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (parent : Fin output.metricParents.card) :
    wz1PaperLineDistance
        (output.metricParents.tube parent)
        ((quotient.level coordinate.1).centerFamily.tube
          (output.upperQuotientCenter coordinate parent)) ≤
      rho / 2 +
        600000 * schedule.actualScale coordinate.1 +
        schedule.actualScale coordinate.1 / 4 := by
  let representative :=
    output.upperMetricParentRepresentative parent
  let ambientSource :=
    output.mesh.complete.selectedFine.embedding representative
  let actualParent :=
    (schedule.scaleData coordinate.1).cover.parent ambientSource
  have metricToFine :
      wz1PaperLineDistance
          (output.metricParents.tube parent)
          (output.selectedFine.tube representative) ≤
        rho / 2 := by
    rw [wz1PaperLineDistance_symm]
    exact output.upperMetricParentRepresentative_covers parent
  have fineToProxy :
      wz1PaperLineDistance
          (output.selectedFine.tube representative)
          (schedule.coordinateProxyTube
            fineNonempty coordinate.1 actualParent) ≤
        600000 * schedule.actualScale coordinate.1 := by
    rw [output.mesh.complete.selectedFine.tube_eq]
    exact
      schedule.completePacket_coordinateProxyTube_lineDistance_le
        fineNonempty fineLine fineBase coordinate.1 actualParent
        ambientSource
        ((schedule.scaleData coordinate.1).cover
          |>.parent_mem_fullFiber ambientSource)
  have proxyToCenter :
      wz1PaperLineDistance
          (schedule.coordinateProxyTube
            fineNonempty coordinate.1 actualParent)
          ((quotient.level coordinate.1).centerFamily.tube
            (output.upperQuotientCenter coordinate parent)) ≤
        schedule.actualScale coordinate.1 / 4 := by
    exact
      (quotient.level coordinate.1).actualProxy_center_lineDistance_le
        fineLine actualParent
  calc
    wz1PaperLineDistance
        (output.metricParents.tube parent)
        ((quotient.level coordinate.1).centerFamily.tube
          (output.upperQuotientCenter coordinate parent)) ≤
      wz1PaperLineDistance
          (output.metricParents.tube parent)
          (output.selectedFine.tube representative) +
        wz1PaperLineDistance
          (output.selectedFine.tube representative)
          ((quotient.level coordinate.1).centerFamily.tube
            (output.upperQuotientCenter coordinate parent)) :=
      wz1PaperLineDistance_triangle _ _ _
    _ ≤
      wz1PaperLineDistance
          (output.metricParents.tube parent)
          (output.selectedFine.tube representative) +
        (wz1PaperLineDistance
            (output.selectedFine.tube representative)
            (schedule.coordinateProxyTube
              fineNonempty coordinate.1 actualParent) +
          wz1PaperLineDistance
            (schedule.coordinateProxyTube
              fineNonempty coordinate.1 actualParent)
            ((quotient.level coordinate.1).centerFamily.tube
              (output.upperQuotientCenter coordinate parent))) := by
        gcongr
        exact wz1PaperLineDistance_triangle _ _ _
    _ ≤
        rho / 2 +
          600000 * schedule.actualScale coordinate.1 +
          schedule.actualScale coordinate.1 / 4 := by
      linarith

theorem metricParent_upperQuotientCenter_lineDistance_scaled
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (parent : Fin output.metricParents.card) :
    wz1PaperLineDistance
        (output.metricParents.tube parent)
        ((quotient.level coordinate.1).centerFamily.tube
          (output.upperQuotientCenter coordinate parent)) ≤
      (2400003 / 4 : ℝ) *
        schedule.actualScale coordinate.1 := by
  exact
    (output.metricParent_upperQuotientCenter_lineDistance_le
      fineLine fineBase coordinate parent).trans <| by
        nlinarith [coordinate.2.1]

def upperCenterIndices
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate) :
    Finset (Fin (quotient.level coordinate.1).centerFamily.card) :=
  Finset.univ.image (output.upperQuotientCenter coordinate)

noncomputable def upperCenters
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate) :
    WZ2PaperPureTubeSubfamily
      (quotient.level coordinate.1).centerFamily :=
  WZ2PaperPureTubeSubfamily.fromFinset
    (quotient.level coordinate.1).centerFamily
    (output.upperCenterIndices coordinate)

noncomputable def upperCenterEquiv
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate) :
    Fin (output.upperCenterIndices coordinate).card ≃
      output.upperCenterIndices coordinate :=
  (output.upperCenterIndices coordinate).orderIsoOfFin rfl |>.toEquiv

noncomputable def upperEnvelopeOwner
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (parent : Fin output.metricParents.card) :
    Fin (output.upperCenters coordinate).family.card :=
  (output.upperCenterEquiv coordinate).symm
    ⟨output.upperQuotientCenter coordinate parent,
      Finset.mem_image.mpr
        ⟨parent, Finset.mem_univ parent, rfl⟩⟩

theorem upperEnvelopeOwner_ambient
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (parent : Fin output.metricParents.card) :
    (output.upperCenters coordinate).embedding
        (output.upperEnvelopeOwner coordinate parent) =
      output.upperQuotientCenter coordinate parent := by
  exact congrArg Subtype.val <|
    (output.upperCenterEquiv coordinate).apply_symm_apply _

theorem upperEnvelopeOwner_surjective
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate) :
    Function.Surjective (output.upperEnvelopeOwner coordinate) := by
  intro selectedCenter
  have centerMem :
      ((output.upperCenters coordinate).embedding selectedCenter) ∈
        output.upperCenterIndices coordinate :=
    Finset.orderEmbOfFin_mem
      (output.upperCenterIndices coordinate) rfl selectedCenter
  rcases Finset.mem_image.mp centerMem with
    ⟨parent, _parentMem, centerEq⟩
  refine ⟨parent, ?_⟩
  apply (output.upperCenters coordinate).embedding.injective
  rw [output.upperEnvelopeOwner_ambient, centerEq]

noncomputable def upperEnvelopeFamily
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate) :
    Kakeya.Streamlined.TubeFamily
      (pureWZ2Prop62UpperEnvelopeFactor *
        schedule.actualScale coordinate.1) where
  card := (output.upperCenters coordinate).family.card
  tube center :=
    wz2PaperCenteredLineTube
      (targetScale :=
        pureWZ2Prop62UpperEnvelopeFactor *
          schedule.actualScale coordinate.1)
      ((output.upperCenters coordinate).family.tube center)

theorem upperEnvelopeFamily_lineClass
    (fineLine : WZ1PaperIsLineClass fine)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate) :
    WZ1PaperIsLineClass (output.upperEnvelopeFamily coordinate) := by
  intro center
  exact
    wz2PaperCenteredLineTube_lineClass <|
      (quotient.level coordinate.1).centerFamily_lineClass fineLine <|
        (output.upperCenters coordinate).embedding center

theorem upperEnvelopeFamily_midpoint_norm_le_one
    (fineLine : WZ1PaperIsLineClass fine)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (center : Fin (output.upperEnvelopeFamily coordinate).card) :
    ‖wz2PaperTubeMidpoint
        ((output.upperEnvelopeFamily coordinate).tube center)‖ ≤ 1 := by
  exact
    wz2PaperCenteredLineTube_midpoint_norm_le_one <|
      (quotient.level coordinate.1).centerFamily_lineClass fineLine <|
        (output.upperCenters coordinate).embedding center

theorem upperEnvelopeFamily_lineDistance
    (fineLine : WZ1PaperIsLineClass fine)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (first second :
      Fin (output.upperCenters coordinate).family.card) :
    wz1PaperLineDistance
        ((output.upperEnvelopeFamily coordinate).tube first)
        ((output.upperEnvelopeFamily coordinate).tube second) =
      wz1PaperLineDistance
        ((quotient.level coordinate.1).centerFamily.tube
          ((output.upperCenters coordinate).embedding first))
        ((quotient.level coordinate.1).centerFamily.tube
          ((output.upperCenters coordinate).embedding second)) := by
  change
    wz1PaperLineDistance
        (wz2PaperCenteredLineTube
          ((output.upperCenters coordinate).family.tube first))
        (wz2PaperCenteredLineTube
          ((output.upperCenters coordinate).family.tube second)) =
      _
  rw [(output.upperCenters coordinate).tube_eq,
    (output.upperCenters coordinate).tube_eq]
  rw [wz1PaperLineDistance_centeredLineTube_both
    ((quotient.level coordinate.1).centerFamily_lineClass fineLine _)
    ((quotient.level coordinate.1).centerFamily_lineClass fineLine _)]

theorem upperEnvelopeOwner_containment
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (parent : Fin output.metricParents.card) :
    (output.metricParents.tube parent).carrier ⊆
      ((output.upperEnvelopeFamily coordinate).tube
        (output.upperEnvelopeOwner coordinate parent)).carrier := by
  have metricCentered :
      wz2PaperCenteredLineTube (targetScale := rho)
          (output.metricParents.tube parent) =
        output.metricParents.tube parent := by
    exact
      centeredFamily_cast output.metric_coarse_eq
        (fun meshParent => by
          change
            wz2PaperCenteredLineTube (targetScale := rho)
                (wz2PaperCenteredLineTube
                  (targetScale := rho)
                  (schedule.coordinateProxyTube
                    fineNonempty packetCoordinate
                    (output.mesh.representative
                      (output.mesh.cellEquiv meshParent)))) =
              wz2PaperCenteredLineTube
                (targetScale := rho)
                (schedule.coordinateProxyTube
                  fineNonempty packetCoordinate
                  (output.mesh.representative
                    (output.mesh.cellEquiv meshParent)))
          exact
            wz2PaperCenteredLineTube_recenter
              (schedule.coordinateProxyTube_lineClass
                fineNonempty fineLine packetCoordinate
                (output.mesh.representative
                  (output.mesh.cellEquiv meshParent))))
        parent
  rw [← metricCentered]
  change
    (wz2PaperCenteredLineTube (targetScale := rho)
      (output.metricParents.tube parent)).carrier ⊆
      (wz2PaperCenteredLineTube
        (targetScale :=
          pureWZ2Prop62UpperEnvelopeFactor *
            schedule.actualScale coordinate.1)
        ((output.upperCenters coordinate).family.tube
          (output.upperEnvelopeOwner coordinate parent))).carrier
  apply
    wz2Paper_centered_carrier_subset_of_lineDistance_bound
      rhoPos
  ·
    rw [(output.upperCenters coordinate).tube_eq,
      output.upperEnvelopeOwner_ambient]
  · have rhoLeScale : rho ≤ schedule.actualScale coordinate.1 :=
      coordinate.2.1
    have distanceLe :=
      output.metricParent_upperQuotientCenter_lineDistance_scaled
        fineLine fineBase coordinate parent
    norm_num [pureWZ2Prop62UpperEnvelopeFactor] at distanceLe ⊢
    nlinarith

theorem upperEnvelope_conflict_centerDistance_le
    (fineLine : WZ1PaperIsLineClass fine)
    (rhoPos : 0 < rho)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    {first second : Fin (output.upperEnvelopeFamily coordinate).card}
    (overlap :
      (wz2PaperOrdinaryDilatedFiberIndices
          2 output.metricParents
          (output.upperEnvelopeFamily coordinate) first ∩
        wz2PaperOrdinaryDilatedFiberIndices
          2 output.metricParents
          (output.upperEnvelopeFamily coordinate) second).Nonempty) :
    wz1PaperLineDistance
        ((quotient.level coordinate.1).centerFamily.tube
          ((output.upperCenters coordinate).embedding second))
        ((quotient.level coordinate.1).centerFamily.tube
          ((output.upperCenters coordinate).embedding first)) ≤
      pureWZ2Prop62UpperEnvelopeConflictRadius *
        schedule.actualScale coordinate.1 := by
  rcases overlap with ⟨child, childMem⟩
  rcases Finset.mem_inter.mp childMem with
    ⟨firstMem, secondMem⟩
  rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
    at firstMem secondMem
  have childMidpoint :
      ‖wz2PaperTubeMidpoint
        (output.metricParents.tube child)‖ ≤ 1 := by
    have centered :
        wz2PaperCenteredLineTube (targetScale := rho)
            (output.metricParents.tube child) =
          output.metricParents.tube child := by
      exact
        centeredFamily_cast output.metric_coarse_eq
          (fun meshParent => by
            change
              wz2PaperCenteredLineTube (targetScale := rho)
                  (wz2PaperCenteredLineTube
                    (targetScale := rho)
                    (schedule.coordinateProxyTube
                      fineNonempty packetCoordinate
                      (output.mesh.representative
                        (output.mesh.cellEquiv meshParent)))) =
                wz2PaperCenteredLineTube
                  (targetScale := rho)
                  (schedule.coordinateProxyTube
                    fineNonempty packetCoordinate
                    (output.mesh.representative
                      (output.mesh.cellEquiv meshParent)))
            exact
              wz2PaperCenteredLineTube_recenter
                (schedule.coordinateProxyTube_lineClass
                  fineNonempty fineLine packetCoordinate
                  (output.mesh.representative
                    (output.mesh.cellEquiv meshParent))))
          child
    rw [← centered]
    exact
      wz2PaperCenteredLineTube_midpoint_norm_le_one
        (output.section6Cover.coarse_line_class child)
  have firstDistance :=
    wz2_paper_bounded_centered_doubled_containment_lineDistance_le
      rhoPos
      (mul_pos (by norm_num [pureWZ2Prop62UpperEnvelopeFactor])
        (schedule.scaleData coordinate.1).rho_pos)
      (output.section6Cover.coarse_line_class child)
      (output.upperEnvelopeFamily_lineClass fineLine coordinate first)
      1 childMidpoint firstMem
  have secondDistance :=
    wz2_paper_bounded_centered_doubled_containment_lineDistance_le
      rhoPos
      (mul_pos (by norm_num [pureWZ2Prop62UpperEnvelopeFactor])
        (schedule.scaleData coordinate.1).rho_pos)
      (output.section6Cover.coarse_line_class child)
      (output.upperEnvelopeFamily_lineClass fineLine coordinate second)
      1 childMidpoint secondMem
  have triangle :=
    wz1PaperLineDistance_triangle
      ((output.upperEnvelopeFamily coordinate).tube second)
      (output.metricParents.tube child)
      ((output.upperEnvelopeFamily coordinate).tube first)
  have symmetry :
      wz1PaperLineDistance
          ((output.upperEnvelopeFamily coordinate).tube second)
          (output.metricParents.tube child) =
        wz1PaperLineDistance
          (output.metricParents.tube child)
          ((output.upperEnvelopeFamily coordinate).tube second) :=
    wz1PaperLineDistance_symm _ _
  rw [symmetry] at triangle
  change
    wz1PaperLineDistance
        ((quotient.level coordinate.1).centerFamily.tube
          ((output.upperCenters coordinate).embedding second))
        ((quotient.level coordinate.1).centerFamily.tube
          ((output.upperCenters coordinate).embedding first)) ≤ _
  rw [← output.upperEnvelopeFamily_lineDistance
    fineLine coordinate second first]
  exact
    triangle.trans <| by
      norm_num [pureWZ2Prop62UpperEnvelopeFactor,
        pureWZ2Prop62UpperEnvelopeConflictRadius] at *
      nlinarith

theorem upperEnvelope_conflict_degree
    (fineLine : WZ1PaperIsLineClass fine)
    (rhoPos : 0 < rho)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (fixed : Fin (output.upperEnvelopeFamily coordinate).card) :
    (Finset.univ.filter fun other =>
      other ≠ fixed ∧
        (wz2PaperOrdinaryDilatedFiberIndices
            2 output.metricParents
            (output.upperEnvelopeFamily coordinate) fixed ∩
          wz2PaperOrdinaryDilatedFiberIndices
            2 output.metricParents
            (output.upperEnvelopeFamily coordinate) other).Nonempty).card ≤
      pureWZ2Prop62UpperEnvelopeConflictDegree := by
  let conflicts : Finset (Fin (output.upperEnvelopeFamily coordinate).card) :=
    Finset.univ.filter fun other =>
      other ≠ fixed ∧
        (wz2PaperOrdinaryDilatedFiberIndices
            2 output.metricParents
            (output.upperEnvelopeFamily coordinate) fixed ∩
          wz2PaperOrdinaryDilatedFiberIndices
            2 output.metricParents
            (output.upperEnvelopeFamily coordinate) other).Nonempty
  change conflicts.card ≤ pureWZ2Prop62UpperEnvelopeConflictDegree
  let centerFamily :=
    (quotient.level coordinate.1).centerFamily
  let selectedCenters := output.upperCenters coordinate
  let neighborhood :
      Finset (Fin selectedCenters.family.card) :=
    Finset.univ.filter fun other =>
      wz1PaperLineDistance
          (selectedCenters.family.tube other)
          (selectedCenters.family.tube fixed) ≤
        pureWZ2Prop62UpperEnvelopeConflictRadius *
          schedule.actualScale coordinate.1
  have selectedCenterDistinct :
      WZ1PaperIsEssentiallyDistinct selectedCenters.family := by
    intro first second indexNe
    have ambientNe :
        selectedCenters.embedding first ≠
          selectedCenters.embedding second :=
      selectedCenters.embedding.injective.ne indexNe
    simpa only [selectedCenters.tube_eq] using
      (quotient.level coordinate.1).centerFamily_distinct
        fineLine
        (selectedCenters.embedding first)
        (selectedCenters.embedding second)
        ambientNe
  have selectedCenterLine :
      WZ1PaperIsLineClass selectedCenters.family := by
    intro center
    simpa only [selectedCenters.tube_eq] using
      (quotient.level coordinate.1).centerFamily_lineClass
        fineLine (selectedCenters.embedding center)
  have subset :
      conflicts ⊆ neighborhood := by
    intro other otherMem
    change other ∈ neighborhood
    unfold neighborhood
    exact
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by
          rw [selectedCenters.tube_eq, selectedCenters.tube_eq]
          exact
            output.upperEnvelope_conflict_centerDistance_le
              fineLine rhoPos coordinate
              (Finset.mem_filter.mp otherMem).2.2⟩
  have packing :
      neighborhood.card ≤
        (2 * Nat.ceil
          (8 *
              (pureWZ2Prop62UpperEnvelopeConflictRadius *
                schedule.actualScale coordinate.1) /
            (schedule.actualScale coordinate.1 / 4)) + 1) ^ 5 := by
    unfold neighborhood
    exact
      tube_packing_bound_general
        selectedCenterDistinct selectedCenterLine
        (by
          have scalePos :=
            (schedule.scaleData coordinate.1).rho_pos
          positivity :
          0 < schedule.actualScale coordinate.1 / 4)
        (pureWZ2Prop62UpperEnvelopeConflictRadius *
          schedule.actualScale coordinate.1)
        (mul_pos
          (by norm_num [pureWZ2Prop62UpperEnvelopeConflictRadius])
          (schedule.scaleData coordinate.1).rho_pos)
        fixed
  have ceiling :
      Nat.ceil
          (8 *
              (pureWZ2Prop62UpperEnvelopeConflictRadius *
                schedule.actualScale coordinate.1) /
            (schedule.actualScale coordinate.1 / 4)) =
        2304007680 := by
    have algebra :
        8 *
              (pureWZ2Prop62UpperEnvelopeConflictRadius *
                schedule.actualScale coordinate.1) /
            (schedule.actualScale coordinate.1 / 4) =
          (2304007680 : ℝ) := by
      field_simp [(schedule.scaleData coordinate.1).rho_pos.ne']
      norm_num [pureWZ2Prop62UpperEnvelopeConflictRadius]
    rw [algebra]
    norm_num
  rw [ceiling] at packing
  have conflictCardLe : conflicts.card ≤ neighborhood.card :=
    Finset.card_le_card subset
  norm_num [pureWZ2Prop62UpperEnvelopeConflictDegree] at packing ⊢
  omega

noncomputable def upperEnvelopeScaleInput
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate) :
    PureWZ2Prop62UpperScaleInput
      output.metricParents
      (output.upperEnvelopeFamily coordinate)
      pureWZ2Prop62UpperEnvelopeConflictDegree where
  rho_pos := rhoPos
  upper_pos :=
    mul_pos (by norm_num [pureWZ2Prop62UpperEnvelopeFactor])
      (schedule.scaleData coordinate.1).rho_pos
  owner := output.upperEnvelopeOwner coordinate
  owner_surjective := output.upperEnvelopeOwner_surjective coordinate
  owner_containment :=
    output.upperEnvelopeOwner_containment
      fineLine fineBase rhoPos coordinate
  conflict_degree :=
    output.upperEnvelope_conflict_degree fineLine rhoPos coordinate

noncomputable def upperEnvelopeColoring
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate) :
    (output.upperEnvelopeScaleInput
      fineLine fineBase rhoPos coordinate).ColoringData :=
  Classical.choice <|
    (output.upperEnvelopeScaleInput
      fineLine fineBase rhoPos coordinate).exists_coloring

end PureWZ2Prop62ProxyAncestryMetricOutput

end Kakeya.Assouad

end
