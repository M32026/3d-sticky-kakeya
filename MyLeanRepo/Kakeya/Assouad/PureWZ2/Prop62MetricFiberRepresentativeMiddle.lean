import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MiddleFamilyOrdinaryNestedScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientFiberRoute
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientAllScaleColorPreCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62RepresentativeParentScaledPacking
import Mathlib.Tactic

/-!
# Representative middle scale on one final metric fiber

At one old descendant coordinate, the analytic Definition 2.12 witness stays
the restriction of the public laminar scale to the final genuine metric
fiber.  Its line-geometric replacement is the family of canonical
representatives of precisely the ambient parents hit by that fiber.

The all-coordinate pre-core color makes those representatives strongly
separated.  At sufficiently small actual scale, the representative line
cover gives strict carrier containment, hence a genuine pure partitioning
cover.  Exact agreement of the two parent partitions identifies their full
fibers, and general John-to-John transport moves the old fiber CWA to the
representative parent chart.

No aligned exact-source object is used.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Fixed enlargement used for the representative middle family. -/
def pureWZ2Prop62MetricFiberRepresentativeMiddleFactor : ℕ :=
  pureWZ2Prop62RepresentativeParentScaledFactor

/-- The single John-chart loss paid when replacing an old parent by its
representative middle parent. -/
def pureWZ2Prop62MetricFiberRepresentativeMiddleJohnLoss : ENNReal :=
  27 *
    ENNReal.ofReal
      (pureWZ2Prop62MetricFiberRepresentativeMiddleFactor ^ 3)

private noncomputable def finiteParentEquiv
    {Source Left Right : Type*}
    [Fintype Source] [Fintype Left] [Fintype Right]
    [Nonempty Source]
    (left : Source → Left)
    (right : Source → Right)
    (leftSurjective : Function.Surjective left)
    (rightSurjective : Function.Surjective right)
    (compatible : ∀ first second, left first = left second ↔
      right first = right second) :
    Left ≃ Right := by
  let representative : Left → Source :=
    fun value => Classical.choose (leftSurjective value)
  let toFun : Left → Right := fun value => right (representative value)
  have representative_left :
      ∀ value, left (representative value) = value :=
    fun value => Classical.choose_spec (leftSurjective value)
  have injective : Function.Injective toFun := by
    intro first second equality
    have leftEquality :
        left (representative first) =
          left (representative second) :=
      (compatible (representative first) (representative second)).2 equality
    simpa only [representative_left] using leftEquality
  have surjective : Function.Surjective toFun := by
    intro value
    rcases rightSurjective value with ⟨source, sourceRight⟩
    refine ⟨left source, ?_⟩
    have leftEquality :
        left (representative (left source)) = left source := by
      rw [representative_left]
    have rightEquality :=
      (compatible (representative (left source)) source).1 leftEquality
    exact rightEquality.trans sourceRight
  exact Equiv.ofBijective toFun ⟨injective, surjective⟩

private theorem finiteParentEquiv_apply
    {Source Left Right : Type*}
    [Fintype Source] [Fintype Left] [Fintype Right]
    [Nonempty Source]
    (left : Source → Left)
    (right : Source → Right)
    (leftSurjective : Function.Surjective left)
    (rightSurjective : Function.Surjective right)
    (compatible : ∀ first second, left first = left second ↔
      right first = right second)
    (source : Source) :
    finiteParentEquiv left right leftSurjective rightSurjective compatible
        (left source) =
      right source := by
  let equivalence :=
    finiteParentEquiv left right leftSurjective rightSurjective compatible
  change right (Classical.choose (leftSurjective (left source))) = right source
  exact
    (compatible
      (Classical.choose (leftSurjective (left source))) source).1 <|
      Classical.choose_spec (leftSurjective (left source))

private noncomputable def fullFiberSubtypeEquivOfEq
    {delta firstScale secondScale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {first : Kakeya.Streamlined.TubeFamily firstScale}
    {second : Kakeya.Streamlined.TubeFamily secondScale}
    (firstParent : Fin first.card)
    (secondParent : Fin second.card)
    (fiberEq :
      wz2PaperOrdinaryFullFiberIndices fine first firstParent =
        wz2PaperOrdinaryFullFiberIndices fine second secondParent) :
    {source : Fin fine.card //
      source ∈
        wz2PaperOrdinaryFullFiberIndices fine first firstParent} ≃
      {source : Fin fine.card //
        source ∈
          wz2PaperOrdinaryFullFiberIndices fine second secondParent} where
  toFun source :=
    ⟨source.1, by
      rw [← fiberEq]
      exact source.2⟩
  invFun source :=
    ⟨source.1, by
      rw [fiberEq]
      exact source.2⟩
  left_inv source := by
    ext
    rfl
  right_inv source := by
    ext
    rfl

private noncomputable def fullFiberBodyIndexEquivOfEq
    {delta firstScale secondScale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {first : Kakeya.Streamlined.TubeFamily firstScale}
    {second : Kakeya.Streamlined.TubeFamily secondScale}
    (firstParent : Fin first.card)
    (secondParent : Fin second.card)
    (fiberEq :
      wz2PaperOrdinaryFullFiberIndices fine first firstParent =
        wz2PaperOrdinaryFullFiberIndices fine second secondParent) :
    Fin (wz2PaperOrdinaryFullFiberIndices fine first firstParent).card ≃
      Fin (wz2PaperOrdinaryFullFiberIndices fine second secondParent).card :=
  ((wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := fine) (coarse := first) firstParent).trans
    (fullFiberSubtypeEquivOfEq
      firstParent secondParent fiberEq)).trans
    (wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := fine) (coarse := second) secondParent).symm

private theorem fullFiberBodyIndexEquivOfEq_source
    {delta firstScale secondScale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {first : Kakeya.Streamlined.TubeFamily firstScale}
    {second : Kakeya.Streamlined.TubeFamily secondScale}
    (firstParent : Fin first.card)
    (secondParent : Fin second.card)
    (fiberEq :
      wz2PaperOrdinaryFullFiberIndices fine first firstParent =
        wz2PaperOrdinaryFullFiberIndices fine second secondParent)
    (target :
      Fin (wz2PaperOrdinaryFullFiberIndices fine first firstParent).card) :
    ((wz2PaperOrdinaryFullFiberIndexEquiv
        (fine := fine) (coarse := second) secondParent)
      (fullFiberBodyIndexEquivOfEq firstParent secondParent fiberEq target)).1 =
      ((wz2PaperOrdinaryFullFiberIndexEquiv
        (fine := fine) (coarse := first) firstParent) target).1 := by
  simp [fullFiberBodyIndexEquivOfEq, fullFiberSubtypeEquivOfEq]

private theorem relabelCanonical_carrier_eq
    {sourceScale targetScale : ℝ}
    (source : Kakeya.DeltaTube sourceScale) :
    (wz2PaperRelabelTube (targetScale := targetScale)
      (wz2PaperCanonicalLineTube source)).carrier =
      (wz2PaperRelabelTube (targetScale := targetScale) source).carrier := by
  unfold wz2PaperCanonicalLineTube
  split_ifs with orientation
  · rfl
  · change
      (reverseTube
        (wz2PaperRelabelTube (targetScale := targetScale) source)).carrier =
        (wz2PaperRelabelTube (targetScale := targetScale) source).carrier
    exact reverseTube_carrier _

/--
If a fine representative lies in an actual parent, then a sufficiently large
same-axis relabeling of that representative contains the entire actual
ordinary carrier.
-/
private theorem actualParent_carrier_subset_representative
    {delta actual targetScale : ℝ}
    {representative : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube actual}
    (deltaPos : 0 < delta)
    (actualPos : 0 < actual)
    (factorBound : 8 * actual ≤ targetScale)
    (representativeMem : representative.carrier ⊆ parent.carrier) :
    parent.carrier ⊆
      (wz2PaperRelabelTube (targetScale := targetScale)
        (wz2PaperCanonicalLineTube representative)).carrier := by
  rw [relabelCanonical_carrier_eq representative]
  intro point pointMem
  have parentSegmentCompact :
      IsCompact (Kakeya.unitSegment parent.base parent.direction) :=
    isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  change point ∈
    Metric.cthickening actual
      (Kakeya.unitSegment parent.base parent.direction) at pointMem
  rw [parentSegmentCompact.cthickening_eq_biUnion_closedBall
    actualPos.le] at pointMem
  rcases Set.mem_iUnion₂.mp pointMem with
    ⟨parentAxisPoint, parentAxisMem, pointParentAxis⟩
  rcases parentAxisMem with ⟨parameter, parameterMem, rfl⟩
  rcases
      containment_alignment_bound
        deltaPos.le actualPos representative parent representativeMem
    with aligned | reversed
  · let representativeAxisPoint :=
      representative.base + (parameter : ℝ) • representative.direction
    have representativeAxisMem :
        representativeAxisPoint ∈
          Kakeya.unitSegment representative.base representative.direction :=
      ⟨parameter, parameterMem, rfl⟩
    apply Metric.mem_cthickening_of_dist_le
      point representativeAxisPoint targetScale
      (Kakeya.unitSegment representative.base representative.direction)
      representativeAxisMem
    calc
      dist point representativeAxisPoint ≤
          dist point
              (parent.base + (parameter : ℝ) • parent.direction) +
            dist (parent.base + (parameter : ℝ) • parent.direction)
              representativeAxisPoint :=
        dist_triangle _ _ _
      _ ≤ actual +
          (‖parent.base - representative.base‖ +
            ‖(parameter : ℝ) •
              (parent.direction - representative.direction)‖) := by
        gcongr
        · simpa [Metric.mem_closedBall] using pointParentAxis
        · rw [dist_eq_norm]
          dsimp only [representativeAxisPoint]
          rw [show
            parent.base + (parameter : ℝ) • parent.direction -
                (representative.base +
                  (parameter : ℝ) • representative.direction) =
              (parent.base - representative.base) +
                (parameter : ℝ) •
                  (parent.direction - representative.direction) by module]
          exact norm_add_le _ _
      _ ≤ actual + (3 * actual + 4 * actual) := by
        gcongr
        · simpa [norm_sub_rev] using aligned.2
        · rw [norm_smul, Real.norm_eq_abs]
          calc
            |parameter| *
                  ‖parent.direction - representative.direction‖ ≤
                1 *
                  ‖parent.direction - representative.direction‖ := by
              gcongr
              simpa [abs_of_nonneg parameterMem.1] using parameterMem.2
            _ ≤ 1 * (4 * actual) := by
              gcongr
              simpa [norm_sub_rev] using aligned.1
            _ = 4 * actual := by ring
      _ = 8 * actual := by ring
      _ ≤ targetScale := factorBound
  · let reversedParameter : ℝ := 1 - parameter
    let representativeAxisPoint :=
      representative.base +
        (reversedParameter : ℝ) • representative.direction
    have reversedParameterMem :
        reversedParameter ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨by dsimp only [reversedParameter]; linarith [parameterMem.2],
        by dsimp only [reversedParameter]; linarith [parameterMem.1]⟩
    have representativeAxisMem :
        representativeAxisPoint ∈
          Kakeya.unitSegment representative.base representative.direction :=
      ⟨reversedParameter, reversedParameterMem, rfl⟩
    apply Metric.mem_cthickening_of_dist_le
      point representativeAxisPoint targetScale
      (Kakeya.unitSegment representative.base representative.direction)
      representativeAxisMem
    calc
      dist point representativeAxisPoint ≤
          dist point
              (parent.base + (parameter : ℝ) • parent.direction) +
            dist (parent.base + (parameter : ℝ) • parent.direction)
              representativeAxisPoint :=
        dist_triangle _ _ _
      _ ≤ actual +
          (‖parent.base -
                (representative.base + representative.direction)‖ +
            ‖(parameter : ℝ) •
              (parent.direction + representative.direction)‖) := by
        gcongr
        · simpa [Metric.mem_closedBall] using pointParentAxis
        · rw [dist_eq_norm]
          dsimp only [representativeAxisPoint, reversedParameter]
          rw [show
            parent.base + (parameter : ℝ) • parent.direction -
                (representative.base +
                  (1 - (parameter : ℝ)) • representative.direction) =
              (parent.base -
                  (representative.base + representative.direction)) +
                (parameter : ℝ) •
                  (parent.direction + representative.direction) by module]
          exact norm_add_le _ _
      _ ≤ actual + (3 * actual + 4 * actual) := by
        gcongr
        · simpa [norm_sub_rev] using reversed.2
        · rw [norm_smul, Real.norm_eq_abs]
          calc
            |parameter| *
                  ‖parent.direction + representative.direction‖ ≤
                1 *
                  ‖parent.direction + representative.direction‖ := by
              gcongr
              simpa [abs_of_nonneg parameterMem.1] using parameterMem.2
            _ ≤ 1 * (4 * actual) := by
              gcongr
              simpa [add_comm] using reversed.1
            _ = 4 * actual := by ring
      _ = 8 * actual := by ring
      _ ≤ targetScale := factorBound

/-- The representative-line family hit by one final metric fiber. -/
noncomputable def pureWZ2Prop62MetricFiberRepresentativeMiddleFamily
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (parent : Fin metricCore.restriction.coarseSelected.family.card)
    (coordinate : Fin schedule.levelCount) :
    Kakeya.Streamlined.TubeFamily
      (pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
        schedule.actualScale coordinate) :=
  PureWZ2Prop62RepresentativeParentColoringData.hitRepresentativeLineFamily
    schedule fineNonempty coordinate
      (pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
        schedule.actualScale coordinate)
      (PureWZ2Prop62ProxyQuotientAllScaleColorPreCoreData.finalMetricFiberAmbientSubfamily
        metricCore parent)

/-- Internal construction retaining the line cover used to build the bridge. -/
structure PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow sourceConstant : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (parent : Fin metricCore.restriction.coarseSelected.family.card)
    (coordinate : Fin schedule.levelCount)
    (descendant :
      PureWZ2Prop62ProxyQuotientFiberDescendantData
        metricCore sourceConstant parent coordinate) where
  bridge :
    WZ2PaperMiddleFamilyScaleBridge
      (K := pureWZ2Prop62MetricFiberRepresentativeMiddleJohnLoss)
      descendant.scaleData
      (pureWZ2Prop62MetricFiberRepresentativeMiddleFamily
        metricCore parent coordinate)
  lineCover :
    WZ1PaperTubeCover
      (metricCore.restriction.metricFiberSource parent).family
      (pureWZ2Prop62MetricFiberRepresentativeMiddleFamily
        metricCore parent coordinate)
  lineCover_parent_eq :
    lineCover.parent = bridge.cover.parent
  coarse_line_class :
    WZ1PaperIsLineClass
      (pureWZ2Prop62MetricFiberRepresentativeMiddleFamily
        metricCore parent coordinate)
  separated :
    ∀ first second, first ≠ second →
      wz2PaperLiteralSourceSeparationFactor *
            (pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
              schedule.actualScale coordinate) <
        wz1PaperLineDistance
          ((pureWZ2Prop62MetricFiberRepresentativeMiddleFamily
            metricCore parent coordinate).tube first)
          ((pureWZ2Prop62MetricFiberRepresentativeMiddleFamily
            metricCore parent coordinate).tube second)

/--
Construct the representative middle scale on one final metric fiber.

`actualSmall` is the small-scale hypothesis used by the closed
representative-line cover theorem.  `conflictScaleLarge` says that the
already-selected all-coordinate coloring was built at least at the literal
partitioning separation threshold for the enlarged middle radius.
-/
private noncomputable def
    pureWZ2_prop62_metricFiber_representativeMiddleConstruction
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow sourceConstant : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    (packetCoordinate : Fin schedule.levelCount)
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    {upperColoring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {conflictScale : Fin schedule.levelCount → ℝ}
    {conflictDegree : Fin schedule.levelCount → ℕ}
    (allScale :
      PureWZ2Prop62ProxyQuotientAllScaleColorPreCoreData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metricCore.metric upperColoring
          conflictScale conflictDegree)
    (preliminary_eq :
      metricCore.cleanup.preliminary =
        allScale.adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (parent : Fin metricCore.restriction.coarseSelected.family.card)
    (coordinate : Fin schedule.levelCount)
    (descendant :
      PureWZ2Prop62ProxyQuotientFiberDescendantData
        metricCore sourceConstant parent coordinate)
    (actualSmall :
      schedule.actualScale coordinate ≤ 1 / 10000)
    (conflictScaleLarge :
      wz2PaperLiteralSourceSeparationFactor *
          (pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
            schedule.actualScale coordinate) ≤
        conflictScale coordinate) :
    PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData
      metricCore parent coordinate descendant := by
  let analytic := descendant.scaleData
  let selected :=
    PureWZ2Prop62ProxyQuotientAllScaleColorPreCoreData.finalMetricFiberAmbientSubfamily
      metricCore parent
  let hit :=
    (schedule.scaleData coordinate).cover.hitParentSubfamily selected
  let middleScale :=
    pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
      schedule.actualScale coordinate
  let middle :=
    PureWZ2Prop62RepresentativeParentColoringData.hitRepresentativeLineFamily
      schedule fineNonempty coordinate middleScale selected
  have localNonempty :
      (metricCore.restriction.metricFiberSource parent).family.Nonempty := by
    change 0 <
      (wz2PaperFullFiberIndices
        metricCore.restriction.fineSelected.family
        metricCore.restriction.coarseSelected.family parent).card
    rcases metricCore.restriction.section6Cover.parent_hit parent with
      ⟨source, covered⟩
    exact Finset.card_pos.mpr
      ⟨source,
        (mem_wz2PaperFullFiberIndices_iff parent source).mpr covered⟩
  letI : Nonempty (Fin selected.family.card) :=
    Fin.pos_iff_nonempty.mp localNonempty
  have analyticParentSurjective :
      Function.Surjective analytic.cover.parent :=
    analytic.cover.parent_surjective_of_uniform
      analytic.rho_pos.le localNonempty analytic.full_fiber_uniform
  have hitParentSurjective :
      Function.Surjective
        ((schedule.scaleData coordinate).cover.hitParent selected) :=
    (schedule.scaleData coordinate).cover.hitParent_surjective selected
  have selectedEmbedding :
      ∀ source : Fin selected.family.card,
        selected.embedding source =
          metricCore.metricFiberAmbientIndex parent source := by
    intro source
    rfl
  have selectedTubeEq :
      ∀ source : Fin selected.family.card,
        selected.family.tube source =
          (metricCore.restriction.metricFiberSource parent).family.tube
            source := by
    intro source
    rfl
  have hitParentAmbient :
      ∀ source : Fin selected.family.card,
        hit.embedding
            ((schedule.scaleData coordinate).cover.hitParent
              selected source) =
          (schedule.scaleData coordinate).cover.parent
            (metricCore.metricFiberAmbientIndex parent source) := by
    intro source
    rw [(schedule.scaleData coordinate).cover.hitParent_ambient]
    rw [selectedEmbedding]
  have compatible :
      ∀ first second : Fin selected.family.card,
        ((schedule.scaleData coordinate).cover.hitParent
            selected first =
          (schedule.scaleData coordinate).cover.hitParent
            selected second) ↔
        analytic.cover.parent first = analytic.cover.parent second := by
    intro first second
    constructor
    · intro equality
      apply descendant.parent_embedding.injective
      rw [descendant.parent_commutes, descendant.parent_commutes]
      rw [
        ← hitParentAmbient first,
        ← hitParentAmbient second,
        equality
      ]
    · intro equality
      apply hit.embedding.injective
      rw [hitParentAmbient, hitParentAmbient]
      rw [
        ← descendant.parent_commutes first,
        ← descendant.parent_commutes second,
        equality
      ]
  let parentEquiv : Fin middle.card ≃ Fin analytic.coarse.card :=
    finiteParentEquiv
      ((schedule.scaleData coordinate).cover.hitParent selected)
      analytic.cover.parent hitParentSurjective analyticParentSurjective
      compatible
  have parentEquiv_apply :
      ∀ source : Fin selected.family.card,
        parentEquiv
            ((schedule.scaleData coordinate).cover.hitParent
              selected source) =
          analytic.cover.parent source := by
    intro source
    exact
      finiteParentEquiv_apply
        ((schedule.scaleData coordinate).cover.hitParent selected)
      analytic.cover.parent hitParentSurjective analyticParentSurjective
        compatible source
  have middlePos : 0 < middleScale := by
    dsimp only [middleScale]
    exact mul_pos
      (by
        rw [pureWZ2Prop62MetricFiberRepresentativeMiddleFactor,
          pureWZ2Prop62RepresentativeParentScaledFactor_eq]
        norm_num)
      analytic.rho_pos
  have localLine :
      WZ1PaperIsLineClass
        (metricCore.restriction.metricFiberSource parent).family := by
    intro source
    rw [← metricCore.metricFiberAmbientIndex_tube]
    exact fineLine (metricCore.metricFiberAmbientIndex parent source)
  have middleLine : WZ1PaperIsLineClass middle := by
    exact
      PureWZ2Prop62RepresentativeParentColoringData.hitRepresentativeLineFamily_lineClass
        (schedule := schedule) (fineNonempty := fineNonempty)
        fineLine coordinate middleScale selected
  have assignedLineCover :
      ∀ source : Fin selected.family.card,
        WZ1PaperTubeCovers
          (selected.family.tube source)
          (middle.tube
            ((schedule.scaleData coordinate).cover.hitParent
              selected source)) := by
    intro source
    have ambientCover :=
      schedule.parentRepresentative_lineCover
        fineNonempty fineLine fineBase coordinate actualSmall
        middleScale
        (by
          dsimp only [middleScale]
          have actualPos := analytic.rho_pos
          rw [pureWZ2Prop62MetricFiberRepresentativeMiddleFactor,
            pureWZ2Prop62RepresentativeParentScaledFactor_eq]
          exact le_rfl)
        (selected.embedding source)
    change
      WZ1PaperTubeCovers
        (selected.family.tube source)
        ((schedule.representativeLineFamily
          fineNonempty coordinate middleScale).tube
            (hit.embedding
              ((schedule.scaleData coordinate).cover.hitParent
                selected source)))
    rw [selected.tube_eq, hitParentAmbient]
    exact ambientCover
  have assignedCarrier :
      ∀ source : Fin selected.family.card,
        (selected.family.tube source).carrier ⊆
          (middle.tube
            ((schedule.scaleData coordinate).cover.hitParent
              selected source)).carrier := by
    intro source
    let ambientSource := selected.embedding source
    let ambientParent :=
      (schedule.scaleData coordinate).cover.parent ambientSource
    let representativeSource :=
      schedule.parentRepresentative
        fineNonempty coordinate ambientParent
    let representative :=
      wz2PaperCanonicalLineTube (fine.tube representativeSource)
    have sourceActual :
        (fine.tube ambientSource).carrier ⊆
          ((schedule.scaleData coordinate).coarse.tube
            ambientParent).carrier :=
      (mem_wz2PaperOrdinaryFullFiberIndices_iff
        ambientParent ambientSource).mp
        ((schedule.scaleData coordinate).cover
          |>.parent_mem_fullFiber ambientSource)
    have representativeActual :
        (fine.tube representativeSource).carrier ⊆
          ((schedule.scaleData coordinate).coarse.tube
            ambientParent).carrier :=
      (mem_wz2PaperOrdinaryFullFiberIndices_iff
        ambientParent representativeSource).mp
        (schedule.parentRepresentative_mem
          fineNonempty coordinate ambientParent)
    have actualRepresentative :=
      actualParent_carrier_subset_representative
        (schedule.scaleData coordinate).delta_pos
        (schedule.scaleData coordinate).rho_pos
        (by
          have actualPos := (schedule.scaleData coordinate).rho_pos
          change
            8 * schedule.actualScale coordinate ≤
              pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
                schedule.actualScale coordinate
          rw [pureWZ2Prop62MetricFiberRepresentativeMiddleFactor,
            pureWZ2Prop62RepresentativeParentScaledFactor_eq]
          exact
            mul_le_mul_of_nonneg_right
              (by norm_num : (8 : ℝ) ≤ 1200000)
              actualPos.le)
        representativeActual
    have sourceEnvelope := sourceActual.trans actualRepresentative
    rw [selected.tube_eq,
      PureWZ2Prop62RepresentativeParentColoringData.hitRepresentativeLineFamily_tube,
      hitParentAmbient]
    exact sourceEnvelope
  have middleSeparated :
      ∀ first second : Fin middle.card,
        first ≠ second →
          wz2PaperLiteralSourceSeparationFactor * middleScale <
            wz1PaperLineDistance
              (middle.tube first) (middle.tube second) := by
    intro first second distinct
    exact
      conflictScaleLarge.trans_lt <|
        allScale.finalMetricFiber_hitRepresentativeLineFamily_stronglySeparated
          metricCore rfl preliminary_eq parent coordinate middleScale
          first second distinct
  let cover : WZ2PaperPurePartitioningCover selected.family middle :=
    {
      covers := by
        intro source
        refine
          ⟨(schedule.scaleData coordinate).cover.hitParent
              selected source, ?_⟩
        rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
        exact assignedCarrier source
      doubled_fibers_disjoint := by
        intro first second distinct
        rw [Finset.disjoint_left]
        intro source firstMem secondMem
        have sourceBase :
            ‖((metricCore.restriction.metricFiberSource parent).family.tube
                source).base‖ ≤ 5 := by
          rw [← metricCore.metricFiberAmbientIndex_tube]
          exact fineBase (metricCore.metricFiberAmbientIndex parent source)
        have sourceMidpoint :
            ‖wz2PaperTubeMidpoint (selected.family.tube source)‖ ≤ 6 := by
          rw [selectedTubeEq source]
          unfold wz2PaperTubeMidpoint
          calc
            ‖((metricCore.restriction.metricFiberSource parent).family.tube
                  source).base +
                (1 / 2 : ℝ) •
                  ((metricCore.restriction.metricFiberSource parent).family.tube
                    source).direction‖ ≤
                ‖((metricCore.restriction.metricFiberSource parent).family.tube
                    source).base‖ +
                  ‖(1 / 2 : ℝ) •
                    ((metricCore.restriction.metricFiberSource parent).family.tube
                      source).direction‖ :=
              norm_add_le _ _
            _ ≤ 5 + 1 / 2 := by
              rw [norm_smul, Real.norm_eq_abs,
                ((metricCore.restriction.metricFiberSource parent).family.tube
                  source).direction_unit]
              norm_num
              nlinarith
            _ ≤ 6 := by norm_num
        have firstDistance :=
          wz2_paper_bounded_centered_doubled_containment_lineDistance_le
            analytic.delta_pos middlePos
            (localLine source) (middleLine first)
            6 sourceMidpoint
            (by
              rw [← selectedTubeEq source]
              exact
                (mem_wz2PaperOrdinaryDilatedFiberIndices_iff
                  first source).mp firstMem)
        have secondDistance :=
          wz2_paper_bounded_centered_doubled_containment_lineDistance_le
            analytic.delta_pos middlePos
            (localLine source) (middleLine second)
            6 sourceMidpoint
            (by
              rw [← selectedTubeEq source]
              exact
                (mem_wz2PaperOrdinaryDilatedFiberIndices_iff
                  second source).mp secondMem)
        have triangle :=
          wz1PaperLineDistance_triangle
            (middle.tube first) (selected.family.tube source)
            (middle.tube second)
        have symmetry :
            wz1PaperLineDistance
                (middle.tube first) (selected.family.tube source) =
              wz1PaperLineDistance
                (selected.family.tube source) (middle.tube first) :=
          wz1PaperLineDistance_symm _ _
        rw [symmetry] at triangle
        have firstDistance' :
            wz1PaperLineDistance
                (selected.family.tube source) (middle.tube first) ≤
              140 * middleScale := by
          rw [selectedTubeEq source]
          norm_num at firstDistance ⊢
          exact firstDistance
        have secondDistance' :
            wz1PaperLineDistance
                (selected.family.tube source) (middle.tube second) ≤
              140 * middleScale := by
          rw [selectedTubeEq source]
          norm_num at secondDistance ⊢
          exact secondDistance
        have separated := middleSeparated first second distinct
        norm_num [wz2PaperLiteralSourceSeparationFactor] at separated
        nlinarith [middlePos]
    }
  have coverParentEq :
      ∀ source : Fin selected.family.card,
        cover.parent source =
          (schedule.scaleData coordinate).cover.hitParent
            selected source := by
    intro source
    apply
      (cover.mem_fullFiber_iff_parent_eq
        middlePos.le
        ((schedule.scaleData coordinate).cover.hitParent
          selected source) source).mp
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    exact assignedCarrier source
  have bridgeParentCommutes :
      ∀ source : Fin selected.family.card,
        parentEquiv (cover.parent source) =
          analytic.cover.parent source := by
    intro source
    rw [coverParentEq]
    exact parentEquiv_apply source
  have fiberIndicesEq :
      ∀ middleParent : Fin middle.card,
        wz2PaperOrdinaryFullFiberIndices
            selected.family middle middleParent =
          wz2PaperOrdinaryFullFiberIndices
            selected.family analytic.coarse
              (parentEquiv middleParent) := by
    intro middleParent
    ext source
    have analyticMem :
        source ∈
            wz2PaperOrdinaryFullFiberIndices
              selected.family analytic.coarse
                (parentEquiv middleParent) ↔
          analytic.cover.parent source = parentEquiv middleParent := by
      change
        source ∈
            wz2PaperOrdinaryFullFiberIndices
              (metricCore.restriction.metricFiberSource parent).family
              analytic.coarse (parentEquiv middleParent) ↔
          analytic.cover.parent source = parentEquiv middleParent
      exact analytic.cover.mem_fullFiber_iff_parent_eq
        analytic.rho_pos.le (parentEquiv middleParent) source
    rw [
      cover.mem_fullFiber_iff_parent_eq
        middlePos.le middleParent source,
      analyticMem
    ]
    constructor
    · intro equality
      rw [← bridgeParentCommutes source]
      exact congrArg parentEquiv equality
    · intro equality
      apply parentEquiv.injective
      rw [bridgeParentCommutes source]
      exact equality
  let bridge :
      WZ2PaperMiddleFamilyScaleBridge
        (K := pureWZ2Prop62MetricFiberRepresentativeMiddleJohnLoss)
        analytic middle :=
    {
      middle_pos := middlePos
      cover := cover
      parentEquiv := parentEquiv
      parent_commutes := bridgeParentCommutes
      loss_one := by
        calc
          (1 : ENNReal) ≤ 27 * 1 := by norm_num
          _ ≤
              27 *
                ENNReal.ofReal
                  (pureWZ2Prop62MetricFiberRepresentativeMiddleFactor ^ 3) := by
            gcongr
            rw [pureWZ2Prop62MetricFiberRepresentativeMiddleFactor,
              pureWZ2Prop62RepresentativeParentScaledFactor_eq]
            norm_num
      loss_ne_top := by
        unfold pureWZ2Prop62MetricFiberRepresentativeMiddleJohnLoss
        exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
      fiberTransport := by
        intro middleParent sourceFiber
        let targetJohn :=
          WZ2PaperAssouadUnitRescalingData.ofTube
            (middle.tube middleParent) middlePos
        let indexEquiv :=
          fullFiberBodyIndexEquivOfEq
            middleParent (parentEquiv middleParent)
            (fiberIndicesEq middleParent)
        refine
          {
            normalization := targetJohn
            indexEquiv := indexEquiv
            carrier_containment := ?_
            outerJohnVolume_le := ?_
          }
        · intro targetIndex
          change
            wz2PaperGeneralJohnToJohnCoordinateChange
                  sourceFiber.normalization targetJohn ''
                (sourceFiber.normalization.map ''
                  (selected.family.tube
                    ((wz2PaperOrdinaryFullFiberIndexEquiv
                      (fine := selected.family)
                      (coarse := analytic.coarse)
                      (parentEquiv middleParent))
                        (indexEquiv targetIndex)).1).carrier) ⊆
              targetJohn.map ''
                (selected.family.tube
                  ((wz2PaperOrdinaryFullFiberIndexEquiv
                    (fine := selected.family) (coarse := middle)
                    middleParent) targetIndex).1).carrier
          rw [
            wz2PaperGeneralJohnToJohnCoordinateChange_image,
            fullFiberBodyIndexEquivOfEq_source
              middleParent (parentEquiv middleParent)
                (fiberIndicesEq middleParent) targetIndex
          ]
        · exact
            wz2PaperFactor_outerJohn_volume_le
              analytic.rho_pos
              (by
                rw [pureWZ2Prop62MetricFiberRepresentativeMiddleFactor,
                  pureWZ2Prop62RepresentativeParentScaledFactor_eq]
                norm_num)
              (analytic.coarse.tube (parentEquiv middleParent))
              (middle.tube middleParent)
              sourceFiber.normalization targetJohn
    }
  let lineCover :
      WZ1PaperTubeCover selected.family middle :=
    {
      parent := cover.parent
      parent_surjective := by
        intro middleParent
        rcases hitParentSurjective middleParent with ⟨source, sourceEq⟩
        exact ⟨source, (coverParentEq source).trans sourceEq⟩
      parent_covers := by
        intro source
        rw [coverParentEq]
        exact assignedLineCover source
      parent_unique := by
        intro source candidate candidateCover
        by_contra distinct
        have separated :=
          middleSeparated candidate (cover.parent source) distinct
        have assignedCover : WZ1PaperTubeCovers
            (selected.family.tube source)
            (middle.tube (cover.parent source)) := by
          rw [coverParentEq]
          exact assignedLineCover source
        have triangle :=
          wz1PaperLineDistance_triangle
            (middle.tube candidate)
            (selected.family.tube source)
            (middle.tube (cover.parent source))
        have symmetry :
            wz1PaperLineDistance
                (middle.tube candidate) (selected.family.tube source) =
              wz1PaperLineDistance
                (selected.family.tube source) (middle.tube candidate) :=
          wz1PaperLineDistance_symm _ _
        rw [symmetry] at triangle
        unfold WZ1PaperTubeCovers at candidateCover assignedCover
        norm_num [wz2PaperLiteralSourceSeparationFactor] at separated
        nlinarith [middlePos]
    }
  exact
    {
      bridge := bridge
      lineCover := lineCover
      lineCover_parent_eq := rfl
      coarse_line_class := middleLine
      separated := middleSeparated
    }

/-- The reusable analytic-to-representative middle-family bridge. -/
noncomputable def pureWZ2_prop62_metricFiber_representativeMiddle
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow sourceConstant : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData schedule fineNonempty}
    {width : ℝ}
    (packetCoordinate : Fin schedule.levelCount)
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    {upperColoring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {conflictScale : Fin schedule.levelCount → ℝ}
    {conflictDegree : Fin schedule.levelCount → ℕ}
    (allScale :
      PureWZ2Prop62ProxyQuotientAllScaleColorPreCoreData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metricCore.metric upperColoring
          conflictScale conflictDegree)
    (preliminary_eq :
      metricCore.cleanup.preliminary =
        allScale.adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (parent : Fin metricCore.restriction.coarseSelected.family.card)
    (coordinate : Fin schedule.levelCount)
    (descendant :
      PureWZ2Prop62ProxyQuotientFiberDescendantData
        metricCore sourceConstant parent coordinate)
    (actualSmall :
      schedule.actualScale coordinate ≤ 1 / 10000)
    (conflictScaleLarge :
      wz2PaperLiteralSourceSeparationFactor *
          (pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
            schedule.actualScale coordinate) ≤
        conflictScale coordinate) :
    WZ2PaperMiddleFamilyScaleBridge
      (K := pureWZ2Prop62MetricFiberRepresentativeMiddleJohnLoss)
      descendant.scaleData
      (pureWZ2Prop62MetricFiberRepresentativeMiddleFamily
        metricCore parent coordinate) :=
  (pureWZ2_prop62_metricFiber_representativeMiddleConstruction
    schedule packetCoordinate metricCore allScale preliminary_eq
    fineLine fineBase parent coordinate descendant actualSmall
    conflictScaleLarge).bridge

namespace PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow sourceConstant : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    {metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {parent : Fin metricCore.restriction.coarseSelected.family.card}
    {coordinate : Fin schedule.levelCount}
    {descendant :
      PureWZ2Prop62ProxyQuotientFiberDescendantData
        metricCore sourceConstant parent coordinate}
    (data :
      PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData
        metricCore parent coordinate descendant)

/-- The transported scale data, with its middle family made explicit. -/
noncomputable def middleScaleData :
    WZ2PaperPureScaleCoverData
      (metricCore.restriction.metricFiberSource parent).family
      (pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
        schedule.actualScale coordinate)
      (pureWZ2Prop62MetricFiberRepresentativeMiddleJohnLoss *
        sourceConstant) :=
  WZ2PaperMiddleFamilyScaleBridge.middleScaleData
    (PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.bridge
      data)

/-- The saved line cover covers every source with the transported pure parent. -/
theorem parent_covers
    (source :
      Fin (metricCore.restriction.metricFiberSource parent).family.card) :
    WZ1PaperTubeCovers
      ((metricCore.restriction.metricFiberSource parent).family.tube source)
      ((PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.middleScaleData data).coarse.tube
        ((PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.middleScaleData data).cover.parent source)) := by
  change
    WZ1PaperTubeCovers
      ((metricCore.restriction.metricFiberSource parent).family.tube source)
      ((pureWZ2Prop62MetricFiberRepresentativeMiddleFamily
        metricCore parent coordinate).tube
          ((WZ2PaperMiddleFamilyScaleBridge.cover
            (PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.bridge
              data)).parent source))
  rw [←
    PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.lineCover_parent_eq
      data]
  exact
    (PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.lineCover
      data).parent_covers source

/-- Every representative middle parent remains in the final metric parent. -/
theorem parent_near_anchor
    (actualLeRho :
      pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
          schedule.actualScale coordinate ≤ rho) :
    ∀ middle,
      WZ2PaperDilatedTubeCovers 2
        ((PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.middleScaleData data).coarse.tube middle)
        (metricCore.restriction.coarseSelected.family.tube parent) := by
  intro middle
  have sourceNonempty :
      (metricCore.restriction.metricFiberSource parent).family.Nonempty :=
    metricCore.metricFiberSource_nonempty parent
  have middleFiberNonempty :=
    (PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.middleScaleData data).cover.fullFiber_nonempty_of_uniform
      sourceNonempty
      (PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.middleScaleData data).full_fiber_uniform middle
  rcases middleFiberNonempty with ⟨source, sourceMem⟩
  have sourceParent :
      (PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.middleScaleData data).cover.parent source = middle :=
    ((PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.middleScaleData data).cover.mem_fullFiber_iff_parent_eq
      (PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.middleScaleData data).rho_pos.le middle source).mp sourceMem
  have fineToMiddle :=
    PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.parent_covers
      data source
  rw [sourceParent] at fineToMiddle
  have fineToAnchor :=
    metricCore.metricFiberSource_parent_covers parent source
  have triangle :=
    wz1PaperLineDistance_triangle
      ((PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.middleScaleData data).coarse.tube middle)
      ((metricCore.restriction.metricFiberSource parent).family.tube source)
      (metricCore.restriction.coarseSelected.family.tube parent)
  have symmetry :
      wz1PaperLineDistance
          ((PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.middleScaleData data).coarse.tube middle)
          ((metricCore.restriction.metricFiberSource parent).family.tube
            source) =
        wz1PaperLineDistance
          ((metricCore.restriction.metricFiberSource parent).family.tube
            source)
          ((PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.middleScaleData data).coarse.tube middle) :=
    wz1PaperLineDistance_symm _ _
  rw [symmetry] at triangle
  unfold WZ1PaperTubeCovers at fineToMiddle fineToAnchor
  unfold WZ2PaperDilatedTubeCovers
  have middleScaleLe :
      pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
          schedule.actualScale coordinate ≤ rho :=
    actualLeRho
  nlinarith

/-- The final metric fiber inherits the ambient source line class. -/
theorem source_line_class :
    WZ1PaperIsLineClass
      (metricCore.restriction.metricFiberSource parent).family :=
  metricCore.restriction.section6Cover.fine_line_class.subfamily
    (metricCore.restriction.metricFiberSource parent).toTubeSubfamily

/-- Target fine tubes are local after rescaling by the final metric parent. -/
theorem target_local
    (rhoLeOne : rho ≤ 1)
    (fineBoundedBase : HasBoundedBase fine 4) :
    ∀ target,
      ‖wz2PaperTubeMidpoint
        ((wz2PaperLiteralOrdinaryRescaledFamily
          (metricCore.restriction.metricFiberSource parent).family
          (metricCore.restriction.coarseSelected.family.tube parent)
          metricCore.metric.metricInput.rho_pos).tube target)‖ ≤ 3 := by
  intro target
  exact
    wz2PaperLiteralOrdinaryRescaledTube_midpoint_norm_le_three_of_boundedBase
      metricCore.metric.metricInput.rho_pos rhoLeOne
      ((metricCore.restriction.metricFiberSource parent).family.tube target)
      (metricCore.restriction.coarseSelected.family.tube parent)
      (PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.source_line_class
        (metricCore := metricCore) (parent := parent) target)
      (by
        rw [← metricCore.metricFiberAmbientIndex_tube]
        exact
          fineBoundedBase
            (metricCore.metricFiberAmbientIndex parent target))
      (metricCore.metricFiberSource_parent_covers parent target)

/-- Ordinary nested localization for the representative middle family. -/
theorem localization
    (rhoLeOne : rho ≤ 1)
    (fineBoundedBase : HasBoundedBase fine 4)
    (actualLeRho :
      pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
          schedule.actualScale coordinate ≤ rho) :
    WZ2PaperOrdinaryNestedTargetLocalization
      (metricCore.restriction.metricFiberSource parent).family
      (PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.middleScaleData data).coarse
      (metricCore.restriction.coarseSelected.family.tube parent)
      metricCore.metric.metricInput.rho_pos :=
  wz2PaperOrdinaryNestedTargetLocalization_of_sourceCovers
    (PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.middleScaleData data).delta_pos
    (PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.middleScaleData data).rho_pos
    metricCore.metric.metricInput.rho_pos rhoLeOne
    (metricCore.restriction.metricFiberSource parent).family
    (PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.middleScaleData data).coarse
    (metricCore.restriction.coarseSelected.family.tube parent)
    (PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.source_line_class
      (metricCore := metricCore) (parent := parent))
    (PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.coarse_line_class data)
    (metricCore.restriction.section6Cover.coarse_line_class parent)
    (metricCore.metricFiberSource_parent_covers parent)
    (PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.parent_near_anchor data actualLeRho)
    (PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.target_local
      (metricCore := metricCore) (parent := parent)
      rhoLeOne fineBoundedBase)

/--
Package the representative middle bridge as the exact local descendant
consumed by the quotient requested-scale route.
-/
noncomputable def toRouteDescendantData
    (rhoLeOne : rho ≤ 1)
    (fineBoundedBase : HasBoundedBase fine 4)
    (actualLeRho :
      pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
          schedule.actualScale coordinate ≤ rho) :
    PureWZ2Prop62ProxyQuotientFiberRouteDescendantData
      metricCore
      (pureWZ2Prop62MetricFiberRepresentativeMiddleJohnLoss *
        sourceConstant)
      pureWZ2Prop62MetricFiberRepresentativeMiddleFactor
      parent coordinate := by
  exact
    {
      actual :=
        pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
          schedule.actualScale coordinate
      actual_eq_scaled := rfl
      scaleData :=
        PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.middleScaleData data
      partitioningCover :=
        WZ2PaperMiddleFamilyScaleBridge.cover
          (PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.bridge
            data)
      partitioningCover_eq := rfl
      coarse_line_class :=
        PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.coarse_line_class
          data
      lineCover :=
        PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.lineCover
          data
      lineCover_parent_eq :=
        PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.lineCover_parent_eq
          data
      parent_near_anchor :=
        PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.parent_near_anchor data actualLeRho
      separated :=
        PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.separated
          data
      localization :=
        PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.localization
          data rhoLeOne fineBoundedBase actualLeRho
    }

end PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData

/--
One-step constructor directly consumable by
`PureWZ2Prop62ProxyQuotientFiberRouteInput.descendant`.
-/
noncomputable def
    pureWZ2_prop62_metricFiber_representativeRouteDescendant
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow sourceConstant : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData schedule fineNonempty}
    {width : ℝ}
    (packetCoordinate : Fin schedule.levelCount)
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    {upperColoring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {conflictScale : Fin schedule.levelCount → ℝ}
    {conflictDegree : Fin schedule.levelCount → ℕ}
    (allScale :
      PureWZ2Prop62ProxyQuotientAllScaleColorPreCoreData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metricCore.metric upperColoring
          conflictScale conflictDegree)
    (preliminary_eq :
      metricCore.cleanup.preliminary =
        allScale.adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (parent : Fin metricCore.restriction.coarseSelected.family.card)
    (coordinate : Fin schedule.levelCount)
    (descendant :
      PureWZ2Prop62ProxyQuotientFiberDescendantData
        metricCore sourceConstant parent coordinate)
    (actualSmall :
      schedule.actualScale coordinate ≤ 1 / 10000)
    (conflictScaleLarge :
      wz2PaperLiteralSourceSeparationFactor *
          (pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
            schedule.actualScale coordinate) ≤
        conflictScale coordinate)
    (rhoLeOne : rho ≤ 1)
    (fineBoundedBase : HasBoundedBase fine 4)
    (actualLeRho :
      pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
          schedule.actualScale coordinate ≤ rho) :
    PureWZ2Prop62ProxyQuotientFiberRouteDescendantData
      metricCore
      (pureWZ2Prop62MetricFiberRepresentativeMiddleJohnLoss *
        sourceConstant)
      pureWZ2Prop62MetricFiberRepresentativeMiddleFactor
      parent coordinate :=
  PureWZ2Prop62MetricFiberRepresentativeMiddleConstructionData.toRouteDescendantData
      (pureWZ2_prop62_metricFiber_representativeMiddleConstruction
        schedule packetCoordinate metricCore allScale preliminary_eq
        fineLine fineBase parent coordinate descendant actualSmall
        conflictScaleLarge)
      rhoLeOne fineBoundedBase actualLeRho

end Kakeya.Assouad

end
