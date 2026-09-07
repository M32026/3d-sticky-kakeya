import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientFiberCWA
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryNestedLocalization
import Mathlib.Tactic

/-!
# Proposition 6.2 quotient metric-fiber requested route

The public laminar schedule and the quotient metric core live on the same
ambient fine family.  Each descendant carries its own actual scale, pure
partitioning witness, line cover, line class, parent separation, and nested
localization.  The scalar route rounds at the old physical scale and exposes
the scaled descendant `scaleFactor * r`.

No ambient-wide line schedule, aligned exact-source object, alternate fine
family, or second tree cleanup is introduced.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Canonical enlargement from one rounded laminar scale to the route scale. -/
def pureWZ2Prop62ProxyQuotientFiberRouteScaleFactor : ℕ :=
  1200000

@[simp] theorem pureWZ2Prop62ProxyQuotientFiberRouteScaleFactor_eq :
    pureWZ2Prop62ProxyQuotientFiberRouteScaleFactor = 1200000 :=
  rfl

theorem pureWZ2Prop62ProxyQuotientFiberRouteScaleFactor_one :
    (1 : ℝ) ≤ pureWZ2Prop62ProxyQuotientFiberRouteScaleFactor := by
  norm_num [pureWZ2Prop62ProxyQuotientFiberRouteScaleFactor]

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
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)

/-- The ambient fine index of one member of a final genuine metric fiber. -/
def metricFiberAmbientIndex
    (parent :
      Fin metricCore.restriction.coarseSelected.family.card)
    (source :
      Fin
        (metricCore.restriction.metricFiberSource parent).family.card) :
    Fin fine.card :=
  metricCore.metric.mesh.complete.selectedFine.embedding <|
    metricCore.restriction.fineSelected.embedding <|
      (metricCore.restriction.metricFiberSource parent).embedding source

@[simp] theorem metricFiberAmbientIndex_tube
    (parent :
      Fin metricCore.restriction.coarseSelected.family.card)
    (source :
      Fin
        (metricCore.restriction.metricFiberSource parent).family.card) :
    fine.tube (metricCore.metricFiberAmbientIndex parent source) =
      (metricCore.restriction.metricFiberSource parent).family.tube
        source := by
  rw [metricFiberAmbientIndex,
    (metricCore.restriction.metricFiberSource parent).tube_eq,
    metricCore.restriction.fineSelected.tube_eq,
    metricCore.metric.mesh.complete.selectedFine.tube_eq]

/-- Every final genuine metric fiber is nonempty. -/
theorem metricFiberSource_nonempty
    (parent :
      Fin metricCore.restriction.coarseSelected.family.card) :
    (metricCore.restriction.metricFiberSource parent).family.Nonempty := by
  change
    0 <
      (wz2PaperFullFiberIndices
        metricCore.restriction.fineSelected.family
        metricCore.restriction.coarseSelected.family parent).card
  rcases metricCore.restriction.section6Cover.parent_hit parent with
    ⟨source, covered⟩
  exact
    Finset.card_pos.mpr
      ⟨source,
        (mem_wz2PaperFullFiberIndices_iff parent source).mpr
          covered⟩

/-- Every member of a final genuine metric fiber is covered by its parent. -/
theorem metricFiberSource_parent_covers
    (parent :
      Fin metricCore.restriction.coarseSelected.family.card)
    (source :
      Fin
        (metricCore.restriction.metricFiberSource parent).family.card) :
    WZ1PaperTubeCovers
      ((metricCore.restriction.metricFiberSource parent).family.tube source)
      (metricCore.restriction.coarseSelected.family.tube parent) := by
  rw [(metricCore.restriction.metricFiberSource parent).tube_eq]
  exact
    (mem_wz2PaperFullFiberIndices_iff parent
      ((metricCore.restriction.metricFiberSource parent).embedding
        source)).mp
      (Finset.orderEmbOfFin_mem
        (wz2PaperFullFiberIndices
          metricCore.restriction.fineSelected.family
          metricCore.restriction.coarseSelected.family parent)
        rfl source)

end PureWZ2Prop62ProxyQuotientMetricCoreOutput

/--
Compatibility data identifying an analytic descendant with one ambient
laminar coordinate.

New route inputs should instead supply
`PureWZ2Prop62ProxyQuotientFiberRouteDescendantData`, whose line geometry is
local to the actual middle scale used by the route.
-/
structure PureWZ2Prop62ProxyQuotientFiberDescendantData
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
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (sourceConstant : ENNReal)
    (parent :
      Fin metricCore.restriction.coarseSelected.family.card)
    (coordinate : Fin schedule.levelCount) where
  scaleData :
    WZ2PaperPureScaleCoverData
      (metricCore.restriction.metricFiberSource parent).family
      (schedule.actualScale coordinate) sourceConstant
  parent_embedding :
    Fin scaleData.coarse.card ↪
      Fin (schedule.scaleData coordinate).coarse.card
  parent_tube_eq :
    ∀ middle,
      scaleData.coarse.tube middle =
        (schedule.scaleData coordinate).coarse.tube
          (parent_embedding middle)
  parent_commutes :
    ∀ source,
      parent_embedding (scaleData.cover.parent source) =
        (schedule.scaleData coordinate).cover.parent
          (metricCore.metricFiberAmbientIndex parent source)

/--
One self-contained descendant witness on a final genuine metric fiber.

The analytic scale in the ambient laminar schedule is only recorded through
`actual_eq_scaled`.  All line geometry consumed by the ordinary nested-scale
constructor belongs to `scaleData.coarse` at the actual route scale.
-/
structure PureWZ2Prop62ProxyQuotientFiberRouteDescendantData
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
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (sourceConstant : ENNReal)
    (scaleFactor : ℝ)
    (parent :
      Fin metricCore.restriction.coarseSelected.family.card)
    (coordinate : Fin schedule.levelCount) where
  actual : ℝ
  actual_eq_scaled :
    actual = scaleFactor * schedule.actualScale coordinate
  scaleData :
    WZ2PaperPureScaleCoverData
      (metricCore.restriction.metricFiberSource parent).family
      actual sourceConstant
  partitioningCover :
    WZ2PaperPurePartitioningCover
      (metricCore.restriction.metricFiberSource parent).family
      scaleData.coarse
  partitioningCover_eq :
    partitioningCover = scaleData.cover
  coarse_line_class :
    WZ1PaperIsLineClass scaleData.coarse
  lineCover :
    WZ1PaperTubeCover
      (metricCore.restriction.metricFiberSource parent).family
      scaleData.coarse
  lineCover_parent_eq :
    lineCover.parent = partitioningCover.parent
  parent_near_anchor :
    ∀ middle,
      WZ2PaperDilatedTubeCovers 2
        (scaleData.coarse.tube middle)
        (metricCore.restriction.coarseSelected.family.tube parent)
  separated :
    ∀ first second, first ≠ second →
      wz2PaperLiteralSourceSeparationFactor * actual <
        wz1PaperLineDistance
          (scaleData.coarse.tube first)
          (scaleData.coarse.tube second)
  localization :
    WZ2PaperOrdinaryNestedTargetLocalization
      (metricCore.restriction.metricFiberSource parent).family
      scaleData.coarse
      (metricCore.restriction.coarseSelected.family.tube parent)
      metricCore.metric.metricInput.rho_pos

namespace PureWZ2Prop62ProxyQuotientFiberRouteDescendantData

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
    {metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {sourceConstant : ENNReal}
    {scaleFactor : ℝ}
    {parent :
      Fin metricCore.restriction.coarseSelected.family.card}
    {coordinate : Fin schedule.levelCount}
    (data :
      PureWZ2Prop62ProxyQuotientFiberRouteDescendantData
        metricCore sourceConstant scaleFactor parent coordinate)

/-- The local line cover covers with the same parent as the partitioning cover. -/
theorem parent_covers
    (source :
      Fin (metricCore.restriction.metricFiberSource parent).family.card) :
    WZ1PaperTubeCovers
      ((metricCore.restriction.metricFiberSource parent).family.tube source)
      (data.scaleData.coarse.tube (data.scaleData.cover.parent source)) := by
  rw [← data.partitioningCover_eq, ← data.lineCover_parent_eq]
  exact data.lineCover.parent_covers source

end PureWZ2Prop62ProxyQuotientFiberRouteDescendantData

/--
Compatibility conversion from an old ambient-coordinate descendant.

This constructor is deliberately restricted to scale factor one.  It packages
all ambient line geometry into the local descendant record; the new route
consumer never sees the ambient-wide hypotheses.
-/
noncomputable def PureWZ2Prop62ProxyQuotientFiberDescendantData.toRouteDescendantData
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
    {metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {sourceConstant : ENNReal}
    {parent :
      Fin metricCore.restriction.coarseSelected.family.card}
    {coordinate : Fin schedule.levelCount}
    (data :
      PureWZ2Prop62ProxyQuotientFiberDescendantData
        metricCore sourceConstant parent coordinate)
    (rhoLeOne : rho ≤ 1)
    (fineBoundedBase : HasBoundedBase fine 4)
    (coarseLineClass :
      WZ1PaperIsLineClass (schedule.scaleData coordinate).coarse)
    (parentLineCover :
      ∀ source,
        WZ1PaperTubeCovers
          (fine.tube source)
          ((schedule.scaleData coordinate).coarse.tube
            ((schedule.scaleData coordinate).cover.parent source)))
    (scheduledParentSeparated :
      ∀ first second : Fin (schedule.scaleData coordinate).coarse.card,
        first ≠ second →
          wz2PaperLiteralSourceSeparationFactor *
                schedule.actualScale coordinate <
            wz1PaperLineDistance
              ((schedule.scaleData coordinate).coarse.tube first)
              ((schedule.scaleData coordinate).coarse.tube second))
    (actualLeRho : schedule.actualScale coordinate ≤ rho) :
    PureWZ2Prop62ProxyQuotientFiberRouteDescendantData
      metricCore sourceConstant 1 parent coordinate := by
  have localNonempty :
      (metricCore.restriction.metricFiberSource parent).family.Nonempty :=
    metricCore.metricFiberSource_nonempty parent
  have localParentCovers :
      ∀ source :
          Fin (metricCore.restriction.metricFiberSource parent).family.card,
        WZ1PaperTubeCovers
          ((metricCore.restriction.metricFiberSource parent).family.tube source)
          (data.scaleData.coarse.tube (data.scaleData.cover.parent source)) := by
    intro source
    rw [data.parent_tube_eq, data.parent_commutes]
    rw [← metricCore.metricFiberAmbientIndex_tube]
    exact parentLineCover (metricCore.metricFiberAmbientIndex parent source)
  let lineCover :
      WZ1PaperTubeCover
        (metricCore.restriction.metricFiberSource parent).family
        data.scaleData.coarse :=
    {
      parent := data.scaleData.cover.parent
      parent_surjective :=
        data.scaleData.cover.parent_surjective_of_uniform
          data.scaleData.rho_pos.le localNonempty
          data.scaleData.full_fiber_uniform
      parent_covers := localParentCovers
      parent_unique := by
        intro source candidate candidateCovers
        by_contra distinct
        have separated :=
          scheduledParentSeparated
            (data.parent_embedding candidate)
            (data.parent_embedding (data.scaleData.cover.parent source))
            (data.parent_embedding.injective.ne distinct)
        have triangle :=
          wz1PaperLineDistance_triangle
            (data.scaleData.coarse.tube candidate)
            ((metricCore.restriction.metricFiberSource parent).family.tube
              source)
            (data.scaleData.coarse.tube
              (data.scaleData.cover.parent source))
        have symmetry :
            wz1PaperLineDistance
                (data.scaleData.coarse.tube candidate)
                ((metricCore.restriction.metricFiberSource parent).family.tube
                  source) =
              wz1PaperLineDistance
                ((metricCore.restriction.metricFiberSource parent).family.tube
                  source)
                (data.scaleData.coarse.tube candidate) :=
          wz1PaperLineDistance_symm _ _
        rw [symmetry] at triangle
        rw [← data.parent_tube_eq candidate,
          ← data.parent_tube_eq (data.scaleData.cover.parent source)] at separated
        norm_num [wz2PaperLiteralSourceSeparationFactor] at separated
        unfold WZ1PaperTubeCovers at candidateCovers localParentCovers
        exact
          (not_le_of_gt separated)
            (triangle.trans <| by
              nlinarith [candidateCovers, localParentCovers source,
                data.scaleData.rho_pos])
    }
  have parentNearAnchor :
      ∀ middle,
        WZ2PaperDilatedTubeCovers 2
          (data.scaleData.coarse.tube middle)
          (metricCore.restriction.coarseSelected.family.tube parent) := by
    intro middle
    have middleFiberNonempty :=
      data.scaleData.cover.fullFiber_nonempty_of_uniform
        localNonempty data.scaleData.full_fiber_uniform middle
    rcases middleFiberNonempty with ⟨source, sourceMem⟩
    have sourceParent :
        data.scaleData.cover.parent source = middle :=
      (data.scaleData.cover.mem_fullFiber_iff_parent_eq
        data.scaleData.rho_pos.le middle source).mp sourceMem
    have fineToMiddle := localParentCovers source
    rw [sourceParent] at fineToMiddle
    have fineToAnchor :=
      metricCore.metricFiberSource_parent_covers parent source
    have triangle :=
      wz1PaperLineDistance_triangle
        (data.scaleData.coarse.tube middle)
        ((metricCore.restriction.metricFiberSource parent).family.tube source)
        (metricCore.restriction.coarseSelected.family.tube parent)
    have symmetry :
        wz1PaperLineDistance
            (data.scaleData.coarse.tube middle)
            ((metricCore.restriction.metricFiberSource parent).family.tube
              source) =
          wz1PaperLineDistance
            ((metricCore.restriction.metricFiberSource parent).family.tube
              source)
            (data.scaleData.coarse.tube middle) :=
      wz1PaperLineDistance_symm _ _
    rw [symmetry] at triangle
    unfold WZ1PaperTubeCovers at fineToMiddle fineToAnchor
    unfold WZ2PaperDilatedTubeCovers
    nlinarith
  have localLine :
      WZ1PaperIsLineClass
        (metricCore.restriction.metricFiberSource parent).family :=
    metricCore.restriction.section6Cover.fine_line_class.subfamily
      (metricCore.restriction.metricFiberSource parent).toTubeSubfamily
  have middleLine :
      WZ1PaperIsLineClass data.scaleData.coarse := by
    intro middle
    rw [data.parent_tube_eq]
    exact coarseLineClass (data.parent_embedding middle)
  have anchorLine :
      WZ1PaperTubeInLineClass
        (metricCore.restriction.coarseSelected.family.tube parent) :=
    metricCore.restriction.section6Cover.coarse_line_class parent
  have targetLocal :
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
        (localLine target)
        (by
          rw [← metricCore.metricFiberAmbientIndex_tube]
          exact fineBoundedBase (metricCore.metricFiberAmbientIndex parent target))
        (metricCore.metricFiberSource_parent_covers parent target)
  have localization :
      WZ2PaperOrdinaryNestedTargetLocalization
        (metricCore.restriction.metricFiberSource parent).family
        data.scaleData.coarse
        (metricCore.restriction.coarseSelected.family.tube parent)
        metricCore.metric.metricInput.rho_pos :=
    wz2PaperOrdinaryNestedTargetLocalization_of_sourceCovers
      (schedule.scaleData packetCoordinate).delta_pos
      data.scaleData.rho_pos metricCore.metric.metricInput.rho_pos rhoLeOne
      (metricCore.restriction.metricFiberSource parent).family
      data.scaleData.coarse
      (metricCore.restriction.coarseSelected.family.tube parent)
      localLine middleLine anchorLine
      (metricCore.metricFiberSource_parent_covers parent)
      parentNearAnchor targetLocal
  exact
    {
      actual := schedule.actualScale coordinate
      actual_eq_scaled := by simp
      scaleData := data.scaleData
      partitioningCover := data.scaleData.cover
      partitioningCover_eq := rfl
      coarse_line_class := middleLine
      lineCover := lineCover
      lineCover_parent_eq := rfl
      parent_near_anchor := parentNearAnchor
      separated := by
        intro first second distinct
        rw [data.parent_tube_eq, data.parent_tube_eq]
        exact
          scheduledParentSeparated
            (data.parent_embedding first) (data.parent_embedding second)
            (data.parent_embedding.injective.ne distinct)
      localization := localization
    }

/--
Scaled descendant-or-top dichotomy on the public laminar schedule.

The schedule is rounded at the original physical request
`max (100 * delta) (rho * requested)`.  In the descendant branch the public
route scale is `scaleFactor * r`, where `r` is the rounded schedule scale.
-/
theorem PureWZ2Prop62LaminarPureSchedule.requested_scaled_descendant_or_top
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (packetCoordinate : Fin schedule.levelCount)
    {rho scaleFactor K : ℝ}
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (scaleSeparation : 100 * delta ≤ rho)
    (scaleFactorOne : 1 ≤ scaleFactor)
    (scaleFactorLeK : scaleFactor ≤ K)
    (packetScaleLtRhoDivK :
      schedule.actualScale packetCoordinate < rho / K)
    (sourceConstant : ENNReal)
    (sourceConstantFinite :
      WZ2PaperFiniteErrorConstant sourceConstant)
    (floorGate :
      scaleWindow * ENNReal.ofReal delta <
        ENNReal.ofReal (schedule.actualScale packetCoordinate))
    (scaledWindowAbsorption :
      (100 : ENNReal) * ENNReal.ofReal scaleFactor * scaleWindow ≤
        (81000000 : ENNReal) * sourceConstant)
    (topGate :
      (4 : ENNReal) *
          ((100 : ENNReal) * scaleWindow * ENNReal.ofReal rho) ≤
        ((81000000 : ENNReal) * sourceConstant) *
          ENNReal.ofReal (schedule.actualScale packetCoordinate)) :
    ∀ requested : WZ2PaperRequestedScale (delta / rho),
      (∃ coordinate : Fin schedule.levelCount,
        packetCoordinate.val < coordinate.val ∧
          100 * delta ≤ scaleFactor * schedule.actualScale coordinate ∧
          scaleFactor * schedule.actualScale coordinate ≤ rho ∧
          requested.1 ≤
            (scaleFactor * schedule.actualScale coordinate) / rho ∧
          ENNReal.ofReal
              ((scaleFactor * schedule.actualScale coordinate) / rho) <
            ((81000000 : ENNReal) * sourceConstant) *
              ENNReal.ofReal requested.1) ∨
      (4 : ENNReal) <
        ((81000000 : ENNReal) * sourceConstant) *
          ENNReal.ofReal requested.1 := by
  intro requested
  have deltaPos : 0 < delta :=
    (schedule.scaleData packetCoordinate).delta_pos
  have requestedPos : 0 < requested.1 :=
    (div_pos deltaPos rhoPos).trans_le requested.2.1
  have _floorGate := floorGate
  have deltaLeRhoRequested :
      delta ≤ rho * requested.1 := by
    have raw := (div_le_iff₀ rhoPos).mp requested.2.1
    simpa only [mul_comm] using raw
  have factorPos : 0 < scaleFactor :=
    zero_lt_one.trans_le scaleFactorOne
  have factorNonneg : 0 ≤ scaleFactor := factorPos.le
  have KOne : 1 ≤ K :=
    scaleFactorOne.trans scaleFactorLeK
  have KPos : 0 < K :=
    zero_lt_one.trans_le KOne
  let physicalRequested : WZ2PaperRequestedScale delta :=
    ⟨max (100 * delta) (rho * requested.1),
      by
        constructor
        · exact
            (show delta ≤ 100 * delta by nlinarith).trans
              (le_max_left _ _)
        · apply max_le
          · exact scaleSeparation.trans rhoLeOne
          · nlinarith [requested.2.2]⟩
  have physicalLe :
      physicalRequested.1 ≤ 100 * rho * requested.1 := by
    dsimp only [physicalRequested]
    apply max_le
    · exact
        (mul_le_mul_of_nonneg_left deltaLeRhoRequested
          (by norm_num : (0 : ℝ) ≤ 100)).trans_eq (by ring)
    · have rhoRequestedPos : 0 < rho * requested.1 :=
        mul_pos rhoPos requestedPos
      calc
        rho * requested.1 = 1 * (rho * requested.1) := by ring
        _ ≤ 100 * (rho * requested.1) :=
          mul_le_mul_of_nonneg_right (by norm_num) rhoRequestedPos.le
        _ = 100 * rho * requested.1 := by ring
  rcases schedule.rounding physicalRequested with
    ⟨coordinate, physicalLeActual, actualWindow⟩
  let targetConstant : ENNReal :=
    (81000000 : ENNReal) * sourceConstant
  let windowDenominator : ENNReal :=
    (100 : ENNReal) * scaleWindow * ENNReal.ofReal rho
  have physicalWindow :
      ENNReal.ofReal physicalRequested.1 ≤
        (100 : ENNReal) * ENNReal.ofReal rho *
          ENNReal.ofReal requested.1 := by
    have rightNonnegative :
        0 ≤ 100 * rho * requested.1 := by positivity
    have raw :
        ENNReal.ofReal physicalRequested.1 ≤
          ENNReal.ofReal (100 * rho * requested.1) :=
      (ENNReal.ofReal_le_ofReal_iff rightNonnegative).mpr physicalLe
    calc
      ENNReal.ofReal physicalRequested.1 ≤
          ENNReal.ofReal (100 * rho * requested.1) := raw
      _ =
          (100 : ENNReal) * ENNReal.ofReal rho *
            ENNReal.ofReal requested.1 := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 100 * rho)]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 100)]
        norm_num
  have roundedWindow :
      ENNReal.ofReal (schedule.actualScale coordinate) <
        ((100 : ENNReal) * scaleWindow) *
          ENNReal.ofReal rho * ENNReal.ofReal requested.1 := by
    calc
      ENNReal.ofReal (schedule.actualScale coordinate) <
          scaleWindow * ENNReal.ofReal physicalRequested.1 :=
        actualWindow
      _ ≤
          scaleWindow *
            ((100 : ENNReal) * ENNReal.ofReal rho *
              ENNReal.ofReal requested.1) := by
        gcongr
      _ =
          ((100 : ENNReal) * scaleWindow) *
            ENNReal.ofReal rho * ENNReal.ofReal requested.1 := by
        ring
  by_cases descendant :
      packetCoordinate.val < coordinate.val
  · left
    have roundedLePacket :
        schedule.actualScale coordinate ≤
          schedule.actualScale packetCoordinate :=
      schedule.actualScale_antitone packetCoordinate coordinate descendant.le
    have treeSafe :
        100 * delta ≤ schedule.actualScale coordinate :=
      (le_max_left _ _).trans physicalLeActual
    have scaledTreeSafe :
        100 * delta ≤
          scaleFactor * schedule.actualScale coordinate := by
      have roundedNonneg :
          0 ≤ schedule.actualScale coordinate :=
        (schedule.scaleData coordinate).rho_pos.le
      exact treeSafe.trans <| by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right scaleFactorOne roundedNonneg
    have scaledActualLeRho :
        scaleFactor * schedule.actualScale coordinate ≤ rho := by
      have packetNonnegative :
          0 ≤ schedule.actualScale packetCoordinate :=
        (schedule.scaleData packetCoordinate).rho_pos.le
      have packetMulKLtRho :
          schedule.actualScale packetCoordinate * K < rho :=
        (lt_div_iff₀ KPos).mp packetScaleLtRhoDivK
      calc
        scaleFactor * schedule.actualScale coordinate ≤
            scaleFactor * schedule.actualScale packetCoordinate :=
          mul_le_mul_of_nonneg_left roundedLePacket factorNonneg
        _ ≤ K * schedule.actualScale packetCoordinate :=
          mul_le_mul_of_nonneg_right scaleFactorLeK packetNonnegative
        _ = schedule.actualScale packetCoordinate * K := by ring
        _ ≤ rho := packetMulKLtRho.le
    have requestedLe :
        requested.1 ≤
          (scaleFactor * schedule.actualScale coordinate) / rho := by
      apply (le_div_iff₀ rhoPos).mpr
      calc
        requested.1 * rho = rho * requested.1 := by ring
        _ ≤ physicalRequested.1 := by
          exact le_max_right _ _
        _ ≤ schedule.actualScale coordinate := physicalLeActual
        _ ≤ scaleFactor * schedule.actualScale coordinate := by
          have roundedNonneg :
              0 ≤ schedule.actualScale coordinate :=
            (schedule.scaleData coordinate).rho_pos.le
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right scaleFactorOne roundedNonneg
    have factorENNPos : 0 < ENNReal.ofReal scaleFactor :=
      ENNReal.ofReal_pos.mpr factorPos
    have scaledRoundedWindow :
        ENNReal.ofReal
            (scaleFactor * schedule.actualScale coordinate) <
          ((100 : ENNReal) * ENNReal.ofReal scaleFactor * scaleWindow) *
            ENNReal.ofReal rho * ENNReal.ofReal requested.1 := by
      rw [ENNReal.ofReal_mul factorNonneg]
      calc
        ENNReal.ofReal scaleFactor *
              ENNReal.ofReal (schedule.actualScale coordinate) <
            ENNReal.ofReal scaleFactor *
              (((100 : ENNReal) * scaleWindow) *
                ENNReal.ofReal rho * ENNReal.ofReal requested.1) :=
          ENNReal.mul_lt_mul_right factorENNPos.ne'
            ENNReal.ofReal_ne_top roundedWindow
        _ =
            ((100 : ENNReal) * ENNReal.ofReal scaleFactor * scaleWindow) *
              ENNReal.ofReal rho * ENNReal.ofReal requested.1 := by
          ring
    have rescaledWindow :
        ENNReal.ofReal
            ((scaleFactor * schedule.actualScale coordinate) / rho) <
          targetConstant * ENNReal.ofReal requested.1 := by
      rw [ENNReal.ofReal_div_of_pos rhoPos]
      apply ENNReal.div_lt_of_lt_mul
      calc
        ENNReal.ofReal
              (scaleFactor * schedule.actualScale coordinate) <
            ((100 : ENNReal) * ENNReal.ofReal scaleFactor * scaleWindow) *
              ENNReal.ofReal rho * ENNReal.ofReal requested.1 :=
          scaledRoundedWindow
        _ ≤
            targetConstant * ENNReal.ofReal requested.1 *
              ENNReal.ofReal rho := by
          dsimp only [targetConstant]
          calc
            ((100 : ENNReal) * ENNReal.ofReal scaleFactor * scaleWindow) *
                  ENNReal.ofReal rho * ENNReal.ofReal requested.1 =
                ((100 : ENNReal) * ENNReal.ofReal scaleFactor * scaleWindow) *
                  ENNReal.ofReal requested.1 * ENNReal.ofReal rho := by
              ring
            _ ≤
                ((81000000 : ENNReal) * sourceConstant) *
                  ENNReal.ofReal requested.1 * ENNReal.ofReal rho := by
              gcongr
    exact
      ⟨coordinate, descendant, scaledTreeSafe, scaledActualLeRho,
        requestedLe, by
          simpa only [targetConstant] using rescaledWindow⟩
  · right
    have coordinateLePacket :
        coordinate.val ≤ packetCoordinate.val := by
      omega
    have packetLeActual :
        schedule.actualScale packetCoordinate ≤
          schedule.actualScale coordinate :=
      schedule.actualScale_antitone coordinate packetCoordinate
        coordinateLePacket
    have packetWindow :
        ENNReal.ofReal (schedule.actualScale packetCoordinate) <
          windowDenominator * ENNReal.ofReal requested.1 := by
      calc
        ENNReal.ofReal (schedule.actualScale packetCoordinate) ≤
            ENNReal.ofReal (schedule.actualScale coordinate) :=
          ENNReal.ofReal_mono packetLeActual
        _ <
            ((100 : ENNReal) * scaleWindow) *
              ENNReal.ofReal rho * ENNReal.ofReal requested.1 :=
          roundedWindow
        _ =
            windowDenominator * ENNReal.ofReal requested.1 := by
          rfl
    have targetNeZero : targetConstant ≠ 0 := by
      dsimp only [targetConstant]
      exact mul_ne_zero (by norm_num)
        (ne_of_gt (zero_lt_one.trans_le sourceConstantFinite.1))
    have targetNeTop : targetConstant ≠ ⊤ := by
      dsimp only [targetConstant]
      exact ENNReal.mul_ne_top (by norm_num) sourceConstantFinite.2
    have denominatorNeZero : windowDenominator ≠ 0 := by
      dsimp only [windowDenominator]
      exact mul_ne_zero
        (mul_ne_zero (by norm_num)
          (ne_of_gt
            (zero_lt_one.trans_le schedule.scaleWindow_finite.1)))
        (ENNReal.ofReal_ne_zero_iff.mpr rhoPos)
    have denominatorNeTop : windowDenominator ≠ ⊤ := by
      dsimp only [windowDenominator]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num)
          schedule.scaleWindow_finite.2)
        ENNReal.ofReal_ne_top
    have multipliedWindow :
        targetConstant *
              ENNReal.ofReal (schedule.actualScale packetCoordinate) <
          targetConstant *
            (windowDenominator * ENNReal.ofReal requested.1) :=
      ENNReal.mul_lt_mul_right targetNeZero targetNeTop packetWindow
    have cancelled :
        (4 : ENNReal) * windowDenominator <
          (targetConstant * ENNReal.ofReal requested.1) *
            windowDenominator := by
      calc
        (4 : ENNReal) * windowDenominator ≤
            targetConstant *
              ENNReal.ofReal (schedule.actualScale packetCoordinate) := by
          simpa only [targetConstant, windowDenominator] using topGate
        _ <
            targetConstant *
              (windowDenominator * ENNReal.ofReal requested.1) :=
          multipliedWindow
        _ =
            (targetConstant * ENNReal.ofReal requested.1) *
              windowDenominator := by
          ring
    exact
      (ENNReal.mul_lt_mul_iff_left
        denominatorNeZero denominatorNeTop).mp cancelled

/--
Minimal closed input missing from the old ancestry-route theorem.

The old theorem is tied to a `PureWZ2Prop62MetricPacketOutput`, a
`PureWZ2Prop62PureSchedule` on its selected-fine family, and an internally
computed `coreOutput`.  Here the descendants are instead tied directly to the
same public laminar schedule and the externally supplied receipt already stored
in `metricCore`.
-/
structure PureWZ2Prop62ProxyQuotientFiberRouteInput
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (sourceConstant : ENNReal) where
  rho_le_one : rho ≤ 1
  scale_separation : 100 * delta ≤ rho
  source_constant_finite :
    WZ2PaperFiniteErrorConstant sourceConstant
  scaleFactor : ℝ
  scaleFactor_one : 1 ≤ scaleFactor
  K : ℝ
  scaleFactor_le_K : scaleFactor ≤ K
  packet_scale_lt_rho_div_K :
    schedule.actualScale packetCoordinate < rho / K
  fine_bounded_base : HasBoundedBase fine 4
  floor_gate :
    scaleWindow * ENNReal.ofReal delta <
      ENNReal.ofReal (schedule.actualScale packetCoordinate)
  scaled_window_absorption :
    (100 : ENNReal) * ENNReal.ofReal scaleFactor * scaleWindow ≤
      (81000000 : ENNReal) * sourceConstant
  inserted_singleton_top_gate :
    (4 : ENNReal) *
        ((100 : ENNReal) * scaleWindow * ENNReal.ofReal rho) ≤
      ((81000000 : ENNReal) * sourceConstant) *
        ENNReal.ofReal (schedule.actualScale packetCoordinate)
  descendant :
    ∀ (parent :
        Fin metricCore.restriction.coarseSelected.family.card)
      (coordinate : Fin schedule.levelCount),
      packetCoordinate.val < coordinate.val →
        PureWZ2Prop62ProxyQuotientFiberRouteDescendantData
          metricCore sourceConstant scaleFactor parent coordinate

/--
Compatibility input for callers that still possess line geometry for every
ambient schedule coordinate.  `toFiberRouteInput` packages those hypotheses
into factor-one local descendants.
-/
structure PureWZ2Prop62ProxyQuotientFiberRouteAmbientInput
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (sourceConstant : ENNReal) where
  rho_le_one : rho ≤ 1
  scale_separation : 100 * delta ≤ rho
  source_constant_finite :
    WZ2PaperFiniteErrorConstant sourceConstant
  packet_scale_le_rho :
    schedule.actualScale packetCoordinate ≤ rho
  coarse_line_class :
    ∀ coordinate,
      WZ1PaperIsLineClass (schedule.scaleData coordinate).coarse
  parent_line_cover :
    ∀ coordinate source,
      WZ1PaperTubeCovers
        (fine.tube source)
        ((schedule.scaleData coordinate).coarse.tube
          ((schedule.scaleData coordinate).cover.parent source))
  scheduled_parent_separated :
    ∀ (coordinate : Fin schedule.levelCount)
      (first second : Fin (schedule.scaleData coordinate).coarse.card),
      first ≠ second →
        wz2PaperLiteralSourceSeparationFactor *
              schedule.actualScale coordinate <
          wz1PaperLineDistance
            ((schedule.scaleData coordinate).coarse.tube first)
            ((schedule.scaleData coordinate).coarse.tube second)
  fine_bounded_base : HasBoundedBase fine 4
  window_absorption :
    (100 : ENNReal) * scaleWindow ≤
      (81000000 : ENNReal) * sourceConstant
  inserted_singleton_top_gate :
    (4 : ENNReal) *
        ((100 : ENNReal) * scaleWindow * ENNReal.ofReal rho) ≤
      ((81000000 : ENNReal) * sourceConstant) *
        ENNReal.ofReal (schedule.actualScale packetCoordinate)
  descendant :
    ∀ (parent :
        Fin metricCore.restriction.coarseSelected.family.card)
      (coordinate : Fin schedule.levelCount),
      packetCoordinate.val < coordinate.val →
        PureWZ2Prop62ProxyQuotientFiberDescendantData
          metricCore sourceConstant parent coordinate

namespace PureWZ2Prop62ProxyQuotientFiberRouteAmbientInput

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
    {metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {sourceConstant : ENNReal}
    (input :
      PureWZ2Prop62ProxyQuotientFiberRouteAmbientInput
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metricCore sourceConstant)

/-- Convert the ambient-wide legacy input into factor-one local descendants. -/
noncomputable def toFiberRouteInput
    (packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho)
    (floorGate :
      scaleWindow * ENNReal.ofReal delta <
        ENNReal.ofReal (schedule.actualScale packetCoordinate)) :
    PureWZ2Prop62ProxyQuotientFiberRouteInput
      schedule fineNonempty quotient width packetCoordinate
        strideBase weight metricCore sourceConstant where
  rho_le_one := input.rho_le_one
  scale_separation := input.scale_separation
  source_constant_finite := input.source_constant_finite
  scaleFactor := 1
  scaleFactor_one := le_rfl
  K := 1
  scaleFactor_le_K := le_rfl
  packet_scale_lt_rho_div_K := by
    simpa using packetScaleLtRho
  fine_bounded_base := input.fine_bounded_base
  floor_gate := floorGate
  scaled_window_absorption := by
    simpa using input.window_absorption
  inserted_singleton_top_gate := input.inserted_singleton_top_gate
  descendant := by
    intro parent coordinate coordinateAfter
    exact
      (input.descendant parent coordinate coordinateAfter).toRouteDescendantData
        input.rho_le_one input.fine_bounded_base
        (input.coarse_line_class coordinate)
        (input.parent_line_cover coordinate)
        (input.scheduled_parent_separated coordinate)
        ((schedule.actualScale_antitone
          packetCoordinate coordinate coordinateAfter.le).trans
            input.packet_scale_le_rho)

end PureWZ2Prop62ProxyQuotientFiberRouteAmbientInput

namespace PureWZ2Prop62ProxyQuotientFiberRouteInput

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
    {metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {sourceConstant : ENNReal}
    (input :
      PureWZ2Prop62ProxyQuotientFiberRouteInput
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metricCore sourceConstant)

include input

/-- Compatibility projection used by the existing fiber-CWA wrapper. -/
theorem packet_scale_le_rho :
    schedule.actualScale packetCoordinate ≤ rho := by
  have packetScaleNonnegative :
      0 ≤ schedule.actualScale packetCoordinate :=
    (schedule.scaleData packetCoordinate).rho_pos.le
  have KOne :
      1 ≤ PureWZ2Prop62ProxyQuotientFiberRouteInput.K input :=
    (PureWZ2Prop62ProxyQuotientFiberRouteInput.scaleFactor_one input).trans
      (PureWZ2Prop62ProxyQuotientFiberRouteInput.scaleFactor_le_K input)
  have KPos :
      0 < PureWZ2Prop62ProxyQuotientFiberRouteInput.K input :=
    zero_lt_one.trans_le KOne
  have packetMulKLtRho :
      schedule.actualScale packetCoordinate *
          PureWZ2Prop62ProxyQuotientFiberRouteInput.K input < rho :=
    (lt_div_iff₀ KPos).mp
      (PureWZ2Prop62ProxyQuotientFiberRouteInput.packet_scale_lt_rho_div_K input)
  have packetScaleLeScaled :
      schedule.actualScale packetCoordinate ≤
        PureWZ2Prop62ProxyQuotientFiberRouteInput.K input *
          schedule.actualScale packetCoordinate := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right
        KOne
        packetScaleNonnegative
  exact packetScaleLeScaled.trans <| by
    simpa only [mul_comm] using packetMulKLtRho.le

/-- The exact final metric fiber remains covered by its final metric parent. -/
theorem source_covered
    (parent :
      Fin metricCore.restriction.coarseSelected.family.card)
    (source :
      Fin
        (metricCore.restriction.metricFiberSource parent).family.card) :
    WZ1PaperTubeCovers
      ((metricCore.restriction.metricFiberSource parent).family.tube
        source)
      (metricCore.restriction.coarseSelected.family.tube parent) := by
  rw [(metricCore.restriction.metricFiberSource parent).tube_eq]
  exact
    (mem_wz2PaperFullFiberIndices_iff parent
      ((metricCore.restriction.metricFiberSource parent).embedding
        source)).mp
      (Finset.orderEmbOfFin_mem
        (wz2PaperFullFiberIndices
          metricCore.restriction.fineSelected.family
          metricCore.restriction.coarseSelected.family parent)
        rfl source)

/-- Every final metric fiber is nonempty, with no family replacement. -/
theorem source_nonempty
    (parent :
      Fin metricCore.restriction.coarseSelected.family.card) :
    (metricCore.restriction.metricFiberSource parent).family.Nonempty := by
  change
    0 <
      (wz2PaperFullFiberIndices
        metricCore.restriction.fineSelected.family
        metricCore.restriction.coarseSelected.family parent).card
  rcases metricCore.restriction.section6Cover.parent_hit parent with
    ⟨source, covered⟩
  exact
    Finset.card_pos.mpr
      ⟨source,
        (mem_wz2PaperFullFiberIndices_iff parent source).mpr
          covered⟩

/--
Construct the exact quotient fiber route from the public laminar schedule and
the minimal descendant-restriction bridge.
-/
noncomputable def toFiberRouteData :
    PureWZ2Prop62ProxyQuotientFiberRouteData
      metricCore sourceConstant := by
  refine
    {
      rho_le_one := input.rho_le_one
      delta_pos := (schedule.scaleData packetCoordinate).delta_pos
      scale_separation := input.scale_separation
      source_constant_finite := input.source_constant_finite
      requested_route := ?_
    }
  intro parent requested
  rcases
      schedule.requested_scaled_descendant_or_top
        packetCoordinate metricCore.metric.metricInput.rho_pos
        input.rho_le_one input.scale_separation
        input.scaleFactor_one input.scaleFactor_le_K
        input.packet_scale_lt_rho_div_K
        sourceConstant input.source_constant_finite
        input.floor_gate
        input.scaled_window_absorption
        input.inserted_singleton_top_gate requested
    with descendant | top
  · rcases descendant with
      ⟨coordinate, coordinateAfter, treeSafe, actualLeRho,
        requestedLe, within⟩
    let data := input.descendant parent coordinate coordinateAfter
    exact
      Or.inl
        ⟨data.actual, data.scaleData,
          by simpa only [data.actual_eq_scaled] using treeSafe,
          by simpa only [data.actual_eq_scaled] using actualLeRho,
          by simpa only [data.actual_eq_scaled] using requestedLe,
          by simpa only [data.actual_eq_scaled] using within,
          data.coarse_line_class,
          data.parent_covers,
          data.parent_near_anchor,
          data.separated,
          data.localization⟩
  · exact Or.inr top

end PureWZ2Prop62ProxyQuotientFiberRouteInput

theorem pureWZ2_prop62_proxy_quotient_fiber_route
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (sourceConstant : ENNReal)
    (input :
      PureWZ2Prop62ProxyQuotientFiberRouteInput
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metricCore sourceConstant) :
    Nonempty
      (PureWZ2Prop62ProxyQuotientFiberRouteData
        metricCore sourceConstant) :=
  ⟨input.toFiberRouteData⟩

/-- Compatibility entry point for the former ambient-wide route hypotheses. -/
theorem pureWZ2_prop62_proxy_quotient_fiber_route_of_ambient
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (sourceConstant : ENNReal)
    (input :
      PureWZ2Prop62ProxyQuotientFiberRouteAmbientInput
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metricCore sourceConstant)
    (packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho)
    (floorGate :
      scaleWindow * ENNReal.ofReal delta <
        ENNReal.ofReal (schedule.actualScale packetCoordinate)) :
    Nonempty
      (PureWZ2Prop62ProxyQuotientFiberRouteData
        metricCore sourceConstant) :=
  pureWZ2_prop62_proxy_quotient_fiber_route
    schedule fineNonempty quotient width packetCoordinate strideBase weight
      metricCore sourceConstant
      (input.toFiberRouteInput packetScaleLtRho floorGate)

end Kakeya.Assouad

end
