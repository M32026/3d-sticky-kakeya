import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryUpperSchedule

/-!
# Proposition 6.2: nested schedule on the metric-parent family

The metric-parent construction retains the complete old ancestry above the
inserted `rho` level.  At every such coordinate, the factor-nineteen upper
construction gives a pure scale witness on the final metric-parent family.
Keeping the original coordinate order preserves the parent-map nesting used
by the second one-pass tree cleanup.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

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

def finalMetricParentCoordinate
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (coordinate : Fin packetCoordinate.1) :
    schedule.UpperCoordinate rho packetCoordinate :=
  ⟨schedule.ancestryAmbientCoordinate packetCoordinate coordinate,
    allAncestryCoordinatesUpper coordinate,
    coordinate.2⟩

@[simp] theorem finalMetricParentCoordinate_val
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (coordinate : Fin packetCoordinate.1) :
    (finalMetricParentCoordinate
      allAncestryCoordinatesUpper coordinate).1.1 = coordinate.1 := by
  rfl

noncomputable def finalMetricParentScaleWitness
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
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.finalMetricRestriction.fineSelected.family.tube
          source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (coordinate : Fin packetCoordinate.1) :
    PureWZ2Prop62UpperScaleWitness
      (upper :=
        19 * schedule.actualScale
          (schedule.ancestryAmbientCoordinate
            packetCoordinate coordinate))
      output.finalMetricRestriction.coarseSelected.family
      output.finalUpperScheduleConstant :=
  output.finalUpperScaleWitness
    coordinates rhoPos widthPos packetScaleLeRho sixWidthLe
    allAncestryCoordinatesUpper scaleGap fineAxisBox
    (finalMetricParentCoordinate
      allAncestryCoordinatesUpper coordinate)

theorem finalMetricParentScale_parent_ancestor
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
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.finalMetricRestriction.fineSelected.family.tube
          source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (coordinate : Fin packetCoordinate.1)
    (child :
      Fin output.finalMetricRestriction.coarseSelected.family.card) :
    let witness :=
      output.finalMetricParentScaleWitness
        coordinates rhoPos widthPos packetScaleLeRho sixWidthLe
        allAncestryCoordinatesUpper scaleGap fineAxisBox coordinate
    witness.coverData.selectedParents.embedding
        (witness.scaleData.cover.parent child) =
      finalUpperAncestor (output := output)
        (finalMetricParentCoordinate
          allAncestryCoordinatesUpper coordinate) child := by
  dsimp only [finalMetricParentScaleWitness]
  exact
    (output.finalUpperMonochromaticCover
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper
      (finalMetricParentCoordinate
        allAncestryCoordinatesUpper coordinate)
      ).parent_owner_eq child

theorem finalMetricParentScale_parent_eq_iff
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
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.finalMetricRestriction.fineSelected.family.tube
          source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (coordinate : Fin packetCoordinate.1)
    (first second :
      Fin output.finalMetricRestriction.coarseSelected.family.card) :
    let witness :=
      output.finalMetricParentScaleWitness
        coordinates rhoPos widthPos packetScaleLeRho sixWidthLe
        allAncestryCoordinatesUpper scaleGap fineAxisBox coordinate
    witness.scaleData.cover.parent first =
        witness.scaleData.cover.parent second ↔
      finalUpperAncestor (output := output)
          (finalMetricParentCoordinate
            allAncestryCoordinatesUpper coordinate) first =
        finalUpperAncestor (output := output)
          (finalMetricParentCoordinate
            allAncestryCoordinatesUpper coordinate) second := by
  dsimp only
  constructor
  · intro parentEq
    have embedded :=
      congrArg
        (output.finalMetricParentScaleWitness
          coordinates rhoPos widthPos packetScaleLeRho sixWidthLe
          allAncestryCoordinatesUpper scaleGap fineAxisBox coordinate
          ).coverData.selectedParents.embedding
        parentEq
    exact
      (output.finalMetricParentScale_parent_ancestor
        coordinates rhoPos widthPos packetScaleLeRho sixWidthLe
        allAncestryCoordinatesUpper scaleGap fineAxisBox
        coordinate first).symm.trans <|
          embedded.trans <|
            output.finalMetricParentScale_parent_ancestor
              coordinates rhoPos widthPos packetScaleLeRho sixWidthLe
              allAncestryCoordinatesUpper scaleGap fineAxisBox
              coordinate second
  · intro ancestorEq
    apply
      (output.finalMetricParentScaleWitness
        coordinates rhoPos widthPos packetScaleLeRho sixWidthLe
        allAncestryCoordinatesUpper scaleGap fineAxisBox coordinate
        ).coverData.selectedParents.embedding.injective
    exact
      (output.finalMetricParentScale_parent_ancestor
        coordinates rhoPos widthPos packetScaleLeRho sixWidthLe
        allAncestryCoordinatesUpper scaleGap fineAxisBox
        coordinate first).trans <|
          ancestorEq.trans <|
            (output.finalMetricParentScale_parent_ancestor
              coordinates rhoPos widthPos packetScaleLeRho sixWidthLe
              allAncestryCoordinatesUpper scaleGap fineAxisBox
              coordinate second).symm

/--
The ordered upper ancestry, with the paper's factor-nineteen parent tubes,
is a literal nested pure schedule on the final metric-parent family.
-/
noncomputable def finalMetricParentSchedule
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (widthPos : 0 < width)
    (packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (scaleGap : 4 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.finalMetricRestriction.fineSelected.family.tube
          source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2) :
    PureWZ2Prop62PureSchedule
      output.finalMetricRestriction.coarseSelected.family
      output.finalUpperScheduleConstant
      output.finalUpperScheduleConstant := by
  have deltaLeRho : delta ≤ rho := by
    have deltaPos := (schedule.scaleData packetCoordinate).delta_pos
    nlinarith
  have packetCoordinatePos : 0 < packetCoordinate.1 := by
    let requested : WZ2PaperRequestedScale delta :=
      ⟨rho, deltaLeRho, rhoLeOne⟩
    rcases schedule.rounding requested with
      ⟨coordinate, rhoLeActual, _actualWindow⟩
    have coordinateLtPacket : coordinate.1 < packetCoordinate.1 := by
      by_contra notLt
      have packetLeCoordinate :
          packetCoordinate.1 ≤ coordinate.1 := by omega
      have actualLePacket :=
        schedule.actualScale_antitone
          packetCoordinate coordinate packetLeCoordinate
      linarith
    omega
  let upperCoordinate :
      Fin packetCoordinate.1 →
        schedule.UpperCoordinate rho packetCoordinate :=
    fun coordinate =>
      finalMetricParentCoordinate
        allAncestryCoordinatesUpper coordinate
  let witness :
      ∀ coordinate : Fin packetCoordinate.1,
        PureWZ2Prop62UpperScaleWitness
          (upper := 19 * schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
          output.finalMetricRestriction.coarseSelected.family
          output.finalUpperScheduleConstant :=
    fun coordinate =>
      output.finalMetricParentScaleWitness
        coordinates rhoPos widthPos packetScaleLtRho.le sixWidthLe
        allAncestryCoordinatesUpper scaleGap fineAxisBox coordinate
  refine
    {
      ambient_finite := output.finalUpperScheduleConstant_finite
      scaleWindow_finite := output.finalUpperScheduleConstant_finite
      fine_distinct := output.finalMetricParents_ordinary_distinct
      levelCount := packetCoordinate.1
      levelCount_pos := packetCoordinatePos
      actualScale := fun coordinate =>
        19 * schedule.actualScale
          (schedule.ancestryAmbientCoordinate
            packetCoordinate coordinate)
      delta_le_actualScale := ?_
      actualScale_antitone := ?_
      scaleData := fun coordinate => (witness coordinate).scaleData
      coarse_line_class := ?_
      parent_covers := ?_
      parent_nested := ?_
      rounding := ?_
    }
  · intro coordinate
    have lower := allAncestryCoordinatesUpper coordinate
    have scalePos :=
      (schedule.scaleData
        (schedule.ancestryAmbientCoordinate
          packetCoordinate coordinate)).rho_pos
    nlinarith
  · intro first second firstLeSecond
    have oldScaleLe :=
      schedule.actualScale_antitone
        (schedule.ancestryAmbientCoordinate packetCoordinate first)
        (schedule.ancestryAmbientCoordinate packetCoordinate second)
        firstLeSecond
    nlinarith
  · intro coordinate
    let upper := upperCoordinate coordinate
    intro parent
    change
      WZ1PaperTubeInLineClass
        ((witness coordinate).coverData.selectedParents.family.tube parent)
    rw [(witness coordinate).coverData.selectedParents.tube_eq]
    change
      WZ1PaperTubeInLineClass
        ((output.finalUpperScaleGeometryInput
          coordinates rhoPos widthPos packetScaleLtRho.le
          sixWidthLe allAncestryCoordinatesUpper upper
          ).modifiedParents.tube _)
    exact
      (output.finalUpperScaleGeometryInput
        coordinates rhoPos widthPos packetScaleLtRho.le
        sixWidthLe allAncestryCoordinatesUpper upper
        ).modifiedParents_line_class _
  · intro coordinate child
    let upper := upperCoordinate coordinate
    let currentWitness := witness coordinate
    unfold WZ1PaperTubeCovers
    have parentAmbient :=
      output.finalMetricParentScale_parent_ancestor
        coordinates rhoPos widthPos packetScaleLtRho.le sixWidthLe
        allAncestryCoordinatesUpper scaleGap fineAxisBox coordinate child
    have close :=
      output.finalUpperAncestor_close
        rhoPos widthPos packetScaleLtRho.le sixWidthLe
        allAncestryCoordinatesUpper upper child
    have parentTubeEq :
        (currentWitness.scaleData).coarse.tube
            ((currentWitness.scaleData).cover.parent child) =
          wz2PaperCenteredLineTube
            (targetScale :=
              19 * schedule.actualScale
                (schedule.ancestryAmbientCoordinate
                  packetCoordinate coordinate))
            ((output.finalOldScaleData upper.1).coarse.tube
              (finalUpperAncestor (output := output) upper child)) := by
      calc
        (currentWitness.scaleData).coarse.tube
            ((currentWitness.scaleData).cover.parent child) =
            currentWitness.coverData.selectedParents.family.tube
              ((currentWitness.scaleData).cover.parent child) := by
          rfl
        _ =
            currentWitness.parents.tube
              (currentWitness.coverData.selectedParents.embedding
                ((currentWitness.scaleData).cover.parent child)) :=
          currentWitness.coverData.selectedParents.tube_eq _
        _ =
            currentWitness.parents.tube
              (finalUpperAncestor (output := output) upper child) := by
          rw [parentAmbient]
        _ =
            wz2PaperCenteredLineTube
              (targetScale :=
                19 * schedule.actualScale
                  (schedule.ancestryAmbientCoordinate
                    packetCoordinate coordinate))
              ((output.finalOldScaleData upper.1).coarse.tube
                (finalUpperAncestor (output := output) upper child)) := by
          rfl
    change
      wz1PaperLineDistance
          (output.finalMetricRestriction.coarseSelected.family.tube child)
          ((currentWitness.scaleData).coarse.tube
            ((currentWitness.scaleData).cover.parent child)) ≤
        (19 * schedule.actualScale
          (schedule.ancestryAmbientCoordinate
            packetCoordinate coordinate)) / 2
    rw [parentTubeEq]
    rw [wz1PaperLineDistance_centeredLineTube_right
      (output.finalMetricRestriction.section6Cover.coarse_line_class child)
      (output.finalOldScaleData_coarse_line_class upper.1
        (finalUpperAncestor (output := output) upper child))]
    change
      wz1PaperLineDistance
          (output.finalMetricRestriction.coarseSelected.family.tube child)
          ((output.finalOldScaleData upper.1).coarse.tube
            (finalUpperAncestor (output := output) upper child)) ≤
        19 * schedule.actualScale upper.1 / 2
    exact close.trans <| by
      have scalePos := (output.finalOldScaleData upper.1).rho_pos
      nlinarith
  · intro level hnext first second nextParentEq
    let current : Fin packetCoordinate.1 :=
      ⟨level, Nat.lt_of_succ_lt hnext⟩
    let next : Fin packetCoordinate.1 :=
      ⟨level + 1, hnext⟩
    have nextAncestorEq :
        finalUpperAncestor (output := output)
            (upperCoordinate next) first =
          finalUpperAncestor (output := output)
            (upperCoordinate next) second := by
      exact
        (output.finalMetricParentScale_parent_eq_iff
          coordinates rhoPos widthPos packetScaleLtRho.le sixWidthLe
          allAncestryCoordinatesUpper scaleGap fineAxisBox
          next first second).mp nextParentEq
    have currentAncestorEq :
        finalUpperAncestor (output := output)
            (upperCoordinate current) first =
          finalUpperAncestor (output := output)
            (upperCoordinate current) second := by
      unfold finalUpperAncestor at nextAncestorEq ⊢
      exact
        output.finalOldScaleData_parent_eq_of_coordinate_le
          (upperCoordinate current).1 (upperCoordinate next).1
          (Nat.le_succ level)
          (finalMetricFiberRepresentative (output := output) first)
          (finalMetricFiberRepresentative (output := output) second)
          nextAncestorEq
    exact
      (output.finalMetricParentScale_parent_eq_iff
        coordinates rhoPos widthPos packetScaleLtRho.le sixWidthLe
        allAncestryCoordinatesUpper scaleGap fineAxisBox
        current first second).mpr currentAncestorEq
  · intro requested
    have deltaLeRequested : delta ≤ requested.1 :=
      deltaLeRho.trans requested.2.1
    let physicalRequested : WZ2PaperRequestedScale delta :=
      ⟨requested.1, deltaLeRequested, requested.2.2⟩
    rcases schedule.rounding physicalRequested with
      ⟨coordinate, requestedLeActual, actualWindow⟩
    have rhoLeActual :
        rho ≤ schedule.actualScale coordinate :=
      requested.2.1.trans requestedLeActual
    have coordinateLtPacket :
        coordinate.1 < packetCoordinate.1 := by
      by_contra notLt
      have packetLeCoordinate :
          packetCoordinate.1 ≤ coordinate.1 := by omega
      have actualLePacket :=
        schedule.actualScale_antitone
          packetCoordinate coordinate packetLeCoordinate
      linarith
    let selected : Fin packetCoordinate.1 :=
      ⟨coordinate.1, coordinateLtPacket⟩
    refine ⟨selected, ?_, ?_⟩
    · change requested.1 ≤
        19 * schedule.actualScale
          (schedule.ancestryAmbientCoordinate
            packetCoordinate selected)
      change requested.1 ≤ 19 * schedule.actualScale coordinate
      nlinarith
    · change
        ENNReal.ofReal
            (19 * schedule.actualScale
              (schedule.ancestryAmbientCoordinate
                packetCoordinate selected)) <
          output.finalUpperScheduleConstant *
            ENNReal.ofReal requested.1
      change
        ENNReal.ofReal (19 * schedule.actualScale coordinate) <
          output.finalUpperScheduleConstant *
            ENNReal.ofReal requested.1
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 19)]
      have scaledWindow :
          (19 : ENNReal) *
              ENNReal.ofReal (schedule.actualScale coordinate) <
            (19 : ENNReal) *
              (scaleWindow * ENNReal.ofReal requested.1) := by
        have raw :=
          ENNReal.mul_lt_mul_left
            (by norm_num : (19 : ENNReal) ≠ 0)
            (by norm_num : (19 : ENNReal) ≠ ⊤)
            actualWindow
        simpa only [physicalRequested, mul_comm] using raw
      norm_num
      calc
        (19 : ENNReal) *
            ENNReal.ofReal (schedule.actualScale coordinate) <
          (19 : ENNReal) *
            (scaleWindow * ENNReal.ofReal requested.1) :=
          scaledWindow
        _ =
          ((19 : ENNReal) * scaleWindow) *
            ENNReal.ofReal requested.1 := by ring
        _ ≤
          output.finalUpperScheduleConstant *
            ENNReal.ofReal requested.1 := by
          gcongr
          exact
            (le_max_right
              (max output.finalUpperFiberUniformConstant
                output.finalUpperParentBodyConstant)
              ((19 : ENNReal) * scaleWindow)).trans
              (le_max_right _ _)

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
