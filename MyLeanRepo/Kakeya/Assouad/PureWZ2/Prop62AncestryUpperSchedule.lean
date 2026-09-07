import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryUpperParentCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62UpperSchedule
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureHitParentRestriction

/-!
# Proposition 6.2: finite upper schedule on the final metric-parent family

The old schedule is rounded at each requested parent scale.  The strict
inequality `s < rho` ensures that every rounded coordinate lies strictly
above the packet coordinate and is therefore one of the frozen upper
ancestry coordinates.  Each old radius `r` produces a factor-`19` witness.
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

def finalUpperScheduleConstant : ENNReal :=
  max 1 <|
    max
      (max output.finalUpperFiberUniformConstant
        output.finalUpperParentBodyConstant)
      ((19 : ENNReal) * scaleWindow)

theorem finalUpperScheduleConstant_finite :
    WZ2PaperFiniteErrorConstant
      output.finalUpperScheduleConstant := by
  have densityFinite :
      output.ancestryDensityLoss ≠ ⊤ := by
    exact
      output.ancestryAuxiliary.densityLoss_ne_top
        output.binnedAmbientPreliminary_nonempty
  have coreFinite :
      output.finalCoreConstant ≠ ⊤ :=
    (output.ancestryAuxiliary.outputConstant_finite
      output.binnedAmbientPreliminary_nonempty).2
  have uniformFinite :
      output.finalUpperFiberUniformConstant ≠ ⊤ := by
    unfold finalUpperFiberUniformConstant
    exact
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top densityFinite coreFinite)
        (by norm_num)
  have bodyFinite :
      output.finalUpperParentBodyConstant ≠ ⊤ := by
    unfold finalUpperParentBodyConstant
    exact
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top (by norm_num) (by norm_num))
            densityFinite)
          coreFinite)
        (by norm_num)
  have windowFinite :
      (19 : ENNReal) * scaleWindow ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      schedule.scaleWindow_finite.2
  refine
    ⟨le_max_left _ _,
      max_ne_top (by simp) <|
        max_ne_top
          (max_ne_top uniformFinite bodyFinite)
          windowFinite⟩

noncomputable def finalUpperScaleWitness
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
    (coordinate : schedule.UpperCoordinate rho packetCoordinate) :
    PureWZ2Prop62UpperScaleWitness
      (upper := 19 * schedule.actualScale coordinate.1)
      output.finalMetricRestriction.coarseSelected.family
      output.finalUpperScheduleConstant where
  degree := 0
  parents :=
    (output.finalUpperScaleGeometryInput
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate
      ).modifiedParents
  input :=
    output.finalUpperScaleInput
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate
  coloring :=
    output.finalUpperScaleColoring
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate
  selectedColor := 0
  monochromatic := fun child => Fin.eq_zero _
  coverData :=
    output.finalUpperMonochromaticCover
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate
  coverConstant := output.finalUpperFiberUniformConstant
  bodyConstant := output.finalUpperParentBodyConstant
  fullFiberUniform :=
    output.finalUpperFullFiber_uniform
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate
  normalization :=
    output.finalUpperNormalization
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate
  fiberCWA :=
    output.finalUpperParentFiberCWA
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper scaleGap
      fineAxisBox coordinate
  constant_le :=
    calc
      max output.finalUpperFiberUniformConstant
          output.finalUpperParentBodyConstant ≤
        max
          (max output.finalUpperFiberUniformConstant
            output.finalUpperParentBodyConstant)
          ((19 : ENNReal) * scaleWindow) :=
        le_max_left _ _
      _ ≤
        max 1
          (max
            (max output.finalUpperFiberUniformConstant
              output.finalUpperParentBodyConstant)
            ((19 : ENNReal) * scaleWindow)) :=
        le_max_right _ _

theorem finalMetricParents_ordinary_distinct :
    WZ2PaperOrdinaryIsEssentiallyDistinct
      output.finalMetricRestriction.coarseSelected.family := by
  let selected :
      WZ2PaperPureTubeSubfamily output.metric.metricParents :=
    {
      family :=
        output.finalMetricRestriction.coarseSelected.family
      embedding :=
        output.finalMetricRestriction.coarseSelected.embedding
      tube_eq :=
        output.finalMetricRestriction.coarseSelected.tube_eq
    }
  exact
    output.metric.metricParents_ordinary_distinct.subfamily selected

noncomputable def finalUpperSchedule
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (actualScaleLeOne :
      ∀ coordinate, schedule.actualScale coordinate ≤ 1)
    (widthPos : 0 < width)
    (packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho)
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
          Kakeya.Streamlined.axisBox 2 2 2) :
    PureWZ2Prop62UpperSchedule
      output.finalMetricRestriction.coarseSelected.family
      output.finalUpperScheduleConstant := by
  let Upper :=
    schedule.UpperCoordinate rho packetCoordinate
  have upperNonempty : Nonempty Upper := by
    let requested : WZ2PaperRequestedScale delta :=
      ⟨rho,
        ⟨(show delta ≤ rho by
            have deltaPos :=
              (schedule.scaleData packetCoordinate).delta_pos
            nlinarith [scaleGap]),
          rhoLeOne⟩⟩
    rcases schedule.rounding requested with
      ⟨coordinate, rhoLeActual, _window⟩
    have coordinateLtPacket :
        coordinate.1 < packetCoordinate.1 := by
      by_contra notLt
      have packetLeCoordinate :
          packetCoordinate.1 ≤ coordinate.1 := by omega
      have actualLePacket :=
        schedule.actualScale_antitone
          packetCoordinate coordinate packetLeCoordinate
      linarith
    exact
      ⟨⟨coordinate, rhoLeActual, coordinateLtPacket⟩⟩
  let upperEquiv : Fin (Fintype.card Upper) ≃ Upper :=
    (Fintype.equivFin Upper).symm
  have upperCountPos : 0 < Fintype.card Upper :=
    Fintype.card_pos_iff.mpr upperNonempty
  refine
    {
      output_finite := output.finalUpperScheduleConstant_finite
      parent_distinct := output.finalMetricParents_ordinary_distinct
      coordinateCount := Fintype.card Upper
      coordinateCount_pos := upperCountPos
      baseScale := fun coordinate =>
        schedule.actualScale (upperEquiv coordinate).1
      baseScale_mem := fun coordinate =>
        ⟨(upperEquiv coordinate).2.1,
          actualScaleLeOne (upperEquiv coordinate).1⟩
      witness := fun coordinate =>
        output.finalUpperScaleWitness
          coordinates rhoPos widthPos packetScaleLtRho.le
          sixWidthLe allAncestryCoordinatesUpper
          scaleGap fineAxisBox (upperEquiv coordinate)
      rounding := ?_
    }
  intro requested
  have deltaLeRequested :
      delta ≤ requested.1 :=
    (show delta ≤ rho by
      have deltaPos :=
        (schedule.scaleData packetCoordinate).delta_pos
      nlinarith [scaleGap]).trans requested.2.1
  let physicalRequested : WZ2PaperRequestedScale delta :=
    ⟨requested.1,
      ⟨deltaLeRequested, requested.2.2⟩⟩
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
  let upper : Upper :=
    ⟨coordinate, rhoLeActual, coordinateLtPacket⟩
  let selectedCoordinate :=
    upperEquiv.symm upper
  have selectedCoordinateEq :
      upperEquiv selectedCoordinate = upper :=
    upperEquiv.apply_symm_apply upper
  have selectedCoordinateValEq :
      (upperEquiv selectedCoordinate).1 = coordinate := by
    exact congrArg Subtype.val selectedCoordinateEq
  refine
    ⟨selectedCoordinate, ?_, ?_⟩
  · change requested.1 ≤
      19 * schedule.actualScale
        (upperEquiv selectedCoordinate).1
    rw [selectedCoordinateValEq]
    nlinarith
  · change
      ENNReal.ofReal
          (19 * schedule.actualScale
            (upperEquiv selectedCoordinate).1) <
        output.finalUpperScheduleConstant *
          ENNReal.ofReal requested.1
    rw [selectedCoordinateValEq]
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

theorem finalMetricParents_publicPureCWA
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (actualScaleLeOne :
      ∀ coordinate, schedule.actualScale coordinate ≤ 1)
    (widthPos : 0 < width)
    (packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho)
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
          Kakeya.Streamlined.axisBox 2 2 2) :
    WZ2PaperPureCWAAtNearbyScales
      output.finalMetricRestriction.coarseSelected.family
      output.finalUpperScheduleConstant :=
  pureWZ2_prop62_upperSchedule_nearbyCWA <|
    output.finalUpperSchedule
      coordinates rhoPos rhoLeOne actualScaleLeOne
      widthPos packetScaleLtRho
      sixWidthLe allAncestryCoordinatesUpper scaleGap fineAxisBox

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
