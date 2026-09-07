import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientUpperEnvelope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientAuxiliaryTree

/-!
# Proposition 6.2 quotient-center prefix bridge

The upper-envelope conflict coloring is pulled back both to metric parents
and to ambient fine leaves.  On any leaf set monochromatic at every upper
coordinate, equality of one upper quotient center is equivalent to equality
of the entire preceding quotient-center prefix.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

def pureWZ2Prop62UpperEnvelopeCenterConflict
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
    {packetCoordinate : Fin schedule.levelCount}
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (first second :
      Fin (quotient.level coordinate.1).centerFamily.card) : Prop :=
  second ≠ first ∧
    wz1PaperLineDistance
        ((quotient.level coordinate.1).centerFamily.tube second)
        ((quotient.level coordinate.1).centerFamily.tube first) ≤
      pureWZ2Prop62UpperEnvelopeConflictRadius *
        schedule.actualScale coordinate.1

structure PureWZ2Prop62UpperEnvelopeCenterColoringData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    (rho : ℝ)
    (packetCoordinate : Fin schedule.levelCount) where
  color :
    ∀ coordinate :
        schedule.ProxyUpperCoordinate rho packetCoordinate,
      Fin (quotient.level coordinate.1).centerFamily.card →
        Fin (pureWZ2Prop62UpperEnvelopeConflictDegree + 1)
  proper :
    ∀ coordinate first second,
      first ≠ second →
      wz1PaperLineDistance
          ((quotient.level coordinate.1).centerFamily.tube first)
          ((quotient.level coordinate.1).centerFamily.tube second) ≤
        pureWZ2Prop62UpperEnvelopeConflictRadius *
          schedule.actualScale coordinate.1 →
      color coordinate first ≠ color coordinate second

theorem pureWZ2_prop62_upperEnvelope_center_conflict_degree
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (fineLine : WZ1PaperIsLineClass fine)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (packetCoordinate : Fin schedule.levelCount)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (fixed :
      Fin (quotient.level coordinate.1).centerFamily.card) :
    (Finset.univ.filter
      (pureWZ2Prop62UpperEnvelopeCenterConflict
        (quotient := quotient) coordinate fixed)).card ≤
      pureWZ2Prop62UpperEnvelopeConflictDegree := by
  let conflicts :
      Finset (Fin (quotient.level coordinate.1).centerFamily.card) :=
    Finset.univ.filter
      (pureWZ2Prop62UpperEnvelopeCenterConflict
        (quotient := quotient) coordinate fixed)
  let neighborhood :
      Finset (Fin (quotient.level coordinate.1).centerFamily.card) :=
    Finset.univ.filter fun other =>
      wz1PaperLineDistance
          ((quotient.level coordinate.1).centerFamily.tube other)
          ((quotient.level coordinate.1).centerFamily.tube fixed) ≤
        pureWZ2Prop62UpperEnvelopeConflictRadius *
          schedule.actualScale coordinate.1
  change conflicts.card ≤ pureWZ2Prop62UpperEnvelopeConflictDegree
  have subset : conflicts ⊆ neighborhood := by
    intro other otherMem
    exact
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,
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
        ((quotient.level coordinate.1).centerFamily_distinct fineLine)
        ((quotient.level coordinate.1).centerFamily_lineClass fineLine)
        (by
          have scalePos :=
            (schedule.scaleData coordinate.1).rho_pos
          positivity :
          0 < schedule.actualScale coordinate.1 / 4)
        (pureWZ2Prop62UpperEnvelopeConflictRadius *
          schedule.actualScale coordinate.1)
        (mul_pos
          (by
            norm_num [pureWZ2Prop62UpperEnvelopeConflictRadius])
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

structure PureWZ2Prop62UpperEnvelopeLevelColoringData
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
    {packetCoordinate : Fin schedule.levelCount}
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate) where
  color :
    Fin (quotient.level coordinate.1).centerFamily.card →
      Fin (pureWZ2Prop62UpperEnvelopeConflictDegree + 1)
  proper :
    ∀ first second, first ≠ second →
      wz1PaperLineDistance
          ((quotient.level coordinate.1).centerFamily.tube first)
          ((quotient.level coordinate.1).centerFamily.tube second) ≤
        pureWZ2Prop62UpperEnvelopeConflictRadius *
          schedule.actualScale coordinate.1 →
      color first ≠ color second

theorem pureWZ2_prop62_upperEnvelope_level_coloring
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (fineLine : WZ1PaperIsLineClass fine)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (packetCoordinate : Fin schedule.levelCount)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate) :
    Nonempty
      (PureWZ2Prop62UpperEnvelopeLevelColoringData
        (quotient := quotient) coordinate) := by
  let conflict :=
    pureWZ2Prop62UpperEnvelopeCenterConflict
      (quotient := quotient) coordinate
  have symmetric :
      ∀ first second,
        conflict first second → conflict second first := by
    intro first second conflictData
    change
      first ≠ second ∧
        wz1PaperLineDistance
            ((quotient.level coordinate.1).centerFamily.tube first)
            ((quotient.level coordinate.1).centerFamily.tube second) ≤
          pureWZ2Prop62UpperEnvelopeConflictRadius *
            schedule.actualScale coordinate.1
    change
      second ≠ first ∧
        wz1PaperLineDistance
            ((quotient.level coordinate.1).centerFamily.tube second)
            ((quotient.level coordinate.1).centerFamily.tube first) ≤
          pureWZ2Prop62UpperEnvelopeConflictRadius *
            schedule.actualScale coordinate.1 at conflictData
    exact
      ⟨conflictData.1.symm, by
        rw [wz1PaperLineDistance_symm]
        exact conflictData.2⟩
  have irreflexive :
      ∀ center, ¬conflict center center := by
    intro center conflictData
    change
      center ≠ center ∧
        wz1PaperLineDistance
            ((quotient.level coordinate.1).centerFamily.tube center)
            ((quotient.level coordinate.1).centerFamily.tube center) ≤
          pureWZ2Prop62UpperEnvelopeConflictRadius *
            schedule.actualScale coordinate.1 at conflictData
    exact conflictData.1 rfl
  rcases
      pureWZ2_greedy_proper_coloring
        (D := pureWZ2Prop62UpperEnvelopeConflictDegree)
        symmetric irreflexive
        (fun fixed => by
          exact
            pureWZ2_prop62_upperEnvelope_center_conflict_degree
              schedule fineNonempty fineLine quotient
              packetCoordinate coordinate fixed)
    with
    ⟨color, proper⟩
  exact
    ⟨{
      color := color
      proper := by
        intro first second indexNe distanceClose
        exact
          proper first second
            ⟨indexNe.symm, by
              rw [wz1PaperLineDistance_symm]
              exact distanceClose⟩
    }⟩

theorem pureWZ2_prop62_upperEnvelope_center_coloring
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (fineLine : WZ1PaperIsLineClass fine)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (packetCoordinate : Fin schedule.levelCount) :
    Nonempty
      (PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate) := by
  let coordinateColoring :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        PureWZ2Prop62UpperEnvelopeLevelColoringData
          (quotient := quotient) coordinate :=
    fun coordinate => by
      exact Classical.choice <|
        pureWZ2_prop62_upperEnvelope_level_coloring
          schedule fineNonempty fineLine quotient
          packetCoordinate coordinate
  exact
    ⟨{
      color := fun coordinate =>
        (coordinateColoring coordinate).color
      proper := fun coordinate =>
        (coordinateColoring coordinate).proper
    }⟩

namespace PureWZ2Prop62UpperEnvelopeCenterColoringData

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
    {packetCoordinate : Fin schedule.levelCount}
    (coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate)

def leafColor
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (source : Fin fine.card) :
    Fin (pureWZ2Prop62UpperEnvelopeConflictDegree + 1) :=
  coloring.color coordinate
    (quotient.leafCenter coordinate.1 source)

def metricParentColor
    {width : ℝ}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (output :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (parent : Fin output.metricParents.card) :
    Fin (pureWZ2Prop62UpperEnvelopeConflictDegree + 1) :=
  coloring.color coordinate
    (output.upperQuotientCenter coordinate parent)

theorem leafColor_eq_metricParentColor
    {width : ℝ}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (output :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (source : Fin output.selectedFine.card) :
    coloring.leafColor coordinate
        (output.mesh.complete.selectedFine.embedding source) =
      coloring.metricParentColor output coordinate
        (output.section6Cover.toWZ1PaperTubeCover.parent source) := by
  unfold leafColor metricParentColor
  rw [output.upperQuotientCenter_source
    fineLine fineBase rhoPos widthPos packetScaleLeRho sixWidthLe
    coordinate
    (output.section6Cover.toWZ1PaperTubeCover.parent source)
    source rfl]

theorem earlierCenter_lineDistance_le
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (later :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (earlier :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (earlierLe : earlier.1.1 ≤ later.1.1)
    (first second : Fin fine.card)
    (laterCenterEq :
      quotient.leafCenter later.1 first =
        quotient.leafCenter later.1 second) :
    wz1PaperLineDistance
        ((quotient.level earlier.1).centerFamily.tube
          (quotient.leafCenter earlier.1 first))
        ((quotient.level earlier.1).centerFamily.tube
          (quotient.leafCenter earlier.1 second)) ≤
      2400003 * schedule.actualScale earlier.1 := by
  let earlierScale := schedule.actualScale earlier.1
  let laterScale := schedule.actualScale later.1
  let firstEarlierParent :=
    (schedule.scaleData earlier.1).cover.parent first
  let secondEarlierParent :=
    (schedule.scaleData earlier.1).cover.parent second
  let firstLaterParent :=
    (schedule.scaleData later.1).cover.parent first
  let secondLaterParent :=
    (schedule.scaleData later.1).cover.parent second
  let firstEarlierProxy :=
    schedule.coordinateProxyTube
      fineNonempty earlier.1 firstEarlierParent
  let secondEarlierProxy :=
    schedule.coordinateProxyTube
      fineNonempty earlier.1 secondEarlierParent
  have firstCenterProxy :
      wz1PaperLineDistance
          ((quotient.level earlier.1).centerFamily.tube
            (quotient.leafCenter earlier.1 first))
          firstEarlierProxy ≤
        earlierScale / 4 := by
    rw [wz1PaperLineDistance_symm]
    exact
      (quotient.level earlier.1).actualProxy_center_lineDistance_le
        fineLine firstEarlierParent
  have firstProxyFine :
      wz1PaperLineDistance firstEarlierProxy (fine.tube first) ≤
        600000 * earlierScale := by
    rw [wz1PaperLineDistance_symm]
    exact
      schedule.completePacket_coordinateProxyTube_lineDistance_le
        fineNonempty fineLine fineBase earlier.1
        firstEarlierParent first
        ((schedule.scaleData earlier.1).cover.parent_mem_fullFiber first)
  have firstFineLaterProxy :
      wz1PaperLineDistance
          (fine.tube first)
          (schedule.coordinateProxyTube
            fineNonempty later.1 firstLaterParent) ≤
        600000 * laterScale :=
    schedule.completePacket_coordinateProxyTube_lineDistance_le
      fineNonempty fineLine fineBase later.1 firstLaterParent first
      ((schedule.scaleData later.1).cover.parent_mem_fullFiber first)
  have secondLaterProxyFine :
      wz1PaperLineDistance
          (schedule.coordinateProxyTube
            fineNonempty later.1 secondLaterParent)
          (fine.tube second) ≤
        600000 * laterScale := by
    rw [wz1PaperLineDistance_symm]
    exact
      schedule.completePacket_coordinateProxyTube_lineDistance_le
        fineNonempty fineLine fineBase later.1 secondLaterParent second
        ((schedule.scaleData later.1).cover.parent_mem_fullFiber second)
  have secondFineEarlierProxy :
      wz1PaperLineDistance (fine.tube second) secondEarlierProxy ≤
        600000 * earlierScale :=
    schedule.completePacket_coordinateProxyTube_lineDistance_le
      fineNonempty fineLine fineBase earlier.1
      secondEarlierParent second
      ((schedule.scaleData earlier.1).cover.parent_mem_fullFiber second)
  have secondProxyCenter :
      wz1PaperLineDistance
          secondEarlierProxy
          ((quotient.level earlier.1).centerFamily.tube
            (quotient.leafCenter earlier.1 second)) ≤
        earlierScale / 4 :=
    (quotient.level earlier.1).actualProxy_center_lineDistance_le
      fineLine secondEarlierParent
  have firstLaterProxyCenter :
      wz1PaperLineDistance
          (schedule.coordinateProxyTube
            fineNonempty later.1 firstLaterParent)
          ((quotient.level later.1).centerFamily.tube
            (quotient.leafCenter later.1 first)) ≤
        laterScale / 4 :=
    (quotient.level later.1).actualProxy_center_lineDistance_le
      fineLine firstLaterParent
  have centerSecondLaterProxy :
      wz1PaperLineDistance
          ((quotient.level later.1).centerFamily.tube
            (quotient.leafCenter later.1 second))
          (schedule.coordinateProxyTube
            fineNonempty later.1 secondLaterParent) ≤
        laterScale / 4 := by
    rw [wz1PaperLineDistance_symm]
    exact
      (quotient.level later.1).actualProxy_center_lineDistance_le
        fineLine secondLaterParent
  have laterProxyDistance :
      wz1PaperLineDistance
          (schedule.coordinateProxyTube
            fineNonempty later.1 firstLaterParent)
          (schedule.coordinateProxyTube
            fineNonempty later.1 secondLaterParent) ≤
        laterScale / 2 := by
    calc
      wz1PaperLineDistance
          (schedule.coordinateProxyTube
            fineNonempty later.1 firstLaterParent)
          (schedule.coordinateProxyTube
            fineNonempty later.1 secondLaterParent) ≤
        wz1PaperLineDistance
            (schedule.coordinateProxyTube
              fineNonempty later.1 firstLaterParent)
            ((quotient.level later.1).centerFamily.tube
              (quotient.leafCenter later.1 first)) +
          wz1PaperLineDistance
            ((quotient.level later.1).centerFamily.tube
              (quotient.leafCenter later.1 second))
            (schedule.coordinateProxyTube
              fineNonempty later.1 secondLaterParent) := by
        rw [laterCenterEq]
        exact wz1PaperLineDistance_triangle _ _ _
      _ ≤ laterScale / 4 + laterScale / 4 := by
        gcongr
      _ = laterScale / 2 := by ring
  have firstCenterFine :
      wz1PaperLineDistance
          ((quotient.level earlier.1).centerFamily.tube
            (quotient.leafCenter earlier.1 first))
          (fine.tube first) ≤
        earlierScale / 4 + 600000 * earlierScale :=
    (wz1PaperLineDistance_triangle _ firstEarlierProxy _).trans <| by
      linarith
  have firstCenterLaterProxy :
      wz1PaperLineDistance
          ((quotient.level earlier.1).centerFamily.tube
            (quotient.leafCenter earlier.1 first))
          (schedule.coordinateProxyTube
            fineNonempty later.1 firstLaterParent) ≤
        earlierScale / 4 + 600000 * earlierScale +
          600000 * laterScale :=
    (wz1PaperLineDistance_triangle _ (fine.tube first) _).trans <| by
      linarith
  have firstCenterSecondLaterProxy :
      wz1PaperLineDistance
          ((quotient.level earlier.1).centerFamily.tube
            (quotient.leafCenter earlier.1 first))
          (schedule.coordinateProxyTube
            fineNonempty later.1 secondLaterParent) ≤
        earlierScale / 4 + 600000 * earlierScale +
          600000 * laterScale + laterScale / 2 :=
    (wz1PaperLineDistance_triangle _
      (schedule.coordinateProxyTube
        fineNonempty later.1 firstLaterParent) _).trans <| by
      linarith
  have firstCenterSecondFine :
      wz1PaperLineDistance
          ((quotient.level earlier.1).centerFamily.tube
            (quotient.leafCenter earlier.1 first))
          (fine.tube second) ≤
        earlierScale / 4 + 600000 * earlierScale +
          600000 * laterScale + laterScale / 2 +
          600000 * laterScale :=
    (wz1PaperLineDistance_triangle _
      (schedule.coordinateProxyTube
        fineNonempty later.1 secondLaterParent) _).trans <| by
      linarith
  have firstCenterSecondEarlierProxy :
      wz1PaperLineDistance
          ((quotient.level earlier.1).centerFamily.tube
            (quotient.leafCenter earlier.1 first))
          secondEarlierProxy ≤
        earlierScale / 4 + 600000 * earlierScale +
          600000 * laterScale + laterScale / 2 +
          600000 * laterScale + 600000 * earlierScale :=
    (wz1PaperLineDistance_triangle _ (fine.tube second) _).trans <| by
      linarith
  have total :
      wz1PaperLineDistance
          ((quotient.level earlier.1).centerFamily.tube
            (quotient.leafCenter earlier.1 first))
          ((quotient.level earlier.1).centerFamily.tube
            (quotient.leafCenter earlier.1 second)) ≤
        earlierScale / 4 + 600000 * earlierScale +
          600000 * laterScale + laterScale / 2 +
          600000 * laterScale + 600000 * earlierScale +
          earlierScale / 4 :=
    (wz1PaperLineDistance_triangle _ secondEarlierProxy _).trans <| by
      nlinarith [
        firstCenterSecondEarlierProxy,
        secondProxyCenter]
  have laterLeEarlier : laterScale ≤ earlierScale :=
    schedule.actualScale_antitone earlier.1 later.1 earlierLe
  have earlierPos : 0 < earlierScale :=
    (schedule.scaleData earlier.1).rho_pos
  have numerical :
      earlierScale / 4 + 600000 * earlierScale +
            600000 * laterScale + laterScale / 2 +
            600000 * laterScale + 600000 * earlierScale +
            earlierScale / 4 ≤
        2400003 * earlierScale := by
    nlinarith
  exact total.trans numerical

theorem earlierCenter_eq_of_monochromatic_of_laterCenter_eq
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (later :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (earlier :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (earlierLe : earlier.1.1 ≤ later.1.1)
    (first second : Fin fine.card)
    (colorEq :
      coloring.leafColor earlier first =
        coloring.leafColor earlier second)
    (laterCenterEq :
      quotient.leafCenter later.1 first =
        quotient.leafCenter later.1 second) :
    quotient.leafCenter earlier.1 first =
      quotient.leafCenter earlier.1 second := by
  by_contra centerNe
  exact
    (coloring.proper earlier
      (quotient.leafCenter earlier.1 first)
      (quotient.leafCenter earlier.1 second)
      centerNe
      ((earlierCenter_lineDistance_le
        (quotient := quotient)
        fineLine fineBase later earlier earlierLe first second
        laterCenterEq).trans <| by
          have scalePos :=
            (schedule.scaleData earlier.1).rho_pos
          norm_num [
            pureWZ2Prop62UpperEnvelopeConflictRadius]
          nlinarith))
      colorEq

theorem monochromatic_centerPacket_inter_prefixNode
    {width : ℝ}
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (U0 : Finset (Fin fine.card))
    (selectedColor :
      ∀ _coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        Fin (pureWZ2Prop62UpperEnvelopeConflictDegree + 1))
    (monochromatic :
      ∀ source ∈ U0,
        ∀ coordinate :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          coloring.leafColor coordinate source =
            selectedColor coordinate)
    (auxiliary :
      PureWZ2Prop62ProxyQuotientAuxiliaryLevel
        schedule fineNonempty quotient rho width packetCoordinate)
    (anchor : Fin fine.card)
    (anchorMem : anchor ∈ U0)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate) :
    U0 ∩
        quotient.centerPacketIndices coordinate.1
          (quotient.leafCenter coordinate.1 anchor) =
      U0 ∩
        auxiliary.prefixNodeAt (coordinate.1.1 + 1) anchor := by
  ext source
  simp only [Finset.mem_inter,
    PureWZ2Prop62ProxyQuotientScheduleData.centerPacketIndices,
    Finset.mem_filter, Finset.mem_univ, true_and,
    PureWZ2Prop62ProxyQuotientAuxiliaryLevel.prefixNodeAt]
  constructor
  · rintro ⟨sourceMem, centerEq⟩
    refine ⟨sourceMem, ?_⟩
    intro earlier earlierLt
    have earlierLeCoordinate :
        earlier.1 ≤ coordinate.1.1 := by
      omega
    have earlierLtPacket :
        earlier.1 < packetCoordinate.1 :=
      earlierLeCoordinate.trans_lt coordinate.2.2
    have earlierCoordinateBound :
        earlier.1 < schedule.levelCount :=
      earlierLtPacket.trans packetCoordinate.2
    have earlierRho :
        rho ≤
          schedule.actualScale
            ⟨earlier.1, earlierCoordinateBound⟩ := by
      exact
        coordinate.2.1.trans <|
          schedule.actualScale_antitone
            ⟨earlier.1, earlierCoordinateBound⟩
            coordinate.1 earlierLeCoordinate
    let earlierUpper :
        schedule.ProxyUpperCoordinate rho packetCoordinate :=
      ⟨⟨earlier.1, earlierCoordinateBound⟩,
        ⟨earlierRho, earlierLtPacket⟩⟩
    have sourceColor := monochromatic source sourceMem earlierUpper
    have anchorColor := monochromatic anchor anchorMem earlierUpper
    exact
      coloring.earlierCenter_eq_of_monochromatic_of_laterCenter_eq
        fineLine fineBase coordinate earlierUpper
        earlierLeCoordinate source anchor
        (sourceColor.trans anchorColor.symm) centerEq
  · rintro ⟨sourceMem, prefixMem⟩
    refine ⟨sourceMem, ?_⟩
    exact
      prefixMem coordinate
        (by
          change coordinate.1.1 < coordinate.1.1 + 1
          omega)

end PureWZ2Prop62UpperEnvelopeCenterColoringData

namespace PureWZ2Prop62ProxyQuotientAuxiliaryLevel

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
    (auxiliary :
      PureWZ2Prop62ProxyQuotientAuxiliaryLevel
        schedule fineNonempty quotient rho width packetCoordinate)

theorem tree_fiber_prefix_eq
    (coordinate : Fin packetCoordinate.1)
    (leaf : Fin fine.card) :
    auxiliary.tree.fiber (coordinate.1 + 1)
        (auxiliary.nodeAt (coordinate.1 + 1) leaf) =
      auxiliary.prefixNodeAt (coordinate.1 + 1) leaf := by
  have levelLe :
      coordinate.1 + 1 ≤ packetCoordinate.1 := by
    omega
  ext source
  change
    (source ∈
      Finset.univ.filter fun candidate =>
        auxiliary.nodeAt (coordinate.1 + 1) candidate =
          auxiliary.nodeAt (coordinate.1 + 1) leaf) ↔
      source ∈ auxiliary.prefixNodeAt (coordinate.1 + 1) leaf
  simp only [
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [auxiliary.nodeAt_prefix levelLe,
    auxiliary.nodeAt_prefix levelLe]
  constructor
  · intro nodeEq
    have sourceMem :
        source ∈
          auxiliary.prefixNodeAt (coordinate.1 + 1) source := by
      unfold prefixNodeAt
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact
        schedule.proxyUpperCenterPrefixEquivalent_refl
          fineNonempty quotient rho packetCoordinate
          (coordinate.1 + 1) source
    rw [nodeEq] at sourceMem
    exact sourceMem
  · intro sourceMem
    exact
      auxiliary.prefixNodeAt_eq_of_equivalent
        (coordinate.1 + 1) source leaf <| by
          simpa only [
            PureWZ2Prop62ProxyQuotientAuxiliaryLevel.prefixNodeAt,
            Finset.mem_filter, Finset.mem_univ, true_and
          ] using sourceMem

theorem tree_fiber_upperCoordinate_prefix_eq
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (leaf : Fin fine.card) :
    auxiliary.tree.fiber (coordinate.1.1 + 1)
        (auxiliary.nodeAt (coordinate.1.1 + 1) leaf) =
      auxiliary.prefixNodeAt (coordinate.1.1 + 1) leaf := by
  exact
    auxiliary.tree_fiber_prefix_eq
      ⟨coordinate.1.1, coordinate.2.2⟩ leaf

end PureWZ2Prop62ProxyQuotientAuxiliaryLevel

end Kakeya.Assouad

end
