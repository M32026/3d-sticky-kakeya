import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CompleteAncestryAuxiliaryLevel
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ScheduledParentConflictColoring

/-!
# Proposition 6.2: upper ancestry selection inside each metric cell

At every old coordinate whose scale is at least the prescribed metric scale
`rho`, the scheduled-parent conflict coloring separates distinct ancestors
which can occur above one `s`-mesh cell.  Therefore the vector of conflict
colors determines the complete upper ancestry inside that cell.  The per-cell
weighted selector may choose this vector independently in each occupied cell.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62PureSchedule

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow)

/-- Old schedule coordinates above `rho` and before the packet coordinate. -/
abbrev UpperCoordinate
    (rho : ℝ)
    (packetCoordinate : Fin schedule.levelCount) :=
  {coordinate : Fin schedule.levelCount //
    rho ≤ schedule.actualScale coordinate ∧
      coordinate.1 < packetCoordinate.1}

/-- Exact old parent vector on the upper schedule coordinates. -/
abbrev UpperAncestry
    (rho : ℝ)
    (packetCoordinate : Fin schedule.levelCount) :=
  ∀ coordinate : schedule.UpperCoordinate rho packetCoordinate,
    Fin (schedule.scaleData coordinate.1).coarse.card

/-- Scheduled conflict-color vector on all upper coordinates. -/
abbrev UpperColorVector
    (rho : ℝ)
    (packetCoordinate : Fin schedule.levelCount) :=
  schedule.UpperCoordinate rho packetCoordinate →
    Fin (pureWZ2OrdinaryLineConflictDegree + 1)

/-- Upper old ancestry of one ambient fine leaf. -/
def upperAncestry
    (rho : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (source : Fin fine.card) :
    schedule.UpperAncestry rho packetCoordinate :=
  fun coordinate =>
    (schedule.scaleData coordinate.1).cover.parent source

/-- Upper scheduled conflict-color vector of one ambient fine leaf. -/
def upperColorVector
    (scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule)
    (rho : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (source : Fin fine.card) :
    schedule.UpperColorVector rho packetCoordinate :=
  fun coordinate =>
    scheduled.leafColor coordinate.1 source

/-- The line-parameter cell of the old `s`-parent of one fine leaf. -/
def packetLineCell
    (packetCoordinate : Fin schedule.levelCount)
    (width : ℝ)
    (source : Fin fine.card) :
    Fin 4 → ℤ :=
  pureWZ2Prop62LineCell width
    ((schedule.scaleData packetCoordinate).coarse.tube
      ((schedule.scaleData packetCoordinate).cover.parent source))

theorem packetLineCell_parent_invariant
    (packetCoordinate : Fin schedule.levelCount)
    (width : ℝ)
    (first second : Fin fine.card)
    (parentEq :
      (schedule.scaleData packetCoordinate).cover.parent first =
        (schedule.scaleData packetCoordinate).cover.parent second) :
    schedule.packetLineCell packetCoordinate width first =
      schedule.packetLineCell packetCoordinate width second := by
  unfold packetLineCell
  rw [parentEq]

/--
Two upper old parents lying above the same `s`-mesh cell are inside the
scheduled conflict radius.
-/
theorem upperParent_lineDistance_le_of_same_packetLineCell
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (parentCovers :
      ∀ coordinate source,
        WZ1PaperTubeCovers
          (fine.tube source)
          ((schedule.scaleData coordinate).coarse.tube
            ((schedule.scaleData coordinate).cover.parent source)))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate)
    (first second : Fin fine.card)
    (sameCell :
      schedule.packetLineCell packetCoordinate width first =
        schedule.packetLineCell packetCoordinate width second) :
    wz1PaperLineDistance
        ((schedule.scaleData coordinate.1).coarse.tube
          ((schedule.scaleData coordinate.1).cover.parent first))
        ((schedule.scaleData coordinate.1).coarse.tube
          ((schedule.scaleData coordinate.1).cover.parent second)) ≤
      wz2PaperLiteralSourceSeparationFactor *
        schedule.actualScale coordinate.1 := by
  let upperData := schedule.scaleData coordinate.1
  let packetData := schedule.scaleData packetCoordinate
  have upperPos : 0 < schedule.actualScale coordinate.1 :=
    upperData.rho_pos
  have packetParentsClose :
      wz1PaperLineDistance
          (packetData.coarse.tube (packetData.cover.parent first))
          (packetData.coarse.tube (packetData.cover.parent second)) ≤
        6 * width := by
    exact
      pureWZ2_prop62_sameLineCell_lineDistance_le
        widthPos
        (packetData.coarse.tube (packetData.cover.parent first))
        (packetData.coarse.tube (packetData.cover.parent second))
        (schedule.coarse_line_class packetCoordinate
          (packetData.cover.parent first))
        (schedule.coarse_line_class packetCoordinate
          (packetData.cover.parent second))
        sameCell
  have firstUpper :
      wz1PaperLineDistance
          (upperData.coarse.tube (upperData.cover.parent first))
          (fine.tube first) ≤
        schedule.actualScale coordinate.1 / 2 := by
    rw [wz1PaperLineDistance_symm]
    exact parentCovers coordinate.1 first
  have firstPacket :
      wz1PaperLineDistance
          (fine.tube first)
          (packetData.coarse.tube (packetData.cover.parent first)) ≤
        schedule.actualScale packetCoordinate / 2 :=
    parentCovers packetCoordinate first
  have secondPacket :
      wz1PaperLineDistance
          (packetData.coarse.tube (packetData.cover.parent second))
          (fine.tube second) ≤
        schedule.actualScale packetCoordinate / 2 := by
    rw [wz1PaperLineDistance_symm]
    exact parentCovers packetCoordinate second
  have secondUpper :
      wz1PaperLineDistance
          (fine.tube second)
          (upperData.coarse.tube (upperData.cover.parent second)) ≤
        schedule.actualScale coordinate.1 / 2 :=
    parentCovers coordinate.1 second
  have firstToPacket :
      wz1PaperLineDistance
          (upperData.coarse.tube (upperData.cover.parent first))
          (packetData.coarse.tube (packetData.cover.parent first)) ≤
        schedule.actualScale coordinate.1 / 2 +
          schedule.actualScale packetCoordinate / 2 := by
    exact
      (wz1PaperLineDistance_triangle
        (upperData.coarse.tube (upperData.cover.parent first))
        (fine.tube first)
        (packetData.coarse.tube
          (packetData.cover.parent first))).trans <| by
          gcongr
  have packetToSecond :
      wz1PaperLineDistance
          (packetData.coarse.tube (packetData.cover.parent second))
          (upperData.coarse.tube (upperData.cover.parent second)) ≤
        schedule.actualScale packetCoordinate / 2 +
          schedule.actualScale coordinate.1 / 2 := by
    exact
      (wz1PaperLineDistance_triangle
        (packetData.coarse.tube (packetData.cover.parent second))
        (fine.tube second)
        (upperData.coarse.tube
          (upperData.cover.parent second))).trans <| by
          gcongr
  have total :
      wz1PaperLineDistance
          (upperData.coarse.tube (upperData.cover.parent first))
          (upperData.coarse.tube (upperData.cover.parent second)) ≤
        schedule.actualScale coordinate.1 +
          schedule.actualScale packetCoordinate + 6 * width := by
    calc
      wz1PaperLineDistance
          (upperData.coarse.tube (upperData.cover.parent first))
          (upperData.coarse.tube (upperData.cover.parent second)) ≤
          wz1PaperLineDistance
              (upperData.coarse.tube (upperData.cover.parent first))
              (packetData.coarse.tube (packetData.cover.parent first)) +
            wz1PaperLineDistance
              (packetData.coarse.tube (packetData.cover.parent first))
              (upperData.coarse.tube (upperData.cover.parent second)) :=
        wz1PaperLineDistance_triangle
          (upperData.coarse.tube (upperData.cover.parent first))
          (packetData.coarse.tube (packetData.cover.parent first))
          (upperData.coarse.tube (upperData.cover.parent second))
      _ ≤
          wz1PaperLineDistance
              (upperData.coarse.tube (upperData.cover.parent first))
              (packetData.coarse.tube (packetData.cover.parent first)) +
            (wz1PaperLineDistance
                (packetData.coarse.tube (packetData.cover.parent first))
                (packetData.coarse.tube
                  (packetData.cover.parent second)) +
              wz1PaperLineDistance
                (packetData.coarse.tube
                  (packetData.cover.parent second))
                (upperData.coarse.tube
                  (upperData.cover.parent second))) := by
        exact
          add_le_add_right
            (wz1PaperLineDistance_triangle
              (packetData.coarse.tube (packetData.cover.parent first))
              (packetData.coarse.tube (packetData.cover.parent second))
              (upperData.coarse.tube (upperData.cover.parent second)))
            (wz1PaperLineDistance
              (upperData.coarse.tube (upperData.cover.parent first))
              (packetData.coarse.tube (packetData.cover.parent first)))
      _ ≤
          (schedule.actualScale coordinate.1 / 2 +
              schedule.actualScale packetCoordinate / 2) +
            (6 * width +
              (schedule.actualScale packetCoordinate / 2 +
                schedule.actualScale coordinate.1 / 2)) := by
        exact add_le_add firstToPacket
          (add_le_add packetParentsClose packetToSecond)
      _ =
          schedule.actualScale coordinate.1 +
            schedule.actualScale packetCoordinate + 6 * width := by
        ring
  calc
    wz1PaperLineDistance
        (upperData.coarse.tube (upperData.cover.parent first))
        (upperData.coarse.tube (upperData.cover.parent second)) ≤
        schedule.actualScale coordinate.1 +
          schedule.actualScale packetCoordinate + 6 * width :=
      total
    _ ≤ 5 / 2 * schedule.actualScale coordinate.1 := by
      have rhoLeUpper := coordinate.2.1
      nlinarith
    _ ≤
        wz2PaperLiteralSourceSeparationFactor *
          schedule.actualScale coordinate.1 := by
      unfold wz2PaperLiteralSourceSeparationFactor
      nlinarith

/--
Inside one packet cell, equality of all upper conflict colors forces equality
of the complete upper ancestry.
-/
theorem upperAncestry_eq_of_sameCell_and_colorVector_eq
    (scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (parentCovers :
      ∀ coordinate source,
        WZ1PaperTubeCovers
          (fine.tube source)
          ((schedule.scaleData coordinate).coarse.tube
            ((schedule.scaleData coordinate).cover.parent source)))
    (first second : Fin fine.card)
    (sameCell :
      schedule.packetLineCell packetCoordinate width first =
        schedule.packetLineCell packetCoordinate width second)
    (sameColors :
      schedule.upperColorVector scheduled rho packetCoordinate first =
        schedule.upperColorVector scheduled rho packetCoordinate second) :
    schedule.upperAncestry rho packetCoordinate first =
      schedule.upperAncestry rho packetCoordinate second := by
  funext coordinate
  let firstParent :=
    (schedule.scaleData coordinate.1).cover.parent first
  let secondParent :=
    (schedule.scaleData coordinate.1).cover.parent second
  by_contra parentNe
  have distanceClose :=
    schedule.upperParent_lineDistance_le_of_same_packetLineCell
      rho width packetCoordinate rhoPos widthPos packetScaleLeRho sixWidthLe
      parentCovers coordinate first second sameCell
  have colorNe :=
    (scheduled.coloring coordinate.1).proper
      firstParent secondParent parentNe distanceClose
  have colorEq :
      (scheduled.coloring coordinate.1).color firstParent =
        (scheduled.coloring coordinate.1).color secondParent := by
    exact congrFun sameColors coordinate
  exact colorNe colorEq

/--
If every old coordinate before the packet level lies above `rho`, equality of
the selected upper ancestry vector is equality of the complete old ancestry
vector used by the auxiliary level.
-/
theorem ancestry_eq_of_upperAncestry_eq
    (rho : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (first second : Fin fine.card)
    (upperAncestryEq :
      schedule.upperAncestry rho packetCoordinate first =
        schedule.upperAncestry rho packetCoordinate second) :
    schedule.ancestry packetCoordinate first =
      schedule.ancestry packetCoordinate second := by
  funext coordinate
  let upperCoordinate :
      schedule.UpperCoordinate rho packetCoordinate :=
    ⟨schedule.ancestryAmbientCoordinate
        packetCoordinate coordinate,
      allAncestryCoordinatesUpper coordinate,
      by
        change coordinate.1 < packetCoordinate.1
        exact coordinate.2⟩
  exact congrFun upperAncestryEq upperCoordinate

/-- Per-cell selection of one upper ancestry color vector. -/
noncomputable def selectUpperAncestryColorPerCell
    (scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (weight : Fin fine.card → ENNReal) :
    PureWZ2Prop62PerCellColorSelectionData
      (Fin fine.card)
      (PacketCell
        (schedule.packetLineCell packetCoordinate width))
      (schedule.UpperColorVector rho packetCoordinate)
      (packetCell
        (schedule.packetLineCell packetCoordinate width))
      (schedule.upperColorVector
        scheduled rho packetCoordinate)
      weight :=
  Classical.choice <|
    pureWZ2_prop62_perCell_color_selection
      (Fin fine.card)
      (PacketCell
        (schedule.packetLineCell packetCoordinate width))
      (schedule.UpperColorVector rho packetCoordinate)
      (packetCell
        (schedule.packetLineCell packetCoordinate width))
      (schedule.upperColorVector
        scheduled rho packetCoordinate)
      weight

namespace PureWZ2Prop62PerCellColorSelectionData

theorem selected_upperAncestry_eq_of_sameCell
    (scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (weight : Fin fine.card → ENNReal)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (parentCovers :
      ∀ coordinate source,
        WZ1PaperTubeCovers
          (fine.tube source)
          ((schedule.scaleData coordinate).coarse.tube
            ((schedule.scaleData coordinate).cover.parent source)))
    (first second : Fin fine.card)
    (firstMem :
      first ∈
        (schedule.selectUpperAncestryColorPerCell
          scheduled rho width packetCoordinate weight).selected)
    (secondMem :
      second ∈
        (schedule.selectUpperAncestryColorPerCell
          scheduled rho width packetCoordinate weight).selected)
    (sameCell :
      schedule.packetLineCell packetCoordinate width first =
        schedule.packetLineCell packetCoordinate width second) :
    schedule.upperAncestry rho packetCoordinate first =
      schedule.upperAncestry rho packetCoordinate second := by
  let selection :=
    schedule.selectUpperAncestryColorPerCell
      scheduled rho width packetCoordinate weight
  have firstColor := selection.selected_monochromatic first firstMem
  have secondColor := selection.selected_monochromatic second secondMem
  have packetCellEq :
      packetCell
          (schedule.packetLineCell packetCoordinate width) first =
        packetCell
          (schedule.packetLineCell packetCoordinate width) second := by
    apply Subtype.ext
    exact sameCell
  rw [packetCellEq] at firstColor
  have colorEq :
      schedule.upperColorVector scheduled rho packetCoordinate first =
        schedule.upperColorVector scheduled rho packetCoordinate second :=
    firstColor.trans secondColor.symm
  exact
    schedule.upperAncestry_eq_of_sameCell_and_colorVector_eq
      scheduled rho width packetCoordinate rhoPos widthPos
      packetScaleLeRho sixWidthLe parentCovers
      first second sameCell colorEq

end PureWZ2Prop62PerCellColorSelectionData

end PureWZ2Prop62PureSchedule

end Kakeya.Assouad

end
