import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CompleteAncestryAuxiliaryLevel
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62GlobalResiduePerCellSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PerCellColorSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientSchedule

/-!
# Proposition 6.2 proxy upper ancestry inside each packet cell

The literal Definition 2.12 parent tree and the Section 6 line geometry are
kept separate.  At each upper level, actual complete parents are sent to the
proxy-line quotient center constructed in `Prop62ProxyQuotientSchedule`.

Inside one packet-scale proxy cell, equality of all quotient-center colors
forces equality of the complete quotient-center ancestry.  The color is
selected independently in every occupied packet cell, as in the paper.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62LaminarPureSchedule

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)

/-- Old coordinates above `rho` and strictly before the packet level. -/
abbrev ProxyUpperCoordinate
    (rho : ℝ)
    (packetCoordinate : Fin schedule.levelCount) :=
  {coordinate : Fin schedule.levelCount //
    rho ≤ schedule.actualScale coordinate ∧
      coordinate.1 < packetCoordinate.1}

/-- Finite color vectors on the old levels above `rho`. -/
abbrev ProxyUpperColorVector
    (rho : ℝ)
    (packetCoordinate : Fin schedule.levelCount) :=
  schedule.ProxyUpperCoordinate rho packetCoordinate →
    Fin (pureWZ2Prop62ProxyCenterConflictDegree + 1)

/-- Finite image of a packet-cell label on the laminar schedule leaves. -/
def proxyPacketCells
    {RawCell : Type}
    [DecidableEq RawCell]
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (rawCell : Fin fine.card → RawCell) :
    Finset RawCell :=
  Finset.image rawCell Finset.univ

/-- Occupied packet-cell subtype for the laminar schedule. -/
abbrev ProxyPacketCell
    {RawCell : Type}
    [DecidableEq RawCell]
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (rawCell : Fin fine.card → RawCell) :=
  {cell // cell ∈ schedule.proxyPacketCells rawCell}

/-- Canonical occupied packet-cell label of one leaf. -/
def proxyPacketCell
    {RawCell : Type}
    [DecidableEq RawCell]
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (rawCell : Fin fine.card → RawCell)
    (source : Fin fine.card) :
    schedule.ProxyPacketCell rawCell :=
  ⟨rawCell source,
    Finset.mem_image.mpr
      ⟨source, Finset.mem_univ source, rfl⟩⟩

/-- Packet-scale line cell of the actual packet's canonical proxy axis. -/
def proxyPacketLineCell
    (fineNonempty : fine.Nonempty)
    (packetCoordinate : Fin schedule.levelCount)
    (width : ℝ)
    (source : Fin fine.card) :
    Fin 4 → ℤ :=
  pureWZ2Prop62LineCell width <|
    schedule.coordinateProxyTube
      fineNonempty packetCoordinate
      ((schedule.scaleData packetCoordinate).cover.parent source)

theorem proxyPacketLineCell_parent_invariant
    (fineNonempty : fine.Nonempty)
    (packetCoordinate : Fin schedule.levelCount)
    (width : ℝ)
    (first second : Fin fine.card)
    (parentEq :
      (schedule.scaleData packetCoordinate).cover.parent first =
        (schedule.scaleData packetCoordinate).cover.parent second) :
    schedule.proxyPacketLineCell
        fineNonempty packetCoordinate width first =
      schedule.proxyPacketLineCell
        fineNonempty packetCoordinate width second := by
  unfold proxyPacketLineCell
  rw [parentEq]

end PureWZ2Prop62LaminarPureSchedule

namespace PureWZ2Prop62ProxyQuotientScheduleData

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)

/-- Complete quotient-center ancestry on the old levels above `rho`. -/
abbrev ProxyUpperAncestry
    (rho : ℝ)
    (packetCoordinate : Fin schedule.levelCount) :=
  ∀ coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate,
    Fin (quotient.level coordinate.1).centerFamily.card

/-- Quotient-center ancestry of one ambient fine leaf. -/
def proxyUpperAncestry
    (rho : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (source : Fin fine.card) :
    quotient.ProxyUpperAncestry rho packetCoordinate :=
  fun coordinate =>
    quotient.leafCenter coordinate.1 source

/-- Quotient-center color vector of one ambient fine leaf. -/
def proxyUpperColorVector
    (rho : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (source : Fin fine.card) :
    schedule.ProxyUpperColorVector rho packetCoordinate :=
  fun coordinate =>
    quotient.leafCenterColor coordinate.1 source

/--
Two quotient centers above one packet-scale proxy cell are inside the fixed
center-color conflict radius.
-/
theorem upperCenter_lineDistance_le_of_same_proxyPacketLineCell
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (first second : Fin fine.card)
    (sameCell :
      schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width first =
        schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width second) :
    wz1PaperLineDistance
        ((quotient.level coordinate.1).centerFamily.tube
          (quotient.leafCenter coordinate.1 first))
        ((quotient.level coordinate.1).centerFamily.tube
          (quotient.leafCenter coordinate.1 second)) ≤
      wz2PaperLiteralSourceSeparationFactor *
        schedule.actualScale coordinate.1 := by
  let upperScale := schedule.actualScale coordinate.1
  let packetScale := schedule.actualScale packetCoordinate
  let firstUpperParent :=
    (schedule.scaleData coordinate.1).cover.parent first
  let secondUpperParent :=
    (schedule.scaleData coordinate.1).cover.parent second
  let firstPacketParent :=
    (schedule.scaleData packetCoordinate).cover.parent first
  let secondPacketParent :=
    (schedule.scaleData packetCoordinate).cover.parent second
  let firstUpperProxy :=
    schedule.coordinateProxyTube
      fineNonempty coordinate.1 firstUpperParent
  let secondUpperProxy :=
    schedule.coordinateProxyTube
      fineNonempty coordinate.1 secondUpperParent
  let firstPacketProxy :=
    schedule.coordinateProxyTube
      fineNonempty packetCoordinate firstPacketParent
  let secondPacketProxy :=
    schedule.coordinateProxyTube
      fineNonempty packetCoordinate secondPacketParent
  have firstCenterUpper :
      wz1PaperLineDistance
          ((quotient.level coordinate.1).centerFamily.tube
            (quotient.leafCenter coordinate.1 first))
          firstUpperProxy ≤
        upperScale / 4 := by
    rw [wz1PaperLineDistance_symm]
    exact
      (quotient.level coordinate.1).actualProxy_center_lineDistance_le
        fineLine firstUpperParent
  have firstUpperFine :
      wz1PaperLineDistance firstUpperProxy (fine.tube first) ≤
        600000 * upperScale := by
    rw [wz1PaperLineDistance_symm]
    exact
      schedule.completePacket_coordinateProxyTube_lineDistance_le
        fineNonempty fineLine fineBase coordinate.1
        firstUpperParent first
        ((schedule.scaleData coordinate.1).cover
          |>.parent_mem_fullFiber first)
  have firstFinePacket :
      wz1PaperLineDistance (fine.tube first) firstPacketProxy ≤
        600000 * packetScale :=
    schedule.completePacket_coordinateProxyTube_lineDistance_le
      fineNonempty fineLine fineBase packetCoordinate
      firstPacketParent first
      ((schedule.scaleData packetCoordinate).cover
        |>.parent_mem_fullFiber first)
  have packetProxyClose :
      wz1PaperLineDistance firstPacketProxy secondPacketProxy ≤
        6 * width := by
    exact
      pureWZ2_prop62_sameLineCell_lineDistance_le
        widthPos firstPacketProxy secondPacketProxy
        (schedule.coordinateProxyTube_lineClass
          fineNonempty fineLine packetCoordinate firstPacketParent)
        (schedule.coordinateProxyTube_lineClass
          fineNonempty fineLine packetCoordinate secondPacketParent)
        sameCell
  have secondPacketFine :
      wz1PaperLineDistance secondPacketProxy (fine.tube second) ≤
        600000 * packetScale := by
    rw [wz1PaperLineDistance_symm]
    exact
      schedule.completePacket_coordinateProxyTube_lineDistance_le
        fineNonempty fineLine fineBase packetCoordinate
        secondPacketParent second
        ((schedule.scaleData packetCoordinate).cover
          |>.parent_mem_fullFiber second)
  have secondFineUpper :
      wz1PaperLineDistance (fine.tube second) secondUpperProxy ≤
        600000 * upperScale :=
    schedule.completePacket_coordinateProxyTube_lineDistance_le
      fineNonempty fineLine fineBase coordinate.1
      secondUpperParent second
      ((schedule.scaleData coordinate.1).cover
        |>.parent_mem_fullFiber second)
  have secondUpperCenter :
      wz1PaperLineDistance
          secondUpperProxy
          ((quotient.level coordinate.1).centerFamily.tube
            (quotient.leafCenter coordinate.1 second)) ≤
        upperScale / 4 :=
    (quotient.level coordinate.1).actualProxy_center_lineDistance_le
      fineLine secondUpperParent
  have total :
      wz1PaperLineDistance
          ((quotient.level coordinate.1).centerFamily.tube
            (quotient.leafCenter coordinate.1 first))
          ((quotient.level coordinate.1).centerFamily.tube
            (quotient.leafCenter coordinate.1 second)) ≤
        upperScale / 4 +
          (600000 * upperScale +
            (600000 * packetScale +
              (6 * width +
                (600000 * packetScale +
                  (600000 * upperScale +
                    upperScale / 4))))) := by
    calc
      wz1PaperLineDistance
          ((quotient.level coordinate.1).centerFamily.tube
            (quotient.leafCenter coordinate.1 first))
          ((quotient.level coordinate.1).centerFamily.tube
            (quotient.leafCenter coordinate.1 second))
          ≤
        wz1PaperLineDistance
            ((quotient.level coordinate.1).centerFamily.tube
              (quotient.leafCenter coordinate.1 first))
            firstUpperProxy +
          wz1PaperLineDistance
            firstUpperProxy
            ((quotient.level coordinate.1).centerFamily.tube
              (quotient.leafCenter coordinate.1 second)) :=
        wz1PaperLineDistance_triangle _ _ _
      _ ≤
        wz1PaperLineDistance
            ((quotient.level coordinate.1).centerFamily.tube
              (quotient.leafCenter coordinate.1 first))
            firstUpperProxy +
          (wz1PaperLineDistance firstUpperProxy (fine.tube first) +
            wz1PaperLineDistance
              (fine.tube first)
              ((quotient.level coordinate.1).centerFamily.tube
                (quotient.leafCenter coordinate.1 second))) := by
        gcongr
        exact wz1PaperLineDistance_triangle _ _ _
      _ ≤
        wz1PaperLineDistance
            ((quotient.level coordinate.1).centerFamily.tube
              (quotient.leafCenter coordinate.1 first))
            firstUpperProxy +
          (wz1PaperLineDistance firstUpperProxy (fine.tube first) +
            (wz1PaperLineDistance (fine.tube first) firstPacketProxy +
              wz1PaperLineDistance
                firstPacketProxy
                ((quotient.level coordinate.1).centerFamily.tube
                  (quotient.leafCenter coordinate.1 second)))) := by
        gcongr
        exact wz1PaperLineDistance_triangle _ _ _
      _ ≤
        wz1PaperLineDistance
            ((quotient.level coordinate.1).centerFamily.tube
              (quotient.leafCenter coordinate.1 first))
            firstUpperProxy +
          (wz1PaperLineDistance firstUpperProxy (fine.tube first) +
            (wz1PaperLineDistance (fine.tube first) firstPacketProxy +
              (wz1PaperLineDistance firstPacketProxy secondPacketProxy +
                wz1PaperLineDistance
                  secondPacketProxy
                  ((quotient.level coordinate.1).centerFamily.tube
                    (quotient.leafCenter coordinate.1 second))))) := by
        gcongr
        exact wz1PaperLineDistance_triangle _ _ _
      _ ≤
        wz1PaperLineDistance
            ((quotient.level coordinate.1).centerFamily.tube
              (quotient.leafCenter coordinate.1 first))
            firstUpperProxy +
          (wz1PaperLineDistance firstUpperProxy (fine.tube first) +
            (wz1PaperLineDistance (fine.tube first) firstPacketProxy +
              (wz1PaperLineDistance firstPacketProxy secondPacketProxy +
                (wz1PaperLineDistance
                    secondPacketProxy (fine.tube second) +
                  wz1PaperLineDistance
                    (fine.tube second)
                    ((quotient.level coordinate.1).centerFamily.tube
                      (quotient.leafCenter coordinate.1 second)))))) := by
        gcongr
        exact wz1PaperLineDistance_triangle _ _ _
      _ ≤
        wz1PaperLineDistance
            ((quotient.level coordinate.1).centerFamily.tube
              (quotient.leafCenter coordinate.1 first))
            firstUpperProxy +
          (wz1PaperLineDistance firstUpperProxy (fine.tube first) +
            (wz1PaperLineDistance (fine.tube first) firstPacketProxy +
              (wz1PaperLineDistance firstPacketProxy secondPacketProxy +
                (wz1PaperLineDistance
                    secondPacketProxy (fine.tube second) +
                  (wz1PaperLineDistance
                      (fine.tube second) secondUpperProxy +
                    wz1PaperLineDistance
                      secondUpperProxy
                      ((quotient.level coordinate.1).centerFamily.tube
                        (quotient.leafCenter coordinate.1 second))))))) := by
        gcongr
        exact wz1PaperLineDistance_triangle _ _ _
      _ ≤
        upperScale / 4 +
          (600000 * upperScale +
            (600000 * packetScale +
              (6 * width +
                (600000 * packetScale +
                  (600000 * upperScale +
                    upperScale / 4))))) := by
        exact
          add_le_add firstCenterUpper <|
            add_le_add firstUpperFine <|
              add_le_add firstFinePacket <|
                add_le_add packetProxyClose <|
                  add_le_add secondPacketFine <|
                    add_le_add secondFineUpper secondUpperCenter
  calc
    wz1PaperLineDistance
        ((quotient.level coordinate.1).centerFamily.tube
          (quotient.leafCenter coordinate.1 first))
        ((quotient.level coordinate.1).centerFamily.tube
          (quotient.leafCenter coordinate.1 second)) ≤
      upperScale / 4 +
        (600000 * upperScale +
          (600000 * packetScale +
            (6 * width +
              (600000 * packetScale +
                (600000 * upperScale +
                  upperScale / 4))))) :=
      total
    _ ≤ 2400001 * upperScale := by
      have rhoLeUpper : rho ≤ upperScale :=
        coordinate.2.1
      nlinarith
    _ ≤
        wz2PaperLiteralSourceSeparationFactor * upperScale := by
      have upperPos : 0 < upperScale :=
        (schedule.scaleData coordinate.1).rho_pos
      norm_num [wz2PaperLiteralSourceSeparationFactor]
      nlinarith

/--
Inside one packet proxy cell, equality of all upper center colors fixes the
complete quotient-center ancestry.
-/
theorem proxyUpperAncestry_eq_of_sameCell_and_colorVector_eq
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (first second : Fin fine.card)
    (sameCell :
      schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width first =
        schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width second)
    (sameColors :
      quotient.proxyUpperColorVector
          rho packetCoordinate first =
        quotient.proxyUpperColorVector
          rho packetCoordinate second) :
    quotient.proxyUpperAncestry rho packetCoordinate first =
      quotient.proxyUpperAncestry rho packetCoordinate second := by
  funext coordinate
  apply quotient.leafCenter_eq_of_color_eq_of_lineDistance_le
  · exact congrFun sameColors coordinate
  · exact
      quotient.upperCenter_lineDistance_le_of_same_proxyPacketLineCell
        fineLine fineBase rho width packetCoordinate rhoPos widthPos
        packetScaleLeRho sixWidthLe coordinate first second sameCell

/-- Per-cell selection of one quotient-center ancestry color vector. -/
noncomputable def selectProxyUpperAncestryColorPerCell
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (weight : Fin fine.card → ENNReal) :
    PureWZ2Prop62PerCellColorSelectionData
      (Fin fine.card)
      (schedule.ProxyPacketCell
        (schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width))
      (schedule.ProxyUpperColorVector rho packetCoordinate)
      (schedule.proxyPacketCell
        (schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width))
      (quotient.proxyUpperColorVector rho packetCoordinate)
      weight :=
  Classical.choice <|
    pureWZ2_prop62_perCell_color_selection
      (Fin fine.card)
      (schedule.ProxyPacketCell
        (schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width))
      (schedule.ProxyUpperColorVector rho packetCoordinate)
      (schedule.proxyPacketCell
        (schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width))
      (quotient.proxyUpperColorVector rho packetCoordinate)
      weight

/--
The paper's combined preliminary geometric choice: one global mesh residue
and one quotient-center ancestry color independently in every occupied
packet cell.
-/
noncomputable def selectProxyResidueUpperAncestryPerCell
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal) :
    PureWZ2Prop62GlobalResiduePerCellSelectionData
      (Fin fine.card)
      (schedule.ProxyPacketCell
        (schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width))
      (Fin 4 → ZMod (strideBase + 1))
      (schedule.ProxyUpperColorVector rho packetCoordinate)
      (schedule.proxyPacketCell
        (schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width))
      (fun source =>
        pureWZ2Prop62LineColor width (strideBase + 1)
          (schedule.coordinateProxyTube
            fineNonempty packetCoordinate
            ((schedule.scaleData packetCoordinate).cover.parent source)))
      (quotient.proxyUpperColorVector rho packetCoordinate)
      weight :=
  Classical.choice <|
    pureWZ2_prop62_globalResidue_perCell_color_selection
      (Fin fine.card)
      (schedule.ProxyPacketCell
        (schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width))
      (Fin 4 → ZMod (strideBase + 1))
      (schedule.ProxyUpperColorVector rho packetCoordinate)
      (schedule.proxyPacketCell
        (schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width))
      (fun source =>
        pureWZ2Prop62LineColor width (strideBase + 1)
          (schedule.coordinateProxyTube
            fineNonempty packetCoordinate
            ((schedule.scaleData packetCoordinate).cover.parent source)))
      (quotient.proxyUpperColorVector rho packetCoordinate)
      weight

namespace PureWZ2Prop62PerCellColorSelectionData

theorem proxyPerCell_selected_packet_saturated
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (weight : Fin fine.card → ENNReal)
    (first second : Fin fine.card)
    (packetParentEq :
      (schedule.scaleData packetCoordinate).cover.parent first =
        (schedule.scaleData packetCoordinate).cover.parent second) :
    first ∈
        (selectProxyUpperAncestryColorPerCell
          (quotient := quotient)
          rho width packetCoordinate weight).selected ↔
      second ∈
        (selectProxyUpperAncestryColorPerCell
          (quotient := quotient)
          rho width packetCoordinate weight).selected := by
  let selection :=
    selectProxyUpperAncestryColorPerCell
      (quotient := quotient)
      rho width packetCoordinate weight
  have cellValueEq :
      schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width first =
        schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width second :=
    schedule.proxyPacketLineCell_parent_invariant
      fineNonempty packetCoordinate width
      first second packetParentEq
  have cellEq :
      schedule.proxyPacketCell
          (schedule.proxyPacketLineCell
            fineNonempty packetCoordinate width) first =
        schedule.proxyPacketCell
          (schedule.proxyPacketLineCell
            fineNonempty packetCoordinate width) second := by
    apply Subtype.ext
    exact cellValueEq
  have colorEq :
      quotient.proxyUpperColorVector
          rho packetCoordinate first =
        quotient.proxyUpperColorVector
          rho packetCoordinate second := by
    funext coordinate
    unfold proxyUpperColorVector
    unfold PureWZ2Prop62ProxyQuotientScheduleData.leafCenterColor
    congr 1
    unfold PureWZ2Prop62ProxyQuotientScheduleData.leafCenter
    unfold PureWZ2Prop62ProxyQuotientScheduleData.actualCenter
    congr 1
    exact
      schedule.parent_eq_of_coordinate_le
        coordinate.1 packetCoordinate
        (Nat.le_of_lt coordinate.2.2)
        first second packetParentEq
  rw [selection.selected_eq]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [cellEq, colorEq]

theorem selected_proxyUpperAncestry_eq_of_sameCell
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (weight : Fin fine.card → ENNReal)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (first second : Fin fine.card)
    (firstMem :
      first ∈
        (selectProxyUpperAncestryColorPerCell
          (quotient := quotient)
          rho width packetCoordinate weight).selected)
    (secondMem :
      second ∈
        (selectProxyUpperAncestryColorPerCell
          (quotient := quotient)
          rho width packetCoordinate weight).selected)
    (sameCell :
      schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width first =
        schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width second) :
    quotient.proxyUpperAncestry rho packetCoordinate first =
      quotient.proxyUpperAncestry rho packetCoordinate second := by
  let selection :=
    selectProxyUpperAncestryColorPerCell
      (quotient := quotient)
      rho width packetCoordinate weight
  have firstColor :=
    selection.selected_monochromatic first firstMem
  have secondColor :=
    selection.selected_monochromatic second secondMem
  have packetCellEq :
      schedule.proxyPacketCell
          (schedule.proxyPacketLineCell
            fineNonempty packetCoordinate width) first =
        schedule.proxyPacketCell
          (schedule.proxyPacketLineCell
            fineNonempty packetCoordinate width) second := by
    apply Subtype.ext
    exact sameCell
  rw [packetCellEq] at firstColor
  have colorEq :
      quotient.proxyUpperColorVector
          rho packetCoordinate first =
        quotient.proxyUpperColorVector
          rho packetCoordinate second :=
    firstColor.trans secondColor.symm
  exact
    quotient.proxyUpperAncestry_eq_of_sameCell_and_colorVector_eq
      fineLine fineBase rho width packetCoordinate rhoPos widthPos
      packetScaleLeRho sixWidthLe first second sameCell colorEq

end PureWZ2Prop62PerCellColorSelectionData

namespace PureWZ2Prop62GlobalResiduePerCellSelectionData

theorem proxyResiduePerCell_selected_packet_saturated
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (first second : Fin fine.card)
    (packetParentEq :
      (schedule.scaleData packetCoordinate).cover.parent first =
        (schedule.scaleData packetCoordinate).cover.parent second) :
    first ∈
        (selectProxyResidueUpperAncestryPerCell
          (quotient := quotient)
          rho width packetCoordinate strideBase weight).selected ↔
      second ∈
        (selectProxyResidueUpperAncestryPerCell
          (quotient := quotient)
          rho width packetCoordinate strideBase weight).selected := by
  let selection :=
    selectProxyResidueUpperAncestryPerCell
      (quotient := quotient)
      rho width packetCoordinate strideBase weight
  have cellValueEq :
      schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width first =
        schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width second :=
    schedule.proxyPacketLineCell_parent_invariant
      fineNonempty packetCoordinate width
      first second packetParentEq
  have cellEq :
      schedule.proxyPacketCell
          (schedule.proxyPacketLineCell
            fineNonempty packetCoordinate width) first =
        schedule.proxyPacketCell
          (schedule.proxyPacketLineCell
            fineNonempty packetCoordinate width) second := by
    apply Subtype.ext
    exact cellValueEq
  have residueEq :
      pureWZ2Prop62LineColor width (strideBase + 1)
          (schedule.coordinateProxyTube
            fineNonempty packetCoordinate
            ((schedule.scaleData packetCoordinate).cover.parent first)) =
        pureWZ2Prop62LineColor width (strideBase + 1)
          (schedule.coordinateProxyTube
            fineNonempty packetCoordinate
            ((schedule.scaleData packetCoordinate).cover.parent second)) := by
    rw [packetParentEq]
  have colorEq :
      quotient.proxyUpperColorVector
          rho packetCoordinate first =
        quotient.proxyUpperColorVector
          rho packetCoordinate second := by
    funext coordinate
    unfold proxyUpperColorVector
    unfold PureWZ2Prop62ProxyQuotientScheduleData.leafCenterColor
    congr 1
    unfold PureWZ2Prop62ProxyQuotientScheduleData.leafCenter
    unfold PureWZ2Prop62ProxyQuotientScheduleData.actualCenter
    congr 1
    exact
      schedule.parent_eq_of_coordinate_le
        coordinate.1 packetCoordinate
        (Nat.le_of_lt coordinate.2.2)
        first second packetParentEq
  rw [selection.selected_eq]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [residueEq, cellEq, colorEq]

end PureWZ2Prop62GlobalResiduePerCellSelectionData

end PureWZ2Prop62ProxyQuotientScheduleData

end Kakeya.Assouad

end
