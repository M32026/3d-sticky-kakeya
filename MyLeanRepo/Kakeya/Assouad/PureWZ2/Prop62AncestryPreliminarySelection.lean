import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62GlobalResiduePerCellSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PreliminarySelection

/-!
# Proposition 6.2: combine per-cell ancestry and global preliminary colors

First choose one global mesh residue and, inside that residue, one
upper-ancestry color vector independently in every metric cell.  Then mask
all other leaves to weight zero and perform the paper's one global
dependent-color selection followed by one dyadic leaf-weight bin.  Positive
selected weight forces the final preliminary set to remain inside this
combined selection.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62AncestryPreliminarySelectionData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow)
    (scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    {coordinateCount : ℕ}
    (Color : Fin coordinateCount → Type*)
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    (color : ∀ coordinate, Fin fine.card → Color coordinate)
    (weight : Fin fine.card → ENNReal) where
  residueStrideBase : ℕ
  perCell :
    PureWZ2Prop62GlobalResiduePerCellSelectionData
      (Fin fine.card)
      (PureWZ2Prop62PureSchedule.PacketCell
        (schedule.packetLineCell packetCoordinate width))
      (Fin 4 → ZMod (residueStrideBase + 1))
      (schedule.UpperColorVector rho packetCoordinate)
      (PureWZ2Prop62PureSchedule.packetCell
        (schedule.packetLineCell packetCoordinate width))
      (fun source =>
        pureWZ2Prop62LineColor width (residueStrideBase + 1)
          ((schedule.scaleData packetCoordinate).coarse.tube
            ((schedule.scaleData packetCoordinate).cover.parent source)))
      (schedule.upperColorVector
        scheduled rho packetCoordinate)
      weight
  perCell_eq :
    perCell =
      schedule.selectResidueUpperAncestryPerCell
        scheduled rho width packetCoordinate residueStrideBase weight
  activeWeight : Fin fine.card → ENNReal
  activeWeight_eq :
    activeWeight =
      fun source =>
        if source ∈ perCell.selected then weight source else 0
  preliminary :
    PureWZ2Prop62PreliminarySelectionData
      coordinateCount Color color activeWeight
  selected_subset_perCell :
    preliminary.selected ⊆ perCell.selected

theorem pureWZ2_prop62_ancestry_preliminary_selection
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow)
    (scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    {coordinateCount : ℕ}
    (Color : Fin coordinateCount → Type*)
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    (color : ∀ coordinate, Fin fine.card → Color coordinate)
    (weight : Fin fine.card → ENNReal)
    (residueStrideBase : ℕ)
    (activeTotalFinite :
      let perCell :=
        schedule.selectResidueUpperAncestryPerCell
          scheduled rho width packetCoordinate residueStrideBase weight
      let activeWeight :=
        fun source =>
          if source ∈ perCell.selected then weight source else 0
      (∑ source : Fin fine.card, activeWeight source) ≠ ⊤)
    (activeTotalPos :
      let perCell :=
        schedule.selectResidueUpperAncestryPerCell
          scheduled rho width packetCoordinate residueStrideBase weight
      let activeWeight :=
        fun source =>
          if source ∈ perCell.selected then weight source else 0
      0 < ∑ source : Fin fine.card, activeWeight source) :
    Nonempty
      (PureWZ2Prop62AncestryPreliminarySelectionData
        schedule scheduled rho width packetCoordinate
        Color color weight) := by
  let perCell :=
    schedule.selectResidueUpperAncestryPerCell
      scheduled rho width packetCoordinate residueStrideBase weight
  let activeWeight : Fin fine.card → ENNReal :=
    fun source =>
      if source ∈ perCell.selected then weight source else 0
  rcases
      pureWZ2_prop62_preliminary_selection
        coordinateCount Color color activeWeight
        activeTotalFinite activeTotalPos
    with
    ⟨preliminary⟩
  have selectedSubset :
      preliminary.selected ⊆ perCell.selected := by
    intro source sourceMem
    have weightLower :=
      (preliminary.selected_weight_band source sourceMem).1
    have activePositive :
        0 < activeWeight source :=
      preliminary.weightLevel_pos.trans_le weightLower
    by_contra sourceNotMem
    have activeZero : activeWeight source = 0 := by
      simp [activeWeight, sourceNotMem]
    rw [activeZero] at activePositive
    exact (lt_self_iff_false 0).mp activePositive
  exact
    ⟨{
      residueStrideBase := residueStrideBase
      perCell := perCell
      perCell_eq := rfl
      activeWeight := activeWeight
      activeWeight_eq := rfl
      preliminary := preliminary
      selected_subset_perCell := selectedSubset
    }⟩

namespace PureWZ2Prop62AncestryPreliminarySelectionData

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow}
    {scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule}
    {rho width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {coordinateCount : ℕ}
    {Color : Fin coordinateCount → Type*}
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    {color : ∀ coordinate, Fin fine.card → Color coordinate}
    {weight : Fin fine.card → ENNReal}
    (data :
      PureWZ2Prop62AncestryPreliminarySelectionData
        schedule scheduled rho width packetCoordinate
        Color color weight)

theorem perCell_selected_upperAncestry_eq_of_sameCell
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
    (firstSelected : first ∈ data.perCell.selected)
    (secondSelected : second ∈ data.perCell.selected)
    (sameCell :
      schedule.packetLineCell packetCoordinate width first =
        schedule.packetLineCell packetCoordinate width second) :
    schedule.upperAncestry rho packetCoordinate first =
      schedule.upperAncestry rho packetCoordinate second := by
  have firstColor :=
    data.perCell.selected_monochromatic first firstSelected
  have secondColor :=
    data.perCell.selected_monochromatic second secondSelected
  have packetCellEq :
      PureWZ2Prop62PureSchedule.packetCell
          (schedule.packetLineCell packetCoordinate width) first =
        PureWZ2Prop62PureSchedule.packetCell
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

theorem selected_upperAncestry_eq_of_sameCell
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
    (firstMem : first ∈ data.preliminary.selected)
    (secondMem : second ∈ data.preliminary.selected)
    (sameCell :
      schedule.packetLineCell packetCoordinate width first =
        schedule.packetLineCell packetCoordinate width second) :
    schedule.upperAncestry rho packetCoordinate first =
      schedule.upperAncestry rho packetCoordinate second :=
  data.perCell_selected_upperAncestry_eq_of_sameCell
    rhoPos widthPos packetScaleLeRho sixWidthLe parentCovers
    first second
    (data.selected_subset_perCell firstMem)
    (data.selected_subset_perCell secondMem)
    sameCell

theorem selected_sameResidue
    (first second : Fin fine.card)
    (firstMem : first ∈ data.preliminary.selected)
    (secondMem : second ∈ data.preliminary.selected) :
    pureWZ2Prop62LineColor width (data.residueStrideBase + 1)
          ((schedule.scaleData packetCoordinate).coarse.tube
            ((schedule.scaleData packetCoordinate).cover.parent first)) =
      pureWZ2Prop62LineColor width (data.residueStrideBase + 1)
        ((schedule.scaleData packetCoordinate).coarse.tube
          ((schedule.scaleData packetCoordinate).cover.parent second)) := by
  exact
    (data.perCell.selected_residue first
      (data.selected_subset_perCell firstMem)).trans
      (data.perCell.selected_residue second
        (data.selected_subset_perCell secondMem)).symm

theorem selected_completeAncestryLabel_eq_of_sameCell
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
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (first second : Fin fine.card)
    (firstMem : first ∈ data.preliminary.selected)
    (secondMem : second ∈ data.preliminary.selected)
    (sameCell :
      schedule.packetLineCell packetCoordinate width first =
        schedule.packetLineCell packetCoordinate width second) :
    schedule.completeAncestryLabel packetCoordinate
          (schedule.packetLineCell packetCoordinate width) first =
      schedule.completeAncestryLabel packetCoordinate
        (schedule.packetLineCell packetCoordinate width) second := by
  apply Prod.ext
  · apply Subtype.ext
    exact sameCell
  · have upperEq :=
      data.selected_upperAncestry_eq_of_sameCell
        rhoPos widthPos packetScaleLeRho sixWidthLe parentCovers
        first second firstMem secondMem sameCell
    exact
      schedule.ancestry_eq_of_upperAncestry_eq
        rho packetCoordinate allAncestryCoordinatesUpper
        first second upperEq

theorem perCell_mem_iff_of_completeAncestryLabel_eq
    (first second : Fin fine.card)
    (labelEq :
      schedule.completeAncestryLabel packetCoordinate
            (schedule.packetLineCell packetCoordinate width) first =
        schedule.completeAncestryLabel packetCoordinate
          (schedule.packetLineCell packetCoordinate width) second) :
    first ∈ data.perCell.selected ↔
      second ∈ data.perCell.selected := by
  have cellEq :
      PureWZ2Prop62PureSchedule.packetCell
          (schedule.packetLineCell packetCoordinate width) first =
        PureWZ2Prop62PureSchedule.packetCell
          (schedule.packetLineCell packetCoordinate width) second :=
    congrArg Prod.fst labelEq
  have ancestryEq :
      schedule.ancestry packetCoordinate first =
        schedule.ancestry packetCoordinate second :=
    congrArg Prod.snd labelEq
  have colorEq :
      schedule.upperColorVector scheduled rho packetCoordinate first =
        schedule.upperColorVector scheduled rho packetCoordinate second := by
    funext coordinate
    unfold PureWZ2Prop62PureSchedule.upperColorVector
    unfold PureWZ2Prop62ScheduledParentColoringData.leafColor
    congr 1
    let ancestryCoordinate :
        schedule.AncestryCoordinate packetCoordinate :=
      ⟨coordinate.1.1, coordinate.2.2⟩
    exact congrFun ancestryEq ancestryCoordinate
  have residueEq :
      pureWZ2Prop62LineColor width (data.residueStrideBase + 1)
            ((schedule.scaleData packetCoordinate).coarse.tube
              ((schedule.scaleData packetCoordinate).cover.parent first)) =
        pureWZ2Prop62LineColor width (data.residueStrideBase + 1)
          ((schedule.scaleData packetCoordinate).coarse.tube
            ((schedule.scaleData packetCoordinate).cover.parent second)) := by
    have rawCellEq := congrArg Subtype.val cellEq
    unfold pureWZ2Prop62LineColor
    funext coordinate
    exact congrArg
      (fun value : ℤ => (value : ZMod (data.residueStrideBase + 1)))
      (congrFun rawCellEq coordinate)
  rw [data.perCell.selected_eq]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [residueEq, cellEq, colorEq]

end PureWZ2Prop62AncestryPreliminarySelectionData

end Kakeya.Assouad

end
