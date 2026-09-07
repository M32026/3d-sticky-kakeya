import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62UpperAncestryCellSelection

/-!
# Proposition 6.2: one global residue and one color per cell

The metric-parent construction first keeps one global mesh residue class.
Inside that class it then chooses one ancestry color independently in every
occupied metric cell.  The total loss is the product of the two finite color
cardinalities.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62GlobalResiduePerCellSelectionData
    (Index Cell Residue Color : Type*)
    [Fintype Index] [DecidableEq Index]
    [Fintype Cell] [DecidableEq Cell]
    [Fintype Residue] [DecidableEq Residue] [Nonempty Residue]
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    (cell : Index → Cell)
    (residue : Index → Residue)
    (color : Index → Color)
    (weight : Index → ENNReal) where
  selectedResidue : Residue
  selectedColor : Cell → Color
  selected : Finset Index
  selected_eq :
    selected =
      Finset.univ.filter fun index =>
        residue index = selectedResidue ∧
          color index = selectedColor (cell index)
  selected_residue :
    ∀ index ∈ selected,
      residue index = selectedResidue
  selected_monochromatic :
    ∀ index ∈ selected,
      color index = selectedColor (cell index)
  weight_retention :
    (∑ index : Index, weight index) ≤
      (Fintype.card Residue : ENNReal) *
        (Fintype.card Color : ENNReal) *
          ∑ index ∈ selected, weight index

theorem pureWZ2_prop62_globalResidue_perCell_color_selection
    (Index Cell Residue Color : Type*)
    [Fintype Index] [DecidableEq Index]
    [Fintype Cell] [DecidableEq Cell]
    [Fintype Residue] [DecidableEq Residue] [Nonempty Residue]
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    (cell : Index → Cell)
    (residue : Index → Residue)
    (color : Index → Color)
    (weight : Index → ENNReal) :
    Nonempty
      (PureWZ2Prop62GlobalResiduePerCellSelectionData
        Index Cell Residue Color cell residue color weight) := by
  let residueStage :=
    Classical.choice <|
      pureWZ2_prop62_perCell_color_selection
        Index Unit Residue
        (fun _ => ()) residue weight
  let selectedResidue : Residue :=
    residueStage.selectedColor ()
  let residueWeight : Index → ENNReal :=
    fun index =>
      if index ∈ residueStage.selected then weight index else 0
  let cellStage :=
    Classical.choice <|
      pureWZ2_prop62_perCell_color_selection
        Index Cell Color cell color residueWeight
  let selected : Finset Index :=
    cellStage.selected.filter fun index =>
      index ∈ residueStage.selected
  have residueStageEq :
      residueStage.selected =
        Finset.univ.filter fun index =>
          residue index = selectedResidue := by
    rw [residueStage.selected_eq]
  have selectedEq :
      selected =
        Finset.univ.filter fun index =>
          residue index = selectedResidue ∧
            color index = cellStage.selectedColor (cell index) := by
    ext index
    simp only [selected, Finset.mem_filter]
    rw [cellStage.selected_eq, residueStageEq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have residueSumEq :
      (∑ index ∈ residueStage.selected, weight index) =
        ∑ index : Index, residueWeight index := by
    rw [show
      (∑ index : Index, residueWeight index) =
        ∑ index ∈ residueStage.selected, weight index by
      unfold residueWeight
      calc
        (∑ index : Index,
            if index ∈ residueStage.selected then weight index else 0) =
            ∑ index ∈
                (Finset.univ.filter fun index =>
                  index ∈ residueStage.selected),
              weight index := by
          exact
            (Finset.sum_filter
              (s := (Finset.univ : Finset Index))
              (p := fun index => index ∈ residueStage.selected)
              (f := weight)).symm
        _ = ∑ index ∈ residueStage.selected, weight index := by
          congr 1
          ext index
          simp]
  have selectedSumEq :
      (∑ index ∈ cellStage.selected, residueWeight index) =
        ∑ index ∈ selected, weight index := by
    unfold residueWeight selected
    calc
      (∑ index ∈ cellStage.selected,
          if index ∈ residueStage.selected then weight index else 0) =
          ∑ index ∈
              (cellStage.selected.filter fun index =>
                index ∈ residueStage.selected),
            weight index := by
        exact
          (Finset.sum_filter
            (s := cellStage.selected)
            (p := fun index => index ∈ residueStage.selected)
            (f := weight)).symm
      _ = _ := rfl
  have retention :
      (∑ index : Index, weight index) ≤
        (Fintype.card Residue : ENNReal) *
          (Fintype.card Color : ENNReal) *
            ∑ index ∈ selected, weight index := by
    calc
      (∑ index : Index, weight index) ≤
          (Fintype.card Residue : ENNReal) *
            ∑ index ∈ residueStage.selected, weight index :=
        residueStage.weight_retention
      _ =
          (Fintype.card Residue : ENNReal) *
            ∑ index : Index, residueWeight index := by
        rw [residueSumEq]
      _ ≤
          (Fintype.card Residue : ENNReal) *
            ((Fintype.card Color : ENNReal) *
              ∑ index ∈ cellStage.selected, residueWeight index) := by
        gcongr
        exact cellStage.weight_retention
      _ =
          (Fintype.card Residue : ENNReal) *
            (Fintype.card Color : ENNReal) *
              ∑ index ∈ selected, weight index := by
        rw [selectedSumEq]
        ring
  exact
    ⟨{
      selectedResidue := selectedResidue
      selectedColor := cellStage.selectedColor
      selected := selected
      selected_eq := selectedEq
      selected_residue := by
        intro index indexMem
        rw [selectedEq] at indexMem
        exact (Finset.mem_filter.mp indexMem).2.1
      selected_monochromatic := by
        intro index indexMem
        rw [selectedEq] at indexMem
        exact (Finset.mem_filter.mp indexMem).2.2
      weight_retention := retention
    }⟩

namespace PureWZ2Prop62PureSchedule

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow)

/--
The paper's combined preliminary stage: one global residue of the old
`s`-parents, followed by one upper-ancestry color in every occupied metric
cell.
-/
noncomputable def selectResidueUpperAncestryPerCell
    (scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal) :
    PureWZ2Prop62GlobalResiduePerCellSelectionData
      (Fin fine.card)
      (PureWZ2Prop62PureSchedule.PacketCell
        (schedule.packetLineCell packetCoordinate width))
      (Fin 4 → ZMod (strideBase + 1))
      (schedule.UpperColorVector rho packetCoordinate)
      (PureWZ2Prop62PureSchedule.packetCell
        (schedule.packetLineCell packetCoordinate width))
      (fun source =>
        pureWZ2Prop62LineColor width (strideBase + 1)
          ((schedule.scaleData packetCoordinate).coarse.tube
            ((schedule.scaleData packetCoordinate).cover.parent source)))
      (schedule.upperColorVector
        scheduled rho packetCoordinate)
      weight :=
  Classical.choice <|
    pureWZ2_prop62_globalResidue_perCell_color_selection
      (Fin fine.card)
      (PureWZ2Prop62PureSchedule.PacketCell
        (schedule.packetLineCell packetCoordinate width))
      (Fin 4 → ZMod (strideBase + 1))
      (schedule.UpperColorVector rho packetCoordinate)
      (PureWZ2Prop62PureSchedule.packetCell
        (schedule.packetLineCell packetCoordinate width))
      (fun source =>
        pureWZ2Prop62LineColor width (strideBase + 1)
          ((schedule.scaleData packetCoordinate).coarse.tube
            ((schedule.scaleData packetCoordinate).cover.parent source)))
      (schedule.upperColorVector
        scheduled rho packetCoordinate)
      weight

end PureWZ2Prop62PureSchedule

end Kakeya.Assouad

end
