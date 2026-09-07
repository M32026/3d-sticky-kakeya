import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PerCellColorSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AuxiliaryTreeCore

/-!
# Proposition 6.2: the complete-ancestry auxiliary tree level

A metric cell alone need not be laminar with every old level.  The paper first
splits that cell by the complete old ancestry vector above the selected
`s`-packet level.  The pair `(cell, ancestry)` is then a genuine auxiliary node:
it refines the immediately preceding old level, while an `s`-packet determines
both its cell and all of its older ancestors.
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

/-- Old coordinates strictly above the selected packet coordinate. -/
abbrev AncestryCoordinate
    (packetCoordinate : Fin schedule.levelCount) :=
  Fin packetCoordinate.1

/-- Embed one ancestry coordinate into the full old schedule. -/
def ancestryAmbientCoordinate
    (packetCoordinate : Fin schedule.levelCount)
    (coordinate : schedule.AncestryCoordinate packetCoordinate) :
    Fin schedule.levelCount :=
  ⟨coordinate.1, coordinate.2.trans packetCoordinate.2⟩

/-- The exact vector of old strict parents above the selected packet level. -/
abbrev Ancestry
    (packetCoordinate : Fin schedule.levelCount) :=
  ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
    Fin
      (schedule.scaleData
        (schedule.ancestryAmbientCoordinate
          packetCoordinate coordinate)).coarse.card

/-- Exact old ancestry of one ambient fine leaf. -/
def ancestry
    (packetCoordinate : Fin schedule.levelCount)
    (source : Fin fine.card) :
    schedule.Ancestry packetCoordinate :=
  fun coordinate =>
    (schedule.scaleData
      (schedule.ancestryAmbientCoordinate
        packetCoordinate coordinate)).cover.parent source

/-- Finite image of any packet-cell label on the ambient fine family. -/
def packetCells
    {RawCell : Type}
    [DecidableEq RawCell]
    (rawCell : Fin fine.card → RawCell) :
    Finset RawCell :=
  Finset.image rawCell Finset.univ

/-- The occupied packet cells, represented as a finite subtype. -/
abbrev PacketCell
    {RawCell : Type}
    [DecidableEq RawCell]
    (rawCell : Fin fine.card → RawCell) :=
  {cell // cell ∈ packetCells rawCell}

/-- Canonical occupied-cell label of one fine leaf. -/
def packetCell
    {RawCell : Type}
    [DecidableEq RawCell]
    (rawCell : Fin fine.card → RawCell)
    (source : Fin fine.card) :
    PacketCell rawCell :=
  ⟨rawCell source,
    Finset.mem_image.mpr
      ⟨source, Finset.mem_univ source, rfl⟩⟩

/-- The auxiliary label used by the one final ambient-tree cleanup. -/
abbrev CompleteAncestryLabel
    {RawCell : Type}
    [DecidableEq RawCell]
    (packetCoordinate : Fin schedule.levelCount)
    (rawCell : Fin fine.card → RawCell) :=
  PacketCell rawCell × schedule.Ancestry packetCoordinate

/-- Pair the occupied cell with the complete old ancestry vector. -/
def completeAncestryLabel
    {RawCell : Type}
    [DecidableEq RawCell]
    (packetCoordinate : Fin schedule.levelCount)
    (rawCell : Fin fine.card → RawCell)
    (source : Fin fine.card) :
    schedule.CompleteAncestryLabel packetCoordinate rawCell :=
  ⟨packetCell rawCell source,
    schedule.ancestry packetCoordinate source⟩

private theorem nodeAt_eq_of_parent_eq
    (coordinate : Fin schedule.levelCount)
    (first second : Fin fine.card)
    (parentEq :
      (schedule.scaleData coordinate).cover.parent first =
        (schedule.scaleData coordinate).cover.parent second) :
    schedule.nodeAt (coordinate.1 + 1) first =
      schedule.nodeAt (coordinate.1 + 1) second := by
  rw [schedule.nodeAt_succ coordinate.2,
    schedule.nodeAt_succ coordinate.2]
  ext source
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [parentEq]

private theorem parent_eq_of_nodeAt_eq
    (coordinate : Fin schedule.levelCount)
    (first second : Fin fine.card)
    (nodeEq :
      schedule.nodeAt (coordinate.1 + 1) first =
        schedule.nodeAt (coordinate.1 + 1) second) :
    (schedule.scaleData coordinate).cover.parent first =
      (schedule.scaleData coordinate).cover.parent second := by
  have firstMem :
      first ∈ schedule.nodeAt (coordinate.1 + 1) first := by
    rw [schedule.nodeAt_succ coordinate.2]
    simp
  rw [nodeEq] at firstMem
  simpa only [schedule.nodeAt_succ coordinate.2,
    Finset.mem_filter, Finset.mem_univ, true_and] using firstMem

/--
The complete ancestry label is a genuine laminar level immediately before the
selected packet coordinate.
-/
noncomputable def completeAncestryAuxiliaryLevel
    {RawCell : Type}
    [DecidableEq RawCell]
    (packetCoordinate : Fin schedule.levelCount)
    (rawCell : Fin fine.card → RawCell)
    (cell_parent_invariant :
      ∀ first second,
        (schedule.scaleData packetCoordinate).cover.parent first =
            (schedule.scaleData packetCoordinate).cover.parent second →
          rawCell first = rawCell second) :
    PureWZ2Prop62AuxiliaryLevel
      schedule
      (schedule.CompleteAncestryLabel packetCoordinate rawCell) where
  insertionLevel := packetCoordinate.1
  insertion_lt := packetCoordinate.2
  label := schedule.completeAncestryLabel packetCoordinate rawCell
  label_refines_previous := by
    intro first second labelEq
    by_cases packetZero : packetCoordinate.1 = 0
    · rw [packetZero]
      simp
    · let previousLevel := packetCoordinate.1 - 1
      have previousSucc : previousLevel + 1 = packetCoordinate.1 := by
        dsimp only [previousLevel]
        omega
      let previousCoordinate :
          schedule.AncestryCoordinate packetCoordinate :=
        ⟨previousLevel, by
          dsimp only [previousLevel]
          omega⟩
      have ancestryEq :
          schedule.ancestry packetCoordinate first =
            schedule.ancestry packetCoordinate second :=
        congrArg Prod.snd labelEq
      have parentEq :
          (schedule.scaleData
            (schedule.ancestryAmbientCoordinate
              packetCoordinate previousCoordinate)).cover.parent first =
          (schedule.scaleData
            (schedule.ancestryAmbientCoordinate
              packetCoordinate previousCoordinate)).cover.parent second :=
        congrFun ancestryEq previousCoordinate
      have coordinateVal :
          (schedule.ancestryAmbientCoordinate
            packetCoordinate previousCoordinate).1 + 1 =
              packetCoordinate.1 := by
        exact previousSucc
      rw [← coordinateVal]
      exact
        schedule.nodeAt_eq_of_parent_eq
          (schedule.ancestryAmbientCoordinate
            packetCoordinate previousCoordinate)
          first second parentEq
  next_refines_label := by
    intro first second nodeEq
    have packetParentEq :
        (schedule.scaleData packetCoordinate).cover.parent first =
          (schedule.scaleData packetCoordinate).cover.parent second :=
      schedule.parent_eq_of_nodeAt_eq
        packetCoordinate first second nodeEq
    have cellEq :
        packetCell rawCell first =
          packetCell rawCell second := by
      apply Subtype.ext
      exact cell_parent_invariant first second packetParentEq
    have ancestryEq :
        schedule.ancestry packetCoordinate first =
          schedule.ancestry packetCoordinate second := by
      funext coordinate
      exact
        schedule.parent_eq_of_coordinate_le
          (schedule.ancestryAmbientCoordinate
            packetCoordinate coordinate)
          packetCoordinate
          (by
            change coordinate.1 ≤ packetCoordinate.1
            omega)
          first second packetParentEq
    exact Prod.ext cellEq ancestryEq

end PureWZ2Prop62PureSchedule

end Kakeya.Assouad

end
