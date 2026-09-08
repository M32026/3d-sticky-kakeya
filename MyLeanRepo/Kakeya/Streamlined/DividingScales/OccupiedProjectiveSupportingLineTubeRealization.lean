import MyLeanRepo.Kakeya.Streamlined.DividingScales.ProjectiveSupportingLineCellGeometry

/-!
# Realizing occupied supporting-line labels

At one grid level, choose one actual tube for each occupied supporting-line
label and reuse its axis at a prescribed radius `rho`.

When `mesh ≤ rho`, this gives a surjective

`LocalDilatedTubeCover 31 21`

of the original unit-ball family.  The construction is quotient-faithful:
axial endpoint position is never required to be close.
-/

noncomputable section

namespace Kakeya.Streamlined

open GeometricLemmas

/-- Occupied supporting-line labels at one grid level. -/
abbrev OccupiedProjectiveSupportingLineLabel
    {delta : ℝ}
    (family : TubeFamily delta)
    (base level : ℕ) :=
  OccupiedIntegerGridLabel
    (tubeFamilyProjectiveSupportingLineCoordinates family)
    base level

/-- Canonical finite enumeration of occupied supporting-line labels. -/
def occupiedProjectiveSupportingLineLabelEquiv
    {delta : ℝ}
    (family : TubeFamily delta)
    (base level : ℕ) :
    OccupiedProjectiveSupportingLineLabel family base level ≃
      Fin (Fintype.card
        (OccupiedProjectiveSupportingLineLabel family base level)) :=
  Fintype.equivFin _

/-- One actual original tube occupying a prescribed line label. -/
def occupiedProjectiveSupportingLineRepresentative
    {delta : ℝ}
    (family : TubeFamily delta)
    (base level : ℕ)
    (parent : OccupiedProjectiveSupportingLineLabel family base level) :
    Fin family.card :=
  occupiedIntegerGridRepresentative
    (tubeFamilyProjectiveSupportingLineCoordinates family)
    base level parent

/-- The selected representative occupies exactly its prescribed label. -/
theorem tubeProjectiveSupportingLineGridParent_representative
    {delta : ℝ}
    (family : TubeFamily delta)
    (base level : ℕ)
    (parent : OccupiedProjectiveSupportingLineLabel family base level) :
    tubeProjectiveSupportingLineGridParent family base level
        (occupiedProjectiveSupportingLineRepresentative
          family base level parent) =
      parent := by
  exact occupiedIntegerGridParent_representative
    (tubeFamilyProjectiveSupportingLineCoordinates family)
    base level parent

/-- One radius-`rho` tube for every occupied supporting-line label. -/
def occupiedProjectiveSupportingLineRepresentativeFamily
    {delta rho : ℝ}
    (family : TubeFamily delta)
    (base level : ℕ) :
    TubeFamily rho where
  card :=
    Fintype.card
      (OccupiedProjectiveSupportingLineLabel family base level)
  tube parentIndex :=
    let parent :=
      (occupiedProjectiveSupportingLineLabelEquiv
        family base level).symm parentIndex
    withRadius rho
      (family.tube
        (occupiedProjectiveSupportingLineRepresentative
          family base level parent))

/-- Realized parent index of one original tube. -/
def occupiedProjectiveSupportingLineRealizedParent
    {delta rho : ℝ}
    (family : TubeFamily delta)
    (base level : ℕ)
    (index : Fin family.card) :
    Fin
      (occupiedProjectiveSupportingLineRepresentativeFamily
        (rho := rho) family base level).card :=
  occupiedProjectiveSupportingLineLabelEquiv family base level
    (tubeProjectiveSupportingLineGridParent
      family base level index)

/-- Every realized supporting-line parent is used. -/
theorem occupiedProjectiveSupportingLineRealizedParent_surjective
    {delta rho : ℝ}
    (family : TubeFamily delta)
    (base level : ℕ) :
    Function.Surjective
      (occupiedProjectiveSupportingLineRealizedParent
        (rho := rho) family base level) := by
  exact
    (occupiedProjectiveSupportingLineLabelEquiv
      family base level).surjective.comp
      (occupiedIntegerGridParent_surjective
        (tubeFamilyProjectiveSupportingLineCoordinates family)
        base level)

/-- A child and the chosen representative of its parent have the same label. -/
theorem original_and_supportingLineRepresentative_label_eq
    {delta : ℝ}
    (family : TubeFamily delta)
    (base level : ℕ)
    (index : Fin family.card) :
    let parent :=
      tubeProjectiveSupportingLineGridParent
        family base level index
    integerGridLabel base level
        (projectiveSupportingLineCoordinates
          (family.tube index)) =
      integerGridLabel base level
        (projectiveSupportingLineCoordinates
          (family.tube
            (occupiedProjectiveSupportingLineRepresentative
              family base level parent))) := by
  dsimp only
  have hrepresentative :=
    tubeProjectiveSupportingLineGridParent_representative
      family base level
      (tubeProjectiveSupportingLineGridParent
        family base level index)
  exact congrArg Subtype.val hrepresentative.symm

/--
The integer grid label of one realized parent is exactly the occupied label
represented by its index.
-/
theorem occupiedProjectiveSupportingLineRepresentativeFamily_gridLabel
    {delta rho : ℝ}
    (family : TubeFamily delta)
    (base level : ℕ)
    (parentIndex :
      Fin
        (occupiedProjectiveSupportingLineRepresentativeFamily
          (rho := rho) family base level).card) :
    integerGridLabel base level
        (projectiveSupportingLineCoordinates
          ((occupiedProjectiveSupportingLineRepresentativeFamily
            (rho := rho) family base level).tube parentIndex)) =
      ((occupiedProjectiveSupportingLineLabelEquiv
        family base level).symm parentIndex).val := by
  let parent :=
    (occupiedProjectiveSupportingLineLabelEquiv
      family base level).symm parentIndex
  have hrepresentative :=
    tubeProjectiveSupportingLineGridParent_representative
      family base level parent
  change
    integerGridLabel base level
        (projectiveSupportingLineCoordinates
          (withRadius rho
            (family.tube
              (occupiedProjectiveSupportingLineRepresentative
                family base level parent)))) =
      parent.val
  rw [projectiveSupportingLineCoordinates_withRadius]
  exact congrArg Subtype.val hrepresentative

/-- Realized parent indices have injective integer grid labels. -/
theorem occupiedProjectiveSupportingLineRepresentativeFamily_gridLabel_injective
    {delta rho : ℝ}
    (family : TubeFamily delta)
    (base level : ℕ) :
    Function.Injective fun parentIndex :
        Fin
          (occupiedProjectiveSupportingLineRepresentativeFamily
            (rho := rho) family base level).card =>
      integerGridLabel base level
        (projectiveSupportingLineCoordinates
          ((occupiedProjectiveSupportingLineRepresentativeFamily
            (rho := rho) family base level).tube parentIndex)) := by
  intro first second hlabel
  have hfirst :=
    occupiedProjectiveSupportingLineRepresentativeFamily_gridLabel
      family base level first
  have hsecond :=
    occupiedProjectiveSupportingLineRepresentativeFamily_gridLabel
      family base level second
  apply
    (occupiedProjectiveSupportingLineLabelEquiv
      family base level).symm.injective
  apply Subtype.ext
  rw [← hfirst, ← hsecond]
  exact hlabel

/-- Every realized parent keeps the midpoint of an actual unit-ball tube. -/
theorem occupiedProjectiveSupportingLineRepresentativeFamily_midpoint_norm_le_one
    {delta rho : ℝ}
    (family : TubeFamily delta)
    (hfamilyBall : family.IsInUnitBall)
    (base level : ℕ)
    (parentIndex :
      Fin
        (occupiedProjectiveSupportingLineRepresentativeFamily
          (rho := rho) family base level).card) :
    ‖tubeMidpoint
        ((occupiedProjectiveSupportingLineRepresentativeFamily
          (rho := rho) family base level).tube parentIndex)‖ ≤ 1 := by
  let parent :=
    (occupiedProjectiveSupportingLineLabelEquiv
      family base level).symm parentIndex
  change
    ‖tubeMidpoint
        (withRadius rho
          (family.tube
            (occupiedProjectiveSupportingLineRepresentative
              family base level parent)))‖ ≤ 1
  rw [withRadius_midpoint]
  exact
    tubeMidpoint_norm_le_one
      (hfamilyBall
        (occupiedProjectiveSupportingLineRepresentative
          family base level parent))

/--
Occupied supporting-line representatives give a surjective local-dilated
cover whenever the grid mesh is at most the requested parent radius.
-/
def occupiedProjectiveSupportingLineLocalCover
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    (family : TubeFamily delta)
    (hfamilyBall : family.IsInUnitBall)
    (base level : ℕ)
    (hbase : 1 ≤ base)
    (hmeshRho : (base ^ level : ℝ)⁻¹ ≤ rho) :
    LocalDilatedTubeCover 31 21 family
      (occupiedProjectiveSupportingLineRepresentativeFamily
        (rho := rho) family base level) where
  parent :=
    occupiedProjectiveSupportingLineRealizedParent
      (rho := rho) family base level
  parent_surjective :=
    occupiedProjectiveSupportingLineRealizedParent_surjective
      (rho := rho) family base level
  nested index := by
    let parentLabel :=
      tubeProjectiveSupportingLineGridParent
        family base level index
    let representativeIndex :=
      occupiedProjectiveSupportingLineRepresentative
        family base level parentLabel
    have hlabel :
        integerGridLabel base level
            (projectiveSupportingLineCoordinates
              (family.tube index)) =
          integerGridLabel base level
            (projectiveSupportingLineCoordinates
              (family.tube representativeIndex)) := by
      dsimp only [representativeIndex, parentLabel]
      exact original_and_supportingLineRepresentative_label_eq
        family base level index
    have hcontained :=
      carrier_subset_dilated_of_supportingLineGridLabel_eq
        hdelta.le hrho hrhoOne hdeltaRho hbase hmeshRho
        (hfamilyBall index) (hfamilyBall representativeIndex)
        hlabel
    simpa only [
      occupiedProjectiveSupportingLineRepresentativeFamily,
      occupiedProjectiveSupportingLineRealizedParent,
      occupiedProjectiveSupportingLineLabelEquiv,
      Equiv.symm_apply_apply,
      representativeIndex,
      parentLabel] using hcontained
  transverse_midpoint_close index := by
    let parentLabel :=
      tubeProjectiveSupportingLineGridParent
        family base level index
    let representativeIndex :=
      occupiedProjectiveSupportingLineRepresentative
        family base level parentLabel
    have hlabel :
        integerGridLabel base level
            (projectiveSupportingLineCoordinates
              (family.tube index)) =
          integerGridLabel base level
            (projectiveSupportingLineCoordinates
              (family.tube representativeIndex)) := by
      dsimp only [representativeIndex, parentLabel]
      exact original_and_supportingLineRepresentative_label_eq
        family base level index
    have hbound :=
      supportingLine_sameCell_transverseMidpoint_le_unoriented
        hbase
        (tubeMidpoint_norm_le_one (hfamilyBall index))
        hlabel
    have hboundRho :
        21 * (base ^ level : ℝ)⁻¹ ≤ 21 * rho :=
      mul_le_mul_of_nonneg_left hmeshRho (by norm_num)
    have hfinal := hbound.trans hboundRho
    simpa only [
      occupiedProjectiveSupportingLineRepresentativeFamily,
      occupiedProjectiveSupportingLineRealizedParent,
      occupiedProjectiveSupportingLineLabelEquiv,
      Equiv.symm_apply_apply,
      withRadius_midpoint,
      withRadius_direction,
      representativeIndex,
      parentLabel] using hfinal
  direction_close_or_reverse index := by
    let parentLabel :=
      tubeProjectiveSupportingLineGridParent
        family base level index
    let representativeIndex :=
      occupiedProjectiveSupportingLineRepresentative
        family base level parentLabel
    have hlabel :
        integerGridLabel base level
            (projectiveSupportingLineCoordinates
              (family.tube index)) =
          integerGridLabel base level
            (projectiveSupportingLineCoordinates
              (family.tube representativeIndex)) := by
      dsimp only [representativeIndex, parentLabel]
      exact original_and_supportingLineRepresentative_label_eq
        family base level index
    have hbound :=
      supportingLine_sameCell_direction_close_or_reverse
        hbase hlabel
    have hboundRho :
        18 * (base ^ level : ℝ)⁻¹ ≤ 21 * rho := by
      have hnonneg : 0 ≤ (base ^ level : ℝ)⁻¹ := by positivity
      nlinarith
    rcases hbound with hsame | hopposite
    · left
      have hfinal := hsame.trans hboundRho
      simpa only [
        occupiedProjectiveSupportingLineRepresentativeFamily,
        occupiedProjectiveSupportingLineRealizedParent,
        occupiedProjectiveSupportingLineLabelEquiv,
        Equiv.symm_apply_apply,
        withRadius_direction,
        representativeIndex,
        parentLabel] using hfinal
    · right
      have hfinal := hopposite.trans hboundRho
      simpa only [
        occupiedProjectiveSupportingLineRepresentativeFamily,
        occupiedProjectiveSupportingLineRealizedParent,
        occupiedProjectiveSupportingLineLabelEquiv,
        Equiv.symm_apply_apply,
        withRadius_direction,
        representativeIndex,
        parentLabel] using hfinal

end Kakeya.Streamlined
