import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationRaceBlocker
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGridCubeVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements

/-!
# Top-level assembly for frozen pure WZ2 normalization

This module separates the mechanical part of the frozen normalization record
from its genuine mathematical inputs.

The cropped shading is defined canonically by `pureWZ2DenseCubicalization`.
Its measurability, containment, carrier identity, and cubicality are proved
here, so they are not repeated as producer premises.  The remaining
source-local witness records exactly the ordinary retained selection, affine
family geometry, line class, top-level Convex-Wolff bound, and final cropped
extremality.

Three quantifier-correct routes then close
`PureWZ2CroppedCriticalNormalizationAt`:

* a source-uniform producer;
* a producer for axis-box-localized critical sources, together with the
  corresponding localized critical sequence;
* a derived-localization producer which may replace a stronger-loss source
  by a new extremal configuration at the normalization input loss.

No locality assumption is inferred from the frozen critical package.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-! ## Canonical dense cropped shading -/

/--
The dense cubicalization is a union of whole paper grid cells.
-/
theorem pureWZ2DenseCubicalization_cubical_topLevel
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta)
    (source : Set Point3) :
    ∀ point : Point3,
      point ∈ pureWZ2DenseCubicalization tube source →
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          pureWZ2DenseCubicalization tube source := by
  intro point pointMem other otherMem
  have indexEq :
      wz1PaperGridIndex delta other =
        wz1PaperGridIndex delta point :=
    (mem_wz1PaperGridCube
      delta (wz1PaperGridIndex delta point) other).mp otherMem
  simpa [pureWZ2DenseCubicalization, indexEq] using pointMem

/--
The dense cubicalization is a countable union of measurable paper grid cells.
-/
theorem pureWZ2DenseCubicalization_measurable_topLevel
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta)
    (source : Set Point3) :
    MeasurableSet (pureWZ2DenseCubicalization tube source) := by
  let selectedCell : (ℤ × ℤ × ℤ) → Prop := fun cell =>
    wz1PaperGridCube delta cell ⊆ wz1PaperTubeCarrier tube ∧
      (100 : ENNReal)⁻¹ *
            volume source *
            (volume tube.carrier)⁻¹ *
            volume (wz1PaperGridCube delta cell) ≤
        volume (source ∩ wz1PaperGridCube delta cell)
  have carrierEq :
      pureWZ2DenseCubicalization tube source =
        ⋃ cell : ℤ × ℤ × ℤ,
          if selectedCell cell then
            wz1PaperGridCube delta cell
          else
            (∅ : Set Point3) := by
    ext point
    simp only [
      pureWZ2DenseCubicalization, Set.mem_iUnion,
      Set.mem_setOf_eq
    ]
    constructor
    · intro pointMem
      refine ⟨wz1PaperGridIndex delta point, ?_⟩
      have pointCell :
          point ∈
            wz1PaperGridCube delta
              (wz1PaperGridIndex delta point) :=
        (mem_wz1PaperGridCube
          delta (wz1PaperGridIndex delta point) point).mpr rfl
      simpa [selectedCell, pointCell] using pointMem
    · rintro ⟨cell, pointMem⟩
      by_cases cellSelected : selectedCell cell
      · rw [if_pos cellSelected] at pointMem
        have indexEq :
            wz1PaperGridIndex delta point = cell :=
          (mem_wz1PaperGridCube delta cell point).mp pointMem
        rwa [indexEq]
      · rw [if_neg cellSelected] at pointMem
        simpa using pointMem
  rw [carrierEq]
  exact MeasurableSet.iUnion fun cell => by
    by_cases cellSelected : selectedCell cell
    · rw [if_pos cellSelected]
      exact wz1PaperGridCube_measurable cell
    · rw [if_neg cellSelected]
      exact MeasurableSet.empty

/--
Every selected dense grid cell lies in the paper tube carrier by definition.
-/
theorem pureWZ2DenseCubicalization_subset_paperCarrier_topLevel
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta)
    (source : Set Point3) :
    pureWZ2DenseCubicalization tube source ⊆
      wz1PaperTubeCarrier tube := by
  intro point pointMem
  exact
    pointMem.1
      ((mem_wz1PaperGridCube
        delta (wz1PaperGridIndex delta point) point).mpr rfl)

/--
The canonical cropped shading associated to an ordinary shading, an affine
isometry, and an index equivalence.
-/
noncomputable def pureWZ2NormalizationCroppedShading
    {delta : ℝ}
    {ordinaryFamily croppedFamily :
      Kakeya.Streamlined.TubeFamily delta}
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (indexEquiv : Fin ordinaryFamily.card ≃ Fin croppedFamily.card)
    (ordinaryRefined :
      Kakeya.Streamlined.TubeShading ordinaryFamily) :
    WZ1PaperTubeShading croppedFamily where
  carrier index :=
    pureWZ2DenseCubicalization
      (croppedFamily.tube index)
      (frame ''
        ordinaryRefined.carrier (indexEquiv.symm index))
  measurable_carrier index :=
    pureWZ2DenseCubicalization_measurable_topLevel
      (croppedFamily.tube index)
      (frame ''
        ordinaryRefined.carrier (indexEquiv.symm index))
  subset_body index :=
    pureWZ2DenseCubicalization_subset_paperCarrier_topLevel
      (croppedFamily.tube index)
      (frame ''
        ordinaryRefined.carrier (indexEquiv.symm index))

@[simp]
theorem pureWZ2NormalizationCroppedShading_carrier
    {delta : ℝ}
    {ordinaryFamily croppedFamily :
      Kakeya.Streamlined.TubeFamily delta}
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (indexEquiv : Fin ordinaryFamily.card ≃ Fin croppedFamily.card)
    (ordinaryRefined :
      Kakeya.Streamlined.TubeShading ordinaryFamily)
    (index : Fin ordinaryFamily.card) :
    (pureWZ2NormalizationCroppedShading
      frame indexEquiv ordinaryRefined).carrier
        (indexEquiv index) =
      pureWZ2DenseCubicalization
        (croppedFamily.tube (indexEquiv index))
        (frame '' ordinaryRefined.carrier index) := by
  simp [pureWZ2NormalizationCroppedShading]

theorem pureWZ2NormalizationCroppedShading_cubical
    {delta : ℝ}
    {ordinaryFamily croppedFamily :
      Kakeya.Streamlined.TubeFamily delta}
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (indexEquiv : Fin ordinaryFamily.card ≃ Fin croppedFamily.card)
    (ordinaryRefined :
      Kakeya.Streamlined.TubeShading ordinaryFamily) :
    WZ1PaperIsCubicalShading
      (pureWZ2NormalizationCroppedShading
        frame indexEquiv ordinaryRefined) := by
  intro index point pointMem
  exact
    pureWZ2DenseCubicalization_cubical_topLevel
      (croppedFamily.tube index)
      (frame ''
        ordinaryRefined.carrier (indexEquiv.symm index))
      point pointMem

/-! ## Source-local mathematical witness -/

/--
The exact non-mechanical inputs needed to build one frozen normalization
record for a fixed source extremal configuration.

The cropped shading itself and its three structural fields are deliberately
absent: they are generated canonically above.  Thus this structure isolates
the remaining mathematical work without changing the frozen API.
-/
structure PureWZ2CroppedCriticalNormalizationSourceLeaves
    {sigma inputLoss outputLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma inputLoss delta)
    (normalizationExponent : ℕ) where
  input_loss_le_half : inputLoss ≤ outputLoss / 2
  selected : Kakeya.Streamlined.TubeSubfamily source.family
  selected_nonempty : selected.family.Nonempty
  ordinaryRefined :
    Kakeya.Streamlined.TubeShading selected.family
  ordinary_subshading :
    ∀ index,
      ordinaryRefined.carrier index ⊆
        source.shading.carrier (selected.embedding index)
  retained_mass :
    wz2PaperPureRefinementFraction delta normalizationExponent *
        source.shading.mass ≤
      ordinaryRefined.mass
  frame : Point3 ≃ᵃⁱ[ℝ] Point3
  croppedFamily : Kakeya.Streamlined.TubeFamily delta
  indexEquiv :
    Fin selected.family.card ≃ Fin croppedFamily.card
  ordinary_carrier_image_eq :
    ∀ index,
      (croppedFamily.tube (indexEquiv index)).carrier =
        frame '' (selected.family.tube index).carrier
  ordinary_per_tube :
    ∀ index,
      (Kakeya.realRpowENN delta inputLoss / 2) *
            volume (selected.family.tube index).carrier ≤
        volume (ordinaryRefined.carrier index)
  ordinary_axial_window :
    ∀ index point,
      point ∈ frame '' ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8
  line_class : WZ1PaperIsLineClass croppedFamily
  cropped_top_level_cwa :
    WZ2PaperConvexWolffBound
      croppedFamily
      (Kakeya.realRpowENN delta (-outputLoss))
  final_extremal :
    WZ2PaperCroppedIsExtremal
      sigma outputLoss croppedFamily
      (pureWZ2NormalizationCroppedShading
        frame indexEquiv ordinaryRefined)
  ordinary_cell_containment :
    ∀ index (cell : ℤ × ℤ × ℤ),
      ((frame '' ordinaryRefined.carrier index) ∩
          wz1PaperGridCube delta cell).Nonempty →
        wz1PaperGridCube delta cell ⊆
          wz1PaperTubeCarrier
            (croppedFamily.tube (indexEquiv index))
  ordinary_bounded_base :
    HasBoundedBase croppedFamily 4

namespace PureWZ2CroppedCriticalNormalizationSourceLeaves

/--
Mechanical assembly of the frozen normalization record from the concentrated
source-local leaves.
-/
noncomputable def toNormalizationData
    {sigma inputLoss outputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (leaves :
      PureWZ2CroppedCriticalNormalizationSourceLeaves
        (outputLoss := outputLoss)
        source normalizationExponent) :
    PureWZ2CroppedCriticalNormalizationData
      (outputLoss := outputLoss)
      source normalizationExponent where
  input_loss_le_half := leaves.input_loss_le_half
  selected := leaves.selected
  selected_nonempty := leaves.selected_nonempty
  ordinaryRefined := leaves.ordinaryRefined
  ordinary_subshading := leaves.ordinary_subshading
  retained_mass := leaves.retained_mass
  frame := leaves.frame
  croppedFamily := leaves.croppedFamily
  indexEquiv := leaves.indexEquiv
  ordinary_carrier_image_eq := leaves.ordinary_carrier_image_eq
  ordinary_per_tube := leaves.ordinary_per_tube
  ordinary_axial_window := by
    intro index point pointMem
    exact
      (leaves.ordinary_axial_window index point pointMem).trans
        (by norm_num)
  croppedRefined :=
    pureWZ2NormalizationCroppedShading
      leaves.frame leaves.indexEquiv leaves.ordinaryRefined
  cropped_carrier_eq_dense_cubicalization index :=
    pureWZ2NormalizationCroppedShading_carrier
      leaves.frame leaves.indexEquiv leaves.ordinaryRefined index
  cropped_cubical :=
    pureWZ2NormalizationCroppedShading_cubical
      leaves.frame leaves.indexEquiv leaves.ordinaryRefined
  line_class := leaves.line_class
  cropped_top_level_cwa := leaves.cropped_top_level_cwa
  final_extremal := leaves.final_extremal
  ordinary_cell_containment := leaves.ordinary_cell_containment
  ordinary_bounded_base := leaves.ordinary_bounded_base

end PureWZ2CroppedCriticalNormalizationSourceLeaves

/-! ## Quantifier-correct producer interfaces -/

/--
A source-uniform producer of the concentrated normalization leaves.

The scale threshold is fixed before the source, exactly as required for
direct use of `PureWZ2CriticalPackage.extremal_sequence`.
-/
def PureWZ2CroppedCriticalNormalizationSourceUniformLeafAt
    (normalizationExponent : ℕ) : Prop :=
  ∀ sigma outputLoss : ℝ,
    0 < outputLoss →
      ∃ inputLoss delta₁ : ℝ,
        0 < inputLoss ∧
        inputLoss ≤ outputLoss / 2 ∧
        0 < delta₁ ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₁ →
          ∀ source :
              PureWZ2ExtremalConfiguration
                sigma inputLoss delta,
            Nonempty
              (PureWZ2CroppedCriticalNormalizationSourceLeaves
                (outputLoss := outputLoss)
                source normalizationExponent)

/--
Convert a source-uniform leaf producer into the existing normalization-race
leaf interface.
-/
theorem pureWZ2_normalizationRaceUniformLeaf_of_sourceUniformLeaf
    (normalizationExponent : ℕ)
    (leaf :
      PureWZ2CroppedCriticalNormalizationSourceUniformLeafAt
        normalizationExponent) :
    PureWZ2CroppedCriticalNormalizationRaceUniformLeafAt
      normalizationExponent := by
  intro sigma outputLoss outputLossPos
  rcases leaf sigma outputLoss outputLossPos with
    ⟨inputLoss, delta₁, inputLossPos, inputLossLe,
      delta₁Pos, produce⟩
  have inputLossLeOutput : inputLoss ≤ outputLoss := by
    linarith
  refine
    ⟨inputLoss, delta₁, inputLossPos, inputLossLeOutput,
      delta₁Pos, ?_⟩
  intro delta deltaPos deltaLe source
  rcases produce delta deltaPos deltaLe source with ⟨leaves⟩
  exact ⟨leaves.toNormalizationData⟩

/--
Close all frozen top-level normalization quantifiers from a source-uniform
producer.
-/
theorem pureWZ2_cropped_critical_normalization_of_sourceUniformLeaf
    (normalizationExponent : ℕ)
    (leaf :
      PureWZ2CroppedCriticalNormalizationSourceUniformLeafAt
        normalizationExponent) :
    PureWZ2CroppedCriticalNormalizationAt normalizationExponent :=
  pureWZ2_cropped_critical_normalization_race_of_uniform_leaf
    normalizationExponent
    (pureWZ2_normalizationRaceUniformLeaf_of_sourceUniformLeaf
      normalizationExponent leaf)

/--
A source-local producer valid for extremizers whose shaded union is already
inside the fixed axis box used by the normalization geometry.
-/
def PureWZ2CroppedCriticalNormalizationSourceLocalLeafAt
    (normalizationExponent : ℕ) : Prop :=
  ∀ sigma outputLoss : ℝ,
    0 < outputLoss →
      ∃ inputLoss delta₁ : ℝ,
        0 < inputLoss ∧
        inputLoss ≤ outputLoss / 2 ∧
        0 < delta₁ ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₁ →
          ∀ source :
              PureWZ2ExtremalConfiguration
                sigma inputLoss delta,
            source.shading.union ⊆
                Kakeya.Streamlined.axisBox 2 2 2 →
              Nonempty
                (PureWZ2CroppedCriticalNormalizationSourceLeaves
                  (outputLoss := outputLoss)
                  source normalizationExponent)

/--
Convert a localized source-leaf producer into the existing normalization-race
local leaf.
-/
theorem pureWZ2_normalizationRaceLocalLeaf_of_sourceLocalLeaf
    (normalizationExponent : ℕ)
    (leaf :
      PureWZ2CroppedCriticalNormalizationSourceLocalLeafAt
        normalizationExponent) :
    PureWZ2CroppedCriticalNormalizationRaceLocalLeafAt
      normalizationExponent := by
  intro sigma outputLoss outputLossPos
  rcases leaf sigma outputLoss outputLossPos with
    ⟨inputLoss, delta₁, inputLossPos, inputLossLe,
      delta₁Pos, produce⟩
  have inputLossLeOutput : inputLoss ≤ outputLoss := by
    linarith
  refine
    ⟨inputLoss, delta₁, inputLossPos, inputLossLeOutput,
      delta₁Pos, ?_⟩
  intro delta deltaPos deltaLe source sourceLocal
  rcases
      produce delta deltaPos deltaLe source sourceLocal
    with
    ⟨leaves⟩
  exact ⟨leaves.toNormalizationData⟩

/--
Close all frozen top-level normalization quantifiers from a localized
producer and the explicitly missing localized critical sequence.
-/
theorem pureWZ2_cropped_critical_normalization_of_sourceLocalLeaf
    (normalizationExponent : ℕ)
    (leaf :
      PureWZ2CroppedCriticalNormalizationSourceLocalLeafAt
        normalizationExponent)
    (localizedSequence : PureWZ2CriticalAxisBoxExtremalSequence) :
    PureWZ2CroppedCriticalNormalizationAt normalizationExponent :=
  pureWZ2_cropped_critical_normalization_race_of_local_leaf
    normalizationExponent
    (pureWZ2_normalizationRaceLocalLeaf_of_sourceLocalLeaf
      normalizationExponent leaf)
    localizedSequence

/--
A derived-localization producer.  It starts from an extremizer at
`sourceLoss`, constructs a new extremizer at `inputLoss`, and supplies the
concentrated normalization leaves for that new source.
-/
def PureWZ2CroppedCriticalNormalizationSourceDerivedLeafAt
    (normalizationExponent : ℕ) : Prop :=
  ∀ sigma outputLoss : ℝ,
    0 < outputLoss →
      ∃ sourceLoss inputLoss delta₁ : ℝ,
        0 < sourceLoss ∧
        0 < inputLoss ∧
        inputLoss ≤ outputLoss / 2 ∧
        0 < delta₁ ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₁ →
          ∀ source :
              PureWZ2ExtremalConfiguration
                sigma sourceLoss delta,
            ∃ localized :
                PureWZ2ExtremalConfiguration
                  sigma inputLoss delta,
              Nonempty
                (PureWZ2CroppedCriticalNormalizationSourceLeaves
                  (outputLoss := outputLoss)
                  localized normalizationExponent)

/--
Convert a derived source-leaf producer into the existing normalization-race
derived leaf.
-/
theorem pureWZ2_normalizationRaceDerivedLeaf_of_sourceDerivedLeaf
    (normalizationExponent : ℕ)
    (leaf :
      PureWZ2CroppedCriticalNormalizationSourceDerivedLeafAt
        normalizationExponent) :
    PureWZ2CroppedCriticalNormalizationRaceDerivedLeafAt
      normalizationExponent := by
  intro sigma outputLoss outputLossPos
  rcases leaf sigma outputLoss outputLossPos with
    ⟨sourceLoss, inputLoss, delta₁,
      sourceLossPos, inputLossPos, inputLossLe,
      delta₁Pos, produce⟩
  have inputLossLeOutput : inputLoss ≤ outputLoss := by
    linarith
  refine
    ⟨sourceLoss, inputLoss, delta₁,
      sourceLossPos, inputLossPos, inputLossLeOutput,
      delta₁Pos, ?_⟩
  intro delta deltaPos deltaLe source
  rcases produce delta deltaPos deltaLe source with
    ⟨localized, ⟨leaves⟩⟩
  exact ⟨localized, ⟨leaves.toNormalizationData⟩⟩

/--
Close all frozen top-level normalization quantifiers from a
derived-localization producer.
-/
theorem pureWZ2_cropped_critical_normalization_of_sourceDerivedLeaf
    (normalizationExponent : ℕ)
    (leaf :
      PureWZ2CroppedCriticalNormalizationSourceDerivedLeafAt
        normalizationExponent) :
    PureWZ2CroppedCriticalNormalizationAt normalizationExponent :=
  pureWZ2_cropped_critical_normalization_race_of_derived_leaf
    normalizationExponent
    (pureWZ2_normalizationRaceDerivedLeaf_of_sourceDerivedLeaf
      normalizationExponent leaf)

/-! ## Existential frozen wrapper -/

theorem pureWZ2_cropped_critical_normalization_statement_of_sourceUniformLeaf
    (normalizationExponent : ℕ)
    (leaf :
      PureWZ2CroppedCriticalNormalizationSourceUniformLeafAt
        normalizationExponent) :
    PureWZ2CroppedCriticalNormalizationStatement :=
  ⟨normalizationExponent,
    pureWZ2_cropped_critical_normalization_of_sourceUniformLeaf
      normalizationExponent leaf⟩

theorem pureWZ2_cropped_critical_normalization_statement_of_sourceLocalLeaf
    (normalizationExponent : ℕ)
    (leaf :
      PureWZ2CroppedCriticalNormalizationSourceLocalLeafAt
        normalizationExponent)
    (localizedSequence : PureWZ2CriticalAxisBoxExtremalSequence) :
    PureWZ2CroppedCriticalNormalizationStatement :=
  ⟨normalizationExponent,
    pureWZ2_cropped_critical_normalization_of_sourceLocalLeaf
      normalizationExponent leaf localizedSequence⟩

theorem pureWZ2_cropped_critical_normalization_statement_of_sourceDerivedLeaf
    (normalizationExponent : ℕ)
    (leaf :
      PureWZ2CroppedCriticalNormalizationSourceDerivedLeafAt
        normalizationExponent) :
    PureWZ2CroppedCriticalNormalizationStatement :=
  ⟨normalizationExponent,
    pureWZ2_cropped_critical_normalization_of_sourceDerivedLeaf
      normalizationExponent leaf⟩

end Kakeya.Assouad

end
