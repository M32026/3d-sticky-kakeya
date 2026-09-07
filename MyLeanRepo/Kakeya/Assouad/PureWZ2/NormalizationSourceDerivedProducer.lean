import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationTopLevelAssembly

/-!
# Source-derived producer for cropped critical normalization

This module closes all record and quantifier wiring in the source-derived
normalization leaf while keeping the genuine mathematical obstruction
explicit.

The structural producer must construct one retained ordinary selection, its
rigid framed family, pure nearby-scale CWA, line-class geometry, and the
top-level cropped Convex-Wolff bound.  Once those data are fixed, the
canonical cropped shading is already determined by
`pureWZ2NormalizationCroppedShading`.

Only two scalar facts about that canonical shading remain:

* aggregate cropped density at `outputLoss`;
* the cropped union-volume upper bound at `outputLoss`.

No ordinary/cropped mass comparison is assumed.  Such a comparison does not
follow from the frozen data: the dense-cubicalization predicate can select
positive-volume cells even when its ordinary source is empty.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
The provenance-preserving geometric and structural output needed before the
two scalar canonical-crop estimates.

The stronger source is retained as a parameter so that a producer cannot
silently forget which frozen extremizer it was called on.  The target API
does not require an additional relation between `source` and `localized`.
-/
structure PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralData
    {sigma sourceLoss inputLoss outputLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta)
    (normalizationExponent : ℕ) where
  input_loss_le_half : inputLoss ≤ outputLoss / 2
  selected : Kakeya.Streamlined.TubeSubfamily localized.family
  selected_nonempty : selected.family.Nonempty
  ordinaryRefined :
    Kakeya.Streamlined.TubeShading selected.family
  ordinary_subshading :
    ∀ index,
      ordinaryRefined.carrier index ⊆
        localized.shading.carrier (selected.embedding index)
  retained_mass :
    wz2PaperPureRefinementFraction delta normalizationExponent *
        localized.shading.mass ≤
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
  cropped_pure_cwa :
    WZ2PaperPureCWAAtNearbyScales
      croppedFamily
      (Kakeya.realRpowENN delta (-outputLoss))
  cropped_top_level_cwa :
    WZ2PaperConvexWolffBound
      croppedFamily
      (Kakeya.realRpowENN delta (-outputLoss))
  ordinary_cell_containment :
    ∀ index (cell : ℤ × ℤ × ℤ),
      ((frame '' ordinaryRefined.carrier index) ∩
          wz1PaperGridCube delta cell).Nonempty →
        wz1PaperGridCube delta cell ⊆
          wz1PaperTubeCarrier
            (croppedFamily.tube (indexEquiv index))
  ordinary_bounded_base :
    HasBoundedBase croppedFamily 4

namespace PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralData

variable
    {sigma sourceLoss inputLoss outputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (data :
      PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralData
        (outputLoss := outputLoss)
        source localized normalizationExponent)

/-- The canonical cropped shading determined by the structural data. -/
noncomputable def canonicalCroppedShading :
    WZ1PaperTubeShading data.croppedFamily :=
  pureWZ2NormalizationCroppedShading
    data.frame data.indexEquiv data.ordinaryRefined

/-- The index equivalence transports nonemptiness to the cropped family. -/
theorem croppedFamily_nonempty :
    data.croppedFamily.Nonempty := by
  have cardEq :
      data.selected.family.card =
        data.croppedFamily.card := by
    simpa using Fintype.card_congr data.indexEquiv
  change 0 < data.croppedFamily.card
  rw [← cardEq]
  exact data.selected_nonempty

end PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralData

/--
The exact quantitative obstruction after source selection, framing, and both
CWA fields have been supplied.

These are direct properties of the canonical cropped shading.  In
particular, the certificate does not postulate paired ordinary/cropped mass.
-/
structure PureWZ2CroppedCriticalNormalizationCanonicalScalars
    {sigma sourceLoss inputLoss outputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (data :
      PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralData
        (outputLoss := outputLoss)
        source localized normalizationExponent) : Prop where
  dense :
    data.canonicalCroppedShading.IsLambdaDense
      (Kakeya.realRpowENN delta outputLoss)
  volume_upper :
    volume data.canonicalCroppedShading.union ≤
      Kakeya.realRpowENN delta (sigma - outputLoss)

namespace PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralData

/--
Assemble the concentrated frozen source leaves from structural data and the
two canonical-crop scalar estimates.
-/
noncomputable def toSourceLeaves
    {sigma sourceLoss inputLoss outputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (data :
      PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralData
        (outputLoss := outputLoss)
        source localized normalizationExponent)
    (scalars :
      PureWZ2CroppedCriticalNormalizationCanonicalScalars data) :
    PureWZ2CroppedCriticalNormalizationSourceLeaves
      (outputLoss := outputLoss)
      localized normalizationExponent where
  input_loss_le_half := data.input_loss_le_half
  selected := data.selected
  selected_nonempty := data.selected_nonempty
  ordinaryRefined := data.ordinaryRefined
  ordinary_subshading := data.ordinary_subshading
  retained_mass := data.retained_mass
  frame := data.frame
  croppedFamily := data.croppedFamily
  indexEquiv := data.indexEquiv
  ordinary_carrier_image_eq := data.ordinary_carrier_image_eq
  ordinary_per_tube := data.ordinary_per_tube
  ordinary_axial_window := data.ordinary_axial_window
  line_class := data.line_class
  cropped_top_level_cwa := data.cropped_top_level_cwa
  final_extremal :=
    {
      delta_pos := localized.extremal.delta_pos
      delta_le_one := localized.extremal.delta_le_one
      nonempty := data.croppedFamily_nonempty
      cwa_nearby_scales := data.cropped_pure_cwa
      cubical :=
        pureWZ2NormalizationCroppedShading_cubical
          data.frame data.indexEquiv data.ordinaryRefined
      dense := scalars.dense
      volume_upper := scalars.volume_upper
    }
  ordinary_cell_containment := data.ordinary_cell_containment
  ordinary_bounded_base := data.ordinary_bounded_base

end PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralData

/--
A source-derived structural producer with the quantifier order required by
the frozen critical sequence.
-/
def PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralProducerAt
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
                (PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralData
                  (outputLoss := outputLoss)
                  source localized normalizationExponent)

/--
A uniform producer of the two scalar facts for every structural output.

Keeping this separate from the structural producer records the precise
mathematical obstruction rather than hiding it in a full normalization
record or an unjustified paired-mass premise.
-/
def PureWZ2CroppedCriticalNormalizationCanonicalScalarsProducerAt
    (normalizationExponent : ℕ) : Prop :=
  ∀ {sigma sourceLoss inputLoss outputLoss delta : ℝ},
    ∀ {source :
        PureWZ2ExtremalConfiguration sigma sourceLoss delta},
      ∀ {localized :
          PureWZ2ExtremalConfiguration sigma inputLoss delta},
        ∀ data :
            PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralData
              (outputLoss := outputLoss)
              source localized normalizationExponent,
          PureWZ2CroppedCriticalNormalizationCanonicalScalars data

/--
The strongest unconditional assembly available from the audited interfaces:
the source-derived frozen leaf follows from the provenance-preserving
structural producer and exactly the two remaining canonical-crop scalars.
-/
theorem pureWZ2_cropped_critical_normalization_sourceDerivedLeaf_of_producers
    (normalizationExponent : ℕ)
    (structural :
      PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralProducerAt
        normalizationExponent)
    (canonicalScalars :
      PureWZ2CroppedCriticalNormalizationCanonicalScalarsProducerAt
        normalizationExponent) :
    PureWZ2CroppedCriticalNormalizationSourceDerivedLeafAt
      normalizationExponent := by
  intro sigma outputLoss outputLossPos
  rcases structural sigma outputLoss outputLossPos with
    ⟨sourceLoss, inputLoss, delta₁,
      sourceLossPos, inputLossPos, inputLossLe,
      delta₁Pos, produce⟩
  refine
    ⟨sourceLoss, inputLoss, delta₁,
      sourceLossPos, inputLossPos, inputLossLe,
      delta₁Pos, ?_⟩
  intro delta deltaPos deltaLe source
  rcases produce delta deltaPos deltaLe source with
    ⟨localized, ⟨data⟩⟩
  exact
    ⟨localized,
      ⟨data.toSourceLeaves
        (canonicalScalars data)⟩⟩

/--
Consequently the same two producers close the frozen normalization theorem,
including the critical-package quantifiers.
-/
theorem pureWZ2_cropped_critical_normalization_of_sourceDerivedProducers
    (normalizationExponent : ℕ)
    (structural :
      PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralProducerAt
        normalizationExponent)
    (canonicalScalars :
      PureWZ2CroppedCriticalNormalizationCanonicalScalarsProducerAt
        normalizationExponent) :
    PureWZ2CroppedCriticalNormalizationAt normalizationExponent :=
  pureWZ2_cropped_critical_normalization_of_sourceDerivedLeaf
    normalizationExponent
    (pureWZ2_cropped_critical_normalization_sourceDerivedLeaf_of_producers
      normalizationExponent structural canonicalScalars)

end Kakeya.Assouad

end
