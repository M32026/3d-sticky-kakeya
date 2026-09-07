import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationCanonicalCropScalars

/-!
# The rigid-crop geometry leaf after spatial localization

`PureWZ2SameDeltaSpatialCellLocalizationData` fixes a localized extremizer,
but the finite direction-cone and half-segment pigeonholes necessarily pass
to a further tube subfamily.  Consequently they cannot directly construct
`PureWZ2LocalizedCanonicalRigidFrameData`, whose framed family is definitionally
the whole localized family.  At normalization exponent zero, the source-derived
record also asks for full mass retention, while the two pigeonholes pay a fixed
mass loss.

This file therefore records the per-localization geometry certificate that is
actually produced by those pigeonholes.  It contains only the selected
ordinary shading, one common rigid frame, the fixed line-class/box geometry,
and the three quantitative crop comparisons.  CWA regularization and the
choice of a new extremal configuration belong before this leaf.

The final section proves the exact scalar absorption needed downstream.  The
per-tube density half, direction/spatial selection, and half-segment split
are charged a fixed factor `1 / 2823576`; the paper-body, crop-retention, and
union-expansion constants are `13824`, `1 / 100`, and `200`.  The union
estimate spends two copies of the input loss, so the precise gap is
`2 * inputLoss < outputLoss`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
One density half, six direction cones, `49³` spatial cells, and one
half-segment split.
-/
def pureWZ2RigidCropSelectionFactor : ENNReal :=
  (2823576 : ENNReal)⁻¹

/-- Fixed comparison between a paper carrier and its ordinary carrier. -/
def pureWZ2RigidCropBodyFactor : ENNReal :=
  13824

/-- Fixed mass retained by the canonical dense crop. -/
def pureWZ2RigidCropMassFactor : ENNReal :=
  (100 : ENNReal)⁻¹

/-- Fixed coefficient in the dense-cubical union expansion. -/
def pureWZ2RigidCropUnionFactor : ENNReal :=
  200

/--
The thinnest geometry output after spatial localization and the two finite
pigeonholes.

The selected shading is allowed to be a genuine subfamily of the localized
family.  This is the field missing from
`PureWZ2LocalizedCanonicalRigidFrameData`.  The last three fields are exactly
the geometric estimates consumed by the scalar argument.
-/
structure PureWZ2LocalizedCanonicalRigidCropGeometryData
    {sigma sourceLoss inputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    (localization :
      PureWZ2SameDeltaSpatialCellLocalizationData
        source localized) where
  selected : Kakeya.Streamlined.TubeSubfamily localized.family
  selected_nonempty : selected.family.Nonempty
  ordinaryRefined :
    Kakeya.Streamlined.TubeShading selected.family
  ordinary_subshading :
    ∀ index,
      ordinaryRefined.carrier index ⊆
        localized.shading.carrier (selected.embedding index)
  fixed_mass_retention :
    pureWZ2RigidCropSelectionFactor *
        localized.shading.mass ≤
      ordinaryRefined.mass
  per_tube_density :
    ∀ index,
      (Kakeya.realRpowENN delta inputLoss / 2) *
          volume (selected.family.tube index).carrier ≤
        volume (ordinaryRefined.carrier index)
  frame : Point3 ≃ᵃⁱ[ℝ] Point3
  croppedFamily : Kakeya.Streamlined.TubeFamily delta
  indexEquiv :
    Fin selected.family.card ≃ Fin croppedFamily.card
  ordinary_carrier_image_eq :
    ∀ index,
      (croppedFamily.tube (indexEquiv index)).carrier =
        frame '' (selected.family.tube index).carrier
  carrier_margin :
    ∀ index point,
      point ∈ (croppedFamily.tube index).carrier →
        |point 0| ≤ 1 - delta ∧
          |point 1| ≤ 1 - delta ∧
          |point 2| ≤ 1 - delta
  full_carrier_axisBox :
    ∀ index,
      (croppedFamily.tube index).carrier ⊆
        Kakeya.Streamlined.axisBox 2 2 2
  line_class : WZ1PaperIsLineClass croppedFamily
  paper_body_mass_upper :
    (wz1PaperBodyFamily croppedFamily).mass ≤
      pureWZ2RigidCropBodyFactor *
        selected.family.toBodyFamily.mass
  canonical_crop_mass_retention :
    pureWZ2RigidCropMassFactor * ordinaryRefined.mass ≤
      (pureWZ2NormalizationCroppedShading
        frame indexEquiv ordinaryRefined).mass
  canonical_crop_union_expansion :
    volume
        (pureWZ2NormalizationCroppedShading
          frame indexEquiv ordinaryRefined).union ≤
      (pureWZ2RigidCropUnionFactor *
          Kakeya.realRpowENN delta (-inputLoss)) *
        volume (frame '' ordinaryRefined.union)

/--
The per-localization geometry leaf.  It deliberately has no source-uniform
producer quantifiers and no all-scale CWA fields.
-/
def PureWZ2LocalizedCanonicalRigidCropGeometryLeaf
    {sigma sourceLoss inputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    (localization :
      PureWZ2SameDeltaSpatialCellLocalizationData
        source localized) : Prop :=
  Nonempty
    (PureWZ2LocalizedCanonicalRigidCropGeometryData
      localization)

namespace PureWZ2LocalizedCanonicalRigidCropGeometryData

variable
    {sigma sourceLoss inputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {localization :
      PureWZ2SameDeltaSpatialCellLocalizationData
        source localized}
    (geometry :
      PureWZ2LocalizedCanonicalRigidCropGeometryData
        localization)

/-- The canonical crop determined by the selected shading and common frame. -/
noncomputable def canonicalCroppedShading :
    WZ1PaperTubeShading geometry.croppedFamily :=
  pureWZ2NormalizationCroppedShading
    geometry.frame geometry.indexEquiv geometry.ordinaryRefined

@[simp]
theorem canonicalCroppedShading_eq :
    geometry.canonicalCroppedShading =
      pureWZ2NormalizationCroppedShading
        geometry.frame geometry.indexEquiv geometry.ordinaryRefined :=
  rfl

private theorem ordinary_union_measurable :
    MeasurableSet geometry.ordinaryRefined.union := by
  have unionEq :
      geometry.ordinaryRefined.union =
        ⋃ index : Fin geometry.selected.family.card,
          geometry.ordinaryRefined.carrier index := by
    ext point
    constructor
    · rintro ⟨index, pointMem⟩
      exact Set.mem_iUnion.mpr ⟨index, pointMem⟩
    · intro pointMem
      rcases Set.mem_iUnion.mp pointMem with
        ⟨index, indexMem⟩
      exact ⟨index, indexMem⟩
  rw [unionEq]
  exact MeasurableSet.iUnion geometry.ordinaryRefined.measurable_carrier

private theorem ordinary_union_subset_localized :
    geometry.ordinaryRefined.union ⊆ localized.shading.union := by
  rintro point ⟨index, pointMem⟩
  exact
    ⟨geometry.selected.embedding index,
      geometry.ordinary_subshading index pointMem⟩

private theorem aggregate_per_tube_density :
    (Kakeya.realRpowENN delta inputLoss / 2) *
        geometry.selected.family.toBodyFamily.mass ≤
      geometry.ordinaryRefined.mass := by
  change
    (Kakeya.realRpowENN delta inputLoss / 2) *
          (∑ index : Fin geometry.selected.family.card,
            volume (geometry.selected.family.tube index).carrier) ≤
      ∑ index : Fin geometry.selected.family.card,
        volume (geometry.ordinaryRefined.carrier index)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun index _ =>
    geometry.per_tube_density index

end PureWZ2LocalizedCanonicalRigidCropGeometryData

/--
The three explicit small-scale absorptions.

The first field pays the direction/spatial/half selection loss.  The second
combines the paper-body factor `13824`, the per-tube density factor `1 / 2`,
and the crop factor `1 / 100`.  The third pays the `200 * delta⁻inputLoss`
union expansion against the localized volume upper bound.
-/
structure PureWZ2LocalizedCanonicalRigidCropScalarAbsorption
    (inputLoss outputLoss delta : ℝ) : Prop where
  selection :
    Kakeya.realRpowENN delta (outputLoss - inputLoss) ≤
      pureWZ2RigidCropSelectionFactor
  body_crop :
    Kakeya.realRpowENN delta (outputLoss - inputLoss) *
        pureWZ2RigidCropBodyFactor ≤
      (200 : ENNReal)⁻¹
  union :
    pureWZ2RigidCropUnionFactor *
        Kakeya.realRpowENN delta
          (outputLoss - 2 * inputLoss) ≤
      1

private theorem exists_delta_realRpowENN_le_inv
    (constant : ENNReal)
    (constantFinite : constant ≠ ⊤)
    {gap : ℝ}
    (gapPos : 0 < gap) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ delta : ℝ,
        0 < delta →
        delta ≤ delta₀ →
          Kakeya.realRpowENN delta gap ≤ constant⁻¹ := by
  rcases
      exists_delta_realRpowENN_bound
        constant constantFinite gapPos with
    ⟨delta₀, delta₀Pos, delta₀LeOne, bound⟩
  refine ⟨delta₀, delta₀Pos, delta₀LeOne, ?_⟩
  intro delta deltaPos deltaLe
  have inverseBound :=
    ENNReal.inv_le_inv' (bound delta deltaPos deltaLe)
  rw [pure_wz2_realRpowENN_inv deltaPos] at inverseBound
  simpa only [neg_neg] using inverseBound

/--
One threshold absorbs every fixed rigid-crop constant.

The strict two-loss gap is not cosmetic: the union expansion contains
`delta⁻inputLoss` and is applied to a localized union already bounded by
`delta^(sigma - inputLoss)`.
-/
theorem exists_pureWZ2LocalizedCanonicalRigidCropScalarAbsorption
    {inputLoss outputLoss : ℝ}
    (inputLossPos : 0 < inputLoss)
    (twoInputLossLt : 2 * inputLoss < outputLoss) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ delta : ℝ,
        0 < delta →
        delta ≤ delta₀ →
          PureWZ2LocalizedCanonicalRigidCropScalarAbsorption
            inputLoss outputLoss delta := by
  have oneGapPos : 0 < outputLoss - inputLoss := by
    linarith
  have twoGapPos : 0 < outputLoss - 2 * inputLoss := by
    linarith
  rcases
      exists_delta_realRpowENN_le_inv
        (2823576 : ENNReal) (by norm_num) oneGapPos with
    ⟨selectionDelta, selectionDeltaPos,
      selectionDeltaLeOne, selectionBound⟩
  rcases
      exists_delta_realRpowENN_le_inv
        (2764800 : ENNReal) (by norm_num) oneGapPos with
    ⟨bodyDelta, bodyDeltaPos,
      bodyDeltaLeOne, bodyBound⟩
  rcases
      exists_delta_realRpowENN_le_inv
        (200 : ENNReal) (by norm_num) twoGapPos with
    ⟨unionDelta, unionDeltaPos,
      unionDeltaLeOne, unionBound⟩
  let delta₀ := min selectionDelta (min bodyDelta unionDelta)
  have delta₀Pos : 0 < delta₀ :=
    lt_min selectionDeltaPos
      (lt_min bodyDeltaPos unionDeltaPos)
  have delta₀LeOne : delta₀ ≤ 1 :=
    (min_le_left selectionDelta
      (min bodyDelta unionDelta)).trans selectionDeltaLeOne
  refine ⟨delta₀, delta₀Pos, delta₀LeOne, ?_⟩
  intro delta deltaPos deltaLe
  have deltaSelection : delta ≤ selectionDelta :=
    deltaLe.trans
      (min_le_left selectionDelta (min bodyDelta unionDelta))
  have deltaBody : delta ≤ bodyDelta :=
    deltaLe.trans
      ((min_le_right selectionDelta
        (min bodyDelta unionDelta)).trans
          (min_le_left bodyDelta unionDelta))
  have deltaUnion : delta ≤ unionDelta :=
    deltaLe.trans
      ((min_le_right selectionDelta
        (min bodyDelta unionDelta)).trans
          (min_le_right bodyDelta unionDelta))
  refine
    {
      selection := ?_
      body_crop := ?_
      union := ?_
    }
  · simpa [pureWZ2RigidCropSelectionFactor] using
      selectionBound delta deltaPos deltaSelection
  · calc
      Kakeya.realRpowENN delta (outputLoss - inputLoss) *
            pureWZ2RigidCropBodyFactor ≤
          (2764800 : ENNReal)⁻¹ * 13824 := by
        exact mul_le_mul_right'
          (bodyBound delta deltaPos deltaBody) 13824
      _ = (200 : ENNReal)⁻¹ := by
        rw [show (2764800 : ENNReal) =
            13824 * 200 by norm_num,
          ENNReal.mul_inv (by norm_num) (by norm_num)]
        calc
          (13824 : ENNReal)⁻¹ * (200 : ENNReal)⁻¹ * 13824 =
              (200 : ENNReal)⁻¹ *
                ((13824 : ENNReal)⁻¹ * 13824) := by
            ring
          _ = (200 : ENNReal)⁻¹ := by
            rw [ENNReal.inv_mul_cancel] <;> norm_num
  · calc
      pureWZ2RigidCropUnionFactor *
            Kakeya.realRpowENN delta
              (outputLoss - 2 * inputLoss) ≤
          (200 : ENNReal) * (200 : ENNReal)⁻¹ := by
        exact mul_le_mul_left'
          (unionBound delta deltaPos deltaUnion) 200
      _ = 1 := by
        rw [ENNReal.mul_inv_cancel] <;> norm_num

namespace PureWZ2LocalizedCanonicalRigidCropGeometryData

variable
    {sigma sourceLoss inputLoss outputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {localization :
      PureWZ2SameDeltaSpatialCellLocalizationData
        source localized}
    (geometry :
      PureWZ2LocalizedCanonicalRigidCropGeometryData
        localization)
    (absorption :
      PureWZ2LocalizedCanonicalRigidCropScalarAbsorption
        inputLoss outputLoss delta)

include absorption

/-- The fixed finite selection loss is absorbed into the loss gap. -/
theorem absorbed_mass_retention :
    Kakeya.realRpowENN delta (outputLoss - inputLoss) *
        localized.shading.mass ≤
      geometry.ordinaryRefined.mass := by
  have selectionAbsorption :=
    PureWZ2LocalizedCanonicalRigidCropScalarAbsorption.selection
      absorption
  calc
    Kakeya.realRpowENN delta (outputLoss - inputLoss) *
          localized.shading.mass ≤
        pureWZ2RigidCropSelectionFactor *
          localized.shading.mass := by
      exact mul_le_mul_right' selectionAbsorption _
    _ ≤ geometry.ordinaryRefined.mass :=
      geometry.fixed_mass_retention

/--
The paper-body comparison, per-tube density, and crop retention imply the
desired aggregate cropped density after scalar absorption.
-/
theorem canonical_crop_dense :
    geometry.canonicalCroppedShading.IsLambdaDense
      (Kakeya.realRpowENN delta outputLoss) := by
  have bodyCropAbsorption :=
    PureWZ2LocalizedCanonicalRigidCropScalarAbsorption.body_crop
      absorption
  have powerSplit :
      Kakeya.realRpowENN delta outputLoss =
        Kakeya.realRpowENN delta (outputLoss - inputLoss) *
          Kakeya.realRpowENN delta inputLoss := by
    rw [← Kakeya.Streamlined.realRpowENN_add
      localized.extremal.delta_pos]
    congr 1
    ring
  change
    Kakeya.realRpowENN delta outputLoss *
          (wz1PaperBodyFamily geometry.croppedFamily).mass ≤
      geometry.canonicalCroppedShading.mass
  calc
    Kakeya.realRpowENN delta outputLoss *
          (wz1PaperBodyFamily geometry.croppedFamily).mass ≤
        Kakeya.realRpowENN delta outputLoss *
          (pureWZ2RigidCropBodyFactor *
            geometry.selected.family.toBodyFamily.mass) := by
      gcongr
      exact geometry.paper_body_mass_upper
    _ =
        (Kakeya.realRpowENN delta
            (outputLoss - inputLoss) *
          pureWZ2RigidCropBodyFactor) *
        (Kakeya.realRpowENN delta inputLoss *
          geometry.selected.family.toBodyFamily.mass) := by
      rw [powerSplit]
      ring
    _ ≤
        (200 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta inputLoss *
            geometry.selected.family.toBodyFamily.mass) := by
      exact mul_le_mul_right' bodyCropAbsorption _
    _ =
        pureWZ2RigidCropMassFactor *
          ((Kakeya.realRpowENN delta inputLoss / 2) *
            geometry.selected.family.toBodyFamily.mass) := by
      rw [show (200 : ENNReal)⁻¹ =
          (100 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ by
        rw [← ENNReal.mul_inv (by norm_num) (by norm_num)]
        norm_num]
      simp only [pureWZ2RigidCropMassFactor, div_eq_mul_inv]
      ring
    _ ≤
        pureWZ2RigidCropMassFactor *
          geometry.ordinaryRefined.mass := by
      gcongr
      exact geometry.aggregate_per_tube_density
    _ ≤ geometry.canonicalCroppedShading.mass := by
      simpa [canonicalCroppedShading] using
        geometry.canonical_crop_mass_retention

/--
The union expansion and localized extremal volume bound imply the desired
cropped union bound after spending two input-loss copies.
-/
theorem canonical_crop_volume_upper :
    volume geometry.canonicalCroppedShading.union ≤
      Kakeya.realRpowENN delta (sigma - outputLoss) := by
  have unionAbsorption :=
    PureWZ2LocalizedCanonicalRigidCropScalarAbsorption.union
      absorption
  have frameVolume :
      volume (geometry.frame '' geometry.ordinaryRefined.union) =
        volume geometry.ordinaryRefined.union :=
    Kakeya.Streamlined.AffineIsometryEquiv.volume_image
      geometry.frame geometry.ordinaryRefined.union
        geometry.ordinary_union_measurable
  have powerIdentity :
      Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN delta (sigma - inputLoss) =
        Kakeya.realRpowENN delta
            (outputLoss - 2 * inputLoss) *
          Kakeya.realRpowENN delta
            (sigma - outputLoss) := by
    rw [← Kakeya.Streamlined.realRpowENN_add
        localized.extremal.delta_pos,
      ← Kakeya.Streamlined.realRpowENN_add
        localized.extremal.delta_pos]
    congr 1
    ring
  calc
    volume geometry.canonicalCroppedShading.union ≤
        (pureWZ2RigidCropUnionFactor *
            Kakeya.realRpowENN delta (-inputLoss)) *
          volume (geometry.frame '' geometry.ordinaryRefined.union) := by
      simpa [canonicalCroppedShading] using
        geometry.canonical_crop_union_expansion
    _ =
        (pureWZ2RigidCropUnionFactor *
            Kakeya.realRpowENN delta (-inputLoss)) *
          volume geometry.ordinaryRefined.union := by
      rw [frameVolume]
    _ ≤
        (pureWZ2RigidCropUnionFactor *
            Kakeya.realRpowENN delta (-inputLoss)) *
          volume localized.shading.union := by
      exact mul_le_mul_left'
        (measure_mono geometry.ordinary_union_subset_localized)
        (pureWZ2RigidCropUnionFactor *
          Kakeya.realRpowENN delta (-inputLoss))
    _ ≤
        (pureWZ2RigidCropUnionFactor *
            Kakeya.realRpowENN delta (-inputLoss)) *
          Kakeya.realRpowENN delta (sigma - inputLoss) := by
      gcongr
      exact localized.extremal.volume_upper
    _ =
        (pureWZ2RigidCropUnionFactor *
            Kakeya.realRpowENN delta
              (outputLoss - 2 * inputLoss)) *
          Kakeya.realRpowENN delta
            (sigma - outputLoss) := by
      rw [mul_assoc, powerIdentity]
      ring
    _ ≤
        1 *
          Kakeya.realRpowENN delta
            (sigma - outputLoss) := by
      exact mul_le_mul_right' unionAbsorption _
    _ = Kakeya.realRpowENN delta (sigma - outputLoss) :=
      one_mul _

end PureWZ2LocalizedCanonicalRigidCropGeometryData

end Kakeya.Assouad

end
