import MyLeanRepo.Kakeya.Assouad.PureWZ2.IndexedPerTubePruning
import MyLeanRepo.Kakeya.Assouad.PureWZ2.DenseCubicalizationVacuity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers
import MyLeanRepo.Kakeya.Streamlined.VolumeHelpers

/-!
# A synchronized per-tube core for frozen WZ2 normalization

The frozen normalization record does not assert that the affine image of its
ordinary shading has any aggregate overlap with the cropped cubical shading.
This is essential: when the ordinary source is empty,
`pureWZ2DenseCubicalization_empty_source` shows that dense cubicalization can
still contain positive-volume grid cells.

This module isolates that exact missing quantity.  The `literalOverlapShading`
is the pointwise intersection of the affine ordinary source with the frozen
cropped shading.  One aggregate lower bound for its mass simultaneously
supplies:

* enough density for indexed per-tube pruning;
* retention of cropped shaded mass on the same retained indices.

The resulting core records positive ordinary volume, and hence a nonempty
ordinary source, at every retained index.  No arbitrary intersection is
assumed to retain mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2CroppedCriticalNormalizationData

variable
    {sigma inputLoss outputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := outputLoss)
        source normalizationExponent)

private theorem frame_image_measurable
    (index : Fin normalized.selected.family.card) :
    MeasurableSet
      (normalized.frame ''
        normalized.ordinaryRefined.carrier index) := by
  let measurableFrame : Point3 ≃ᵐ Point3 :=
    {
      toFun := normalized.frame
      invFun := normalized.frame.symm
      left_inv := normalized.frame.left_inv
      right_inv := normalized.frame.right_inv
      measurable_toFun :=
        normalized.frame.continuous_of_finiteDimensional.measurable
      measurable_invFun :=
        normalized.frame.symm.continuous_of_finiteDimensional.measurable
    }
  exact
    (measurableFrame.measurableSet_image).mpr
      (normalized.ordinaryRefined.measurable_carrier index)

/--
The literal ordinary/cropped overlap on every frozen cropped index.

Using the intersection, rather than either carrier separately, is what makes
one later index selection valid simultaneously for the ordinary and cropped
models.
-/
noncomputable def literalOverlapShading :
    Kakeya.Streamlined.TubeShading normalized.croppedFamily where
  carrier index :=
    (normalized.frame ''
        normalized.ordinaryRefined.carrier
          (normalized.indexEquiv.symm index)) ∩
      normalized.croppedRefined.carrier index
  measurable_carrier index :=
    (frame_image_measurable normalized
      (normalized.indexEquiv.symm index)).inter
        (normalized.croppedRefined.measurable_carrier index)
  subset_body index := by
    intro point pointMem
    rcases pointMem.1 with ⟨sourcePoint, sourcePointMem, rfl⟩
    have sourceBody :=
      normalized.ordinaryRefined.subset_body
        (normalized.indexEquiv.symm index) sourcePointMem
    have imageBody :
        normalized.frame sourcePoint ∈
          normalized.frame ''
            (normalized.selected.family.tube
              (normalized.indexEquiv.symm index)).carrier :=
      ⟨sourcePoint, sourceBody, rfl⟩
    rw [← normalized.ordinary_carrier_image_eq
      (normalized.indexEquiv.symm index),
      normalized.indexEquiv.apply_symm_apply index] at imageBody
    exact imageBody

theorem literalOverlapShading_carrier
    (index : Fin normalized.croppedFamily.card) :
    normalized.literalOverlapShading.carrier index =
      (normalized.frame ''
          normalized.ordinaryRefined.carrier
            (normalized.indexEquiv.symm index)) ∩
        normalized.croppedRefined.carrier index :=
  rfl

/-- View one finite set of cropped indices as a genuine synchronized subfamily. -/
noncomputable def synchronizedSubfamily
    (retained : Finset (Fin normalized.croppedFamily.card)) :
    Kakeya.Streamlined.TubeSubfamily normalized.croppedFamily where
  family := selectedTubeFamily normalized.croppedFamily retained
  embedding :=
    ⟨fun index => (retained.equivFin.symm index).1, by
      intro first second equality
      apply retained.equivFin.symm.injective
      exact Subtype.ext equality⟩
  tube_eq _ := rfl

/-- The cropped shading restricted along exactly the synchronized indices. -/
noncomputable def synchronizedCroppedShading
    (retained : Finset (Fin normalized.croppedFamily.card)) :
    WZ1PaperTubeShading
      (normalized.synchronizedSubfamily retained).family :=
  restrictPaperShading
    (normalized.synchronizedSubfamily retained)
    normalized.croppedRefined

/-- The literal overlap shading restricted along the same synchronized indices. -/
noncomputable def synchronizedOverlapShading
    (retained : Finset (Fin normalized.croppedFamily.card)) :
    Kakeya.Streamlined.TubeShading
      (normalized.synchronizedSubfamily retained).family :=
  selectedTubeShading normalized.literalOverlapShading retained

/--
The output of synchronized aggregate-to-per-tube pruning.

All fields refer to the same `retained` set.  In particular, the ordinary
pointwise lower bound, cropped mass retention, and cardinality retention
cannot silently come from different subfamilies.
-/
structure NormalizationSynchronizedPerTubeCore
    (outputEta : ℝ)
    (croppedMassFraction : ENNReal) where
  retained : Finset (Fin normalized.croppedFamily.card)
  retained_nonempty : retained.Nonempty
  cardinality_retention :
    Kakeya.realRpowENN delta outputEta *
          normalized.croppedFamily.enncard ≤
      (normalized.synchronizedSubfamily retained).family.enncard
  overlap_mass_retention :
    normalized.literalOverlapShading.mass ≤
      2 * (normalized.synchronizedOverlapShading retained).mass
  cropped_mass_retention :
    croppedMassFraction * normalized.croppedRefined.mass ≤
      2 * (normalized.synchronizedCroppedShading retained).mass
  overlap_per_tube :
    ∀ index :
        Fin (normalized.synchronizedSubfamily retained).family.card,
      Kakeya.realRpowENN delta outputEta *
            ((normalized.synchronizedSubfamily retained).family.tube
              index).volume ≤
        volume
          ((normalized.synchronizedOverlapShading retained).carrier
            index)
  ordinary_per_tube :
    ∀ index :
        Fin (normalized.synchronizedSubfamily retained).family.card,
      Kakeya.realRpowENN delta outputEta *
            ((normalized.synchronizedSubfamily retained).family.tube
              index).volume ≤
        volume
          (normalized.ordinaryRefined.carrier
            (normalized.indexEquiv.symm
              ((normalized.synchronizedSubfamily retained).embedding
                index)))
  ordinary_volume_pos :
    ∀ index :
        Fin (normalized.synchronizedSubfamily retained).family.card,
      0 <
        volume
          (normalized.ordinaryRefined.carrier
            (normalized.indexEquiv.symm
              ((normalized.synchronizedSubfamily retained).embedding
                index)))
  ordinary_source_nonempty :
    ∀ index :
        Fin (normalized.synchronizedSubfamily retained).family.card,
      (normalized.ordinaryRefined.carrier
        (normalized.indexEquiv.symm
          ((normalized.synchronizedSubfamily retained).embedding
            index))).Nonempty
  frame_ordinary_source_nonempty :
    ∀ index :
        Fin (normalized.synchronizedSubfamily retained).family.card,
      (normalized.frame ''
        normalized.ordinaryRefined.carrier
          (normalized.indexEquiv.symm
            ((normalized.synchronizedSubfamily retained).embedding
              index))).Nonempty

/--
Construct a synchronized core from the exact aggregate overlap missing from
the frozen normalization record.

The single `aggregateOverlap` premise is bicriteria: its left branch is the
aggregate density needed by `pure_wz2_indexed_per_tube_pruning`, while its
right branch is the requested retained fraction of the cropped shaded mass.
The theorem never infers either inequality merely from an intersection.
-/
theorem exists_normalizationSynchronizedPerTubeCore
    (inputEta outputEta : ℝ)
    (croppedMassFraction : ENNReal)
    (densitySeparation :
      Kakeya.realRpowENN delta outputEta ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta inputEta)
    (aggregateOverlap :
      max
          (Kakeya.realRpowENN delta inputEta *
            normalized.croppedFamily.toBodyFamily.mass)
          (croppedMassFraction *
            normalized.croppedRefined.mass) ≤
        normalized.literalOverlapShading.mass) :
    Nonempty
      (NormalizationSynchronizedPerTubeCore
        normalized outputEta croppedMassFraction) := by
  have overlapDense :
      normalized.literalOverlapShading.IsLambdaDense
        (Kakeya.realRpowENN delta inputEta) := by
    exact
      (le_max_left
        (Kakeya.realRpowENN delta inputEta *
          normalized.croppedFamily.toBodyFamily.mass)
        (croppedMassFraction *
          normalized.croppedRefined.mass)).trans aggregateOverlap
  rcases
      pure_wz2_indexed_per_tube_pruning
        normalized.final_extremal.delta_pos
        normalized.final_extremal.delta_le_one
        normalized.final_extremal.nonempty
        normalized.literalOverlapShading
        overlapDense densitySeparation with
    ⟨retained, retainedNonempty, cardinalityRetention,
      overlapMassRetention, overlapPerTubeAmbient⟩
  let synchronized := normalized.synchronizedSubfamily retained
  have overlapPerTube :
      ∀ index : Fin synchronized.family.card,
        Kakeya.realRpowENN delta outputEta *
              (synchronized.family.tube index).volume ≤
          volume
            ((normalized.synchronizedOverlapShading retained).carrier
              index) := by
    intro index
    exact
      overlapPerTubeAmbient
        (retained.equivFin.symm index).1
        (retained.equivFin.symm index).2
  have ordinaryPerTube :
      ∀ index : Fin synchronized.family.card,
        Kakeya.realRpowENN delta outputEta *
              (synchronized.family.tube index).volume ≤
          volume
            (normalized.ordinaryRefined.carrier
              (normalized.indexEquiv.symm
                (synchronized.embedding index))) := by
    intro index
    let ambient := synchronized.embedding index
    let ordinary := normalized.indexEquiv.symm ambient
    calc
      Kakeya.realRpowENN delta outputEta *
            (synchronized.family.tube index).volume ≤
          volume
            ((normalized.synchronizedOverlapShading retained).carrier
              index) :=
        overlapPerTube index
      _ ≤
          volume
            (normalized.frame ''
              normalized.ordinaryRefined.carrier ordinary) := by
        apply measure_mono
        exact Set.inter_subset_left
      _ =
          volume
            (normalized.ordinaryRefined.carrier ordinary) := by
        exact
          Kakeya.Streamlined.AffineIsometryEquiv.volume_image
            normalized.frame
            (normalized.ordinaryRefined.carrier ordinary)
            (normalized.ordinaryRefined.measurable_carrier ordinary)
  have ordinaryVolumePos :
      ∀ index : Fin synchronized.family.card,
        0 <
          volume
            (normalized.ordinaryRefined.carrier
              (normalized.indexEquiv.symm
                (synchronized.embedding index))) := by
    intro index
    have densityPos :
        0 < Kakeya.realRpowENN delta outputEta :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos
          normalized.final_extremal.delta_pos outputEta)
    have tubeVolumePos :
        0 < (synchronized.family.tube index).volume := by
      simpa [Kakeya.DeltaTube.volume] using
        wz2_paper_ordinary_tube_volume_pos
          (synchronized.family.tube index)
          normalized.final_extremal.delta_pos
    exact
      (ENNReal.mul_pos densityPos.ne' tubeVolumePos.ne').trans_le
        (ordinaryPerTube index)
  have ordinarySourceNonempty :
      ∀ index : Fin synchronized.family.card,
        (normalized.ordinaryRefined.carrier
          (normalized.indexEquiv.symm
            (synchronized.embedding index))).Nonempty := by
    intro index
    exact
      nonempty_of_measure_ne_zero
        (ordinaryVolumePos index).ne'
  have frameOrdinarySourceNonempty :
      ∀ index : Fin synchronized.family.card,
        (normalized.frame ''
          normalized.ordinaryRefined.carrier
            (normalized.indexEquiv.symm
              (synchronized.embedding index))).Nonempty := by
    intro index
    exact Set.image_nonempty.mpr (ordinarySourceNonempty index)
  have selectedOverlapLeCropped :
      (normalized.synchronizedOverlapShading retained).mass ≤
        (normalized.synchronizedCroppedShading retained).mass := by
    change
      (∑ index : Fin synchronized.family.card,
          volume
            ((normalized.synchronizedOverlapShading retained).carrier
              index)) ≤
        ∑ index : Fin synchronized.family.card,
          volume
            ((normalized.synchronizedCroppedShading retained).carrier
              index)
    exact Finset.sum_le_sum fun index _ => by
      apply measure_mono
      exact Set.inter_subset_right
  have croppedMassDemand :
      croppedMassFraction * normalized.croppedRefined.mass ≤
        normalized.literalOverlapShading.mass :=
    (le_max_right
      (Kakeya.realRpowENN delta inputEta *
        normalized.croppedFamily.toBodyFamily.mass)
      (croppedMassFraction *
        normalized.croppedRefined.mass)).trans aggregateOverlap
  have croppedMassRetention :
      croppedMassFraction * normalized.croppedRefined.mass ≤
        2 * (normalized.synchronizedCroppedShading retained).mass := by
    calc
      croppedMassFraction * normalized.croppedRefined.mass ≤
          normalized.literalOverlapShading.mass :=
        croppedMassDemand
      _ ≤
          2 *
            (normalized.synchronizedOverlapShading retained).mass := by
        exact overlapMassRetention
      _ ≤
          2 *
            (normalized.synchronizedCroppedShading retained).mass := by
        gcongr
  exact
    ⟨{
      retained := retained
      retained_nonempty := retainedNonempty
      cardinality_retention := cardinalityRetention
      overlap_mass_retention := overlapMassRetention
      cropped_mass_retention := croppedMassRetention
      overlap_per_tube := overlapPerTube
      ordinary_per_tube := ordinaryPerTube
      ordinary_volume_pos := ordinaryVolumePos
      ordinary_source_nonempty := ordinarySourceNonempty
      frame_ordinary_source_nonempty := frameOrdinarySourceNonempty
    }⟩

end PureWZ2CroppedCriticalNormalizationData

end Kakeya.Assouad

end
