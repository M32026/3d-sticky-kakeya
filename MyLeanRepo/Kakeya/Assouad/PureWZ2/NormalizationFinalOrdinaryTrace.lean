import MyLeanRepo.Kakeya.Assouad.PureWZ2.DenseCubicalTrace
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Ordinary trace on a final normalized subshading

A frozen normalization identifies every cropped carrier with the dense
cubicalization of an ordinary source carrier after a rigid frame.  Any later
cubical subshading therefore has a canonical ordinary trace on the same
selected indices.  This module records that trace without assuming that an
arbitrary cropped carrier itself lies in an ordinary unit tube.
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
    (selected :
      Kakeya.Streamlined.TubeSubfamily normalized.croppedFamily)
    (finalShading : WZ1PaperTubeShading selected.family)

noncomputable def ordinaryIndex
    (index : Fin selected.family.card) :
    Fin normalized.selected.family.card :=
  normalized.indexEquiv.symm (selected.embedding index)

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
  have imageMeasurable :=
    (measurableFrame.measurableSet_image).mpr
      (normalized.ordinaryRefined.measurable_carrier index)
  exact imageMeasurable

/--
The ordinary trace of a final cropped subshading.

The first factor remembers the normalized ordinary source carrier; the
second factor remembers the actual final cropped carrier used downstream.
-/
noncomputable def finalOrdinaryTrace :
    Kakeya.Streamlined.TubeShading selected.family where
  carrier index :=
    (normalized.frame ''
      normalized.ordinaryRefined.carrier
        (ordinaryIndex normalized selected index)) ∩
      finalShading.carrier index
  measurable_carrier index :=
    (frame_image_measurable normalized
      (ordinaryIndex normalized selected index)).inter
        (finalShading.measurable_carrier index)
  subset_body index := by
    intro point pointMem
    let ordinary :=
      ordinaryIndex normalized selected index
    have ordinaryMem :
        point ∈
          normalized.frame ''
            (normalized.selected.family.tube ordinary).carrier := by
      rcases pointMem.1 with ⟨sourcePoint, sourcePointMem, rfl⟩
      exact
        ⟨sourcePoint,
          normalized.ordinaryRefined.subset_body
            ordinary sourcePointMem,
          rfl⟩
    have indexEq :
        normalized.indexEquiv ordinary =
          selected.embedding index :=
      normalized.indexEquiv.apply_symm_apply
        (selected.embedding index)
    have carrierEq :
        (normalized.croppedFamily.tube
            (selected.embedding index)).carrier =
          normalized.frame ''
            (normalized.selected.family.tube ordinary).carrier := by
      rw [← indexEq]
      exact normalized.ordinary_carrier_image_eq ordinary
    change point ∈ (selected.family.tube index).carrier
    rw [selected.tube_eq index, carrierEq]
    exact ordinaryMem

theorem finalOrdinaryTrace_carrier
    (index : Fin selected.family.card) :
    (normalized.finalOrdinaryTrace selected finalShading).carrier index =
      (normalized.frame ''
        normalized.ordinaryRefined.carrier
          (ordinaryIndex normalized selected index)) ∩
        finalShading.carrier index :=
  rfl

/--
The per-tube ordinary density stored by normalization is preserved by the
common rigid frame and restricts to every later selected cropped subfamily.
-/
theorem framed_ordinary_per_tube
    (index : Fin selected.family.card) :
    (Kakeya.realRpowENN delta inputLoss / 2) *
          volume
            (normalized.croppedFamily.tube
              (selected.embedding index)).carrier ≤
      volume
        (normalized.frame ''
          normalized.ordinaryRefined.carrier
            (ordinaryIndex normalized selected index)) := by
  let ordinary := ordinaryIndex normalized selected index
  have indexEq :
      normalized.indexEquiv ordinary =
        selected.embedding index :=
    normalized.indexEquiv.apply_symm_apply
      (selected.embedding index)
  have sourceDensity := normalized.ordinary_per_tube ordinary
  rw [← indexEq, normalized.ordinary_carrier_image_eq ordinary]
  rw [
    Kakeya.Streamlined.AffineIsometryEquiv.volume_image
      normalized.frame
      (normalized.selected.family.tube ordinary).carrier
      (wz2_paper_ordinary_tube_carrier_measurable
        (normalized.selected.family.tube ordinary)
        normalized.final_extremal.delta_pos),
    Kakeya.Streamlined.AffineIsometryEquiv.volume_image
      normalized.frame
      (normalized.ordinaryRefined.carrier ordinary)
      (normalized.ordinaryRefined.measurable_carrier ordinary)
  ]
  exact sourceDensity

/--
Every final cubical carrier inherits the defining dense-cubical trace lower
bound from its normalized ordinary source carrier.
-/
theorem finalOrdinaryTrace_volume_lower
    (hdelta : 0 < delta)
    (finalCubical : WZ1PaperIsCubicalShading finalShading)
    (finalSubset :
      ∀ index,
        finalShading.carrier index ⊆
          normalized.croppedRefined.carrier
            (selected.embedding index))
    (index : Fin selected.family.card) :
    (100 : ENNReal)⁻¹ *
          volume
            (normalized.frame ''
              normalized.ordinaryRefined.carrier
                (ordinaryIndex normalized selected index)) *
          (volume
            (normalized.croppedFamily.tube
              (selected.embedding index)).carrier)⁻¹ *
          volume (finalShading.carrier index) ≤
      volume
        ((normalized.finalOrdinaryTrace
          selected finalShading).carrier index) := by
  let ordinary :=
    ordinaryIndex normalized selected index
  have indexEq :
      normalized.indexEquiv ordinary =
        selected.embedding index :=
    normalized.indexEquiv.apply_symm_apply
      (selected.embedding index)
  have denseSubset :
      finalShading.carrier index ⊆
        pureWZ2DenseCubicalization
          (normalized.croppedFamily.tube
            (selected.embedding index))
          (normalized.frame ''
            normalized.ordinaryRefined.carrier ordinary) := by
    intro point pointMem
    have croppedMem := finalSubset index pointMem
    have normalizedEq :=
      normalized.cropped_carrier_eq_dense_cubicalization ordinary
    rw [indexEq] at normalizedEq
    rwa [normalizedEq] at croppedMem
  exact
    pureWZ2_dense_cubical_trace
      hdelta
      (normalized.croppedFamily.tube
        (selected.embedding index))
      (normalized.frame ''
        normalized.ordinaryRefined.carrier ordinary)
      (finalShading.carrier index)
      (frame_image_measurable normalized ordinary)
      (finalShading.measurable_carrier index)
      (finalCubical index)
      denseSubset

/--
Uniform per-tube ordinary density turns the pointwise trace estimates into
one aggregate mass comparison on the exact final indexed family.
-/
theorem finalOrdinaryTrace_mass_lower
    (hdelta : 0 < delta)
    (finalCubical : WZ1PaperIsCubicalShading finalShading)
    (finalSubset :
      ∀ index,
        finalShading.carrier index ⊆
          normalized.croppedRefined.carrier
            (selected.embedding index))
    (density : ENNReal)
    (ordinaryPerTube :
      ∀ index : Fin selected.family.card,
        density *
            volume
              (normalized.croppedFamily.tube
                (selected.embedding index)).carrier ≤
          volume
            (normalized.frame ''
              normalized.ordinaryRefined.carrier
                (ordinaryIndex normalized selected index))) :
    (100 : ENNReal)⁻¹ * density * finalShading.mass ≤
      (normalized.finalOrdinaryTrace
        selected finalShading).mass := by
  have perTube :
      ∀ index : Fin selected.family.card,
        (100 : ENNReal)⁻¹ * density *
              volume (finalShading.carrier index) ≤
          volume
            ((normalized.finalOrdinaryTrace
              selected finalShading).carrier index) := by
    intro index
    let tube :=
      normalized.croppedFamily.tube
        (selected.embedding index)
    let ordinarySource :=
      normalized.frame ''
        normalized.ordinaryRefined.carrier
          (ordinaryIndex normalized selected index)
    have tubeVolumePos :
        0 < volume tube.carrier :=
      wz2_paper_ordinary_tube_volume_pos tube hdelta
    have tubeVolumeTop :
        volume tube.carrier ≠ ⊤ :=
      wz2_paper_ordinary_tube_volume_ne_top tube hdelta
    have densityRatio :
        density ≤
          volume ordinarySource *
            (volume tube.carrier)⁻¹ := by
      have scaled :=
        mul_le_mul_right'
          (ordinaryPerTube index)
          (volume tube.carrier)⁻¹
      calc
        density =
            (density * volume tube.carrier) *
              (volume tube.carrier)⁻¹ := by
          rw [mul_assoc,
            ENNReal.mul_inv_cancel
              tubeVolumePos.ne' tubeVolumeTop,
            mul_one]
        _ ≤
            volume ordinarySource *
              (volume tube.carrier)⁻¹ := scaled
    calc
      (100 : ENNReal)⁻¹ * density *
            volume (finalShading.carrier index) ≤
          ((100 : ENNReal)⁻¹ *
              (volume ordinarySource *
                (volume tube.carrier)⁻¹)) *
              volume (finalShading.carrier index) := by
        exact
          mul_le_mul_right'
            (mul_le_mul_left'
              densityRatio (100 : ENNReal)⁻¹)
            (volume (finalShading.carrier index))
      _ =
          (100 : ENNReal)⁻¹ *
              volume ordinarySource *
              (volume tube.carrier)⁻¹ *
              volume (finalShading.carrier index) := by
        ring
      _ ≤
          volume
            ((normalized.finalOrdinaryTrace
              selected finalShading).carrier index) := by
        exact
          normalized.finalOrdinaryTrace_volume_lower
            selected finalShading hdelta finalCubical finalSubset index
  change
    (100 : ENNReal)⁻¹ * density *
          (∑ index : Fin selected.family.card,
            volume (finalShading.carrier index)) ≤
      ∑ index : Fin selected.family.card,
        volume
          ((normalized.finalOrdinaryTrace
            selected finalShading).carrier index)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun index _ => perTube index

/--
The canonical normalization density specializes the aggregate trace lower
bound without any additional geometric hypothesis.
-/
theorem finalOrdinaryTrace_mass_lower_normalized
    (hdelta : 0 < delta)
    (finalCubical : WZ1PaperIsCubicalShading finalShading)
    (finalSubset :
      ∀ index,
        finalShading.carrier index ⊆
          normalized.croppedRefined.carrier
            (selected.embedding index)) :
    (100 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta inputLoss / 2) *
          finalShading.mass ≤
      (normalized.finalOrdinaryTrace
        selected finalShading).mass :=
  normalized.finalOrdinaryTrace_mass_lower
    selected finalShading hdelta finalCubical finalSubset
    (Kakeya.realRpowENN delta inputLoss / 2)
    (normalized.framed_ordinary_per_tube selected)

end PureWZ2CroppedCriticalNormalizationData

end Kakeya.Assouad

end
