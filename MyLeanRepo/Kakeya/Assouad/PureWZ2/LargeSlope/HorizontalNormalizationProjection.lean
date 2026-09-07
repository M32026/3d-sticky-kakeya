import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicCenteredMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicProjectionIdentity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalNormalizationAffineEquiv
import MyLeanRepo.Kakeya.Assouad.PureWZ2.IntervalSlopeRescaling

/-!
# Slope-preserving horizontal normalization after the Section-6 map

The exact triangular map in Proposition 6.5 already normalizes the slope
derivative.  If its transported plane map has a large Lipschitz constant, the
permitted Lemma-3.5 normalization can be chosen as the diagonal map

`(x, y, z) ↦ (lambda * x, lambda * y, z)`.

Scaling the two horizontal coordinates equally and leaving height unchanged
preserves the transformed slope (and hence its derivative bounds), while it
expands precisely the small horizontal singular directions of the triangular
map.  This module records the exact projection covariance needed by the final
global-AD transport.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The exact slope after horizontal normalization.  There is no multiplicative
or height-reparameterization factor. -/
def pureWZ2HorizontalNormalizedSlope
    (geometrySlope : SlopeFunction) (sourceSlope : ℝ → ℝ) (c d m : ℝ)
    (horizontalCenter : Point3) (t : ℝ) : ℝ :=
  anisotropicRescaledSlopeWithShear sourceSlope c d m
    (geometrySlope (c + (d - c) / 2)) (horizontalCenter 2 + t)

/-- Target height under the combined map is equivalent to the corresponding
source height. -/
theorem pureWZ2HorizontalNormalizedMap_coord_two_iff
    (g : SlopeFunction) {c d m : ℝ}
    (hcd : c < d)
    (anisotropicCenter horizontalCenter point : Point3) (lambda t : ℝ) :
    pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
        horizontalCenter lambda point 2 = t ↔
      point 2 = c + (d - c) / 2 *
        (horizontalCenter 2 + t + 1) := by
  have hcoord :
      anisotropicCenteredRescalingMap g c d m anisotropicCenter point 2 =
        2 * (point 2 - c) / (d - c) - 1 := by
    unfold anisotropicCenteredRescalingMap
    rw [PiLp.sub_apply, (anisotropicRescalingMap_coord g c d m point).2.2]
    simp [point3]
  rw [show pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
        horizontalCenter lambda point 2 =
      anisotropicCenteredRescalingMap g c d m anisotropicCenter point 2 -
        horizontalCenter 2 by
    simp [pureWZ2HorizontalNormalizedMap, point3]]
  rw [hcoord]
  have hdc : d - c ≠ 0 := sub_ne_zero.mpr hcd.ne'
  constructor <;> intro h <;> field_simp [hdc] at h ⊢ <;> linarith

/-- Translation term in the scalar-projection covariance. -/
def pureWZ2HorizontalNormalizedProjectionOffset
    (geometrySlope : SlopeFunction) (sourceSlope : ℝ → ℝ) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3)
    (lambda t : ℝ) : ℝ :=
  -lambda *
    (anisotropicRescalingMap geometrySlope c d m anisotropicCenter 0 +
      horizontalCenter 0 +
      anisotropicRescaledSlopeWithShear sourceSlope c d m
          (geometrySlope (c + (d - c) / 2)) (horizontalCenter 2 + t) *
        horizontalCenter 1)

/-- Pointwise covariance of scalar projection under horizontal normalization. -/
theorem pureWZ2HorizontalNormalized_projection_pointwise
    (geometrySlope : SlopeFunction) (sourceSlope : ℝ → ℝ)
    {c d m lambda : ℝ}
    (hcd : c < d) (hm : 0 < m)
    (anisotropicCenter horizontalCenter point : Point3) (t : ℝ)
    (hheight : pureWZ2HorizontalNormalizedMap geometrySlope c d m anisotropicCenter
      horizontalCenter lambda point 2 = t) :
    inner ℝ
        (pureWZ2HorizontalNormalizedMap geometrySlope c d m anisotropicCenter
          horizontalCenter lambda point)
        (globalGrainDirection
          (pureWZ2HorizontalNormalizedSlope geometrySlope sourceSlope c d m
            horizontalCenter t)) =
      lambda * inner ℝ point
          (globalGrainDirection (sourceSlope (point 2))) +
        pureWZ2HorizontalNormalizedProjectionOffset geometrySlope sourceSlope
          c d m anisotropicCenter horizontalCenter lambda t := by
  have hsourceHeight :=
    (pureWZ2HorizontalNormalizedMap_coord_two_iff geometrySlope hcd
      anisotropicCenter horizontalCenter point lambda t).mp hheight
  have hanisotropic := anisotropic_projection_pointwise_withShear
    (c := c) (d := d) (m := m) geometrySlope sourceSlope hcd hm
      (horizontalCenter 2 + t) point hsourceHeight
  let image := anisotropicCenteredRescalingMap geometrySlope c d m
    anisotropicCenter point
  let exactSlope := anisotropicRescaledSlopeWithShear sourceSlope c d m
    (geometrySlope (c + (d - c) / 2)) (horizontalCenter 2 + t)
  have himageZero : image 0 =
      anisotropicRescalingMap geometrySlope c d m point 0 -
        anisotropicRescalingMap geometrySlope c d m anisotropicCenter 0 := by
    simp [image, anisotropicCenteredRescalingMap, point3]
  have himageOne : image 1 =
      anisotropicRescalingMap geometrySlope c d m point 1 := by
    simp [image, anisotropicCenteredRescalingMap, point3]
  have hprojection : inner ℝ image (globalGrainDirection exactSlope) =
      inner ℝ point (globalGrainDirection (sourceSlope (point 2))) -
        anisotropicRescalingMap geometrySlope c d m anisotropicCenter 0 := by
    have hleft : inner ℝ image (globalGrainDirection exactSlope) =
        image 0 + exactSlope * image 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    have hright : inner ℝ
          (anisotropicRescalingMap geometrySlope c d m point)
          (globalGrainDirection exactSlope) =
        anisotropicRescalingMap geometrySlope c d m point 0 +
          exactSlope * anisotropicRescalingMap geometrySlope c d m point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    rw [hleft, himageZero, himageOne]
    calc
      anisotropicRescalingMap geometrySlope c d m point 0 -
            anisotropicRescalingMap geometrySlope c d m anisotropicCenter 0 +
          exactSlope * anisotropicRescalingMap geometrySlope c d m point 1 =
          (anisotropicRescalingMap geometrySlope c d m point 0 +
            exactSlope * anisotropicRescalingMap geometrySlope c d m point 1) -
              anisotropicRescalingMap geometrySlope c d m anisotropicCenter 0 := by ring
      _ = inner ℝ
            (anisotropicRescalingMap geometrySlope c d m point)
            (globalGrainDirection exactSlope) -
              anisotropicRescalingMap geometrySlope c d m anisotropicCenter 0 := by
          rw [hright]
      _ = _ := by rw [hanisotropic]
  have htarget :
      inner ℝ
          (pureWZ2HorizontalNormalizedMap geometrySlope c d m anisotropicCenter
            horizontalCenter lambda point)
          (globalGrainDirection
            (pureWZ2HorizontalNormalizedSlope geometrySlope sourceSlope c d m
              horizontalCenter t)) =
        lambda *
          (inner ℝ image (globalGrainDirection exactSlope) -
            horizontalCenter 0 - exactSlope * horizontalCenter 1) := by
    rw [show inner ℝ
        (pureWZ2HorizontalNormalizedMap geometrySlope c d m anisotropicCenter
          horizontalCenter lambda point)
        (globalGrainDirection
          (pureWZ2HorizontalNormalizedSlope geometrySlope sourceSlope c d m
            horizontalCenter t)) =
      (pureWZ2HorizontalNormalizedMap geometrySlope c d m anisotropicCenter
          horizontalCenter lambda point) 0 +
        pureWZ2HorizontalNormalizedSlope geometrySlope sourceSlope c d m
          horizontalCenter t *
          (pureWZ2HorizontalNormalizedMap geometrySlope c d m anisotropicCenter
            horizontalCenter lambda point) 1 by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]]
    rw [show (pureWZ2HorizontalNormalizedMap geometrySlope c d m anisotropicCenter
          horizontalCenter lambda point) 0 =
        lambda * (image 0 - horizontalCenter 0) by
      simp [pureWZ2HorizontalNormalizedMap, image, point3]]
    rw [show (pureWZ2HorizontalNormalizedMap geometrySlope c d m anisotropicCenter
          horizontalCenter lambda point) 1 =
        lambda * (image 1 - horizontalCenter 1) by
      simp [pureWZ2HorizontalNormalizedMap, image, point3]]
    change lambda * (image 0 - horizontalCenter 0) +
        exactSlope * (lambda * (image 1 - horizontalCenter 1)) = _
    rw [show inner ℝ image (globalGrainDirection exactSlope) =
        image 0 + exactSlope * image 1 by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]]
    ring
  rw [htarget, hprojection]
  dsimp only [pureWZ2HorizontalNormalizedProjectionOffset, exactSlope]
  ring

/-- Set-level covariance.  The target slope is unchanged (up to a height
translation), and the scalar projection is dilated by the positive factor
`lambda`. -/
theorem pureWZ2HorizontalNormalized_projection_set
    (geometrySlope : SlopeFunction) (sourceSlope : ℝ → ℝ)
    {c d m lambda : ℝ}
    (hcd : c < d) (hm : 0 < m)
    (anisotropicCenter horizontalCenter : Point3)
    (source : Set Point3) (t : ℝ) :
    scalarProjection
        (globalGrainDirection
          (pureWZ2HorizontalNormalizedSlope geometrySlope sourceSlope c d m
            horizontalCenter t))
        (horizontalSlice
          (pureWZ2HorizontalNormalizedMap geometrySlope c d m anisotropicCenter
            horizontalCenter lambda '' source) t) =
      (fun value : ℝ => lambda * value +
        pureWZ2HorizontalNormalizedProjectionOffset geometrySlope sourceSlope
          c d m anisotropicCenter horizontalCenter lambda t) ''
        scalarProjection
          (globalGrainDirection
            (sourceSlope (c + (d - c) / 2 *
              (horizontalCenter 2 + t + 1))))
          (horizontalSlice source
            (c + (d - c) / 2 *
              (horizontalCenter 2 + t + 1))) := by
  ext value
  constructor
  · rintro ⟨target, ⟨⟨sourcePoint, hsourcePoint, rfl⟩, hheight⟩, rfl⟩
    have hsourceHeight :=
      (pureWZ2HorizontalNormalizedMap_coord_two_iff geometrySlope hcd
        anisotropicCenter horizontalCenter sourcePoint lambda t).mp hheight
    refine ⟨inner ℝ sourcePoint
        (globalGrainDirection (sourceSlope (sourcePoint 2))), ?_, ?_⟩
    · exact ⟨sourcePoint, ⟨hsourcePoint, hsourceHeight⟩, by rw [hsourceHeight]⟩
    · exact (pureWZ2HorizontalNormalized_projection_pointwise geometrySlope
        sourceSlope hcd hm
        anisotropicCenter horizontalCenter sourcePoint t hheight).symm
  · rintro ⟨sourceValue,
      ⟨sourcePoint, ⟨hsourcePoint, hsourceHeight⟩, rfl⟩, rfl⟩
    have hheight : pureWZ2HorizontalNormalizedMap geometrySlope c d m anisotropicCenter
        horizontalCenter lambda sourcePoint 2 = t :=
      (pureWZ2HorizontalNormalizedMap_coord_two_iff geometrySlope hcd
        anisotropicCenter horizontalCenter sourcePoint lambda t).mpr hsourceHeight
    refine ⟨pureWZ2HorizontalNormalizedMap geometrySlope c d m anisotropicCenter
        horizontalCenter lambda sourcePoint,
      ⟨⟨sourcePoint, hsourcePoint, rfl⟩, hheight⟩, ?_⟩
    rw [← hsourceHeight]
    exact pureWZ2HorizontalNormalized_projection_pointwise geometrySlope
      sourceSlope hcd hm
      anisotropicCenter horizontalCenter sourcePoint t hheight

/-- The same projection-slope identity for the interval-local Node-5 route.
The affine map only reads the source slope at the selected midpoint, so the
constant `geometrySlope` stored by `PureWZ2HorizontalSourceData` is enough. -/
theorem PureWZ2HorizontalSourceData.horizontalNormalizedSlope_eq
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (data : PureWZ2HorizontalSourceData cfg)
    (horizontalCenter : Point3) (hcenter : horizontalCenter 2 = 0)
    (t : PureWZ2UnitInterval) :
    pureWZ2HorizontalNormalizedSlope data.geometrySlope data.globalSlope
        data.c data.d data.m horizontalCenter t.1 = data.f t := by
  rw [data.f_formula]
  simp [pureWZ2HorizontalNormalizedSlope, hcenter]

end Kakeya.Assouad

end
