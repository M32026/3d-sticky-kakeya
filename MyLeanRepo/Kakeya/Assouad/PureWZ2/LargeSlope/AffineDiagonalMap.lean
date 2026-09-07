import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperHorizontalRotation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DiagonalRescaling
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperIsotropicLocalAD
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Paper-faithful affine diagonal map after Lemma 32

The map composes a height translation, one fixed horizontal orthogonal
rotation, an axis-parallel diagonal dilation, and an isotropic dilation.
No shear occurs. The complete configuration is transported by this same map.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- Source height corresponding to a target height for a centered height
dilation.  The paper uses `heightScale = 100 / m`; the active source interval
is only mapped into a target subinterval and is not forced to fill `[-1,1]`. -/
def pureWZ2AffineDiagonalSourceHeight
    (c d heightScale t : ℝ) : ℝ :=
  (c + d) / 2 + t / heightScale

/-- Horizontal slope after rotating the direction (1,a,0) to the x-axis. -/
def pureWZ2RotatedSlopeValue (a value : ℝ) : ℝ :=
  (value - a) / (1 + a * value)

/-- The paper affine diagonal map with an additional positive isotropic
normalization factor. -/
def pureWZ2AffineDiagonalMapCentered
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale isotropicScale : ℝ)
    (point : Point3) : Point3 :=
  let rotated := pureWZ2HorizontalRotation frameSlope (point - center)
  point3
    (isotropicScale * rotated 0)
    (isotropicScale * transverseScale * rotated 1)
    (isotropicScale * heightScale * rotated 2)

/-- Height-only centering used by the slope covariance layer. -/
def pureWZ2AffineDiagonalMapAt
    (frameSlope anchor heightScale transverseScale isotropicScale : ℝ)
    (point : Point3) : Point3 :=
  let translated := point3 (point 0) (point 1) (point 2 - anchor)
  let rotated := pureWZ2HorizontalRotation frameSlope translated
  point3
    (isotropicScale * rotated 0)
    (isotropicScale * transverseScale * rotated 1)
    (isotropicScale * heightScale * rotated 2)

/-- Midpoint-compatible wrapper for the affine diagonal map. -/
def pureWZ2AffineDiagonalMap
    (frameSlope c d heightScale transverseScale isotropicScale : ℝ)
    (point : Point3) : Point3 :=
  pureWZ2AffineDiagonalMapAt frameSlope ((c + d) / 2) heightScale
    transverseScale isotropicScale point

/-- The translation center of the affine-diagonal map. -/
def pureWZ2AffineDiagonalCenter (c d : ℝ) : Point3 :=
  point3 0 0 ((c + d) / 2)

/-- Linear part of the paper affine-diagonal map. -/
def pureWZ2AffineDiagonalLinear
    (frameSlope heightScale transverseScale isotropicScale : ℝ)
    (vector : Point3) : Point3 :=
  let rotated := pureWZ2HorizontalRotation frameSlope vector
  point3
    (isotropicScale * rotated 0)
    (isotropicScale * transverseScale * rotated 1)
    (isotropicScale * heightScale * rotated 2)

theorem pureWZ2AffineDiagonalLinear_add
    (frameSlope heightScale transverseScale isotropicScale : ℝ)
    (first second : Point3) :
    pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale
        isotropicScale (first + second) =
      pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale
          isotropicScale first +
        pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale
          isotropicScale second := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2AffineDiagonalLinear, point3, map_add] <;> ring

theorem pureWZ2AffineDiagonalLinear_smul
    (frameSlope heightScale transverseScale isotropicScale scalar : ℝ)
    (vector : Point3) :
    pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale
        isotropicScale (scalar • vector) =
      scalar • pureWZ2AffineDiagonalLinear frameSlope heightScale
        transverseScale isotropicScale vector := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2AffineDiagonalLinear, point3, map_smul] <;> ring

theorem pureWZ2AffineDiagonalLinear_sub
    (frameSlope heightScale transverseScale isotropicScale : ℝ)
    (first second : Point3) :
    pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale
        isotropicScale (first - second) =
      pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale
          isotropicScale first -
        pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale
          isotropicScale second := by
  rw [sub_eq_add_neg, sub_eq_add_neg, pureWZ2AffineDiagonalLinear_add]
  have hneg := pureWZ2AffineDiagonalLinear_smul frameSlope heightScale
    transverseScale isotropicScale (-1) second
  simpa using hneg

theorem pureWZ2AffineDiagonalMapCentered_eq_linear_sub_center
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale isotropicScale : ℝ)
    (point : Point3) :
    pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale isotropicScale point =
      pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale
        isotropicScale (point - center) := by
  rfl

theorem pureWZ2AffineDiagonalMapCentered_add_smul
    (frameSlope : ℝ) (center base direction : Point3)
    (heightScale transverseScale isotropicScale scalar : ℝ) :
    pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale isotropicScale (base + scalar • direction) =
      pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale isotropicScale base +
        scalar • pureWZ2AffineDiagonalLinear frameSlope heightScale
          transverseScale isotropicScale direction := by
  rw [pureWZ2AffineDiagonalMapCentered_eq_linear_sub_center,
    pureWZ2AffineDiagonalMapCentered_eq_linear_sub_center]
  rw [show base + scalar • direction - center =
      (base - center) + scalar • direction by module]
  rw [pureWZ2AffineDiagonalLinear_add,
    pureWZ2AffineDiagonalLinear_smul]

theorem pureWZ2AffineDiagonalMapCentered_sub
    (frameSlope : ℝ) (center first second : Point3)
    (heightScale transverseScale isotropicScale : ℝ) :
    pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale isotropicScale first -
        pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale isotropicScale second =
      pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale
        isotropicScale (first - second) := by
  rw [pureWZ2AffineDiagonalMapCentered_eq_linear_sub_center,
    pureWZ2AffineDiagonalMapCentered_eq_linear_sub_center,
    ← pureWZ2AffineDiagonalLinear_sub]
  congr 1
  abel

/-- Inverse of the linear part. -/
def pureWZ2AffineDiagonalLinearInverse
    (frameSlope heightScale transverseScale isotropicScale : ℝ)
    (vector : Point3) : Point3 :=
  (pureWZ2HorizontalRotation frameSlope).symm
    (point3
      (vector 0 / isotropicScale)
      (vector 1 / (isotropicScale * transverseScale))
      (vector 2 / (isotropicScale * heightScale)))

/-- Inverse transpose of the linear part.  Notice that the source normal is
rotated by the same fixed rotation as the source configuration and then by
the reciprocal diagonal factors. -/
def pureWZ2AffineDiagonalInvTranspose
    (frameSlope heightScale transverseScale isotropicScale : ℝ)
    (normal : Point3) : Point3 :=
  let rotated := pureWZ2HorizontalRotation frameSlope normal
  point3
    (rotated 0 / isotropicScale)
    (rotated 1 / (isotropicScale * transverseScale))
    (rotated 2 / (isotropicScale * heightScale))

/-- Linear-map packaging of the inverse transpose. -/
def pureWZ2AffineDiagonalInvTransposeLinear
    (frameSlope heightScale transverseScale isotropicScale : ℝ) :
    Point3 →ₗ[ℝ] Point3 where
  toFun := pureWZ2AffineDiagonalInvTranspose frameSlope heightScale
    transverseScale isotropicScale
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2AffineDiagonalInvTranspose, point3, map_add] <;> ring
  map_smul' scalar normal := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2AffineDiagonalInvTranspose, point3, map_smul] <;> ring

@[simp] theorem pureWZ2AffineDiagonalInvTransposeLinear_apply
    (frameSlope heightScale transverseScale isotropicScale : ℝ)
    (normal : Point3) :
    pureWZ2AffineDiagonalInvTransposeLinear frameSlope heightScale
        transverseScale isotropicScale normal =
      pureWZ2AffineDiagonalInvTranspose frameSlope heightScale
        transverseScale isotropicScale normal := rfl

/-- The inverse transpose is globally Lipschitz with its operator norm. -/
theorem pureWZ2AffineDiagonalInvTranspose_lipschitz
    (frameSlope heightScale transverseScale isotropicScale : ℝ) :
    LipschitzWith
      ‖(pureWZ2AffineDiagonalInvTransposeLinear frameSlope heightScale
          transverseScale isotropicScale).toContinuousLinearMap‖₊
      (pureWZ2AffineDiagonalInvTranspose frameSlope heightScale
        transverseScale isotropicScale) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [dist_eq_norm, dist_eq_norm]
  have hsub :
      pureWZ2AffineDiagonalInvTranspose frameSlope heightScale
            transverseScale isotropicScale first -
          pureWZ2AffineDiagonalInvTranspose frameSlope heightScale
            transverseScale isotropicScale second =
        pureWZ2AffineDiagonalInvTranspose frameSlope heightScale
          transverseScale isotropicScale (first - second) := by
    rw [← pureWZ2AffineDiagonalInvTransposeLinear_apply,
      ← pureWZ2AffineDiagonalInvTransposeLinear_apply,
      ← pureWZ2AffineDiagonalInvTransposeLinear_apply, map_sub]
  rw [hsub]
  change
    ‖(pureWZ2AffineDiagonalInvTransposeLinear frameSlope heightScale
        transverseScale isotropicScale).toContinuousLinearMap
          (first - second)‖ ≤ _
  simpa only [coe_nnnorm] using
    (pureWZ2AffineDiagonalInvTransposeLinear frameSlope heightScale
      transverseScale isotropicScale).toContinuousLinearMap.le_opNorm
        (first - second)

/-- Explicit inverse of the affine map. -/
def pureWZ2AffineDiagonalInverse
    (frameSlope c d heightScale transverseScale isotropicScale : ℝ)
    (target : Point3) : Point3 :=
  pureWZ2AffineDiagonalCenter c d +
    pureWZ2AffineDiagonalLinearInverse frameSlope heightScale
      transverseScale isotropicScale target

theorem pureWZ2AffineDiagonalMap_eq_linear_sub_center
    (frameSlope c d heightScale transverseScale isotropicScale : ℝ)
    (point : Point3) :
    pureWZ2AffineDiagonalMap frameSlope c d heightScale transverseScale
        isotropicScale
        point =
      pureWZ2AffineDiagonalLinear frameSlope heightScale
        transverseScale isotropicScale
        (point - pureWZ2AffineDiagonalCenter c d) := by
  have htranslated : point3 (point 0) (point 1)
        (point 2 - (c + d) / 2) =
      point - pureWZ2AffineDiagonalCenter c d := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2AffineDiagonalCenter, point3]
  simp only [pureWZ2AffineDiagonalMap, pureWZ2AffineDiagonalMapAt,
    pureWZ2AffineDiagonalLinear]
  rw [htranslated]

theorem pureWZ2AffineDiagonalMapAt_eq_linear_sub_center
    (frameSlope anchor heightScale transverseScale isotropicScale : ℝ)
    (point : Point3) :
    pureWZ2AffineDiagonalMapAt frameSlope anchor heightScale transverseScale
        isotropicScale point =
      pureWZ2AffineDiagonalLinear frameSlope heightScale
        transverseScale isotropicScale
        (point - point3 0 0 anchor) := by
  have htranslated : point3 (point 0) (point 1) (point 2 - anchor) =
      point - point3 0 0 anchor := by
    ext coordinate
    fin_cases coordinate <;> simp [point3]
  simp only [pureWZ2AffineDiagonalMapAt, pureWZ2AffineDiagonalLinear]
  rw [htranslated]

theorem pureWZ2AffineDiagonalLinear_inverse
    (frameSlope : ℝ)
    {heightScale transverseScale isotropicScale : ℝ}
    (hheight : heightScale ≠ 0)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : isotropicScale ≠ 0)
    (vector : Point3) :
    pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale
        isotropicScale
        (pureWZ2AffineDiagonalLinearInverse frameSlope heightScale
          transverseScale isotropicScale vector) = vector := by
  have hrotation : pureWZ2HorizontalRotation frameSlope
      ((pureWZ2HorizontalRotation frameSlope).symm
        (point3
          (vector 0 / isotropicScale)
          (vector 1 / (isotropicScale * transverseScale))
          (vector 2 / (isotropicScale * heightScale)))) =
      point3
        (vector 0 / isotropicScale)
        (vector 1 / (isotropicScale * transverseScale))
        (vector 2 / (isotropicScale * heightScale)) :=
    (pureWZ2HorizontalRotation frameSlope).apply_symm_apply _
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2AffineDiagonalLinear,
      pureWZ2AffineDiagonalLinearInverse, hrotation, point3] <;>
    field_simp [hheight, htransverse, hisotropic] <;> ring

theorem pureWZ2AffineDiagonalLinearInverse_linear
    (frameSlope : ℝ)
    {heightScale transverseScale isotropicScale : ℝ}
    (hheight : heightScale ≠ 0)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : isotropicScale ≠ 0)
    (vector : Point3) :
    pureWZ2AffineDiagonalLinearInverse frameSlope heightScale
        transverseScale isotropicScale
        (pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale
          isotropicScale vector) = vector := by
  apply (pureWZ2HorizontalRotation frameSlope).injective
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2AffineDiagonalLinear,
      pureWZ2AffineDiagonalLinearInverse, point3] <;>
    field_simp [hheight, htransverse, hisotropic] <;> ring

/-- The invertible linear part of the centered affine diagonal map. -/
noncomputable def pureWZ2AffineDiagonalLinearEquiv
    (frameSlope heightScale transverseScale isotropicScale : ℝ)
    (hheight : heightScale ≠ 0)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : isotropicScale ≠ 0) :
    Point3 ≃ₗ[ℝ] Point3 where
  toFun := pureWZ2AffineDiagonalLinear frameSlope heightScale
    transverseScale isotropicScale
  invFun := pureWZ2AffineDiagonalLinearInverse frameSlope heightScale
    transverseScale isotropicScale
  left_inv := pureWZ2AffineDiagonalLinearInverse_linear frameSlope
    hheight htransverse hisotropic
  right_inv := pureWZ2AffineDiagonalLinear_inverse frameSlope
    hheight htransverse hisotropic
  map_add' := pureWZ2AffineDiagonalLinear_add frameSlope heightScale
    transverseScale isotropicScale
  map_smul' := pureWZ2AffineDiagonalLinear_smul frameSlope heightScale
    transverseScale isotropicScale

/-- The centered paper map as an affine equivalence. -/
noncomputable def pureWZ2AffineDiagonalAffineEquivCentered
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale isotropicScale : ℝ)
    (hheight : heightScale ≠ 0)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : isotropicScale ≠ 0) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  AffineEquiv.ofLinearEquiv
    (pureWZ2AffineDiagonalLinearEquiv frameSlope heightScale
      transverseScale isotropicScale hheight htransverse hisotropic)
    center 0

@[simp] theorem pureWZ2AffineDiagonalAffineEquivCentered_apply
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale isotropicScale : ℝ)
    (hheight : heightScale ≠ 0)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : isotropicScale ≠ 0)
    (point : Point3) :
    pureWZ2AffineDiagonalAffineEquivCentered frameSlope center heightScale
        transverseScale isotropicScale hheight htransverse hisotropic point =
      pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale isotropicScale point := by
  rw [pureWZ2AffineDiagonalAffineEquivCentered,
    AffineEquiv.ofLinearEquiv_apply]
  simp [pureWZ2AffineDiagonalLinearEquiv,
    pureWZ2AffineDiagonalMapCentered_eq_linear_sub_center]

@[simp] theorem pureWZ2AffineDiagonalMap_inverse
    (frameSlope : ℝ) {c d heightScale transverseScale isotropicScale : ℝ}
    (hcd : c < d)
    (hheight : heightScale ≠ 0)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : isotropicScale ≠ 0)
    (target : Point3) :
    pureWZ2AffineDiagonalMap frameSlope c d heightScale transverseScale
        isotropicScale
        (pureWZ2AffineDiagonalInverse frameSlope c d heightScale
          transverseScale isotropicScale target) = target := by
  rw [pureWZ2AffineDiagonalMap_eq_linear_sub_center]
  have hsub : pureWZ2AffineDiagonalInverse frameSlope c d heightScale
        transverseScale isotropicScale target -
        pureWZ2AffineDiagonalCenter c d =
      pureWZ2AffineDiagonalLinearInverse frameSlope heightScale
        transverseScale isotropicScale target := by
    simp [pureWZ2AffineDiagonalInverse]
  rw [hsub]
  exact pureWZ2AffineDiagonalLinear_inverse frameSlope hheight htransverse
    hisotropic target

@[simp] theorem pureWZ2AffineDiagonalInverse_map
    (frameSlope : ℝ) {c d heightScale transverseScale isotropicScale : ℝ}
    (hcd : c < d)
    (hheight : heightScale ≠ 0)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : isotropicScale ≠ 0)
    (source : Point3) :
    pureWZ2AffineDiagonalInverse frameSlope c d heightScale transverseScale
        isotropicScale
        (pureWZ2AffineDiagonalMap frameSlope c d heightScale transverseScale
          isotropicScale source) = source := by
  rw [pureWZ2AffineDiagonalMap_eq_linear_sub_center]
  simp only [pureWZ2AffineDiagonalInverse]
  rw [pureWZ2AffineDiagonalLinearInverse_linear frameSlope hheight
    htransverse hisotropic]
  abel

/-- Exact covariance of directions and normals. -/
theorem pureWZ2AffineDiagonal_inner_identity
    (frameSlope : ℝ)
    {heightScale transverseScale isotropicScale : ℝ}
    (hheight : heightScale ≠ 0)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : isotropicScale ≠ 0)
    (direction normal : Point3) :
    inner ℝ
        (pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale
          isotropicScale direction)
        (pureWZ2AffineDiagonalInvTranspose frameSlope heightScale
          transverseScale isotropicScale normal) =
      inner ℝ direction normal := by
  let rotation := pureWZ2HorizontalRotation frameSlope
  let rotatedDirection := rotation direction
  let rotatedNormal := rotation normal
  have hrotated : inner ℝ (rotation direction) (rotation normal) =
      inner ℝ direction normal := rotation.inner_map_map direction normal
  have hleft : inner ℝ
        (pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale
          isotropicScale direction)
        (pureWZ2AffineDiagonalInvTranspose frameSlope heightScale
          transverseScale isotropicScale normal) =
      inner ℝ (rotation direction) (rotation normal) := by
    change inner ℝ
        (point3
          (isotropicScale * rotatedDirection 0)
          (isotropicScale * transverseScale * rotatedDirection 1)
          (isotropicScale * heightScale * rotatedDirection 2))
        (point3
          (rotatedNormal 0 / isotropicScale)
          (rotatedNormal 1 / (isotropicScale * transverseScale))
          (rotatedNormal 2 / (isotropicScale * heightScale))) =
      inner ℝ rotatedDirection rotatedNormal
    simp [PiLp.inner_apply, Fin.sum_univ_succ, point3]
    field_simp [hheight, htransverse, hisotropic]
  rw [hleft, hrotated]

@[simp] theorem pureWZ2AffineDiagonalMap_coord_zero
    (frameSlope c d heightScale transverseScale isotropicScale : ℝ)
    (point : Point3) :
    pureWZ2AffineDiagonalMap frameSlope c d heightScale transverseScale
        isotropicScale point 0 =
      isotropicScale *
        ((point 0 + frameSlope * point 1) /
          pureWZ2HorizontalNorm frameSlope) := by
  simp [pureWZ2AffineDiagonalMap, pureWZ2AffineDiagonalMapAt,
    pureWZ2HorizontalRotation_coord_zero, point3]
  field_simp [pureWZ2HorizontalNorm_pos frameSlope |>.ne']
  all_goals ring_nf <;> simp

@[simp] theorem pureWZ2AffineDiagonalMapCentered_coord_zero
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale isotropicScale : ℝ)
    (hisotropic : isotropicScale ≠ 0)
    (point : Point3) :
    pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale isotropicScale point 0 =
      isotropicScale *
        (((point 0 - center 0) +
            frameSlope * (point 1 - center 1)) /
          pureWZ2HorizontalNorm frameSlope) := by
  simp [pureWZ2AffineDiagonalMapCentered,
    pureWZ2HorizontalRotation_coord_zero, point3, hisotropic]
  field_simp [pureWZ2HorizontalNorm_pos frameSlope |>.ne', hisotropic]
  ring

@[simp] theorem pureWZ2AffineDiagonalMapAt_coord_zero
    (frameSlope anchor heightScale transverseScale isotropicScale : ℝ)
    (point : Point3) :
    pureWZ2AffineDiagonalMapAt frameSlope anchor heightScale transverseScale
        isotropicScale point 0 =
      isotropicScale *
        ((point 0 + frameSlope * point 1) /
          pureWZ2HorizontalNorm frameSlope) := by
  simp [pureWZ2AffineDiagonalMapAt,
    pureWZ2HorizontalRotation_coord_zero, point3]
  field_simp [pureWZ2HorizontalNorm_pos frameSlope |>.ne']
  all_goals ring_nf <;> simp

@[simp] theorem pureWZ2AffineDiagonalMap_coord_one
    (frameSlope c d heightScale transverseScale isotropicScale : ℝ)
    (point : Point3) :
    pureWZ2AffineDiagonalMap frameSlope c d heightScale transverseScale
        isotropicScale point 1 =
      isotropicScale * transverseScale *
        ((-frameSlope * point 0 + point 1) /
          pureWZ2HorizontalNorm frameSlope) := by
  simp [pureWZ2AffineDiagonalMap, pureWZ2AffineDiagonalMapAt,
    pureWZ2HorizontalRotation_coord_one, point3]
  field_simp [pureWZ2HorizontalNorm_pos frameSlope |>.ne']
  all_goals ring_nf <;> simp

@[simp] theorem pureWZ2AffineDiagonalMapCentered_coord_one
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale isotropicScale : ℝ)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : isotropicScale ≠ 0)
    (point : Point3) :
    pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale isotropicScale point 1 =
      isotropicScale * transverseScale *
        ((-frameSlope * (point 0 - center 0) +
            (point 1 - center 1)) /
          pureWZ2HorizontalNorm frameSlope) := by
  simp [pureWZ2AffineDiagonalMapCentered,
    pureWZ2HorizontalRotation_coord_one, point3, htransverse, hisotropic]
  field_simp [pureWZ2HorizontalNorm_pos frameSlope |>.ne',
    htransverse, hisotropic]
  ring

@[simp] theorem pureWZ2AffineDiagonalMapAt_coord_one
    (frameSlope anchor heightScale transverseScale isotropicScale : ℝ)
    (point : Point3) :
    pureWZ2AffineDiagonalMapAt frameSlope anchor heightScale transverseScale
        isotropicScale point 1 =
      isotropicScale * transverseScale *
        ((-frameSlope * point 0 + point 1) /
          pureWZ2HorizontalNorm frameSlope) := by
  simp [pureWZ2AffineDiagonalMapAt,
    pureWZ2HorizontalRotation_coord_one, point3]
  field_simp [pureWZ2HorizontalNorm_pos frameSlope |>.ne']
  all_goals ring_nf <;> simp

@[simp] theorem pureWZ2AffineDiagonalMap_coord_two
    (frameSlope c d heightScale transverseScale isotropicScale : ℝ)
    (point : Point3) :
    pureWZ2AffineDiagonalMap frameSlope c d heightScale transverseScale
        isotropicScale point 2 =
      isotropicScale * heightScale * (point 2 - (c + d) / 2) := by
  simp [pureWZ2AffineDiagonalMap, pureWZ2AffineDiagonalMapAt,
    pureWZ2HorizontalRotation_coord_two, point3]

@[simp] theorem pureWZ2AffineDiagonalMapCentered_coord_two
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale isotropicScale : ℝ)
    (point : Point3) :
    pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale isotropicScale point 2 =
      isotropicScale * heightScale * (point 2 - center 2) := by
  simp [pureWZ2AffineDiagonalMapCentered,
    pureWZ2HorizontalRotation_coord_two, point3]

@[simp] theorem pureWZ2AffineDiagonalMapAt_coord_two
    (frameSlope anchor heightScale transverseScale isotropicScale : ℝ)
    (point : Point3) :
    pureWZ2AffineDiagonalMapAt frameSlope anchor heightScale transverseScale
        isotropicScale point 2 =
      isotropicScale * heightScale * (point 2 - anchor) := by
  simp [pureWZ2AffineDiagonalMapAt,
    pureWZ2HorizontalRotation_coord_two, point3]

/-- Algebraic zero at the midpoint. The global C2 target slope is constructed
in the safe-saturation module, where the Mobius denominator is uniformly
separated from zero. -/
theorem pureWZ2RotatedSlopeValue_midpoint_zero
    (source : SlopeFunction) (c d : ℝ) :
    pureWZ2RotatedSlopeValue (source ((c + d) / 2))
      (source (pureWZ2AffineDiagonalSourceHeight c d 1 0)) = 0 := by
  have hmid : pureWZ2AffineDiagonalSourceHeight c d 1 0 =
      (c + d) / 2 := by
    simp [pureWZ2AffineDiagonalSourceHeight]
  rw [hmid]
  simp [pureWZ2RotatedSlopeValue]

/-- Exact horizontal projection identity for the fixed rotation. -/
theorem pureWZ2HorizontalRotation_projection_identity
    (frameSlope value : ℝ) (point : Point3)
    (hdenom : 1 + frameSlope * value ≠ 0) :
    inner ℝ (pureWZ2HorizontalRotation frameSlope point)
        (globalGrainDirection
          (pureWZ2RotatedSlopeValue frameSlope value)) =
      (pureWZ2HorizontalNorm frameSlope /
          (1 + frameSlope * value)) *
        inner ℝ point (globalGrainDirection value) := by
  have hnorm : pureWZ2HorizontalNorm frameSlope ≠ 0 :=
    (pureWZ2HorizontalNorm_pos frameSlope).ne'
  simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ,
    pureWZ2RotatedSlopeValue,
    pureWZ2HorizontalRotation_coord_zero,
    pureWZ2HorizontalRotation_coord_one]
  field_simp [hnorm, hdenom]
  rw [pureWZ2HorizontalNorm_sq]
  ring

/-- Exact scalar-projection covariance for the full affine-diagonal map.
The target direction is the genuine Mobius direction divided by the
transverse diagonal factor; no public-slope approximation is used here. -/
theorem pureWZ2AffineDiagonal_projection_identity
    (frameSlope c d heightScale transverseScale isotropicScale value : ℝ)
    (point : Point3)
    (htransverse : transverseScale ≠ 0)
    (hdenom : 1 + frameSlope * value ≠ 0) :
    inner ℝ
        (pureWZ2AffineDiagonalMap frameSlope c d heightScale transverseScale
          isotropicScale point)
        (globalGrainDirection
          (pureWZ2RotatedSlopeValue frameSlope value / transverseScale)) =
      isotropicScale *
          (pureWZ2HorizontalNorm frameSlope /
            (1 + frameSlope * value)) *
        inner ℝ point (globalGrainDirection value) := by
  let translated := point3 (point 0) (point 1)
    (point 2 - (c + d) / 2)
  have hrotation := pureWZ2HorizontalRotation_projection_identity
    frameSlope value translated hdenom
  have hsource :
      inner ℝ translated (globalGrainDirection value) =
        inner ℝ point (globalGrainDirection value) := by
    simp [translated, globalGrainDirection, PiLp.inner_apply,
      Fin.sum_univ_succ, point3]
  rw [hsource] at hrotation
  let rotated := pureWZ2HorizontalRotation frameSlope translated
  have hdiagonal :
      inner ℝ
          (point3
            (isotropicScale * rotated 0)
            (isotropicScale * transverseScale * rotated 1)
            (isotropicScale * heightScale * rotated 2))
          (globalGrainDirection
            (pureWZ2RotatedSlopeValue frameSlope value /
              transverseScale)) =
        isotropicScale *
          inner ℝ rotated
            (globalGrainDirection
              (pureWZ2RotatedSlopeValue frameSlope value)) := by
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ, point3]
    field_simp [htransverse]
  change inner ℝ
      (point3
        (isotropicScale *
          (pureWZ2HorizontalRotation frameSlope translated) 0)
        (isotropicScale * transverseScale *
          (pureWZ2HorizontalRotation frameSlope translated) 1)
        (isotropicScale * heightScale *
          (pureWZ2HorizontalRotation frameSlope translated) 2))
      (globalGrainDirection
        (pureWZ2RotatedSlopeValue frameSlope value / transverseScale)) = _
  rw [show pureWZ2HorizontalRotation frameSlope translated = rotated by rfl]
  rw [hdiagonal, hrotation]
  ring

/-- Exact scalar-projection covariance for an arbitrary source height
anchor. -/
theorem pureWZ2AffineDiagonalAt_projection_identity
    (frameSlope anchor heightScale transverseScale isotropicScale value : ℝ)
    (point : Point3)
    (htransverse : transverseScale ≠ 0)
    (hdenom : 1 + frameSlope * value ≠ 0) :
    inner ℝ
        (pureWZ2AffineDiagonalMapAt frameSlope anchor heightScale
          transverseScale isotropicScale point)
        (globalGrainDirection
          (pureWZ2RotatedSlopeValue frameSlope value / transverseScale)) =
      isotropicScale *
          (pureWZ2HorizontalNorm frameSlope /
            (1 + frameSlope * value)) *
        inner ℝ point (globalGrainDirection value) := by
  let translated := point3 (point 0) (point 1) (point 2 - anchor)
  have hrotation := pureWZ2HorizontalRotation_projection_identity
    frameSlope value translated hdenom
  have hsource :
      inner ℝ translated (globalGrainDirection value) =
        inner ℝ point (globalGrainDirection value) := by
    simp [translated, globalGrainDirection, PiLp.inner_apply,
      Fin.sum_univ_succ, point3]
  rw [hsource] at hrotation
  let rotated := pureWZ2HorizontalRotation frameSlope translated
  have hdiagonal :
      inner ℝ
          (point3
            (isotropicScale * rotated 0)
            (isotropicScale * transverseScale * rotated 1)
            (isotropicScale * heightScale * rotated 2))
          (globalGrainDirection
            (pureWZ2RotatedSlopeValue frameSlope value /
              transverseScale)) =
        isotropicScale *
          inner ℝ rotated
            (globalGrainDirection
              (pureWZ2RotatedSlopeValue frameSlope value)) := by
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ, point3]
    field_simp [htransverse]
  change inner ℝ
      (point3
        (isotropicScale *
          (pureWZ2HorizontalRotation frameSlope translated) 0)
        (isotropicScale * transverseScale *
          (pureWZ2HorizontalRotation frameSlope translated) 1)
        (isotropicScale * heightScale *
          (pureWZ2HorizontalRotation frameSlope translated) 2))
      (globalGrainDirection
        (pureWZ2RotatedSlopeValue frameSlope value / transverseScale)) = _
  rw [show pureWZ2HorizontalRotation frameSlope translated = rotated by rfl]
  rw [hdiagonal, hrotation]
  ring

/-- A common horizontal translation does not affect the slope covariance:
it contributes only the expected affine projection offset.  On every target
horizontal slice this offset is constant, so AD transport may translate the
one-dimensional projected set without changing covering numbers. -/
theorem pureWZ2AffineDiagonalCentered_projection_identity
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale isotropicScale value : ℝ)
    (point : Point3)
    (htransverse : transverseScale ≠ 0)
    (hdenom : 1 + frameSlope * value ≠ 0) :
    inner ℝ
        (pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale isotropicScale point)
        (globalGrainDirection
          (pureWZ2RotatedSlopeValue frameSlope value / transverseScale)) =
      isotropicScale *
          (pureWZ2HorizontalNorm frameSlope /
            (1 + frameSlope * value)) *
        inner ℝ (point - center) (globalGrainDirection value) := by
  let translated := point - center
  have hrotation := pureWZ2HorizontalRotation_projection_identity
    frameSlope value translated hdenom
  let rotated := pureWZ2HorizontalRotation frameSlope translated
  have hdiagonal :
      inner ℝ
          (point3
            (isotropicScale * rotated 0)
            (isotropicScale * transverseScale * rotated 1)
            (isotropicScale * heightScale * rotated 2))
          (globalGrainDirection
            (pureWZ2RotatedSlopeValue frameSlope value /
              transverseScale)) =
        isotropicScale *
          inner ℝ rotated
            (globalGrainDirection
              (pureWZ2RotatedSlopeValue frameSlope value)) := by
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ, point3]
    field_simp [htransverse]
  change inner ℝ
      (point3
        (isotropicScale *
          (pureWZ2HorizontalRotation frameSlope translated) 0)
        (isotropicScale * transverseScale *
          (pureWZ2HorizontalRotation frameSlope translated) 1)
        (isotropicScale * heightScale *
          (pureWZ2HorizontalRotation frameSlope translated) 2))
      (globalGrainDirection
        (pureWZ2RotatedSlopeValue frameSlope value / transverseScale)) = _
  rw [show pureWZ2HorizontalRotation frameSlope translated = rotated by rfl]
  rw [hdiagonal, hrotation]
  ring

/-- Exact determinant of the general fixed-rotation affine-diagonal map. -/
theorem pureWZ2AffineDiagonalAffineEquivCentered_abs_det_general
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale isotropicScale : ℝ)
    (hheight : 0 < heightScale)
    (htransverse : 0 < transverseScale)
    (hisotropic : 0 < isotropicScale) :
    |LinearMap.det
      ((pureWZ2AffineDiagonalAffineEquivCentered frameSlope center
        heightScale transverseScale isotropicScale hheight.ne'
          htransverse.ne' hisotropic.ne').linear : Point3 →ₗ[ℝ] Point3)| =
      heightScale * transverseScale * isotropicScale ^ 3 := by
  let linear : Point3 →ₗ[ℝ] Point3 :=
    (pureWZ2AffineDiagonalAffineEquivCentered frameSlope center
      heightScale transverseScale isotropicScale hheight.ne'
        htransverse.ne' hisotropic.ne').linear
  let basis : Module.Basis (Fin 3) ℝ Point3 := PiLp.basisFun 2 ℝ (Fin 3)
  have hmatrix : LinearMap.toMatrix basis basis linear =
      !![isotropicScale / pureWZ2HorizontalNorm frameSlope,
          isotropicScale * frameSlope / pureWZ2HorizontalNorm frameSlope, 0;
        -(isotropicScale * transverseScale * frameSlope) /
          pureWZ2HorizontalNorm frameSlope,
          isotropicScale * transverseScale /
            pureWZ2HorizontalNorm frameSlope, 0;
        0, 0, isotropicScale * heightScale] := by
    ext i j
    have hentry : (LinearMap.toMatrix basis basis linear) i j =
        (linear (basis j)) i := by
      rw [LinearMap.toMatrix_apply]
      exact PiLp.basisFun_repr 2 ℝ (Fin 3) (linear (basis j)) i
    rw [hentry]
    fin_cases i <;> fin_cases j <;>
      simp [linear, basis, pureWZ2AffineDiagonalAffineEquivCentered,
        pureWZ2AffineDiagonalLinearEquiv, pureWZ2AffineDiagonalLinear,
        pureWZ2HorizontalRotation, pureWZ2HorizontalRotationEquiv,
        pureWZ2HorizontalRotationLinear, PiLp.basisFun_apply, point3] <;> ring
  have hnorm := pureWZ2HorizontalNorm_sq frameSlope
  have hnormPos := pureWZ2HorizontalNorm_pos frameSlope
  change |LinearMap.det linear| = _
  rw [← LinearMap.det_toMatrix basis linear, hmatrix]
  simp [Matrix.det_fin_three]
  field_simp [hnormPos.ne']
  rw [hnorm]
  have hdenominator : 1 + frameSlope ^ 2 ≠ 0 := by positivity
  rw [show 1 - -frameSlope ^ 2 = 1 + frameSlope ^ 2 by ring]
  have hcancel :
      isotropicScale ^ 3 * transverseScale * heightScale *
          (1 + frameSlope ^ 2) / (1 + frameSlope ^ 2) =
        isotropicScale ^ 3 * transverseScale * heightScale := by
    field_simp [hdenominator]
  rw [hcancel]
  have hproductPos :
      0 < isotropicScale ^ 3 * transverseScale * heightScale := by
    positivity
  rw [abs_of_pos hproductPos]

/-- The centered fixed rotation followed by the literal paper diagonal has
Jacobian `m`. -/
theorem pureWZ2AffineDiagonalMapCentered_volume_image
    (frameSlope : ℝ) (center : Point3)
    {m : ℝ} (hm : 0 < m)
    {source : Set Point3} (hsource : MeasurableSet source) :
    MeasureTheory.volume
        (pureWZ2AffineDiagonalMapCentered frameSlope center
          (100 / m) (m ^ 2 / 100) 1 '' source) =
      ENNReal.ofReal m * MeasureTheory.volume source := by
  let translated : Set Point3 := (fun point : Point3 => point - center) '' source
  let rotated : Set Point3 := pureWZ2HorizontalRotation frameSlope '' translated
  have htranslatedMeasurable : MeasurableSet translated := by
    have heq : translated = (fun point : Point3 => center + point) ⁻¹' source := by
      ext point
      simp only [translated, Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨sourcePoint, hpoint, rfl⟩
        simpa using hpoint
      · intro hpoint
        exact ⟨center + point, hpoint, by abel⟩
    rw [heq]
    exact hsource.preimage (measurable_const.add measurable_id)
  have hrotatedMeasurable : MeasurableSet rotated :=
    (pureWZ2HorizontalRotation frameSlope).toMeasurableEquiv
      |>.measurableSet_image.mpr htranslatedMeasurable
  have himage :
      pureWZ2AffineDiagonalMapCentered frameSlope center
          (100 / m) (m ^ 2 / 100) 1 '' source =
        diagonalRescalingMap m '' rotated := by
    ext target
    constructor
    · rintro ⟨point, hpoint, rfl⟩
      refine ⟨pureWZ2HorizontalRotation frameSlope (point - center),
        ⟨point - center, ⟨point, hpoint, rfl⟩, rfl⟩, ?_⟩
      ext coordinate
      fin_cases coordinate <;>
        simp [pureWZ2AffineDiagonalMapCentered, diagonalRescalingMap_apply,
          point3]
    · rintro ⟨rotatedPoint, ⟨translatedPoint,
          ⟨point, hpoint, rfl⟩, rfl⟩, rfl⟩
      refine ⟨point, hpoint, ?_⟩
      ext coordinate
      fin_cases coordinate <;>
        simp [pureWZ2AffineDiagonalMapCentered, diagonalRescalingMap_apply,
          point3]
  rw [himage, volume_image_diagonalRescalingMap m hm hrotatedMeasurable]
  rw [pureWZ2HorizontalRotation_volume_image frameSlope htranslatedMeasurable]
  have htranslatedVolume : MeasureTheory.volume translated =
      MeasureTheory.volume source := by
    have heq : translated = (fun point : Point3 => center + point) ⁻¹' source := by
      ext point
      simp only [translated, Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨sourcePoint, hpoint, rfl⟩
        simpa using hpoint
      · intro hpoint
        exact ⟨center + point, hpoint, by abel⟩
    rw [heq]
    exact MeasureTheory.measure_preimage_add MeasureTheory.volume center source
  rw [htranslatedVolume]

/-- The same Jacobian identity with the normalization constant exposed.
Only the product of the height and transverse factors matters. -/
theorem pureWZ2AffineDiagonalMapCentered_volume_image_general
    (frameSlope : ℝ) (center : Point3)
    {m C0 : ℝ} (hm : 0 < m) (hC0 : 0 < C0)
    {source : Set Point3} (_hsource : MeasurableSet source) :
    MeasureTheory.volume
        (pureWZ2AffineDiagonalMapCentered frameSlope center
          (C0 / m) (m ^ 2 / C0) 1 '' source) =
      ENNReal.ofReal m * MeasureTheory.volume source := by
  let equivalence := pureWZ2AffineDiagonalAffineEquivCentered frameSlope center
    (C0 / m) (m ^ 2 / C0) 1
    (div_ne_zero hC0.ne' hm.ne')
    (div_ne_zero (sq_pos_of_pos hm).ne' hC0.ne') one_ne_zero
  rw [show pureWZ2AffineDiagonalMapCentered frameSlope center
        (C0 / m) (m ^ 2 / C0) 1 '' source = equivalence '' source by
      ext point
      simp [equivalence]]
  rw [wz2PaperAffineEquiv_volume_image_eq]
  change ENNReal.ofReal
      |LinearMap.det (equivalence.linear : Point3 →ₗ[ℝ] Point3)| *
        MeasureTheory.volume source = _
  rw [show |LinearMap.det (equivalence.linear : Point3 →ₗ[ℝ] Point3)| =
      (C0 / m) * (m ^ 2 / C0) * 1 ^ 3 by
    exact pureWZ2AffineDiagonalAffineEquivCentered_abs_det_general
      frameSlope center (C0 / m) (m ^ 2 / C0) 1
      (div_pos hC0 hm) (div_pos (sq_pos_of_pos hm) hC0) (by norm_num)]
  have hproduct : (C0 / m) * (m ^ 2 / C0) * 1 ^ 3 = m := by
    field_simp [hm.ne', hC0.ne']
  rw [hproduct]

end Kakeya.Assouad

end
