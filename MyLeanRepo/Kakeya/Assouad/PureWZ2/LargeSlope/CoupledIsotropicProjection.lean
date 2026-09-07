import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CoupledIsotropicSlope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CubicalSliceADBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicCenteredMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperIsotropicLocalAD
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.MapInjectivity

/-!
# Exact global projection through the coupled final rescaling

This records the global-grain covariance of the centered triangular map
followed by the final positive isotropic dilation. On each target height the
scalar projection is a positive affine image of the corresponding source
exact-slice projection.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The combined centered anisotropic map and final isotropic dilation. -/
def pureWZ2CoupledIsotropicMap
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter isotropicCenter : Point3) (lambda : ℝ)
    (point : Point3) : Point3 :=
  pureWZ2IsotropicMap isotropicCenter lambda
    (anisotropicCenteredRescalingMap g c d m anisotropicCenter point)

/-- The exact target slope before replacement by its affine tangent. -/
def pureWZ2CombinedExactSlope
    (g : SlopeFunction) (c d m : ℝ)
    (isotropicCenter : Point3) (lambda t : ℝ) : ℝ :=
  anisotropicRescaledSlope g c d m
    (isotropicCenter 2 + t / lambda)

/-- The slice-wise translation in the scalar projection identity. -/
def pureWZ2CoupledProjectionOffset
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter isotropicCenter : Point3)
    (lambda t : ℝ) : ℝ :=
  -lambda *
    (anisotropicRescalingMap g c d m anisotropicCenter 0 +
      isotropicCenter 0 +
      pureWZ2CombinedExactSlope g c d m isotropicCenter lambda t *
        isotropicCenter 1)

/-- Target height corresponding to a specified source height under the
coupled map. -/
def pureWZ2CoupledTargetHeight
    (c d : ℝ) (isotropicCenter : Point3) (lambda sourceHeight : ℝ) : ℝ :=
  lambda * (2 * (sourceHeight - c) / (d - c) - 1 - isotropicCenter 2)

@[simp] theorem pureWZ2CoupledIsotropicMap_replaceHeight_coord_two
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter isotropicCenter point : Point3) (lambda height : ℝ) :
    pureWZ2CoupledIsotropicMap g c d m anisotropicCenter isotropicCenter lambda
        (pureWZ2ReplaceHeight point height) 2 =
      pureWZ2CoupledTargetHeight c d isotropicCenter lambda height := by
  simp [pureWZ2CoupledIsotropicMap, pureWZ2CoupledTargetHeight,
    pureWZ2IsotropicMap, anisotropicCenteredRescalingMap,
    anisotropicRescalingMap, pureWZ2ReplaceHeight, point3]

/-- Target height t corresponds exactly to this source height. -/
theorem pureWZ2CoupledIsotropicMap_coord_two_iff
    (g : SlopeFunction) {c d m lambda : ℝ}
    (hcd : c < d) (hlambda : 0 < lambda)
    (anisotropicCenter isotropicCenter point : Point3) (t : ℝ) :
    pureWZ2CoupledIsotropicMap g c d m anisotropicCenter
        isotropicCenter lambda point 2 = t ↔
      point 2 = c + (d - c) / 2 *
        (isotropicCenter 2 + t / lambda + 1) := by
  have hcoordPoint := (anisotropicRescalingMap_coord g c d m point).2.2
  have hcenteredCoord :
      anisotropicCenteredRescalingMap g c d m anisotropicCenter point 2 =
        2 * (point 2 - c) / (d - c) - 1 := by
    unfold anisotropicCenteredRescalingMap
    rw [PiLp.sub_apply, hcoordPoint]
    simp [point3]
  have hcombinedCoord :
      pureWZ2CoupledIsotropicMap g c d m anisotropicCenter
          isotropicCenter lambda point 2 =
        lambda *
          ((2 * (point 2 - c) / (d - c) - 1) - isotropicCenter 2) := by
    unfold pureWZ2CoupledIsotropicMap pureWZ2IsotropicMap
    rw [PiLp.smul_apply, PiLp.sub_apply, hcenteredCoord]
    rfl
  rw [hcombinedCoord]
  have hdc : d - c ≠ 0 := sub_ne_zero.mpr hcd.ne'
  constructor <;> intro h
  · field_simp [hlambda.ne', hdc] at h ⊢
    linarith
  · field_simp [hlambda.ne', hdc] at h ⊢
    linarith

/-- Pointwise covariance of the global-grain scalar projection. -/
theorem pureWZ2CoupledIsotropic_projection_pointwise
    (g : SlopeFunction) {c d m lambda : ℝ}
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (anisotropicCenter isotropicCenter point : Point3) (t : ℝ)
    (hheight : pureWZ2CoupledIsotropicMap g c d m anisotropicCenter
      isotropicCenter lambda point 2 = t) :
    inner ℝ
        (pureWZ2CoupledIsotropicMap g c d m anisotropicCenter
          isotropicCenter lambda point)
        (globalGrainDirection
          (pureWZ2CombinedExactSlope g c d m isotropicCenter lambda t)) =
      lambda * inner ℝ point (globalGrainDirection (g (point 2))) +
        pureWZ2CoupledProjectionOffset g c d m anisotropicCenter
          isotropicCenter lambda t := by
  have hsourceHeight :=
    (pureWZ2CoupledIsotropicMap_coord_two_iff g hcd hlambda
      anisotropicCenter isotropicCenter point t).mp hheight
  have hanisotropic := anisotropic_projection_pointwise g c d m hcd hm
    (isotropicCenter 2 + t / lambda) point hsourceHeight
  unfold pureWZ2CoupledIsotropicMap pureWZ2IsotropicMap
    anisotropicCenteredRescalingMap pureWZ2CombinedExactSlope
    pureWZ2CoupledProjectionOffset
  simp only [real_inner_smul_left, inner_sub_left]
  have hshift : inner ℝ
      (point3 (anisotropicRescalingMap g c d m anisotropicCenter 0) 0 0)
      (globalGrainDirection
        (anisotropicRescaledSlope g c d m
          (isotropicCenter 2 + t / lambda))) =
      anisotropicRescalingMap g c d m anisotropicCenter 0 := by
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ, point3]
  have hcenter : inner ℝ isotropicCenter
      (globalGrainDirection
        (anisotropicRescaledSlope g c d m
          (isotropicCenter 2 + t / lambda))) =
      isotropicCenter 0 +
        anisotropicRescaledSlope g c d m
          (isotropicCenter 2 + t / lambda) * isotropicCenter 1 := by
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
  rw [hshift, hcenter, hanisotropic]
  unfold pureWZ2CombinedExactSlope
  ring

/-- Exact projection covariance for a source point moved to an arbitrary
height.  This is the cellwise identity used by the final cubical quotient. -/
theorem pureWZ2CoupledIsotropic_projection_replaceHeight
    (g : SlopeFunction) {c d m lambda : ℝ}
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (anisotropicCenter isotropicCenter point : Point3) (height : ℝ) :
    let source := pureWZ2ReplaceHeight point height
    let targetHeight := pureWZ2CoupledTargetHeight c d isotropicCenter
      lambda height
    inner ℝ
        (pureWZ2CoupledIsotropicMap g c d m anisotropicCenter
          isotropicCenter lambda source)
        (globalGrainDirection
          (pureWZ2CombinedExactSlope g c d m isotropicCenter
            lambda targetHeight)) =
      lambda * inner ℝ source (globalGrainDirection (g height)) +
        pureWZ2CoupledProjectionOffset g c d m anisotropicCenter
          isotropicCenter lambda targetHeight := by
  dsimp only
  simpa only [pureWZ2ReplaceHeight_apply_two] using
    pureWZ2CoupledIsotropic_projection_pointwise g hcd hm hlambda
      anisotropicCenter isotropicCenter
      (pureWZ2ReplaceHeight point height)
      (pureWZ2CoupledTargetHeight c d isotropicCenter lambda height)
      (pureWZ2CoupledIsotropicMap_replaceHeight_coord_two
    g c d m anisotropicCenter isotropicCenter point lambda height
      )

/-- Set-level form of the combined exact projection identity. -/
theorem pureWZ2CoupledIsotropic_projection_set
    (g : SlopeFunction) {c d m lambda : ℝ}
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (anisotropicCenter isotropicCenter : Point3)
    (source : Set Point3) (t : ℝ) :
    scalarProjection
        (globalGrainDirection
          (pureWZ2CombinedExactSlope g c d m isotropicCenter lambda t))
        (horizontalSlice
          (pureWZ2CoupledIsotropicMap g c d m anisotropicCenter
            isotropicCenter lambda '' source) t) =
      (fun value : ℝ => lambda * value +
        pureWZ2CoupledProjectionOffset g c d m anisotropicCenter
          isotropicCenter lambda t) ''
        scalarProjection
          (globalGrainDirection
            (g (c + (d - c) / 2 *
              (isotropicCenter 2 + t / lambda + 1))))
          (horizontalSlice source
            (c + (d - c) / 2 *
              (isotropicCenter 2 + t / lambda + 1))) := by
  ext value
  constructor
  · rintro ⟨target, ⟨⟨sourcePoint, hsourcePoint, rfl⟩, hheight⟩, rfl⟩
    have hsourceHeight :=
      (pureWZ2CoupledIsotropicMap_coord_two_iff g hcd hlambda
        anisotropicCenter isotropicCenter sourcePoint t).mp hheight
    refine ⟨inner ℝ sourcePoint
        (globalGrainDirection (g (sourcePoint 2))), ?_, ?_⟩
    · exact ⟨sourcePoint, ⟨hsourcePoint, hsourceHeight⟩, by rw [hsourceHeight]⟩
    · exact (pureWZ2CoupledIsotropic_projection_pointwise g hcd hm hlambda
        anisotropicCenter isotropicCenter sourcePoint t hheight).symm
  · rintro ⟨sourceValue,
      ⟨sourcePoint, ⟨hsourcePoint, hsourceHeight⟩, rfl⟩, rfl⟩
    have hheight : pureWZ2CoupledIsotropicMap g c d m anisotropicCenter
        isotropicCenter lambda sourcePoint 2 = t :=
      (pureWZ2CoupledIsotropicMap_coord_two_iff g hcd hlambda
        anisotropicCenter isotropicCenter sourcePoint t).mpr hsourceHeight
    refine ⟨pureWZ2CoupledIsotropicMap g c d m anisotropicCenter
        isotropicCenter lambda sourcePoint,
      ⟨⟨sourcePoint, hsourcePoint, rfl⟩, hheight⟩, ?_⟩
    rw [← hsourceHeight]
    exact pureWZ2CoupledIsotropic_projection_pointwise g hcd hm hlambda
      anisotropicCenter isotropicCenter sourcePoint t hheight

/-- Moving a source point only in height has an especially simple image
under the coupled map: the horizontal shear and transverse coordinate do not
move, while the final height is multiplied by `lambda * 2 / (d-c)`. -/
theorem pureWZ2CoupledIsotropicMap_replaceHeight_dist
    (g : SlopeFunction) {c d m lambda : ℝ}
    (hcd : c < d) (hlambda : 0 < lambda)
    (anisotropicCenter isotropicCenter point : Point3) (height : ℝ) :
    dist
        (pureWZ2CoupledIsotropicMap g c d m anisotropicCenter
          isotropicCenter lambda point)
        (pureWZ2CoupledIsotropicMap g c d m anisotropicCenter
          isotropicCenter lambda (pureWZ2ReplaceHeight point height)) =
      lambda * (2 / (d - c)) * |point 2 - height| := by
  have hdc : 0 < 2 / (d - c) := by positivity
  rw [dist_eq_norm]
  have hdifference :
      pureWZ2CoupledIsotropicMap g c d m anisotropicCenter
          isotropicCenter lambda point -
        pureWZ2CoupledIsotropicMap g c d m anisotropicCenter
          isotropicCenter lambda (pureWZ2ReplaceHeight point height) =
      point3 0 0 (lambda * (2 / (d - c)) * (point 2 - height)) := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2CoupledIsotropicMap, pureWZ2IsotropicMap,
        anisotropicCenteredRescalingMap, anisotropicRescalingMap,
        pureWZ2ReplaceHeight, point3] <;>
      field_simp [sub_ne_zero.mpr hcd.ne'] <;> ring
  rw [hdifference]
  have hfactor : 0 ≤ lambda * (2 / (d - c)) := by positivity
  have hnorm :
      ‖point3 0 0 (lambda * (2 / (d - c)) * (point 2 - height))‖ =
        |lambda * (2 / (d - c)) * (point 2 - height)| := by
    rw [show point3 0 0
        (lambda * (2 / (d - c)) * (point 2 - height)) =
      (lambda * (2 / (d - c)) * (point 2 - height)) •
        EuclideanSpace.single (2 : Fin 3) (1 : ℝ) by simp [point3]]
    rw [norm_smul, Real.norm_eq_abs]
    simp
  rw [hnorm, abs_mul, abs_of_nonneg hfactor]

end Kakeya.Assouad

end
