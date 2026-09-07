import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64AffineMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64IsotropicPlaneMap

/-!
# The combined affine equivalence in Proposition 6.4

The final geometric change of variables is the exact translated Proposition
6.4 normalization followed by the positive isotropic dilation from Lemma 3.5.
This module packages that composition as one affine equivalence and records
its exact forward Jacobian.  It contains no tube-selection or CWA input.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- The positive isotropic map used in Proposition 6.4, represented as an
affine equivalence. -/
noncomputable def pureWZ2Proposition64IsotropicAffineEquiv
    (center : Point3) (scale : ℝ) (hscale : 0 < scale) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  (AffineEquiv.constVAdd ℝ Point3 (-center)).trans
    (AffineEquiv.ofLinearEquiv
      (LinearEquiv.smulOfNeZero ℝ Point3 scale hscale.ne') 0 0)

@[simp] theorem pureWZ2Proposition64IsotropicAffineEquiv_apply
    (center : Point3) (scale : ℝ) (hscale : 0 < scale)
    (point : Point3) :
    pureWZ2Proposition64IsotropicAffineEquiv center scale hscale point =
      pureWZ2Proposition64IsotropicMap center scale point := by
  simp [pureWZ2Proposition64IsotropicAffineEquiv,
    pureWZ2Proposition64IsotropicMap, AffineEquiv.trans_apply,
    LinearEquiv.smulOfNeZero_apply]
  module

/-- The exact R4 map: translated `Phi`, then the final isotropic dilation. -/
noncomputable def pureWZ2Proposition64CombinedAffineEquiv
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation isotropicCenter : Point3) (scale : ℝ)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (hscale : 0 < scale) : Point3 ≃ᵃ[ℝ] Point3 :=
  (pureWZ2Proposition64TranslatedAffineEquiv g slabCenter anchorHeight
      halfHeight normalization translation hhalfHeight hnormalization).trans
    (pureWZ2Proposition64IsotropicAffineEquiv isotropicCenter scale hscale)

@[simp] theorem pureWZ2Proposition64CombinedAffineEquiv_apply
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation isotropicCenter : Point3) (scale : ℝ)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (hscale : 0 < scale) (point : Point3) :
    pureWZ2Proposition64CombinedAffineEquiv g slabCenter anchorHeight
        halfHeight normalization translation isotropicCenter scale
        hhalfHeight hnormalization hscale point =
      pureWZ2Proposition64IsotropicMap isotropicCenter scale
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation point) := by
  simp [pureWZ2Proposition64CombinedAffineEquiv, AffineEquiv.trans_apply]

/-- Exact forward volume formula for the full R4 change of variables.  The
two factors are intentionally left separated: the first is the Lemma-3.5
isotropic dilation and the second is the Proposition-6.4 affine Jacobian. -/
theorem pureWZ2Proposition64CombinedAffineEquiv_volume_image_eq
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    {halfHeight normalization scale : ℝ}
    (translation isotropicCenter : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (hscale : 0 < scale)
    {source : Set Point3} (hsource : MeasurableSet source) :
    volume
        (pureWZ2Proposition64CombinedAffineEquiv g slabCenter anchorHeight
          halfHeight normalization translation isotropicCenter scale
          hhalfHeight hnormalization hscale '' source) =
      ENNReal.ofReal (scale ^ 3) *
        (ENNReal.ofReal (1 / (normalization * halfHeight)) *
          volume source) := by
  let translated := pureWZ2Proposition64TranslatedAffineEquiv g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight hnormalization
  let isotropic := pureWZ2Proposition64IsotropicAffineEquiv
    isotropicCenter scale hscale
  have hcombined :
      pureWZ2Proposition64CombinedAffineEquiv g slabCenter anchorHeight
          halfHeight normalization translation isotropicCenter scale
          hhalfHeight hnormalization hscale '' source =
        pureWZ2Proposition64IsotropicMap isotropicCenter scale ''
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation '' source) := by
    ext point
    simp only [Set.mem_image]
    constructor
    · rintro ⟨sourcePoint, hsourcePoint, rfl⟩
      refine ⟨pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation sourcePoint,
        ⟨sourcePoint, hsourcePoint, rfl⟩, ?_⟩
      simp
    · rintro ⟨translatedPoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
      refine ⟨sourcePoint, hsourcePoint, ?_⟩
      simp
  have htranslatedMeasurable : MeasurableSet
      (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
        halfHeight normalization translation '' source) := by
    have hmap : (translated : Point3 → Point3) =
        pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation := by
      funext point
      exact pureWZ2Proposition64TranslatedAffineEquiv_apply g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization point
    rw [← hmap]
    exact translated.toHomeomorphOfFiniteDimensional.toMeasurableEquiv
      |>.measurableSet_image.mpr hsource
  rw [hcombined]
  rw [pureWZ2Proposition64IsotropicMap_volume_image_eq
    isotropicCenter hscale htranslatedMeasurable]
  rw [pureWZ2Proposition64TranslatedMap_volume_image_eq
    g slabCenter anchorHeight translation hhalfHeight hnormalization]

/-- Exact inverse-volume formula for the physical combined Proposition-6.4
map. -/
theorem pureWZ2Proposition64CombinedAffineEquiv_inverse_volume_eq
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    {halfHeight normalization scale : ℝ}
    (translation isotropicCenter : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (hscale : 0 < scale) (targetSet : Set Point3) :
    volume
        ((pureWZ2Proposition64CombinedAffineEquiv g slabCenter anchorHeight
          halfHeight normalization translation isotropicCenter scale
          hhalfHeight hnormalization hscale).symm '' targetSet) =
      ENNReal.ofReal (normalization * halfHeight / scale ^ 3) *
        volume targetSet := by
  rw [wz2PaperAffineEquiv_volume_image_eq]
  let combined := pureWZ2Proposition64CombinedAffineEquiv g slabCenter
    anchorHeight halfHeight normalization translation isotropicCenter scale
      hhalfHeight hnormalization hscale
  let translated := pureWZ2Proposition64TranslatedAffineEquiv g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight hnormalization
  let isotropic := pureWZ2Proposition64IsotropicAffineEquiv
    isotropicCenter scale hscale
  have hcombinedDet :
      LinearMap.det (combined.linear : Point3 →ₗ[ℝ] Point3) =
        scale ^ 3 * (1 / (normalization * halfHeight)) := by
    have hcombinedLinear :
        (combined.linear : Point3 →ₗ[ℝ] Point3) =
          (isotropic.linear : Point3 →ₗ[ℝ] Point3).comp
            (translated.linear : Point3 →ₗ[ℝ] Point3) := by
      rfl
    rw [hcombinedLinear, LinearMap.det_comp]
    have hisotropic :
        LinearMap.det
            (isotropic.linear : Point3 →ₗ[ℝ] Point3) =
          scale ^ 3 := by
      have hisotropicLinear :
          (isotropic.linear : Point3 →ₗ[ℝ] Point3) =
            scale • LinearMap.id := by
        rfl
      rw [hisotropicLinear, LinearMap.det_smul, LinearMap.det_id]
      norm_num [Module.finrank_fin_fun]
    rw [hisotropic]
    have htranslated :
        LinearMap.det
            (translated.linear : Point3 →ₗ[ℝ] Point3) =
          1 / (normalization * halfHeight) := by
      dsimp only [translated, pureWZ2Proposition64TranslatedAffineEquiv]
      exact pureWZ2Proposition64Linear_det
        (g anchorHeight) halfHeight normalization
    rw [htranslated]
  have hinverseDet :
      LinearMap.det (combined.symm.linear : Point3 →ₗ[ℝ] Point3) =
        normalization * halfHeight / scale ^ 3 := by
    rw [show combined.symm.linear = combined.linear.symm by rfl,
      LinearEquiv.det_coe_symm, hcombinedDet]
    field_simp [hhalfHeight.ne', hnormalization.ne', hscale.ne']
  rw [show
      LinearMap.det
          ((pureWZ2Proposition64CombinedAffineEquiv g slabCenter anchorHeight
            halfHeight normalization translation isotropicCenter scale
            hhalfHeight hnormalization hscale).symm.linear :
              Point3 →ₗ[ℝ] Point3) =
        normalization * halfHeight / scale ^ 3 by
    exact hinverseDet]
  rw [abs_of_pos (div_pos (mul_pos hnormalization hhalfHeight)
    (pow_pos hscale 3))]

/-- The canonical coordinate change from one source actual-John packet to a
target actual-John packet after the full Proposition-6.4 map. -/
noncomputable def pureWZ2Proposition64ActualJohnCoordinateChange
    {sourceRho targetRho : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation isotropicCenter : Point3) (scale : ℝ)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (hscale : 0 < scale) : Point3 ≃ᵃ[ℝ] Point3 :=
  sourceJohn.map.symm.trans
    ((pureWZ2Proposition64CombinedAffineEquiv g slabCenter anchorHeight
      halfHeight normalization translation isotropicCenter scale
      hhalfHeight hnormalization hscale).trans targetJohn.map)

@[simp] theorem pureWZ2Proposition64ActualJohnCoordinateChange_apply_map
    {sourceRho targetRho : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation isotropicCenter : Point3) (scale : ℝ)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (hscale : 0 < scale) (point : Point3) :
    pureWZ2Proposition64ActualJohnCoordinateChange sourceJohn targetJohn g
        slabCenter anchorHeight halfHeight normalization translation
        isotropicCenter scale hhalfHeight hnormalization hscale
        (sourceJohn.map point) =
      targetJohn.map
        (pureWZ2Proposition64IsotropicMap isotropicCenter scale
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation point)) := by
  simp [pureWZ2Proposition64ActualJohnCoordinateChange,
    AffineEquiv.trans_apply]

/-- The preceding coordinate change sends the source-John image of a physical
set exactly to the target-John image of its full R4 affine image. -/
theorem pureWZ2Proposition64ActualJohnCoordinateChange_image
    {sourceRho targetRho : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation isotropicCenter : Point3) (scale : ℝ)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (hscale : 0 < scale) (source : Set Point3) :
    pureWZ2Proposition64ActualJohnCoordinateChange sourceJohn targetJohn g
          slabCenter anchorHeight halfHeight normalization translation
          isotropicCenter scale hhalfHeight hnormalization hscale ''
        (sourceJohn.map '' source) =
      targetJohn.map ''
        (pureWZ2Proposition64CombinedAffineEquiv g slabCenter anchorHeight
          halfHeight normalization translation isotropicCenter scale
          hhalfHeight hnormalization hscale '' source) := by
  ext point
  constructor
  · rintro ⟨sourceJohnPoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
    refine ⟨pureWZ2Proposition64CombinedAffineEquiv g slabCenter anchorHeight
        halfHeight normalization translation isotropicCenter scale
        hhalfHeight hnormalization hscale sourcePoint,
      ⟨sourcePoint, hsourcePoint, rfl⟩, ?_⟩
    simp
  · rintro ⟨combinedPoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
    refine ⟨sourceJohn.map sourcePoint, ⟨sourcePoint, hsourcePoint, rfl⟩, ?_⟩
    simp

/-- Exact inverse-volume formula for the source-John to final target-John
coordinate change.  This isolates all scale dependence in three explicit
determinant factors. -/
theorem pureWZ2Proposition64ActualJohnCoordinateChange_inverse_volume_eq
    {sourceRho targetRho : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation isotropicCenter : Point3) {scale : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (hscale : 0 < scale) (targetSet : Set Point3) :
    volume
        ((pureWZ2Proposition64ActualJohnCoordinateChange sourceJohn
          targetJohn g slabCenter anchorHeight halfHeight normalization
          translation isotropicCenter scale hhalfHeight hnormalization
          hscale).symm '' targetSet) =
      ENNReal.ofReal
          |LinearMap.det
            (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)| *
        ENNReal.ofReal (normalization * halfHeight / scale ^ 3) *
          ENNReal.ofReal
            |LinearMap.det
              (sourceJohn.parent_convex_body.outerJohnEllipsoidMap.symm :
                Point3 →ₗ[ℝ] Point3)| *
            volume targetSet := by
  rw [wz2PaperAffineEquiv_volume_image_eq]
  let combined := pureWZ2Proposition64CombinedAffineEquiv g slabCenter
    anchorHeight halfHeight normalization translation isotropicCenter scale
      hhalfHeight hnormalization hscale
  let translated := pureWZ2Proposition64TranslatedAffineEquiv g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight hnormalization
  let isotropic := pureWZ2Proposition64IsotropicAffineEquiv
    isotropicCenter scale hscale
  have hlinear :
      (pureWZ2Proposition64ActualJohnCoordinateChange sourceJohn targetJohn g
        slabCenter anchorHeight halfHeight normalization translation
        isotropicCenter scale hhalfHeight hnormalization hscale).symm.linear =
      targetJohn.map.symm.linear.trans
        (combined.symm.linear.trans sourceJohn.map.linear) := rfl
  rw [hlinear]
  have hlinearMap :
      ((targetJohn.map.symm.linear.trans
        (combined.symm.linear.trans sourceJohn.map.linear) :
          Point3 ≃ₗ[ℝ] Point3) : Point3 →ₗ[ℝ] Point3) =
        (sourceJohn.map.linear : Point3 →ₗ[ℝ] Point3).comp
          ((combined.symm.linear : Point3 →ₗ[ℝ] Point3).comp
            (targetJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3)) := by
    ext point
    rfl
  rw [hlinearMap, LinearMap.det_comp, LinearMap.det_comp, abs_mul, abs_mul]
  have htarget :
      (targetJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3) =
        targetJohn.parent_convex_body.outerJohnEllipsoidMap := rfl
  have hsource :
      (sourceJohn.map.linear : Point3 →ₗ[ℝ] Point3) =
        sourceJohn.parent_convex_body.outerJohnEllipsoidMap.symm := rfl
  rw [htarget, hsource]
  have hcombinedDet :
      LinearMap.det (combined.linear : Point3 →ₗ[ℝ] Point3) =
        scale ^ 3 * (1 / (normalization * halfHeight)) := by
    have hcombinedLinear :
        (combined.linear : Point3 →ₗ[ℝ] Point3) =
          (isotropic.linear : Point3 →ₗ[ℝ] Point3).comp
            (translated.linear : Point3 →ₗ[ℝ] Point3) := by
      rfl
    rw [hcombinedLinear, LinearMap.det_comp]
    have hisotropic :
        LinearMap.det
            (isotropic.linear : Point3 →ₗ[ℝ] Point3) =
          scale ^ 3 := by
      have hisotropicLinear :
          (isotropic.linear : Point3 →ₗ[ℝ] Point3) =
            scale • LinearMap.id := by
        rfl
      rw [hisotropicLinear, LinearMap.det_smul, LinearMap.det_id]
      norm_num [Module.finrank_fin_fun]
    rw [hisotropic]
    have htranslated :
        LinearMap.det
            (translated.linear : Point3 →ₗ[ℝ] Point3) =
          1 / (normalization * halfHeight) := by
      dsimp only [translated, pureWZ2Proposition64TranslatedAffineEquiv]
      exact pureWZ2Proposition64Linear_det
        (g anchorHeight) halfHeight normalization
    rw [htranslated]
  rw [show LinearMap.det (combined.symm.linear : Point3 →ₗ[ℝ] Point3) =
      normalization * halfHeight / scale ^ 3 by
    rw [show combined.symm.linear = combined.linear.symm by rfl,
      LinearEquiv.det_coe_symm, hcombinedDet]
    field_simp [hhalfHeight.ne', hnormalization.ne', hscale.ne']
    ]
  rw [abs_of_pos (div_pos (mul_pos hnormalization hhalfHeight)
    (pow_pos hscale 3))]
  rw [ENNReal.ofReal_mul (abs_nonneg _),
    ENNReal.ofReal_mul (by positivity :
      0 ≤ normalization * halfHeight / scale ^ 3)]
  ring

end Kakeya.Assouad

end
