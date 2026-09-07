import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalNormalizationNormal

/-!
# Exact plane map for the horizontal-normalized Section-6 image

This file packages the exact image of the triangular Section-6 map followed
by the horizontal dilation `(x, y, z) ↦ (lambda*x, lambda*y, z)`.  It stays below
the family and cubical-saturation layers: every target point has its literal
source preimage, and the plane field is the normalized combined
inverse-transpose normal at that same source point.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- The exact image under the triangular map followed by horizontal
dilation. -/
def pureWZ2HorizontalNormalizedExactImage
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (source : Set Point3) : Set Point3 :=
  pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
    horizontalCenter lambda '' source

/-- The canonical source preimage of a point in the exact combined image. -/
def pureWZ2HorizontalNormalizedExactSourcePoint
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (source : Set Point3)
    (target : {point : Point3 // point ∈
      pureWZ2HorizontalNormalizedExactImage g c d m anisotropicCenter
        horizontalCenter lambda source}) :
    {point : Point3 // point ∈ source} :=
  let equivalence := pureWZ2HorizontalNormalizedAffineEquiv
    g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
  ⟨equivalence.symm target, by
    have htargetImage : target.1 ∈
        pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' source := target.property
    rcases htargetImage with ⟨sourcePoint, hsourcePoint, heq⟩
    have htarget : target.1 = equivalence sourcePoint := by
      rw [pureWZ2HorizontalNormalizedAffineEquiv_apply]
      exact heq.symm
    rw [htarget, AffineEquiv.symm_apply_apply]
    exact hsourcePoint⟩

@[simp] theorem pureWZ2HorizontalNormalizedMap_exactSourcePoint
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (source : Set Point3)
    (target : {point : Point3 // point ∈
      pureWZ2HorizontalNormalizedExactImage g c d m anisotropicCenter
        horizontalCenter lambda source}) :
    pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
        horizontalCenter lambda
        (pureWZ2HorizontalNormalizedExactSourcePoint g c d m
          anisotropicCenter horizontalCenter lambda hcd hm hlambda
          source target) = target := by
  rw [← pureWZ2HorizontalNormalizedAffineEquiv_apply]
  exact AffineEquiv.apply_symm_apply _ _

/-- Pulling back along the combined affine equivalence has the explicit
inverse-operator Lipschitz constant. -/
theorem pureWZ2HorizontalNormalizedExactSourcePoint_lipschitz
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (source : Set Point3) :
    LipschitzWith
      ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m
          anisotropicCenter horizontalCenter lambda hcd hm hlambda).linear.symm
            |>.toContinuousLinearEquiv.toContinuousLinearMap‖₊
      (pureWZ2HorizontalNormalizedExactSourcePoint g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda source) := by
  let equivalence := pureWZ2HorizontalNormalizedAffineEquiv
    g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
  let inverseLinear :=
    equivalence.linear.symm.toContinuousLinearEquiv.toContinuousLinearMap
  apply LipschitzWith.of_dist_le_mul
  intro first second
  have hfirst :
      (pureWZ2HorizontalNormalizedExactSourcePoint g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda source first :
          Point3) = equivalence.symm first := rfl
  have hsecond :
      (pureWZ2HorizontalNormalizedExactSourcePoint g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda source second :
          Point3) = equivalence.symm second := rfl
  have hsub : equivalence.symm first - equivalence.symm second =
      inverseLinear ((first : Point3) - (second : Point3)) := by
    have h := AffineMap.linearMap_vsub equivalence.symm.toAffineMap
      (first : Point3) (second : Point3)
    change equivalence.symm.linear (first.1 - second.1) =
      equivalence.symm first.1 - equivalence.symm second.1 at h
    rw [AffineEquiv.linear_symm equivalence] at h
    exact h.symm
  have hlinear := inverseLinear.le_opNorm
    ((first : Point3) - (second : Point3))
  rw [Subtype.dist_eq, hfirst, hsecond, dist_eq_norm, hsub]
  rw [Subtype.dist_eq, dist_eq_norm]
  simpa only [inverseLinear, coe_nnnorm] using hlinear

/-- Linear packaging of the horizontal inverse-transpose factor. -/
def pureWZ2HorizontalNormalizedNormalLinear (lambda : ℝ) :
    Point3 →ₗ[ℝ] Point3 where
  toFun := pureWZ2HorizontalNormalizedNormal lambda
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2HorizontalNormalizedNormal, point3] <;> ring
  map_smul' scalar normal := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2HorizontalNormalizedNormal, point3] <;> ring

@[simp] theorem pureWZ2HorizontalNormalizedNormalLinear_apply
    (lambda : ℝ) (normal : Point3) :
    pureWZ2HorizontalNormalizedNormalLinear lambda normal =
      pureWZ2HorizontalNormalizedNormal lambda normal :=
  rfl

/-- Linear packaging of the combined inverse transpose. -/
def pureWZ2HorizontalNormalizedExactNormalLinear
    (g : SlopeFunction) (c d m lambda : ℝ) : Point3 →ₗ[ℝ] Point3 :=
  (pureWZ2HorizontalNormalizedNormalLinear lambda).comp
    (dPhiInvTLinear g c d m)

@[simp] theorem pureWZ2HorizontalNormalizedExactNormalLinear_apply
    (g : SlopeFunction) (c d m lambda : ℝ) (normal : Point3) :
    pureWZ2HorizontalNormalizedExactNormalLinear g c d m lambda normal =
      pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal :=
  rfl

/-- The combined inverse transpose is globally Lipschitz with the norm of
its displayed linear map. -/
theorem pureWZ2HorizontalNormalizedExactNormal_lipschitz
    (g : SlopeFunction) (c d m lambda : ℝ) :
    LipschitzWith
      ‖(pureWZ2HorizontalNormalizedExactNormalLinear g c d m lambda).toContinuousLinearMap‖₊
      (pureWZ2HorizontalNormalizedExactNormal g c d m lambda) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [dist_eq_norm, dist_eq_norm]
  change ‖pureWZ2HorizontalNormalizedExactNormalLinear g c d m lambda first -
      pureWZ2HorizontalNormalizedExactNormalLinear g c d m lambda second‖ ≤ _
  rw [← map_sub]
  exact (pureWZ2HorizontalNormalizedExactNormalLinear g c d m lambda
    |>.toContinuousLinearMap).le_opNorm (first - second)

/-- The source normal field transported to the exact combined image and
renormalized to unit length. -/
def pureWZ2HorizontalNormalizedExactPlaneMap
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (source : Set Point3)
    (sourcePlaneMap : {point : Point3 // point ∈ source} → Point3)
    (target : {point : Point3 // point ∈
      pureWZ2HorizontalNormalizedExactImage g c d m anisotropicCenter
        horizontalCenter lambda source}) : Point3 :=
  let sourcePoint := pureWZ2HorizontalNormalizedExactSourcePoint
    g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
      source target
  let transported := pureWZ2HorizontalNormalizedExactNormal
    g c d m lambda (sourcePlaneMap sourcePoint)
  (‖transported‖⁻¹ : ℝ) • transported

theorem pureWZ2HorizontalNormalizedExactPlaneMap_unit
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (source : Set Point3)
    (sourcePlaneMap : {point : Point3 // point ∈ source} → Point3)
    (hsourceUnit : ∀ point, ‖sourcePlaneMap point‖ = 1)
    (target : {point : Point3 // point ∈
      pureWZ2HorizontalNormalizedExactImage g c d m anisotropicCenter
        horizontalCenter lambda source}) :
    ‖pureWZ2HorizontalNormalizedExactPlaneMap g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda
      source sourcePlaneMap target‖ = 1 := by
  let sourcePoint := pureWZ2HorizontalNormalizedExactSourcePoint
    g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
      source target
  let transported := pureWZ2HorizontalNormalizedExactNormal
    g c d m lambda (sourcePlaneMap sourcePoint)
  have hsourceNonzero : sourcePlaneMap sourcePoint ≠ 0 := by
    intro hzero
    have hunit := hsourceUnit sourcePoint
    rw [hzero, norm_zero] at hunit
    norm_num at hunit
  have htransportedNonzero : transported ≠ 0 := by
    intro hzero
    have hinverseZero : dPhiInvT g c d m (sourcePlaneMap sourcePoint) = 0 := by
      apply pureWZ2HorizontalNormalizedNormal_injective hlambda.ne'
      simpa [transported, pureWZ2HorizontalNormalizedExactNormal,
        pureWZ2HorizontalNormalizedNormal, point3] using hzero
    apply hsourceNonzero
    apply dPhiInvT_injective g c d m hcd hm
    simpa [dPhiInvT, point3] using hinverseZero
  have hnorm : 0 < ‖transported‖ := norm_pos_iff.mpr htransportedNonzero
  change ‖(‖transported‖⁻¹ : ℝ) • transported‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp [hnorm.ne']

/-- Explicit Lipschitz constant for the normalized exact plane map. -/
def pureWZ2HorizontalNormalizedExactPlaneMapK
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (sourceK : NNReal) (lower : ℝ) (hlower : 0 < lower) : NNReal :=
  ⟨2 / lower, by positivity⟩ *
    ‖(pureWZ2HorizontalNormalizedExactNormalLinear g c d m lambda).toContinuousLinearMap‖₊ *
    sourceK *
    ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda).linear.symm
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖₊

/-- The normalized exact plane map is Lipschitz with the displayed finite
constant. -/
theorem pureWZ2HorizontalNormalizedExactPlaneMap_lipschitz
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (source : Set Point3)
    (sourcePlaneMap : {point : Point3 // point ∈ source} → Point3)
    (sourceK : NNReal) (hsourceLipschitz : LipschitzWith sourceK sourcePlaneMap)
    (lower : ℝ) (hlower : 0 < lower)
    (hnormalLower : ∀ point, lower ≤
      ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda
        (sourcePlaneMap point)‖) :
    LipschitzWith
      (pureWZ2HorizontalNormalizedExactPlaneMapK g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda
          sourceK lower hlower)
      (pureWZ2HorizontalNormalizedExactPlaneMap g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda
          source sourcePlaneMap) := by
  let sourceMap := pureWZ2HorizontalNormalizedExactSourcePoint
    g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda source
  let unnormalized :
      {point : Point3 // point ∈
        pureWZ2HorizontalNormalizedExactImage g c d m anisotropicCenter
          horizontalCenter lambda source} → Point3 :=
    fun point => pureWZ2HorizontalNormalizedExactNormal g c d m lambda
      (sourcePlaneMap (sourceMap point))
  let sourcePreimageK :=
    ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda).linear.symm
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖₊
  let inverseTransposeK :=
    ‖(pureWZ2HorizontalNormalizedExactNormalLinear g c d m lambda).toContinuousLinearMap‖₊
  let normalizationK : NNReal := ⟨2 / lower, by positivity⟩
  have hsourceMap : LipschitzWith sourcePreimageK sourceMap := by
    simpa only [sourceMap, sourcePreimageK] using
      pureWZ2HorizontalNormalizedExactSourcePoint_lipschitz
        g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda source
  have hunnormalized :
      LipschitzWith (inverseTransposeK * sourceK * sourcePreimageK)
        unnormalized := by
    have hlinear : LipschitzWith inverseTransposeK
        (pureWZ2HorizontalNormalizedExactNormal g c d m lambda) := by
      simpa only [inverseTransposeK] using
        pureWZ2HorizontalNormalizedExactNormal_lipschitz g c d m lambda
    simpa only [unnormalized, sourceMap, Function.comp_def, mul_assoc] using
      hlinear.comp (hsourceLipschitz.comp hsourceMap)
  apply LipschitzWith.of_dist_le_mul
  intro first second
  have hnormal := normalization_lipschitz
    (x := unnormalized first) (y := unnormalized second) hlower
      (hnormalLower (sourceMap first)) (hnormalLower (sourceMap second))
  have hraw := hunnormalized.dist_le_mul first second
  change dist
      (pureWZ2HorizontalNormalizedExactPlaneMap g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda
          source sourcePlaneMap first)
      (pureWZ2HorizontalNormalizedExactPlaneMap g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda
          source sourcePlaneMap second) ≤ _
  rw [dist_eq_norm]
  calc
    ‖pureWZ2HorizontalNormalizedExactPlaneMap g c d m
          anisotropicCenter horizontalCenter lambda hcd hm hlambda
            source sourcePlaneMap first -
        pureWZ2HorizontalNormalizedExactPlaneMap g c d m
          anisotropicCenter horizontalCenter lambda hcd hm hlambda
            source sourcePlaneMap second‖
        ≤ (2 / lower) * ‖unnormalized first - unnormalized second‖ := by
          simpa only [pureWZ2HorizontalNormalizedExactPlaneMap,
            unnormalized, sourceMap] using hnormal
    _ ≤ (2 / lower) *
        (((inverseTransposeK * sourceK * sourcePreimageK : NNReal) : ℝ) *
          dist first second) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa only [dist_eq_norm] using hraw
    _ = ((normalizationK * inverseTransposeK * sourceK *
          sourcePreimageK : NNReal) : ℝ) * dist first second := by
      change (2 / lower) *
          ((inverseTransposeK : ℝ) * (sourceK : ℝ) *
            (sourcePreimageK : ℝ) * dist first second) = _
      rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_mul]
      change (2 / lower) *
          ((inverseTransposeK : ℝ) * (sourceK : ℝ) *
            (sourcePreimageK : ℝ) * dist first second) =
        (2 / lower * (inverseTransposeK : ℝ) * (sourceK : ℝ) *
          (sourcePreimageK : ℝ)) * dist first second
      ring

/-- The normalized target direction associated to a source direction under
the combined affine map. -/
def pureWZ2HorizontalNormalizedExactDirection
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (direction : Point3) : Point3 :=
  let imageDirection :=
    (pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
      horizontalCenter lambda hcd hm hlambda).linear direction
  (‖imageDirection‖⁻¹ : ℝ) • imageDirection

/-- Exact source incidence gives a `sourceDelta / q` bound after the combined
normalization whenever the direction/normal norm product is at least `q > 0`. -/
theorem pureWZ2HorizontalNormalizedExactPlaneMap_incidence_le_div
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (source : Set Point3)
    (sourcePlaneMap : {point : Point3 // point ∈ source} → Point3)
    (hsourceUnit : ∀ point, ‖sourcePlaneMap point‖ = 1)
    (target : {point : Point3 // point ∈
      pureWZ2HorizontalNormalizedExactImage g c d m anisotropicCenter
        horizontalCenter lambda source})
    (direction : Point3) (hdirection : direction ≠ 0)
    (sourceDelta q : ℝ)
    (hsource : |inner ℝ direction
      (sourcePlaneMap
        (pureWZ2HorizontalNormalizedExactSourcePoint g c d m
          anisotropicCenter horizontalCenter lambda hcd hm hlambda
            source target))| ≤ sourceDelta)
    (hq : 0 < q)
    (hproduct : q ≤
      ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda).linear direction‖ *
      ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda
        (sourcePlaneMap
          (pureWZ2HorizontalNormalizedExactSourcePoint g c d m
            anisotropicCenter horizontalCenter lambda hcd hm hlambda
            source target))‖) :
    |inner ℝ
        (pureWZ2HorizontalNormalizedExactDirection g c d m
          anisotropicCenter horizontalCenter lambda hcd hm hlambda direction)
        (pureWZ2HorizontalNormalizedExactPlaneMap g c d m
          anisotropicCenter horizontalCenter lambda hcd hm hlambda
            source sourcePlaneMap target)| ≤ sourceDelta / q := by
  let sourcePoint := pureWZ2HorizontalNormalizedExactSourcePoint
    g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
      source target
  have hnormal : sourcePlaneMap sourcePoint ≠ 0 := by
    intro hzero
    have hunit := hsourceUnit sourcePoint
    rw [hzero, norm_zero] at hunit
    norm_num at hunit
  simpa only [pureWZ2HorizontalNormalizedExactDirection,
      pureWZ2HorizontalNormalizedExactPlaneMap, sourcePoint] using
    pureWZ2HorizontalNormalized_incidence_le_div g hcd hm hlambda
      anisotropicCenter horizontalCenter direction
      (sourcePlaneMap sourcePoint) hdirection hnormal hsource hq hproduct

/-- Compatibility form of
`pureWZ2HorizontalNormalizedExactPlaneMap_incidence_le_div` at `q = 1/3`. -/
theorem pureWZ2HorizontalNormalizedExactPlaneMap_incidence_le_three_mul
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (source : Set Point3)
    (sourcePlaneMap : {point : Point3 // point ∈ source} → Point3)
    (hsourceUnit : ∀ point, ‖sourcePlaneMap point‖ = 1)
    (target : {point : Point3 // point ∈
      pureWZ2HorizontalNormalizedExactImage g c d m anisotropicCenter
        horizontalCenter lambda source})
    (direction : Point3) (hdirection : direction ≠ 0)
    (sourceDelta : ℝ)
    (hsource : |inner ℝ direction
      (sourcePlaneMap
        (pureWZ2HorizontalNormalizedExactSourcePoint g c d m
          anisotropicCenter horizontalCenter lambda hcd hm hlambda
            source target))| ≤ sourceDelta)
    (hproduct : 1 / 3 ≤
      ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda).linear direction‖ *
      ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda
        (sourcePlaneMap
          (pureWZ2HorizontalNormalizedExactSourcePoint g c d m
            anisotropicCenter horizontalCenter lambda hcd hm hlambda
              source target))‖) :
    |inner ℝ
        (pureWZ2HorizontalNormalizedExactDirection g c d m
          anisotropicCenter horizontalCenter lambda hcd hm hlambda direction)
        (pureWZ2HorizontalNormalizedExactPlaneMap g c d m
          anisotropicCenter horizontalCenter lambda hcd hm hlambda
            source sourcePlaneMap target)| ≤ 3 * sourceDelta := by
  have hresult := pureWZ2HorizontalNormalizedExactPlaneMap_incidence_le_div
    g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
      source sourcePlaneMap hsourceUnit target direction hdirection sourceDelta
        (1 / 3 : ℝ) hsource (by norm_num) hproduct
  simpa [div_eq_mul_inv, mul_comm] using hresult

/-- Exact horizontal-normalization output, before any family retubing or
cubical saturation. -/
structure PureWZ2HorizontalNormalizedExactPlaneMapData
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (source : Set Point3)
    (sourcePlaneMap : {point : Point3 // point ∈ source} → Point3) where
  K : NNReal
  planeMap : {point : Point3 // point ∈
    pureWZ2HorizontalNormalizedExactImage g c d m anisotropicCenter
      horizontalCenter lambda source} → Point3
  planeMap_eq : planeMap =
    pureWZ2HorizontalNormalizedExactPlaneMap g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda
        source sourcePlaneMap
  planeMap_lipschitz : LipschitzWith K planeMap
  planeMap_unit : ∀ point, ‖planeMap point‖ = 1
  planeMap_incidence :
    ∀ target direction sourceDelta,
      direction ≠ 0 →
      |inner ℝ direction
        (sourcePlaneMap
          (pureWZ2HorizontalNormalizedExactSourcePoint g c d m
            anisotropicCenter horizontalCenter lambda hcd hm hlambda
              source target))| ≤ sourceDelta →
      1 / 3 ≤
        ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m
          anisotropicCenter horizontalCenter lambda hcd hm hlambda).linear
            direction‖ *
        ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda
          (sourcePlaneMap
            (pureWZ2HorizontalNormalizedExactSourcePoint g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda
                source target))‖ →
      |inner ℝ
          (pureWZ2HorizontalNormalizedExactDirection g c d m
            anisotropicCenter horizontalCenter lambda hcd hm hlambda direction)
          (planeMap target)| ≤ 3 * sourceDelta

/-- Assemble the exact-image package with its explicit Lipschitz constant. -/
theorem pureWZ2_toHorizontalNormalizedExactPlaneMapData
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (source : Set Point3)
    (sourcePlaneMap : {point : Point3 // point ∈ source} → Point3)
    (sourceK : NNReal) (hsourceLipschitz : LipschitzWith sourceK sourcePlaneMap)
    (hsourceUnit : ∀ point, ‖sourcePlaneMap point‖ = 1)
    (lower : ℝ) (hlower : 0 < lower)
    (hnormalLower : ∀ point, lower ≤
      ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda
        (sourcePlaneMap point)‖) :
    Nonempty (PureWZ2HorizontalNormalizedExactPlaneMapData g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda
        source sourcePlaneMap) := by
  let K := pureWZ2HorizontalNormalizedExactPlaneMapK g c d m
    anisotropicCenter horizontalCenter lambda hcd hm hlambda
      sourceK lower hlower
  exact ⟨{
    K := K
    planeMap := pureWZ2HorizontalNormalizedExactPlaneMap g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda
        source sourcePlaneMap
    planeMap_eq := rfl
    planeMap_lipschitz := by
      simpa only [K] using
        pureWZ2HorizontalNormalizedExactPlaneMap_lipschitz g c d m
          anisotropicCenter horizontalCenter lambda hcd hm hlambda
            source sourcePlaneMap sourceK hsourceLipschitz lower hlower
              hnormalLower
    planeMap_unit := pureWZ2HorizontalNormalizedExactPlaneMap_unit
      g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
        source sourcePlaneMap hsourceUnit
    planeMap_incidence := by
      intro target direction sourceDelta hdirection hsource hproduct
      exact pureWZ2HorizontalNormalizedExactPlaneMap_incidence_le_three_mul
        g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
          source sourcePlaneMap hsourceUnit target direction hdirection
            sourceDelta hsource hproduct
  }⟩

end Kakeya.Assouad

end
