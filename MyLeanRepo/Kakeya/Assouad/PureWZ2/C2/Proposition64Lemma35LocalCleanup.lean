import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64IsotropicRetubing

/-!
# Proposition 6.4: local-grain part of the Lemma 3.5 cleanup

This module performs the operations in the order used in `wz2_64.tex`:
restrict the exact `Phi`-image shading to a mass-popular box, apply one
positive isotropic similarity, saturate in the final paper grid, and extend
and normalize the transported plane field.  The final family retains the
source-parent map and the axis identity for the composition of `Phi` with
the isotropic similarity.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Restrict a plane field together with a subshading. -/
def pureWZ2Proposition64RestrictedPlaneMap
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading restricted : WZ1PaperTubeShading family}
    (hsub : PureWZ2PaperIsSubshading restricted shading)
    (planeMap : {point : Point3 // point ∈ shading.union} → Point3)
    (point : {point : Point3 // point ∈ restricted.union}) : Point3 :=
  planeMap ⟨point, by
    rcases point.property with ⟨index, hpoint⟩
    exact ⟨index, hsub index hpoint⟩⟩

theorem pureWZ2Proposition64RestrictedPlaneMap_lipschitz
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading restricted : WZ1PaperTubeShading family}
    (hsub : PureWZ2PaperIsSubshading restricted shading)
    {planeMap : {point : Point3 // point ∈ shading.union} → Point3}
    {K : NNReal} (hplaneMap : LipschitzWith K planeMap) :
    LipschitzWith K
      (pureWZ2Proposition64RestrictedPlaneMap hsub planeMap) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  simpa [pureWZ2Proposition64RestrictedPlaneMap, Subtype.dist_eq] using
    hplaneMap.dist_le_mul
      (⟨first, by
        rcases first.property with ⟨index, hpoint⟩
        exact ⟨index, hsub index hpoint⟩⟩ :
          {point : Point3 // point ∈ shading.union})
      (⟨second, by
        rcases second.property with ⟨index, hpoint⟩
        exact ⟨index, hsub index hpoint⟩⟩ :
          {point : Point3 // point ∈ shading.union})

/-- The isotropic image of the restricted exact-image union. -/
def pureWZ2Proposition64PopularExactImage
    {delta width : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (popular : PureWZ2Proposition64PopularBoxData shading width)
    (scale : ℝ) : Set Point3 :=
  pureWZ2Proposition64IsotropicMap popular.center scale ''
    popular.restricted.union

/-- The exact transported normal after restricting to the popular box and
applying the final isotropic similarity. -/
def pureWZ2Proposition64PopularIsotropicPlaneMap
    {delta width : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (popular : PureWZ2Proposition64PopularBoxData shading width)
    (rawNormal : {point : Point3 // point ∈ shading.union} → Point3)
    {scale : ℝ} (hscale : 0 < scale) :
    {point : Point3 // point ∈
      pureWZ2Proposition64PopularExactImage popular scale} → Point3 :=
  pureWZ2Proposition64IsotropicPlaneMap
    (pureWZ2Proposition64RestrictedPlaneMap
      popular.restricted_subshading rawNormal) popular.center hscale

/-- The popular box fits into the source ball required by the isotropic
retubing.  The factor three is a rational upper bound for `sqrt 3`. -/
theorem PureWZ2Proposition64PopularBoxData.union_subset_closedBall
    {delta width scale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (popular : PureWZ2Proposition64PopularBoxData shading width)
    (hwidth : 0 < width) (hscale : 0 < scale)
    (hbudget : 3 * scale * width ≤ 1) :
    popular.restricted.union ⊆
      Metric.closedBall popular.center (1 / (2 * scale)) := by
  intro point hpoint
  have hbox : point ∈ popular.box := by
    rw [popular.restricted_union] at hpoint
    exact hpoint.2
  have haxis : point ∈ wz1AxisBox popular.center
      (point3 (width / 2) (width / 2) (width / 2)) := by
    rw [popular.box_eq] at hbox
    exact hbox.1
  have hcoord : ∀ i : Fin 3,
      |point i - popular.center i| ≤ width / 2 := by
    intro i
    have hi := haxis i
    fin_cases i <;> simpa [point3] using hi
  have hcoordSq : ∀ i : Fin 3,
      (point i - popular.center i) ^ 2 ≤ (width / 2) ^ 2 := by
    intro i
    simpa [sq_abs] using
      ((sq_le_sq₀ (abs_nonneg (point i - popular.center i))
        (by positivity : 0 ≤ width / 2)).2 (hcoord i))
  have hthree : 3 * width / 2 ≤ 1 / (2 * scale) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * scale)).2
    nlinarith
  rw [Metric.mem_closedBall, dist_eq_norm, EuclideanSpace.norm_eq,
    Real.sqrt_le_iff]
  constructor
  · positivity
  · simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three, PiLp.sub_apply]
    have hsum :
        (point 0 - popular.center 0) ^ 2 +
            (point 1 - popular.center 1) ^ 2 +
            (point 2 - popular.center 2) ^ 2 ≤
          (width / 2) ^ 2 + (width / 2) ^ 2 + (width / 2) ^ 2 :=
      add_le_add (add_le_add (hcoordSq 0) (hcoordSq 1)) (hcoordSq 2)
    have hsq : (3 * width / 2) ^ 2 ≤ (1 / (2 * scale)) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 hthree
    nlinarith [hsum, hsq, sq_nonneg width]

/-- Tighter version used to place the rebased ordinary representatives in the
paper line class after the final isotropic similarity. -/
theorem PureWZ2Proposition64PopularBoxData.union_subset_closedBall_twelve
    {delta width scale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (popular : PureWZ2Proposition64PopularBoxData shading width)
    (hwidth : 0 < width) (hscale : 0 < scale)
    (hbudget : 18 * scale * width ≤ 1) :
    popular.restricted.union ⊆
      Metric.closedBall popular.center (1 / (12 * scale)) := by
  intro point hpoint
  have hbox : point ∈ popular.box := by
    rw [popular.restricted_union] at hpoint
    exact hpoint.2
  have haxis : point ∈ wz1AxisBox popular.center
      (point3 (width / 2) (width / 2) (width / 2)) := by
    rw [popular.box_eq] at hbox
    exact hbox.1
  have hcoord : ∀ i : Fin 3,
      |point i - popular.center i| ≤ width / 2 := by
    intro i
    have hi := haxis i
    fin_cases i <;> simpa [point3] using hi
  have hcoordSq : ∀ i : Fin 3,
      (point i - popular.center i) ^ 2 ≤ (width / 2) ^ 2 := by
    intro i
    simpa [sq_abs] using
      ((sq_le_sq₀ (abs_nonneg (point i - popular.center i))
        (by positivity : 0 ≤ width / 2)).2 (hcoord i))
  have htight : 3 * width / 2 ≤ 1 / (12 * scale) := by
    apply (le_div_iff₀ (by positivity : 0 < 12 * scale)).2
    nlinarith
  rw [Metric.mem_closedBall, dist_eq_norm, EuclideanSpace.norm_eq,
    Real.sqrt_le_iff]
  constructor
  · positivity
  · simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three, PiLp.sub_apply]
    have hsum :
        (point 0 - popular.center 0) ^ 2 +
            (point 1 - popular.center 1) ^ 2 +
            (point 2 - popular.center 2) ^ 2 ≤
          (width / 2) ^ 2 + (width / 2) ^ 2 + (width / 2) ^ 2 :=
      add_le_add (add_le_add (hcoordSq 0) (hcoordSq 1)) (hcoordSq 2)
    have hsq : (3 * width / 2) ^ 2 ≤ (1 / (12 * scale)) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 htight
    nlinarith [hsum, hsq, sq_nonneg width]

/-- Every point in the isotropic popular exact image lies in the radius-one
half ball used in the saturation AD estimate. -/
theorem PureWZ2Proposition64PopularBoxData.isotropic_image_norm_le_half
    {delta width scale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (popular : PureWZ2Proposition64PopularBoxData shading width)
    (hwidth : 0 < width) (hscale : 0 < scale)
    (hbudget : 3 * scale * width ≤ 1) :
    ∀ point : {point : Point3 // point ∈
      pureWZ2Proposition64PopularExactImage popular scale},
      ‖(point : Point3)‖ ≤ 1 / 2 := by
  intro point
  rcases point.property with ⟨source, hsource, hpoint⟩
  have hsourceBall := popular.union_subset_closedBall hwidth hscale hbudget hsource
  rw [Metric.mem_closedBall] at hsourceBall
  change ‖(point : Point3)‖ ≤ 1 / 2
  rw [← hpoint]
  rw [show ‖pureWZ2Proposition64IsotropicMap popular.center scale source‖ =
      scale * dist source popular.center by
        simp [pureWZ2Proposition64IsotropicMap, dist_eq_norm, norm_smul,
          Real.norm_eq_abs, abs_of_pos hscale]]
  calc
    scale * dist source popular.center ≤ scale * (1 / (2 * scale)) := by
      gcongr
    _ = 1 / 2 := by field_simp [hscale.ne']

/-- Uniform ball-distortion budget used when the exact local AD estimate is
transported through the Proposition 6.4 affine map and final isotropic
similarity.  The source scale is `rho / (4 * scale)`. -/
theorem pureWZ2Proposition64_localAD_ball_budget
    {rho targetDelta scale normalization : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (htarget : targetDelta ≤ rho) (htargetNonneg : 0 ≤ targetDelta)
    (hscale : 1 ≤ scale) (hnormalization : 0 ≤ normalization)
    (hlarge : 900 * normalization ^ 2 ≤ scale) :
    3 * normalization * ((Real.sqrt rho + 4 * targetDelta) / scale) ≤
      Real.sqrt (rho / (4 * scale)) := by
  have hsqrtOne : Real.sqrt rho ≤ 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · simpa using hrhoOne
  have hsqrtSq : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt hrho.le
  have hrhoSqrt : rho ≤ Real.sqrt rho := by
    nlinarith [Real.sqrt_nonneg rho]
  have hsum : Real.sqrt rho + 4 * targetDelta ≤ 5 * Real.sqrt rho := by
    linarith
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have hlhsNonneg : 0 ≤ 3 * normalization *
      ((Real.sqrt rho + 4 * targetDelta) / scale) := by positivity
  have hrhsNonneg : 0 ≤ Real.sqrt (rho / (4 * scale)) := Real.sqrt_nonneg _
  rw [← (sq_le_sq₀ hlhsNonneg hrhsNonneg)]
  rw [Real.sq_sqrt (div_nonneg hrho.le (by positivity : 0 ≤ 4 * scale))]
  have hbound :
      3 * normalization * ((Real.sqrt rho + 4 * targetDelta) / scale) ≤
        15 * normalization * Real.sqrt rho / scale := by
    calc
      3 * normalization * ((Real.sqrt rho + 4 * targetDelta) / scale) =
          (3 * normalization * (Real.sqrt rho + 4 * targetDelta)) / scale :=
            by ring
      _ ≤ (3 * normalization * (5 * Real.sqrt rho)) / scale := by
        apply (div_le_div_iff_of_pos_right hscalePos).2
        gcongr
      _ = 15 * normalization * Real.sqrt rho / scale := by ring
  have hbigNonneg : 0 ≤ 15 * normalization * Real.sqrt rho / scale := by
    positivity
  have hsqBound := (sq_le_sq₀ hlhsNonneg hbigNonneg).2 hbound
  apply hsqBound.trans
  rw [div_pow]
  apply (div_le_div_iff₀ (sq_pos_of_pos hscalePos)
    (by positivity : 0 < 4 * scale)).2
  rw [mul_pow, hsqrtSq]
  have hproduct :
      0 ≤ (scale - 900 * normalization ^ 2) * (rho * scale) :=
    mul_nonneg (sub_nonneg.mpr hlarge)
      (mul_nonneg hrho.le (by linarith))
  nlinarith

/-- The inverse-transpose lower bound makes the transported projection scale
`rho / (4 * scale)` admissible for a final request at scale `rho`. -/
theorem pureWZ2Proposition64_localAD_projection_budget
    {rho scale normalNorm : ℝ}
    (hrho : 0 ≤ rho) (hscale : 0 < scale)
    (hnorm : 1 / 4 ≤ normalNorm) :
    (scale / normalNorm) * (rho / (4 * scale)) ≤ rho := by
  have hnormPos : 0 < normalNorm := by linarith
  have hfour : 1 ≤ 4 * normalNorm := by linarith
  calc
    (scale / normalNorm) * (rho / (4 * scale)) =
        rho / (4 * normalNorm) := by
      field_simp [hscale.ne', hnormPos.ne']
    _ ≤ rho / 1 := div_le_div_of_nonneg_left hrho (by norm_num) hfour
    _ = rho := by ring

/-- One small extension constant and a half-scale source radius discharge all
three cubical-saturation error budgets used by the final local grains. -/
theorem pureWZ2Proposition64_saturation_error_budgets
    {sourceDelta finalDelta extensionLipschitz : ℝ}
    (hfinalDelta : 0 < finalDelta) (hfinalDeltaSmall : finalDelta ≤ 1 / 4)
    (hsource : sourceDelta ≤ finalDelta / 2)
    (hsmall : 16 * extensionLipschitz ≤ 1) :
    sourceDelta + 4 * extensionLipschitz * (2 * finalDelta) ≤ finalDelta ∧
    2 * finalDelta + (1 / 2 : ℝ) *
        (4 * extensionLipschitz * (2 * finalDelta)) ≤ 6 * finalDelta ∧
    1 / 10 + 4 * extensionLipschitz * (2 * finalDelta) ≤ 1 / 2 := by
  have herror : 4 * extensionLipschitz * (2 * finalDelta) ≤
      finalDelta / 2 := by
    have hproduct : 0 ≤ (1 - 16 * extensionLipschitz) * finalDelta :=
      mul_nonneg (sub_nonneg.mpr hsmall) hfinalDelta.le
    nlinarith
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith

/-- Canonical source point below a point in the isotropic image of a popular
restriction of the exact `Phi` image. -/
def pureWZ2Proposition64PopularSourcePoint
    {sourceDelta imageDelta width scale : ℝ}
    {g : ℝ → ℝ} {slabCenter anchorHeight halfHeight normalization : ℝ}
    {translation : Point3}
    {hhalfHeight : 0 < halfHeight}
    {hnormalization : 9 ≤ normalization}
    {hsourceDelta : 0 < sourceDelta}
    {hanchorSlope : |g anchorHeight| ≤ 8}
    {hradius : 180 * sourceDelta ≤ 6 * imageDelta}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {hsourceLine : WZ1PaperIsLineClass sourceFamily}
    {himageBox : ∀ index, ∀ point ∈ sourceShading.carrier index,
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point ∈
        Kakeya.Streamlined.axisBox 2 2 2}
    (popular : PureWZ2Proposition64PopularBoxData
      (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization hanchorSlope hradius sourceFamily sourceShading
        hsourceLine himageBox) width)
    (hscale : 0 < scale)
    (targetPoint : {point : Point3 // point ∈
      pureWZ2Proposition64PopularExactImage popular scale}) :
    {point : Point3 // point ∈ sourceShading.union} :=
  pureWZ2Proposition64ExactSourcePoint
    (⟨pureWZ2Proposition64IsotropicSourcePoint popular.center hscale targetPoint, by
      rcases (pureWZ2Proposition64IsotropicSourcePoint
        popular.center hscale targetPoint).property with ⟨index, hpoint⟩
      exact ⟨index, popular.restricted_subshading index hpoint⟩⟩)

/-- Exact local AD on an arbitrary part of the isotropic image of a popular
box.  This is the direct specialization of the affine-plus-isotropic
transport theorem to the canonical exact preimage of the target point. -/
theorem pureWZ2Proposition64_popularExactLocalAD
    {sourceDelta imageDelta width scale sigma sourceRho targetRho
      targetRadius : ℝ}
    {g : ℝ → ℝ} {slabCenter anchorHeight halfHeight normalization : ℝ}
    {translation : Point3}
    {hhalfHeight : 0 < halfHeight}
    {hnormalization : 9 ≤ normalization}
    {hsourceDelta : 0 < sourceDelta}
    {hanchorSlope : |g anchorHeight| ≤ 8}
    {hradius : 180 * sourceDelta ≤ 6 * imageDelta}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {hsourceLine : WZ1PaperIsLineClass sourceFamily}
    {himageBox : ∀ index, ∀ point ∈ sourceShading.carrier index,
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point ∈
        Kakeya.Streamlined.axisBox 2 2 2}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (exactData : @PureWZ2Proposition64ExactPlaneMapData sourceDelta imageDelta
      sigma g slabCenter anchorHeight halfHeight normalization translation
      hhalfHeight hnormalization hsourceDelta hanchorSlope hradius
      sourceFamily sourceShading hsourceLine himageBox C sourceLocal)
    (popular : PureWZ2Proposition64PopularBoxData
      (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization hanchorSlope hradius sourceFamily sourceShading
        hsourceLine himageBox) width)
    (hhalfHeightOne : halfHeight ≤ 1)
    (hscale : 0 < scale)
    (hsourceVertical : ∀ point, |sourceLocal.planeMap point 2| ≤ 1 / 2)
    (targetPoint : {point : Point3 // point ∈
      pureWZ2Proposition64PopularExactImage popular scale})
    (targetSet : Set Point3)
    (htargetImage : targetSet ⊆
      pureWZ2Proposition64PopularExactImage popular scale)
    (htargetBall : targetSet ⊆
      Metric.closedBall (targetPoint : Point3) targetRadius)
    (hsourceRho : sourceDelta ≤ sourceRho)
    (hsourceRhoOne : sourceRho ≤ 1)
    (hball : 3 * normalization * (targetRadius / scale) ≤
      Real.sqrt sourceRho)
    (hbase :
      (scale / ‖pureWZ2Proposition64InverseTranspose (g anchorHeight)
        halfHeight normalization
        (sourceLocal.planeMap
          (pureWZ2Proposition64PopularSourcePoint popular hscale
            targetPoint))‖) *
          sourceRho ≤ targetRho)
    (htargetRho : 0 < targetRho) :
    PureWZ2PaperADSet1
      (scalarProjection
        (pureWZ2Proposition64PopularIsotropicPlaneMap popular
          exactData.planeMap hscale targetPoint) targetSet)
      targetRho (1 - sigma) C := by
  let exactRestricted := pureWZ2Proposition64IsotropicSourcePoint
    popular.center hscale targetPoint
  let exactFull : {point : Point3 // point ∈
      (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization hanchorSlope hradius sourceFamily sourceShading
        hsourceLine himageBox).union} :=
    ⟨exactRestricted, by
      rcases exactRestricted.property with ⟨index, hpoint⟩
      exact ⟨index, popular.restricted_subshading index hpoint⟩⟩
  let sourcePoint := pureWZ2Proposition64ExactSourcePoint exactFull
  have hsourcePointEq : sourcePoint =
      pureWZ2Proposition64PopularSourcePoint popular hscale targetPoint := by
    rfl
  have htargetPoint : (targetPoint : Point3) =
      pureWZ2Proposition64IsotropicMap popular.center scale
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation sourcePoint) := by
    calc
      (targetPoint : Point3) =
          pureWZ2Proposition64IsotropicMap popular.center scale
            exactRestricted :=
        (pureWZ2Proposition64IsotropicMap_sourcePoint
          popular.center hscale targetPoint).symm
      _ = pureWZ2Proposition64IsotropicMap popular.center scale
          exactFull := rfl
      _ = pureWZ2Proposition64IsotropicMap popular.center scale
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation sourcePoint) := by
        apply congrArg (pureWZ2Proposition64IsotropicMap popular.center scale)
        exact (pureWZ2Proposition64Map_exactSourcePoint exactFull).symm
  have hcombinedImage : targetSet ⊆
      (fun source =>
        pureWZ2Proposition64IsotropicMap popular.center scale
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation source)) ''
        sourceShading.union := by
    intro point hpoint
    rcases htargetImage hpoint with ⟨exactPoint, hexactPoint, hpointEq⟩
    have hexactFull : exactPoint ∈
        (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
          anchorHeight halfHeight normalization translation hhalfHeight
          hnormalization hanchorSlope hradius sourceFamily sourceShading
          hsourceLine himageBox).union := by
      rcases hexactPoint with ⟨index, hcarrier⟩
      exact ⟨index, popular.restricted_subshading index hcarrier⟩
    rw [pureWZ2Proposition64ExactImageShading_union] at hexactFull
    rcases hexactFull with ⟨source, hsource, hexactEq⟩
    exact ⟨source, hsource, hpointEq ▸ congrArg
      (pureWZ2Proposition64IsotropicMap popular.center scale) hexactEq⟩
  have hbase' :
      (scale / ‖pureWZ2Proposition64InverseTranspose (g anchorHeight)
        halfHeight normalization (sourceLocal.planeMap sourcePoint)‖) *
          sourceRho ≤ targetRho := by
    rw [hsourcePointEq]
    exact hbase
  have had := pureWZ2Proposition64_exact_isotropic_local_ad_of_image_in_ball
    sourceLocal g slabCenter anchorHeight halfHeight normalization translation
      popular.center hhalfHeight hhalfHeightOne hnormalization hanchorSlope
      hscale sourcePoint (hsourceVertical sourcePoint) targetPoint htargetPoint
      targetSet hcombinedImage htargetBall hsourceRho hsourceRhoOne hball
      hbase' htargetRho
  have hnormalEq :
      pureWZ2Proposition64PopularIsotropicPlaneMap popular
          exactData.planeMap hscale targetPoint =
        pureWZ2Proposition64TransportedNormal (g anchorHeight) halfHeight
          normalization (sourceLocal.planeMap sourcePoint) := by
    rw [exactData.planeMap_eq]
    rfl
  rw [hnormalEq]
  exact had

/-- The exact AD input needed by saturation, with the paper choice
`sourceRho = rho / (4 * scale)` kept explicit. -/
theorem pureWZ2Proposition64_popularExactLocalAD_uniform
    {sourceDelta imageDelta finalDelta width scale sigma : ℝ}
    {g : ℝ → ℝ} {slabCenter anchorHeight halfHeight normalization : ℝ}
    {translation : Point3}
    {hhalfHeight : 0 < halfHeight} {hnormalization : 9 ≤ normalization}
    {hsourceDelta : 0 < sourceDelta}
    {hanchorSlope : |g anchorHeight| ≤ 8}
    {hradius : 180 * sourceDelta ≤ 6 * imageDelta}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {hsourceLine : WZ1PaperIsLineClass sourceFamily}
    {himageBox : ∀ index, ∀ point ∈ sourceShading.carrier index,
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point ∈
        Kakeya.Streamlined.axisBox 2 2 2}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (exactData : @PureWZ2Proposition64ExactPlaneMapData sourceDelta imageDelta
      sigma g slabCenter anchorHeight halfHeight normalization translation
      hhalfHeight hnormalization hsourceDelta hanchorSlope hradius
      sourceFamily sourceShading hsourceLine himageBox C sourceLocal)
    (popular : PureWZ2Proposition64PopularBoxData
      (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization hanchorSlope hradius sourceFamily sourceShading
        hsourceLine himageBox) width)
    (hhalfHeightOne : halfHeight ≤ 1) (hscale : 1 ≤ scale)
    (hlarge : 900 * normalization ^ 2 ≤ scale)
    (hsourceScale : sourceDelta ≤ finalDelta / (4 * scale))
    (hsourceVertical : ∀ point, |sourceLocal.planeMap point 2| ≤ 1 / 2) :
    ∀ rho : ℝ, finalDelta ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈
        pureWZ2Proposition64PopularExactImage popular scale},
        PureWZ2PaperADSet1
          (scalarProjection
            (pureWZ2Proposition64PopularIsotropicPlaneMap popular
              exactData.planeMap (lt_of_lt_of_le zero_lt_one hscale) point)
            (pureWZ2Proposition64PopularExactImage popular scale ∩
              Metric.closedBall (point : Point3)
                (Real.sqrt rho + 2 * (2 * finalDelta))))
          rho (1 - sigma) C := by
  intro rho hrhoLower hrhoOne point
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have hsourceScalePos : 0 < finalDelta / (4 * scale) :=
    lt_of_lt_of_le hsourceDelta hsourceScale
  have hfinalDeltaPos : 0 < finalDelta :=
    (div_pos_iff_of_pos_right (by positivity : 0 < 4 * scale)).mp
      hsourceScalePos
  have hrhoPos : 0 < rho := hfinalDeltaPos.trans_le hrhoLower
  let sourceRho := rho / (4 * scale)
  have hsourceRho : sourceDelta ≤ sourceRho := by
    dsimp only [sourceRho]
    exact hsourceScale.trans <|
      div_le_div_of_nonneg_right hrhoLower (by positivity)
  have hsourceRhoOne : sourceRho ≤ 1 := by
    dsimp only [sourceRho]
    calc
      rho / (4 * scale) ≤ rho := by
        exact div_le_self hrhoPos.le (by nlinarith : 1 ≤ 4 * scale)
      _ ≤ 1 := hrhoOne
  have hball : 3 * normalization *
      ((Real.sqrt rho + 2 * (2 * finalDelta)) / scale) ≤
        Real.sqrt sourceRho := by
    dsimp only [sourceRho]
    convert pureWZ2Proposition64_localAD_ball_budget hrhoPos hrhoOne
      hrhoLower hfinalDeltaPos.le hscale
      (by linarith : 0 ≤ normalization) hlarge using 1 <;> ring
  let sourcePoint := pureWZ2Proposition64PopularSourcePoint popular
    (lt_of_lt_of_le zero_lt_one hscale) point
  have htransportedLower : (1 / 4 : ℝ) ≤
      ‖pureWZ2Proposition64InverseTranspose (g anchorHeight) halfHeight
        normalization (sourceLocal.planeMap sourcePoint)‖ :=
    pureWZ2Proposition64InverseTranspose_norm_lower hanchorSlope
      hnormalization (sourceLocal.planeMap_unit sourcePoint)
        (hsourceVertical sourcePoint)
  have hbase :
      (scale / ‖pureWZ2Proposition64InverseTranspose (g anchorHeight)
        halfHeight normalization (sourceLocal.planeMap sourcePoint)‖) *
          sourceRho ≤ rho :=
    pureWZ2Proposition64_localAD_projection_budget hrhoPos.le
      (lt_of_lt_of_le zero_lt_one hscale) htransportedLower
  exact pureWZ2Proposition64_popularExactLocalAD sourceLocal exactData popular
    hhalfHeightOne (lt_of_lt_of_le zero_lt_one hscale) hsourceVertical point
    _ Set.inter_subset_left Set.inter_subset_right hsourceRho hsourceRhoOne
    hball hbase hrhoPos

/-- A fully saturated target carrier has a nearby exact-image point on the same
source tube, and isotropic dilation does not change the tube direction or its
incidence with the transported normal. -/
theorem pureWZ2Proposition64IsotropicPaperShading_incidenceWitness
    {sourceDelta targetDelta sourceIncidence width scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (rawNormal : {point : Point3 // point ∈ sourceShading.union} → Point3)
    (popular : PureWZ2Proposition64PopularBoxData sourceShading width)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
      2 * targetDelta ≤ 6 * targetDelta)
    (hsourceWindow : popular.restricted.union ⊆
      Metric.closedBall popular.center (1 / (2 * scale)))
    (hincidence : ∀ index point,
      ∀ hpoint : point ∈ popular.restricted.carrier index,
        |inner ℝ (sourceFamily.tube index).direction
          (rawNormal ⟨point, ⟨index,
            popular.restricted_subshading index hpoint⟩⟩)| ≤
              sourceIncidence) :
    ∀ index point,
      ∀ _hpoint : point ∈
        (pureWZ2Proposition64FullIsotropicPaperShading popular.restricted
          popular.center scale hsourceDelta htargetDelta htargetDeltaSmall
            hscale hradius hsourceWindow).carrier index,
        ∃ source : {point : Point3 // point ∈
          pureWZ2Proposition64PopularExactImage popular scale},
          dist point (source : Point3) ≤ 2 * targetDelta ∧
          |inner ℝ
            ((pureWZ2Proposition64IsotropicPaperFamily
              (targetDelta := targetDelta) sourceFamily popular.center
                scale).tube index).direction
            (pureWZ2Proposition64PopularIsotropicPlaneMap popular rawNormal
              (lt_of_lt_of_le zero_lt_one hscale) source)| ≤
                sourceIncidence := by
  intro index point hpoint
  change Fin sourceFamily.card at index
  rcases hpoint with ⟨imagePoint, himagePoint, hcell⟩
  rcases himagePoint with ⟨original, horiginal, himage⟩
  refine ⟨⟨imagePoint, ⟨original, ⟨index, horiginal⟩, himage⟩⟩, ?_, ?_⟩
  · exact le_of_lt <|
      wz1_paper_grid_cube_diameter_lt_two_rho htargetDelta
        (cell := wz1PaperGridIndex targetDelta point)
        ((mem_wz1PaperGridCube _ _ _).mpr rfl)
        ((mem_wz1PaperGridCube _ _ _).mpr hcell.symm)
  · subst imagePoint
    let restrictedPoint : {point : Point3 // point ∈ popular.restricted.union} :=
      ⟨original, ⟨index, horiginal⟩⟩
    let isotropicPoint : {point : Point3 // point ∈
        pureWZ2Proposition64PopularExactImage popular scale} :=
      ⟨pureWZ2Proposition64IsotropicMap popular.center scale original,
        ⟨original, ⟨index, horiginal⟩, rfl⟩⟩
    have hsourceEq :
        pureWZ2Proposition64IsotropicSourcePoint popular.center
            (lt_of_lt_of_le zero_lt_one hscale)
            isotropicPoint =
          restrictedPoint := by
      apply Subtype.ext
      exact pureWZ2Proposition64IsotropicInverse_map popular.center
        (lt_of_lt_of_le zero_lt_one hscale) original
    change |inner ℝ (sourceFamily.tube index).direction
      (pureWZ2Proposition64RestrictedPlaneMap
        popular.restricted_subshading rawNormal
          (pureWZ2Proposition64IsotropicSourcePoint popular.center
            (lt_of_lt_of_le zero_lt_one hscale) _))| ≤ sourceIncidence
    rw [hsourceEq]
    exact hincidence index original horiginal

/-- The local-geometric output of the paper's Lemma 3.5 operation, before
the final AD budget is discharged.  Its exact image is the isotropic image of
the popular restriction, rather than an unrelated carrier. -/
structure PureWZ2Proposition64Lemma35LocalCleanupData
    {sourceDelta targetDelta width scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (rawNormal : {point : Point3 // point ∈ sourceShading.union} → Point3)
    (targetK : NNReal)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
      2 * targetDelta ≤ 6 * targetDelta) where
  popular : PureWZ2Proposition64PopularBoxData sourceShading width
  sourceWindow : popular.restricted.union ⊆
    Metric.closedBall popular.center (1 / (2 * scale))
  exactNormal : {point : Point3 // point ∈
    pureWZ2Proposition64PopularExactImage popular scale} → Point3
  exactNormal_eq : exactNormal =
    pureWZ2Proposition64PopularIsotropicPlaneMap popular rawNormal
      (lt_of_lt_of_le zero_lt_one hscale)
  exactNormal_lipschitz : LipschitzWith targetK exactNormal
  exactNormal_unit : ∀ point, ‖exactNormal point‖ = 1
  saturation : PureWZ2Proposition64SaturationPlaneMapData
    (pureWZ2Proposition64PopularExactImage popular scale)
    (pureWZ2Proposition64FullIsotropicPaperShading popular.restricted
      popular.center scale hsourceDelta htargetDelta htargetDeltaSmall hscale
        hradius sourceWindow).union
    exactNormal (2 * targetDelta)
      (4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        (2 * targetDelta))
  sourceParent : Fin sourceFamily.card → Fin sourceFamily.card
  sourceParent_eq : sourceParent = id
  axis_provenance : ∀ target,
    tubeAxisLine
        ((pureWZ2Proposition64IsotropicPaperFamily
          (targetDelta := targetDelta) sourceFamily popular.center scale).tube
            target) =
      pureWZ2Proposition64IsotropicMap popular.center scale ''
        tubeAxisLine (sourceFamily.tube (sourceParent target))
  cubical : WZ1PaperIsCubicalShading
    (pureWZ2Proposition64FullIsotropicPaperShading popular.restricted
      popular.center scale hsourceDelta htargetDelta htargetDeltaSmall hscale
        hradius sourceWindow)

/-- Select the popular box, perform the one isotropic similarity, saturate in
the final grid, and extend/normalize the transported exact plane field. -/
theorem pureWZ2Proposition64_assembleLemma35LocalCleanup
    {sourceDelta targetDelta width scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (rawNormal : {point : Point3 // point ∈ sourceShading.union} → Point3)
    {sourceK targetK : NNReal}
    (hrawLipschitz : LipschitzWith sourceK rawNormal)
    (hrawUnit : ∀ point, ‖rawNormal point‖ = 1)
    (hwidth : 0 < width) (hwidthOne : width ≤ 1)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hboxScale : 3 * scale * width ≤ 1)
    (hradius : scale * (6 * sourceDelta) +
      2 * targetDelta ≤ 6 * targetDelta)
    (hK : (sourceK : ℝ) ≤ (targetK : ℝ) * scale)
    (hsmall :
      ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        (2 * targetDelta) ≤ 1 / 2)
    (hone :
      4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) ≤ 1) :
    Nonempty (PureWZ2Proposition64Lemma35LocalCleanupData
      (width := width) (scale := scale) sourceShading rawNormal targetK
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius) := by
  rcases pureWZ2Proposition64_selectPopularBox sourceShading hwidth hwidthOne with
    ⟨popular⟩
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have hsourceWindow := popular.union_subset_closedBall
    hwidth hscalePos hboxScale
  let exactImage := pureWZ2Proposition64PopularExactImage popular scale
  let exactNormal : {point : Point3 // point ∈ exactImage} → Point3 :=
    pureWZ2Proposition64PopularIsotropicPlaneMap popular rawNormal hscalePos
  have hrestrictedLipschitz : LipschitzWith sourceK
      (pureWZ2Proposition64RestrictedPlaneMap
        popular.restricted_subshading rawNormal) :=
    pureWZ2Proposition64RestrictedPlaneMap_lipschitz
      popular.restricted_subshading hrawLipschitz
  have hexactLipschitz : LipschitzWith targetK exactNormal := by
    exact pureWZ2Proposition64IsotropicPlaneMap_lipschitz
      hrestrictedLipschitz popular.center hscalePos hK
  have hexactUnit : ∀ point, ‖exactNormal point‖ = 1 := by
    intro point
    exact pureWZ2Proposition64IsotropicPlaneMap_unit
      (pureWZ2Proposition64RestrictedPlaneMap
        popular.restricted_subshading rawNormal)
      (fun source => hrawUnit _) popular.center hscalePos point
  let targetShading := pureWZ2Proposition64FullIsotropicPaperShading
    popular.restricted popular.center scale hsourceDelta htargetDelta
      htargetDeltaSmall hscale hradius hsourceWindow
  have htargetWitness : ∀ point : {point : Point3 // point ∈ targetShading.union},
      ∃ source : {point : Point3 // point ∈ exactImage},
        dist (point : Point3) (source : Point3) ≤ 2 * targetDelta := by
    exact pureWZ2Proposition64FullIsotropicPaperShading_targetWitness
      popular.restricted popular.center scale hsourceDelta htargetDelta
        htargetDeltaSmall hscale hradius hsourceWindow
  rcases pureWZ2Proposition64_extendPlaneMapToSaturation
      hexactLipschitz hexactUnit (by positivity : 0 ≤ 2 * targetDelta)
      htargetWitness hsmall hone with ⟨saturation⟩
  refine ⟨{
    popular := popular
    sourceWindow := hsourceWindow
    exactNormal := exactNormal
    exactNormal_eq := rfl
    exactNormal_lipschitz := hexactLipschitz
    exactNormal_unit := hexactUnit
    saturation := saturation
    sourceParent := id
    sourceParent_eq := rfl
    axis_provenance := ?_
    cubical := pureWZ2Proposition64FullIsotropicPaperShading_cubical
      popular.restricted popular.center scale hsourceDelta htargetDelta
        htargetDeltaSmall hscale hradius hsourceWindow }⟩
  intro target
  change tubeAxisLine (pureWZ2Proposition64IsotropicRebasedPaperTube
      (targetDelta := targetDelta) popular.center scale
        (sourceFamily.tube target)) = _
  exact pureWZ2Proposition64IsotropicRebasedPaperTube_axis
    (targetDelta := targetDelta) popular.center hscalePos
      (sourceFamily.tube target)

namespace PureWZ2Proposition64Lemma35LocalCleanupData

/-- The final saturated paper shading carried by a local cleanup package. -/
def finalShading
    {sourceDelta targetDelta width scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rawNormal : {point : Point3 // point ∈ sourceShading.union} → Point3}
    {targetK : NNReal}
    {hsourceDelta : 0 < sourceDelta} {htargetDelta : 0 < targetDelta}
    {htargetDeltaSmall : targetDelta ≤ 1 / 4}
    {hscale : 1 ≤ scale}
    {hradius : scale * (6 * sourceDelta) +
      2 * targetDelta ≤ 6 * targetDelta}
    (data : PureWZ2Proposition64Lemma35LocalCleanupData
      (width := width) (scale := scale) sourceShading rawNormal targetK
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius) :
    WZ1PaperTubeShading
      (pureWZ2Proposition64IsotropicPaperFamily
        (targetDelta := targetDelta) sourceFamily data.popular.center scale) :=
  pureWZ2Proposition64FullIsotropicPaperShading data.popular.restricted
    data.popular.center scale hsourceDelta htargetDelta htargetDeltaSmall hscale
      hradius data.sourceWindow

/-- The exact isotropic image in a cleanup package lies in the radius-one-half
ball.  This uses the stored popular-box containment, so downstream consumers
do not need to reconstruct its coordinate proof. -/
theorem exactImage_norm_le_half
    {sourceDelta targetDelta width scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rawNormal : {point : Point3 // point ∈ sourceShading.union} → Point3}
    {targetK : NNReal}
    {hsourceDelta : 0 < sourceDelta} {htargetDelta : 0 < targetDelta}
    {htargetDeltaSmall : targetDelta ≤ 1 / 4}
    {hscale : 1 ≤ scale}
    {hradius : scale * (6 * sourceDelta) +
      2 * targetDelta ≤ 6 * targetDelta}
    (data : PureWZ2Proposition64Lemma35LocalCleanupData
      (width := width) (scale := scale) sourceShading rawNormal targetK
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius) :
    ∀ point : {point : Point3 // point ∈
      pureWZ2Proposition64PopularExactImage data.popular scale},
      ‖(point : Point3)‖ ≤ 1 / 2 := by
  intro point
  rcases point.property with ⟨source, hsource, hpoint⟩
  have hsourceBall := data.sourceWindow hsource
  rw [Metric.mem_closedBall] at hsourceBall
  change ‖(point : Point3)‖ ≤ 1 / 2
  rw [← hpoint]
  rw [show ‖pureWZ2Proposition64IsotropicMap data.popular.center scale source‖ =
      scale * dist source data.popular.center by
        simp [pureWZ2Proposition64IsotropicMap, dist_eq_norm, norm_smul,
          Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le zero_lt_one hscale)]]
  calc
    scale * dist source data.popular.center ≤
        scale * (1 / (2 * scale)) := by gcongr
    _ = 1 / 2 := by
      field_simp [(lt_of_lt_of_le zero_lt_one hscale).ne']

/-- The exact-image incidence witness specialized to the exact normal stored
in the cleanup package. -/
theorem incidenceWitness
    {sourceDelta targetDelta sourceIncidence width scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rawNormal : {point : Point3 // point ∈ sourceShading.union} → Point3}
    {targetK : NNReal}
    {hsourceDelta : 0 < sourceDelta} {htargetDelta : 0 < targetDelta}
    {htargetDeltaSmall : targetDelta ≤ 1 / 4}
    {hscale : 1 ≤ scale}
    {hradius : scale * (6 * sourceDelta) +
      2 * targetDelta ≤ 6 * targetDelta}
    (data : PureWZ2Proposition64Lemma35LocalCleanupData
      (width := width) (scale := scale) sourceShading rawNormal targetK
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius)
    (hincidence : ∀ index point,
      ∀ hpoint : point ∈ data.popular.restricted.carrier index,
        |inner ℝ (sourceFamily.tube index).direction
          (rawNormal ⟨point, ⟨index,
            data.popular.restricted_subshading index hpoint⟩⟩)| ≤
              sourceIncidence) :
    ∀ index point,
      ∀ _hpoint : point ∈ data.finalShading.carrier index,
        ∃ source : {point : Point3 // point ∈
          pureWZ2Proposition64PopularExactImage data.popular scale},
          dist point (source : Point3) ≤ 2 * targetDelta ∧
          |inner ℝ
            ((pureWZ2Proposition64IsotropicPaperFamily
              (targetDelta := targetDelta) sourceFamily data.popular.center
                scale).tube index).direction
              (data.exactNormal source)| ≤ sourceIncidence := by
  intro index point hpoint
  rcases pureWZ2Proposition64IsotropicPaperShading_incidenceWitness
      sourceShading rawNormal data.popular hsourceDelta htargetDelta
      htargetDeltaSmall hscale hradius data.sourceWindow hincidence
      index point hpoint with ⟨source, hdist, hsource⟩
  refine ⟨source, hdist, ?_⟩
  rw [data.exactNormal_eq]
  exact hsource

/-- Final local grains after the exact-image AD input has been transported
through the isotropic image and enlarged to the saturated paper shading. -/
noncomputable def toLocalGrainData
    {sourceDelta targetDelta sourceIncidence width scale sigma pointBound : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rawNormal : {point : Point3 // point ∈ sourceShading.union} → Point3}
    {targetK : NNReal} {C : ENNReal}
    {hsourceDelta : 0 < sourceDelta} {htargetDelta : 0 < targetDelta}
    {htargetDeltaSmall : targetDelta ≤ 1 / 4}
    {hscale : 1 ≤ scale}
    {hradius : scale * (6 * sourceDelta) +
      2 * targetDelta ≤ 6 * targetDelta}
    (data : PureWZ2Proposition64Lemma35LocalCleanupData
      (width := width) (scale := scale) sourceShading rawNormal targetK
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 // point ∈
      pureWZ2Proposition64PopularExactImage data.popular scale},
        ‖(source : Point3)‖ ≤ pointBound)
    (hincidence : ∀ index point,
      ∀ hpoint : point ∈ data.popular.restricted.carrier index,
        |inner ℝ (sourceFamily.tube index).direction
          (rawNormal ⟨point, ⟨index,
            data.popular.restricted_subshading index hpoint⟩⟩)| ≤
              sourceIncidence)
    (hincidenceBudget : sourceIncidence +
      4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        (2 * targetDelta) ≤ targetDelta)
    (hprojectionBudget : 2 * targetDelta + pointBound *
      (4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        (2 * targetDelta)) ≤ 6 * targetDelta)
    (hexactAD : ∀ rho : ℝ, targetDelta ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ data.finalShading.union},
        PureWZ2PaperADSet1
          (scalarProjection (data.exactNormal (data.saturation.sourcePoint point))
            (pureWZ2Proposition64PopularExactImage data.popular scale ∩
              Metric.closedBall (data.saturation.sourcePoint point : Point3)
                (Real.sqrt rho + 2 * (2 * targetDelta))))
          rho (1 - sigma) C) :
    PureWZ2LocalGrainData data.finalShading sigma (192 * C) :=
  data.saturation.toLocalGrainDataSixDelta
    (by positivity : 0 ≤ 2 * targetDelta)
    (by positivity : 0 ≤
      4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        (2 * targetDelta))
    hpointBound hexactBound (data.incidenceWitness hincidence)
    hincidenceBudget hprojectionBudget hexactAD

/-- The vertical bound for the final local grains, with the exact transported
normal bound and saturation error shown separately. -/
theorem toLocalGrainData_vertical_bound
    {sourceDelta targetDelta sourceIncidence width scale sigma pointBound : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rawNormal : {point : Point3 // point ∈ sourceShading.union} → Point3}
    {targetK : NNReal} {C : ENNReal}
    {hsourceDelta : 0 < sourceDelta} {htargetDelta : 0 < targetDelta}
    {htargetDeltaSmall : targetDelta ≤ 1 / 4}
    {hscale : 1 ≤ scale}
    {hradius : scale * (6 * sourceDelta) +
      2 * targetDelta ≤ 6 * targetDelta}
    (data : PureWZ2Proposition64Lemma35LocalCleanupData
      (width := width) (scale := scale) sourceShading rawNormal targetK
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 // point ∈
      pureWZ2Proposition64PopularExactImage data.popular scale},
        ‖(source : Point3)‖ ≤ pointBound)
    (hincidence : ∀ index point,
      ∀ hpoint : point ∈ data.popular.restricted.carrier index,
        |inner ℝ (sourceFamily.tube index).direction
          (rawNormal ⟨point, ⟨index,
            data.popular.restricted_subshading index hpoint⟩⟩)| ≤
              sourceIncidence)
    (hincidenceBudget : sourceIncidence +
      4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        (2 * targetDelta) ≤ targetDelta)
    (hprojectionBudget : 2 * targetDelta + pointBound *
      (4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        (2 * targetDelta)) ≤ 6 * targetDelta)
    (hexactAD : ∀ rho : ℝ, targetDelta ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ data.finalShading.union},
        PureWZ2PaperADSet1
          (scalarProjection (data.exactNormal (data.saturation.sourcePoint point))
            (pureWZ2Proposition64PopularExactImage data.popular scale ∩
              Metric.closedBall (data.saturation.sourcePoint point : Point3)
                (Real.sqrt rho + 2 * (2 * targetDelta))))
          rho (1 - sigma) C)
    (hexactVertical : ∀ source : {point : Point3 // point ∈
      pureWZ2Proposition64PopularExactImage data.popular scale},
        |data.exactNormal source 2| ≤ 1 / 10)
    (hverticalBudget : 1 / 10 +
      4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        (2 * targetDelta) ≤ 1 / 2) :
    ∀ point : {point : Point3 // point ∈ data.finalShading.union},
      |(data.toLocalGrainData hpointBound hexactBound hincidence
        hincidenceBudget hprojectionBudget hexactAD).planeMap point 2| ≤
          1 / 2 := by
  exact data.saturation.toLocalGrainDataSixDelta_vertical_bound
    (by positivity : 0 ≤ 2 * targetDelta)
    (by positivity : 0 ≤
      4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        (2 * targetDelta))
    hpointBound hexactBound (data.incidenceWitness hincidence)
    hincidenceBudget hprojectionBudget hexactAD hexactVertical hverticalBudget

/-- Specialize the generic saturation wrapper to the exact Proposition 6.4
plane field.  All local AD information comes from the original source local
grains through the exact affine map and the one isotropic similarity. -/
noncomputable def toExactLocalGrainData
    {sourceDelta imageDelta finalDelta width scale sigma : ℝ}
    {g : ℝ → ℝ} {slabCenter anchorHeight halfHeight normalization : ℝ}
    {translation : Point3}
    {hhalfHeight : 0 < halfHeight} {hnormalization : 9 ≤ normalization}
    {hsourceDelta : 0 < sourceDelta}
    {hanchorSlope : |g anchorHeight| ≤ 8}
    {himageRadius : 180 * sourceDelta ≤ 6 * imageDelta}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {hsourceLine : WZ1PaperIsLineClass sourceFamily}
    {himageBox : ∀ index, ∀ point ∈ sourceShading.carrier index,
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point ∈
        Kakeya.Streamlined.axisBox 2 2 2}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (exactData : @PureWZ2Proposition64ExactPlaneMapData sourceDelta imageDelta
      sigma g slabCenter anchorHeight halfHeight normalization translation
      hhalfHeight hnormalization hsourceDelta hanchorSlope himageRadius
      sourceFamily sourceShading hsourceLine himageBox C sourceLocal)
    {targetK : NNReal}
    {htargetDelta : 0 < finalDelta}
    {htargetDeltaSmall : finalDelta ≤ 1 / 4}
    {hscale : 1 ≤ scale}
    {hretubeRadius : scale * (6 * imageDelta) +
      2 * finalDelta ≤ 6 * finalDelta}
    (data : PureWZ2Proposition64Lemma35LocalCleanupData
      (width := width) (scale := scale)
      (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization hanchorSlope himageRadius sourceFamily sourceShading
        hsourceLine himageBox) exactData.planeMap targetK
      (by linarith : 0 < imageDelta) htargetDelta htargetDeltaSmall hscale
        hretubeRadius)
    (hhalfHeightOne : halfHeight ≤ 1)
    (hlarge : 900 * normalization ^ 2 ≤ scale)
    (hsourceScale : sourceDelta ≤ finalDelta / (4 * scale))
    (hsourceVertical : ∀ point, |sourceLocal.planeMap point 2| ≤ 1 / 2)
    (hincidenceBudget : sourceDelta +
      4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        (2 * finalDelta) ≤ finalDelta)
    (hprojectionBudget : 2 * finalDelta + (1 / 2 : ℝ) *
      (4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        (2 * finalDelta)) ≤ 6 * finalDelta) :
    PureWZ2LocalGrainData data.finalShading sigma (192 * C) := by
  apply data.toLocalGrainData (sourceIncidence := sourceDelta)
    (pointBound := (1 / 2 : ℝ)) (C := C) (by norm_num)
    data.exactImage_norm_le_half
  · intro index point hpoint
    exact exactData.planeMap_incidence_source index point
      (data.popular.restricted_subshading index hpoint)
  · exact hincidenceBudget
  · exact hprojectionBudget
  · intro rho hrhoLower hrhoOne point
    let exactPoint := data.saturation.sourcePoint point
    have had := pureWZ2Proposition64_popularExactLocalAD_uniform sourceLocal
      exactData data.popular hhalfHeightOne hscale hlarge hsourceScale
      hsourceVertical rho hrhoLower hrhoOne exactPoint
    have hnormal : data.exactNormal exactPoint =
        pureWZ2Proposition64PopularIsotropicPlaneMap data.popular
          exactData.planeMap (lt_of_lt_of_le zero_lt_one hscale) exactPoint := by
      exact congrFun data.exactNormal_eq exactPoint
    rw [hnormal]
    exact had

/-- The final exact local-grain package retains the anchored-chart vertical
normal bound after the cubical saturation. -/
theorem toExactLocalGrainData_vertical_bound
    {sourceDelta imageDelta finalDelta width scale sigma : ℝ}
    {g : ℝ → ℝ} {slabCenter anchorHeight halfHeight normalization : ℝ}
    {translation : Point3}
    {hhalfHeight : 0 < halfHeight} {hnormalization : 9 ≤ normalization}
    {hsourceDelta : 0 < sourceDelta}
    {hanchorSlope : |g anchorHeight| ≤ 8}
    {himageRadius : 180 * sourceDelta ≤ 6 * imageDelta}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {hsourceLine : WZ1PaperIsLineClass sourceFamily}
    {himageBox : ∀ index, ∀ point ∈ sourceShading.carrier index,
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point ∈
        Kakeya.Streamlined.axisBox 2 2 2}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (exactData : @PureWZ2Proposition64ExactPlaneMapData sourceDelta imageDelta
      sigma g slabCenter anchorHeight halfHeight normalization translation
      hhalfHeight hnormalization hsourceDelta hanchorSlope himageRadius
      sourceFamily sourceShading hsourceLine himageBox C sourceLocal)
    {targetK : NNReal}
    {htargetDelta : 0 < finalDelta}
    {htargetDeltaSmall : finalDelta ≤ 1 / 4}
    {hscale : 1 ≤ scale}
    {hretubeRadius : scale * (6 * imageDelta) +
      2 * finalDelta ≤ 6 * finalDelta}
    (data : PureWZ2Proposition64Lemma35LocalCleanupData
      (width := width) (scale := scale)
      (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization hanchorSlope himageRadius sourceFamily sourceShading
        hsourceLine himageBox) exactData.planeMap targetK
      (by linarith : 0 < imageDelta) htargetDelta htargetDeltaSmall hscale
        hretubeRadius)
    (hhalfHeightOne : halfHeight ≤ 1)
    (hlarge : 900 * normalization ^ 2 ≤ scale)
    (hsourceScale : sourceDelta ≤ finalDelta / (4 * scale))
    (hsourceVertical : ∀ point, |sourceLocal.planeMap point 2| ≤ 1 / 2)
    (hincidenceBudget : sourceDelta +
      4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        (2 * finalDelta) ≤ finalDelta)
    (hprojectionBudget : 2 * finalDelta + (1 / 2 : ℝ) *
      (4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        (2 * finalDelta)) ≤ 6 * finalDelta)
    (hverticalBudget : 1 / 10 +
      4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        (2 * finalDelta) ≤ 1 / 2) :
    ∀ point : {point : Point3 // point ∈ data.finalShading.union},
      |(data.toExactLocalGrainData sourceLocal exactData hhalfHeightOne hlarge
        hsourceScale hsourceVertical hincidenceBudget hprojectionBudget).planeMap
          point 2| ≤ 1 / 2 := by
  let hincidence := fun index point hpoint =>
    exactData.planeMap_incidence_source index point
      (data.popular.restricted_subshading index hpoint)
  have hexactAD : ∀ rho : ℝ, finalDelta ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ data.finalShading.union},
        PureWZ2PaperADSet1
          (scalarProjection (data.exactNormal (data.saturation.sourcePoint point))
            (pureWZ2Proposition64PopularExactImage data.popular scale ∩
              Metric.closedBall (data.saturation.sourcePoint point : Point3)
                (Real.sqrt rho + 2 * (2 * finalDelta))))
          rho (1 - sigma) C := by
    intro rho hrhoLower hrhoOne point
    let exactPoint := data.saturation.sourcePoint point
    have had := pureWZ2Proposition64_popularExactLocalAD_uniform sourceLocal
      exactData data.popular hhalfHeightOne hscale hlarge hsourceScale
      hsourceVertical rho hrhoLower hrhoOne exactPoint
    have hnormal : data.exactNormal exactPoint =
        pureWZ2Proposition64PopularIsotropicPlaneMap data.popular
          exactData.planeMap (lt_of_lt_of_le zero_lt_one hscale) exactPoint := by
      exact congrFun data.exactNormal_eq exactPoint
    rw [hnormal]
    exact had
  have hexactVertical : ∀ source : {point : Point3 // point ∈
      pureWZ2Proposition64PopularExactImage data.popular scale},
      |data.exactNormal source 2| ≤ 1 / 10 := by
    intro source
    have hnormal : data.exactNormal source =
        pureWZ2Proposition64PopularIsotropicPlaneMap data.popular
          exactData.planeMap (lt_of_lt_of_le zero_lt_one hscale) source := by
      exact congrFun data.exactNormal_eq source
    rw [hnormal]
    let restrictedPoint := pureWZ2Proposition64IsotropicSourcePoint
      data.popular.center (lt_of_lt_of_le zero_lt_one hscale) source
    let fullPoint : {point : Point3 // point ∈
        (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
          anchorHeight halfHeight normalization translation hhalfHeight
          hnormalization hanchorSlope himageRadius sourceFamily sourceShading
          hsourceLine himageBox).union} :=
      ⟨restrictedPoint, by
        rcases restrictedPoint.property with ⟨index, hpoint⟩
        exact ⟨index, data.popular.restricted_subshading index hpoint⟩⟩
    exact exactData.planeMap_vertical_bound fullPoint
  exact data.saturation.toLocalGrainDataSixDelta_vertical_bound
    (by positivity : 0 ≤ 2 * finalDelta)
    (by positivity : 0 ≤
      4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        (2 * finalDelta))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) data.exactImage_norm_le_half
    (data.incidenceWitness hincidence) hincidenceBudget hprojectionBudget
    hexactAD hexactVertical hverticalBudget

end PureWZ2Proposition64Lemma35LocalCleanupData

end Kakeya.Assouad

end
