import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.VerticalNormalization

/-!
# The affine map from Proposition 6.4

This file names the exact coordinate change used in `wz2_64.tex`.  A source
slab `slabCenter + halfHeight * [-1,1]` is sent to the standard height
interval, and the first horizontal coordinate is sheared by the fixed value
`g anchorHeight` at a genuinely occupied slab height and normalized by one
fixed constant.  The second coordinate is unchanged.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- Proposition 6.4's affine normalization
`(x,y,z) ↦ (C⁻¹ (x + g(z_*)y), y, (z-c)/h)`.  The slab center `c`
and the occupied anchor height `z_*` are deliberately separate parameters. -/
def pureWZ2Proposition64Map
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (point : Point3) : Point3 :=
  point3
    ((point 0 + g anchorHeight * point 1) / normalization)
    (point 1)
    ((point 2 - slabCenter) / halfHeight)

/-- The inessential fixed translation allowed immediately after the displayed
map in Proposition 6.4.  It is kept explicit because the paper's subsequent
Lemma-3.5 window selection uses it to return to the standard line chart. -/
def pureWZ2Proposition64TranslatedMap
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation point : Point3) : Point3 :=
  pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
      normalization point + translation

@[simp] theorem pureWZ2Proposition64TranslatedMap_apply_two
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation point : Point3) :
    pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation point 2 =
      (point 2 - slabCenter) / halfHeight + translation 2 := by
  simp [pureWZ2Proposition64TranslatedMap,
    pureWZ2Proposition64Map, point3]

/-- The fixed translation does not change affine differences. -/
theorem pureWZ2Proposition64TranslatedMap_sub
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation first second : Point3) :
    pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation first -
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation second =
      pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
          normalization first -
        pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
          normalization second := by
  simp [pureWZ2Proposition64TranslatedMap]

/-- A horizontal fixed translation shifts every slice projection by the
corresponding scalar inner product. -/
theorem pureWZ2Proposition64TranslatedMap_slice_projection
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation direction : Point3) (source : Set Point3) (z : ℝ)
    (htranslationHeight : translation 2 = 0) :
    scalarProjection direction
        (horizontalSlice
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation '' source) z) =
      (fun value : ℝ => value + inner ℝ translation direction) ''
        scalarProjection direction
          (horizontalSlice
            (pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
              normalization '' source) z) := by
  ext value
  constructor
  · rintro ⟨translatedPoint,
      ⟨⟨sourcePoint, hsourcePoint, rfl⟩, hheight⟩, rfl⟩
    let imagePoint :=
      pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
        normalization sourcePoint
    have himageHeight : imagePoint 2 = z := by
      have hsum : imagePoint 2 + translation 2 = z := by
        simpa [imagePoint, pureWZ2Proposition64TranslatedMap] using hheight
      rw [htranslationHeight] at hsum
      simpa using hsum
    refine ⟨inner ℝ imagePoint direction,
      ⟨imagePoint, ⟨⟨sourcePoint, hsourcePoint, rfl⟩, himageHeight⟩, rfl⟩, ?_⟩
    simp [pureWZ2Proposition64TranslatedMap, imagePoint, inner_add_left]
  · rintro ⟨sourceValue,
      ⟨imagePoint, ⟨⟨sourcePoint, hsourcePoint, himagePoint⟩, hheight⟩,
        hsourceValue⟩, rfl⟩
    subst imagePoint
    subst sourceValue
    refine
      ⟨pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation sourcePoint,
        ⟨⟨sourcePoint, hsourcePoint, rfl⟩, ?_⟩, ?_⟩
    · simp [pureWZ2Proposition64TranslatedMap, hheight, htranslationHeight]
    · simp [pureWZ2Proposition64TranslatedMap, inner_add_left]

/-- Linear part of the exact Proposition 6.4 coordinate change. -/
def pureWZ2Proposition64Linear
    (anchorSlope halfHeight normalization : ℝ) : Point3 →ₗ[ℝ] Point3 where
  toFun point := point3
    ((point 0 + anchorSlope * point 1) / normalization)
    (point 1)
    (point 2 / halfHeight)
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> simp [point3] <;> ring
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;> simp [point3] <;> ring

/-- The linear part is injective whenever the two scale factors are positive. -/
theorem pureWZ2Proposition64Linear_injective
    {anchorSlope halfHeight normalization : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization) :
    Function.Injective
      (pureWZ2Proposition64Linear anchorSlope halfHeight normalization) := by
  intro first second heq
  have hzero := congrArg (fun point : Point3 => point 0) heq
  have hone := congrArg (fun point : Point3 => point 1) heq
  have htwo := congrArg (fun point : Point3 => point 2) heq
  simp only [pureWZ2Proposition64Linear, LinearMap.coe_mk, AddHom.coe_mk]
    at hzero hone htwo
  simp [point3] at hzero hone htwo
  have hone' : first 1 = second 1 := hone
  have htwo' : first 2 = second 2 :=
    (div_left_inj' hhalfHeight.ne').mp htwo
  have hzero' : first 0 = second 0 := by
    apply (add_left_inj (a := anchorSlope * first 1)).mp
    apply (div_left_inj' hnormalization.ne').mp
    simpa [hone'] using hzero
  ext coordinate
  fin_cases coordinate
  · exact hzero'
  · exact hone'
  · exact htwo'

/-- The exact Proposition 6.4 map as an affine equivalence. -/
noncomputable def pureWZ2Proposition64AffineEquiv
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization) : Point3 ≃ᵃ[ℝ] Point3 :=
  AffineEquiv.ofLinearEquiv
    (LinearEquiv.ofInjectiveEndo
      (pureWZ2Proposition64Linear
        (g anchorHeight) halfHeight normalization)
      (pureWZ2Proposition64Linear_injective
        hhalfHeight hnormalization))
    (point3 0 0 slabCenter) 0

/-- The exact Proposition 6.4 affine equivalence followed by the fixed
horizontal translation used in the Lemma-3.5 window selection. -/
noncomputable def pureWZ2Proposition64TranslatedAffineEquiv
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization) : Point3 ≃ᵃ[ℝ] Point3 :=
  (pureWZ2Proposition64AffineEquiv g slabCenter anchorHeight halfHeight
      normalization hhalfHeight hnormalization).trans
    (AffineEquiv.constVAdd ℝ Point3 translation)

/-- The determinant of the exact Proposition 6.4 linear part.  In
particular, the fixed shear has determinant one and the Jacobian is
`1 / (normalization * halfHeight)`, exactly as in the paper. -/
theorem pureWZ2Proposition64Linear_det
    (anchorSlope halfHeight normalization : ℝ) :
    LinearMap.det
        (pureWZ2Proposition64Linear anchorSlope halfHeight normalization) =
      1 / (normalization * halfHeight) := by
  let basis : Module.Basis (Fin 3) ℝ Point3 :=
    PiLp.basisFun 2 ℝ (Fin 3)
  have hmatrix :
      LinearMap.toMatrix basis basis
          (pureWZ2Proposition64Linear anchorSlope halfHeight normalization) =
        !![1 / normalization, anchorSlope / normalization, 0;
           0, 1, 0;
           0, 0, 1 / halfHeight] := by
    ext i j
    have hentry :
        (LinearMap.toMatrix basis basis
          (pureWZ2Proposition64Linear anchorSlope halfHeight normalization)) i j =
          (pureWZ2Proposition64Linear anchorSlope halfHeight normalization
            (basis j)) i := by
      simp [LinearMap.toMatrix_apply]
      rfl
    rw [hentry]
    fin_cases i <;> fin_cases j <;>
      simp [pureWZ2Proposition64Linear, point3, basis,
        PiLp.basisFun_apply]
  rw [← LinearMap.det_toMatrix basis, hmatrix]
  simp [Matrix.det_fin_three]
  ring

@[simp] theorem pureWZ2Proposition64AffineEquiv_apply
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization) (point : Point3) :
    pureWZ2Proposition64AffineEquiv g slabCenter anchorHeight halfHeight
        normalization hhalfHeight hnormalization point =
      pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
        normalization point := by
  rw [pureWZ2Proposition64AffineEquiv, AffineEquiv.ofLinearEquiv_apply]
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2Proposition64Linear, pureWZ2Proposition64Map, point3] <;> ring

@[simp] theorem pureWZ2Proposition64TranslatedAffineEquiv_apply
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization) (point : Point3) :
    pureWZ2Proposition64TranslatedAffineEquiv g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight hnormalization point =
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation point := by
  simp [pureWZ2Proposition64TranslatedAffineEquiv,
    AffineEquiv.trans_apply, pureWZ2Proposition64TranslatedMap, add_comm]

/-- Exact Jacobian of the Proposition 6.4 affine normalization. -/
theorem pureWZ2Proposition64AffineEquiv_volume_image_eq
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    {halfHeight normalization : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (source : Set Point3) :
    MeasureTheory.volume
        (pureWZ2Proposition64AffineEquiv g slabCenter anchorHeight
          halfHeight normalization hhalfHeight hnormalization '' source) =
      ENNReal.ofReal (1 / (normalization * halfHeight)) *
        MeasureTheory.volume source := by
  rw [wz2PaperAffineEquiv_volume_image_eq]
  rw [show LinearMap.det
      ((pureWZ2Proposition64AffineEquiv g slabCenter anchorHeight
        halfHeight normalization hhalfHeight hnormalization).linear :
          Point3 →ₗ[ℝ] Point3) =
      1 / (normalization * halfHeight) by
        exact pureWZ2Proposition64Linear_det
          (g anchorHeight) halfHeight normalization]
  rw [abs_of_pos (by positivity : 0 < 1 / (normalization * halfHeight))]

/-- Pointwise Jacobian formula for the coordinate presentation used by the
normalization and tube-transport modules. -/
theorem pureWZ2Proposition64Map_volume_image_eq
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    {halfHeight normalization : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (source : Set Point3) :
    MeasureTheory.volume
        (pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
          normalization '' source) =
      ENNReal.ofReal (1 / (normalization * halfHeight)) *
        MeasureTheory.volume source := by
  rw [← pureWZ2Proposition64AffineEquiv_volume_image_eq g slabCenter
    anchorHeight hhalfHeight hnormalization source]
  congr 1
  ext point
  simp only [Set.mem_image]
  constructor
  · rintro ⟨sourcePoint, hsourcePoint, rfl⟩
    exact ⟨sourcePoint, hsourcePoint,
      pureWZ2Proposition64AffineEquiv_apply g slabCenter anchorHeight
        halfHeight normalization hhalfHeight hnormalization sourcePoint⟩
  · rintro ⟨sourcePoint, hsourcePoint, rfl⟩
    exact ⟨sourcePoint, hsourcePoint,
      (pureWZ2Proposition64AffineEquiv_apply g slabCenter anchorHeight
        halfHeight normalization hhalfHeight hnormalization sourcePoint).symm⟩

/-- The fixed translation in Proposition 6.4 does not alter the exact
Jacobian factor. -/
theorem pureWZ2Proposition64TranslatedMap_volume_image_eq
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    {halfHeight normalization : ℝ}
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (source : Set Point3) :
    MeasureTheory.volume
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation '' source) =
      ENNReal.ofReal (1 / (normalization * halfHeight)) *
        MeasureTheory.volume source := by
  let equivalence := pureWZ2Proposition64TranslatedAffineEquiv g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight hnormalization
  have hmap :
      (equivalence : Point3 → Point3) =
        pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation := by
    funext point
    exact pureWZ2Proposition64TranslatedAffineEquiv_apply g slabCenter
      anchorHeight halfHeight normalization translation hhalfHeight
      hnormalization point
  rw [← hmap, wz2PaperAffineEquiv_volume_image_eq]
  rw [show LinearMap.det (equivalence.linear : Point3 →ₗ[ℝ] Point3) =
      1 / (normalization * halfHeight) by
        dsimp only [equivalence,
          pureWZ2Proposition64TranslatedAffineEquiv]
        exact pureWZ2Proposition64Linear_det
          (g anchorHeight) halfHeight normalization]
  rw [abs_of_pos (by positivity : 0 < 1 / (normalization * halfHeight))]

/-- Exact preimage-volume formula for the translated Proposition 6.4 map.
This is the measure input for transporting Convex-Wolff envelopes. -/
theorem pureWZ2Proposition64TranslatedMap_volume_preimage_eq
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    {halfHeight normalization : ℝ}
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (target : Set Point3) :
    MeasureTheory.volume
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation ⁻¹' target) =
      ENNReal.ofReal (normalization * halfHeight) *
        MeasureTheory.volume target := by
  let equivalence := pureWZ2Proposition64TranslatedAffineEquiv g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight hnormalization
  have hmap :
      (equivalence : Point3 → Point3) =
        pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation := by
    funext point
    exact pureWZ2Proposition64TranslatedAffineEquiv_apply g slabCenter
      anchorHeight halfHeight normalization translation hhalfHeight
      hnormalization point
  rw [← hmap]
  have hpreimage :
      equivalence ⁻¹' target = equivalence.symm '' target :=
    (Equiv.image_symm_eq_preimage equivalence.toEquiv target).symm
  rw [hpreimage]
  rw [wz2PaperAffineEquiv_volume_image_eq]
  have hdet :
      LinearMap.det (equivalence.linear : Point3 →ₗ[ℝ] Point3) =
        1 / (normalization * halfHeight) := by
    dsimp only [equivalence, pureWZ2Proposition64TranslatedAffineEquiv]
    exact pureWZ2Proposition64Linear_det
      (g anchorHeight) halfHeight normalization
  rw [show LinearMap.det (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3) =
      normalization * halfHeight by
        rw [show equivalence.symm.linear = equivalence.linear.symm by rfl,
          LinearEquiv.det_coe_symm, hdet]
        field_simp [hhalfHeight.ne', hnormalization.ne']]
  rw [abs_of_pos (mul_pos hnormalization hhalfHeight)]

/-- The slope transformed together with the Proposition 6.4 configuration. -/
def pureWZ2Proposition64Slope
    (g : SlopeFunction)
    (slabCenter anchorHeight halfHeight normalization : ℝ) :
    SlopeFunction where
  toFun t :=
    (g (slabCenter + halfHeight * t) - g anchorHeight) / normalization
  contDiff := by
    have hAffine : ContDiff ℝ 2
        (fun t : ℝ => slabCenter + halfHeight * t) :=
      contDiff_const.add (contDiff_const.mul contDiff_id)
    exact ((g.contDiff.comp hAffine).sub contDiff_const).div_const normalization

@[simp] theorem pureWZ2Proposition64Map_apply_zero
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (point : Point3) :
    pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
        normalization point 0 =
      (point 0 + g anchorHeight * point 1) / normalization := by
  simp [pureWZ2Proposition64Map, point3]

@[simp] theorem pureWZ2Proposition64Map_apply_one
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (point : Point3) :
    pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
        normalization point 1 =
      point 1 := by
  simp [pureWZ2Proposition64Map, point3]

@[simp] theorem pureWZ2Proposition64Map_apply_two
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (point : Point3) :
    pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
        normalization point 2 =
      (point 2 - slabCenter) / halfHeight := by
  simp [pureWZ2Proposition64Map, point3]

@[simp] theorem pureWZ2Proposition64Slope_apply
    (g : SlopeFunction)
    (slabCenter anchorHeight halfHeight normalization t : ℝ) :
    pureWZ2Proposition64Slope g slabCenter anchorHeight halfHeight
        normalization t =
      (g (slabCenter + halfHeight * t) - g anchorHeight) /
        normalization := rfl

/-- The short source slab is sent to the standard height interval. -/
theorem pureWZ2Proposition64Map_height_mem
    (g : ℝ → ℝ) {slabCenter halfHeight : ℝ}
    (anchorHeight normalization : ℝ)
    (hhalfHeight : 0 < halfHeight) {point : Point3}
    (hpoint : point 2 ∈
      Set.Icc (slabCenter - halfHeight) (slabCenter + halfHeight)) :
    pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
        normalization point 2 ∈
      Set.Icc (-1 : ℝ) 1 := by
  rw [pureWZ2Proposition64Map_apply_two]
  constructor
  · apply (le_div_iff₀ hhalfHeight).2
    linarith [hpoint.1]
  · apply (div_le_iff₀ hhalfHeight).2
    linarith [hpoint.2]

/-- The exact map sends the selected short slab of the standard source box
back into the standard box once the fixed normalization constant is at least
`9`.  This is the explicit version of “increase `C_*` by an absolute factor”
in the proof of Proposition 6.4. -/
theorem pureWZ2Proposition64Map_mem_axisBox
    (g : ℝ → ℝ) {slabCenter anchorHeight halfHeight normalization : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    {point : Point3}
    (hpointBox : point ∈ Kakeya.Streamlined.axisBox 2 2 2)
    (hpointSlab : point 2 ∈
      Set.Icc (slabCenter - halfHeight) (slabCenter + halfHeight)) :
    pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
        normalization point ∈
      Kakeya.Streamlined.axisBox 2 2 2 := by
  have hx : |point 0| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpointBox.1
  have hy : |point 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpointBox.2.1
  have hnormalizationPos : 0 < normalization := by linarith
  have hfirst :
      |(point 0 + g anchorHeight * point 1) / normalization| ≤ 1 := by
    rw [abs_div, abs_of_pos hnormalizationPos]
    apply (div_le_one hnormalizationPos).2
    calc
      |point 0 + g anchorHeight * point 1| ≤
          |point 0| + |g anchorHeight| * |point 1| := by
        simpa [abs_mul] using
          abs_add_le (point 0) (g anchorHeight * point 1)
      _ ≤ 1 + 8 * 1 := by gcongr
      _ ≤ normalization := by norm_num at hnormalization ⊢; exact hnormalization
  have hheight := pureWZ2Proposition64Map_height_mem g anchorHeight
    normalization hhalfHeight hpointSlab
  have hthird :
      |pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
          normalization point 2| ≤ 1 := abs_le.mpr hheight
  simpa [Kakeya.Streamlined.axisBox,
    pureWZ2Proposition64Map_apply_zero,
    pureWZ2Proposition64Map_apply_one] using
      And.intro hfirst (And.intro hy hthird)

/-- Exact projection covariance for the map in `wz2_64.tex`, equation
`x' + y' g_tilde(t) = C⁻¹ (x + y g(z))`. -/
theorem pureWZ2Proposition64Map_projection
    (g : SlopeFunction)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (point : Point3)
    (hheight : point 2 = slabCenter + halfHeight *
      (pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
        normalization point 2)) :
    inner ℝ (pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
        normalization point)
        (globalGrainDirection
          (pureWZ2Proposition64Slope g slabCenter anchorHeight halfHeight
            normalization
            (pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
              normalization point 2))) =
      (inner ℝ point (globalGrainDirection (g (point 2)))) /
        normalization := by
  simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ,
    pureWZ2Proposition64Map, pureWZ2Proposition64Slope, point3]
  have hheight' : slabCenter +
      halfHeight * ((point 2 - slabCenter) / halfHeight) =
      point 2 := by
    simpa [pureWZ2Proposition64Map_apply_two] using hheight.symm
  have hg : g (slabCenter +
      halfHeight * ((point 2 - slabCenter) / halfHeight)) =
      g (point 2) := congrArg g hheight'
  rw [hg]
  ring

/-- With nonzero slab height, the source height is exactly recovered from the
normalized height. -/
theorem pureWZ2Proposition64Map_height_inverse
    (g : ℝ → ℝ) {slabCenter halfHeight normalization : ℝ}
    (anchorHeight : ℝ)
    (hhalfHeight : halfHeight ≠ 0) (point : Point3) :
    point 2 = slabCenter + halfHeight *
      (pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
        normalization point 2) := by
  rw [pureWZ2Proposition64Map_apply_two]
  field_simp [hhalfHeight]
  ring

/-- Pointwise form of Proposition 6.4's displayed projection identity. -/
theorem pureWZ2Proposition64Map_projection_identity
    (g : SlopeFunction)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (hhalfHeight : halfHeight ≠ 0) (point : Point3) :
    inner ℝ (pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
        normalization point)
        (globalGrainDirection
          (pureWZ2Proposition64Slope g slabCenter anchorHeight halfHeight
            normalization
            (pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
              normalization point 2))) =
      (inner ℝ point (globalGrainDirection (g (point 2)))) /
        normalization :=
  pureWZ2Proposition64Map_projection g slabCenter anchorHeight halfHeight
    normalization point
    (pureWZ2Proposition64Map_height_inverse
      g anchorHeight hhalfHeight point)

/-- Exact projection covariance including the fixed horizontal translation.
The translation contributes only one constant scalar shift on each slice. -/
theorem pureWZ2Proposition64TranslatedMap_projection_identity
    (g : SlopeFunction)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation point : Point3)
    (htranslationHeight : translation 2 = 0)
    (hhalfHeight : halfHeight ≠ 0) :
    inner ℝ
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation point)
        (globalGrainDirection
          (pureWZ2Proposition64Slope g slabCenter anchorHeight halfHeight
            normalization
            (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
              halfHeight normalization translation point 2))) =
      (inner ℝ point (globalGrainDirection (g (point 2)))) / normalization +
        inner ℝ translation
          (globalGrainDirection
            (pureWZ2Proposition64Slope g slabCenter anchorHeight halfHeight
              normalization
              (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
                halfHeight normalization translation point 2))) := by
  have hheight :
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point 2 =
        pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
          normalization point 2 := by
    simp [pureWZ2Proposition64TranslatedMap, htranslationHeight]
  rw [hheight]
  rw [pureWZ2Proposition64TranslatedMap, inner_add_left]
  rw [pureWZ2Proposition64Map_projection_identity g slabCenter anchorHeight
    halfHeight normalization hhalfHeight point]

end Kakeya.Assouad

end
