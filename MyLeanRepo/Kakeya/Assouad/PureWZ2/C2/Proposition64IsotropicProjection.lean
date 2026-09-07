import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64IsotropicPlaneMap

/-!
# Slice projections under the final Proposition 6.4 similarity

The final isotropic similarity changes the height parameter.  This leaf
records the exact set identity used to transport the global AD estimate.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- Exact slice-projection covariance under the final positive isotropic
similarity. A target height `z` pulls back to `center 2 + z / scale`; at that
height the scalar projection is a positive dilation followed by a translation. -/
theorem pureWZ2Proposition64IsotropicMap_slice_projection
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (direction : Point3) (source : Set Point3) (z : ℝ) :
    scalarProjection direction
        (horizontalSlice
          (pureWZ2Proposition64IsotropicMap center scale '' source) z) =
      (fun value : ℝ =>
        scale * value - scale * inner ℝ center direction) ''
        scalarProjection direction
          (horizontalSlice source (center 2 + z / scale)) := by
  ext value
  constructor
  · rintro ⟨targetPoint,
      ⟨⟨sourcePoint, hsourcePoint, rfl⟩, htargetHeight⟩, rfl⟩
    have hsourceHeight : sourcePoint 2 = center 2 + z / scale := by
      have hheight : scale * (sourcePoint 2 - center 2) = z := by
        simpa [pureWZ2Proposition64IsotropicMap, smul_eq_mul] using
          htargetHeight
      field_simp [hscale.ne']
      linarith
    refine ⟨inner ℝ sourcePoint direction,
      ⟨sourcePoint, ⟨hsourcePoint, hsourceHeight⟩, rfl⟩, ?_⟩
    simp only [pureWZ2Proposition64IsotropicMap, inner_smul_left,
      inner_sub_left, starRingEnd_apply, star_trivial]
    ring
  · rintro ⟨sourceValue,
      ⟨sourcePoint, ⟨hsourcePoint, hsourceHeight⟩, rfl⟩, rfl⟩
    refine ⟨pureWZ2Proposition64IsotropicMap center scale sourcePoint,
      ⟨⟨sourcePoint, hsourcePoint, rfl⟩, ?_⟩, ?_⟩
    · simp only [pureWZ2Proposition64IsotropicMap, PiLp.smul_apply,
        PiLp.sub_apply, smul_eq_mul]
      rw [hsourceHeight]
      field_simp [hscale.ne']
      ring
    · simp only [pureWZ2Proposition64IsotropicMap, inner_smul_left,
        inner_sub_left, starRingEnd_apply, star_trivial]
      ring

/-- The exact translated image of the selected short slab stays in the
standard height window.  The horizontal common-window translation has zero
third coordinate, so this is exactly the height normalization built into
`Phi`. -/
theorem pureWZ2Proposition64TranslatedMap_image_height_mem
    (g : ℝ → ℝ) (slabCenter anchorHeight normalization : ℝ)
    {halfHeight : ℝ} (hhalfHeight : 0 < halfHeight)
    (translation : Point3) (htranslationHeight : translation 2 = 0)
    (source : Set Point3)
    (hsourceHeight : ∀ point ∈ source,
      point 2 ∈ Set.Icc
        (slabCenter - halfHeight) (slabCenter + halfHeight)) :
    ∀ point ∈
        pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation '' source,
      point 2 ∈ Set.Icc (-1 : ℝ) 1 := by
  rintro point ⟨sourcePoint, hsourcePoint, rfl⟩
  rw [pureWZ2Proposition64TranslatedMap_apply_two, htranslationHeight, add_zero]
  convert
    pureWZ2Proposition64Map_height_mem g anchorHeight normalization hhalfHeight
      (hsourceHeight sourcePoint hsourcePoint) using 1 <;>
    simp [pureWZ2Proposition64Map, point3]

/-- A horizontal common-window translation preserves the exact normalized
global AD estimate. -/
theorem PureWZ2Proposition64NormalizedData.translated_global_ad
    {sourceDelta sigma rawLoss extensionConstant : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    {raw : PureWZ2RawC2GlobalGrainData
      sourceShading sigma C rawLoss extensionConstant}
    {slabCenter anchorHeight halfHeight normalization : ℝ}
    (normalized : PureWZ2Proposition64NormalizedData
      raw slabCenter anchorHeight halfHeight normalization)
    (translation : Point3) (htranslationHeight : translation 2 = 0) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (normalized.slope z))
          (horizontalSlice
            (pureWZ2Proposition64TranslatedMap raw.slope slabCenter
              anchorHeight halfHeight normalization translation ''
                sourceShading.union) z))
        (sourceDelta / normalization) (1 - sigma) (6 * C) := by
  intro z hz
  rw [pureWZ2Proposition64TranslatedMap_slice_projection raw.slope
    slabCenter anchorHeight halfHeight normalization translation
    (globalGrainDirection (normalized.slope z)) sourceShading.union z
    htranslationHeight]
  exact (normalized.global_ad z hz).translate _

/-- Transport a global paper AD estimate through the final isotropic
similarity.  Only occupied target heights need the inverse-height formula; at
an empty target slice the conclusion follows by monotonicity from any source
slice. -/
theorem pureWZ2Proposition64_isotropic_global_ad_of_nonempty_slice
    {sourceDelta sigma alpha scale : ℝ} {C : ENNReal}
    (sourceSlope finalSlope : SlopeFunction)
    (source : Set Point3) (center : Point3)
    (hscale : 0 < scale)
    (hsourceHeightWindow : ∀ point ∈ source,
      point 2 ∈ Set.Icc (-1 : ℝ) 1)
    (hsourceAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (sourceSlope z))
          (horizontalSlice source z)) sourceDelta alpha C)
    (hfinalSlope : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice
        (pureWZ2Proposition64IsotropicMap center scale '' source) z ≠ ∅ →
      finalSlope z = sourceSlope (center 2 + z / scale)) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice
        (pureWZ2Proposition64IsotropicMap center scale '' source) z ≠ ∅ →
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (finalSlope z))
          (horizontalSlice
            (pureWZ2Proposition64IsotropicMap center scale '' source) z))
        (scale * sourceDelta) alpha C := by
  intro z hz hslice
  have hsourceHeight : center 2 + z / scale ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨targetPoint, htargetPoint⟩
    rcases htargetPoint with
      ⟨⟨sourcePoint, hsourcePoint, hpointEq⟩, htargetHeight⟩
    have hheight : sourcePoint 2 = center 2 + z / scale := by
      rw [← hpointEq] at htargetHeight
      have hscaled : scale * (sourcePoint 2 - center 2) = z := by
        simpa [pureWZ2Proposition64IsotropicMap, smul_eq_mul] using
          htargetHeight
      field_simp [hscale.ne']
      linarith
    rw [← hheight]
    exact hsourceHeightWindow sourcePoint hsourcePoint
  have hsource := hsourceAD (center 2 + z / scale) hsourceHeight
  have hscaled := hsource.image_mul hscale
  have htranslated := hscaled.translate
    (-scale * inner ℝ center
      (globalGrainDirection (sourceSlope (center 2 + z / scale))))
  have hslope := hfinalSlope z hz hslice
  rw [hslope]
  rw [pureWZ2Proposition64IsotropicMap_slice_projection center hscale]
  simpa only [Set.image_image, Function.comp_apply, sub_eq_add_neg, neg_mul] using
    htranslated

/-- The isotropic global AD conclusion at every target height.  Occupied
slices use the exact covariance theorem above; an empty slice inherits the
same AD parameters by subset monotonicity. -/
theorem pureWZ2Proposition64_isotropic_global_ad
    {sourceDelta sigma alpha scale : ℝ} {C : ENNReal}
    (sourceSlope finalSlope : SlopeFunction)
    (source : Set Point3) (center : Point3)
    (hscale : 0 < scale)
    (hsourceHeightWindow : ∀ point ∈ source,
      point 2 ∈ Set.Icc (-1 : ℝ) 1)
    (hsourceAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (sourceSlope z))
          (horizontalSlice source z)) sourceDelta alpha C)
    (hfinalSlope : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice
        (pureWZ2Proposition64IsotropicMap center scale '' source) z ≠ ∅ →
      finalSlope z = sourceSlope (center 2 + z / scale)) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (finalSlope z))
          (horizontalSlice
            (pureWZ2Proposition64IsotropicMap center scale '' source) z))
        (scale * sourceDelta) alpha C := by
  intro z hz
  by_cases hslice : horizontalSlice
      (pureWZ2Proposition64IsotropicMap center scale '' source) z = ∅
  · have hseed := ((hsourceAD 0 (by norm_num)).image_mul hscale).translate
        (-scale * inner ℝ center
          (globalGrainDirection (sourceSlope 0)))
    apply hseed.mono
    intro value hvalue
    rcases hvalue with ⟨point, hpoint, _⟩
    rw [hslice] at hpoint
    exact hpoint.elim
  · exact pureWZ2Proposition64_isotropic_global_ad_of_nonempty_slice
      (sigma := sigma) sourceSlope finalSlope source center hscale hsourceHeightWindow
        hsourceAD hfinalSlope z hz hslice

end Kakeya.Assouad

end
