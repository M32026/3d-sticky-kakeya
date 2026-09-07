import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64ExactNormalTransport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64CommonWindow
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64TubeTransport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.GrainRestriction

/-!
# Local plane field on the exact Proposition 6.4 image

This is the exact-image part of Item 2 in Proposition 6.4.  The plane field
is transported by the inverse transpose of the same affine map used for the
tubes.  The following isotropic normalization and cubical thickening remain
separate Lemma-3.5 steps.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- Exact image shading on the one-to-one affine image family. -/
def pureWZ2Proposition64ExactImageShading
    {sourceDelta targetDelta : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hradius : 180 * sourceDelta ≤ 6 * targetDelta)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (himageBox : ∀ index, ∀ point ∈ sourceShading.carrier index,
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point ∈
        Kakeya.Streamlined.axisBox 2 2 2) :
    WZ1PaperTubeShading
      (pureWZ2Proposition64ImageFamily targetDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight
        (by linarith : 0 < normalization)
        sourceFamily) where
  carrier index :=
    pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
      normalization translation '' sourceShading.carrier index
  measurable_carrier index := by
    let affine := pureWZ2Proposition64TranslatedAffineEquiv g slabCenter
      anchorHeight halfHeight normalization translation hhalfHeight
      (by linarith : 0 < normalization)
    have heq :
        pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
              normalization translation '' sourceShading.carrier index =
          affine '' sourceShading.carrier index := by
      ext point
      simp only [Set.mem_image]
      constructor <;> rintro ⟨source, hsource, rfl⟩
      · exact ⟨source, hsource,
          pureWZ2Proposition64TranslatedAffineEquiv_apply g slabCenter
            anchorHeight halfHeight normalization translation hhalfHeight
            (by linarith : 0 < normalization) source⟩
      · exact ⟨source, hsource,
          (pureWZ2Proposition64TranslatedAffineEquiv_apply g slabCenter
            anchorHeight halfHeight normalization translation hhalfHeight
            (by linarith : 0 < normalization) source).symm⟩
    rw [heq]
    exact affine.toHomeomorphOfFiniteDimensional.toMeasurableEquiv
      |>.measurableSet_image.mpr (sourceShading.measurable_carrier index)
  subset_body index := by
    rintro imagePoint ⟨sourcePoint, hsourcePoint, rfl⟩
    exact pureWZ2Proposition64TranslatedMap_mem_imageTube
      hsourceDelta
      g slabCenter anchorHeight halfHeight normalization translation
      hhalfHeight (by linarith : 1 ≤ normalization) hanchorSlope hradius
      (sourceFamily.tube index) (hsourceLine index)
      (sourceShading.subset_body index hsourcePoint)
      (himageBox index sourcePoint hsourcePoint)

/-- The union of the one-to-one exact-image shading is the exact image of
the source union. -/
theorem pureWZ2Proposition64ExactImageShading_union
    {sourceDelta targetDelta : ℝ}
    {g : ℝ → ℝ} {slabCenter anchorHeight halfHeight normalization : ℝ}
    {translation : Point3}
    {hhalfHeight : 0 < halfHeight}
    {hnormalization : 9 ≤ normalization}
    {hsourceDelta : 0 < sourceDelta}
    {hanchorSlope : |g anchorHeight| ≤ 8}
    {hradius : 180 * sourceDelta ≤ 6 * targetDelta}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {hsourceLine : WZ1PaperIsLineClass sourceFamily}
    {himageBox : ∀ index, ∀ point ∈ sourceShading.carrier index,
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point ∈
        Kakeya.Streamlined.axisBox 2 2 2} :
    (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
      anchorHeight halfHeight normalization translation hhalfHeight
      hnormalization hanchorSlope hradius sourceFamily sourceShading
      hsourceLine himageBox).union =
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation '' sourceShading.union := by
  ext point
  constructor
  · rintro ⟨index, sourcePoint, hsourcePoint, rfl⟩
    exact ⟨sourcePoint, ⟨index, hsourcePoint⟩, rfl⟩
  · rintro ⟨sourcePoint, ⟨index, hsourcePoint⟩, rfl⟩
    exact ⟨index, sourcePoint, hsourcePoint, rfl⟩

/-- Exact union-volume scaling for the one-to-one translated `Phi` image. -/
theorem pureWZ2Proposition64ExactImageShading_union_volume
    {sourceDelta targetDelta : ℝ}
    {g : ℝ → ℝ} {slabCenter anchorHeight halfHeight normalization : ℝ}
    {translation : Point3}
    {hhalfHeight : 0 < halfHeight}
    {hnormalization : 9 ≤ normalization}
    {hsourceDelta : 0 < sourceDelta}
    {hanchorSlope : |g anchorHeight| ≤ 8}
    {hradius : 180 * sourceDelta ≤ 6 * targetDelta}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {hsourceLine : WZ1PaperIsLineClass sourceFamily}
    {himageBox : ∀ index, ∀ point ∈ sourceShading.carrier index,
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point ∈
        Kakeya.Streamlined.axisBox 2 2 2} :
    MeasureTheory.volume
        (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
          anchorHeight halfHeight normalization translation hhalfHeight
          hnormalization hanchorSlope hradius sourceFamily sourceShading
          hsourceLine himageBox).union =
      ENNReal.ofReal (1 / (normalization * halfHeight)) *
        MeasureTheory.volume sourceShading.union := by
  rw [pureWZ2Proposition64ExactImageShading_union]
  exact pureWZ2Proposition64TranslatedMap_volume_image_eq g slabCenter
    anchorHeight translation hhalfHeight (by linarith) sourceShading.union

/-- Each exact-image carrier is literally the translated `Phi` image of the
corresponding source carrier. -/
theorem pureWZ2Proposition64ExactImageShading_carrier_provenance
    {sourceDelta targetDelta : ℝ}
    {g : ℝ → ℝ} {slabCenter anchorHeight halfHeight normalization : ℝ}
    {translation : Point3}
    {hhalfHeight : 0 < halfHeight}
    {hnormalization : 9 ≤ normalization}
    {hsourceDelta : 0 < sourceDelta}
    {hanchorSlope : |g anchorHeight| ≤ 8}
    {hradius : 180 * sourceDelta ≤ 6 * targetDelta}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {hsourceLine : WZ1PaperIsLineClass sourceFamily}
    {himageBox : ∀ index, ∀ point ∈ sourceShading.carrier index,
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point ∈
        Kakeya.Streamlined.axisBox 2 2 2} :
    ∀ target,
      (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization hanchorSlope hradius sourceFamily sourceShading
        hsourceLine himageBox).carrier target ⊆
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation '' sourceShading.carrier target := by
  intro target point hpoint
  exact hpoint

/-- Exact indexed shaded-mass scaling under the Proposition 6.4 map. -/
theorem pureWZ2Proposition64ExactImageShading_mass
    {sourceDelta targetDelta : ℝ}
    {g : ℝ → ℝ} {slabCenter anchorHeight : ℝ}
    {halfHeight normalization : ℝ}
    {translation : Point3}
    {hhalfHeight : 0 < halfHeight}
    {hnormalization : 9 ≤ normalization}
    {hsourceDelta : 0 < sourceDelta}
    {hanchorSlope : |g anchorHeight| ≤ 8}
    {hradius : 180 * sourceDelta ≤ 6 * targetDelta}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {hsourceLine : WZ1PaperIsLineClass sourceFamily}
    {himageBox : ∀ index, ∀ point ∈ sourceShading.carrier index,
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point ∈
        Kakeya.Streamlined.axisBox 2 2 2} :
    (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
      anchorHeight halfHeight normalization translation hhalfHeight
      hnormalization hanchorSlope hradius sourceFamily sourceShading
      hsourceLine himageBox).mass =
      ENNReal.ofReal (1 / (normalization * halfHeight)) *
        sourceShading.mass := by
  change (∑ index,
      MeasureTheory.volume
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation ''
          sourceShading.carrier index)) = _
  simp only [Kakeya.Streamlined.Shading.mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  exact pureWZ2Proposition64TranslatedMap_volume_image_eq g slabCenter
    anchorHeight translation hhalfHeight (by linarith) _

/-- Every point of the exact image shading has its canonical source
preimage in the original shaded union. -/
def pureWZ2Proposition64ExactSourcePoint
    {sourceDelta targetDelta : ℝ}
    {g : ℝ → ℝ} {slabCenter anchorHeight halfHeight normalization : ℝ}
    {translation : Point3}
    {hhalfHeight : 0 < halfHeight}
    {hnormalization : 9 ≤ normalization}
    {hsourceDelta : 0 < sourceDelta}
    {hanchorSlope : |g anchorHeight| ≤ 8}
    {hradius : 180 * sourceDelta ≤ 6 * targetDelta}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {hsourceLine : WZ1PaperIsLineClass sourceFamily}
    {himageBox : ∀ index, ∀ point ∈ sourceShading.carrier index,
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point ∈
        Kakeya.Streamlined.axisBox 2 2 2}
    (target : {point : Point3 // point ∈
      (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization hanchorSlope hradius sourceFamily sourceShading
        hsourceLine himageBox).union}) :
    {point : Point3 // point ∈ sourceShading.union} := by
  let inversePoint := pureWZ2Proposition64TranslatedInverse g slabCenter
    anchorHeight halfHeight normalization translation target
  refine ⟨inversePoint, ?_⟩
  rcases target.property with ⟨index, sourcePoint, hsourcePoint, heq⟩
  have hinverse : inversePoint = sourcePoint := by
    dsimp only [inversePoint]
    rw [← heq]
    exact pureWZ2Proposition64TranslatedInverse_map g slabCenter anchorHeight
      translation sourcePoint hhalfHeight.ne'
        (by linarith : normalization ≠ 0)
  rw [hinverse]
  exact ⟨index, hsourcePoint⟩

@[simp] theorem pureWZ2Proposition64Map_exactSourcePoint
    {sourceDelta targetDelta : ℝ}
    {g : ℝ → ℝ} {slabCenter anchorHeight halfHeight normalization : ℝ}
    {translation : Point3}
    {hhalfHeight : 0 < halfHeight}
    {hnormalization : 9 ≤ normalization}
    {hsourceDelta : 0 < sourceDelta}
    {hanchorSlope : |g anchorHeight| ≤ 8}
    {hradius : 180 * sourceDelta ≤ 6 * targetDelta}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {hsourceLine : WZ1PaperIsLineClass sourceFamily}
    {himageBox : ∀ index, ∀ point ∈ sourceShading.carrier index,
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point ∈
        Kakeya.Streamlined.axisBox 2 2 2}
    (target : {point : Point3 // point ∈
      (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization hanchorSlope hradius sourceFamily sourceShading
        hsourceLine himageBox).union}) :
    pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation
        (pureWZ2Proposition64ExactSourcePoint target) = target := by
  exact pureWZ2Proposition64TranslatedMap_inverse g slabCenter anchorHeight
    translation target hhalfHeight.ne'
      (by linarith : normalization ≠ 0)

/-- The canonical preimage of a point in one exact target carrier lies in the
corresponding source carrier. -/
theorem pureWZ2Proposition64ExactSourcePoint_mem_carrier
    {sourceDelta targetDelta : ℝ}
    {g : ℝ → ℝ} {slabCenter anchorHeight halfHeight normalization : ℝ}
    {translation : Point3}
    {hhalfHeight : 0 < halfHeight}
    {hnormalization : 9 ≤ normalization}
    {hsourceDelta : 0 < sourceDelta}
    {hanchorSlope : |g anchorHeight| ≤ 8}
    {hradius : 180 * sourceDelta ≤ 6 * targetDelta}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {hsourceLine : WZ1PaperIsLineClass sourceFamily}
    {himageBox : ∀ index, ∀ point ∈ sourceShading.carrier index,
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point ∈
        Kakeya.Streamlined.axisBox 2 2 2}
    (index) (point : Point3)
    (hpoint : point ∈
      (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization hanchorSlope hradius sourceFamily sourceShading
        hsourceLine himageBox).carrier index) :
    (pureWZ2Proposition64ExactSourcePoint
      (g := g) (slabCenter := slabCenter) (anchorHeight := anchorHeight)
      (halfHeight := halfHeight) (normalization := normalization)
      (translation := translation) (hhalfHeight := hhalfHeight)
      (hnormalization := hnormalization) (hsourceDelta := hsourceDelta)
      (hanchorSlope := hanchorSlope) (hradius := hradius)
      (sourceFamily := sourceFamily) (sourceShading := sourceShading)
      (hsourceLine := hsourceLine) (himageBox := himageBox)
      ⟨point, ⟨index, hpoint⟩⟩ : Point3) ∈ sourceShading.carrier index := by
  rcases hpoint with ⟨sourcePoint, hsourcePoint, heq⟩
  change pureWZ2Proposition64TranslatedInverse g slabCenter anchorHeight
      halfHeight normalization translation point ∈ sourceShading.carrier index
  rw [← heq, pureWZ2Proposition64TranslatedInverse_map g slabCenter
    anchorHeight translation sourcePoint hhalfHeight.ne'
      (by linarith : normalization ≠ 0)]
  exact hsourcePoint

/-- The exact-image inverse-transpose plane field. -/
def pureWZ2Proposition64ExactPlaneMap
    {sourceDelta targetDelta sigma : ℝ}
    {g : ℝ → ℝ} {slabCenter anchorHeight halfHeight normalization : ℝ}
    {translation : Point3}
    {hhalfHeight : 0 < halfHeight}
    {hnormalization : 9 ≤ normalization}
    {hsourceDelta : 0 < sourceDelta}
    {hanchorSlope : |g anchorHeight| ≤ 8}
    {hradius : 180 * sourceDelta ≤ 6 * targetDelta}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {hsourceLine : WZ1PaperIsLineClass sourceFamily}
    {himageBox : ∀ index, ∀ point ∈ sourceShading.carrier index,
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point ∈
        Kakeya.Streamlined.axisBox 2 2 2}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (target : {point : Point3 // point ∈
      (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization hanchorSlope hradius sourceFamily sourceShading
        hsourceLine himageBox).union}) : Point3 :=
  pureWZ2Proposition64TransportedNormal (g anchorHeight) halfHeight
    normalization
    (sourceLocal.planeMap
      (@pureWZ2Proposition64ExactSourcePoint sourceDelta targetDelta g
        slabCenter anchorHeight halfHeight normalization translation
        hhalfHeight hnormalization hsourceDelta hanchorSlope hradius
        sourceFamily sourceShading hsourceLine himageBox target))

/-- Quantitative exact-image plane-map package before the final isotropic
normalization in Lemma 3.5. -/
structure PureWZ2Proposition64ExactPlaneMapData
    {sourceDelta targetDelta sigma : ℝ}
    {g : ℝ → ℝ} {slabCenter anchorHeight halfHeight normalization : ℝ}
    {translation : Point3}
    {hhalfHeight : 0 < halfHeight}
    {hnormalization : 9 ≤ normalization}
    {hsourceDelta : 0 < sourceDelta}
    {hanchorSlope : |g anchorHeight| ≤ 8}
    {hradius : 180 * sourceDelta ≤ 6 * targetDelta}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {hsourceLine : WZ1PaperIsLineClass sourceFamily}
    {himageBox : ∀ index, ∀ point ∈ sourceShading.carrier index,
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point ∈
        Kakeya.Streamlined.axisBox 2 2 2}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C) where
  K : NNReal
  K_le : (K : ℝ) ≤ 288 * normalization ^ 2
  planeMap : {point : Point3 // point ∈
    (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
      anchorHeight halfHeight normalization translation hhalfHeight
      hnormalization hanchorSlope hradius sourceFamily sourceShading
      hsourceLine himageBox).union} → Point3
  planeMap_eq : planeMap = pureWZ2Proposition64ExactPlaneMap sourceLocal
  planeMap_lipschitz : LipschitzWith K planeMap
  planeMap_unit : ∀ point, ‖planeMap point‖ = 1
  planeMap_incidence_source :
    ∀ index point,
      ∀ hpoint : point ∈
          (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
            anchorHeight halfHeight normalization translation hhalfHeight
            hnormalization hanchorSlope hradius sourceFamily sourceShading
            hsourceLine himageBox).carrier index,
        |inner ℝ
            ((pureWZ2Proposition64ImageFamily targetDelta g slabCenter
              anchorHeight halfHeight normalization translation hhalfHeight
              (by linarith) sourceFamily).tube index).direction
            (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ sourceDelta
  planeMap_incidence :
    ∀ index point,
      ∀ hpoint : point ∈
          (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
            anchorHeight halfHeight normalization translation hhalfHeight
            hnormalization hanchorSlope hradius sourceFamily sourceShading
            hsourceLine himageBox).carrier index,
        |inner ℝ
            ((pureWZ2Proposition64ImageFamily targetDelta g slabCenter
              anchorHeight halfHeight normalization translation hhalfHeight
              (by linarith) sourceFamily).tube index).direction
            (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ targetDelta
  planeMap_vertical_bound : ∀ point, |planeMap point 2| ≤ 1 / 10

/-- Assemble the exact-image plane field from the local grains already carried
by the selected Proposition 6.4 slab. -/
noncomputable def pureWZ2Proposition64ExactPlaneMapData
    {sourceDelta targetDelta sigma : ℝ}
    {g : ℝ → ℝ} {slabCenter anchorHeight : ℝ}
    {halfHeight normalization : ℝ}
    {translation : Point3}
    {hhalfHeight : 0 < halfHeight}
    {hnormalization : 9 ≤ normalization}
    {hsourceDelta : 0 < sourceDelta}
    {hanchorSlope : |g anchorHeight| ≤ 8}
    {hradius : 180 * sourceDelta ≤ 6 * targetDelta}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {hsourceLine : WZ1PaperIsLineClass sourceFamily}
    {himageBox : ∀ index, ∀ point ∈ sourceShading.carrier index,
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point ∈
        Kakeya.Streamlined.axisBox 2 2 2}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (hsourceVertical : ∀ point, |sourceLocal.planeMap point 2| ≤ 1 / 2)
    (hsourceTarget : sourceDelta ≤ targetDelta)
    (hhalfHeightSmall : halfHeight ≤ 1 / 20) :
    @PureWZ2Proposition64ExactPlaneMapData sourceDelta targetDelta sigma g
      slabCenter anchorHeight halfHeight normalization translation hhalfHeight
      hnormalization hsourceDelta hanchorSlope hradius sourceFamily
      sourceShading hsourceLine himageBox C sourceLocal := by
  let sourcePoint :
      {point : Point3 // point ∈
        (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
          anchorHeight halfHeight normalization translation hhalfHeight
          hnormalization hanchorSlope hradius sourceFamily sourceShading
          hsourceLine himageBox).union} →
        {point : Point3 // point ∈ sourceShading.union} :=
    fun target =>
      @pureWZ2Proposition64ExactSourcePoint sourceDelta targetDelta g
        slabCenter anchorHeight halfHeight normalization translation
        hhalfHeight hnormalization hsourceDelta hanchorSlope hradius
        sourceFamily sourceShading hsourceLine himageBox target
  have hsourcePoint : ∀ first second,
      dist (sourcePoint first) (sourcePoint second) ≤
        3 * normalization * dist first second := by
    intro first second
    change dist
        (pureWZ2Proposition64TranslatedInverse g slabCenter anchorHeight
          halfHeight normalization translation (first : Point3))
        (pureWZ2Proposition64TranslatedInverse g slabCenter anchorHeight
          halfHeight normalization translation (second : Point3)) ≤ _
    simpa only [Subtype.dist_eq] using
      pureWZ2Proposition64TranslatedInverse_dist_le g slabCenter anchorHeight
        halfHeight normalization translation first second
        (by rw [abs_of_pos hhalfHeight]; linarith)
        hanchorSlope (by linarith)
  exact
    { K := ⟨288 * normalization ^ 2,
        mul_nonneg (by norm_num) (sq_nonneg normalization)⟩
      K_le := le_rfl
      planeMap := pureWZ2Proposition64ExactPlaneMap
        (targetDelta := targetDelta) (g := g) (slabCenter := slabCenter)
        (anchorHeight := anchorHeight) (halfHeight := halfHeight)
        (normalization := normalization) (translation := translation)
          (hhalfHeight := hhalfHeight) (hnormalization := hnormalization)
        (hsourceDelta := hsourceDelta) (hanchorSlope := hanchorSlope)
        (hradius := hradius) (sourceFamily := sourceFamily)
        (sourceShading := sourceShading) (hsourceLine := hsourceLine)
        (himageBox := himageBox) sourceLocal
      planeMap_eq := rfl
      planeMap_lipschitz := by
        exact pureWZ2Proposition64TransportedNormal_lipschitz g slabCenter
          anchorHeight halfHeight normalization translation
          (by rw [abs_of_pos hhalfHeight]; linarith)
          hanchorSlope hnormalization sourceLocal.planeMap
          sourceLocal.planeMap_lipschitz sourcePoint hsourcePoint
          sourceLocal.planeMap_unit hsourceVertical
      planeMap_unit := by
        intro point
        exact pureWZ2Proposition64TransportedNormal_unit hanchorSlope
          (by linarith) (sourceLocal.planeMap_unit (sourcePoint point))
          (hsourceVertical (sourcePoint point))
      planeMap_incidence_source := by
        intro index point hpoint
        let targetPoint : {point : Point3 // point ∈
            (pureWZ2Proposition64ExactImageShading hsourceDelta g slabCenter
              anchorHeight halfHeight normalization translation hhalfHeight
              hnormalization hanchorSlope hradius sourceFamily sourceShading
              hsourceLine himageBox).union} :=
          ⟨point, ⟨index, hpoint⟩⟩
        let sourcePreimage := sourcePoint targetPoint
        have hsourceCarrier : (sourcePreimage : Point3) ∈
            sourceShading.carrier index := by
          exact pureWZ2Proposition64ExactSourcePoint_mem_carrier
            index point hpoint
        change |inner ℝ
            (pureWZ2Proposition64ImageTube targetDelta g slabCenter
              anchorHeight halfHeight normalization translation hhalfHeight
              (by linarith) (sourceFamily.tube index)).direction
            (pureWZ2Proposition64TransportedNormal (g anchorHeight)
              halfHeight normalization
              (sourceLocal.planeMap sourcePreimage))| ≤ sourceDelta
        exact pureWZ2Proposition64ImageTube_inner_transportedNormal g
          slabCenter anchorHeight translation hsourceDelta hhalfHeight
          hhalfHeightSmall hnormalization hanchorSlope
          (sourceFamily.tube index) (hsourceLine index).vertical
          (sourceLocal.planeMap sourcePreimage)
          (sourceLocal.planeMap_unit sourcePreimage)
          (hsourceVertical sourcePreimage)
          (sourceLocal.planeMap_incidence index sourcePreimage hsourceCarrier)
      planeMap_incidence := by
        intro index point hpoint
        exact (pureWZ2Proposition64ImageTube_inner_transportedNormal g
          slabCenter anchorHeight translation hsourceDelta hhalfHeight
          hhalfHeightSmall hnormalization hanchorSlope
          (sourceFamily.tube index) (hsourceLine index).vertical
          (sourceLocal.planeMap (sourcePoint ⟨point, ⟨index, hpoint⟩⟩))
          (sourceLocal.planeMap_unit
            (sourcePoint ⟨point, ⟨index, hpoint⟩⟩))
          (hsourceVertical (sourcePoint ⟨point, ⟨index, hpoint⟩⟩))
          (sourceLocal.planeMap_incidence index
            (sourcePoint ⟨point, ⟨index, hpoint⟩⟩)
            (pureWZ2Proposition64ExactSourcePoint_mem_carrier
              index point hpoint))).trans hsourceTarget
      planeMap_vertical_bound := by
        intro point
        exact pureWZ2Proposition64TransportedNormal_vertical_bound
          hhalfHeight hhalfHeightSmall hanchorSlope hnormalization
          (sourceLocal.planeMap_unit (sourcePoint point))
          (hsourceVertical (sourcePoint point)) }

end Kakeya.Assouad
