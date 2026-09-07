import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64ExactImageLocalGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PaperADSixDeltaPerturbation
import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingIsotropicVolume
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Final isotropic normalization of the Proposition 6.4 plane field

After the exact affine map `Phi`, the transported plane field is Lipschitz
with a fixed constant.  The mild-rescaling step of Lemma 3.5 applies one
positive isotropic dilation, extends the field to the cubical saturation, and
normalizes it.  This file records precisely those operations.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

attribute [local instance] Classical.propDecidable

/-- The final positive isotropic similarity in Lemma 3.5. -/
def pureWZ2Proposition64IsotropicMap
    (center : Point3) (scale : ℝ) (point : Point3) : Point3 :=
  scale • (point - center)

/-- The inverse of the final positive isotropic similarity. -/
def pureWZ2Proposition64IsotropicInverse
    (center : Point3) (scale : ℝ) (point : Point3) : Point3 :=
  center + scale⁻¹ • point

/-- The final isotropic similarity has the expected cubic Jacobian. -/
theorem pureWZ2Proposition64IsotropicMap_volume_image_eq
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    {source : Set Point3} (hsource : MeasurableSet source) :
    MeasureTheory.volume
        (pureWZ2Proposition64IsotropicMap center scale '' source) =
      ENNReal.ofReal (scale ^ 3) * MeasureTheory.volume source := by
  simpa only [pureWZ2Proposition64IsotropicMap,
    wz1IsotropicRescalingMap] using
      volume_image_wz1IsotropicRescalingMap hscale center hsource

@[simp] theorem pureWZ2Proposition64IsotropicMap_inverse
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (point : Point3) :
    pureWZ2Proposition64IsotropicMap center scale
        (pureWZ2Proposition64IsotropicInverse center scale point) = point := by
  simp only [pureWZ2Proposition64IsotropicMap,
    pureWZ2Proposition64IsotropicInverse]
  have hsub : center + scale⁻¹ • point - center = scale⁻¹ • point := by
    abel
  rw [hsub, smul_smul]
  have hmul : scale * scale⁻¹ = 1 := by field_simp [hscale.ne']
  rw [hmul, one_smul]

@[simp] theorem pureWZ2Proposition64IsotropicInverse_map
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (point : Point3) :
    pureWZ2Proposition64IsotropicInverse center scale
        (pureWZ2Proposition64IsotropicMap center scale point) = point := by
  simp only [pureWZ2Proposition64IsotropicMap,
    pureWZ2Proposition64IsotropicInverse, smul_smul]
  have hmul : scale⁻¹ * scale = 1 := by field_simp [hscale.ne']
  rw [hmul, one_smul]
  abel

/-- Canonical exact-image point below a point of the isotropically dilated
exact image. -/
def pureWZ2Proposition64IsotropicSourcePoint
    {exactImage : Set Point3} (center : Point3) {scale : ℝ}
    (hscale : 0 < scale)
    (target : {point : Point3 //
      point ∈ pureWZ2Proposition64IsotropicMap center scale '' exactImage}) :
    {point : Point3 // point ∈ exactImage} :=
  ⟨pureWZ2Proposition64IsotropicInverse center scale target, by
    rcases target.property with ⟨source, hsource, heq⟩
    have hinverse :
        pureWZ2Proposition64IsotropicInverse center scale target = source := by
      rw [← heq, pureWZ2Proposition64IsotropicInverse_map center hscale]
    rwa [hinverse]⟩

@[simp] theorem pureWZ2Proposition64IsotropicMap_sourcePoint
    {exactImage : Set Point3} (center : Point3) {scale : ℝ}
    (hscale : 0 < scale)
    (target : {point : Point3 //
      point ∈ pureWZ2Proposition64IsotropicMap center scale '' exactImage}) :
    pureWZ2Proposition64IsotropicMap center scale
        (pureWZ2Proposition64IsotropicSourcePoint center hscale target) =
      target := by
  exact pureWZ2Proposition64IsotropicMap_inverse center hscale target

theorem pureWZ2Proposition64IsotropicSourcePoint_dist
    {exactImage : Set Point3} (center : Point3) {scale : ℝ}
    (hscale : 0 < scale)
    (first second : {point : Point3 //
      point ∈ pureWZ2Proposition64IsotropicMap center scale '' exactImage}) :
    dist (pureWZ2Proposition64IsotropicSourcePoint center hscale first)
        (pureWZ2Proposition64IsotropicSourcePoint center hscale second) =
      dist (first : Point3) (second : Point3) / scale := by
  simp only [pureWZ2Proposition64IsotropicSourcePoint, Subtype.dist_eq,
    pureWZ2Proposition64IsotropicInverse, dist_eq_norm]
  have hdiff : center + scale⁻¹ • (first : Point3) -
      (center + scale⁻¹ • (second : Point3)) =
        scale⁻¹ • ((first : Point3) - (second : Point3)) := by
    rw [smul_sub]
    module
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hscale, div_eq_mul_inv]
  ring

/-- Pull the exact-image normal field through the final isotropic dilation.
The normal itself is unchanged because the inverse transpose is scalar. -/
def pureWZ2Proposition64IsotropicPlaneMap
    {exactImage : Set Point3}
    (rawNormal : {point : Point3 // point ∈ exactImage} → Point3)
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (target : {point : Point3 //
      point ∈ pureWZ2Proposition64IsotropicMap center scale '' exactImage}) :
    Point3 :=
  rawNormal (pureWZ2Proposition64IsotropicSourcePoint center hscale target)

theorem pureWZ2Proposition64IsotropicPlaneMap_unit
    {exactImage : Set Point3}
    (rawNormal : {point : Point3 // point ∈ exactImage} → Point3)
    (hrawUnit : ∀ point, ‖rawNormal point‖ = 1)
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (target : {point : Point3 //
      point ∈ pureWZ2Proposition64IsotropicMap center scale '' exactImage}) :
    ‖pureWZ2Proposition64IsotropicPlaneMap rawNormal center hscale target‖ = 1 :=
  hrawUnit (pureWZ2Proposition64IsotropicSourcePoint center hscale target)

/-- Dilation by `scale` divides the Lipschitz constant of the exact-image
normal field by `scale`. -/
theorem pureWZ2Proposition64IsotropicPlaneMap_lipschitz
    {exactImage : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {sourceK targetK : NNReal}
    (hrawLipschitz : LipschitzWith sourceK rawNormal)
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (hK : (sourceK : ℝ) ≤ (targetK : ℝ) * scale) :
    LipschitzWith targetK
      (pureWZ2Proposition64IsotropicPlaneMap rawNormal center hscale) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  have hsource := hrawLipschitz.dist_le_mul
    (pureWZ2Proposition64IsotropicSourcePoint center hscale first)
    (pureWZ2Proposition64IsotropicSourcePoint center hscale second)
  rw [pureWZ2Proposition64IsotropicSourcePoint_dist center hscale] at hsource
  calc
    dist (pureWZ2Proposition64IsotropicPlaneMap rawNormal center hscale first)
        (pureWZ2Proposition64IsotropicPlaneMap rawNormal center hscale second)
        ≤ (sourceK : ℝ) * (dist (first : Point3) (second : Point3) / scale) :=
          hsource
    _ ≤ ((targetK : ℝ) * scale) *
          (dist (first : Point3) (second : Point3) / scale) := by gcongr
    _ = (targetK : ℝ) * dist first second := by
          rw [Subtype.dist_eq]
          field_simp [hscale.ne']

/-- A subset of a positive affine image of a paper AD set inherits the same
bound at every larger base scale. -/
theorem PureWZ2PaperADSet1.affine_image_subset_coarsen
    {source target : Set ℝ}
    {sourceDelta targetDelta alpha a b : ℝ} {C : ENNReal}
    (hsource : PureWZ2PaperADSet1 source sourceDelta alpha C)
    (ha : 0 < a) (htargetDelta : 0 < targetDelta)
    (hbase : a * sourceDelta ≤ targetDelta)
    (hsubset : target ⊆ (fun value : ℝ => a * value + b) '' source) :
    PureWZ2PaperADSet1 target targetDelta alpha C := by
  have himage : PureWZ2PaperADSet1
      ((fun value : ℝ => a * value + b) '' source)
      (a * sourceDelta) alpha C := by
    simpa only [Set.image_image, Function.comp_apply] using
      (hsource.image_mul ha).translate b
  exact (himage.coarsen_scale htargetDelta hbase).mono hsubset

/-- Distances in the final isotropic image are exactly multiplied by its
positive scale. -/
theorem pureWZ2Proposition64IsotropicMap_dist
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (first second : Point3) :
    dist (pureWZ2Proposition64IsotropicMap center scale first)
        (pureWZ2Proposition64IsotropicMap center scale second) =
      scale * dist first second := by
  simp only [pureWZ2Proposition64IsotropicMap, dist_eq_norm]
  have hdiff : scale • (first - center) - scale • (second - center) =
      scale • (first - second) := by
    rw [← smul_sub]
    congr 1
    abel
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hscale]

/-- Exact scalar-projection covariance for the Proposition 6.4 affine map
followed by the final isotropic dilation. -/
theorem pureWZ2Proposition64Combined_projection_difference
    (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation isotropicCenter : Point3) {scale : ℝ}
    (hhalfHeight : halfHeight ≠ 0)
    (hnormalization : normalization ≠ 0)
    (first second normal : Point3) :
    let transported := pureWZ2Proposition64InverseTranspose
      (g anchorHeight) halfHeight normalization normal
    let normalized := (‖transported‖⁻¹ : ℝ) • transported
    inner ℝ
          (pureWZ2Proposition64IsotropicMap isotropicCenter scale
            (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
              halfHeight normalization translation first)) normalized -
        inner ℝ
          (pureWZ2Proposition64IsotropicMap isotropicCenter scale
            (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
              halfHeight normalization translation second)) normalized =
      (scale / ‖transported‖) *
        (inner ℝ first normal - inner ℝ second normal) := by
  dsimp only
  let transported := pureWZ2Proposition64InverseTranspose
    (g anchorHeight) halfHeight normalization normal
  have hmapDifference :
      pureWZ2Proposition64IsotropicMap isotropicCenter scale
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation first) -
        pureWZ2Proposition64IsotropicMap isotropicCenter scale
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation second) =
      scale • pureWZ2Proposition64Linear (g anchorHeight) halfHeight
        normalization (first - second) := by
    simp only [pureWZ2Proposition64IsotropicMap]
    rw [← smul_sub]
    congr 1
    rw [show
      (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
            normalization translation first - isotropicCenter) -
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation second - isotropicCenter) =
        pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
            normalization translation first -
          pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation second by abel]
    rw [pureWZ2Proposition64TranslatedMap_sub]
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2Proposition64Map, pureWZ2Proposition64Linear, point3] <;>
      ring
  rw [← inner_sub_left, hmapDifference, inner_smul_left, inner_smul_right,
    pureWZ2Proposition64Linear_inner_inverseTranspose (g anchorHeight)
      hhalfHeight hnormalization, inner_sub_left]
  simp only [starRingEnd_apply, star_trivial]
  ring

/-- The source distance recovered from the exact Proposition 6.4 map and a
positive isotropic dilation. -/
theorem pureWZ2Proposition64Combined_source_dist_le
    (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation isotropicCenter : Point3) {scale : ℝ}
    (hscale : 0 < scale)
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightOne : halfHeight ≤ 1)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hnormalization : 9 ≤ normalization)
    (first second : Point3) :
    dist first second ≤ 3 * normalization *
      (dist
        (pureWZ2Proposition64IsotropicMap isotropicCenter scale
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation first))
        (pureWZ2Proposition64IsotropicMap isotropicCenter scale
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation second)) / scale) := by
  have hinverse := pureWZ2Proposition64TranslatedInverse_dist_le g
    slabCenter anchorHeight halfHeight normalization translation
    (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
      normalization translation first)
    (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
      normalization translation second) (by
        rw [abs_of_pos hhalfHeight]
        exact hhalfHeightOne) hanchorSlope hnormalization
  rw [pureWZ2Proposition64TranslatedInverse_map g slabCenter anchorHeight
      translation first hhalfHeight.ne' (by linarith),
    pureWZ2Proposition64TranslatedInverse_map g slabCenter anchorHeight
      translation second hhalfHeight.ne' (by linarith)] at hinverse
  rw [pureWZ2Proposition64IsotropicMap_dist isotropicCenter hscale]
  simpa [hscale.ne'] using hinverse

/-- The covering-number part of local AD transport.  Geometry is supplied by
an actual source point, a source-ball containment, and the exact affine
projection relation. -/
theorem pureWZ2Proposition64_affine_isotropic_local_ad
    {sourceDelta sourceRho targetRho sigma a b : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (sourcePoint : {point : Point3 // point ∈ sourceShading.union})
    (targetNormal : Point3) (targetSet : Set Point3)
    (hsourceRho : sourceDelta ≤ sourceRho)
    (hsourceRhoOne : sourceRho ≤ 1)
    (ha : 0 < a) (htargetRho : 0 < targetRho)
    (hbase : a * sourceRho ≤ targetRho)
    (hprojection : scalarProjection targetNormal targetSet ⊆
      (fun value : ℝ => a * value + b) ''
        scalarProjection (sourceLocal.planeMap sourcePoint)
          (sourceShading.union ∩
            Metric.closedBall (sourcePoint : Point3)
              (Real.sqrt sourceRho))) :
    PureWZ2PaperADSet1 (scalarProjection targetNormal targetSet)
      targetRho (1 - sigma) C := by
  exact (sourceLocal.local_ad sourceRho hsourceRho hsourceRhoOne sourcePoint)
    |>.affine_image_subset_coarsen ha htargetRho hbase hprojection

/-- Local AD on a genuine subset of the exact Proposition 6.4 image followed
by the final isotropic dilation.  The two displayed inequalities are exactly
the ball-distortion and projection-scale budgets from Lemma 3.5. -/
theorem pureWZ2Proposition64_exact_isotropic_local_ad_of_image_in_ball
    {sourceDelta sourceRho targetRho targetRadius sigma scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation isotropicCenter : Point3)
    (hhalfHeight : 0 < halfHeight) (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hscale : 0 < scale)
    (sourcePoint : {point : Point3 // point ∈ sourceShading.union})
    (hsourceVertical : |sourceLocal.planeMap sourcePoint 2| ≤ 1 / 2)
    (targetPoint : Point3)
    (htargetPoint : targetPoint =
      pureWZ2Proposition64IsotropicMap isotropicCenter scale
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation sourcePoint))
    (targetSet : Set Point3)
    (htargetImage : targetSet ⊆
      (fun source =>
        pureWZ2Proposition64IsotropicMap isotropicCenter scale
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation source)) ''
        sourceShading.union)
    (htargetBall : targetSet ⊆
      Metric.closedBall targetPoint targetRadius)
    (hsourceRho : sourceDelta ≤ sourceRho)
    (hsourceRhoOne : sourceRho ≤ 1)
    (hball : 3 * normalization * (targetRadius / scale) ≤
      Real.sqrt sourceRho)
    (hbase :
      (scale / ‖pureWZ2Proposition64InverseTranspose (g anchorHeight)
          halfHeight normalization (sourceLocal.planeMap sourcePoint)‖) *
        sourceRho ≤ targetRho)
    (htargetRho : 0 < targetRho) :
    PureWZ2PaperADSet1
      (scalarProjection
        (pureWZ2Proposition64TransportedNormal (g anchorHeight)
          halfHeight normalization (sourceLocal.planeMap sourcePoint))
        targetSet) targetRho (1 - sigma) C := by
  let transported := pureWZ2Proposition64InverseTranspose (g anchorHeight)
    halfHeight normalization (sourceLocal.planeMap sourcePoint)
  have htransportedLower : (1 / 4 : ℝ) ≤ ‖transported‖ :=
    pureWZ2Proposition64InverseTranspose_norm_lower hanchorSlope
      hnormalization (sourceLocal.planeMap_unit sourcePoint) hsourceVertical
  have htransportedNorm : 0 < ‖transported‖ := by linarith
  let targetNormal := pureWZ2Proposition64TransportedNormal (g anchorHeight)
    halfHeight normalization (sourceLocal.planeMap sourcePoint)
  let a := scale / ‖transported‖
  let b := inner ℝ targetPoint targetNormal -
    a * inner ℝ (sourcePoint : Point3) (sourceLocal.planeMap sourcePoint)
  have ha : 0 < a := div_pos hscale htransportedNorm
  have hprojection : scalarProjection targetNormal targetSet ⊆
      (fun value : ℝ => a * value + b) ''
        scalarProjection (sourceLocal.planeMap sourcePoint)
          (sourceShading.union ∩
            Metric.closedBall (sourcePoint : Point3)
              (Real.sqrt sourceRho)) := by
    rintro value ⟨target, htargetSet, rfl⟩
    rcases htargetImage htargetSet with
      ⟨source, hsource, hsourceTargetEq⟩
    have hsourceDistance : dist source (sourcePoint : Point3) ≤
        3 * normalization * (dist target targetPoint / scale) := by
      have h := pureWZ2Proposition64Combined_source_dist_le g slabCenter
        anchorHeight halfHeight normalization translation isotropicCenter
        hscale hhalfHeight hhalfHeightOne hanchorSlope hnormalization
        source sourcePoint
      calc
        dist source (sourcePoint : Point3) ≤
            3 * normalization *
              (dist
                (pureWZ2Proposition64IsotropicMap isotropicCenter scale
                  (pureWZ2Proposition64TranslatedMap g slabCenter
                    anchorHeight halfHeight normalization translation source))
                (pureWZ2Proposition64IsotropicMap isotropicCenter scale
                  (pureWZ2Proposition64TranslatedMap g slabCenter
                    anchorHeight halfHeight normalization translation
                      sourcePoint)) / scale) := h
        _ = 3 * normalization * (dist target targetPoint / scale) := by
          congr 2
          exact congrArg₂ dist hsourceTargetEq htargetPoint.symm
    have hsourceBall : source ∈
        Metric.closedBall (sourcePoint : Point3) (Real.sqrt sourceRho) := by
      rw [Metric.mem_closedBall]
      calc
        dist source (sourcePoint : Point3) ≤
            3 * normalization * (dist target targetPoint / scale) :=
          hsourceDistance
        _ ≤ 3 * normalization * (targetRadius / scale) := by
          gcongr
          exact htargetBall htargetSet
        _ ≤ Real.sqrt sourceRho := hball
    refine ⟨inner ℝ source (sourceLocal.planeMap sourcePoint),
      ⟨source, ⟨hsource, hsourceBall⟩, rfl⟩, ?_⟩
    have hdifference := pureWZ2Proposition64Combined_projection_difference
      (scale := scale) g slabCenter anchorHeight halfHeight normalization translation
      isotropicCenter hhalfHeight.ne' (by linarith) source sourcePoint
      (sourceLocal.planeMap sourcePoint)
    dsimp only [transported, targetNormal, a, b,
      pureWZ2Proposition64TransportedNormal] at hdifference ⊢
    calc
      scale / ‖pureWZ2Proposition64InverseTranspose (g anchorHeight)
              halfHeight normalization (sourceLocal.planeMap sourcePoint)‖ *
            inner ℝ source (sourceLocal.planeMap sourcePoint) +
          (inner ℝ targetPoint
              (‖pureWZ2Proposition64InverseTranspose (g anchorHeight)
                    halfHeight normalization
                    (sourceLocal.planeMap sourcePoint)‖⁻¹ •
                pureWZ2Proposition64InverseTranspose (g anchorHeight)
                  halfHeight normalization
                  (sourceLocal.planeMap sourcePoint)) -
            scale / ‖pureWZ2Proposition64InverseTranspose (g anchorHeight)
                    halfHeight normalization
                    (sourceLocal.planeMap sourcePoint)‖ *
              inner ℝ (sourcePoint : Point3)
                (sourceLocal.planeMap sourcePoint)) =
          inner ℝ
            (pureWZ2Proposition64IsotropicMap isotropicCenter scale
              (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
                halfHeight normalization translation source))
            (‖pureWZ2Proposition64InverseTranspose (g anchorHeight)
                  halfHeight normalization (sourceLocal.planeMap sourcePoint)‖⁻¹ •
              pureWZ2Proposition64InverseTranspose (g anchorHeight)
                halfHeight normalization
                (sourceLocal.planeMap sourcePoint)) := by
            rw [htargetPoint]
            linarith [hdifference]
      _ = inner ℝ target
            (‖pureWZ2Proposition64InverseTranspose (g anchorHeight)
                  halfHeight normalization (sourceLocal.planeMap sourcePoint)‖⁻¹ •
              pureWZ2Proposition64InverseTranspose (g anchorHeight)
                halfHeight normalization
                (sourceLocal.planeMap sourcePoint)) := by
            exact congrArg (fun point => inner ℝ point
              (‖pureWZ2Proposition64InverseTranspose (g anchorHeight)
                    halfHeight normalization
                    (sourceLocal.planeMap sourcePoint)‖⁻¹ •
                pureWZ2Proposition64InverseTranspose (g anchorHeight)
                  halfHeight normalization
                  (sourceLocal.planeMap sourcePoint))) hsourceTargetEq
  exact pureWZ2Proposition64_affine_isotropic_local_ad sourceLocal
    sourcePoint targetNormal targetSet hsourceRho hsourceRhoOne ha
    htargetRho (by simpa [a, transported] using hbase) hprojection

/-- A unit normal field on a cubical saturation, with a genuine exact-image
witness at every target point. -/
structure PureWZ2Proposition64SaturationPlaneMapData
    (exactImage target : Set Point3)
    (rawNormal : {point : Point3 // point ∈ exactImage} → Point3)
    (witnessRadius error : ℝ) where
  sourcePoint : {point : Point3 // point ∈ target} →
    {point : Point3 // point ∈ exactImage}
  sourcePoint_dist : ∀ point : {point : Point3 // point ∈ target},
    dist (point : Point3) (sourcePoint point : Point3) ≤ witnessRadius
  planeMap : {point : Point3 // point ∈ target} → Point3
  planeMap_lipschitz : LipschitzWith 1 planeMap
  planeMap_unit : ∀ point : {point : Point3 // point ∈ target},
    ‖planeMap point‖ = 1
  planeMap_close_of_dist :
    ∀ (point : {point : Point3 // point ∈ target})
      (source : {point : Point3 // point ∈ exactImage}),
    dist (point : Point3) (source : Point3) ≤ witnessRadius →
      ‖planeMap point - rawNormal source‖ ≤ error

/-- Kirszbraun extension followed by normalization.  The dilation is chosen
large enough that the normalized extension is one-Lipschitz. -/
theorem pureWZ2Proposition64_extendPlaneMapToSaturation
    {exactImage target : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {K : NNReal} {witnessRadius : ℝ}
    (hrawLipschitz : LipschitzWith K rawNormal)
    (hrawUnit : ∀ point, ‖rawNormal point‖ = 1)
    (hwitnessRadius : 0 ≤ witnessRadius)
    (targetWitness : ∀ point : {point : Point3 // point ∈ target},
      ∃ source : {point : Point3 // point ∈ exactImage},
        dist (point : Point3) (source : Point3) ≤ witnessRadius)
    (hsmall : ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) *
      witnessRadius ≤ 1 / 2)
    (hone : 4 * ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) ≤ 1) :
    Nonempty (PureWZ2Proposition64SaturationPlaneMapData exactImage target
      rawNormal witnessRadius
      (4 * ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) *
        witnessRadius)) := by
  let partialMap : Point3 → Point3 := fun point =>
    if hpoint : point ∈ exactImage then rawNormal ⟨point, hpoint⟩ else 0
  have hpartial : LipschitzOnWith K partialMap exactImage := by
    apply LipschitzOnWith.of_dist_le_mul
    intro first hfirst second hsecond
    have hfirstEq : partialMap first = rawNormal ⟨first, hfirst⟩ := by
      simp [partialMap, hfirst]
    have hsecondEq : partialMap second = rawNormal ⟨second, hsecond⟩ := by
      simp [partialMap, hsecond]
    rw [hfirstEq, hsecondEq]
    simpa [Subtype.dist_eq] using
      hrawLipschitz.dist_le_mul ⟨first, hfirst⟩ ⟨second, hsecond⟩
  rcases hpartial.extend_finite_dimension with
    ⟨extended, hextendedLipschitz, hextendedEq⟩
  let sourcePoint : {point : Point3 // point ∈ target} →
      {point : Point3 // point ∈ exactImage} :=
    fun point => Classical.choose (targetWitness point)
  have hsourcePoint : ∀ point : {point : Point3 // point ∈ target},
      dist (point : Point3) (sourcePoint point : Point3) ≤ witnessRadius :=
    fun point => Classical.choose_spec (targetWitness point)
  let rawExtended : {point : Point3 // point ∈ target} → Point3 :=
    fun point => extended point
  have hrawExtendedLipschitz :
      LipschitzWith (lipschitzExtensionConstant Point3 * K) rawExtended := by
    intro first second
    simpa [rawExtended, Subtype.edist_eq] using
      hextendedLipschitz first.1 second.1
  have hextendedSource : ∀ point,
      extended (sourcePoint point : Point3) = rawNormal (sourcePoint point) := by
    intro point
    have heq := hextendedEq (sourcePoint point).property
    simpa [partialMap, (sourcePoint point).property] using heq.symm
  have hrawClose : ∀ point,
      ‖rawExtended point - rawNormal (sourcePoint point)‖ ≤
        ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) *
          witnessRadius := by
    intro point
    have hdist := hextendedLipschitz.dist_le_mul
      (point : Point3) (sourcePoint point : Point3)
    rw [hextendedSource point] at hdist
    rw [dist_eq_norm] at hdist
    exact hdist.trans <| mul_le_mul_of_nonneg_left
      (hsourcePoint point) (by positivity)
  have hrawNormLower : ∀ point, 1 / 2 ≤ ‖rawExtended point‖ := by
    intro point
    have hnormDiff :
        |‖rawExtended point‖ - ‖rawNormal (sourcePoint point)‖| ≤
          ‖rawExtended point - rawNormal (sourcePoint point)‖ :=
      abs_norm_sub_norm_le _ _
    rw [hrawUnit (sourcePoint point)] at hnormDiff
    have hclose := hrawClose point
    have habsLower : 1 - ‖rawExtended point‖ ≤
        |‖rawExtended point‖ - 1| := by
      have heq : 1 - ‖rawExtended point‖ =
          -(‖rawExtended point‖ - 1) := by ring
      rw [heq]
      exact neg_le_abs _
    linarith
  let planeMap : {point : Point3 // point ∈ target} → Point3 :=
    fun point => (‖rawExtended point‖⁻¹ : ℝ) • rawExtended point
  have hplaneUnit : ∀ point, ‖planeMap point‖ = 1 := by
    intro point
    have hnormPos : 0 < ‖rawExtended point‖ := by
      linarith [hrawNormLower point]
    simp [planeMap, norm_smul, abs_of_nonneg, hnormPos.ne']
  have hplaneLipschitzFour : LipschitzWith
      ⟨4 * ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ), by
        positivity⟩ planeMap := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    rw [dist_eq_norm]
    have hnormal := pureWZ2Proposition64_normalization_lipschitz
      (first := rawExtended first) (second := rawExtended second)
      (lower := (1 / 2 : ℝ)) (by norm_num)
      (hrawNormLower first) (hrawNormLower second)
    have hrawDist := hrawExtendedLipschitz.dist_le_mul first second
    rw [dist_eq_norm] at hrawDist
    calc
      ‖planeMap first - planeMap second‖
          ≤ 4 * ‖rawExtended first - rawExtended second‖ := by
            convert hnormal using 1 <;> norm_num
      _ ≤ 4 * (((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) *
            dist first second) := by gcongr
      _ = (4 * ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ)) *
            dist first second := by ring
  have hplaneLipschitz : LipschitzWith 1 planeMap :=
    hplaneLipschitzFour.weaken (by exact_mod_cast hone)
  have hplaneClose :
      ∀ (point : {point : Point3 // point ∈ target})
        (source : {point : Point3 // point ∈ exactImage}),
      dist (point : Point3) (source : Point3) ≤ witnessRadius →
        ‖planeMap point - rawNormal source‖ ≤
          4 * ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) *
            witnessRadius := by
    intro point source hdist
    have hextendedSource' :
        extended (source : Point3) = rawNormal source := by
      have heq := hextendedEq source.property
      simpa [partialMap, source.property] using heq.symm
    have hrawClose' :
        ‖rawExtended point - rawNormal source‖ ≤
          ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) *
            witnessRadius := by
      have hdistExtended := hextendedLipschitz.dist_le_mul
        (point : Point3) (source : Point3)
      rw [hextendedSource'] at hdistExtended
      rw [dist_eq_norm] at hdistExtended
      exact hdistExtended.trans (by gcongr)
    have hnormal := pureWZ2Proposition64_normalization_lipschitz
      (first := rawExtended point) (second := rawNormal source)
      (lower := (1 / 2 : ℝ)) (by norm_num)
      (hrawNormLower point) (by rw [hrawUnit source]; norm_num)
    have hrawNormalized :
        (‖rawNormal source‖⁻¹ : ℝ) • rawNormal source = rawNormal source := by
      rw [hrawUnit source]
      simp
    rw [hrawNormalized] at hnormal
    calc
      ‖planeMap point - rawNormal source‖
          ≤ 4 * ‖rawExtended point - rawNormal source‖ := by
            convert hnormal using 1 <;> norm_num
      _ ≤ 4 * (((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) *
            witnessRadius) := by gcongr
      _ = 4 * ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) *
            witnessRadius := by ring
  exact ⟨{
    sourcePoint := sourcePoint
    sourcePoint_dist := hsourcePoint
    planeMap := planeMap
    planeMap_lipschitz := hplaneLipschitz
    planeMap_unit := hplaneUnit
    planeMap_close_of_dist := hplaneClose }⟩

namespace PureWZ2Proposition64SaturationPlaneMapData

/-- Incidence survives replacing the exact normal by its nearby normalized
extension. -/
theorem incidence_of_nearby_exact
    {exactImage target : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {witnessRadius error sourceDelta targetDelta : ℝ}
    (data : PureWZ2Proposition64SaturationPlaneMapData exactImage target
      rawNormal witnessRadius error)
    {direction : Point3} (hdirection : ‖direction‖ = 1)
    (point : {point : Point3 // point ∈ target})
    (source : {point : Point3 // point ∈ exactImage})
    (hdist : dist (point : Point3) (source : Point3) ≤ witnessRadius)
    (hexact : |inner ℝ direction (rawNormal source)| ≤ sourceDelta)
    (hbudget : sourceDelta + error ≤ targetDelta) :
    |inner ℝ direction (data.planeMap point)| ≤ targetDelta := by
  have hperturb :
      |inner ℝ direction (data.planeMap point - rawNormal source)| ≤ error := by
    calc
      |inner ℝ direction (data.planeMap point - rawNormal source)|
          ≤ ‖direction‖ * ‖data.planeMap point - rawNormal source‖ :=
            abs_real_inner_le_norm _ _
      _ = ‖data.planeMap point - rawNormal source‖ := by
            rw [hdirection, one_mul]
      _ ≤ error := data.planeMap_close_of_dist point source hdist
  have hsplit : inner ℝ direction (data.planeMap point) =
      inner ℝ direction (rawNormal source) +
        inner ℝ direction (data.planeMap point - rawNormal source) := by
    rw [inner_sub_right]
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans ((add_le_add hexact hperturb).trans hbudget)

/-- The final vertical-normal bound survives the saturation perturbation. -/
theorem vertical_bound_of_nearby_exact
    {exactImage target : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {witnessRadius error bound targetBound : ℝ}
    (data : PureWZ2Proposition64SaturationPlaneMapData exactImage target
      rawNormal witnessRadius error)
    (point : {point : Point3 // point ∈ target})
    (source : {point : Point3 // point ∈ exactImage})
    (hdist : dist (point : Point3) (source : Point3) ≤ witnessRadius)
    (hexact : |rawNormal source 2| ≤ bound)
    (hbudget : bound + error ≤ targetBound) :
    |data.planeMap point 2| ≤ targetBound := by
  have hcoordinate :
      |data.planeMap point 2 - rawNormal source 2| ≤ error := by
    have hnorm := data.planeMap_close_of_dist point source hdist
    have happly : |data.planeMap point 2 - rawNormal source 2| ≤
        ‖data.planeMap point - rawNormal source‖ := by
      simpa [Real.norm_eq_abs] using
        PiLp.norm_apply_le (data.planeMap point - rawNormal source)
          (2 : Fin 3)
    exact happly.trans hnorm
  calc
    |data.planeMap point 2| ≤
        |rawNormal source 2| +
          |data.planeMap point 2 - rawNormal source 2| := by
      have h := abs_add_le (rawNormal source 2)
        (data.planeMap point 2 - rawNormal source 2)
      simpa only [add_sub_cancel] using h
    _ ≤ bound + error := add_le_add hexact hcoordinate
    _ ≤ targetBound := hbudget

/-- Local paper AD survives the cubical saturation.  The exact-image AD
certificate is requested on the enlarged ball prescribed in Lemma 3.5. -/
theorem local_ad_of_exact
    {exactImage target : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {witnessRadius error rho alpha pointBound : ℝ} {C : ENNReal}
    (data : PureWZ2Proposition64SaturationPlaneMapData exactImage target
      rawNormal witnessRadius error)
    (hwitnessRadius : 0 ≤ witnessRadius) (herror : 0 ≤ error)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 // point ∈ exactImage},
      ‖(source : Point3)‖ ≤ pointBound)
    (point : {point : Point3 // point ∈ target})
    (hexactAD : PureWZ2PaperADSet1
      (scalarProjection (rawNormal (data.sourcePoint point))
        (exactImage ∩ Metric.closedBall (data.sourcePoint point : Point3)
          (Real.sqrt rho + 2 * witnessRadius)))
      rho alpha C)
    (hprojectionBudget : witnessRadius + pointBound * error ≤ rho) :
    PureWZ2PaperADSet1
      (scalarProjection (data.planeMap point)
        (target ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)))
      rho alpha (6 * C) := by
  apply hexactAD.perturb_by_delta
  rintro value ⟨targetPoint, htargetPoint, rfl⟩
  let targetSubtype : {point : Point3 // point ∈ target} :=
    ⟨targetPoint, htargetPoint.1⟩
  let sourceSubtype : {point : Point3 // point ∈ exactImage} :=
    data.sourcePoint targetSubtype
  have hsourceDistance :
      dist targetPoint (sourceSubtype : Point3) ≤ witnessRadius :=
    data.sourcePoint_dist targetSubtype
  have hsourceBall : (sourceSubtype : Point3) ∈
      Metric.closedBall (data.sourcePoint point : Point3)
        (Real.sqrt rho + 2 * witnessRadius) := by
    rw [Metric.mem_closedBall]
    calc
      dist (sourceSubtype : Point3) (data.sourcePoint point : Point3)
          ≤ dist (sourceSubtype : Point3) targetPoint +
              dist targetPoint (point : Point3) +
                dist (point : Point3) (data.sourcePoint point : Point3) :=
            dist_triangle4 _ _ _ _
      _ ≤ witnessRadius + Real.sqrt rho + witnessRadius := by
            gcongr
            · simpa [dist_comm] using hsourceDistance
            · exact htargetPoint.2
            · exact data.sourcePoint_dist point
      _ = Real.sqrt rho + 2 * witnessRadius := by ring
  let sourceValue := inner ℝ (sourceSubtype : Point3)
    (rawNormal (data.sourcePoint point))
  refine ⟨sourceValue, ?_, ?_⟩
  · exact ⟨sourceSubtype, ⟨sourceSubtype.property, hsourceBall⟩, rfl⟩
  have hsplit :
      inner ℝ targetPoint (data.planeMap point) - sourceValue =
        inner ℝ (targetPoint - (sourceSubtype : Point3))
            (data.planeMap point) +
          inner ℝ (sourceSubtype : Point3)
            (data.planeMap point - rawNormal (data.sourcePoint point)) := by
    dsimp only [sourceValue]
    rw [inner_sub_left, inner_sub_right]
    ring
  rw [hsplit]
  calc
    |inner ℝ (targetPoint - (sourceSubtype : Point3)) (data.planeMap point) +
      inner ℝ (sourceSubtype : Point3)
        (data.planeMap point - rawNormal (data.sourcePoint point))|
        ≤ |inner ℝ (targetPoint - (sourceSubtype : Point3))
              (data.planeMap point)| +
            |inner ℝ (sourceSubtype : Point3)
              (data.planeMap point - rawNormal (data.sourcePoint point))| :=
          abs_add_le _ _
    _ ≤ ‖targetPoint - (sourceSubtype : Point3)‖ *
            ‖data.planeMap point‖ +
          ‖(sourceSubtype : Point3)‖ *
            ‖data.planeMap point - rawNormal (data.sourcePoint point)‖ := by
          gcongr <;> apply abs_real_inner_le_norm
    _ ≤ witnessRadius * 1 + pointBound * error := by
          gcongr
          · simpa [dist_eq_norm] using hsourceDistance
          · exact (data.planeMap_unit point).le
          · exact hexactBound sourceSubtype
          · exact data.planeMap_close_of_dist point
              (data.sourcePoint point) (data.sourcePoint_dist point)
    _ = witnessRadius + pointBound * error := by ring
    _ ≤ rho := hprojectionBudget

/-- Fixed-multiple version of `local_ad_of_exact`.  Proposition 6.4 uses a
paper-grid saturation whose exact-image witness is within `2 * delta`; the
normal perturbation contributes the remaining error.  Thus the natural
projection error is `O(delta)`, not at most one literal `delta`. -/
theorem local_ad_of_exact_six_delta
    {exactImage target : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {witnessRadius error rho alpha pointBound delta : ℝ} {C : ENNReal}
    (data : PureWZ2Proposition64SaturationPlaneMapData exactImage target
      rawNormal witnessRadius error)
    (hwitnessRadius : 0 ≤ witnessRadius) (herror : 0 ≤ error)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 // point ∈ exactImage},
      ‖(source : Point3)‖ ≤ pointBound)
    (point : {point : Point3 // point ∈ target})
    (hexactAD : PureWZ2PaperADSet1
      (scalarProjection (rawNormal (data.sourcePoint point))
        (exactImage ∩ Metric.closedBall (data.sourcePoint point : Point3)
          (Real.sqrt rho + 2 * witnessRadius)))
      rho alpha C)
    (hprojectionBudget : witnessRadius + pointBound * error ≤ 6 * delta)
    (hdeltaRho : delta ≤ rho) :
    PureWZ2PaperADSet1
      (scalarProjection (data.planeMap point)
        (target ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)))
      rho alpha (192 * C) := by
  apply hexactAD.perturb_by_six_delta
  rintro value ⟨targetPoint, htargetPoint, rfl⟩
  let targetSubtype : {point : Point3 // point ∈ target} :=
    ⟨targetPoint, htargetPoint.1⟩
  let sourceSubtype : {point : Point3 // point ∈ exactImage} :=
    data.sourcePoint targetSubtype
  have hsourceDistance :
      dist targetPoint (sourceSubtype : Point3) ≤ witnessRadius :=
    data.sourcePoint_dist targetSubtype
  have hsourceBall : (sourceSubtype : Point3) ∈
      Metric.closedBall (data.sourcePoint point : Point3)
        (Real.sqrt rho + 2 * witnessRadius) := by
    rw [Metric.mem_closedBall]
    calc
      dist (sourceSubtype : Point3) (data.sourcePoint point : Point3) ≤
          dist (sourceSubtype : Point3) targetPoint +
            dist targetPoint (point : Point3) +
              dist (point : Point3) (data.sourcePoint point : Point3) :=
        dist_triangle4 _ _ _ _
      _ ≤ witnessRadius + Real.sqrt rho + witnessRadius := by
        gcongr
        · simpa [dist_comm] using hsourceDistance
        · exact htargetPoint.2
        · exact data.sourcePoint_dist point
      _ = Real.sqrt rho + 2 * witnessRadius := by ring
  let sourceValue := inner ℝ (sourceSubtype : Point3)
    (rawNormal (data.sourcePoint point))
  refine ⟨sourceValue, ?_, ?_⟩
  · exact ⟨sourceSubtype, ⟨sourceSubtype.property, hsourceBall⟩, rfl⟩
  have hsplit :
      inner ℝ targetPoint (data.planeMap point) - sourceValue =
        inner ℝ (targetPoint - (sourceSubtype : Point3))
            (data.planeMap point) +
          inner ℝ (sourceSubtype : Point3)
            (data.planeMap point - rawNormal (data.sourcePoint point)) := by
    dsimp only [sourceValue]
    rw [inner_sub_left, inner_sub_right]
    ring
  rw [hsplit]
  calc
    |inner ℝ (targetPoint - (sourceSubtype : Point3)) (data.planeMap point) +
      inner ℝ (sourceSubtype : Point3)
        (data.planeMap point - rawNormal (data.sourcePoint point))| ≤
        |inner ℝ (targetPoint - (sourceSubtype : Point3))
            (data.planeMap point)| +
          |inner ℝ (sourceSubtype : Point3)
            (data.planeMap point - rawNormal (data.sourcePoint point))| :=
      abs_add_le _ _
    _ ≤ ‖targetPoint - (sourceSubtype : Point3)‖ * ‖data.planeMap point‖ +
        ‖(sourceSubtype : Point3)‖ *
          ‖data.planeMap point - rawNormal (data.sourcePoint point)‖ := by
      gcongr <;> apply abs_real_inner_le_norm
    _ ≤ witnessRadius * 1 + pointBound * error := by
      gcongr
      · simpa [dist_eq_norm] using hsourceDistance
      · exact (data.planeMap_unit point).le
      · exact hexactBound sourceSubtype
      · exact data.planeMap_close_of_dist point
          (data.sourcePoint point) (data.sourcePoint_dist point)
    _ = witnessRadius + pointBound * error := by ring
    _ ≤ 6 * delta := hprojectionBudget
    _ ≤ 6 * rho := by gcongr

/-- Package the extended unit normal, incidence stability, and the exact-image
local AD input into the public local-grain structure used by Node 5. -/
noncomputable def toLocalGrainData
    {delta sourceDelta sigma witnessRadius error pointBound : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {exactImage : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {C : ENNReal}
    (data : PureWZ2Proposition64SaturationPlaneMapData exactImage
      shading.union rawNormal witnessRadius error)
    (hwitnessRadius : 0 ≤ witnessRadius) (herror : 0 ≤ error)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 // point ∈ exactImage},
      ‖(source : Point3)‖ ≤ pointBound)
    (hincidence : ∀ index point,
      ∀ hpoint : point ∈ shading.carrier index,
        ∃ source : {point : Point3 // point ∈ exactImage},
          dist point (source : Point3) ≤ witnessRadius ∧
          |inner ℝ (family.tube index).direction (rawNormal source)| ≤
            sourceDelta)
    (hincidenceBudget : sourceDelta + error ≤ delta)
    (hprojectionBudget : witnessRadius + pointBound * error ≤ delta)
    (hexactAD : ∀ rho : ℝ, delta ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (rawNormal (data.sourcePoint point))
            (exactImage ∩
              Metric.closedBall (data.sourcePoint point : Point3)
                (Real.sqrt rho + 2 * witnessRadius)))
          rho (1 - sigma) C) :
    PureWZ2LocalGrainData shading sigma (6 * C) where
  planeMap := data.planeMap
  planeMap_lipschitz := data.planeMap_lipschitz
  planeMap_unit := data.planeMap_unit
  planeMap_incidence := by
    intro index point hpoint
    rcases hincidence index point hpoint with ⟨source, hdist, hexact⟩
    exact data.incidence_of_nearby_exact
      (family.tube index).direction_unit
      ⟨point, ⟨index, hpoint⟩⟩ source hdist hexact hincidenceBudget
  local_ad := by
    intro rho hrhoLower hrhoOne point
    exact data.local_ad_of_exact hwitnessRadius herror hpointBound
      hexactBound point (hexactAD rho hrhoLower hrhoOne point)
      (hprojectionBudget.trans hrhoLower)

/-- Package the saturation with the fixed-multiple projection perturbation
used by Proposition 6.4. -/
noncomputable def toLocalGrainDataSixDelta
    {delta sourceDelta sigma witnessRadius error pointBound : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {exactImage : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {C : ENNReal}
    (data : PureWZ2Proposition64SaturationPlaneMapData exactImage
      shading.union rawNormal witnessRadius error)
    (hwitnessRadius : 0 ≤ witnessRadius) (herror : 0 ≤ error)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 // point ∈ exactImage},
      ‖(source : Point3)‖ ≤ pointBound)
    (hincidence : ∀ index point,
      ∀ hpoint : point ∈ shading.carrier index,
        ∃ source : {point : Point3 // point ∈ exactImage},
          dist point (source : Point3) ≤ witnessRadius ∧
          |inner ℝ (family.tube index).direction (rawNormal source)| ≤
            sourceDelta)
    (hincidenceBudget : sourceDelta + error ≤ delta)
    (hprojectionBudget : witnessRadius + pointBound * error ≤ 6 * delta)
    (hexactAD : ∀ rho : ℝ, delta ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (rawNormal (data.sourcePoint point))
            (exactImage ∩
              Metric.closedBall (data.sourcePoint point : Point3)
                (Real.sqrt rho + 2 * witnessRadius)))
          rho (1 - sigma) C) :
    PureWZ2LocalGrainData shading sigma (192 * C) where
  planeMap := data.planeMap
  planeMap_lipschitz := data.planeMap_lipschitz
  planeMap_unit := data.planeMap_unit
  planeMap_incidence := by
    intro index point hpoint
    rcases hincidence index point hpoint with ⟨source, hdist, hexact⟩
    exact data.incidence_of_nearby_exact
      (family.tube index).direction_unit
      ⟨point, ⟨index, hpoint⟩⟩ source hdist hexact hincidenceBudget
  local_ad := by
    intro rho hrhoLower hrhoOne point
    exact data.local_ad_of_exact_six_delta hwitnessRadius herror hpointBound
      hexactBound point (hexactAD rho hrhoLower hrhoOne point)
      hprojectionBudget hrhoLower

/-- The transported field retains the final anchored-chart vertical bound. -/
theorem toLocalGrainData_vertical_bound
    {delta sourceDelta sigma witnessRadius error pointBound : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {exactImage : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {C : ENNReal}
    (data : PureWZ2Proposition64SaturationPlaneMapData exactImage
      shading.union rawNormal witnessRadius error)
    (hwitnessRadius : 0 ≤ witnessRadius) (herror : 0 ≤ error)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 // point ∈ exactImage},
      ‖(source : Point3)‖ ≤ pointBound)
    (hincidence : ∀ index point,
      ∀ hpoint : point ∈ shading.carrier index,
        ∃ source : {point : Point3 // point ∈ exactImage},
          dist point (source : Point3) ≤ witnessRadius ∧
          |inner ℝ (family.tube index).direction (rawNormal source)| ≤
            sourceDelta)
    (hincidenceBudget : sourceDelta + error ≤ delta)
    (hprojectionBudget : witnessRadius + pointBound * error ≤ delta)
    (hexactAD : ∀ rho : ℝ, delta ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (rawNormal (data.sourcePoint point))
            (exactImage ∩
              Metric.closedBall (data.sourcePoint point : Point3)
                (Real.sqrt rho + 2 * witnessRadius)))
          rho (1 - sigma) C)
    (hexactVertical : ∀ source, |rawNormal source 2| ≤ 1 / 10)
    (hverticalBudget : 1 / 10 + error ≤ 1 / 2) :
    ∀ point : {point : Point3 // point ∈ shading.union},
      |(data.toLocalGrainData hwitnessRadius herror hpointBound hexactBound
        hincidence hincidenceBudget hprojectionBudget hexactAD).planeMap point 2| ≤
        1 / 2 := by
  intro point
  exact data.vertical_bound_of_nearby_exact point (data.sourcePoint point)
    (data.sourcePoint_dist point) (hexactVertical (data.sourcePoint point))
    hverticalBudget

/-- The vertical bound for the fixed-multiple local-grain package. -/
theorem toLocalGrainDataSixDelta_vertical_bound
    {delta sourceDelta sigma witnessRadius error pointBound : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {exactImage : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {C : ENNReal}
    (data : PureWZ2Proposition64SaturationPlaneMapData exactImage
      shading.union rawNormal witnessRadius error)
    (hwitnessRadius : 0 ≤ witnessRadius) (herror : 0 ≤ error)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 // point ∈ exactImage},
      ‖(source : Point3)‖ ≤ pointBound)
    (hincidence : ∀ index point,
      ∀ hpoint : point ∈ shading.carrier index,
        ∃ source : {point : Point3 // point ∈ exactImage},
          dist point (source : Point3) ≤ witnessRadius ∧
          |inner ℝ (family.tube index).direction (rawNormal source)| ≤
            sourceDelta)
    (hincidenceBudget : sourceDelta + error ≤ delta)
    (hprojectionBudget : witnessRadius + pointBound * error ≤ 6 * delta)
    (hexactAD : ∀ rho : ℝ, delta ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (rawNormal (data.sourcePoint point))
            (exactImage ∩
              Metric.closedBall (data.sourcePoint point : Point3)
                (Real.sqrt rho + 2 * witnessRadius)))
          rho (1 - sigma) C)
    (hexactVertical : ∀ source, |rawNormal source 2| ≤ 1 / 10)
    (hverticalBudget : 1 / 10 + error ≤ 1 / 2) :
    ∀ point : {point : Point3 // point ∈ shading.union},
      |(data.toLocalGrainDataSixDelta hwitnessRadius herror hpointBound
        hexactBound hincidence hincidenceBudget hprojectionBudget
          hexactAD).planeMap point 2| ≤ 1 / 2 := by
  intro point
  exact data.vertical_bound_of_nearby_exact point (data.sourcePoint point)
    (data.sourcePoint_dist point) (hexactVertical (data.sourcePoint point))
    hverticalBudget

end PureWZ2Proposition64SaturationPlaneMapData

end Kakeya.Assouad

end
