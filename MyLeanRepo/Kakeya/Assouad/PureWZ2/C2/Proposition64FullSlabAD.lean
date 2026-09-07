import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64FinalSlope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64Lemma35LocalCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureCubicalGlobalSlabAD
import MyLeanRepo.Kakeya.Assouad.WZ1.VerticalRescalingSlabAD

/-!
# Global AD for the full Proposition 6.4 cubical saturation

The source cubical shading first supplies the slab form of global AD.  The
Proposition 6.4 affine map and final isotropic similarity then preserve that
control, while the same-grid witness for full cubical saturation contributes
only a fixed target-scale projection perturbation.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- A normalized slope is one-Lipschitz on the paper height interval. -/
theorem pureWZ2Proposition64_normalizedSlope_lipschitzOn
    {slope : SlopeFunction} (hnormalized : slope.IsNormalized) :
    LipschitzOnWith 1 slope (Set.Icc (-1 : ℝ) 1) := by
  have hdifferentiable : Differentiable ℝ slope :=
    slope.contDiff.differentiable (by norm_num)
  have hderiv : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ‖deriv slope z‖ ≤ (1 : ℝ) := by
    intro z hz
    simpa [Real.norm_eq_abs] using (hnormalized z hz).2.1
  intro first hfirst second hsecond
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => hdifferentiable.differentiableAt) hderiv
      (convex_Icc _ _) hfirst hsecond
  have hreal : dist (slope first) (slope second) ≤ dist first second := by
    simpa [Real.dist_eq, abs_sub_comm] using h
  rw [edist_dist, edist_dist]
  simpa using ENNReal.ofReal_le_ofReal hreal

/-- The exact affine image, including the common horizontal translation,
inherits slab AD at every coarser normalized radius.  The only error is the
variation of the translation term as the height moves across the slab. -/
theorem pureWZ2Proposition64TranslatedMap_globalSlabAD
    {sourceDelta sigma rawLoss extensionConstant targetBase slabRadius : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rawConstant slabConstant : ENNReal}
    {raw : PureWZ2RawC2GlobalGrainData
      sourceShading sigma rawConstant rawLoss extensionConstant}
    {slabCenter anchorHeight halfHeight normalization : ℝ}
    (normalized : PureWZ2Proposition64NormalizedData
      raw slabCenter anchorHeight halfHeight normalization)
    (sourceSlabAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (globalGrainProjection raw.slope
          (globalGrainSlab sourceShading.union z sourceDelta))
        sourceDelta (1 - sigma) slabConstant)
    (translation : Point3) (htranslationHeight : translation 2 = 0)
    (htranslationOne : |translation 1| ≤ 2)
    (htargetBase : 0 < targetBase)
    (hslabRadius : 0 < slabRadius)
    (hbase : sourceDelta / normalization ≤ targetBase)
    (hheightBudget : halfHeight * slabRadius ≤ sourceDelta)
    (hprojectionBudget : 2 * slabRadius ≤ 6 * targetBase) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (globalGrainProjection normalized.slope
          (globalGrainSlab
            (pureWZ2Proposition64TranslatedMap raw.slope slabCenter
              anchorHeight halfHeight normalization translation ''
              sourceShading.union) t slabRadius))
        targetBase (1 - sigma) (192 * slabConstant) := by
  intro t ht
  let sourceCenter := slabCenter + halfHeight * t
  have hsourceCenter : sourceCenter ∈ Set.Icc (-1 : ℝ) 1 :=
    normalized.source_window t ht
  have hscaled := (sourceSlabAD sourceCenter hsourceCenter).image_mul
    (one_div_pos.mpr normalized.normalization_pos)
  have hscaled' : PureWZ2PaperADSet1
      ((fun value : ℝ => value / normalization) ''
        globalGrainProjection raw.slope
          (globalGrainSlab sourceShading.union sourceCenter sourceDelta))
      (sourceDelta / normalization) (1 - sigma) slabConstant := by
    convert hscaled using 1 <;> simp [div_eq_mul_inv, mul_comm]
  let shift := inner ℝ translation (globalGrainDirection (normalized.slope t))
  have htranslated := hscaled'.translate shift
  have hcoarse := htranslated.coarsen_scale htargetBase hbase
  apply hcoarse.perturb_by_six_delta
  rintro value ⟨imagePoint, himagePoint, rfl⟩
  rcases himagePoint.1.1 with ⟨sourcePoint, hsourcePoint, himageEq⟩
  have himageHeight : imagePoint 2 =
      (sourcePoint 2 - slabCenter) / halfHeight := by
    rw [← himageEq]
    simp [pureWZ2Proposition64TranslatedMap_apply_two, htranslationHeight]
  have hsourceHeight : sourcePoint 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    have hbox := shading_union_subset_axisBox hsourcePoint
    simpa [Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2
  have htargetDistance : |imagePoint 2 - t| ≤ slabRadius := by
    exact abs_le.mpr ⟨by linarith [himagePoint.1.2.1],
      by linarith [himagePoint.1.2.2]⟩
  have hsourceDistance : |sourcePoint 2 - sourceCenter| ≤ sourceDelta := by
    have hheightEq : sourcePoint 2 - sourceCenter =
        halfHeight * (imagePoint 2 - t) := by
      dsimp only [sourceCenter]
      rw [himageHeight]
      field_simp [normalized.halfHeight_pos.ne']
      ring
    rw [hheightEq, abs_mul, abs_of_pos normalized.halfHeight_pos]
    exact (mul_le_mul_of_nonneg_left htargetDistance
      normalized.halfHeight_pos.le).trans hheightBudget
  have hsourceInSlab : sourcePoint ∈
      globalGrainSlab sourceShading.union sourceCenter sourceDelta :=
    ⟨⟨hsourcePoint, ⟨by linarith [abs_le.mp hsourceDistance],
      by linarith [abs_le.mp hsourceDistance]⟩⟩, hsourceHeight⟩
  let sourceValue :=
    inner ℝ sourcePoint (globalGrainDirection (raw.slope (sourcePoint 2)))
  let fixedValue := sourceValue / normalization + shift
  have hfixedValue : fixedValue ∈
      (fun value : ℝ => value + shift) ''
        ((fun value : ℝ => value / normalization) ''
          globalGrainProjection raw.slope
            (globalGrainSlab sourceShading.union sourceCenter sourceDelta)) := by
    exact ⟨sourceValue / normalization,
      ⟨sourceValue, ⟨sourcePoint, hsourceInSlab, rfl⟩, rfl⟩, rfl⟩
  refine ⟨fixedValue, hfixedValue, ?_⟩
  have hprojection :=
    pureWZ2Proposition64TranslatedMap_projection_identity raw.slope
      slabCenter anchorHeight halfHeight normalization translation sourcePoint
      htranslationHeight normalized.halfHeight_pos.ne'
  have hprojection' :
      inner ℝ imagePoint
          (globalGrainDirection (normalized.slope (imagePoint 2))) =
        sourceValue / normalization +
          inner ℝ translation
            (globalGrainDirection (normalized.slope (imagePoint 2))) := by
    rw [← himageEq]
    simpa [normalized.slope_eq, sourceValue] using hprojection
  change |inner ℝ imagePoint
      (globalGrainDirection (normalized.slope (imagePoint 2))) - fixedValue| ≤
        6 * targetBase
  rw [hprojection']
  have hslopeClose : |normalized.slope (imagePoint 2) - normalized.slope t| ≤
      slabRadius := by
    have himageHeightMem := himagePoint.2
    have hlip := pureWZ2Proposition64_normalizedSlope_lipschitzOn
      normalized.normalized himageHeightMem ht
    have hlipReal : |normalized.slope (imagePoint 2) - normalized.slope t| ≤
        |imagePoint 2 - t| := by
      rw [edist_dist, edist_dist] at hlip
      have hdist : dist (normalized.slope (imagePoint 2))
          (normalized.slope t) ≤ dist (imagePoint 2) t := by
        exact (ENNReal.ofReal_le_ofReal_iff (dist_nonneg)).mp
          (by simpa using hlip)
      simpa [Real.dist_eq] using hdist
    exact hlipReal.trans htargetDistance
  have hshiftDifference :
      inner ℝ translation
          (globalGrainDirection (normalized.slope (imagePoint 2))) -
        inner ℝ translation (globalGrainDirection (normalized.slope t)) =
          (normalized.slope (imagePoint 2) - normalized.slope t) *
            translation 1 := by
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    ring
  dsimp only [fixedValue, shift]
  rw [show sourceValue / normalization +
        inner ℝ translation
            (globalGrainDirection (normalized.slope (imagePoint 2))) -
          (sourceValue / normalization +
            inner ℝ translation (globalGrainDirection (normalized.slope t))) =
        inner ℝ translation
            (globalGrainDirection (normalized.slope (imagePoint 2))) -
          inner ℝ translation (globalGrainDirection (normalized.slope t)) by ring,
      hshiftDifference, abs_mul]
  calc
    |normalized.slope (imagePoint 2) - normalized.slope t| * |translation 1| ≤
        slabRadius * 2 := by gcongr
    _ ≤ 6 * targetBase := by simpa [mul_comm] using hprojectionBudget

/-- The full final-grid saturation lies within one target-scale slab of its
exact isotropic-image witness. -/
theorem pureWZ2Proposition64FullIsotropicPaperShading_slabWitness
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
      2 * targetDelta ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      ∀ point ∈ horizontalSlice
        (pureWZ2Proposition64FullIsotropicPaperShading sourceShading center scale
          hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
            hsourceWindow).union z,
        ∃ sourcePoint ∈
          globalGrainSlab
            (pureWZ2Proposition64IsotropicMap center scale ''
              sourceShading.union) z (2 * targetDelta),
          dist point sourcePoint ≤ 2 * targetDelta := by
  intro z hz point hpoint
  let pointSubtype : {point : Point3 // point ∈
      (pureWZ2Proposition64FullIsotropicPaperShading sourceShading center scale
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
          hsourceWindow).union} := ⟨point, hpoint.1⟩
  rcases pureWZ2Proposition64FullIsotropicPaperShading_targetWitness
      sourceShading center scale hsourceDelta htargetDelta htargetDeltaSmall
        hscale hradius hsourceWindow pointSubtype with
    ⟨sourcePoint, hsourcePointDistance⟩
  have hheightDistance : |(sourcePoint : Point3) 2 - z| ≤
      2 * targetDelta := by
    have hcoordinate := PiLp.dist_apply_le (sourcePoint : Point3) point (2 : Fin 3)
    have hcoordinate' :
        dist ((sourcePoint : Point3) 2) z ≤ dist (sourcePoint : Point3) point := by
      simpa [hpoint.2] using hcoordinate
    simpa [Real.dist_eq] using hcoordinate'.trans
      (by simpa [pointSubtype, dist_comm] using hsourcePointDistance)
  have hsourceHeight : (sourcePoint : Point3) 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases sourcePoint.property with ⟨source, hsource, hsourceEq⟩
    have hsourceBall := hsourceWindow hsource
    rw [Metric.mem_closedBall] at hsourceBall
    have hsourceCoord : |source 2 - center 2| ≤ 1 / (2 * scale) := by
      have hcoord := PiLp.dist_apply_le source center (2 : Fin 3)
      simpa [Real.dist_eq] using hcoord.trans hsourceBall
    have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
    have himageCoord : |(sourcePoint : Point3) 2| ≤ 1 / 2 := by
      rw [← hsourceEq]
      simp only [pureWZ2Proposition64IsotropicMap, PiLp.smul_apply,
        PiLp.sub_apply, smul_eq_mul, abs_mul, abs_of_pos hscalePos]
      calc
        scale * |source 2 - center 2| ≤
            scale * (1 / (2 * scale)) := by gcongr
        _ = 1 / 2 := by field_simp [hscalePos.ne']
    exact ⟨by linarith [abs_le.mp himageCoord],
      by linarith [abs_le.mp himageCoord]⟩
  refine ⟨sourcePoint, ⟨⟨sourcePoint.property, ?_⟩, hsourceHeight⟩,
    hsourcePointDistance⟩
  exact ⟨by linarith [abs_le.mp hheightDistance],
    by linarith [abs_le.mp hheightDistance]⟩

/-- Full-saturation projection values are within `6 * targetDelta` of the
height-dependent projection of an exact-image point in the target slab. -/
theorem pureWZ2Proposition64FullIsotropicPaperShading_projection_slab_close
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
      2 * targetDelta ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale)))
    (targetSlope : SlopeFunction) (hnormalized : targetSlope.IsNormalized) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      ∀ value ∈ scalarProjection (globalGrainDirection (targetSlope z))
        (horizontalSlice
          (pureWZ2Proposition64FullIsotropicPaperShading sourceShading center scale
            hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
              hsourceWindow).union z),
        ∃ sourceValue ∈ globalGrainProjection targetSlope
            (globalGrainSlab
              (pureWZ2Proposition64IsotropicMap center scale ''
                sourceShading.union) z (2 * targetDelta)),
          |value - sourceValue| ≤ 6 * targetDelta := by
  intro z hz value hvalue
  rcases hvalue with ⟨point, hpoint, rfl⟩
  rcases pureWZ2Proposition64FullIsotropicPaperShading_slabWitness
      sourceShading center scale hsourceDelta htargetDelta htargetDeltaSmall
        hscale hradius hsourceWindow z hz point hpoint with
    ⟨sourcePoint, hsourcePoint, hdistance⟩
  let sourceValue := inner ℝ sourcePoint
    (globalGrainDirection (targetSlope (sourcePoint 2)))
  refine ⟨sourceValue, ⟨sourcePoint, hsourcePoint, rfl⟩, ?_⟩
  have hsourceHeight := hsourcePoint.2
  have hslopeDistance : |targetSlope z - targetSlope (sourcePoint 2)| ≤
      2 * targetDelta := by
    have hlip := (pureWZ2Proposition64_normalizedSlope_lipschitzOn hnormalized)
      hz hsourceHeight
    have hheight := PiLp.dist_apply_le point sourcePoint (2 : Fin 3)
    have hheight' : dist z (sourcePoint 2) ≤ dist point sourcePoint := by
      simpa [hpoint.2] using hheight
    have hdistHeight : dist z (sourcePoint 2) ≤ 2 * targetDelta :=
      hheight'.trans hdistance
    have hlipReal : dist (targetSlope z) (targetSlope (sourcePoint 2)) ≤
        dist z (sourcePoint 2) := by
      have hdifferentiable : Differentiable ℝ targetSlope :=
        targetSlope.contDiff.differentiable (by norm_num)
      have hderiv : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
          ‖deriv targetSlope t‖ ≤ (1 : ℝ) := by
        intro t ht
        simpa [Real.norm_eq_abs] using (hnormalized t ht).2.1
      have h := Convex.norm_image_sub_le_of_norm_deriv_le
        (fun t _ => hdifferentiable.differentiableAt) hderiv
          (convex_Icc _ _) hz hsourceHeight
      simpa [Real.dist_eq, abs_sub_comm] using h
    rw [Real.dist_eq] at hlipReal
    exact hlipReal.trans hdistHeight
  have hy : |sourcePoint 1| ≤ 1 := by
      have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
      rcases hsourcePoint.1.1 with ⟨source, hsource, hsourceEq⟩
      rw [← hsourceEq]
      have hcoord := PiLp.dist_apply_le source center (1 : Fin 3)
      have hbound : |source 1 - center 1| ≤ 1 / (2 * scale) := by
        simpa [Real.dist_eq, Metric.mem_closedBall] using hcoord.trans (hsourceWindow hsource)
      simp only [pureWZ2Proposition64IsotropicMap, PiLp.smul_apply,
        PiLp.sub_apply, smul_eq_mul, abs_mul, abs_of_pos hscalePos]
      calc
        scale * |source 1 - center 1| ≤ scale * (1 / (2 * scale)) := by gcongr
        _ = 1 / 2 := by field_simp [hscalePos.ne']
        _ ≤ 1 := by norm_num
  have hpointSourceProjection :
      inner ℝ point (globalGrainDirection (targetSlope z)) - sourceValue =
        inner ℝ (point - sourcePoint)
            (globalGrainDirection (targetSlope z)) +
          (targetSlope z - targetSlope (sourcePoint 2)) * sourcePoint 1 := by
    dsimp only [sourceValue]
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    ring
  rw [hpointSourceProjection]
  have hdirectionNorm : ‖globalGrainDirection (targetSlope z)‖ ≤ 2 := by
    have hslope := (hnormalized z hz).1
    have hslopeSq : (targetSlope z) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (targetSlope z - 1),
        sq_nonneg (targetSlope z + 1), abs_le.mp hslope]
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
    constructor
    · norm_num
    · simp [globalGrainDirection, Fin.sum_univ_succ]
      nlinarith
  calc
    |inner ℝ (point - sourcePoint) (globalGrainDirection (targetSlope z)) +
        (targetSlope z - targetSlope (sourcePoint 2)) * sourcePoint 1| ≤
      |inner ℝ (point - sourcePoint)
          (globalGrainDirection (targetSlope z))| +
        |targetSlope z - targetSlope (sourcePoint 2)| * |sourcePoint 1| := by
      simpa [abs_mul] using abs_add_le
        (inner ℝ (point - sourcePoint) (globalGrainDirection (targetSlope z)))
        ((targetSlope z - targetSlope (sourcePoint 2)) * sourcePoint 1)
    _ ≤ dist point sourcePoint * 2 + (2 * targetDelta) * 1 := by
      have hinner := abs_real_inner_le_norm (point - sourcePoint)
        (globalGrainDirection (targetSlope z))
      calc
        _ ≤ ‖point - sourcePoint‖ *
              ‖globalGrainDirection (targetSlope z)‖ +
            |targetSlope z - targetSlope (sourcePoint 2)| * |sourcePoint 1| := by
          gcongr
        _ ≤ dist point sourcePoint * 2 + (2 * targetDelta) * 1 := by
          rw [dist_eq_norm]
          gcongr
    _ ≤ 6 * targetDelta := by linarith

/-- Isotropic transport of a height-dependent slab projection.  The center's
horizontal coordinate makes the transformation only approximately affine;
one target-scale perturbation pays for that variation. -/
theorem pureWZ2Proposition64IsotropicMap_globalSlabAD
    (sourceSlope targetSlope : SlopeFunction)
    (source : Set Point3) (center : Point3)
    {scale targetBase slabRadius alpha : ℝ}
    {C : ENNReal}
    (hscale : 0 < scale) (htargetBase : 0 < targetBase)
    (hslabRadius : 0 < slabRadius)
    (hcenterOne : |center 1| ≤ 1)
    (hsourceSlopeLipschitz :
      LipschitzOnWith 1 sourceSlope (Set.Icc (-1 : ℝ) 1))
    (hsourceHeight : ∀ point ∈ source,
      point 2 ∈ Set.Icc (-1 : ℝ) 1)
    (hslope : ∀ point ∈ source,
      targetSlope (pureWZ2Proposition64IsotropicMap center scale point 2) =
        sourceSlope (point 2))
    (z : ℝ)
    (hsourceAD : ∀ sourceZ ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (globalGrainProjection sourceSlope
          (globalGrainSlab source sourceZ (slabRadius / scale)))
        (targetBase / scale) alpha C)
    (hprojectionBudget : slabRadius ≤ 6 * targetBase) :
    PureWZ2PaperADSet1
      (globalGrainProjection targetSlope
        (globalGrainSlab
          (pureWZ2Proposition64IsotropicMap center scale '' source) z
            slabRadius))
      targetBase alpha (192 * C) := by
  let rawSourceCenter := center 2 + z / scale
  let sourceCenter := max (-1) (min 1 rawSourceCenter)
  have hsourceCenter : sourceCenter ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  let shift := -scale * inner ℝ center
    (globalGrainDirection (sourceSlope sourceCenter))
  have hreference :=
    ((hsourceAD sourceCenter hsourceCenter).image_mul hscale).translate shift
  have hreference' : PureWZ2PaperADSet1
      ((fun value : ℝ => value + shift) ''
        ((fun value : ℝ => scale * value) ''
          globalGrainProjection sourceSlope
            (globalGrainSlab source sourceCenter (slabRadius / scale))))
      targetBase alpha C := by
    convert hreference using 1
    field_simp [hscale.ne']
  apply hreference'.perturb_by_six_delta
  rintro value ⟨targetPoint, htargetPoint, rfl⟩
  rcases htargetPoint.1.1 with ⟨sourcePoint, hsourcePoint, rfl⟩
  have htargetHeight :
      pureWZ2Proposition64IsotropicMap center scale sourcePoint 2 =
        scale * (sourcePoint 2 - center 2) := by
    simp [pureWZ2Proposition64IsotropicMap]
  have hheightDistanceRaw : |sourcePoint 2 - rawSourceCenter| ≤
      slabRadius / scale := by
    have htargetDistance :
        |pureWZ2Proposition64IsotropicMap center scale sourcePoint 2 - z| ≤
          slabRadius := by
      exact abs_le.mpr ⟨by linarith [htargetPoint.1.2.1],
        by linarith [htargetPoint.1.2.2]⟩
    rw [htargetHeight] at htargetDistance
    have hidentity : scale * (sourcePoint 2 - center 2) - z =
        (sourcePoint 2 - rawSourceCenter) * scale := by
      dsimp only [rawSourceCenter]
      field_simp [hscale.ne']
      ring
    rw [hidentity, abs_mul, abs_of_pos hscale] at htargetDistance
    exact (le_div_iff₀ hscale).2 htargetDistance
  have hsourceHeight' := hsourceHeight sourcePoint hsourcePoint
  have hheightDistance : |sourcePoint 2 - sourceCenter| ≤
      slabRadius / scale := by
    by_cases hupper : rawSourceCenter ≤ 1
    · by_cases hlower : -1 ≤ rawSourceCenter
      · have hcenterEq : sourceCenter = rawSourceCenter := by
          dsimp only [sourceCenter]
          rw [min_eq_right hupper, max_eq_right hlower]
        rw [hcenterEq]
        exact hheightDistanceRaw
      · have hsourceLower := hsourceHeight'.1
        have hcenterEq : sourceCenter = -1 := by
          dsimp only [sourceCenter]
          rw [min_eq_right hupper]
          exact max_eq_left (le_of_not_ge hlower)
        rw [hcenterEq]
        rw [abs_of_nonneg (by linarith)]
        linarith [abs_le.mp hheightDistanceRaw]
    · have hsourceUpper := hsourceHeight'.2
      have hcenterEq : sourceCenter = 1 := by
        dsimp only [sourceCenter]
        rw [min_eq_left (le_of_not_ge hupper)]
        norm_num
      rw [hcenterEq]
      rw [abs_of_nonpos (by linarith)]
      linarith [abs_le.mp hheightDistanceRaw]
  have hsourceSlab : sourcePoint ∈
      globalGrainSlab source sourceCenter (slabRadius / scale) :=
    ⟨⟨hsourcePoint, ⟨by linarith [abs_le.mp hheightDistance],
      by linarith [abs_le.mp hheightDistance]⟩⟩, hsourceHeight'⟩
  let sourceValue := inner ℝ sourcePoint
    (globalGrainDirection (sourceSlope (sourcePoint 2)))
  let referenceValue := scale * sourceValue + shift
  have hreferenceValue : referenceValue ∈
      (fun value : ℝ => value + shift) ''
        ((fun value : ℝ => scale * value) ''
          globalGrainProjection sourceSlope
            (globalGrainSlab source sourceCenter (slabRadius / scale))) := by
    exact ⟨scale * sourceValue,
      ⟨sourceValue, ⟨sourcePoint, hsourceSlab, rfl⟩, rfl⟩, rfl⟩
  refine ⟨referenceValue, hreferenceValue, ?_⟩
  change |inner ℝ (pureWZ2Proposition64IsotropicMap center scale sourcePoint)
      (globalGrainDirection
        (targetSlope (pureWZ2Proposition64IsotropicMap center scale sourcePoint 2))) -
      referenceValue| ≤ 6 * targetBase
  rw [hslope sourcePoint hsourcePoint]
  have hslopeClose :
      |sourceSlope (sourcePoint 2) - sourceSlope sourceCenter| ≤
        slabRadius / scale := by
    have hlip := hsourceSlopeLipschitz hsourceHeight' hsourceCenter
    have hlipReal : |sourceSlope (sourcePoint 2) - sourceSlope sourceCenter| ≤
        |sourcePoint 2 - sourceCenter| := by
      rw [edist_dist, edist_dist] at hlip
      have hdist : dist (sourceSlope (sourcePoint 2))
          (sourceSlope sourceCenter) ≤ dist (sourcePoint 2) sourceCenter :=
        (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp (by simpa using hlip)
      simpa [Real.dist_eq] using hdist
    exact hlipReal.trans hheightDistance
  have hprojection :
      inner ℝ (pureWZ2Proposition64IsotropicMap center scale sourcePoint)
          (globalGrainDirection (sourceSlope (sourcePoint 2))) -
        referenceValue =
      scale * center 1 *
        (sourceSlope sourceCenter - sourceSlope (sourcePoint 2)) := by
    dsimp only [referenceValue, sourceValue, shift]
    simp [pureWZ2Proposition64IsotropicMap, inner_smul_left, inner_sub_left,
      globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    ring
  rw [hprojection, abs_mul, abs_mul, abs_of_pos hscale]
  have hslopeClose' : |sourceSlope sourceCenter - sourceSlope (sourcePoint 2)| ≤
      slabRadius / scale := by simpa [abs_sub_comm] using hslopeClose
  calc
    scale * |center 1| *
        |sourceSlope sourceCenter - sourceSlope (sourcePoint 2)| ≤
      scale * 1 * (slabRadius / scale) := by gcongr
    _ = slabRadius := by field_simp [hscale.ne']
    _ ≤ 6 * targetBase := hprojectionBudget

/-- Closed full-saturation AD transport used by the final Proposition 6.4
assembly.  It composes exact affine slab transport, isotropic slab transport,
and the same-grid perturbation of the full cubical saturation. -/
theorem pureWZ2Proposition64FullIsotropicPaperShading_globalAD
    {sourceDelta imageDelta finalDelta sigma rawLoss extensionConstant : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rawConstant slabConstant : ENNReal}
    {raw : PureWZ2RawC2GlobalGrainData
      sourceShading sigma rawConstant rawLoss extensionConstant}
    {slabCenter anchorHeight halfHeight normalization : ℝ}
    (normalized : PureWZ2Proposition64NormalizedData
      raw slabCenter anchorHeight halfHeight normalization)
    (sourceSlabAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (globalGrainProjection raw.slope
          (globalGrainSlab sourceShading.union z sourceDelta))
        sourceDelta (1 - sigma) slabConstant)
    (translation : Point3) (htranslationHeight : translation 2 = 0)
    (htranslationOne : |translation 1| ≤ 2)
    (sourceImageFamily : Kakeya.Streamlined.TubeFamily imageDelta)
    (sourceImageShading : WZ1PaperTubeShading sourceImageFamily)
    (hexactSource : sourceImageShading.union ⊆
      pureWZ2Proposition64TranslatedMap raw.slope slabCenter anchorHeight
        halfHeight normalization translation '' sourceShading.union)
    (center : Point3) (scale : ℝ)
    (hcenterOne : |center 1| ≤ 1)
    (himageDelta : 0 < imageDelta) (hfinalDelta : 0 < finalDelta)
    (hfinalDeltaSmall : finalDelta ≤ 1 / 4) (hscale : 1 ≤ scale)
    (hradius : scale * (6 * imageDelta) +
      2 * finalDelta ≤ 6 * finalDelta)
    (hsourceWindow : sourceImageShading.union ⊆
      Metric.closedBall center (1 / (2 * scale)))
    (hsourceSlab : ∀ point ∈ sourceShading.union,
      point 2 ∈ Set.Icc
        (slabCenter - halfHeight) (slabCenter + halfHeight))
    (hheightBudget :
      halfHeight * (2 * finalDelta / scale) ≤ sourceDelta)
    (hanalyticScale : scale * (sourceDelta / normalization) ≤ finalDelta)
    (hfinalNormalized :
      (pureWZ2Proposition64FinalSlope normalized.slope center scale).IsNormalized) :
    let finalSlope :=
      pureWZ2Proposition64FinalSlope normalized.slope center scale
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (finalSlope z))
          (horizontalSlice
            (pureWZ2Proposition64FullIsotropicPaperShading sourceImageShading
              center scale himageDelta hfinalDelta hfinalDeltaSmall hscale
                hradius hsourceWindow).union z))
        finalDelta (1 - sigma) (7077888 * slabConstant) := by
  dsimp only
  let finalSlope := pureWZ2Proposition64FinalSlope normalized.slope center scale
  intro z hz
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have htargetBase : 0 < finalDelta / scale :=
    div_pos hfinalDelta hscalePos
  have hbase : sourceDelta / normalization ≤ finalDelta / scale := by
    apply (le_div_iff₀ hscalePos).2
    simpa [mul_comm] using hanalyticScale
  have htranslated := pureWZ2Proposition64TranslatedMap_globalSlabAD
    (targetBase := finalDelta / scale)
    (slabRadius := 2 * finalDelta / scale)
    normalized sourceSlabAD translation htranslationHeight htranslationOne
      htargetBase (by positivity) hbase hheightBudget
        (by
          have hnonneg : 0 ≤ finalDelta / scale := htargetBase.le
          have hfourSix : (4 : ℝ) ≤ 6 := by norm_num
          have hmul := mul_le_mul_of_nonneg_left hfourSix hnonneg
          calc
            2 * (2 * finalDelta / scale) =
                4 * (finalDelta / scale) := by ring
            _ ≤ 6 * (finalDelta / scale) := by simpa [mul_comm] using hmul)
  have htranslatedHeight : ∀ point ∈
      pureWZ2Proposition64TranslatedMap raw.slope slabCenter anchorHeight
        halfHeight normalization translation '' sourceShading.union,
      point 2 ∈ Set.Icc (-1 : ℝ) 1 :=
    pureWZ2Proposition64TranslatedMap_image_height_mem raw.slope slabCenter
      anchorHeight normalization normalized.halfHeight_pos translation
        htranslationHeight sourceShading.union hsourceSlab
  have hsourceImageHeight : ∀ point ∈ sourceImageShading.union,
      point 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    intro point hpoint
    exact htranslatedHeight point (hexactSource hpoint)
  have hsourceImageAD : ∀ sourceZ ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (globalGrainProjection normalized.slope
          (globalGrainSlab sourceImageShading.union sourceZ
            (2 * finalDelta / scale)))
        (finalDelta / scale) (1 - sigma) (192 * slabConstant) := by
    intro sourceZ hsourceZ
    exact (htranslated sourceZ hsourceZ).mono (Set.image_mono <| by
      intro point hpoint
      exact ⟨⟨hexactSource hpoint.1.1, hpoint.1.2⟩, hpoint.2⟩)
  have hslopeCompat : ∀ point ∈ sourceImageShading.union,
      finalSlope (pureWZ2Proposition64IsotropicMap center scale point 2) =
        normalized.slope (point 2) := by
    intro point hpoint
    have hpointHeight := hsourceImageHeight point hpoint
    simp only [finalSlope, pureWZ2Proposition64FinalSlope_apply]
    simp [pureWZ2Proposition64IsotropicMap]
    field_simp [hscalePos.ne']
    ring
  have hisotropic := pureWZ2Proposition64IsotropicMap_globalSlabAD
    (targetBase := finalDelta) (slabRadius := 2 * finalDelta)
    normalized.slope finalSlope sourceImageShading.union center hscalePos
      hfinalDelta (by positivity) hcenterOne
      (pureWZ2Proposition64_normalizedSlope_lipschitzOn normalized.normalized)
      hsourceImageHeight hslopeCompat z hsourceImageAD
      (by linarith [hfinalDelta])
  have hclose :=
    pureWZ2Proposition64FullIsotropicPaperShading_projection_slab_close
      sourceImageShading center scale himageDelta hfinalDelta
        hfinalDeltaSmall hscale hradius hsourceWindow finalSlope
        hfinalNormalized z hz
  have hresult := hisotropic.perturb_by_six_delta hclose
  have hconstant :
      (192 : ENNReal) * (192 * (192 * slabConstant)) =
        7077888 * slabConstant := by ring
  rw [← hconstant]
  exact hresult

end Kakeya.Assouad

end
