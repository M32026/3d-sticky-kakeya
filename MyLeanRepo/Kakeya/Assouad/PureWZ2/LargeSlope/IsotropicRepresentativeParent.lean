import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperIsotropicRetubing
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.RepresentativeParentCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.TubeParameterLineDistance
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperCenteredConflictDegree
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CommonContainerTargetTubeParameterClusterBaseFive
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLinePackingCardinality

/-!
# Representative parents after the final positive similarity

The last normalization in Proposition 6.5 is a positive isotropic
similarity.  It preserves supporting directions, but it does not preserve the
ordinary unit-axis-segment carrier.  Consequently the nearby-scale CWA cannot
be transported by a one-to-one carrier inclusion.  This file instead records
the line geometry needed to rebuild the target parents from representatives
of complete source fibers.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

@[simp] theorem pureWZ2IsotropicPaperTube_paperDirection
    {sourceDelta targetDelta : ℝ}
    (center : Point3) (scale : ℝ)
    (source : Kakeya.DeltaTube sourceDelta) :
    wz1PaperDirection
        (pureWZ2IsotropicPaperTube (targetDelta := targetDelta)
          center scale source) =
      wz1PaperDirection source := by
  rfl

/-- Four-parameter action of the final positive similarity on a supporting
line. -/
def pureWZ2IsotropicTubeParams
    (center : Point3) (scale : ℝ) (params : TubeParams) : TubeParams where
  a := scale * (params.a - center 0 + center 2 * params.c)
  b := scale * (params.b - center 1 + center 2 * params.d)
  c := params.c
  d := params.d

@[simp] theorem pureWZ2IsotropicPaperTube_tubeParams
    {sourceDelta targetDelta : ℝ}
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsource : WZ1PaperTubeInLineClass source) :
    tubeParamsOfTube
        (pureWZ2IsotropicPaperTube (targetDelta := targetDelta)
          center scale source) =
      pureWZ2IsotropicTubeParams center scale (tubeParamsOfTube source) := by
  apply TubeParams.ext
  · simp only [tubeParamsOfTube, pureWZ2IsotropicPaperTube,
      pureWZ2IsotropicMap, pureWZ2IsotropicTubeParams, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul]
    have hvertical : source.direction (2 : Fin 3) ≠ 0 := by
      intro hzero
      have h := hsource.vertical
      rw [hzero, abs_zero] at h
      norm_num at h
    field_simp [hvertical]
    ring
  · simp only [tubeParamsOfTube, pureWZ2IsotropicPaperTube,
      pureWZ2IsotropicMap, pureWZ2IsotropicTubeParams, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul]
    have hvertical : source.direction (2 : Fin 3) ≠ 0 := by
      intro hzero
      have h := hsource.vertical
      rw [hzero, abs_zero] at h
      norm_num at h
    field_simp [hvertical]
    ring
  · rfl
  · rfl

/-- The height-zero point of the isotropic image line is the image of the
source axis point at the height of the similarity center. -/
theorem pureWZ2IsotropicPaperTube_zeroPoint
    {sourceDelta targetDelta : ℝ}
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsource : WZ1PaperTubeInLineClass source) :
    wz1TubeAxisZeroPoint
        (pureWZ2IsotropicPaperTube (targetDelta := targetDelta)
          center scale source) =
      pureWZ2IsotropicMap center scale
        (wz1PaperAxisPointAtHeight source (center 2)) := by
  apply wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
    (by simpa [pureWZ2IsotropicPaperTube] using hsource.vertical)
  · rw [pureWZ2IsotropicPaperTube_axis center hscale]
    exact ⟨wz1PaperAxisPointAtHeight source (center 2),
      wz1PaperAxisPointAtHeight_mem_axis source (center 2), rfl⟩
  · simp only [pureWZ2IsotropicMap, PiLp.smul_apply, smul_eq_mul]
    have hsourceTwo :=
      wz1PaperAxisPointAtHeight_coord_two hsource (center 2)
    simp only [PiLp.sub_apply]
    rw [hsourceTwo]
    ring

/-- Exact line-metric formula for a positive similarity.  The angular term
is unchanged, while the distance between the height-zero intersections is
multiplied by the similarity factor. -/
theorem pureWZ2IsotropicPaperTube_lineDistance
    {firstScale secondScale targetScale : ℝ}
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (first : Kakeya.DeltaTube firstScale)
    (second : Kakeya.DeltaTube secondScale)
    (hfirst : WZ1PaperTubeInLineClass first)
    (hsecond : WZ1PaperTubeInLineClass second) :
    wz1PaperLineDistance
        (pureWZ2IsotropicPaperTube (targetDelta := targetScale)
          center scale first)
        (pureWZ2IsotropicPaperTube (targetDelta := targetScale)
          center scale second) =
      scale * dist
          (wz1PaperAxisPointAtHeight first (center 2))
          (wz1PaperAxisPointAtHeight second (center 2)) +
        InnerProductGeometry.angle
          (wz1PaperDirection first) (wz1PaperDirection second) := by
  rw [wz1PaperLineDistance,
    pureWZ2IsotropicPaperTube_zeroPoint center hscale first hfirst,
    pureWZ2IsotropicPaperTube_zeroPoint center hscale second hsecond,
    pureWZ2IsotropicPaperTube_paperDirection,
    pureWZ2IsotropicPaperTube_paperDirection]
  simp only [pureWZ2IsotropicMap, dist_eq_norm]
  have hsub :
      scale • (wz1PaperAxisPointAtHeight first (center 2) - center) -
          scale • (wz1PaperAxisPointAtHeight second (center 2) - center) =
        scale •
          (wz1PaperAxisPointAtHeight first (center 2) -
            wz1PaperAxisPointAtHeight second (center 2)) := by
    module
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hscale]

/-- On a source-height window contained in `[-1,1]`, the paper line metric
of a positive similarity grows by at most `7 * scale`. -/
theorem pureWZ2IsotropicPaperTube_lineDistance_le
    {firstScale secondScale targetScale : ℝ}
    (center : Point3) {scale : ℝ} (hscale : 1 ≤ scale)
    (hcenter : |center 2| ≤ 1)
    (first : Kakeya.DeltaTube firstScale)
    (second : Kakeya.DeltaTube secondScale)
    (hfirst : WZ1PaperTubeInLineClass first)
    (hsecond : WZ1PaperTubeInLineClass second) :
    wz1PaperLineDistance
        (pureWZ2IsotropicPaperTube (targetDelta := targetScale)
          center scale first)
        (pureWZ2IsotropicPaperTube (targetDelta := targetScale)
          center scale second) ≤
      7 * scale * wz1PaperLineDistance first second := by
  rw [pureWZ2IsotropicPaperTube_lineDistance center
    (lt_of_lt_of_le (by norm_num) hscale) first second hfirst hsecond]
  have hposition := wz1PaperAxisPointAtHeight_dist_le
    hfirst hsecond hcenter
  have hangle : InnerProductGeometry.angle
      (wz1PaperDirection first) (wz1PaperDirection second) ≤
        wz1PaperLineDistance first second := by
    unfold wz1PaperLineDistance
    linarith [dist_nonneg
      (x := wz1TubeAxisZeroPoint first)
      (y := wz1TubeAxisZeroPoint second)]
  have hdistanceNonnegative : 0 ≤ wz1PaperLineDistance first second := by
    unfold wz1PaperLineDistance
    exact add_nonneg dist_nonneg
      (InnerProductGeometry.angle_nonneg _ _)
  nlinarith

/-- Conversely, closeness of two isotropic image lines controls the source
paper-line distance.  The loss comes only from changing the height-zero
section from target height zero to source height `center 2`. -/
theorem wz1PaperLineDistance_le_of_isotropicPaperTube_lineDistance
    {firstScale secondScale targetScale radius : ℝ}
    (center : Point3) {scale : ℝ} (hscale : 1 ≤ scale)
    (hcenter : |center 2| ≤ 1)
    (first : Kakeya.DeltaTube firstScale)
    (second : Kakeya.DeltaTube secondScale)
    (hfirst : WZ1PaperTubeInLineClass first)
    (hsecond : WZ1PaperTubeInLineClass second)
    (htargetFirst : WZ1PaperTubeInLineClass
      (pureWZ2IsotropicPaperTube (targetDelta := targetScale)
        center scale first))
    (htargetSecond : WZ1PaperTubeInLineClass
      (pureWZ2IsotropicPaperTube (targetDelta := targetScale)
        center scale second))
    (hdistance : wz1PaperLineDistance
      (pureWZ2IsotropicPaperTube (targetDelta := targetScale)
        center scale first)
      (pureWZ2IsotropicPaperTube (targetDelta := targetScale)
        center scale second) ≤ radius) :
    wz1PaperLineDistance first second ≤ 42 * radius := by
  let targetFirst := pureWZ2IsotropicPaperTube
    (targetDelta := targetScale) center scale first
  let targetSecond := pureWZ2IsotropicPaperTube
    (targetDelta := targetScale) center scale second
  have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
  have hcluster := tubeParamsOfTube_cluster_of_paperLineDistance
    (by simpa only [targetFirst] using htargetFirst)
    (by simpa only [targetSecond] using htargetSecond) hdistance
  rw [pureWZ2IsotropicPaperTube_tubeParams center hscalePos first hfirst,
    pureWZ2IsotropicPaperTube_tubeParams center hscalePos second hsecond]
    at hcluster
  have hradius : 0 ≤ radius := by
    exact (show 0 ≤ wz1PaperLineDistance targetFirst targetSecond by
      unfold wz1PaperLineDistance
      exact add_nonneg dist_nonneg
        (InnerProductGeometry.angle_nonneg _ _)).trans hdistance
  have ha : |(tubeParamsOfTube first).a -
      (tubeParamsOfTube second).a| ≤ 7 * radius := by
    let a := (tubeParamsOfTube first).a - (tubeParamsOfTube second).a
    let c := (tubeParamsOfTube first).c - (tubeParamsOfTube second).c
    have hcombined : |a + center 2 * c| ≤ radius / scale := by
      have hraw := hcluster.1
      change |scale * ((tubeParamsOfTube first).a - center 0 +
          center 2 * (tubeParamsOfTube first).c) -
        scale * ((tubeParamsOfTube second).a - center 0 +
          center 2 * (tubeParamsOfTube second).c)| ≤ radius at hraw
      have heq : scale * ((tubeParamsOfTube first).a - center 0 +
            center 2 * (tubeParamsOfTube first).c) -
          scale * ((tubeParamsOfTube second).a - center 0 +
            center 2 * (tubeParamsOfTube second).c) =
        scale * (a + center 2 * c) := by
          dsimp only [a, c]
          ring
      rw [heq, abs_mul, abs_of_pos hscalePos] at hraw
      exact (le_div_iff₀ hscalePos).2 (by simpa [mul_comm] using hraw)
    have hcBound : |c| ≤ 6 * radius := by
      exact hcluster.2.2.1
    calc
      |(tubeParamsOfTube first).a - (tubeParamsOfTube second).a| =
          |(a + center 2 * c) - center 2 * c| := by
            dsimp only [a, c]
            congr 1
            ring
      _ ≤ |a + center 2 * c| + |center 2 * c| := abs_sub _ _
      _ ≤ radius / scale + 1 * (6 * radius) := by
        gcongr
        rw [abs_mul]
        gcongr
      _ ≤ 7 * radius := by
        have hdiv : radius / scale ≤ radius :=
          (div_le_self hradius hscale)
        linarith
  have hb : |(tubeParamsOfTube first).b -
      (tubeParamsOfTube second).b| ≤ 7 * radius := by
    let b := (tubeParamsOfTube first).b - (tubeParamsOfTube second).b
    let d := (tubeParamsOfTube first).d - (tubeParamsOfTube second).d
    have hcombined : |b + center 2 * d| ≤ radius / scale := by
      have hraw := hcluster.2.1
      change |scale * ((tubeParamsOfTube first).b - center 1 +
          center 2 * (tubeParamsOfTube first).d) -
        scale * ((tubeParamsOfTube second).b - center 1 +
          center 2 * (tubeParamsOfTube second).d)| ≤ radius at hraw
      have heq : scale * ((tubeParamsOfTube first).b - center 1 +
            center 2 * (tubeParamsOfTube first).d) -
          scale * ((tubeParamsOfTube second).b - center 1 +
            center 2 * (tubeParamsOfTube second).d) =
        scale * (b + center 2 * d) := by
          dsimp only [b, d]
          ring
      rw [heq, abs_mul, abs_of_pos hscalePos] at hraw
      exact (le_div_iff₀ hscalePos).2 (by simpa [mul_comm] using hraw)
    have hdBound : |d| ≤ 6 * radius := by
      exact hcluster.2.2.2
    calc
      |(tubeParamsOfTube first).b - (tubeParamsOfTube second).b| =
          |(b + center 2 * d) - center 2 * d| := by
            dsimp only [b, d]
            congr 1
            ring
      _ ≤ |b + center 2 * d| + |center 2 * d| := abs_sub _ _
      _ ≤ radius / scale + 1 * (6 * radius) := by
        gcongr
        rw [abs_mul]
        gcongr
      _ ≤ 7 * radius := by
        have hdiv : radius / scale ≤ radius :=
          (div_le_self hradius hscale)
        linarith
  have hc : |(tubeParamsOfTube first).c -
      (tubeParamsOfTube second).c| ≤ 7 * radius := by
    exact hcluster.2.2.1.trans (by linarith)
  have hd : |(tubeParamsOfTube first).d -
      (tubeParamsOfTube second).d| ≤ 7 * radius := by
    exact hcluster.2.2.2.trans (by linarith)
  have hresult := wz1PaperLineDistance_le_of_tubeParams_close
    hfirst hsecond (by positivity : 0 ≤ 7 * radius) ha hb hc hd
  convert hresult using 1 <;> ring

private theorem pureWZ2PaperCenteredTube_midpoint_norm_le_three_aux
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube) :
    ‖wz2PaperTubeMidpoint (pureWZ2PaperCenteredTube tube)‖ ≤ 3 := by
  rw [pureWZ2PaperCenteredTube_midpoint]
  let point := wz1TubeAxisZeroPoint tube
  have hzero : point 2 = 0 :=
    wz1TubeAxisZeroPoint_coord_two tube hline.vertical
  have hzeroSq : (point 2) ^ 2 = 0 := by rw [hzero]; norm_num
  have hfirstSq : (point 0) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (point 0)) (by norm_num : (0 : ℝ) ≤ 1 / 3)).2
        hline.2.1
  have hsecondSq : (point 1) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (point 1)) (by norm_num : (0 : ℝ) ≤ 1 / 3)).2
        hline.2.2
  have hnormSq := point3_coord_norm_sq point
  rw [hzeroSq] at hnormSq
  nlinarith [norm_nonneg point]

/-- Midpoint-centered isotropic images cannot create an ordinary centered
conflict unless the original source lines were already close.  This is the
backward metric estimate used by the final distinctness cleanup. -/
theorem source_lineDistance_le_of_isotropic_centered_conflict
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (center : Point3) {scale : ℝ} (hscale : 1 ≤ scale)
    (hcenter : |center 2| ≤ 1)
    (htargetDelta : 0 < targetDelta)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hisotropicLine : WZ1PaperIsLineClass
      (pureWZ2IsotropicPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale))
    (htargetLine : WZ1PaperIsLineClass
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale))
    (reference other : Fin sourceFamily.card)
    (hconflict : pureWZ2PaperCenteredConflict
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)
      reference other) :
    wz1PaperLineDistance
        (sourceFamily.tube reference) (sourceFamily.tube other) ≤
      42 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
        targetDelta := by
  let targetFamily := pureWZ2IsotropicCenteredPaperFamily
    (targetDelta := targetDelta) sourceFamily center scale
  have htargetDistance : wz1PaperLineDistance
      (targetFamily.tube reference) (targetFamily.tube other) ≤
        wz2PaperLocalizedDoubledFiberLineDistanceConstant * targetDelta := by
    rcases hconflict with ⟨_hne, hcontain | hcontain⟩
    · exact wz2_paper_localized_centered_doubled_containment_lineDistance_le
        htargetDelta htargetDelta
        (htargetLine reference) (htargetLine other)
        (by
          have hmid : wz2PaperTubeMidpoint (targetFamily.tube reference) =
              wz1TubeAxisZeroPoint
                (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
                  (sourceFamily.tube reference)) := by
            exact pureWZ2PaperCenteredTube_midpoint _
          rw [hmid]
          let point := wz1TubeAxisZeroPoint
            (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
              (sourceFamily.tube reference))
          have hzero : point 2 = 0 :=
            wz1TubeAxisZeroPoint_coord_two _
              (hisotropicLine reference).vertical
          have hnormSq := point3_coord_norm_sq point
          have hfirstSq : (point 0) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
            simpa only [sq_abs] using
              (sq_le_sq₀ (abs_nonneg (point 0))
                (by norm_num : (0 : ℝ) ≤ 1 / 3)).2
                (hisotropicLine reference).2.1
          have hsecondSq : (point 1) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
            simpa only [sq_abs] using
              (sq_le_sq₀ (abs_nonneg (point 1))
                (by norm_num : (0 : ℝ) ≤ 1 / 3)).2
                (hisotropicLine reference).2.2
          rw [hzero] at hnormSq
          nlinarith [norm_nonneg point]) hcontain
    · rw [wz1PaperLineDistance_symm]
      exact wz2_paper_localized_centered_doubled_containment_lineDistance_le
        htargetDelta htargetDelta
        (htargetLine other) (htargetLine reference)
        (by
          have hmid : wz2PaperTubeMidpoint (targetFamily.tube other) =
              wz1TubeAxisZeroPoint
                (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
                  (sourceFamily.tube other)) := by
            exact pureWZ2PaperCenteredTube_midpoint _
          rw [hmid]
          let point := wz1TubeAxisZeroPoint
            (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
              (sourceFamily.tube other))
          have hzero : point 2 = 0 :=
            wz1TubeAxisZeroPoint_coord_two _
              (hisotropicLine other).vertical
          have hnormSq := point3_coord_norm_sq point
          have hfirstSq : (point 0) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
            simpa only [sq_abs] using
              (sq_le_sq₀ (abs_nonneg (point 0))
                (by norm_num : (0 : ℝ) ≤ 1 / 3)).2
                (hisotropicLine other).2.1
          have hsecondSq : (point 1) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
            simpa only [sq_abs] using
              (sq_le_sq₀ (abs_nonneg (point 1))
                (by norm_num : (0 : ℝ) ≤ 1 / 3)).2
                (hisotropicLine other).2.2
          rw [hzero] at hnormSq
          nlinarith [norm_nonneg point]) hcontain
  have hsource := wz1PaperLineDistance_le_of_isotropicPaperTube_lineDistance
    (targetScale := targetDelta)
    (radius := wz2PaperLocalizedDoubledFiberLineDistanceConstant * targetDelta)
    center hscale hcenter (sourceFamily.tube reference)
    (sourceFamily.tube other) (hsourceLine reference) (hsourceLine other)
    (hisotropicLine reference) (hisotropicLine other) (by
    have heq := pureWZ2PaperCenteredTube_lineDistance
      (pureWZ2IsotropicPaperTube center scale
        (sourceFamily.tube reference))
      (pureWZ2IsotropicPaperTube center scale
        (sourceFamily.tube other))
      (hisotropicLine reference) (hisotropicLine other)
    change wz1PaperLineDistance
        (pureWZ2PaperCenteredTube
          (pureWZ2IsotropicPaperTube center scale
            (sourceFamily.tube reference)))
        (pureWZ2PaperCenteredTube
          (pureWZ2IsotropicPaperTube center scale
            (sourceFamily.tube other))) ≤ _ at htargetDistance
    rw [heq] at htargetDistance
    exact htargetDistance)
  simpa only [mul_assoc] using hsource

/-- A source complete fiber has a uniform paper-line diameter.  This uses
only the source line class and the standard bounded-base hypothesis; the
ordinary parent itself need not be in the vertical chart. -/
theorem wz1PaperLineDistance_le_of_same_source_fiber_base_five
    {sourceDelta sourceRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    (sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant)
    (hsourceDeltaRho : sourceDelta ≤ sourceRho)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (first second : Fin sourceFine.card)
    (hsameParent : sourceScale.cover.parent first =
      sourceScale.cover.parent second) :
    wz1PaperLineDistance (sourceFine.tube first) (sourceFine.tube second) ≤
      600000 * sourceRho := by
  by_cases hsourceRhoSmall : sourceRho ≤ 1 / 10000
  swap
  · have haxis :
        dist (wz1TubeAxisZeroPoint (sourceFine.tube first))
            (wz1TubeAxisZeroPoint (sourceFine.tube second)) < 1 := by
      simpa [dist_comm] using paper_axis_dist_lt_one hsourceLine second first
    have hangle := InnerProductGeometry.angle_le_pi
      (wz1PaperDirection (sourceFine.tube first))
      (wz1PaperDirection (sourceFine.tube second))
    have hpi := Real.pi_lt_four
    dsimp only [wz1PaperLineDistance]
    have hrho : 1 / 10000 < sourceRho := lt_of_not_ge hsourceRhoSmall
    nlinarith
  let parent := sourceScale.coarse.tube
    (sourceScale.cover.parent first)
  have hfirstContained :
      (sourceFine.tube first).carrier ⊆ parent.carrier := by
    exact (mem_wz2PaperOrdinaryFullFiberIndices_iff _ _).mp
      (sourceScale.cover.parent_mem_fullFiber first)
  have hsecondContained :
      (sourceFine.tube second).carrier ⊆ parent.carrier := by
    have hmem := sourceScale.cover.parent_mem_fullFiber second
    have hcontain :=
      (mem_wz2PaperOrdinaryFullFiberIndices_iff _ _).mp hmem
    dsimp only [parent]
    rw [hsameParent]
    exact hcontain
  have hcluster := common_container_target_tube_parameter_cluster_base_five
    sourceDelta sourceRho sourceScale.delta_pos hsourceDeltaRho
    hsourceRhoSmall
    (sourceFine.tube first) (sourceFine.tube second)
    (hsourceLine first).vertical (hsourceLine second).vertical
    (hsourceBase first) (hsourceBase second) parent
    hfirstContained hsecondContained
  have hrhoNonnegative : 0 ≤ sourceRho := sourceScale.rho_pos.le
  have hresult := wz1PaperLineDistance_le_of_tubeParams_close
    (hsourceLine first) (hsourceLine second)
    (mul_nonneg (by norm_num) hrhoNonnegative)
    hcluster.1 hcluster.2.1 hcluster.2.2.1 hcluster.2.2.2
  convert hresult using 1 <;> ring

/-- Line class of an isotropic image line, from the explicit target
height-zero bounds used by the final localized construction. -/
theorem pureWZ2IsotropicPaperTube_lineClass
    {sourceDelta targetDelta : ℝ}
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsource : WZ1PaperTubeInLineClass source)
    (hzero : ∀ coordinate : Fin 2,
      |(pureWZ2IsotropicMap center scale
        (wz1PaperAxisPointAtHeight source (center 2))) coordinate.castSucc| ≤
          1 / 3) :
    WZ1PaperTubeInLineClass
      (pureWZ2IsotropicPaperTube (targetDelta := targetDelta)
        center scale source) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using hsource.1
  · rw [pureWZ2IsotropicPaperTube_zeroPoint center hscale source hsource]
    exact hzero 0
  · rw [pureWZ2IsotropicPaperTube_zeroPoint center hscale source hsource]
    exact hzero 1

/-- A canonical centered line-class tube has midpoint in the fixed radius-3
locality window required by the representative-parent construction. -/
theorem pureWZ2PaperCenteredTube_midpoint_norm_le_three
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube) :
    ‖wz2PaperTubeMidpoint (pureWZ2PaperCenteredTube tube)‖ ≤ 3 :=
  pureWZ2PaperCenteredTube_midpoint_norm_le_three_aux tube hline

/-- The midpoint-centered canonicalization is idempotent on a line-class
tube. -/
@[simp] theorem pureWZ2PaperCenteredTube_idempotent
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube) :
    pureWZ2PaperCenteredTube (pureWZ2PaperCenteredTube tube) =
      pureWZ2PaperCenteredTube tube := by
  let centered := pureWZ2PaperCenteredTube tube
  have hcenteredLine : WZ1PaperTubeInLineClass centered :=
    pureWZ2PaperCenteredTube_lineClass hline
  apply pureWZ2PaperCenteredTube_eq_self centered hcenteredLine
  · change 0 ≤ wz1PaperDirection tube 2
    linarith [hline.1]
  · rw [pureWZ2PaperCenteredTube_midpoint]
    exact wz1TubeAxisZeroPoint_coord_two tube hline.vertical

/-- Package the final positive-similarity geometry as one preliminary
representative-parent cover.  The caller supplies the already-cleaned target
ordinary distinctness and the explicit final-scale containment budget. -/
theorem pureWZ2IsotropicRepresentativeParentData
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    (sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant)
    (center : Point3) {scale : ℝ}
    (hscale : 1 ≤ scale) (hcenter : |center 2| ≤ 1)
    (htargetDelta : 0 < targetDelta) (htargetRho : 0 < targetRho)
    (hsourceNonempty : sourceFine.Nonempty)
    (hsourceDeltaRho : sourceDelta ≤ sourceRho)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (hzero : ∀ (index : Fin sourceFine.card) (coordinate : Fin 2),
      |(pureWZ2IsotropicMap center scale
        (wz1PaperAxisPointAtHeight
          (sourceFine.tube index) (center 2))) coordinate.castSucc| ≤ 1 / 3)
    (htargetDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFine center scale))
    (hcontainment :
      (3 / 2 : ℝ) * (4200000 * scale * sourceRho) + targetDelta ≤
        targetRho) :
    PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho)
      (lineBound := 4200000 * scale * sourceRho)
      sourceScale
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFine center scale)
      (Equiv.refl (Fin sourceFine.card)) := by
  let targetFine := pureWZ2IsotropicCenteredPaperFamily
    (targetDelta := targetDelta) sourceFine center scale
  have htargetLine : WZ1PaperIsLineClass targetFine := by
    intro index
    apply pureWZ2PaperCenteredTube_lineClass
    exact pureWZ2IsotropicPaperTube_lineClass center
      (lt_of_lt_of_le (by norm_num) hscale) (sourceFine.tube index)
      (hsourceLine index) (hzero index)
  have htargetCentered : ∀ index,
      pureWZ2PaperCenteredTube (targetFine.tube index) =
        targetFine.tube index := by
    intro index
    change pureWZ2PaperCenteredTube
        (pureWZ2PaperCenteredTube
          (pureWZ2IsotropicPaperTube center scale
            (sourceFine.tube index))) = _
    exact pureWZ2PaperCenteredTube_idempotent _
      (pureWZ2IsotropicPaperTube_lineClass center
        (lt_of_lt_of_le (by norm_num) hscale) (sourceFine.tube index)
        (hsourceLine index) (hzero index))
  refine
    { source_nonempty := hsourceNonempty
      target_delta_pos := htargetDelta
      target_rho_pos := htargetRho
      target_line_class := htargetLine
      target_ordinary_distinct := htargetDistinct
      target_midpoint_local := ?_
      target_packing_distinct := ?_
      target_carrier_subset_relabel := ?_
      common_source_parent_lineDistance := ?_
      containment_budget := hcontainment }
  · intro index
    exact pureWZ2PaperCenteredTube_midpoint_norm_le_three _
      (pureWZ2IsotropicPaperTube_lineClass center
        (lt_of_lt_of_le (by norm_num) hscale) (sourceFine.tube index)
        (hsourceLine index) (hzero index))
  · have hpacking :=
      pureWZ2_centered_ordinaryDistinct_packingFamily_paperDistinct
        htargetDelta htargetLine (by
          intro first second hne
          change ¬(pureWZ2PaperCenteredTube (targetFine.tube first)).carrier ⊆
              wz2PaperCenteredDilatedCarrier 2
                (pureWZ2PaperCenteredTube (targetFine.tube second)) ∧
            ¬(pureWZ2PaperCenteredTube (targetFine.tube second)).carrier ⊆
              wz2PaperCenteredDilatedCarrier 2
                (pureWZ2PaperCenteredTube (targetFine.tube first))
          have hraw := htargetDistinct first second hne
          simpa only [htargetCentered first, htargetCentered second] using hraw)
    intro first second hne
    have hraw := hpacking first second hne
    change (2 / 3 : ℝ) * targetDelta <
      wz1PaperLineDistance
        (wz2PaperRelabelTube (targetFine.tube first))
        (wz2PaperRelabelTube (targetFine.tube second))
    change (2 / 3 : ℝ) * targetDelta <
      wz1PaperLineDistance
        (wz2PaperRelabelTube
          (pureWZ2PaperCenteredTube (targetFine.tube first)))
        (wz2PaperRelabelTube
          (pureWZ2PaperCenteredTube (targetFine.tube second))) at hraw
    rw [wz2PaperRelabelTube_lineDistance_both] at hraw ⊢
    rw [pureWZ2PaperCenteredTube_lineDistance _ _
      (htargetLine first) (htargetLine second)] at hraw
    exact hraw
  · intro rho hrho first second hbudget
    have hcontain := pureWZ2_centered_carrier_subset_relabel_of_lineDistance
      htargetDelta hrho (targetFine.tube first) (targetFine.tube second) hbudget
    change (targetFine.tube first).carrier ⊆
      (wz2PaperRelabelTube (targetFine.tube second)).carrier
    rwa [htargetCentered first, htargetCentered second] at hcontain
  · intro first second hparent
    change wz1PaperLineDistance
        ((pureWZ2PaperCenteredTube
          (pureWZ2IsotropicPaperTube center scale
            (sourceFine.tube first))))
        ((pureWZ2PaperCenteredTube
          (pureWZ2IsotropicPaperTube center scale
            (sourceFine.tube second)))) ≤ _
    rw [pureWZ2PaperCenteredTube_lineDistance _ _
      (pureWZ2IsotropicPaperTube_lineClass center
        (lt_of_lt_of_le (by norm_num) hscale) (sourceFine.tube first)
        (hsourceLine first) (hzero first))
      (pureWZ2IsotropicPaperTube_lineClass center
        (lt_of_lt_of_le (by norm_num) hscale) (sourceFine.tube second)
        (hsourceLine second) (hzero second))]
    calc
      wz1PaperLineDistance
          (pureWZ2IsotropicPaperTube center scale
            (sourceFine.tube first))
          (pureWZ2IsotropicPaperTube center scale
            (sourceFine.tube second))
          ≤ 7 * scale *
              wz1PaperLineDistance
                (sourceFine.tube first) (sourceFine.tube second) :=
        pureWZ2IsotropicPaperTube_lineDistance_le center hscale hcenter
          (sourceFine.tube first) (sourceFine.tube second)
          (hsourceLine first) (hsourceLine second)
      _ ≤ 7 * scale * (600000 * sourceRho) := by
        gcongr
        exact wz1PaperLineDistance_le_of_same_source_fiber_base_five
          sourceScale hsourceDeltaRho hsourceLine hsourceBase first second hparent
      _ = 4200000 * scale * sourceRho := by ring

end Kakeya.Assouad

end
