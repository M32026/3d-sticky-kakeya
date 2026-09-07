import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalNormalizationCenteredFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicTubeParameterForward
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.TubeParameterLineDistance

/-!
# Line geometry for the horizontal-normalized Section-6 family

The final horizontal dilation is useful only in a quantitative window.  Its
scale must be large enough for the plane-map normalization, but the product
of that scale with the selected height length must remain small enough to
keep the transformed supporting lines in the fixed vertical chart.  This
file records the latter condition explicitly; no line-class assertion is
made for an arbitrary positive horizontal scale.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

private theorem point3_norm_le_two_mul_abs_coord_two
    (vector : Point3)
    (hzero : |vector 0| ≤ |vector 2|)
    (hone : |vector 1| ≤ |vector 2|) :
    ‖vector‖ ≤ 2 * |vector 2| := by
  have hnormSq := point3_coord_norm_sq vector
  have hzeroSq : (vector 0) ^ 2 ≤ (vector 2) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 hzero
  have honeSq : (vector 1) ^ 2 ≤ (vector 2) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 hone
  have hnormSqBound : ‖vector‖ ^ 2 ≤ (2 * |vector 2|) ^ 2 := by
    rw [hnormSq]
    calc
      vector 0 ^ 2 + vector 1 ^ 2 + vector 2 ^ 2 ≤
          3 * vector 2 ^ 2 := by linarith
      _ ≤ 4 * vector 2 ^ 2 := by nlinarith [sq_nonneg (vector 2)]
      _ = (2 * |vector 2|) ^ 2 := by nlinarith [sq_abs (vector 2)]
  exact (sq_le_sq₀ (norm_nonneg vector) (by positivity)).mp hnormSqBound

/-- The normalized combined-image direction remains in the fixed vertical
chart when the horizontal dilation is small relative to the inverse selected
height length. -/
theorem pureWZ2HorizontalNormalizedExactDirection_vertical
    (g : SlopeFunction) {c d m lambda : ℝ}
    (anisotropicCenter horizontalCenter : Point3)
    (hcd : c < d) (hdc : d - c ≤ 1)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hlambda : 0 < lambda)
    (hlambdaLength : lambda * (d - c) ≤ 1 / 4)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1)
    {direction : Point3} (hdirectionUnit : ‖direction‖ = 1)
    (hdirectionVertical : (1 / 2 : ℝ) ≤ |direction 2|) :
    (1 / 2 : ℝ) ≤
      |pureWZ2HorizontalNormalizedExactDirection g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda
          direction 2| := by
  let length := d - c
  let image := dPhiLin g c d m direction
  let combined :=
    (pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
      horizontalCenter lambda hcd hm hlambda).linear direction
  have hlengthPos : 0 < length := by
    dsimp only [length]
    linarith
  have hlengthNonneg : 0 ≤ length := hlengthPos.le
  have hlengthOne : length ≤ 1 := by simpa only [length] using hdc
  have hmNonneg : 0 ≤ m := hm.le
  have hlambdaNonneg : 0 ≤ lambda := hlambda.le
  have hcoordZero : |direction 0| ≤ 1 := by
    have h := PiLp.norm_apply_le direction (0 : Fin 3)
    simpa [Real.norm_eq_abs, hdirectionUnit] using h
  have hcoordOne : |direction 1| ≤ 1 := by
    have h := PiLp.norm_apply_le direction (1 : Fin 3)
    simpa [Real.norm_eq_abs, hdirectionUnit] using h
  have himageZero : |image 0| ≤ 2 := by
    have hformula : image 0 =
        direction 0 + g (c + (d - c) / 2) * direction 1 := by
      simp [image, dPhiLin, point3]
    rw [hformula]
    calc
      |direction 0 + g (c + (d - c) / 2) * direction 1| ≤
          |direction 0| +
            |g (c + (d - c) / 2)| * |direction 1| := by
              simpa [abs_mul] using
                abs_add_le (direction 0)
                  (g (c + (d - c) / 2) * direction 1)
      _ ≤ 1 + 1 * 1 := by gcongr
      _ = 2 := by norm_num
  have himageOne : |image 1| ≤ length / 2 := by
    have hformula : image 1 = (m * length / 2) * direction 1 := by
      simp [image, length, dPhiLin, point3]
    rw [hformula, abs_mul, abs_of_nonneg (by positivity : 0 ≤ m * length / 2)]
    calc
      m * length / 2 * |direction 1| ≤
          1 * length / 2 * 1 := by gcongr
      _ = length / 2 := by ring
  have himageTwo : |image 2| = (2 / length) * |direction 2| := by
    have hformula : image 2 = (2 / length) * direction 2 := by
      simp [image, length, dPhiLin, point3]
    rw [hformula, abs_mul, abs_of_pos (by positivity : 0 < 2 / length)]
  have himageTwoLower : 1 / length ≤ |image 2| := by
    rw [himageTwo]
    apply (div_le_iff₀ hlengthPos).2
    have hfactor : (2 / length) * |direction 2| * length =
        2 * |direction 2| := by
      field_simp [hlengthPos.ne']
    rw [hfactor]
    linarith
  have hcombinedZero : |combined 0| ≤ 2 * lambda := by
    have hformula : combined 0 = lambda * image 0 := by
      simp [combined, image,
        pureWZ2HorizontalNormalizedAffineEquiv_linear_apply, point3]
    rw [hformula, abs_mul, abs_of_pos hlambda]
    nlinarith [mul_le_mul_of_nonneg_left himageZero hlambdaNonneg]
  have hcombinedOne : |combined 1| ≤ lambda * (length / 2) := by
    have hformula : combined 1 = lambda * image 1 := by
      simp [combined, image,
        pureWZ2HorizontalNormalizedAffineEquiv_linear_apply, point3]
    rw [hformula, abs_mul, abs_of_pos hlambda]
    exact mul_le_mul_of_nonneg_left himageOne hlambdaNonneg
  have hcombinedTwo : combined 2 = image 2 := by
    simp [combined, image,
      pureWZ2HorizontalNormalizedAffineEquiv_linear_apply, point3]
  have htwoLambdaLe : 2 * lambda ≤ 1 / length := by
    apply (le_div_iff₀ hlengthPos).2
    nlinarith
  have hcombinedZeroLeTwo : |combined 0| ≤ |combined 2| := by
    calc
      |combined 0| ≤ 2 * lambda := hcombinedZero
      _ ≤ 1 / length := htwoLambdaLe
      _ ≤ |image 2| := himageTwoLower
      _ = |combined 2| := by rw [hcombinedTwo]
  have hcombinedTwoOne : 1 ≤ |combined 2| := by
    calc
      1 ≤ 1 / length := by
        apply (le_div_iff₀ hlengthPos).2
        simpa only [one_mul] using hlengthOne
      _ ≤ |image 2| := himageTwoLower
      _ = |combined 2| := by rw [hcombinedTwo]
  have hcombinedOneLeTwo : |combined 1| ≤ |combined 2| := by
    calc
      |combined 1| ≤ lambda * (length / 2) := hcombinedOne
      _ ≤ 1 / 8 := by nlinarith
      _ ≤ 1 := by norm_num
      _ ≤ |combined 2| := hcombinedTwoOne
  have hcombinedNormLe : ‖combined‖ ≤ 2 * |combined 2| :=
    point3_norm_le_two_mul_abs_coord_two combined
      hcombinedZeroLeTwo hcombinedOneLeTwo
  have hcombinedNonzero : combined ≠ 0 := by
    intro hzero
    have : combined 2 = 0 := by rw [hzero]; simp
    rw [this, abs_zero] at hcombinedTwoOne
    norm_num at hcombinedTwoOne
  have hcombinedNormPos : 0 < ‖combined‖ := norm_pos_iff.mpr hcombinedNonzero
  change (1 / 2 : ℝ) ≤ |(‖combined‖⁻¹ : ℝ) * combined 2|
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg combined))]
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hcombinedNormPos).2
  nlinarith

/-- The canonical point of the combined image line at target height zero. -/
def pureWZ2HorizontalNormalizedZeroPoint
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    {sourceDelta : ℝ} (source : Kakeya.DeltaTube sourceDelta) : Point3 :=
  pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter horizontalCenter
    lambda
    (wz1PaperAxisPointAtHeight source
      (c + (d - c) / 2 * (horizontalCenter 2 + 1)))

theorem pureWZ2HorizontalNormalizedZeroPoint_coord_two
    (g : SlopeFunction) {c d m lambda : ℝ}
    (anisotropicCenter horizontalCenter : Point3)
    (hcd : c < d)
    {sourceDelta : ℝ} (source : Kakeya.DeltaTube sourceDelta)
    (hsource : WZ1PaperTubeInLineClass source) :
    pureWZ2HorizontalNormalizedZeroPoint g c d m anisotropicCenter
      horizontalCenter lambda source 2 = 0 := by
  unfold pureWZ2HorizontalNormalizedZeroPoint
  unfold pureWZ2HorizontalNormalizedMap
  simp only [point3_coord2]
  unfold anisotropicCenteredRescalingMap
  simp only [PiLp.sub_apply, point3_coord2, anisotropicRescalingMap_coord]
  rw [wz1PaperAxisPointAtHeight_coord_two hsource]
  field_simp [sub_ne_zero.mpr hcd.ne']
  ring

theorem pureWZ2HorizontalNormalizedZeroPoint_mem_axis
    (g : SlopeFunction) {c d m lambda : ℝ}
    (anisotropicCenter horizontalCenter : Point3)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    {sourceDelta targetDelta : ℝ}
    (source : Kakeya.DeltaTube sourceDelta) :
    pureWZ2HorizontalNormalizedZeroPoint g c d m anisotropicCenter
        horizontalCenter lambda source ∈
      tubeAxisLine
        (pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
          horizontalCenter lambda hcd hm hlambda source :
            Kakeya.DeltaTube targetDelta) := by
  rw [pureWZ2HorizontalNormalizedExactTube_axis]
  exact ⟨wz1PaperAxisPointAtHeight source
      (c + (d - c) / 2 * (horizontalCenter 2 + 1)),
    wz1PaperAxisPointAtHeight_mem_axis source _, rfl⟩

/-- The displayed point is the actual height-zero point of the exact target
line. -/
theorem pureWZ2HorizontalNormalizedExactTube_zeroPoint
    (g : SlopeFunction) {c d m lambda : ℝ}
    (anisotropicCenter horizontalCenter : Point3)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    {sourceDelta targetDelta : ℝ}
    (source : Kakeya.DeltaTube sourceDelta)
    (hsource : WZ1PaperTubeInLineClass source)
    (htargetVertical : (1 / 2 : ℝ) ≤
      |(pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda source :
          Kakeya.DeltaTube targetDelta).direction 2|) :
    wz1TubeAxisZeroPoint
        (pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
          horizontalCenter lambda hcd hm hlambda source :
            Kakeya.DeltaTube targetDelta) =
      pureWZ2HorizontalNormalizedZeroPoint g c d m anisotropicCenter
        horizontalCenter lambda source := by
  apply wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
    htargetVertical
  · exact pureWZ2HorizontalNormalizedZeroPoint_mem_axis
      g anisotropicCenter horizontalCenter hcd hm hlambda source
  · exact pureWZ2HorizontalNormalizedZeroPoint_coord_two
      g anisotropicCenter horizontalCenter hcd source hsource

/-- A sufficient, scale-aware line-class criterion for one exact horizontal
target tube.  The hypotheses on the two zero-height coordinates are kept
explicit because they are supplied by the common spatial recentering step. -/
theorem pureWZ2HorizontalNormalizedExactTube_lineClass
    (g : SlopeFunction) {c d m lambda : ℝ}
    (anisotropicCenter horizontalCenter : Point3)
    (hcd : c < d) (hdc : d - c ≤ 1)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hlambda : 0 < lambda)
    (hlambdaLength : lambda * (d - c) ≤ 1 / 4)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1)
    {sourceDelta targetDelta : ℝ}
    (source : Kakeya.DeltaTube sourceDelta)
    (hsource : WZ1PaperTubeInLineClass source)
    (hzeroX : |pureWZ2HorizontalNormalizedZeroPoint g c d m
      anisotropicCenter horizontalCenter lambda source 0| ≤ 1 / 3)
    (hzeroY : |pureWZ2HorizontalNormalizedZeroPoint g c d m
      anisotropicCenter horizontalCenter lambda source 1| ≤ 1 / 3) :
    WZ1PaperTubeInLineClass
      (pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda source :
          Kakeya.DeltaTube targetDelta) := by
  let target : Kakeya.DeltaTube targetDelta :=
    pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
      horizontalCenter lambda hcd hm hlambda source
  have htargetVertical : (1 / 2 : ℝ) ≤ |target.direction 2| := by
    exact pureWZ2HorizontalNormalizedExactDirection_vertical
      g anisotropicCenter horizontalCenter hcd hdc hm hmOne hlambda
        hlambdaLength hgmid (direction := source.direction)
          source.direction_unit
          hsource.vertical
  have htargetZero : wz1TubeAxisZeroPoint target =
      pureWZ2HorizontalNormalizedZeroPoint g c d m anisotropicCenter
        horizontalCenter lambda source := by
    exact pureWZ2HorizontalNormalizedExactTube_zeroPoint
      g anisotropicCenter horizontalCenter hcd hm hlambda source hsource
        htargetVertical
  refine ⟨?_, ?_, ?_⟩
  · unfold wz1PaperDirection
    split_ifs with hsign
    · rw [abs_of_nonneg hsign] at htargetVertical
      exact htargetVertical
    · have hnegative : target.direction 2 < 0 := lt_of_not_ge hsign
      rw [abs_of_neg hnegative] at htargetVertical
      exact htargetVertical
  · rw [htargetZero]
    exact hzeroX
  · rw [htargetZero]
    exact hzeroY

/-- The one-to-one exact-image family lies in the paper line class under the
same quantitative scale window and spatial recentering bounds. -/
theorem pureWZ2HorizontalNormalizedExactFamily_lineClass
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (g : SlopeFunction) {c d m lambda : ℝ}
    (anisotropicCenter horizontalCenter : Point3)
    (hcd : c < d) (hdc : d - c ≤ 1)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hlambda : 0 < lambda)
    (hlambdaLength : lambda * (d - c) ≤ 1 / 4)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1)
    (hsource : WZ1PaperIsLineClass sourceFamily)
    (hzeroX : ∀ index,
      |pureWZ2HorizontalNormalizedZeroPoint g c d m anisotropicCenter
        horizontalCenter lambda (sourceFamily.tube index) 0| ≤ 1 / 3)
    (hzeroY : ∀ index,
      |pureWZ2HorizontalNormalizedZeroPoint g c d m anisotropicCenter
        horizontalCenter lambda (sourceFamily.tube index) 1| ≤ 1 / 3) :
    WZ1PaperIsLineClass
      (pureWZ2HorizontalNormalizedExactFamily (targetDelta := targetDelta)
        sourceFamily g c d m anisotropicCenter horizontalCenter lambda
          hcd hm hlambda) := by
  intro index
  exact pureWZ2HorizontalNormalizedExactTube_lineClass
    g anisotropicCenter horizontalCenter hcd hdc hm hmOne hlambda
      hlambdaLength hgmid (sourceFamily.tube index) (hsource index)
        (hzeroX index) (hzeroY index)

/-- Canonical centering preserves the line-class conclusion just proved for
the exact one-to-one family. -/
theorem pureWZ2HorizontalNormalizedCenteredFamily_lineClass_of_scale
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (g : SlopeFunction) {c d m lambda : ℝ}
    (anisotropicCenter horizontalCenter : Point3)
    (hcd : c < d) (hdc : d - c ≤ 1)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hlambda : 0 < lambda)
    (hlambdaLength : lambda * (d - c) ≤ 1 / 4)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1)
    (hsource : WZ1PaperIsLineClass sourceFamily)
    (hzeroX : ∀ index,
      |pureWZ2HorizontalNormalizedZeroPoint g c d m anisotropicCenter
        horizontalCenter lambda (sourceFamily.tube index) 0| ≤ 1 / 3)
    (hzeroY : ∀ index,
      |pureWZ2HorizontalNormalizedZeroPoint g c d m anisotropicCenter
        horizontalCenter lambda (sourceFamily.tube index) 1| ≤ 1 / 3) :
    WZ1PaperIsLineClass
      (pureWZ2HorizontalNormalizedCenteredFamily (targetDelta := targetDelta)
        sourceFamily g c d m anisotropicCenter horizontalCenter lambda
          hcd hm hlambda) := by
  apply pureWZ2HorizontalNormalizedCenteredFamily_lineClass
  exact pureWZ2HorizontalNormalizedExactFamily_lineClass sourceFamily g
    anisotropicCenter horizontalCenter hcd hdc hm hmOne hlambda
      hlambdaLength hgmid hsource hzeroX hzeroY

/-- Vertical-chart parameters of the combined triangular and horizontal
map.  The common horizontal translation disappears from pairwise
differences, while the target-height shift contributes the displayed slope
terms to the intercepts. -/
def pureWZ2HorizontalNormalizedTubeParams
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (params : TubeParams) : TubeParams :=
  let raw := anisotropicCenteredTubeParams g c d m anisotropicCenter params
  { a := lambda * (raw.a - horizontalCenter 0 + horizontalCenter 2 * raw.c)
    b := lambda * (raw.b - horizontalCenter 1 + horizontalCenter 2 * raw.d)
    c := lambda * raw.c
    d := lambda * raw.d }

private theorem pureWZ2HorizontalNormalizedMap_axisPointAtTargetHeight
    {sourceDelta : ℝ}
    (g : SlopeFunction) {c d m lambda : ℝ}
    (anisotropicCenter horizontalCenter : Point3)
    (hcd : c < d)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsourceVertical : source.direction (2 : Fin 3) ≠ 0)
    (targetHeight : ℝ) :
    let sourceHeight :=
      c + (d - c) / 2 * (horizontalCenter 2 + targetHeight + 1)
    let point := pureWZ2HorizontalNormalizedMap g c d m
      anisotropicCenter horizontalCenter lambda
        (tubeAxisPointAtHeight source sourceHeight)
    let params := pureWZ2HorizontalNormalizedTubeParams g c d m
      anisotropicCenter horizontalCenter lambda (tubeParamsOfTube source)
    point 0 = params.a + params.c * targetHeight ∧
      point 1 = params.b + params.d * targetHeight ∧
      point 2 = targetHeight := by
  dsimp only
  have hraw := anisotropicCenteredRescalingMap_axisPointAtHeight
    (m := m) g hcd anisotropicCenter source hsourceVertical
      (horizontalCenter 2 + targetHeight)
  rcases hraw with ⟨hzero, hone, htwo⟩
  simp only [pureWZ2HorizontalNormalizedMap, point3_coord0, point3_coord1,
    point3_coord2]
  dsimp only [pureWZ2HorizontalNormalizedTubeParams]
  rw [hzero, hone, htwo]
  exact ⟨by ring, by ring, by ring⟩

/-- Whole-line provenance determines the exact combined target parameters. -/
theorem tubeParamsOfTube_eq_pureWZ2HorizontalNormalized_of_axis_image
    {sourceDelta targetDelta : ℝ}
    (g : SlopeFunction) {c d m lambda : ℝ}
    (anisotropicCenter horizontalCenter : Point3)
    (hcd : c < d)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsourceVertical : source.direction (2 : Fin 3) ≠ 0)
    (target : Kakeya.DeltaTube targetDelta)
    (htargetVertical : target.direction (2 : Fin 3) ≠ 0)
    (haxis : tubeAxisLine target =
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
        horizontalCenter lambda '' tubeAxisLine source) :
    tubeParamsOfTube target =
      pureWZ2HorizontalNormalizedTubeParams g c d m anisotropicCenter
        horizontalCenter lambda (tubeParamsOfTube source) := by
  let sourceHeight : ℝ → ℝ := fun targetHeight =>
    c + (d - c) / 2 * (horizontalCenter 2 + targetHeight + 1)
  let imagePoint : ℝ → Point3 := fun targetHeight =>
    pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
      horizontalCenter lambda
        (tubeAxisPointAtHeight source (sourceHeight targetHeight))
  let params := pureWZ2HorizontalNormalizedTubeParams g c d m
    anisotropicCenter horizontalCenter lambda (tubeParamsOfTube source)
  have himage : ∀ targetHeight,
      imagePoint targetHeight ∈ tubeAxisLine target := by
    intro targetHeight
    rw [haxis]
    exact ⟨tubeAxisPointAtHeight source (sourceHeight targetHeight),
      tubeAxisPointAtHeight_mem source _, rfl⟩
  have hcoords : ∀ targetHeight,
      imagePoint targetHeight 0 = params.a + params.c * targetHeight ∧
      imagePoint targetHeight 1 = params.b + params.d * targetHeight ∧
      imagePoint targetHeight 2 = targetHeight := by
    intro targetHeight
    exact pureWZ2HorizontalNormalizedMap_axisPointAtTargetHeight
      g anisotropicCenter horizontalCenter hcd source hsourceVertical
        targetHeight
  have htargetZero : ∀ targetHeight,
      imagePoint targetHeight 0 = (tubeParamsOfTube target).a +
        (tubeParamsOfTube target).c * imagePoint targetHeight 2 :=
    fun targetHeight =>
      tubeAxisLine_coord_zero target htargetVertical (himage targetHeight)
  have htargetOne : ∀ targetHeight,
      imagePoint targetHeight 1 = (tubeParamsOfTube target).b +
        (tubeParamsOfTube target).d * imagePoint targetHeight 2 :=
    fun targetHeight =>
      tubeAxisLine_coord_one target htargetVertical (himage targetHeight)
  apply TubeParams.ext
  · have h := htargetZero 0
    rw [(hcoords 0).1, (hcoords 0).2.2] at h
    simpa using h.symm
  · have h := htargetOne 0
    rw [(hcoords 0).2.1, (hcoords 0).2.2] at h
    simpa using h.symm
  · have hzero := htargetZero 0
    have hone := htargetZero 1
    rw [(hcoords 0).1, (hcoords 0).2.2] at hzero
    rw [(hcoords 1).1, (hcoords 1).2.2] at hone
    have ha : (tubeParamsOfTube target).a = params.a := by
      simpa using hzero.symm
    rw [ha] at hone
    linarith
  · have hzero := htargetOne 0
    have hone := htargetOne 1
    rw [(hcoords 0).2.1, (hcoords 0).2.2] at hzero
    rw [(hcoords 1).2.1, (hcoords 1).2.2] at hone
    have hb : (tubeParamsOfTube target).b = params.b := by
      simpa using hzero.symm
    rw [hb] at hone
    linarith

private theorem pureWZ2HorizontalNormalizedTubeParams_sub_le
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3)
    {lambda width : ℝ} (hlambda : 0 ≤ lambda)
    (hcenterHeight : |horizontalCenter 2| ≤ 1)
    (first second : TubeParams)
    (ha : |(anisotropicCenteredTubeParams g c d m anisotropicCenter first).a -
      (anisotropicCenteredTubeParams g c d m anisotropicCenter second).a| ≤ width)
    (hb : |(anisotropicCenteredTubeParams g c d m anisotropicCenter first).b -
      (anisotropicCenteredTubeParams g c d m anisotropicCenter second).b| ≤ width)
    (hc : |(anisotropicCenteredTubeParams g c d m anisotropicCenter first).c -
      (anisotropicCenteredTubeParams g c d m anisotropicCenter second).c| ≤ width)
    (hd : |(anisotropicCenteredTubeParams g c d m anisotropicCenter first).d -
      (anisotropicCenteredTubeParams g c d m anisotropicCenter second).d| ≤ width) :
    let firstTarget := pureWZ2HorizontalNormalizedTubeParams g c d m
      anisotropicCenter horizontalCenter lambda first
    let secondTarget := pureWZ2HorizontalNormalizedTubeParams g c d m
      anisotropicCenter horizontalCenter lambda second
    |firstTarget.a - secondTarget.a| ≤ 2 * lambda * width ∧
      |firstTarget.b - secondTarget.b| ≤ 2 * lambda * width ∧
      |firstTarget.c - secondTarget.c| ≤ 2 * lambda * width ∧
      |firstTarget.d - secondTarget.d| ≤ 2 * lambda * width := by
  dsimp only [pureWZ2HorizontalNormalizedTubeParams]
  let firstRaw := anisotropicCenteredTubeParams g c d m anisotropicCenter first
  let secondRaw := anisotropicCenteredTubeParams g c d m anisotropicCenter second
  have hwidth : 0 ≤ width := (abs_nonneg _).trans ha
  have hfirst :
      |lambda * (firstRaw.a - horizontalCenter 0 +
          horizontalCenter 2 * firstRaw.c) -
        lambda * (secondRaw.a - horizontalCenter 0 +
          horizontalCenter 2 * secondRaw.c)| ≤
        2 * lambda * width := by
    rw [show lambda * (firstRaw.a - horizontalCenter 0 +
          horizontalCenter 2 * firstRaw.c) -
        lambda * (secondRaw.a - horizontalCenter 0 +
          horizontalCenter 2 * secondRaw.c) =
      lambda * ((firstRaw.a - secondRaw.a) +
        horizontalCenter 2 * (firstRaw.c - secondRaw.c)) by ring,
      abs_mul, abs_of_nonneg hlambda]
    calc
      lambda * |(firstRaw.a - secondRaw.a) +
          horizontalCenter 2 * (firstRaw.c - secondRaw.c)| ≤
        lambda * (|firstRaw.a - secondRaw.a| +
          |horizontalCenter 2| * |firstRaw.c - secondRaw.c|) := by
            gcongr
            simpa [abs_mul] using abs_add_le
              (firstRaw.a - secondRaw.a)
              (horizontalCenter 2 * (firstRaw.c - secondRaw.c))
      _ ≤ lambda * (width + 1 * width) := by gcongr
      _ = 2 * lambda * width := by ring
  have hsecond :
      |lambda * (firstRaw.b - horizontalCenter 1 +
          horizontalCenter 2 * firstRaw.d) -
        lambda * (secondRaw.b - horizontalCenter 1 +
          horizontalCenter 2 * secondRaw.d)| ≤
        2 * lambda * width := by
    rw [show lambda * (firstRaw.b - horizontalCenter 1 +
          horizontalCenter 2 * firstRaw.d) -
        lambda * (secondRaw.b - horizontalCenter 1 +
          horizontalCenter 2 * secondRaw.d) =
      lambda * ((firstRaw.b - secondRaw.b) +
        horizontalCenter 2 * (firstRaw.d - secondRaw.d)) by ring,
      abs_mul, abs_of_nonneg hlambda]
    calc
      lambda * |(firstRaw.b - secondRaw.b) +
          horizontalCenter 2 * (firstRaw.d - secondRaw.d)| ≤
        lambda * (|firstRaw.b - secondRaw.b| +
          |horizontalCenter 2| * |firstRaw.d - secondRaw.d|) := by
            gcongr
            simpa [abs_mul] using abs_add_le
              (firstRaw.b - secondRaw.b)
              (horizontalCenter 2 * (firstRaw.d - secondRaw.d))
      _ ≤ lambda * (width + 1 * width) := by gcongr
      _ = 2 * lambda * width := by ring
  refine ⟨hfirst, hsecond, ?_, ?_⟩
  · rw [show lambda * firstRaw.c - lambda * secondRaw.c =
      lambda * (firstRaw.c - secondRaw.c) by ring,
      abs_mul, abs_of_nonneg hlambda]
    nlinarith [mul_le_mul_of_nonneg_left hc hlambda]
  · rw [show lambda * firstRaw.d - lambda * secondRaw.d =
      lambda * (firstRaw.d - secondRaw.d) by ring,
      abs_mul, abs_of_nonneg hlambda]
    nlinarith [mul_le_mul_of_nonneg_left hd hlambda]

/-- The paper line metric of exact combined images grows by at most an
explicit multiple of the horizontal dilation. -/
theorem pureWZ2HorizontalNormalizedExactTube_lineDistance_le
    (g : SlopeFunction) {c d m lambda : ℝ}
    (anisotropicCenter horizontalCenter : Point3)
    (hcd : c < d) (hdc : d - c ≤ 1)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hlambda : 0 < lambda)
    (hcenterHeight : |horizontalCenter 2| ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1)
    {firstScale secondScale targetScale : ℝ}
    (first : Kakeya.DeltaTube firstScale)
    (second : Kakeya.DeltaTube secondScale)
    (hfirst : WZ1PaperTubeInLineClass first)
    (hsecond : WZ1PaperTubeInLineClass second)
    (hfirstTarget : WZ1PaperTubeInLineClass
      (pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda first :
          Kakeya.DeltaTube targetScale))
    (hsecondTarget : WZ1PaperTubeInLineClass
      (pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda second :
          Kakeya.DeltaTube targetScale)) :
    wz1PaperLineDistance
        (pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
          horizontalCenter lambda hcd hm hlambda first :
            Kakeya.DeltaTube targetScale)
        (pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
          horizontalCenter lambda hcd hm hlambda second :
            Kakeya.DeltaTube targetScale) ≤
      288 * lambda * wz1PaperLineDistance first second := by
  let distance := wz1PaperLineDistance first second
  have hdistance : 0 ≤ distance := by
    dsimp only [distance, wz1PaperLineDistance]
    exact add_nonneg dist_nonneg
      (InnerProductGeometry.angle_nonneg _ _)
  have hsourceCluster := tubeParamsOfTube_cluster_of_paperLineDistance
    hfirst hsecond (show wz1PaperLineDistance first second ≤ distance from le_rfl)
  have huniform :
      |(tubeParamsOfTube first).a - (tubeParamsOfTube second).a| ≤ 6 * distance ∧
      |(tubeParamsOfTube first).b - (tubeParamsOfTube second).b| ≤ 6 * distance ∧
      |(tubeParamsOfTube first).c - (tubeParamsOfTube second).c| ≤ 6 * distance ∧
      |(tubeParamsOfTube first).d - (tubeParamsOfTube second).d| ≤ 6 * distance := by
    exact ⟨hsourceCluster.1.trans (by nlinarith),
      hsourceCluster.2.1.trans (by nlinarith),
      hsourceCluster.2.2.1, hsourceCluster.2.2.2⟩
  have hmid : |c + (d - c) / 2| ≤ 1 :=
    abs_le.mpr (hsub ⟨by linarith, by linarith⟩)
  have hanisotropic := anisotropicCenteredTubeParams_sub_le
    g c d m anisotropicCenter (6 * distance) hcd hdc hm hmOne
      hgmid hmid (by positivity)
      (tubeParamsOfTube first) (tubeParamsOfTube second)
      huniform.1 huniform.2.1 huniform.2.2.1 huniform.2.2.2
  have hcombined := pureWZ2HorizontalNormalizedTubeParams_sub_le
    g c d m anisotropicCenter horizontalCenter hlambda.le hcenterHeight
      (tubeParamsOfTube first) (tubeParamsOfTube second)
      hanisotropic.1 hanisotropic.2.1 hanisotropic.2.2.1
        hanisotropic.2.2.2
  let firstTarget : Kakeya.DeltaTube targetScale :=
    pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
      horizontalCenter lambda hcd hm hlambda first
  let secondTarget : Kakeya.DeltaTube targetScale :=
    pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
      horizontalCenter lambda hcd hm hlambda second
  have hfirstVertical : first.direction 2 ≠ 0 := by
    intro hzero
    have h := hfirst.vertical
    rw [hzero, abs_zero] at h
    norm_num at h
  have hsecondVertical : second.direction 2 ≠ 0 := by
    intro hzero
    have h := hsecond.vertical
    rw [hzero, abs_zero] at h
    norm_num at h
  have hfirstTargetVertical : firstTarget.direction 2 ≠ 0 := by
    intro hzero
    have h := hfirstTarget.vertical
    rw [hzero, abs_zero] at h
    norm_num at h
  have hsecondTargetVertical : secondTarget.direction 2 ≠ 0 := by
    intro hzero
    have h := hsecondTarget.vertical
    rw [hzero, abs_zero] at h
    norm_num at h
  have hfirstParams : tubeParamsOfTube firstTarget =
      pureWZ2HorizontalNormalizedTubeParams g c d m anisotropicCenter
        horizontalCenter lambda (tubeParamsOfTube first) := by
    apply tubeParamsOfTube_eq_pureWZ2HorizontalNormalized_of_axis_image
      g anisotropicCenter horizontalCenter hcd first hfirstVertical
        firstTarget hfirstTargetVertical
    exact pureWZ2HorizontalNormalizedExactTube_axis
      g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda first
  have hsecondParams : tubeParamsOfTube secondTarget =
      pureWZ2HorizontalNormalizedTubeParams g c d m anisotropicCenter
        horizontalCenter lambda (tubeParamsOfTube second) := by
    apply tubeParamsOfTube_eq_pureWZ2HorizontalNormalized_of_axis_image
      g anisotropicCenter horizontalCenter hcd second hsecondVertical
        secondTarget hsecondTargetVertical
    exact pureWZ2HorizontalNormalizedExactTube_axis
      g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda second
  have htargetCluster :
      |(tubeParamsOfTube firstTarget).a -
          (tubeParamsOfTube secondTarget).a| ≤ 48 * lambda * distance ∧
      |(tubeParamsOfTube firstTarget).b -
          (tubeParamsOfTube secondTarget).b| ≤ 48 * lambda * distance ∧
      |(tubeParamsOfTube firstTarget).c -
          (tubeParamsOfTube secondTarget).c| ≤ 48 * lambda * distance ∧
      |(tubeParamsOfTube firstTarget).d -
          (tubeParamsOfTube secondTarget).d| ≤ 48 * lambda * distance := by
    rw [hfirstParams, hsecondParams]
    convert hcombined using 1 <;> ring
  have hraw := wz1PaperLineDistance_le_of_tubeParams_close
    hfirstTarget hsecondTarget
      (mul_nonneg (mul_nonneg (by norm_num) hlambda.le) hdistance)
      htargetCluster.1 htargetCluster.2.1 htargetCluster.2.2.1
        htargetCluster.2.2.2
  change wz1PaperLineDistance firstTarget secondTarget ≤ _
  convert hraw using 1 <;> ring

/-- Centering the target representatives leaves the preceding line-distance
estimate unchanged. -/
theorem pureWZ2HorizontalNormalizedCenteredTube_lineDistance_le
    (g : SlopeFunction) {c d m lambda : ℝ}
    (anisotropicCenter horizontalCenter : Point3)
    (hcd : c < d) (hdc : d - c ≤ 1)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hlambda : 0 < lambda)
    (hcenterHeight : |horizontalCenter 2| ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1)
    {firstScale secondScale targetScale : ℝ}
    (first : Kakeya.DeltaTube firstScale)
    (second : Kakeya.DeltaTube secondScale)
    (hfirst : WZ1PaperTubeInLineClass first)
    (hsecond : WZ1PaperTubeInLineClass second)
    (hfirstTarget : WZ1PaperTubeInLineClass
      (pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda first :
          Kakeya.DeltaTube targetScale))
    (hsecondTarget : WZ1PaperTubeInLineClass
      (pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda second :
          Kakeya.DeltaTube targetScale)) :
    wz1PaperLineDistance
        (pureWZ2PaperCenteredTube
          (pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
            horizontalCenter lambda hcd hm hlambda first :
              Kakeya.DeltaTube targetScale))
        (pureWZ2PaperCenteredTube
          (pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
            horizontalCenter lambda hcd hm hlambda second :
              Kakeya.DeltaTube targetScale)) ≤
      288 * lambda * wz1PaperLineDistance first second := by
  rw [pureWZ2PaperCenteredTube_lineDistance _ _ hfirstTarget hsecondTarget]
  exact pureWZ2HorizontalNormalizedExactTube_lineDistance_le
    g anisotropicCenter horizontalCenter hcd hdc hm hmOne hlambda
      hcenterHeight hsub hgmid first second hfirst hsecond hfirstTarget
        hsecondTarget

/-- Family-level distortion estimate consumed directly by the generic
representative-parent schedule. -/
theorem pureWZ2HorizontalNormalizedCenteredFamily_lineDistance_le
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (g : SlopeFunction) {c d m lambda : ℝ}
    (anisotropicCenter horizontalCenter : Point3)
    (hcd : c < d) (hdc : d - c ≤ 1)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hlambda : 0 < lambda)
    (hcenterHeight : |horizontalCenter 2| ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1)
    (hsource : WZ1PaperIsLineClass sourceFamily)
    (htarget : WZ1PaperIsLineClass
      (pureWZ2HorizontalNormalizedExactFamily (targetDelta := targetDelta)
        sourceFamily g c d m anisotropicCenter horizontalCenter lambda
          hcd hm hlambda)) :
    ∀ first second,
      wz1PaperLineDistance
          ((pureWZ2HorizontalNormalizedCenteredFamily
            (targetDelta := targetDelta) sourceFamily g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
            first)
          ((pureWZ2HorizontalNormalizedCenteredFamily
            (targetDelta := targetDelta) sourceFamily g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
            second) ≤
        (288 * lambda) *
          wz1PaperLineDistance (sourceFamily.tube first)
            (sourceFamily.tube second) := by
  intro first second
  exact pureWZ2HorizontalNormalizedCenteredTube_lineDistance_le
    g anisotropicCenter horizontalCenter hcd hdc hm hmOne hlambda
      hcenterHeight hsub hgmid (sourceFamily.tube first)
        (sourceFamily.tube second) (hsource first) (hsource second)
          (htarget first) (htarget second)

end Kakeya.Assouad

end
