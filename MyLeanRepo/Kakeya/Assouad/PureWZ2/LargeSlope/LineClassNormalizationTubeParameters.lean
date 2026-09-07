import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LineClassNormalizationFamily

/-!
# Vertical-chart parameters for the line-class normalization

The map `diag(lambda, 1, lambda)` is written with its center explicitly.
This file records its exact action on supporting-line parameters and the
pairwise inverse estimate used when a target parameter cluster is pulled back
to the source family.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The exact vertical-chart parameters of an image under the centered
line-class normalization. -/
def pureWZ2LineClassNormalizationTubeParams
    (center : Point3) (lambda : ℝ) (params : TubeParams) : TubeParams :=
  { a := lambda * (params.a - center 0 + center 2 * params.c)
    b := params.b - center 1 + center 2 * params.d
    c := params.c
    d := params.d / lambda }

/-- At target height `t`, the image of the source axis point at height
`center.z + t / lambda` has the displayed normalized parameters. -/
theorem pureWZ2LineClassNormalizationMap_axisPointAtTargetHeight
    {sourceDelta : ℝ} (center : Point3) {lambda : ℝ} (hlambda : 0 < lambda)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsourceVertical : source.direction (2 : Fin 3) ≠ 0) (t : ℝ) :
    let sourceHeight := center 2 + t / lambda
    let point := pureWZ2LineClassNormalizationMap center lambda
      (tubeAxisPointAtHeight source sourceHeight)
    let params := pureWZ2LineClassNormalizationTubeParams center lambda
      (tubeParamsOfTube source)
    point 0 = params.a + params.c * t ∧
      point 1 = params.b + params.d * t ∧ point 2 = t := by
  dsimp only
  have hzero := tubeAxisPointAtHeight_coord_zero source hsourceVertical
    (center 2 + t / lambda)
  have hone := tubeAxisPointAtHeight_coord_one source hsourceVertical
    (center 2 + t / lambda)
  have htwo := tubeAxisPointAtHeight_coord_two source hsourceVertical
    (center 2 + t / lambda)
  constructor
  · simp only [pureWZ2LineClassNormalizationMap, point3_coord0]
    rw [hzero]
    dsimp only [pureWZ2LineClassNormalizationTubeParams]
    field_simp [hlambda.ne']
    ring
  constructor
  · simp only [pureWZ2LineClassNormalizationMap, point3_coord1]
    rw [hone]
    dsimp only [pureWZ2LineClassNormalizationTubeParams]
    field_simp [hlambda.ne']
    ring
  · simp only [pureWZ2LineClassNormalizationMap, point3_coord2]
    rw [htwo]
    field_simp [hlambda.ne']
    ring

/-- Whole-axis provenance determines the exact target parameters. -/
theorem tubeParamsOfTube_eq_pureWZ2LineClassNormalization_of_axis_image
    {sourceDelta targetDelta : ℝ} (center : Point3) {lambda : ℝ}
    (hlambda : 0 < lambda) (source : Kakeya.DeltaTube sourceDelta)
    (hsourceVertical : source.direction (2 : Fin 3) ≠ 0)
    (target : Kakeya.DeltaTube targetDelta)
    (htargetVertical : target.direction (2 : Fin 3) ≠ 0)
    (haxis : tubeAxisLine target =
      pureWZ2LineClassNormalizationMap center lambda '' tubeAxisLine source) :
    tubeParamsOfTube target =
      pureWZ2LineClassNormalizationTubeParams center lambda
        (tubeParamsOfTube source) := by
  let sourceHeight : ℝ → ℝ := fun t => center 2 + t / lambda
  let imagePoint : ℝ → Point3 := fun t =>
    pureWZ2LineClassNormalizationMap center lambda
      (tubeAxisPointAtHeight source (sourceHeight t))
  let params := pureWZ2LineClassNormalizationTubeParams center lambda
    (tubeParamsOfTube source)
  have himage : ∀ t, imagePoint t ∈ tubeAxisLine target := by
    intro t
    rw [haxis]
    exact ⟨tubeAxisPointAtHeight source (sourceHeight t),
      tubeAxisPointAtHeight_mem source _, rfl⟩
  have hcoords : ∀ t,
      imagePoint t 0 = params.a + params.c * t ∧
        imagePoint t 1 = params.b + params.d * t ∧ imagePoint t 2 = t := by
    intro t
    exact pureWZ2LineClassNormalizationMap_axisPointAtTargetHeight
      center hlambda source hsourceVertical t
  have htargetZero : ∀ t, imagePoint t 0 = (tubeParamsOfTube target).a +
      (tubeParamsOfTube target).c * imagePoint t 2 :=
    fun t => tubeAxisLine_coord_zero target htargetVertical (himage t)
  have htargetOne : ∀ t, imagePoint t 1 = (tubeParamsOfTube target).b +
      (tubeParamsOfTube target).d * imagePoint t 2 :=
    fun t => tubeAxisLine_coord_one target htargetVertical (himage t)
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

/-- Pairwise differences: the two horizontal center coordinates cancel, and
the height center appears only in the two intercept differences. -/
theorem pureWZ2LineClassNormalizationTubeParams_sub_eq
    (center : Point3) (lambda : ℝ) (first second : TubeParams) :
    let firstTarget := pureWZ2LineClassNormalizationTubeParams center lambda first
    let secondTarget := pureWZ2LineClassNormalizationTubeParams center lambda second
    firstTarget.a - secondTarget.a = lambda *
        ((first.a - second.a) + center 2 * (first.c - second.c)) ∧
      firstTarget.b - secondTarget.b =
        (first.b - second.b) + center 2 * (first.d - second.d) ∧
      firstTarget.c - secondTarget.c = first.c - second.c ∧
      firstTarget.d - secondTarget.d = (first.d - second.d) / lambda := by
  dsimp only [pureWZ2LineClassNormalizationTubeParams]
  exact ⟨by ring, by ring, by ring, by ring⟩

/-- A target four-parameter cluster pulls back to a source cluster.  The
sharp coordinate bounds retain `|center.z|`; under the usual normalized
height and dilation hypotheses each is at most `2 * lambda * radius`. -/
theorem pureWZ2LineClassNormalizationTubeParams_inverse_cluster
    (center : Point3) {lambda radius : ℝ} (hlambda : 0 < lambda)
    (first second : TubeParams)
    (ha : |(pureWZ2LineClassNormalizationTubeParams center lambda first).a -
      (pureWZ2LineClassNormalizationTubeParams center lambda second).a| ≤ radius)
    (hb : |(pureWZ2LineClassNormalizationTubeParams center lambda first).b -
      (pureWZ2LineClassNormalizationTubeParams center lambda second).b| ≤ radius)
    (hc : |(pureWZ2LineClassNormalizationTubeParams center lambda first).c -
      (pureWZ2LineClassNormalizationTubeParams center lambda second).c| ≤ radius)
    (hd : |(pureWZ2LineClassNormalizationTubeParams center lambda first).d -
      (pureWZ2LineClassNormalizationTubeParams center lambda second).d| ≤ radius) :
    |first.a - second.a| ≤ radius / lambda + |center 2| * radius ∧
      |first.b - second.b| ≤ radius + |center 2| * (lambda * radius) ∧
      |first.c - second.c| ≤ radius ∧
      |first.d - second.d| ≤ lambda * radius := by
  have hradius : 0 ≤ radius := (abs_nonneg _).trans ha
  have hdiff := pureWZ2LineClassNormalizationTubeParams_sub_eq
    center lambda first second
  rw [hdiff.1] at ha
  rw [hdiff.2.1] at hb
  rw [hdiff.2.2.1] at hc
  rw [hdiff.2.2.2] at hd
  have hscaledA : |(first.a - second.a) + center 2 *
      (first.c - second.c)| ≤ radius / lambda := by
    rw [abs_mul, abs_of_pos hlambda] at ha
    rw [mul_comm] at ha
    exact (le_div_iff₀ hlambda).mpr ha
  have hscaledD : |first.d - second.d| ≤ lambda * radius := by
    rw [abs_div] at hd
    have : |first.d - second.d| / lambda ≤ radius := by
      simpa [abs_of_pos hlambda] using hd
    simpa [mul_comm] using (div_le_iff₀ hlambda).mp this
  refine ⟨?_, ?_, hc, hscaledD⟩
  · rw [show first.a - second.a =
      ((first.a - second.a) + center 2 * (first.c - second.c)) -
        center 2 * (first.c - second.c) by ring]
    calc
      _ ≤ |(first.a - second.a) + center 2 * (first.c - second.c)| +
          |center 2 * (first.c - second.c)| := by
            simpa using abs_sub_le
              ((first.a - second.a) + center 2 * (first.c - second.c))
              0 (center 2 * (first.c - second.c))
      _ ≤ radius / lambda + |center 2| * radius := by
        rw [abs_mul]
        gcongr
  · rw [show first.b - second.b =
      ((first.b - second.b) + center 2 * (first.d - second.d)) -
        center 2 * (first.d - second.d) by ring]
    calc
      _ ≤ |(first.b - second.b) + center 2 * (first.d - second.d)| +
          |center 2 * (first.d - second.d)| := by
            simpa using abs_sub_le
              ((first.b - second.b) + center 2 * (first.d - second.d))
              0 (center 2 * (first.d - second.d))
      _ ≤ radius + |center 2| * (lambda * radius) := by
        rw [abs_mul]
        gcongr

/-- Uniform form of the inverse cluster bound on a normalized height window. -/
theorem pureWZ2LineClassNormalizationTubeParams_inverse_cluster_le
    (center : Point3) {lambda radius : ℝ} (hlambda : 1 ≤ lambda)
    (hcenterHeight : |center 2| ≤ 1) (first second : TubeParams)
    (ha : |(pureWZ2LineClassNormalizationTubeParams center lambda first).a -
      (pureWZ2LineClassNormalizationTubeParams center lambda second).a| ≤ radius)
    (hb : |(pureWZ2LineClassNormalizationTubeParams center lambda first).b -
      (pureWZ2LineClassNormalizationTubeParams center lambda second).b| ≤ radius)
    (hc : |(pureWZ2LineClassNormalizationTubeParams center lambda first).c -
      (pureWZ2LineClassNormalizationTubeParams center lambda second).c| ≤ radius)
    (hd : |(pureWZ2LineClassNormalizationTubeParams center lambda first).d -
      (pureWZ2LineClassNormalizationTubeParams center lambda second).d| ≤ radius) :
    |first.a - second.a| ≤ 2 * lambda * radius ∧
      |first.b - second.b| ≤ 2 * lambda * radius ∧
      |first.c - second.c| ≤ 2 * lambda * radius ∧
      |first.d - second.d| ≤ 2 * lambda * radius := by
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  have hinverse := pureWZ2LineClassNormalizationTubeParams_inverse_cluster
    center hlambdaPos first second ha hb hc hd
  have hradius : 0 ≤ radius := (abs_nonneg _).trans ha
  have hsquare : 1 ≤ lambda * lambda := by
    nlinarith [mul_self_nonneg (lambda - 1)]
  have hinvle : radius / lambda ≤ lambda * radius := by
    apply (div_le_iff₀ hlambdaPos).mpr
    nlinarith
  have honele : radius ≤ lambda * radius := by nlinarith
  have hcenterRadius : |center 2| * radius ≤ radius := by
    simpa using mul_le_mul_of_nonneg_right hcenterHeight hradius
  have hcenterLambdaRadius : |center 2| * (lambda * radius) ≤
      lambda * radius := by
    have hlambdaRadius : 0 ≤ lambda * radius :=
      mul_nonneg hlambdaPos.le hradius
    simpa using mul_le_mul_of_nonneg_right hcenterHeight hlambdaRadius
  refine ⟨hinverse.1.trans ?_, hinverse.2.1.trans ?_, hinverse.2.2.1.trans ?_,
    hinverse.2.2.2.trans ?_⟩
  · calc
      radius / lambda + |center 2| * radius ≤ lambda * radius + radius := by
        exact add_le_add hinvle hcenterRadius
      _ ≤ 2 * lambda * radius := by nlinarith
  · calc
      radius + |center 2| * (lambda * radius) ≤
          lambda * radius + lambda * radius := by
            exact add_le_add honele hcenterLambdaRadius
      _ ≤ 2 * lambda * radius := by nlinarith
  · nlinarith
  · nlinarith

end Kakeya.Assouad
