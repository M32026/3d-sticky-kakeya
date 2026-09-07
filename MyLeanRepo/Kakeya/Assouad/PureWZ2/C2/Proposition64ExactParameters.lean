import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64IsotropicParameters

/-!
# Vertical-line parameters under the exact Proposition 6.4 map

The exact map is upper triangular in the vertical chart.  This module records
its action on the four line parameters and the inverse cluster bound used by
the paper's essentially-distinct cleanup.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Four vertical-line parameters after the exact translated `Phi` map. -/
def pureWZ2Proposition64ExactTubeParams
    (anchorSlope slabCenter halfHeight normalization : ℝ)
    (translation : Point3) (params : TubeParams) : TubeParams where
  a := ((params.a + params.c * slabCenter) +
      anchorSlope * (params.b + params.d * slabCenter)) / normalization +
    translation 0
  b := params.b + params.d * slabCenter + translation 1
  c := halfHeight * (params.c + anchorSlope * params.d) / normalization
  d := halfHeight * params.d

/-- The exact image of a source axis point at source height
`slabCenter + halfHeight * z` has the coordinates encoded by the transformed
parameters. -/
theorem pureWZ2Proposition64TranslatedMap_axisPointAtTargetHeight
    {sourceDelta : ℝ} (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3) (htranslationHeight : translation 2 = 0)
    (hhalfHeight : 0 < halfHeight)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceVertical : sourceTube.direction 2 ≠ 0) (z : ℝ) :
    let sourceHeight := slabCenter + halfHeight * z
    let imagePoint := pureWZ2Proposition64TranslatedMap g slabCenter
      anchorHeight halfHeight normalization translation
        (tubeAxisPointAtHeight sourceTube sourceHeight)
    let params := pureWZ2Proposition64ExactTubeParams (g anchorHeight)
      slabCenter halfHeight normalization translation
        (tubeParamsOfTube sourceTube)
    imagePoint 0 = params.a + params.c * z ∧
      imagePoint 1 = params.b + params.d * z ∧ imagePoint 2 = z := by
  dsimp only
  have hsourceZero := tubeAxisPointAtHeight_coord_zero sourceTube
    hsourceVertical (slabCenter + halfHeight * z)
  have hsourceOne := tubeAxisPointAtHeight_coord_one sourceTube
    hsourceVertical (slabCenter + halfHeight * z)
  have hsourceTwo := tubeAxisPointAtHeight_coord_two sourceTube
    hsourceVertical (slabCenter + halfHeight * z)
  constructor
  · simp only [pureWZ2Proposition64TranslatedMap, PiLp.add_apply,
      pureWZ2Proposition64Map_apply_zero]
    rw [hsourceZero, hsourceOne]
    simp [pureWZ2Proposition64ExactTubeParams]
    ring
  constructor
  · simp only [pureWZ2Proposition64TranslatedMap, PiLp.add_apply,
      pureWZ2Proposition64Map_apply_one]
    rw [hsourceOne]
    simp [pureWZ2Proposition64ExactTubeParams]
    ring
  · rw [pureWZ2Proposition64TranslatedMap_apply_two, hsourceTwo,
      htranslationHeight]
    field_simp [hhalfHeight.ne']
    ring

/-- Whole-line provenance determines the exact target line parameters. -/
theorem tubeParamsOfTube_eq_proposition64Exact_of_axis_image
    {sourceDelta targetDelta : ℝ} (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (htranslationHeight : translation 2 = 0)
    (hhalfHeight : 0 < halfHeight)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceVertical : sourceTube.direction 2 ≠ 0)
    (targetTube : Kakeya.DeltaTube targetDelta)
    (htargetVertical : targetTube.direction 2 ≠ 0)
    (haxis : tubeAxisLine targetTube =
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation '' tubeAxisLine sourceTube) :
    tubeParamsOfTube targetTube =
      pureWZ2Proposition64ExactTubeParams (g anchorHeight) slabCenter
        halfHeight normalization translation (tubeParamsOfTube sourceTube) := by
  let sourceHeight : ℝ → ℝ := fun z => slabCenter + halfHeight * z
  let imagePoint : ℝ → Point3 := fun z =>
    pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
      normalization translation (tubeAxisPointAtHeight sourceTube (sourceHeight z))
  let params := pureWZ2Proposition64ExactTubeParams (g anchorHeight)
    slabCenter halfHeight normalization translation (tubeParamsOfTube sourceTube)
  have himage : ∀ z, imagePoint z ∈ tubeAxisLine targetTube := by
    intro z
    rw [haxis]
    exact ⟨tubeAxisPointAtHeight sourceTube (sourceHeight z),
      tubeAxisPointAtHeight_mem sourceTube _, rfl⟩
  have hcoords : ∀ z, imagePoint z 0 = params.a + params.c * z ∧
      imagePoint z 1 = params.b + params.d * z ∧ imagePoint z 2 = z := by
    intro z
    exact pureWZ2Proposition64TranslatedMap_axisPointAtTargetHeight g
      slabCenter anchorHeight halfHeight normalization translation
      htranslationHeight hhalfHeight sourceTube hsourceVertical z
  have htargetZero : ∀ z, imagePoint z 0 =
      (tubeParamsOfTube targetTube).a +
        (tubeParamsOfTube targetTube).c * imagePoint z 2 :=
    fun z => tubeAxisLine_coord_zero targetTube htargetVertical (himage z)
  have htargetOne : ∀ z, imagePoint z 1 =
      (tubeParamsOfTube targetTube).b +
        (tubeParamsOfTube targetTube).d * imagePoint z 2 :=
    fun z => tubeAxisLine_coord_one targetTube htargetVertical (himage z)
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
    have ha : (tubeParamsOfTube targetTube).a = params.a := by
      simpa using hzero.symm
    rw [ha] at hone
    linarith
  · have hzero := htargetOne 0
    have hone := htargetOne 1
    rw [(hcoords 0).2.1, (hcoords 0).2.2] at hzero
    rw [(hcoords 1).2.1, (hcoords 1).2.2] at hone
    have hb : (tubeParamsOfTube targetTube).b = params.b := by
      simpa using hzero.symm
    rw [hb] at hone
    linarith

/-- Differences of exact target parameters.  The common translation cancels
and only the upper-triangular linear part remains. -/
theorem pureWZ2Proposition64ExactTubeParams_sub_eq
    (anchorSlope slabCenter halfHeight normalization : ℝ)
    (translation : Point3) (first second : TubeParams) :
    let targetFirst := pureWZ2Proposition64ExactTubeParams anchorSlope
      slabCenter halfHeight normalization translation first
    let targetSecond := pureWZ2Proposition64ExactTubeParams anchorSlope
      slabCenter halfHeight normalization translation second
    targetFirst.a - targetSecond.a =
        ((first.a - second.a) + slabCenter * (first.c - second.c) +
          anchorSlope * ((first.b - second.b) +
            slabCenter * (first.d - second.d))) / normalization ∧
      targetFirst.b - targetSecond.b =
        (first.b - second.b) + slabCenter * (first.d - second.d) ∧
      targetFirst.c - targetSecond.c =
        halfHeight * ((first.c - second.c) +
          anchorSlope * (first.d - second.d)) / normalization ∧
      targetFirst.d - targetSecond.d =
        halfHeight * (first.d - second.d) := by
  dsimp only [pureWZ2Proposition64ExactTubeParams]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Invert a four-parameter cluster through the exact translated `Phi` map.
The bound is deliberately polynomial and auditable; all singular dependence
is through `normalization / halfHeight`, as prescribed by the short slab. -/
theorem pureWZ2Proposition64ExactTubeParams_inverse_cluster
    {anchorSlope slabCenter halfHeight normalization radius : ℝ}
    (translation : Point3)
    (hanchorSlope : |anchorSlope| ≤ 8) (hslabCenter : |slabCenter| ≤ 1)
    (hhalfHeight : 0 < halfHeight) (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 9 ≤ normalization)
    (first second : TubeParams)
    (ha : |(pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
        halfHeight normalization translation first).a -
      (pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
        halfHeight normalization translation second).a| ≤ radius)
    (hb : |(pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
        halfHeight normalization translation first).b -
      (pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
        halfHeight normalization translation second).b| ≤ radius)
    (hc : |(pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
        halfHeight normalization translation first).c -
      (pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
        halfHeight normalization translation second).c| ≤ radius)
    (hd : |(pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
        halfHeight normalization translation first).d -
      (pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
        halfHeight normalization translation second).d| ≤ radius) :
    |first.a - second.a| ≤ 20 * normalization * radius / halfHeight ∧
      |first.b - second.b| ≤ 2 * radius / halfHeight ∧
      |first.c - second.c| ≤ 10 * normalization * radius / halfHeight ∧
      |first.d - second.d| ≤ radius / halfHeight := by
  have hnormalizationPos : 0 < normalization := by linarith
  have hdiff := pureWZ2Proposition64ExactTubeParams_sub_eq
    anchorSlope slabCenter halfHeight normalization translation first second
  have hd' : |first.d - second.d| ≤ radius / halfHeight := by
    rw [hdiff.2.2.2, abs_mul, abs_of_pos hhalfHeight] at hd
    exact (le_div_iff₀ hhalfHeight).2 (by simpa [mul_comm] using hd)
  have hb' : |first.b - second.b| ≤ 2 * radius / halfHeight := by
    rw [hdiff.2.1] at hb
    have hsplit : first.b - second.b =
        ((first.b - second.b) + slabCenter * (first.d - second.d)) -
          slabCenter * (first.d - second.d) := by ring
    rw [hsplit]
    calc
      |_ - _| ≤ |(first.b - second.b) +
          slabCenter * (first.d - second.d)| +
          |slabCenter * (first.d - second.d)| := abs_sub _ _
      _ ≤ radius + 1 * (radius / halfHeight) := by
        rw [abs_mul]
        gcongr
      _ ≤ 2 * radius / halfHeight := by
        have hradius : 0 ≤ radius := (abs_nonneg _).trans hd
        have hradiusLe : radius ≤ radius / halfHeight := by
          apply (le_div_iff₀ hhalfHeight).2
          exact mul_le_of_le_one_right hradius hhalfHeightOne
        calc
          radius + 1 * (radius / halfHeight) ≤
              radius / halfHeight + radius / halfHeight := by
            exact add_le_add hradiusLe (by simp)
          _ = 2 * radius / halfHeight := by ring
  have hc' : |first.c - second.c| ≤
      10 * normalization * radius / halfHeight := by
    rw [hdiff.2.2.1, abs_div, abs_mul, abs_of_pos hhalfHeight,
      abs_of_pos hnormalizationPos] at hc
    have hinner : |(first.c - second.c) +
        anchorSlope * (first.d - second.d)| ≤
          normalization * radius / halfHeight := by
      apply (le_div_iff₀ hhalfHeight).2
      have hc' := (div_le_iff₀ hnormalizationPos).1 hc
      simpa [mul_assoc, mul_comm, mul_left_comm] using hc'
    have hsplit : first.c - second.c =
        ((first.c - second.c) + anchorSlope * (first.d - second.d)) -
          anchorSlope * (first.d - second.d) := by ring
    rw [hsplit]
    calc
      |_ - _| ≤ |(first.c - second.c) +
          anchorSlope * (first.d - second.d)| +
          |anchorSlope * (first.d - second.d)| := abs_sub _ _
      _ ≤ normalization * radius / halfHeight +
          8 * (radius / halfHeight) := by
        rw [abs_mul]
        gcongr
      _ ≤ 10 * normalization * radius / halfHeight := by
        have hradius : 0 ≤ radius := (abs_nonneg _).trans hd
        have hratio : 0 ≤ radius / halfHeight := div_nonneg hradius hhalfHeight.le
        have hcoefficient : 8 ≤ 9 * normalization := by nlinarith
        have hmul := mul_le_mul_of_nonneg_right hcoefficient hratio
        calc
          normalization * radius / halfHeight + 8 * (radius / halfHeight) ≤
              normalization * radius / halfHeight +
                9 * normalization * (radius / halfHeight) := by gcongr
          _ = 10 * normalization * radius / halfHeight := by ring
  have ha' : |first.a - second.a| ≤
      20 * normalization * radius / halfHeight := by
    rw [hdiff.1, abs_div, abs_of_pos hnormalizationPos] at ha
    have hsum : |(first.a - second.a) +
        slabCenter * (first.c - second.c) +
        anchorSlope * ((first.b - second.b) +
          slabCenter * (first.d - second.d))| ≤ normalization * radius := by
      simpa [mul_comm] using (div_le_iff₀ hnormalizationPos).1 ha
    have hsplit : first.a - second.a =
        ((first.a - second.a) + slabCenter * (first.c - second.c) +
          anchorSlope * ((first.b - second.b) +
            slabCenter * (first.d - second.d))) -
        slabCenter * (first.c - second.c) -
        anchorSlope * ((first.b - second.b) +
          slabCenter * (first.d - second.d)) := by ring
    rw [hsplit]
    calc
      |_ - _ - _| ≤
          |(first.a - second.a) + slabCenter * (first.c - second.c) +
            anchorSlope * ((first.b - second.b) +
              slabCenter * (first.d - second.d))| +
          |slabCenter * (first.c - second.c)| +
          |anchorSlope * ((first.b - second.b) +
            slabCenter * (first.d - second.d))| := by
        exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ normalization * radius +
          1 * (10 * normalization * radius / halfHeight) +
          8 * radius := by
        rw [abs_mul, abs_mul]
        gcongr
        simpa [hdiff.2.1] using hb
      _ ≤ 20 * normalization * radius / halfHeight := by
        have hradius : 0 ≤ radius := (abs_nonneg _).trans hd
        have hratio : 0 ≤ radius / halfHeight := div_nonneg hradius hhalfHeight.le
        have hradiusLe : radius ≤ radius / halfHeight := by
          apply (le_div_iff₀ hhalfHeight).2
          exact mul_le_of_le_one_right hradius hhalfHeightOne
        have hnormalizationRatio :
            normalization * radius ≤ normalization * (radius / halfHeight) :=
          mul_le_mul_of_nonneg_left hradiusLe hnormalizationPos.le
        have heighthRatio : 8 * radius ≤
            9 * normalization * (radius / halfHeight) := by
          have hcoefficient : (8 : ℝ) ≤ 9 * normalization := by nlinarith
          exact (mul_le_mul_of_nonneg_left hradiusLe (by norm_num)).trans
            (mul_le_mul_of_nonneg_right hcoefficient hratio)
        calc
          normalization * radius +
              1 * (10 * normalization * radius / halfHeight) +
              8 * radius ≤
            normalization * (radius / halfHeight) +
              10 * normalization * radius / halfHeight +
              9 * normalization * (radius / halfHeight) := by
                have hmiddle : 1 * (10 * normalization * radius / halfHeight) ≤
                    10 * normalization * radius / halfHeight := by simp
                exact add_le_add
                  (add_le_add hnormalizationRatio hmiddle) heighthRatio
          _ = 20 * normalization * radius / halfHeight := by
            field_simp [hhalfHeight.ne']
            ring
  exact ⟨ha', hb', hc', hd'⟩

end Kakeya.Assouad

end
