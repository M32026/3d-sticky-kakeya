import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64Preparation
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.CoveringConstruction
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitRescalingBasics

/-!
# Tube axes under the exact Proposition 6.4 map

This is the first geometric layer of the final Lemma 3.5 step.  It turns the
literal affine image of every source axis into an ordinary normalized tube
axis at a caller-supplied target radius.  It also packages the whole target
grid cells surviving the slice-wise boundary pruning.  No distinctness, CWA,
density, or local-grain conclusion is asserted at this layer.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- Linear image of a source tube direction under Proposition 6.4. -/
def pureWZ2Proposition64ImageDirection
    (g : ℝ → ℝ) (anchorHeight halfHeight normalization : ℝ)
    (direction : Point3) : Point3 :=
  pureWZ2Proposition64Linear
    (g anchorHeight) halfHeight normalization direction

theorem pureWZ2Proposition64ImageDirection_ne_zero
    {delta : ℝ} (g : ℝ → ℝ)
    {halfHeight normalization : ℝ} (anchorHeight : ℝ)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (tube : Kakeya.DeltaTube delta) :
    pureWZ2Proposition64ImageDirection g anchorHeight halfHeight
        normalization tube.direction ≠ 0 := by
  intro hzero
  have hmapZero :
      pureWZ2Proposition64Linear (g anchorHeight) halfHeight normalization
          tube.direction =
        pureWZ2Proposition64Linear (g anchorHeight) halfHeight normalization 0 := by
    simpa [pureWZ2Proposition64ImageDirection] using hzero
  have hdirection : tube.direction = 0 :=
    pureWZ2Proposition64Linear_injective
      hhalfHeight hnormalization hmapZero
  have hunit := tube.direction_unit
  rw [hdirection, norm_zero] at hunit
  norm_num at hunit

/-- A convenient operator-norm bound for the exact affine linear part. -/
theorem pureWZ2Proposition64Linear_norm_le
    {anchorSlope halfHeight normalization : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 1 ≤ normalization)
    (hanchorSlope : |anchorSlope| ≤ 8) (point : Point3) :
    ‖pureWZ2Proposition64Linear anchorSlope halfHeight normalization point‖ ≤
      (11 / halfHeight) * ‖point‖ := by
  let first : Point3 :=
    ((point 0 + anchorSlope * point 1) / normalization) •
      EuclideanSpace.single (0 : Fin 3) 1
  let second : Point3 :=
    (point 1) • EuclideanSpace.single (1 : Fin 3) 1
  let third : Point3 :=
    (point 2 / halfHeight) • EuclideanSpace.single (2 : Fin 3) 1
  have hdecompose :
      pureWZ2Proposition64Linear anchorSlope halfHeight normalization point =
        first + second + third := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2Proposition64Linear, first, second, third, point3]
  have hcoord (coordinate : Fin 3) : |point coordinate| ≤ ‖point‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le point coordinate
  have hfirst :
      |(point 0 + anchorSlope * point 1) / normalization| ≤
        9 * ‖point‖ := by
    rw [abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hnormalization)]
    have hsum :
        |point 0 + anchorSlope * point 1| ≤
          |point 0| + |anchorSlope| * |point 1| := by
      simpa [abs_mul] using abs_add_le (point 0) (anchorSlope * point 1)
    have hnine :
        |point 0| + |anchorSlope| * |point 1| ≤ 9 * ‖point‖ := by
      calc
        _ ≤ ‖point‖ + 8 * ‖point‖ := by
          exact add_le_add (hcoord 0)
            (mul_le_mul hanchorSlope (hcoord 1) (abs_nonneg _)
              (by norm_num))
        _ = 9 * ‖point‖ := by ring
    exact (div_le_self (abs_nonneg _) hnormalization).trans
      (hsum.trans hnine)
  have hthird : |point 2 / halfHeight| ≤ ‖point‖ / halfHeight := by
    rw [abs_div, abs_of_pos hhalfHeight]
    gcongr
    exact hcoord 2
  have hnormSum :
      ‖first + second + third‖ ≤
        |(point 0 + anchorSlope * point 1) / normalization| +
          |point 1| + |point 2 / halfHeight| := by
    calc
      ‖first + second + third‖ ≤ ‖first + second‖ + ‖third‖ :=
        norm_add_le _ _
      _ ≤ (‖first‖ + ‖second‖) + ‖third‖ :=
        add_le_add (norm_add_le first second) (le_refl _)
      _ = _ := by
        simp only [first, second, third, norm_smul, Real.norm_eq_abs]
        norm_num
  have hnormLeDiv : ‖point‖ ≤ ‖point‖ / halfHeight := by
    apply (le_div_iff₀ hhalfHeight).2
    exact mul_le_of_le_one_right (norm_nonneg point) hhalfHeightOne
  rw [hdecompose]
  calc
    ‖first + second + third‖ ≤
        |(point 0 + anchorSlope * point 1) / normalization| +
          |point 1| + |point 2 / halfHeight| := hnormSum
    _ ≤ 9 * ‖point‖ + ‖point‖ + ‖point‖ / halfHeight := by
      gcongr
      exact hcoord 1
    _ ≤ 11 * (‖point‖ / halfHeight) := by
      nlinarith [hnormLeDiv]
    _ = (11 / halfHeight) * ‖point‖ := by ring

/-- The exact Proposition 6.4 map is Lipschitz at the expected short-slab
scale.  This is the metric input for transporting a `delta`-tube thickening
to radius `11 * delta / halfHeight`. -/
theorem pureWZ2Proposition64Map_dist_le
    {anchorSlope halfHeight normalization : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 1 ≤ normalization)
    (hanchorSlope : |anchorSlope| ≤ 8)
    (slabCenter : ℝ) (first second : Point3) :
    dist
        (pureWZ2Proposition64Map (fun _ => anchorSlope) slabCenter 0
          halfHeight normalization first)
        (pureWZ2Proposition64Map (fun _ => anchorSlope) slabCenter 0
          halfHeight normalization second) ≤
      (11 / halfHeight) * dist first second := by
  rw [dist_eq_norm, dist_eq_norm]
  have hdifference :
      pureWZ2Proposition64Map (fun _ => anchorSlope) slabCenter 0
          halfHeight normalization first -
        pureWZ2Proposition64Map (fun _ => anchorSlope) slabCenter 0
          halfHeight normalization second =
      pureWZ2Proposition64Linear anchorSlope halfHeight normalization
        (first - second) := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2Proposition64Map, pureWZ2Proposition64Linear, point3] <;>
      ring
  rw [hdifference]
  exact pureWZ2Proposition64Linear_norm_le hhalfHeight hhalfHeightOne
    hnormalization hanchorSlope (first - second)

/-- The ordinary tube whose full axis is the exact image of a source axis. -/
def pureWZ2Proposition64ImageTube
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    {sourceDelta : ℝ} (sourceTube : Kakeya.DeltaTube sourceDelta) :
    Kakeya.DeltaTube targetDelta where
  base := pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
    normalization translation sourceTube.base
  direction :=
    let imageDirection := pureWZ2Proposition64ImageDirection g anchorHeight
      halfHeight normalization sourceTube.direction
    (‖imageDirection‖⁻¹ : ℝ) • imageDirection
  direction_unit := by
    let imageDirection := pureWZ2Proposition64ImageDirection g anchorHeight
      halfHeight normalization sourceTube.direction
    have hnonzero : imageDirection ≠ 0 :=
      pureWZ2Proposition64ImageDirection_ne_zero g anchorHeight
        hhalfHeight hnormalization sourceTube
    have hnorm : 0 < ‖imageDirection‖ := norm_pos_iff.mpr hnonzero
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnorm]
    exact inv_mul_cancel₀ hnorm.ne'

/-- Affine-linearity of the exact Proposition 6.4 map. -/
theorem pureWZ2Proposition64Map_line
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (base direction : Point3) (parameter : ℝ) :
    pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
        normalization (base + parameter • direction) =
      pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
          normalization base +
        parameter •
          pureWZ2Proposition64ImageDirection g anchorHeight halfHeight
            normalization direction := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2Proposition64Map, pureWZ2Proposition64ImageDirection,
      pureWZ2Proposition64Linear, point3] <;> ring

/-- Exact full-axis provenance for the target tube. -/
theorem pureWZ2Proposition64ImageTube_axisLine
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight : ℝ)
    (translation : Point3)
    {halfHeight normalization : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    {sourceDelta : ℝ} (sourceTube : Kakeya.DeltaTube sourceDelta) :
    tubeAxisLine
        (pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight hnormalization
          sourceTube) =
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation '' tubeAxisLine sourceTube := by
  let imageDirection := pureWZ2Proposition64ImageDirection g anchorHeight
    halfHeight normalization sourceTube.direction
  have hnonzero : imageDirection ≠ 0 :=
    pureWZ2Proposition64ImageDirection_ne_zero g anchorHeight
      hhalfHeight hnormalization sourceTube
  have hnorm : 0 < ‖imageDirection‖ := norm_pos_iff.mpr hnonzero
  let target := pureWZ2Proposition64ImageTube targetDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
    hnormalization sourceTube
  apply Set.Subset.antisymm
  · rintro point ⟨parameter, rfl⟩
    let sourceParameter := parameter / ‖imageDirection‖
    refine ⟨sourceTube.base + sourceParameter • sourceTube.direction,
      ⟨sourceParameter, rfl⟩, ?_⟩
    unfold pureWZ2Proposition64TranslatedMap
    rw [pureWZ2Proposition64Map_line]
    simp only [pureWZ2Proposition64ImageTube]
    have hscaled :
        sourceParameter • imageDirection =
          parameter • (‖imageDirection‖⁻¹ • imageDirection) := by
      simp only [smul_smul]
      dsimp only [sourceParameter]
      congr 1
    rw [hscaled]
    dsimp only [pureWZ2Proposition64TranslatedMap, imageDirection]
    abel

  · rintro point ⟨sourcePoint, ⟨parameter, rfl⟩, rfl⟩
    refine ⟨parameter * ‖imageDirection‖, ?_⟩
    unfold pureWZ2Proposition64TranslatedMap
    rw [pureWZ2Proposition64Map_line]
    simp only [pureWZ2Proposition64ImageTube]
    have hscaled :
        parameter • imageDirection =
          (parameter * ‖imageDirection‖) •
            (‖imageDirection‖⁻¹ • imageDirection) := by
      simp only [smul_smul]
      congr 1
      field_simp [hnorm.ne']
    rw [hscaled]
    dsimp only [pureWZ2Proposition64TranslatedMap, imageDirection]
    abel

/-- The height-zero point of the image axis is the translated affine image
of the source axis at the source slab center.  This is the exact intercept
identity used when the fixed horizontal translation is chosen. -/
theorem pureWZ2Proposition64ImageTube_axisZeroPoint
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight : ℝ)
    {halfHeight normalization : ℝ}
    (translation : Point3)
    (htranslationHeight : translation 2 = 0)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    {sourceDelta : ℝ} (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceLine : WZ1PaperTubeInLineClass sourceTube)
    (htargetVertical :
      (1 / 2 : ℝ) ≤
        |(pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight hnormalization
          sourceTube).direction 2|) :
    wz1TubeAxisZeroPoint
        (pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight hnormalization
          sourceTube) =
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation
        (wz1PaperAxisPointAtHeight sourceTube slabCenter) := by
  apply wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero htargetVertical
  · rw [pureWZ2Proposition64ImageTube_axisLine targetDelta g slabCenter
      anchorHeight translation hhalfHeight hnormalization sourceTube]
    exact ⟨wz1PaperAxisPointAtHeight sourceTube slabCenter,
      wz1PaperAxisPointAtHeight_mem_axis sourceTube slabCenter, rfl⟩
  · rw [pureWZ2Proposition64TranslatedMap_apply_two,
      wz1PaperAxisPointAtHeight_coord_two hsourceLine,
      htranslationHeight]
    ring

/-- Center the common horizontal translation at the image of one selected
source line.  The choice of that line is made by the finite window
pigeonhole in Lemma 3.5; the translation itself is independent of height. -/
def pureWZ2Proposition64CenteringTranslationAt
    {sourceDelta : ℝ} (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (sourceTube : Kakeya.DeltaTube sourceDelta) : Point3 :=
  let zeroImage :=
    pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight normalization
      (wz1PaperAxisPointAtHeight sourceTube slabCenter)
  point3 (-zeroImage 0) (-zeroImage 1) 0

@[simp] theorem pureWZ2Proposition64CenteringTranslationAt_apply_two
    {sourceDelta : ℝ} (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (sourceTube : Kakeya.DeltaTube sourceDelta) :
    pureWZ2Proposition64CenteringTranslationAt g slabCenter anchorHeight
        halfHeight normalization sourceTube 2 = 0 := by
  simp [pureWZ2Proposition64CenteringTranslationAt, point3]

/-- The line selected to define the common translation is centered exactly
at the target height-zero plane. -/
@[simp] theorem pureWZ2Proposition64CenteringTranslationAt_axis_zero
    {sourceDelta : ℝ} (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceLine : WZ1PaperTubeInLineClass sourceTube) :
    pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization
        (pureWZ2Proposition64CenteringTranslationAt g slabCenter anchorHeight
          halfHeight normalization sourceTube)
        (wz1PaperAxisPointAtHeight sourceTube slabCenter) = 0 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2Proposition64TranslatedMap,
      pureWZ2Proposition64CenteringTranslationAt, point3,
      wz1PaperAxisPointAtHeight_coord_two hsourceLine]

/-- A common horizontal translation places an exact image line in the fixed
paper class as soon as its translated height-zero point is in the prescribed
window.  These are exactly the bounds supplied by the finite Lemma-3.5
window pigeonhole. -/
theorem pureWZ2Proposition64ImageTube_lineClass_of_axis_window
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight : ℝ)
    {halfHeight normalization : ℝ}
    (translation : Point3)
    (htranslationHeight : translation 2 = 0)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    {sourceDelta : ℝ} (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceLine : WZ1PaperTubeInLineClass sourceTube)
    (htargetVertical :
      (1 / 2 : ℝ) ≤
        |(pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight hnormalization
          sourceTube).direction 2|)
    (htargetZeroX :
      |pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation
        (wz1PaperAxisPointAtHeight sourceTube slabCenter) 0| ≤ 1 / 3)
    (htargetZeroY :
      |pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation
        (wz1PaperAxisPointAtHeight sourceTube slabCenter) 1| ≤ 1 / 3) :
    WZ1PaperTubeInLineClass
      (pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
        halfHeight normalization translation
        hhalfHeight hnormalization sourceTube) := by
  let target := pureWZ2Proposition64ImageTube targetDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
    hnormalization sourceTube
  have hzero : wz1TubeAxisZeroPoint target =
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation
        (wz1PaperAxisPointAtHeight sourceTube slabCenter) := by
    rw [pureWZ2Proposition64ImageTube_axisZeroPoint targetDelta g slabCenter
      anchorHeight translation htranslationHeight hhalfHeight hnormalization
      sourceTube hsourceLine htargetVertical]
  have htargetVertical' : (1 / 2 : ℝ) ≤ |target.direction 2| := by
    simpa only [target] using htargetVertical
  have hpaperVertical :
      (1 / 2 : ℝ) ≤ wz1PaperDirection target 2 := by
    unfold wz1PaperDirection
    split_ifs with hsign
    · simpa [abs_of_nonneg hsign] using htargetVertical'
    · have hnegative : target.direction 2 < 0 := lt_of_not_ge hsign
      simpa [abs_of_neg hnegative] using htargetVertical'
  refine ⟨hpaperVertical, ?_, ?_⟩
  · rw [hzero]
    exact htargetZeroX
  · rw [hzero]
    exact htargetZeroY

/-- One-to-one target family with exact affine-axis provenance. -/
def pureWZ2Proposition64ImageFamily
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    {sourceDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta) :
    Kakeya.Streamlined.TubeFamily targetDelta where
  card := sourceFamily.card
  tube index := pureWZ2Proposition64ImageTube targetDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight hnormalization
    (sourceFamily.tube index)

theorem pureWZ2Proposition64ImageFamily_axisLine
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight : ℝ)
    (translation : Point3)
    {halfHeight normalization : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    {sourceDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (index : Fin sourceFamily.card) :
    tubeAxisLine
        ((pureWZ2Proposition64ImageFamily targetDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight hnormalization
          sourceFamily).tube
          index) =
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation '' tubeAxisLine (sourceFamily.tube index) :=
  pureWZ2Proposition64ImageTube_axisLine targetDelta g slabCenter anchorHeight
    translation hhalfHeight hnormalization (sourceFamily.tube index)

/-- The normalized image direction remains in the fixed vertical cone. -/
theorem pureWZ2Proposition64ImageTube_vertical
    {targetDelta sourceDelta : ℝ} (g : ℝ → ℝ)
    (slabCenter anchorHeight : ℝ)
    (translation : Point3)
    {halfHeight normalization : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightSmall : halfHeight ≤ 1 / 20)
    (hnormalization : 1 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceVertical : (1 / 2 : ℝ) ≤ |sourceTube.direction 2|) :
    (1 / 2 : ℝ) ≤
      |(pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight
          (lt_of_lt_of_le zero_lt_one hnormalization) sourceTube).direction 2| := by
  let imageDirection := pureWZ2Proposition64ImageDirection g anchorHeight
    halfHeight normalization sourceTube.direction
  have hnonzero : imageDirection ≠ 0 :=
    pureWZ2Proposition64ImageDirection_ne_zero g anchorHeight
      hhalfHeight (lt_of_lt_of_le zero_lt_one hnormalization) sourceTube
  have hnormPos : 0 < ‖imageDirection‖ := norm_pos_iff.mpr hnonzero
  have hcoordinate :
      imageDirection 2 = sourceTube.direction 2 / halfHeight := by
    simp [imageDirection, pureWZ2Proposition64ImageDirection,
      pureWZ2Proposition64Linear, point3]
  have hcoordBound (coordinate : Fin 3) :
      |sourceTube.direction coordinate| ≤ 1 := by
    have h := PiLp.norm_apply_le sourceTube.direction coordinate
    simpa [Real.norm_eq_abs, sourceTube.direction_unit] using h
  have hfirst : |imageDirection 0| ≤ 9 := by
    dsimp only [imageDirection, pureWZ2Proposition64ImageDirection]
    simp only [pureWZ2Proposition64Linear, LinearMap.coe_mk, AddHom.coe_mk]
    rw [show
      (point3
        ((sourceTube.direction 0 +
          g anchorHeight * sourceTube.direction 1) / normalization)
        (sourceTube.direction 1)
        (sourceTube.direction 2 / halfHeight)) 0 =
      (sourceTube.direction 0 +
        g anchorHeight * sourceTube.direction 1) / normalization by
          simp [point3]]
    rw [abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hnormalization)]
    apply (div_le_self (abs_nonneg _) hnormalization).trans
    calc
      |sourceTube.direction 0 + g anchorHeight * sourceTube.direction 1| ≤
          |sourceTube.direction 0| +
            |g anchorHeight| * |sourceTube.direction 1| := by
        simpa [abs_mul] using abs_add_le
          (sourceTube.direction 0)
          (g anchorHeight * sourceTube.direction 1)
      _ ≤ 1 + 8 * 1 := by
        exact add_le_add (hcoordBound 0)
          (mul_le_mul hanchorSlope (hcoordBound 1)
            (abs_nonneg _) (by norm_num))
      _ = 9 := by norm_num
  have hsecond : |imageDirection 1| ≤ 1 := by
    simpa [imageDirection, pureWZ2Proposition64ImageDirection,
      pureWZ2Proposition64Linear, point3] using hcoordBound (1 : Fin 3)
  have hthird : 10 ≤ |imageDirection 2| := by
    rw [hcoordinate, abs_div, abs_of_pos hhalfHeight]
    apply (le_div_iff₀ hhalfHeight).2
    nlinarith [hsourceVertical]
  have hnormSq :
      ‖imageDirection‖ ^ 2 = imageDirection 0 ^ 2 +
        imageDirection 1 ^ 2 + imageDirection 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    ring
  have hfirstSq : imageDirection 0 ^ 2 ≤ 81 := by
    nlinarith [sq_abs (imageDirection 0), abs_nonneg (imageDirection 0)]
  have hsecondSq : imageDirection 1 ^ 2 ≤ 1 := by
    nlinarith [sq_abs (imageDirection 1), abs_nonneg (imageDirection 1)]
  have hthirdSq : 100 ≤ imageDirection 2 ^ 2 := by
    nlinarith [sq_abs (imageDirection 2), abs_nonneg (imageDirection 2)]
  have hnormUpper : ‖imageDirection‖ ≤ 2 * |imageDirection 2| := by
    have hsq : ‖imageDirection‖ ^ 2 ≤
        (2 * |imageDirection 2|) ^ 2 := by
      rw [hnormSq]
      nlinarith [sq_abs (imageDirection 2)]
    nlinarith [norm_nonneg imageDirection, abs_nonneg (imageDirection 2)]
  change (1 / 2 : ℝ) ≤
    |(‖imageDirection‖⁻¹ • imageDirection) 2|
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_norm]
  rw [show ‖imageDirection‖⁻¹ * |imageDirection 2| =
      |imageDirection 2| / ‖imageDirection‖ by ring]
  apply (le_div_iff₀ hnormPos).2
  nlinarith

/-- Under the actual Proposition 6.4 normalization budgets the image line is
strictly more vertical than the generic line-class cutoff.  This is the
numerical fact which makes the image of a height-two slab coverable by three
unit axial segments. -/
theorem pureWZ2Proposition64ImageTube_vertical_two_thirds
    {targetDelta sourceDelta : ℝ} (g : ℝ → ℝ)
    (slabCenter anchorHeight : ℝ)
    (translation : Point3)
    {halfHeight normalization : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightSmall : halfHeight ≤ 1 / 20)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceVertical : (1 / 2 : ℝ) ≤ |sourceTube.direction 2|) :
    (2 / 3 : ℝ) <
      |(pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight
          (by linarith) sourceTube).direction 2| := by
  let imageDirection := pureWZ2Proposition64ImageDirection g anchorHeight
    halfHeight normalization sourceTube.direction
  have hnonzero : imageDirection ≠ 0 :=
    pureWZ2Proposition64ImageDirection_ne_zero g anchorHeight
      hhalfHeight (by linarith) sourceTube
  have hnormPos : 0 < ‖imageDirection‖ := norm_pos_iff.mpr hnonzero
  have hcoordinate :
      imageDirection 2 = sourceTube.direction 2 / halfHeight := by
    simp [imageDirection, pureWZ2Proposition64ImageDirection,
      pureWZ2Proposition64Linear, point3]
  have hcoordBound (coordinate : Fin 3) :
      |sourceTube.direction coordinate| ≤ 1 := by
    have h := PiLp.norm_apply_le sourceTube.direction coordinate
    simpa [Real.norm_eq_abs, sourceTube.direction_unit] using h
  have hfirst : |imageDirection 0| ≤ 1 := by
    dsimp only [imageDirection, pureWZ2Proposition64ImageDirection]
    simp only [pureWZ2Proposition64Linear, LinearMap.coe_mk, AddHom.coe_mk]
    rw [show
      (point3
        ((sourceTube.direction 0 +
          g anchorHeight * sourceTube.direction 1) / normalization)
        (sourceTube.direction 1)
        (sourceTube.direction 2 / halfHeight)) 0 =
      (sourceTube.direction 0 +
        g anchorHeight * sourceTube.direction 1) / normalization by
          simp [point3]]
    rw [abs_div, abs_of_pos (by linarith : 0 < normalization)]
    calc
      |sourceTube.direction 0 + g anchorHeight * sourceTube.direction 1| /
            normalization ≤
          9 / normalization := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        calc
          |sourceTube.direction 0 + g anchorHeight * sourceTube.direction 1| ≤
          |sourceTube.direction 0| +
            |g anchorHeight| * |sourceTube.direction 1| := by
            simpa [abs_mul] using abs_add_le
              (sourceTube.direction 0)
              (g anchorHeight * sourceTube.direction 1)
          _ ≤ 1 + 8 * 1 := by
            exact add_le_add (hcoordBound 0)
              (mul_le_mul hanchorSlope (hcoordBound 1)
                (abs_nonneg _) (by norm_num))
          _ = 9 := by norm_num
      _ ≤ 1 := by
        exact (div_le_one (by linarith : 0 < normalization)).2 hnormalization
  have hsecond : |imageDirection 1| ≤ 1 := by
    simpa [imageDirection, pureWZ2Proposition64ImageDirection,
      pureWZ2Proposition64Linear, point3] using hcoordBound (1 : Fin 3)
  have hthird : 10 ≤ |imageDirection 2| := by
    rw [hcoordinate, abs_div, abs_of_pos hhalfHeight]
    apply (le_div_iff₀ hhalfHeight).2
    nlinarith [hsourceVertical]
  have hnormSq :
      ‖imageDirection‖ ^ 2 = imageDirection 0 ^ 2 +
        imageDirection 1 ^ 2 + imageDirection 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    ring
  have hfirstSq : imageDirection 0 ^ 2 ≤ 1 := by
    nlinarith [sq_abs (imageDirection 0), abs_nonneg (imageDirection 0)]
  have hsecondSq : imageDirection 1 ^ 2 ≤ 1 := by
    nlinarith [sq_abs (imageDirection 1), abs_nonneg (imageDirection 1)]
  have hthirdSq : 100 ≤ imageDirection 2 ^ 2 := by
    nlinarith [sq_abs (imageDirection 2), abs_nonneg (imageDirection 2)]
  have hnormUpper : ‖imageDirection‖ <
      (3 / 2 : ℝ) * |imageDirection 2| := by
    have hsq : ‖imageDirection‖ ^ 2 <
        ((3 / 2 : ℝ) * |imageDirection 2|) ^ 2 := by
      rw [hnormSq]
      nlinarith [sq_abs (imageDirection 2)]
    nlinarith [norm_nonneg imageDirection, abs_nonneg (imageDirection 2)]
  change (2 / 3 : ℝ) <
    |(‖imageDirection‖⁻¹ • imageDirection) 2|
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_norm]
  rw [show ‖imageDirection‖⁻¹ * |imageDirection 2| =
      |imageDirection 2| / ‖imageDirection‖ by ring]
  apply (lt_div_iff₀ hnormPos).2
  nlinarith [hthird]

/-- The distinguished source line used to choose the common horizontal
translation is itself sent to the centered member of `L₃`. -/
theorem pureWZ2Proposition64CenteredAnchorTube_lineClass
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight : ℝ)
    {halfHeight normalization : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightSmall : halfHeight ≤ 1 / 20)
    (hnormalization : 1 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    {sourceDelta : ℝ} (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceLine : WZ1PaperTubeInLineClass sourceTube) :
    WZ1PaperTubeInLineClass
      (pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
        halfHeight normalization
        (pureWZ2Proposition64CenteringTranslationAt g slabCenter anchorHeight
          halfHeight normalization sourceTube)
        hhalfHeight (lt_of_lt_of_le zero_lt_one hnormalization) sourceTube) := by
  let translation := pureWZ2Proposition64CenteringTranslationAt g slabCenter
    anchorHeight halfHeight normalization sourceTube
  apply pureWZ2Proposition64ImageTube_lineClass_of_axis_window targetDelta g
    slabCenter anchorHeight translation
    (pureWZ2Proposition64CenteringTranslationAt_apply_two g slabCenter
      anchorHeight halfHeight normalization sourceTube)
    hhalfHeight (lt_of_lt_of_le zero_lt_one hnormalization) sourceTube
    hsourceLine
  · exact pureWZ2Proposition64ImageTube_vertical g slabCenter anchorHeight
      translation hhalfHeight hhalfHeightSmall hnormalization hanchorSlope
      sourceTube hsourceLine.vertical
  · rw [pureWZ2Proposition64CenteringTranslationAt_axis_zero g slabCenter
      anchorHeight halfHeight normalization sourceTube hsourceLine]
    norm_num
  · rw [pureWZ2Proposition64CenteringTranslationAt_axis_zero g slabCenter
      anchorHeight halfHeight normalization sourceTube hsourceLine]
    norm_num

/-- The exact map does not amplify same-height errors by the short-slab
factor.  This is the crucial metric fact behind the paper's `delta' ≥ delta`
rediscretization; using the global operator norm here would introduce the
spurious loss `delta / halfHeight`. -/
theorem pureWZ2Proposition64Map_dist_le_of_same_height
    {anchorSlope normalization : ℝ}
    (hnormalization : 1 ≤ normalization)
    (hanchorSlope : |anchorSlope| ≤ 8)
    (slabCenter halfHeight : ℝ)
    {first second : Point3}
    (hheight : first 2 = second 2) :
    dist
        (pureWZ2Proposition64Map (fun _ => anchorSlope) slabCenter 0
          halfHeight normalization first)
        (pureWZ2Proposition64Map (fun _ => anchorSlope) slabCenter 0
          halfHeight normalization second) ≤
      10 * dist first second := by
  rw [dist_eq_norm, dist_eq_norm]
  have hdifference :
      pureWZ2Proposition64Map (fun _ => anchorSlope) slabCenter 0
          halfHeight normalization first -
        pureWZ2Proposition64Map (fun _ => anchorSlope) slabCenter 0
          halfHeight normalization second =
      point3
        (((first - second) 0 + anchorSlope * (first - second) 1) /
          normalization) ((first - second) 1) 0 := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2Proposition64Map, point3, hheight] <;> ring
  rw [hdifference]
  have hcoord (coordinate : Fin 3) :
      |(first - second) coordinate| ≤ ‖first - second‖ := by
    simpa [Real.norm_eq_abs] using
      PiLp.norm_apply_le (first - second) coordinate
  have hfirst :
      |((first - second) 0 + anchorSlope * (first - second) 1) /
          normalization| ≤ 9 * ‖first - second‖ := by
    rw [abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hnormalization)]
    apply (div_le_self (abs_nonneg _) hnormalization).trans
    calc
      |(first - second) 0 + anchorSlope * (first - second) 1| ≤
          |(first - second) 0| +
            |anchorSlope| * |(first - second) 1| := by
        simpa [abs_mul] using
          abs_add_le ((first - second) 0)
            (anchorSlope * (first - second) 1)
      _ ≤ ‖first - second‖ + 8 * ‖first - second‖ := by
        exact add_le_add (hcoord 0)
          (mul_le_mul hanchorSlope (hcoord 1)
            (abs_nonneg _) (by norm_num))
      _ = 9 * ‖first - second‖ := by ring
  let firstPart : Point3 :=
    (((first - second) 0 + anchorSlope * (first - second) 1) /
      normalization) • EuclideanSpace.single (0 : Fin 3) 1
  let secondPart : Point3 :=
    ((first - second) 1) • EuclideanSpace.single (1 : Fin 3) 1
  have hpoint3 :
      point3
          (((first - second) 0 + anchorSlope * (first - second) 1) /
            normalization) ((first - second) 1) 0 =
        firstPart + secondPart := by
    ext coordinate
    fin_cases coordinate <;> simp [firstPart, secondPart, point3]
  rw [hpoint3]
  calc
    ‖firstPart + secondPart‖ ≤ ‖firstPart‖ + ‖secondPart‖ :=
      norm_add_le _ _
    _ = |((first - second) 0 +
          anchorSlope * (first - second) 1) / normalization| +
        |(first - second) 1| := by
      simp only [firstPart, secondPart, norm_smul, Real.norm_eq_abs]
      norm_num
    _ ≤ 9 * ‖first - second‖ + ‖first - second‖ := by
      exact add_le_add hfirst (hcoord 1)
    _ = 10 * ‖first - second‖ := by ring

/-- A source paper-carrier point and its same-height source-axis point remain
within a fixed multiple of the original radius after the exact map. -/
theorem pureWZ2Proposition64Map_sameHeightAxis_dist_le
    {sourceDelta : ℝ} (hsourceDelta : 0 < sourceDelta)
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (hnormalization : 1 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceLine : WZ1PaperTubeInLineClass sourceTube)
    {point : Point3} (hpoint : point ∈ wz1PaperTubeCarrier sourceTube) :
    dist
        (pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
          normalization point)
        (pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
          normalization
          (wz1PaperAxisPointAtHeight sourceTube (point 2))) ≤
      180 * sourceDelta := by
  have hsameHeight :
      wz1PaperAxisPointAtHeight sourceTube (point 2) 2 = point 2 :=
    wz1PaperAxisPointAtHeight_coord_two hsourceLine (point 2)
  have hsourceDist := wz2_paper_carrier_same_height_dist_18delta
    hsourceDelta sourceTube hsourceLine hpoint
  have hmapDist := pureWZ2Proposition64Map_dist_le_of_same_height
    (anchorSlope := g anchorHeight)
    hnormalization hanchorSlope slabCenter halfHeight
    hsameHeight.symm
  have hmapIdentity :
      pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
          normalization =
        pureWZ2Proposition64Map (fun _ => g anchorHeight) slabCenter 0
          halfHeight normalization := by
    funext sourcePoint
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2Proposition64Map, point3]
  rw [hmapIdentity]
  exact hmapDist.trans (by nlinarith)

theorem pureWZ2Proposition64TranslatedMap_sameHeightAxis_dist_le
    {sourceDelta : ℝ} (hsourceDelta : 0 < sourceDelta)
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hnormalization : 1 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceLine : WZ1PaperTubeInLineClass sourceTube)
    {point : Point3} (hpoint : point ∈ wz1PaperTubeCarrier sourceTube) :
    dist
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point)
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation
          (wz1PaperAxisPointAtHeight sourceTube (point 2))) ≤
      180 * sourceDelta := by
  rw [dist_eq_norm, pureWZ2Proposition64TranslatedMap_sub]
  rw [← dist_eq_norm]
  exact pureWZ2Proposition64Map_sameHeightAxis_dist_le hsourceDelta g
    slabCenter anchorHeight halfHeight normalization hnormalization
    hanchorSlope sourceTube hsourceLine hpoint

/-- An ordinary unit-segment carrier point and its same-height source-axis
point remain within `20 * sourceDelta` after the exact Proposition-6.4 map.
Unlike the paper-carrier variant, this uses the genuine ordinary carrier and
therefore has no axial crop hypothesis. -/
theorem pureWZ2Proposition64Map_ordinary_sameHeightAxis_dist_le
    {sourceDelta : ℝ} (hsourceDelta : 0 < sourceDelta)
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (hnormalization : 1 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceLine : WZ1PaperTubeInLineClass sourceTube)
    {point : Point3} (hpoint : point ∈ sourceTube.carrier) :
    dist
        (pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
          normalization point)
        (pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
          normalization
          (wz1PaperAxisPointAtHeight sourceTube (point 2))) ≤
      20 * sourceDelta := by
  rcases exists_closest_on_axis hsourceDelta.le sourceTube point hpoint with
    ⟨parameter, _hparameter, hpointAxis⟩
  let axisPoint := sourceTube.base + parameter • sourceTube.direction
  have haxisPoint : axisPoint ∈ tubeAxisLine sourceTube :=
    ⟨parameter, rfl⟩
  have hsourceDist :
      dist point (wz1PaperAxisPointAtHeight sourceTube (point 2)) ≤
        2 * sourceDelta := by
    calc
      dist point (wz1PaperAxisPointAtHeight sourceTube (point 2)) =
          dist (wz1PaperAxisPointAtHeight sourceTube (point 2)) point :=
        dist_comm _ _
      _ ≤ 2 * dist point axisPoint :=
        wz1Paper_axisPointAtHeight_dist_point_le_two_mul
          hsourceLine point axisPoint haxisPoint
      _ ≤ 2 * sourceDelta := by gcongr
  have hsameHeight :
      wz1PaperAxisPointAtHeight sourceTube (point 2) 2 = point 2 :=
    wz1PaperAxisPointAtHeight_coord_two hsourceLine (point 2)
  have hmapDist := pureWZ2Proposition64Map_dist_le_of_same_height
    (anchorSlope := g anchorHeight)
    hnormalization hanchorSlope slabCenter halfHeight hsameHeight.symm
  have hmapIdentity :
      pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
          normalization =
        pureWZ2Proposition64Map (fun _ => g anchorHeight) slabCenter 0
          halfHeight normalization := by
    funext sourcePoint
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2Proposition64Map, point3]
  rw [hmapIdentity]
  exact hmapDist.trans (by nlinarith)

theorem pureWZ2Proposition64TranslatedMap_ordinary_sameHeightAxis_dist_le
    {sourceDelta : ℝ} (hsourceDelta : 0 < sourceDelta)
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hnormalization : 1 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceLine : WZ1PaperTubeInLineClass sourceTube)
    {point : Point3} (hpoint : point ∈ sourceTube.carrier) :
    dist
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point)
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation
          (wz1PaperAxisPointAtHeight sourceTube (point 2))) ≤
      20 * sourceDelta := by
  rw [dist_eq_norm, pureWZ2Proposition64TranslatedMap_sub]
  rw [← dist_eq_norm]
  exact pureWZ2Proposition64Map_ordinary_sameHeightAxis_dist_le hsourceDelta g
    slabCenter anchorHeight halfHeight normalization hnormalization
    hanchorSlope sourceTube hsourceLine hpoint

/-- Along one exact-image axis, a point whose source height lies in the short
slab moves by at most `2 * halfHeight` in either horizontal coordinate from
the height-zero image point. -/
theorem pureWZ2Proposition64ImageAxis_horizontal_shift_le
    {sourceDelta : ℝ} (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceLine : WZ1PaperTubeInLineClass sourceTube)
    {height : ℝ}
    (hheight : height ∈
      Set.Icc (slabCenter - halfHeight) (slabCenter + halfHeight))
    (coordinate : Fin 3)
    (hcoordinate : coordinate = 0 ∨ coordinate = 1) :
    |pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation
          (wz1PaperAxisPointAtHeight sourceTube height) coordinate -
        pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation
          (wz1PaperAxisPointAtHeight sourceTube slabCenter) coordinate| ≤
      2 * halfHeight := by
  let direction := wz1PaperDirection sourceTube
  have hdirectionUnit : ‖direction‖ = 1 := wz1PaperDirection_norm sourceTube
  have hdirectionTwo : (1 / 2 : ℝ) ≤ direction 2 := hsourceLine.1
  have hdirectionTwoPos : 0 < direction 2 := by linarith
  have hdirectionCoord (i : Fin 3) : |direction i| ≤ 1 := by
    have h := PiLp.norm_apply_le direction i
    simpa [Real.norm_eq_abs, hdirectionUnit] using h
  have hheightAbs : |height - slabCenter| ≤ halfHeight := by
    rw [abs_le]
    constructor <;> linarith [hheight.1, hheight.2]
  have haxisDifference (i : Fin 3) :
      |wz1PaperAxisPointAtHeight sourceTube height i -
          wz1PaperAxisPointAtHeight sourceTube slabCenter i| ≤
        2 * halfHeight := by
    simp only [wz1PaperAxisPointAtHeight, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]
    rw [show
      (wz1TubeAxisZeroPoint sourceTube i + height / direction 2 * direction i) -
          (wz1TubeAxisZeroPoint sourceTube i +
            slabCenter / direction 2 * direction i) =
        ((height - slabCenter) / direction 2) * direction i by ring,
      abs_mul, abs_div, abs_of_pos hdirectionTwoPos]
    calc
      |height - slabCenter| / direction 2 * |direction i| ≤
          (halfHeight / (1 / 2 : ℝ)) * 1 := by
        have hquot : |height - slabCenter| / direction 2 ≤
            halfHeight / (1 / 2 : ℝ) := by
          exact div_le_div₀ hhalfHeight.le hheightAbs (by norm_num)
            hdirectionTwo
        exact mul_le_mul hquot (hdirectionCoord i) (abs_nonneg _) (by positivity)
      _ = 2 * halfHeight := by ring
  rcases hcoordinate with rfl | rfl
  · simp only [pureWZ2Proposition64TranslatedMap, PiLp.add_apply,
      pureWZ2Proposition64Map_apply_zero]
    rw [show
      ((wz1PaperAxisPointAtHeight sourceTube height 0 +
            g anchorHeight * wz1PaperAxisPointAtHeight sourceTube height 1) /
            normalization + translation 0) -
          ((wz1PaperAxisPointAtHeight sourceTube slabCenter 0 +
            g anchorHeight * wz1PaperAxisPointAtHeight sourceTube slabCenter 1) /
            normalization + translation 0) =
        ((wz1PaperAxisPointAtHeight sourceTube height 0 -
            wz1PaperAxisPointAtHeight sourceTube slabCenter 0) +
          g anchorHeight *
            (wz1PaperAxisPointAtHeight sourceTube height 1 -
              wz1PaperAxisPointAtHeight sourceTube slabCenter 1)) /
          normalization by ring]
    rw [abs_div, abs_of_pos (by linarith : 0 < normalization)]
    have hsum :
        |(wz1PaperAxisPointAtHeight sourceTube height 0 -
              wz1PaperAxisPointAtHeight sourceTube slabCenter 0) +
            g anchorHeight *
              (wz1PaperAxisPointAtHeight sourceTube height 1 -
                wz1PaperAxisPointAtHeight sourceTube slabCenter 1)| ≤
          18 * halfHeight := by
      calc
        _ ≤ |wz1PaperAxisPointAtHeight sourceTube height 0 -
                wz1PaperAxisPointAtHeight sourceTube slabCenter 0| +
              |g anchorHeight| *
                |wz1PaperAxisPointAtHeight sourceTube height 1 -
                  wz1PaperAxisPointAtHeight sourceTube slabCenter 1| := by
            exact (abs_add_le _ _).trans_eq (by rw [abs_mul])
        _ ≤ 2 * halfHeight + 8 * (2 * halfHeight) := by
            gcongr
            · exact haxisDifference 0
            · exact haxisDifference 1
        _ = 18 * halfHeight := by ring
    calc
      _ ≤ (18 * halfHeight) / normalization := by gcongr
      _ ≤ 2 * halfHeight := by
        apply (div_le_iff₀ (by linarith : 0 < normalization)).2
        nlinarith
  · simpa [pureWZ2Proposition64TranslatedMap,
      pureWZ2Proposition64Map_apply_one] using haxisDifference (1 : Fin 3)

/-- A genuine source shaded point in the selected slab maps into the target
paper tube once the final radius pays the fixed Lemma-3.5 constant. -/
theorem pureWZ2Proposition64TranslatedMap_mem_imageTube
    {sourceDelta targetDelta : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 1 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hradius : 180 * sourceDelta ≤ 6 * targetDelta)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceLine : WZ1PaperTubeInLineClass sourceTube)
    {point : Point3} (hpoint : point ∈ wz1PaperTubeCarrier sourceTube)
    (himageBox :
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point ∈
        Kakeya.Streamlined.axisBox 2 2 2) :
    pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation point ∈
      wz1PaperTubeCarrier
        (pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight
          (lt_of_lt_of_le zero_lt_one hnormalization) sourceTube) := by
  let axisPoint := wz1PaperAxisPointAtHeight sourceTube (point 2)
  have haxisPoint : axisPoint ∈ tubeAxisLine sourceTube :=
    wz1PaperAxisPointAtHeight_mem_axis sourceTube (point 2)
  have htargetAxis :
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation axisPoint ∈
        tubeAxisLine
          (pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
            halfHeight normalization translation hhalfHeight
            (lt_of_lt_of_le zero_lt_one hnormalization) sourceTube) := by
    rw [pureWZ2Proposition64ImageTube_axisLine targetDelta g slabCenter
      anchorHeight translation hhalfHeight
      (lt_of_lt_of_le zero_lt_one hnormalization) sourceTube]
    exact ⟨axisPoint, haxisPoint, rfl⟩
  refine ⟨?_, himageBox⟩
  apply Metric.mem_cthickening_of_dist_le
    (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
      normalization translation point)
    (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
      normalization translation axisPoint)
    (6 * targetDelta) _ htargetAxis
  exact (pureWZ2Proposition64TranslatedMap_sameHeightAxis_dist_le
    hsourceDelta g slabCenter anchorHeight halfHeight normalization translation
    hnormalization hanchorSlope sourceTube hsourceLine hpoint).trans hradius

/-- Every target grid cell meeting the true image and staying in the ambient
box lies in the corresponding paper tube. -/
theorem pureWZ2Proposition64GridCube_subset_imageTube
    {sourceDelta targetDelta : ℝ}
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 1 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hradius : 180 * sourceDelta + 2 * targetDelta ≤ 6 * targetDelta)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceLine : WZ1PaperTubeInLineClass sourceTube)
    {cell : ℤ × ℤ × ℤ} {imagePoint : Point3}
    (hsourcePoint : ∃ sourcePoint ∈ wz1PaperTubeCarrier sourceTube,
      imagePoint =
        pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation sourcePoint)
    (himageCell : imagePoint ∈ wz1PaperGridCube targetDelta cell)
    (hcellBox : wz1PaperGridCube targetDelta cell ⊆
      Kakeya.Streamlined.axisBox 2 2 2) :
    wz1PaperGridCube targetDelta cell ⊆
      wz1PaperTubeCarrier
        (pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight
          (lt_of_lt_of_le zero_lt_one hnormalization) sourceTube) := by
  rcases hsourcePoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  intro point hpointCell
  let sourceAxisPoint :=
    wz1PaperAxisPointAtHeight sourceTube (sourcePoint 2)
  have htargetAxis :
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation sourceAxisPoint ∈
        tubeAxisLine
          (pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
            halfHeight normalization translation hhalfHeight
            (lt_of_lt_of_le zero_lt_one hnormalization) sourceTube) := by
    rw [pureWZ2Proposition64ImageTube_axisLine targetDelta g slabCenter
      anchorHeight translation hhalfHeight
      (lt_of_lt_of_le zero_lt_one hnormalization) sourceTube]
    exact ⟨sourceAxisPoint,
      wz1PaperAxisPointAtHeight_mem_axis sourceTube (sourcePoint 2), rfl⟩
  have hgridDist :
      dist point
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation sourcePoint) <
        2 * targetDelta :=
    wz1_paper_grid_cube_diameter_lt_two_rho htargetDelta
      hpointCell himageCell
  have himageAxis :=
    pureWZ2Proposition64TranslatedMap_sameHeightAxis_dist_le
      hsourceDelta g slabCenter anchorHeight halfHeight normalization
      translation hnormalization hanchorSlope sourceTube hsourceLine hsourcePoint
  have hdist :
      dist point
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation sourceAxisPoint) ≤
        6 * targetDelta := by
    calc
      _ ≤ dist point
            (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
              halfHeight normalization translation sourcePoint) +
          dist
            (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
              halfHeight normalization translation sourcePoint)
            (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
              halfHeight normalization translation sourceAxisPoint) :=
        dist_triangle _ _ _
      _ ≤ 2 * targetDelta + 180 * sourceDelta := by linarith
      _ ≤ 6 * targetDelta := by linarith
  exact ⟨Metric.mem_cthickening_of_dist_le point _ (6 * targetDelta) _
    htargetAxis hdist, hcellBox hpointCell⟩

/-- A whole target grid cell is retained only when it genuinely meets the
exact affine image, lies in the corresponding cropped paper tube, and meets
the image on every occupied horizontal slice.  This is the geometric core of
the usual Lemma-3.5 boundary pruning. -/
def pureWZ2Proposition64SafeCubicalCarrier
    (targetDelta : ℝ) (targetTube : Kakeya.DeltaTube targetDelta)
    (sourceImage : Set Point3) : Set Point3 :=
  ⋃ cell :
      {cell : ℤ × ℤ × ℤ //
        wz1PaperGridCube targetDelta cell ⊆
            wz1PaperTubeCarrier targetTube ∧
          (sourceImage ∩
              wz1PaperGridCube targetDelta cell).Nonempty ∧
            ∀ z ∈ Set.Icc (-1 : ℝ) 1,
              (wz1PaperGridCube targetDelta cell ∩
                {point : Point3 | point 2 = z}).Nonempty →
                (sourceImage ∩ wz1PaperGridCube targetDelta cell ∩
                  {point : Point3 | point 2 = z}).Nonempty},
    wz1PaperGridCube targetDelta cell.1

theorem pureWZ2Proposition64SafeCubicalCarrier_measurable
    (targetDelta : ℝ) (targetTube : Kakeya.DeltaTube targetDelta)
    (sourceImage : Set Point3) :
    MeasurableSet
      (pureWZ2Proposition64SafeCubicalCarrier
        targetDelta targetTube sourceImage) := by
  unfold pureWZ2Proposition64SafeCubicalCarrier
  apply MeasurableSet.iUnion
  intro cell
  exact wz1PaperGridCube_measurable cell.1

theorem pureWZ2Proposition64SafeCubicalCarrier_subset_tube
    (targetDelta : ℝ) (targetTube : Kakeya.DeltaTube targetDelta)
    (sourceImage : Set Point3) :
    pureWZ2Proposition64SafeCubicalCarrier
        targetDelta targetTube sourceImage ⊆
      wz1PaperTubeCarrier targetTube := by
  intro point hpoint
  rcases Set.mem_iUnion.mp hpoint with ⟨cell, hpointCell⟩
  exact cell.2.1 hpointCell

theorem pureWZ2Proposition64SafeCubicalCarrier_near_image
    (targetDelta : ℝ) (targetTube : Kakeya.DeltaTube targetDelta)
    (htargetDelta : 0 < targetDelta)
    (sourceImage : Set Point3) :
    pureWZ2Proposition64SafeCubicalCarrier
        targetDelta targetTube sourceImage ⊆
      Metric.cthickening (2 * targetDelta) sourceImage := by
  intro point hpoint
  rcases Set.mem_iUnion.mp hpoint with ⟨cell, hpointCell⟩
  rcases cell.2.2.1 with ⟨imagePoint, hsourceImage, himageCell⟩
  apply Metric.mem_cthickening_of_dist_le point imagePoint
    (2 * targetDelta) sourceImage hsourceImage
  exact le_of_lt
    (wz1_paper_grid_cube_diameter_lt_two_rho
      htargetDelta hpointCell himageCell)

theorem pureWZ2Proposition64SafeCubicalCarrier_cell_meets_image
    (targetDelta : ℝ) (targetTube : Kakeya.DeltaTube targetDelta)
    (sourceImage : Set Point3)
    {point : Point3}
    (hpoint : point ∈
      pureWZ2Proposition64SafeCubicalCarrier
        targetDelta targetTube sourceImage) :
    ∃ imagePoint ∈ sourceImage,
      wz1PaperGridIndex targetDelta point =
        wz1PaperGridIndex targetDelta imagePoint := by
  rcases Set.mem_iUnion.mp hpoint with ⟨cell, hpointCell⟩
  rcases cell.2.2.1 with ⟨imagePoint, hsourceImage, himageCell⟩
  refine ⟨imagePoint, hsourceImage, ?_⟩
  exact
    ((mem_wz1PaperGridCube _ _ _).mp hpointCell).trans
      ((mem_wz1PaperGridCube _ _ _).mp himageCell).symm

theorem pureWZ2Proposition64SafeCubicalCarrier_isCubical
    (targetDelta : ℝ) (targetTube : Kakeya.DeltaTube targetDelta)
    (sourceImage : Set Point3) :
    ∀ point ∈
        pureWZ2Proposition64SafeCubicalCarrier
          targetDelta targetTube sourceImage,
      wz1PaperGridCube targetDelta
          (wz1PaperGridIndex targetDelta point) ⊆
        pureWZ2Proposition64SafeCubicalCarrier
          targetDelta targetTube sourceImage := by
  intro point hpoint other hother
  rcases Set.mem_iUnion.mp hpoint with ⟨cell, hpointCell⟩
  apply Set.mem_iUnion.mpr
  refine ⟨cell, ?_⟩
  have hindex :
      wz1PaperGridIndex targetDelta point = cell.1 :=
    (mem_wz1PaperGridCube _ _ _).mp hpointCell
  rw [hindex] at hother
  exact hother

theorem pureWZ2Proposition64SafeCubicalCarrier_projection_close
    (targetDelta : ℝ) (targetTube : Kakeya.DeltaTube targetDelta)
    (htargetDelta : 0 < targetDelta)
    (targetSlope : SlopeFunction)
    (hnormalized : targetSlope.IsNormalized)
    (sourceImage : Set Point3)
    {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1)
    {point : Point3}
    (hpoint : point ∈
      pureWZ2Proposition64SafeCubicalCarrier
        targetDelta targetTube sourceImage)
    (hheight : point 2 = z) :
    ∃ imagePoint ∈ horizontalSlice sourceImage z,
      |inner ℝ point (globalGrainDirection (targetSlope z)) -
          inner ℝ imagePoint (globalGrainDirection (targetSlope z))| ≤
        4 * targetDelta := by
  rcases Set.mem_iUnion.mp hpoint with ⟨cell, hpointCell⟩
  have hsliceNonempty :
      (wz1PaperGridCube targetDelta cell.1 ∩
        {candidate : Point3 | candidate 2 = z}).Nonempty :=
    ⟨point, hpointCell, hheight⟩
  rcases cell.2.2.2 z hz hsliceNonempty with
    ⟨imagePoint, ⟨hsourceImage, himageCell⟩, himageHeight⟩
  have hdist : dist point imagePoint < 2 * targetDelta :=
    wz1_paper_grid_cube_diameter_lt_two_rho
      htargetDelta hpointCell himageCell
  have hslope : |targetSlope z| ≤ 1 := (hnormalized z hz).1
  have hdirection : ‖globalGrainDirection (targetSlope z)‖ ≤ 2 := by
    unfold globalGrainDirection
    calc
      ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
          targetSlope z • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)‖ ≤
          ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ +
            ‖targetSlope z •
              EuclideanSpace.single (1 : Fin 3) (1 : ℝ)‖ := norm_add_le _ _
      _ = 1 + |targetSlope z| := by
        simp [norm_smul, Real.norm_eq_abs]
      _ ≤ 2 := by linarith
  refine ⟨imagePoint, ⟨hsourceImage, himageHeight⟩, ?_⟩
  · rw [← inner_sub_left]
    have hinner := abs_real_inner_le_norm
      (point - imagePoint) (globalGrainDirection (targetSlope z))
    calc
      |inner ℝ (point - imagePoint)
          (globalGrainDirection (targetSlope z))| ≤
          ‖point - imagePoint‖ *
            ‖globalGrainDirection (targetSlope z)‖ := hinner
      _ ≤ dist point imagePoint * 2 := by
        rw [dist_eq_norm]
        gcongr
      _ ≤ 4 * targetDelta := by linarith

/-- The canonical whole-cell shading attached to the exact one-to-one image
family.  Empty boundary cells are intentionally allowed here: the quantitative
Lemma-3.5 refinement is the later step that proves enough safe cells remain. -/
def pureWZ2Proposition64SafeImageShading
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    {sourceDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceShading : WZ1PaperTubeShading sourceFamily) :
    WZ1PaperTubeShading
      (pureWZ2Proposition64ImageFamily targetDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight hnormalization
        sourceFamily) where
  carrier := fun index =>
    pureWZ2Proposition64SafeCubicalCarrier targetDelta
      ((pureWZ2Proposition64ImageFamily targetDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight hnormalization
        sourceFamily).tube
          index)
      (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation '' sourceShading.carrier index)
  measurable_carrier := fun index =>
    pureWZ2Proposition64SafeCubicalCarrier_measurable _ _ _
  subset_body := fun index =>
    pureWZ2Proposition64SafeCubicalCarrier_subset_tube _ _ _

/-- Exact-image geometric data before the quantitative Lemma-3.5 cleanup. -/
structure PureWZ2Proposition64ActualImageRediscretizationData
    {sourceDelta targetDelta : ℝ}
    (g : SlopeFunction)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceShading : WZ1PaperTubeShading sourceFamily) where
  translation_height : translation 2 = 0
  family : Kakeya.Streamlined.TubeFamily targetDelta
  shading : WZ1PaperTubeShading family
  sourceParent : Fin family.card → Fin sourceFamily.card
  axis_provenance :
    ∀ target,
      tubeAxisLine (family.tube target) =
        pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation ''
          tubeAxisLine (sourceFamily.tube (sourceParent target))
  shading_near_source_image :
    ∀ target,
      shading.carrier target ⊆
        Metric.cthickening (2 * targetDelta)
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation ''
            sourceShading.carrier (sourceParent target))
  cubical : WZ1PaperIsCubicalShading shading
  cell_meets_source_image :
    ∀ target point, point ∈ shading.carrier target →
      ∃ imagePoint ∈
          pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation ''
            sourceShading.carrier (sourceParent target),
        wz1PaperGridIndex targetDelta point =
          wz1PaperGridIndex targetDelta imagePoint
  projection_close :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      ∀ value ∈
        scalarProjection
          (globalGrainDirection
            (pureWZ2Proposition64Slope g slabCenter anchorHeight
              halfHeight normalization z))
          (horizontalSlice shading.union z),
        ∃ sourceValue ∈
          scalarProjection
            (globalGrainDirection
              (pureWZ2Proposition64Slope g slabCenter anchorHeight
                halfHeight normalization z))
            (horizontalSlice
              (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
                halfHeight normalization translation '' sourceShading.union) z),
          |value - sourceValue| ≤ 4 * targetDelta

/-- Construct the exact-image whole-cell layer.  This theorem performs no
mass, distinctness, CWA, or local-grain inference. -/
noncomputable def pureWZ2Proposition64ActualImageRediscretization
    {sourceDelta targetDelta : ℝ}
    (g : SlopeFunction)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (htranslationHeight : translation 2 = 0)
    (htargetDelta : 0 < targetDelta)
    (hnormalized :
      (pureWZ2Proposition64Slope g slabCenter anchorHeight halfHeight
        normalization).IsNormalized)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceShading : WZ1PaperTubeShading sourceFamily) :
    PureWZ2Proposition64ActualImageRediscretizationData
      (targetDelta := targetDelta)
      g slabCenter anchorHeight halfHeight normalization translation
        hhalfHeight hnormalization sourceFamily sourceShading where
  translation_height := htranslationHeight
  family :=
    pureWZ2Proposition64ImageFamily targetDelta g slabCenter anchorHeight
      halfHeight normalization translation hhalfHeight hnormalization sourceFamily
  shading :=
    pureWZ2Proposition64SafeImageShading targetDelta g slabCenter anchorHeight
      halfHeight normalization translation
      hhalfHeight hnormalization
      sourceFamily sourceShading
  sourceParent := fun index => index
  axis_provenance := fun target =>
    by
      simpa [pureWZ2Proposition64TranslatedMap] using
        (pureWZ2Proposition64ImageFamily_axisLine targetDelta g slabCenter
          anchorHeight translation hhalfHeight hnormalization sourceFamily target)
  shading_near_source_image := fun target =>
    pureWZ2Proposition64SafeCubicalCarrier_near_image
      _ _ htargetDelta _
  cubical := by
    intro target point hpoint
    exact
      pureWZ2Proposition64SafeCubicalCarrier_isCubical
        _ _ _ point hpoint
  cell_meets_source_image := by
    intro target point hpoint
    exact
      pureWZ2Proposition64SafeCubicalCarrier_cell_meets_image
        _ _ _ hpoint
  projection_close := by
    intro z hz value hvalue
    rcases hvalue with ⟨point, ⟨⟨target, htarget⟩, hheight⟩, rfl⟩
    rcases pureWZ2Proposition64SafeCubicalCarrier_projection_close
        targetDelta
        ((pureWZ2Proposition64ImageFamily targetDelta g slabCenter
          anchorHeight halfHeight normalization translation hhalfHeight
          hnormalization
          sourceFamily).tube target)
        htargetDelta
        (pureWZ2Proposition64Slope g slabCenter anchorHeight halfHeight
          normalization) hnormalized
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation '' sourceShading.carrier target)
        hz htarget hheight with
      ⟨imagePoint, himagePoint, hclose⟩
    refine
      ⟨inner ℝ imagePoint
          (globalGrainDirection
            (pureWZ2Proposition64Slope g slabCenter anchorHeight
              halfHeight normalization z)), ?_, hclose⟩
    refine ⟨imagePoint, ⟨?_, himagePoint.2⟩, rfl⟩
    rcases himagePoint.1 with ⟨sourcePoint, hsourcePoint, rfl⟩
    exact ⟨sourcePoint, ⟨target, hsourcePoint⟩, rfl⟩

end Kakeya.Assouad

end
