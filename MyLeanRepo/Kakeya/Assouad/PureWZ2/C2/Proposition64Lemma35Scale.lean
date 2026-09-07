import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64Constants
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64Lemma35LocalCleanup
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# Uniform Lemma 3.5 scales for Proposition 6.4

This is the scalar part of the final mild rescaling in `wz2_64.tex`.  The
normalization and isotropic dilation are fixed before the runtime source
scale.  Once the hierarchy producer also makes its short slab sufficiently
small, one source-scale ceiling discharges all geometric size and extension
budgets used by the exact-image and local-grain constructions.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Fixed one-Lipschitz target constant before the final Kirszbraun
extension and normalization. -/
noncomputable def pureWZ2Proposition64Lemma35TargetK : NNReal :=
  ⟨1 / (64 * (lipschitzExtensionConstant Point3 : ℝ)), by positivity⟩

/-- Fixed isotropic dilation used after the exact Proposition 6.4 map. -/
noncomputable def pureWZ2Proposition64Lemma35Scale : ℝ :=
  18432 * (lipschitzExtensionConstant Point3 : ℝ) *
    pureWZ2Proposition64NormalizationConstant ^ 2

/-- Exact-image tube radius. -/
def pureWZ2Proposition64Lemma35ImageDelta (sourceDelta : ℝ) : ℝ :=
  30 * sourceDelta

/-- Final ordinary radius after the fixed isotropic dilation. -/
noncomputable def pureWZ2Proposition64Lemma35FinalDelta
    (sourceDelta : ℝ) : ℝ :=
  45 * pureWZ2Proposition64Lemma35Scale * sourceDelta

/-- Side length of the popular cube used before isotropic dilation. -/
noncomputable def pureWZ2Proposition64Lemma35Width : ℝ :=
  1 / (18 * pureWZ2Proposition64Lemma35Scale)

theorem pureWZ2Proposition64_lipschitzExtensionConstant_one :
    (1 : ℝ) ≤ (lipschitzExtensionConstant Point3 : ℝ) := by
  exact_mod_cast (show (1 : NNReal) ≤ lipschitzExtensionConstant Point3 by
    rw [lipschitzExtensionConstant]
    exact le_max_right _ _)

theorem pureWZ2Proposition64Lemma35Scale_one :
    1 ≤ pureWZ2Proposition64Lemma35Scale := by
  unfold pureWZ2Proposition64Lemma35Scale
  calc
    (1 : ℝ) ≤ 18432 * 1 * 9 ^ 2 := by norm_num
    _ ≤ 18432 * (lipschitzExtensionConstant Point3 : ℝ) *
        pureWZ2Proposition64NormalizationConstant ^ 2 := by
      gcongr
      · exact pureWZ2Proposition64_lipschitzExtensionConstant_one
      · exact pureWZ2Proposition64NormalizationConstant_nine

theorem pureWZ2Proposition64Lemma35Scale_pos :
    0 < pureWZ2Proposition64Lemma35Scale :=
  lt_of_lt_of_le zero_lt_one pureWZ2Proposition64Lemma35Scale_one

theorem pureWZ2Proposition64Lemma35TargetK_pos :
    0 < pureWZ2Proposition64Lemma35TargetK := by
  unfold pureWZ2Proposition64Lemma35TargetK
  exact_mod_cast (div_pos zero_lt_one <|
    mul_pos (by norm_num) <| lipschitzExtensionConstant_pos Point3)

theorem pureWZ2Proposition64Lemma35_extension_targetK :
    ((lipschitzExtensionConstant Point3 *
        pureWZ2Proposition64Lemma35TargetK : NNReal) : ℝ) = 1 / 64 := by
  unfold pureWZ2Proposition64Lemma35TargetK
  change (lipschitzExtensionConstant Point3 : ℝ) *
    (1 / (64 * (lipschitzExtensionConstant Point3 : ℝ))) = 1 / 64
  field_simp [ne_of_gt (lipschitzExtensionConstant_pos Point3)]

theorem pureWZ2Proposition64Lemma35_exactK_budget :
    288 * pureWZ2Proposition64NormalizationConstant ^ 2 ≤
      (pureWZ2Proposition64Lemma35TargetK : ℝ) *
        pureWZ2Proposition64Lemma35Scale := by
  unfold pureWZ2Proposition64Lemma35TargetK
    pureWZ2Proposition64Lemma35Scale
  change 288 * pureWZ2Proposition64NormalizationConstant ^ 2 ≤
    (1 / (64 * (lipschitzExtensionConstant Point3 : ℝ))) *
      (18432 * (lipschitzExtensionConstant Point3 : ℝ) *
        pureWZ2Proposition64NormalizationConstant ^ 2)
  field_simp [ne_of_gt (lipschitzExtensionConstant_pos Point3)]
  ring_nf
  exact le_rfl

/-- The source threshold chosen before the runtime configuration.  The
separate parameter-window inequality involves the produced short-slab height
and is therefore retained by the hierarchy output. -/
noncomputable def pureWZ2Proposition64Lemma35SourceCeiling
    (targetDelta₀ : ℝ) : ℝ :=
  min (1 / 360) <|
    min (targetDelta₀ /
      (45 * pureWZ2Proposition64Lemma35Scale)) <|
    (1 / 96) / (45 * pureWZ2Proposition64Lemma35Scale)

theorem pureWZ2Proposition64Lemma35SourceCeiling_pos
    {targetDelta₀ : ℝ} (htargetDelta₀ : 0 < targetDelta₀) :
    0 < pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀ := by
  unfold pureWZ2Proposition64Lemma35SourceCeiling
  exact lt_min (by norm_num) <| lt_min
    (div_pos htargetDelta₀ <| mul_pos (by norm_num)
      pureWZ2Proposition64Lemma35Scale_pos)
    (div_pos (by norm_num) <| mul_pos (by norm_num)
      pureWZ2Proposition64Lemma35Scale_pos)

/-- A pre-runtime threshold for the two short-slab inequalities which depend
on the hierarchy depth.  This is the literal order in `wz2_64.tex`: choose
`N`, then choose the source-scale ceiling, and only then obtain the runtime
configuration. -/
structure PureWZ2Proposition64HierarchyScaleThreshold (N : ℕ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  halfHeight_small :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      pureWZ2Proposition64HalfHeight delta N ≤ 1 / 20
  halfHeight_slab_ad :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      pureWZ2Proposition64HalfHeight delta N ≤ 1 / 90
  parameter_window :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      24000 * pureWZ2Proposition64NormalizationConstant *
          (45 * pureWZ2Proposition64Lemma35Scale) * delta ≤
        pureWZ2Proposition64HalfHeight delta N

/-- Construct the hierarchy-dependent part of the Lemma-3.5 small-scale
schedule.  The strict gap `3 / N < 1` is why the paper first takes `N`
sufficiently large. -/
theorem pureWZ2Proposition64_hierarchyScaleThreshold
    {N : ℕ} (hN : 4 ≤ N) :
    Nonempty (PureWZ2Proposition64HierarchyScaleThreshold N) := by
  have hNPos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hexponentPos : 0 < (3 : ℝ) / (N : ℝ) := by positivity
  have hexponentLtOne : (3 : ℝ) / (N : ℝ) < 1 := by
    rw [div_lt_one hNPos]
    exact_mod_cast (by omega : 3 < N)
  rcases exists_delta_mul_rpow_le_rpow
      45 (by norm_num : (0 : ℝ) ≤ 45)
      (show (0 : ℝ) < 3 / (N : ℝ) from hexponentPos) with
    ⟨heightDelta₀, hheightDelta₀, hheightDelta₀One, hheight⟩
  let coefficient : ℝ :=
    2 * (24000 * pureWZ2Proposition64NormalizationConstant *
      (45 * pureWZ2Proposition64Lemma35Scale))
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    exact mul_nonneg (by norm_num) <|
      mul_nonneg
        (mul_nonneg (by norm_num)
          pureWZ2Proposition64NormalizationConstant_pos.le) <|
        mul_nonneg (by norm_num) pureWZ2Proposition64Lemma35Scale_pos.le
  rcases exists_delta_mul_rpow_le_rpow coefficient hcoefficient
      hexponentLtOne with
    ⟨windowDelta₀, hwindowDelta₀, hwindowDelta₀One, hwindow⟩
  let delta₀ := min heightDelta₀ windowDelta₀
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min hheightDelta₀ hwindowDelta₀
    delta₀_le_one := (min_le_left _ _).trans hheightDelta₀One
    halfHeight_small := ?_
    halfHeight_slab_ad := ?_
    parameter_window := ?_ }⟩
  · intro delta hdelta hdeltaSmall
    have hbound := hheight delta hdelta
      (hdeltaSmall.trans (min_le_left _ _))
    have hzero : Real.rpow delta (0 : ℝ) = 1 := Real.rpow_zero delta
    rw [hzero] at hbound
    unfold pureWZ2Proposition64HalfHeight
    nlinarith [Real.rpow_pos_of_pos hdelta (3 / (N : ℝ))]
  · intro delta hdelta hdeltaSmall
    have hbound := hheight delta hdelta
      (hdeltaSmall.trans (min_le_left _ _))
    have hzero : Real.rpow delta (0 : ℝ) = 1 := Real.rpow_zero delta
    rw [hzero] at hbound
    unfold pureWZ2Proposition64HalfHeight
    nlinarith [Real.rpow_pos_of_pos hdelta (3 / (N : ℝ))]
  · intro delta hdelta hdeltaSmall
    have hbound := hwindow delta hdelta
      (hdeltaSmall.trans (min_le_right _ _))
    have hone : Real.rpow delta (1 : ℝ) = delta := Real.rpow_one delta
    rw [hone] at hbound
    unfold pureWZ2Proposition64HalfHeight
    dsimp only [coefficient] at hbound
    nlinarith [Real.rpow_pos_of_pos hdelta (3 / (N : ℝ))]

/-- All fixed-scale geometric inequalities needed by the exact-image,
isotropic saturation, local-grain, and ED-cleanup stages. -/
structure PureWZ2Proposition64Lemma35ScaleData
    (sourceDelta halfHeight targetDelta₀ : ℝ) where
  sourceDelta_pos : 0 < sourceDelta
  halfHeight_pos : 0 < halfHeight
  halfHeight_small : halfHeight ≤ 1 / 20
  halfHeight_slab_ad : halfHeight ≤ 1 / 90
  sourceDelta_le_ceiling : sourceDelta ≤
    pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀
  parameter_window_source :
    24000 * pureWZ2Proposition64NormalizationConstant *
        (45 * pureWZ2Proposition64Lemma35Scale) * sourceDelta ≤ halfHeight
  imageDelta_pos :
    0 < pureWZ2Proposition64Lemma35ImageDelta sourceDelta
  finalDelta_pos :
    0 < pureWZ2Proposition64Lemma35FinalDelta sourceDelta
  finalDelta_le_target :
    pureWZ2Proposition64Lemma35FinalDelta sourceDelta ≤ targetDelta₀
  finalDelta_le_one_ninety_six :
    pureWZ2Proposition64Lemma35FinalDelta sourceDelta ≤ 1 / 96
  sourceDelta_small : 180 * sourceDelta ≤ 1 / 2
  sourceDelta_le_image :
    sourceDelta ≤ pureWZ2Proposition64Lemma35ImageDelta sourceDelta
  image_radius :
    180 * sourceDelta ≤
      6 * pureWZ2Proposition64Lemma35ImageDelta sourceDelta
  scale_one : 1 ≤ pureWZ2Proposition64Lemma35Scale
  scale_large :
    900 * pureWZ2Proposition64NormalizationConstant ^ 2 ≤
      pureWZ2Proposition64Lemma35Scale
  width_pos : 0 < pureWZ2Proposition64Lemma35Width
  width_one : pureWZ2Proposition64Lemma35Width ≤ 1
  box_scale :
    18 * pureWZ2Proposition64Lemma35Scale *
      pureWZ2Proposition64Lemma35Width ≤ 1
  exactK_budget :
    288 * pureWZ2Proposition64NormalizationConstant ^ 2 ≤
      (pureWZ2Proposition64Lemma35TargetK : ℝ) *
        pureWZ2Proposition64Lemma35Scale
  retube_radius :
    pureWZ2Proposition64Lemma35Scale *
          (6 * pureWZ2Proposition64Lemma35ImageDelta sourceDelta) +
        2 * pureWZ2Proposition64Lemma35FinalDelta sourceDelta ≤
      6 * pureWZ2Proposition64Lemma35FinalDelta sourceDelta
  source_scale : sourceDelta ≤
    pureWZ2Proposition64Lemma35FinalDelta sourceDelta /
      (4 * pureWZ2Proposition64Lemma35Scale)
  extension_small :
    ((lipschitzExtensionConstant Point3 *
        pureWZ2Proposition64Lemma35TargetK : NNReal) : ℝ) *
        (2 * pureWZ2Proposition64Lemma35FinalDelta sourceDelta) ≤ 1 / 2
  extension_one :
    4 * ((lipschitzExtensionConstant Point3 *
      pureWZ2Proposition64Lemma35TargetK : NNReal) : ℝ) ≤ 1
  incidence_budget :
    sourceDelta +
        4 * ((lipschitzExtensionConstant Point3 *
          pureWZ2Proposition64Lemma35TargetK : NNReal) : ℝ) *
          (2 * pureWZ2Proposition64Lemma35FinalDelta sourceDelta) ≤
      pureWZ2Proposition64Lemma35FinalDelta sourceDelta
  projection_budget :
    2 * pureWZ2Proposition64Lemma35FinalDelta sourceDelta +
        (1 / 2 : ℝ) *
          (4 * ((lipschitzExtensionConstant Point3 *
            pureWZ2Proposition64Lemma35TargetK : NNReal) : ℝ) *
            (2 * pureWZ2Proposition64Lemma35FinalDelta sourceDelta)) ≤
      6 * pureWZ2Proposition64Lemma35FinalDelta sourceDelta
  vertical_budget :
    1 / 10 +
        4 * ((lipschitzExtensionConstant Point3 *
          pureWZ2Proposition64Lemma35TargetK : NNReal) : ℝ) *
          (2 * pureWZ2Proposition64Lemma35FinalDelta sourceDelta) ≤ 1 / 2
  parameter_window_lower :
    sourceDelta ≤
      24000 * pureWZ2Proposition64NormalizationConstant *
        pureWZ2Proposition64Lemma35FinalDelta sourceDelta / halfHeight
  parameter_window_upper :
    24000 * pureWZ2Proposition64NormalizationConstant *
        pureWZ2Proposition64Lemma35FinalDelta sourceDelta / halfHeight ≤ 1
  analytic_scale_le :
    pureWZ2Proposition64Lemma35Scale *
        (sourceDelta / pureWZ2Proposition64NormalizationConstant) ≤
      pureWZ2Proposition64Lemma35FinalDelta sourceDelta

/-- Construct the complete fixed Lemma-3.5 scale receipt. -/
theorem pureWZ2Proposition64_lemma35ScaleData
    {sourceDelta halfHeight targetDelta₀ : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightSmall : halfHeight ≤ 1 / 90)
    (hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀)
    (hparameterWindow :
      24000 * pureWZ2Proposition64NormalizationConstant *
          (45 * pureWZ2Proposition64Lemma35Scale) * sourceDelta ≤
        halfHeight) :
    PureWZ2Proposition64Lemma35ScaleData
      sourceDelta halfHeight targetDelta₀ := by
  let L : ℝ := (lipschitzExtensionConstant Point3 : ℝ)
  let normalization := pureWZ2Proposition64NormalizationConstant
  let scale := pureWZ2Proposition64Lemma35Scale
  have hL : 1 ≤ L :=
    pureWZ2Proposition64_lipschitzExtensionConstant_one
  have hnormalization : 9 ≤ normalization :=
    pureWZ2Proposition64NormalizationConstant_nine
  have hscale : 1 ≤ scale := pureWZ2Proposition64Lemma35Scale_one
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have hsource360 : sourceDelta ≤ 1 / 360 :=
    hsourceSmall.trans (min_le_left _ _)
  have hsourceTarget :
      sourceDelta ≤ targetDelta₀ / (45 * scale) :=
    hsourceSmall.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have hsourceFinal :
      sourceDelta ≤ (1 / 96) / (45 * scale) :=
    hsourceSmall.trans <| (min_le_right _ _).trans <|
      min_le_right _ _
  have hfinalPos :
      0 < pureWZ2Proposition64Lemma35FinalDelta sourceDelta := by
    unfold pureWZ2Proposition64Lemma35FinalDelta
    positivity
  have hfinalTarget :
      pureWZ2Proposition64Lemma35FinalDelta sourceDelta ≤ targetDelta₀ := by
    have hmul :=
      (le_div_iff₀ (by positivity : 0 < 45 * scale)).mp hsourceTarget
    calc
      pureWZ2Proposition64Lemma35FinalDelta sourceDelta =
          sourceDelta * (45 * scale) := by
        simp only [pureWZ2Proposition64Lemma35FinalDelta, scale]
        ring
      _ ≤ targetDelta₀ := hmul
  have hfinalSmall :
      pureWZ2Proposition64Lemma35FinalDelta sourceDelta ≤ 1 / 96 := by
    have hmul :=
      (le_div_iff₀ (by positivity : 0 < 45 * scale)).mp hsourceFinal
    calc
      pureWZ2Proposition64Lemma35FinalDelta sourceDelta =
          sourceDelta * (45 * scale) := by
        simp only [pureWZ2Proposition64Lemma35FinalDelta, scale]
        ring
      _ ≤ 1 / 96 := hmul
  have hextensionTarget :=
    pureWZ2Proposition64Lemma35_extension_targetK
  refine {
    sourceDelta_pos := hsourceDelta
    halfHeight_pos := hhalfHeight
    halfHeight_small := hhalfHeightSmall.trans (by norm_num)
    halfHeight_slab_ad := hhalfHeightSmall
    sourceDelta_le_ceiling := hsourceSmall
    parameter_window_source := hparameterWindow
    imageDelta_pos := by
      unfold pureWZ2Proposition64Lemma35ImageDelta
      positivity
    finalDelta_pos := hfinalPos
    finalDelta_le_target := hfinalTarget
    finalDelta_le_one_ninety_six := hfinalSmall
    sourceDelta_small := by linarith
    sourceDelta_le_image := by
      unfold pureWZ2Proposition64Lemma35ImageDelta
      linarith
    image_radius := by
      unfold pureWZ2Proposition64Lemma35ImageDelta
      linarith
    scale_one := pureWZ2Proposition64Lemma35Scale_one
    scale_large := by
      change 900 * normalization ^ 2 ≤ 18432 * L * normalization ^ 2
      have hnormSq : 0 ≤ normalization ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg (sub_nonneg.mpr hL) hnormSq]
    width_pos := by
      unfold pureWZ2Proposition64Lemma35Width
      positivity
    width_one := by
      unfold pureWZ2Proposition64Lemma35Width
      apply (div_le_one (by positivity : 0 < 18 * scale)).2
      linarith
    box_scale := by
      unfold pureWZ2Proposition64Lemma35Width
      have hdenom : 18 * pureWZ2Proposition64Lemma35Scale ≠ 0 := by
        positivity
      have heq : pureWZ2Proposition64Lemma35Scale /
          pureWZ2Proposition64Lemma35Scale = 1 := by
        exact div_self (ne_of_gt pureWZ2Proposition64Lemma35Scale_pos)
      calc
        18 * pureWZ2Proposition64Lemma35Scale *
            (1 / (18 * pureWZ2Proposition64Lemma35Scale)) =
          pureWZ2Proposition64Lemma35Scale /
            pureWZ2Proposition64Lemma35Scale := by
              field_simp [hdenom]
        _ ≤ 1 := le_of_eq heq
    exactK_budget := pureWZ2Proposition64Lemma35_exactK_budget
    retube_radius := by
      unfold pureWZ2Proposition64Lemma35ImageDelta
        pureWZ2Proposition64Lemma35FinalDelta
      exact le_of_eq (by ring)
    source_scale := by
      unfold pureWZ2Proposition64Lemma35FinalDelta
      have heq : (45 * scale * sourceDelta) / (4 * scale) =
          (45 / 4) * sourceDelta := by
        field_simp [hscalePos.ne']
      rw [heq]
      nlinarith
    extension_small := by
      rw [hextensionTarget]
      have hfinalNonneg := hfinalPos.le
      nlinarith [hfinalSmall]
    extension_one := by
      rw [hextensionTarget]
      norm_num
    incidence_budget := by
      rw [hextensionTarget]
      unfold pureWZ2Proposition64Lemma35FinalDelta
      have hscaleNonneg : 0 ≤ scale := hscalePos.le
      nlinarith [mul_nonneg hscaleNonneg hsourceDelta.le]
    projection_budget := by
      rw [hextensionTarget]
      nlinarith [hfinalPos.le]
    vertical_budget := by
      rw [hextensionTarget]
      nlinarith [hfinalSmall]
    parameter_window_lower := by
      unfold pureWZ2Proposition64Lemma35FinalDelta
      have hcoefficient : 1 ≤ 24000 * normalization * (45 * scale) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hnormalization)
          (sub_nonneg.mpr hscale)]
      apply (le_div_iff₀ hhalfHeight).2
      have hhalfHeightOne : halfHeight ≤ 1 :=
        hhalfHeightSmall.trans (by norm_num)
      nlinarith [mul_nonneg hsourceDelta.le
        (sub_nonneg.mpr hcoefficient)]
    parameter_window_upper := by
      apply (div_le_one hhalfHeight).2
      simpa only [pureWZ2Proposition64Lemma35FinalDelta, scale, normalization,
        mul_assoc] using hparameterWindow
    analytic_scale_le := by
      unfold pureWZ2Proposition64Lemma35FinalDelta
      have hnormalizationPos : 0 < normalization := by positivity
      have hdiv : sourceDelta / normalization ≤ sourceDelta := by
        apply (div_le_iff₀ hnormalizationPos).2
        nlinarith [mul_nonneg hsourceDelta.le
          (sub_nonneg.mpr (by linarith : 1 ≤ normalization))]
      have hscaled := mul_le_mul_of_nonneg_left hdiv hscalePos.le
      dsimp only [scale, normalization] at hscaled ⊢
      nlinarith [mul_nonneg
        pureWZ2Proposition64Lemma35Scale_pos.le hsourceDelta.le]
  }

namespace PureWZ2Proposition64Lemma35ScaleData

/-- Apply the common Lemma-3.5 scale receipt to the geometric local-cleanup
constructor.  The input shading is the exact affine-image shading; no new
family or plane map is selected here. -/
theorem assembleLocalCleanup
    {sourceDelta halfHeight targetDelta₀ : ℝ}
    (data : PureWZ2Proposition64Lemma35ScaleData
      sourceDelta halfHeight targetDelta₀)
    {sourceFamily : Kakeya.Streamlined.TubeFamily
      (pureWZ2Proposition64Lemma35ImageDelta sourceDelta)}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (rawNormal : {point : Point3 // point ∈ sourceShading.union} → Point3)
    {sourceK : NNReal}
    (hrawLipschitz : LipschitzWith sourceK rawNormal)
    (hrawUnit : ∀ point, ‖rawNormal point‖ = 1)
    (hsourceK : (sourceK : ℝ) ≤
      288 * pureWZ2Proposition64NormalizationConstant ^ 2) :
    Nonempty (PureWZ2Proposition64Lemma35LocalCleanupData
      (width := pureWZ2Proposition64Lemma35Width)
      (scale := pureWZ2Proposition64Lemma35Scale) sourceShading rawNormal
      pureWZ2Proposition64Lemma35TargetK data.imageDelta_pos
      data.finalDelta_pos
      (data.finalDelta_le_one_ninety_six.trans (by norm_num))
      data.scale_one data.retube_radius) := by
  apply pureWZ2Proposition64_assembleLemma35LocalCleanup sourceShading
    rawNormal hrawLipschitz hrawUnit data.width_pos data.width_one
    data.imageDelta_pos data.finalDelta_pos
    (data.finalDelta_le_one_ninety_six.trans (by norm_num)) data.scale_one
    (hK := hsourceK.trans data.exactK_budget)
    (hsmall := data.extension_small) (hone := data.extension_one)
  · linarith [data.box_scale]

/-- Specialize the fixed scale receipt to the exact transported plane map
coming from the same Proposition 6.4 affine image. -/
theorem assembleExactLocalCleanup
    {sourceDelta halfHeight targetDelta₀ sigma : ℝ}
    (data : PureWZ2Proposition64Lemma35ScaleData
      sourceDelta halfHeight targetDelta₀)
    {g : ℝ → ℝ} {slabCenter anchorHeight normalization : ℝ}
    {translation : Point3}
    {hhalfHeight : 0 < halfHeight} {hnormalization : 9 ≤ normalization}
    {hanchorSlope : |g anchorHeight| ≤ 8}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {hsourceLine : WZ1PaperIsLineClass sourceFamily}
    {himageBox : ∀ index, ∀ point ∈ sourceShading.carrier index,
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
          normalization translation point ∈
        Kakeya.Streamlined.axisBox 2 2 2}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (exactData : @PureWZ2Proposition64ExactPlaneMapData sourceDelta
      (pureWZ2Proposition64Lemma35ImageDelta sourceDelta) sigma g slabCenter
      anchorHeight halfHeight normalization translation hhalfHeight
      hnormalization data.sourceDelta_pos hanchorSlope data.image_radius
      sourceFamily sourceShading hsourceLine himageBox C sourceLocal)
    (hnormalizationEq :
      normalization = pureWZ2Proposition64NormalizationConstant) :
    Nonempty (PureWZ2Proposition64Lemma35LocalCleanupData
      (width := pureWZ2Proposition64Lemma35Width)
      (scale := pureWZ2Proposition64Lemma35Scale)
      (pureWZ2Proposition64ExactImageShading data.sourceDelta_pos g
        slabCenter anchorHeight halfHeight normalization translation
        hhalfHeight hnormalization hanchorSlope data.image_radius
        sourceFamily sourceShading hsourceLine himageBox) exactData.planeMap
      pureWZ2Proposition64Lemma35TargetK data.imageDelta_pos
      data.finalDelta_pos
      (data.finalDelta_le_one_ninety_six.trans (by norm_num))
      data.scale_one data.retube_radius) := by
  apply data.assembleLocalCleanup _ exactData.planeMap
    exactData.planeMap_lipschitz exactData.planeMap_unit
  calc
    (exactData.K : ℝ) ≤ 288 * normalization ^ 2 := exactData.K_le
    _ = 288 * pureWZ2Proposition64NormalizationConstant ^ 2 := by
      rw [hnormalizationEq]

end PureWZ2Proposition64Lemma35ScaleData

end Kakeya.Assouad

end
