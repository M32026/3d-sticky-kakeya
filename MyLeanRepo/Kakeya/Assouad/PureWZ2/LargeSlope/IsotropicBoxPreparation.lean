import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicDistinctCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PureExternalWeightRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FinalAnisotropicPopularBox
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GrainSubfamilyRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperAxisCenterBound
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper

/-!
# CWA-compatible source box for the final isotropic normalization

Before the final positive similarity, select a box of width `1 / (100*scale)`
and regularize its actual per-tube masses.  Every retained source tube then
contains a genuine point in that box.  The paper carrier thickness controls
the supporting axis at the box center, and multiplication by `scale` places
the target height-zero point in the fixed line-class window.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

attribute [local instance] Classical.propDecidable

/-- Horizontal width of the source box used immediately before the final
similarity. -/
def pureWZ2FinalIsotropicSourceWidth (scale : ℝ) : ℝ :=
  1 / (100 * scale)

/-- The corresponding mass normalization per ambient source tube. -/
def pureWZ2FinalIsotropicSourceNormalization
    {sourceDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (scale : ℝ) : ENNReal :=
  (ENNReal.ofReal ((pureWZ2FinalIsotropicSourceWidth scale ^ 2 / 9) *
      (sourceDelta / 3)) *
    sourceShading.mass) / sourceFamily.enncard

/-- A per-source mass floor passes through the final-box normalization with
the source cardinality cancelled.  This is the ratio-safe form needed for
uniform control of the following nearby-CWA regularization. -/
theorem pureWZ2FinalIsotropicSourceNormalization_lower
    {sourceDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (scale : ℝ)
    (hfamily : sourceFamily.Nonempty)
    {massFloor : ENNReal}
    (hmass : massFloor * sourceFamily.enncard ≤ sourceShading.mass) :
    ENNReal.ofReal
          ((pureWZ2FinalIsotropicSourceWidth scale ^ 2 / 9) *
            (sourceDelta / 3)) * massFloor ≤
      pureWZ2FinalIsotropicSourceNormalization sourceShading scale := by
  have hcardZero : sourceFamily.enncard ≠ 0 := by
    change (sourceFamily.card : ENNReal) ≠ 0
    exact_mod_cast hfamily.ne'
  have hcardTop : sourceFamily.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  unfold pureWZ2FinalIsotropicSourceNormalization
  apply (ENNReal.le_div_iff_mul_le (Or.inl hcardZero)
    (Or.inl hcardTop)).2
  calc
    (ENNReal.ofReal
          ((pureWZ2FinalIsotropicSourceWidth scale ^ 2 / 9) *
            (sourceDelta / 3)) * massFloor) * sourceFamily.enncard =
        ENNReal.ofReal
          ((pureWZ2FinalIsotropicSourceWidth scale ^ 2 / 9) *
            (sourceDelta / 3)) *
          (massFloor * sourceFamily.enncard) := by ring
    _ ≤ ENNReal.ofReal
          ((pureWZ2FinalIsotropicSourceWidth scale ^ 2 / 9) *
            (sourceDelta / 3)) * sourceShading.mass := by gcongr

/-- Ratio form of `pureWZ2FinalIsotropicSourceNormalization_lower`.  The
source cardinality remains cancelled when the fixed per-source upper weight
`8` is introduced. -/
theorem pureWZ2FinalIsotropicSourceNormalization_inv_mul_eight_le
    {sourceDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (scale : ℝ)
    (hfamily : sourceFamily.Nonempty)
    {massFloor ratioBound : ENNReal}
    (hmass : massFloor * sourceFamily.enncard ≤ sourceShading.mass)
    (hratio :
      (ENNReal.ofReal
          ((pureWZ2FinalIsotropicSourceWidth scale ^ 2 / 9) *
            (sourceDelta / 3)) * massFloor)⁻¹ * 8 ≤ ratioBound) :
    (pureWZ2FinalIsotropicSourceNormalization sourceShading scale)⁻¹ * 8 ≤
      ratioBound := by
  exact (mul_le_mul_right' ((ENNReal.inv_le_inv).2
    (pureWZ2FinalIsotropicSourceNormalization_lower sourceShading scale
      hfamily hmass)) 8).trans hratio

/-- Source preparation data for the final isotropic normalization. -/
structure PureWZ2FinalIsotropicBoxPreparationData
    {sourceDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (sourceConstant scheduleConstant : ENNReal)
    (levelCount : ℕ) (scale : ℝ) where
  popular : PureWZ2FinalAnisotropicPopularBoxData sourceShading
    (pureWZ2FinalIsotropicSourceWidth scale) sourceDelta
  regularized : PureWZ2ExternalWeightRegularizationData
    sourceConstant scheduleConstant
    (pureWZ2FinalIsotropicSourceNormalization sourceShading scale) 8
    levelCount (fun index => volume (popular.restricted.carrier index))

/-- Construct the CWA-compatible source box at width `1/(100*scale)`. -/
theorem pureWZ2_final_isotropic_box_preparation
    {sourceDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    {sourceConstant scheduleConstant : ENNReal}
    (ambientCWA : WZ2PaperPureCWAAtNearbyScales
      sourceFamily sourceConstant)
    (hfamily : sourceFamily.Nonempty)
    (hsourceDeltaOne : sourceDelta ≤ 1)
    (hsourceMass : 0 < sourceShading.mass)
    (scale : ℝ) (hscale : 1 ≤ scale)
    (hscaleDelta : scale * sourceDelta ≤ 1 / 1000)
    (levelCount : ℕ)
    (hsourceTwo : 2 < sourceConstant)
    (hlevels : ENNReal.ofReal (1 / sourceDelta) ≤
      sourceConstant ^ levelCount)
    (hscheduleFinite : WZ2PaperFiniteErrorConstant scheduleConstant)
    (hscheduleConstant : sourceConstant * sourceConstant ≤ scheduleConstant) :
    Nonempty (PureWZ2FinalIsotropicBoxPreparationData sourceShading
      sourceConstant scheduleConstant levelCount scale) := by
  have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
  have hsourceDelta : 0 < sourceDelta := ambientCWA.1
  have hwidth : 0 < pureWZ2FinalIsotropicSourceWidth scale := by
    unfold pureWZ2FinalIsotropicSourceWidth
    positivity
  have hwidthOne : pureWZ2FinalIsotropicSourceWidth scale ≤ 1 := by
    unfold pureWZ2FinalIsotropicSourceWidth
    apply (div_le_one (mul_pos (by norm_num) hscalePos)).2
    nlinarith
  rcases pureWZ2_final_anisotropic_popular_box sourceShading hwidth hwidthOne
      hsourceDelta hsourceDeltaOne with
    ⟨popular⟩
  have hcardZero : sourceFamily.enncard ≠ 0 := by
    change (sourceFamily.card : ENNReal) ≠ 0
    exact_mod_cast hfamily.ne'
  have hcardTop : sourceFamily.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hfactor : 0 < ENNReal.ofReal
      ((pureWZ2FinalIsotropicSourceWidth scale ^ 2 / 9) *
        (sourceDelta / 3)) := by
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hnormalizationZero :
      pureWZ2FinalIsotropicSourceNormalization sourceShading scale ≠ 0 := by
    unfold pureWZ2FinalIsotropicSourceNormalization
    exact (ENNReal.div_pos
      (ENNReal.mul_pos hfactor.ne' hsourceMass.ne').ne' hcardTop).ne'
  have hnormalizationTop :
      pureWZ2FinalIsotropicSourceNormalization sourceShading scale ≠ ⊤ := by
    have hmassTop : sourceShading.mass ≠ ⊤ := by
      change (∑ index, volume (sourceShading.carrier index)) ≠ ⊤
      apply ENNReal.sum_ne_top.mpr
      intro index _
      have hsubset : sourceShading.carrier index ⊆
          Kakeya.Streamlined.axisBox 2 2 2 := fun point hpoint =>
        (sourceShading.subset_body index hpoint).2
      apply ne_top_of_le_ne_top (b := volume
        (Kakeya.Streamlined.axisBox 2 2 2))
      · rw [Kakeya.Streamlined.volume_axisBox 2 2 2] <;> norm_num
      · exact measure_mono hsubset
    unfold pureWZ2FinalIsotropicSourceNormalization
    exact ENNReal.div_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        hmassTop) hcardZero
  have hmass : pureWZ2FinalIsotropicSourceNormalization sourceShading scale *
      sourceFamily.enncard ≤ popular.restricted.mass := by
    unfold pureWZ2FinalIsotropicSourceNormalization
    rw [ENNReal.div_mul_cancel hcardZero hcardTop]
    rw [ENNReal.ofReal_mul (by positivity)]
    calc
      ENNReal.ofReal (pureWZ2FinalIsotropicSourceWidth scale ^ 2 / 9) *
          ENNReal.ofReal (sourceDelta / 3) * sourceShading.mass =
        ENNReal.ofReal (sourceDelta / 3) *
          (ENNReal.ofReal (pureWZ2FinalIsotropicSourceWidth scale ^ 2 / 9) *
            sourceShading.mass) := by ring
      _ ≤ popular.restricted.mass := popular.mass_lower
  have hweight : ∀ index, volume (popular.restricted.carrier index) ≤
      (8 : ENNReal) := by
    intro index
    have hsubset : popular.restricted.carrier index ⊆
        Kakeya.Streamlined.axisBox 2 2 2 := fun point hpoint =>
      (popular.restricted.subset_body index hpoint).2
    calc
      volume (popular.restricted.carrier index) ≤
          volume (Kakeya.Streamlined.axisBox 2 2 2) := measure_mono hsubset
      _ = 8 := by
        rw [Kakeya.Streamlined.volume_axisBox 2 2 2] <;> norm_num
  rcases pureWZ2_external_weight_regularization ambientCWA hfamily
      hsourceDeltaOne hscheduleFinite hnormalizationZero hnormalizationTop
      (by norm_num) (fun index => volume (popular.restricted.carrier index))
      hmass hweight levelCount hsourceTwo hlevels hscheduleConstant with
    ⟨regularized⟩
  exact ⟨{ popular := popular, regularized := regularized }⟩

namespace PureWZ2FinalIsotropicBoxPreparationData

/-- The source shading on precisely the CWA-compatible selected indices. -/
def selectedShading
    {sourceDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant scheduleConstant : ENNReal}
    {levelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicBoxPreparationData sourceShading
      sourceConstant scheduleConstant levelCount scale) :
    WZ1PaperTubeShading data.regularized.selected.family :=
  restrictPaperShading data.regularized.selected data.popular.restricted

@[simp] theorem selectedShading_carrier
    {sourceDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant scheduleConstant : ENNReal}
    {levelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicBoxPreparationData sourceShading
      sourceConstant scheduleConstant levelCount scale)
    (index : Fin data.regularized.selected.family.card) :
    data.selectedShading.carrier index =
      data.popular.restricted.carrier
        (data.regularized.selected.embedding index) := rfl

theorem selectedShading_mass_eq_selectedWeight
    {sourceDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant scheduleConstant : ENNReal}
    {levelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicBoxPreparationData sourceShading
      sourceConstant scheduleConstant levelCount scale) :
    data.selectedShading.mass = data.regularized.selectedWeight := by
  rw [data.regularized.selectedWeight_eq]
  rfl

/-- Ratio-aware output envelope for the first final-isotropic source
regularization.  A per-source mass floor cancels the ambient source
cardinality in the box normalization before the fixed weight upper bound is
introduced. -/
theorem outputConstant_le_ratioEnvelope_of_massFloor
    {sourceDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant scheduleConstant ambientBound scheduleBound
      ratioBound logEnvelope massFloor : ENNReal}
    {levelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicBoxPreparationData sourceShading
      sourceConstant scheduleConstant levelCount scale)
    (hfamily : sourceFamily.Nonempty)
    (hmass : massFloor * sourceFamily.enncard ≤ sourceShading.mass)
    (hambient : sourceConstant ≤ ambientBound)
    (hschedule : scheduleConstant ≤ scheduleBound)
    (hratioFloor :
      (ENNReal.ofReal
          ((pureWZ2FinalIsotropicSourceWidth scale ^ 2 / 9) *
            (sourceDelta / 3)) * massFloor)⁻¹ * 8 ≤ ratioBound)
    (hlog : (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ≤
      logEnvelope)
    (hlogOne : 1 ≤ logEnvelope) :
    data.regularized.outputConstant ≤
      PureWZ2ExternalWeightRegularizationData.pureWZ2ExternalWeightRatioOutputEnvelope
        ambientBound scheduleBound ratioBound logEnvelope levelCount := by
  apply data.regularized.outputConstant_le_externalWeightRatioOutputEnvelope
    hambient hschedule
  · exact pureWZ2FinalIsotropicSourceNormalization_inv_mul_eight_le
      sourceShading scale hfamily hmass hratioFloor
  · exact hlog
  · exact hlogOne

theorem selectedShading_mass_pos
    {sourceDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant scheduleConstant : ENNReal}
    {levelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicBoxPreparationData sourceShading
      sourceConstant scheduleConstant levelCount scale) :
    0 < data.selectedShading.mass := by
  let index : Fin data.regularized.selected.family.card :=
    ⟨0, data.regularized.selected_nonempty⟩
  have hterm : 0 < volume (data.selectedShading.carrier index) := by
    rw [data.selectedShading_carrier]
    exact data.regularized.selected_weight_pos index
  exact hterm.trans_le <| Finset.single_le_sum
    (fun other (_ : other ∈ Finset.univ) =>
      (show (0 : ENNReal) ≤ volume
        (data.selectedShading.carrier other) from bot_le))
    (Finset.mem_univ index)

theorem selectedShading_union_subset_ball
    {sourceDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant scheduleConstant : ENNReal}
    {levelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicBoxPreparationData sourceShading
      sourceConstant scheduleConstant levelCount scale)
    (hscale : 1 ≤ scale)
    (hscaleDelta : scale * sourceDelta ≤ 1 / 1000) :
    data.selectedShading.union ⊆
      Metric.closedBall data.popular.center (1 / (2 * scale)) := by
  intro point hpoint
  have hrestricted : point ∈ data.popular.restricted.union :=
    restrictPaperShading_union_subset data.regularized.selected
      data.popular.restricted hpoint
  have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
  have hsourceDelta : 0 < sourceDelta := data.regularized.cwa_nearby.1
  have hheightWidth : sourceDelta ≤
      pureWZ2FinalIsotropicSourceWidth scale := by
    unfold pureWZ2FinalIsotropicSourceWidth
    rw [le_div_iff₀ (mul_pos (by norm_num) hscalePos)]
    calc
      sourceDelta * (100 * scale) = 100 * (scale * sourceDelta) := by ring
      _ ≤ 100 * (1 / 1000 : ℝ) := by gcongr
      _ ≤ 1 := by norm_num
  have hball := data.popular.restricted_union_subset_ball
    (show 0 ≤ pureWZ2FinalIsotropicSourceWidth scale by
      unfold pureWZ2FinalIsotropicSourceWidth
      positivity) hheightWidth hrestricted
  rw [Metric.mem_closedBall] at hball ⊢
  have hsqrtThree : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg 3]
  have hwidthNonneg :
      0 ≤ pureWZ2FinalIsotropicSourceWidth scale / 2 := by
    unfold pureWZ2FinalIsotropicSourceWidth
    positivity
  calc
    dist point data.popular.center ≤
        Real.sqrt 3 *
          (pureWZ2FinalIsotropicSourceWidth scale / 2) := hball
    _ ≤ 2 *
        (pureWZ2FinalIsotropicSourceWidth scale / 2) := by gcongr
    _ = pureWZ2FinalIsotropicSourceWidth scale := by ring
    _ = 1 / (100 * scale) := rfl
    _ ≤ 1 / (2 * scale) := by
      have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
      apply (div_le_div_iff₀ (mul_pos (by norm_num) hscalePos)
        (mul_pos (by norm_num) hscalePos)).2
      nlinarith

/-- The source box is also no taller than one pre-isotropic grid cell.  This
is the quantitative input that keeps the later source-height decomposition
uniformly finite. -/
theorem selectedShading_height_close
    {sourceDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant scheduleConstant : ENNReal}
    {levelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicBoxPreparationData sourceShading
      sourceConstant scheduleConstant levelCount scale)
    {point : Point3} (hpoint : point ∈ data.selectedShading.union) :
    |point 2 - data.popular.center 2| ≤ sourceDelta / 2 := by
  have hrestricted : point ∈ data.popular.restricted.union :=
    restrictPaperShading_union_subset data.regularized.selected
      data.popular.restricted hpoint
  exact data.popular.height_close point hrestricted

/-- After the final similarity, the exact image of the selected source box is
contained in a fixed ball around the origin. -/
theorem isotropicSelectedImage_norm_le
    {sourceDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant scheduleConstant : ENNReal}
    {levelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicBoxPreparationData sourceShading
      sourceConstant scheduleConstant levelCount scale)
    (hscale : 1 ≤ scale)
    (hscaleDelta : scale * sourceDelta ≤ 1 / 1000) :
    ∀ point : {point : Point3 // point ∈
      pureWZ2IsotropicMap data.popular.center scale ''
        data.selectedShading.union},
      ‖(point : Point3)‖ ≤ Real.sqrt 3 / 200 := by
  rintro ⟨_, source, hsource, rfl⟩
  have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
  have hrestricted : source ∈ data.popular.restricted.union :=
    restrictPaperShading_union_subset data.regularized.selected
      data.popular.restricted hsource
  have hheightWidth : sourceDelta ≤
      pureWZ2FinalIsotropicSourceWidth scale := by
    unfold pureWZ2FinalIsotropicSourceWidth
    rw [le_div_iff₀ (mul_pos (by norm_num) hscalePos)]
    calc
      sourceDelta * (100 * scale) = 100 * (scale * sourceDelta) := by ring
      _ ≤ 100 * (1 / 1000 : ℝ) := by gcongr
      _ ≤ 1 := by norm_num
  have hsourceBall := data.popular.restricted_union_subset_ball
    (show 0 ≤ pureWZ2FinalIsotropicSourceWidth scale by
      unfold pureWZ2FinalIsotropicSourceWidth
      positivity) hheightWidth hrestricted
  rw [Metric.mem_closedBall, dist_eq_norm] at hsourceBall
  simp only [pureWZ2IsotropicMap, norm_smul, Real.norm_eq_abs,
    abs_of_pos hscalePos]
  calc
    scale * ‖source - data.popular.center‖ ≤
        scale * (Real.sqrt 3 *
          (pureWZ2FinalIsotropicSourceWidth scale / 2)) := by
            gcongr
    _ = Real.sqrt 3 / 200 := by
      unfold pureWZ2FinalIsotropicSourceWidth
      field_simp [hscalePos.ne']
      ring

/-- The anisotropic final box keeps the exact target height at the
pre-isotropic scale, independently of the horizontal normalization width. -/
theorem isotropicSelectedImage_height_abs_le
    {sourceDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant scheduleConstant : ENNReal}
    {levelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicBoxPreparationData sourceShading
      sourceConstant scheduleConstant levelCount scale)
    (hscale : 1 ≤ scale) :
    ∀ point : {point : Point3 // point ∈
      pureWZ2IsotropicMap data.popular.center scale ''
        data.selectedShading.union},
      |(point : Point3) 2| ≤ scale * sourceDelta / 2 := by
  rintro ⟨_, source, hsource, rfl⟩
  have hsourceRestricted : source ∈ data.popular.restricted.union :=
    restrictPaperShading_union_subset data.regularized.selected
      data.popular.restricted hsource
  have hheight := data.popular.height_close source hsourceRestricted
  have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
  change |scale * (source 2 - data.popular.center 2)| ≤
    scale * sourceDelta / 2
  rw [abs_mul, abs_of_pos hscalePos]
  nlinarith

/-- Every selected source tube has a genuine point in the chosen box. -/
theorem selectedCarrier_nonempty
    {sourceDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant scheduleConstant : ENNReal}
    {levelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicBoxPreparationData sourceShading
      sourceConstant scheduleConstant levelCount scale)
    (index : Fin data.regularized.selected.family.card) :
    (data.popular.restricted.carrier
      (data.regularized.selected.embedding index)).Nonempty := by
  have hpositive := data.regularized.selected_weight_pos index
  exact nonempty_of_measure_ne_zero hpositive.ne'

/-- A selected tube axis at the isotropic center is uniformly close enough
that its image height-zero point lies in the fixed `1/3` chart. -/
theorem isotropic_zeroPoint_bound
    {sourceDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant scheduleConstant : ENNReal}
    {levelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicBoxPreparationData sourceShading
      sourceConstant scheduleConstant levelCount scale)
    (hsourceDelta : 0 < sourceDelta) (hscale : 1 ≤ scale)
    (hscaleDelta : scale * sourceDelta ≤ 1 / 1000)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (index : Fin data.regularized.selected.family.card)
    (coordinate : Fin 2) :
    |(pureWZ2IsotropicMap data.popular.center scale
      (wz1PaperAxisPointAtHeight
        (data.regularized.selected.family.tube index)
        (data.popular.center 2))) coordinate.castSucc| ≤ 1 / 3 := by
  rcases data.selectedCarrier_nonempty index with ⟨point, hpoint⟩
  have hpointAmbient := data.popular.restricted_subshading
    (data.regularized.selected.embedding index) hpoint
  have hheight : |data.popular.center 2 - point 2| ≤
      sourceDelta / 2 := by
    simpa [abs_sub_comm] using data.popular.height_close point
      ⟨_, hpoint⟩
  have hbound := pureWZ2_paperAxis_center_coordinate_bound hsourceDelta
    (hsourceLine (data.regularized.selected.embedding index))
    data.popular.center
    (point3 (pureWZ2FinalIsotropicSourceWidth scale / 2)
      (pureWZ2FinalIsotropicSourceWidth scale / 2)
      (sourceDelta / 2)) point
    (sourceShading.subset_body
      (data.regularized.selected.embedding index) hpointAmbient)
    (by
      intro axis
      fin_cases axis
      · simpa [point3] using
          (data.popular.horizontal_close point ⟨_, hpoint⟩).1
      · simpa [point3] using
          (data.popular.horizontal_close point ⟨_, hpoint⟩).2
      · simpa [point3] using data.popular.height_close point ⟨_, hpoint⟩)
    (by simpa [point3] using hheight)
    coordinate.castSucc
  rw [data.regularized.selected.tube_eq]
  simp only [pureWZ2IsotropicMap, PiLp.smul_apply, smul_eq_mul,
    PiLp.sub_apply]
  have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
  have hwidthLe : scale *
      pureWZ2FinalIsotropicSourceWidth scale ≤ 1 / 100 := by
    unfold pureWZ2FinalIsotropicSourceWidth
    field_simp [hscalePos.ne']
    norm_num
  have hbound' :
      |(wz1PaperAxisPointAtHeight
          (sourceFamily.tube (data.regularized.selected.embedding index))
          (data.popular.center 2) - data.popular.center)
          coordinate.castSucc| ≤
        2 * (sourceDelta / 2) + 18 * sourceDelta +
          pureWZ2FinalIsotropicSourceWidth scale / 2 := by
    have hhalfTwo :
        (point3 (pureWZ2FinalIsotropicSourceWidth scale / 2)
          (pureWZ2FinalIsotropicSourceWidth scale / 2)
          (sourceDelta / 2)) (2 : Fin 3) = sourceDelta / 2 := by
      simp [point3, PiLp.single_apply]
    have hhalfCoordinate :
        (point3 (pureWZ2FinalIsotropicSourceWidth scale / 2)
          (pureWZ2FinalIsotropicSourceWidth scale / 2)
          (sourceDelta / 2))
            coordinate.castSucc =
        pureWZ2FinalIsotropicSourceWidth scale / 2 := by
      fin_cases coordinate <;> simp [point3, PiLp.single_apply]
    calc
      _ ≤ 2 * (sourceDelta / 2) +
            18 * sourceDelta +
          (point3 (pureWZ2FinalIsotropicSourceWidth scale / 2)
            (pureWZ2FinalIsotropicSourceWidth scale / 2)
            (sourceDelta / 2)) coordinate.castSucc :=
        by simpa only [hhalfTwo] using hbound
      _ = 2 * (sourceDelta / 2) + 18 * sourceDelta +
          pureWZ2FinalIsotropicSourceWidth scale / 2 := by
        rw [hhalfCoordinate]
  rw [abs_mul, abs_of_nonneg (lt_of_lt_of_le (by norm_num) hscale).le]
  calc
    scale * |(wz1PaperAxisPointAtHeight
        (sourceFamily.tube (data.regularized.selected.embedding index))
        (data.popular.center 2) - data.popular.center) coordinate.castSucc|
        ≤ scale *
          (2 * (sourceDelta / 2) + 18 * sourceDelta +
            pureWZ2FinalIsotropicSourceWidth scale / 2) := by gcongr
    _ ≤ 1 / 200 + 19 * (scale * sourceDelta) := by
      calc
        scale *
          (2 * (sourceDelta / 2) + 18 * sourceDelta +
            pureWZ2FinalIsotropicSourceWidth scale / 2) =
          19 * (scale * sourceDelta) +
            (scale * pureWZ2FinalIsotropicSourceWidth scale) / 2 := by ring
        _ ≤ _ := by nlinarith [hwidthLe]
    _ ≤ 1 / 3 := by nlinarith

end PureWZ2FinalIsotropicBoxPreparationData

end Kakeya.Assouad

end
