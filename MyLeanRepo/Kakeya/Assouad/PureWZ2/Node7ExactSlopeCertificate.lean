import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7AffineDiagonalPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7LocalIntervalSlopeExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7SlopeNormalization

/-!
# Exact normalized slope certificate for Node 7

The quotient formula is used only on the actual target-height interval of the
transformed shading.  Its two-jet is then extended as a representation
adapter.  All mathematical bounds are proved only on `[-1,1]`.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

namespace PureWZ2Node7AffineDiagonalPreparationData

abbrev affineScale
    {logExponent : ℕ} {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :=
  data.node7Scale.affineScale

def exactSlopeValue
    {logExponent : ℕ} {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    ℝ → ℝ :=
  node7ExactNormalizedSlopeValue
    commonSource.commonBand.band.lemma31.data.globalSlope
    data.affineScale.slopeData.frameSlope
    data.affineScale.slopeData.anchor
    data.affineScale.slopeData.heightScale
    data.affineScale.slopeData.transverseScale

/-- The target-height interval corresponding exactly to the retained source
interval `[z1,z1+ell]`.  For Node 7 its left endpoint is zero. -/
def activeLeft
    {logExponent : ℕ} {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) : ℝ :=
  data.affineScale.slopeData.heightScale *
    (commonSource.subband.left - data.affineScale.slopeData.anchor)

def activeRight
    {logExponent : ℕ} {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) : ℝ :=
  data.affineScale.slopeData.heightScale *
    (commonSource.subband.right - data.affineScale.slopeData.anchor)

@[simp] theorem activeLeft_eq_zero
    {logExponent : ℕ} {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.activeLeft = 0 := by
  rw [activeLeft, data.node7Scale.anchor_left]
  ring

theorem active_ordered
    {logExponent : ℕ} {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.activeLeft < data.activeRight := by
  unfold activeLeft activeRight
  have hheight : 0 < data.affineScale.slopeData.heightScale :=
    lt_of_lt_of_le (by norm_num) data.affineScale.height_lower
  nlinarith [commonSource.subband.ordered]

theorem active_interval_bounds
    {logExponent : ℕ} {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    0 ≤ data.activeLeft ∧ data.activeRight ≤ 1 / 2 := by
  constructor
  · rw [data.activeLeft_eq_zero]
  · have hrho : 0 < commonSource.commonBand.band.lemma31.data.rho.1 :=
      commonSource.commonBand.band.lemma31.data.cfg.extremal.delta_pos.trans_le
        commonSource.commonBand.band.lemma31.data.rho.2.1
    have hheightUpper : data.affineScale.slopeData.heightScale ≤
        2500 / commonSource.commonBand.band.lemma31.data.rho.1 := by
      exact data.node7Scale.height_upper_2500
    have hlengthNonneg :
        0 ≤ commonSource.subband.right - commonSource.subband.left :=
      sub_nonneg.mpr commonSource.subband.ordered.le
    rw [activeRight, data.node7Scale.anchor_left]
    calc
      data.affineScale.slopeData.heightScale *
            (commonSource.subband.right - commonSource.subband.left) ≤
          (2500 / commonSource.commonBand.band.lemma31.data.rho.1) *
            (commonSource.subband.right - commonSource.subband.left) := by
        exact mul_le_mul_of_nonneg_right hheightUpper hlengthNonneg
      _ = (2500 / commonSource.commonBand.band.lemma31.data.rho.1) *
            (commonSource.commonBand.band.lemma31.data.rho.1 / 5000) := by
        rw [commonSource.subband.length_eq,
          commonSource.commonBand.band.length_eq]
        ring
      _ = 1 / 2 := by
        field_simp [hrho.ne']
        norm_num

@[simp] theorem exactSlopeValue_zero
    {logExponent : ℕ} {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.exactSlopeValue 0 = 0 := by
  unfold exactSlopeValue node7ExactNormalizedSlopeValue
  rw [data.node7Scale.anchor_left, data.node7Scale.frame_at_left]
  simp [node7MobiusRotatedValue]

theorem sourceHeight_mem_subband
    {logExponent : ℕ} {sigma epsilon delta t : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (ht : t ∈ Set.Icc data.activeLeft data.activeRight) :
    data.affineScale.slopeData.anchor +
        t / data.affineScale.slopeData.heightScale ∈
      Set.Icc commonSource.subband.left commonSource.subband.right := by
  have hheight : 0 < data.affineScale.slopeData.heightScale :=
    lt_of_lt_of_le (by norm_num) data.affineScale.height_lower
  unfold activeLeft activeRight at ht
  constructor
  · have hquot : commonSource.subband.left -
        data.affineScale.slopeData.anchor ≤
        t / data.affineScale.slopeData.heightScale := by
      apply (le_div_iff₀ hheight).2
      nlinarith [ht.1]
    linarith
  · have hquot : t / data.affineScale.slopeData.heightScale ≤
        commonSource.subband.right -
          data.affineScale.slopeData.anchor := by
      apply (div_le_iff₀ hheight).2
      nlinarith [ht.2]
    linarith

theorem denominator_bounds
    {logExponent : ℕ} {sigma epsilon delta t : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (ht : t ∈ Set.Icc data.activeLeft data.activeRight) :
    let q := data.affineScale.slopeData.frameSlope
    let u := commonSource.commonBand.band.lemma31.data.globalSlope
      (data.affineScale.slopeData.anchor +
        t / data.affineScale.slopeData.heightScale)
    let B := 1 + q ^ 2
    (99 / 100 : ℝ) * B ≤ 1 + q * u ∧
      1 + q * u ≤ (101 / 100 : ℝ) * B := by
  dsimp only
  let source := commonSource.commonBand.band.lemma31.data.globalSlope
  let anchor := data.affineScale.slopeData.anchor
  let z := anchor + t / data.affineScale.slopeData.heightScale
  have hz := data.sourceHeight_mem_subband ht
  have hanchor := data.affineScale.slope_anchor_mem
  have hinterval : Set.Icc commonSource.subband.left commonSource.subband.right ⊆
      Set.Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨commonSource.commonBand.band.lemma31.data.scaleData.slabLeft_mem.trans
        (commonSource.commonBand.band.left_mem.trans <|
          commonSource.subband.left_mem.trans hx.1),
      hx.2.trans <| commonSource.subband.right_mem.trans <|
        commonSource.commonBand.band.right_mem.trans
          commonSource.commonBand.band.lemma31.data.scaleData.slabRight_mem⟩
  have hsourceDiff : |source z - source anchor| ≤
      |z - anchor| :=
    pureWZ2_normalized_slope_value_difference source
      commonSource.commonBand.band.lemma31.data.globalSlope_normalized
      (hinterval <| ⟨le_rfl, commonSource.subband.ordered.le⟩).1
      (hinterval <| ⟨commonSource.subband.ordered.le, le_rfl⟩).2
      commonSource.subband.ordered.le hanchor hz
  have hzDist : |z - anchor| ≤ commonSource.subband.right -
      commonSource.subband.left := by
    rw [abs_le]
    constructor <;> linarith [hanchor.1, hanchor.2, hz.1, hz.2]
  have hsmall : |source z - source anchor| ≤ 1 / 100 := by
    calc
      |source z - source anchor| ≤ |z - anchor| := hsourceDiff
      _ ≤ commonSource.subband.right - commonSource.subband.left := hzDist
      _ = commonSource.commonBand.band.lemma31.data.rho.1 / 5000 := by
        rw [commonSource.subband.length_eq,
          commonSource.commonBand.band.length_eq]
        ring
      _ ≤ 1 / 100 := by
        linarith [commonSource.commonBand.band.lemma31.rho_tiny]
  have hq : |data.affineScale.slopeData.frameSlope| ≤ 1 :=
    data.affineScale.slopeData.frameSlope_bound
  have hsmallFrame : |source z -
      data.affineScale.slopeData.frameSlope| ≤ 1 / 100 := by
    rw [data.node7Scale.frame_at_left]
    simpa [anchor, data.node7Scale.anchor_left] using hsmall
  have hlower := node7Mobius_denominator_lower hq hsmallFrame
  have hproduct : |data.affineScale.slopeData.frameSlope *
      (source z - data.affineScale.slopeData.frameSlope)| ≤ 1 / 100 := by
    rw [abs_mul]
    nlinarith [abs_nonneg data.affineScale.slopeData.frameSlope,
      abs_nonneg (source z - data.affineScale.slopeData.frameSlope)]
  have hproductBounds := abs_le.mp hproduct
  rw [data.node7Scale.frame_at_left]
  change _ ∧ _
  constructor
  · exact (show (99 / 100 : ℝ) *
        (1 + source commonSource.subband.left ^ 2) ≤
        1 + source commonSource.subband.left * source z by
      have hqBound := hq
      rw [data.node7Scale.frame_at_left] at hqBound
      rw [show 1 + source commonSource.subband.left * source z =
          1 + source commonSource.subband.left ^ 2 +
            source commonSource.subband.left *
              (source z - source commonSource.subband.left) by ring]
      rw [data.node7Scale.frame_at_left] at hproductBounds
      nlinarith [sq_nonneg (source commonSource.subband.left)])
  · rw [show 1 + source commonSource.subband.left * source z =
        1 + source commonSource.subband.left ^ 2 +
          source commonSource.subband.left *
            (source z - source commonSource.subband.left) by ring]
    have hqBound := hq
    rw [data.node7Scale.frame_at_left] at hqBound
    rw [data.node7Scale.frame_at_left] at hproductBounds
    nlinarith [sq_nonneg (source commonSource.subband.left)]

theorem exactSlope_contDiffAt_on_active
    {logExponent : ℕ} {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    ∀ t ∈ Set.Icc data.activeLeft data.activeRight,
      ContDiffAt ℝ 2 data.exactSlopeValue t := by
  intro t ht
  have hbounds := data.denominator_bounds ht
  have hdenomPos : 0 < 1 + data.affineScale.slopeData.frameSlope *
      commonSource.commonBand.band.lemma31.data.globalSlope
        (data.affineScale.slopeData.anchor +
          t / data.affineScale.slopeData.heightScale) := by
    exact (mul_pos (by norm_num) (by positivity)).trans_le hbounds.1
  exact node7ExactNormalizedSlopeValue_contDiffAt
    commonSource.commonBand.band.lemma31.data.globalSlope
    data.affineScale.slopeData.frameSlope
    data.affineScale.slopeData.anchor
    data.affineScale.slopeData.heightScale
    data.affineScale.slopeData.transverseScale t hdenomPos.ne'

theorem exactSlope_first_derivative_bounds_on_active
    {logExponent : ℕ} {sigma epsilon delta t : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (ht : t ∈ Set.Icc data.activeLeft data.activeRight) :
    (6 / 5 : ℝ) ≤ |deriv data.exactSlopeValue t| ∧
      |deriv data.exactSlopeValue t| ≤ 9 / 5 := by
  let source := commonSource.commonBand.band.lemma31.data.globalSlope
  let q := data.affineScale.slopeData.frameSlope
  let z := data.affineScale.slopeData.anchor +
    t / data.affineScale.slopeData.heightScale
  let B := 1 + q ^ 2
  let D := 1 + q * source z
  let m := commonSource.commonBand.band.slopeScale
  let gamma := data.affineScale.slopeData.rotatedSlopeScale
  have hz := data.sourceHeight_mem_subband ht
  have hzBand : z ∈ Set.Icc commonSource.commonBand.band.left
      commonSource.commonBand.band.right :=
    ⟨commonSource.subband.left_mem.trans hz.1,
      hz.2.trans commonSource.subband.right_mem⟩
  have hsourceDerivative :=
    commonSource.commonBand.band.derivative_band z hzBand
  have hsourceTight :=
    commonSource.commonBand.band.derivative_tight_upper z hzBand
  have hxUpper : |deriv source z| ≤ (51 / 50 : ℝ) * m := by
    calc
      |deriv source z| ≤ m +
          commonSource.commonBand.band.lemma31.data.rho.1 / 50 :=
        hsourceTight
      _ ≤ m + m / 50 := by
        gcongr
        exact commonSource.commonBand.band.slopeScale_lower
      _ = (51 / 50 : ℝ) * m := by ring
  have hdenom := data.denominator_bounds ht
  have hBOne : 1 ≤ B := by
    dsimp only [B]
    nlinarith [sq_nonneg q]
  have hDPos : 0 < D := by
    dsimp only [D]
    exact (mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hBOne)).trans_le
      hdenom.1
  have hgamma : gamma = (4 / 5 : ℝ) * m / B := by
    dsimp only [gamma, m, B, q]
    rw [data.node7Scale.rotated_scale_eq]
    unfold pureWZ2Node7RotatedSlopeScale
    rw [data.node7Scale.frame_at_left]
  have hheight : data.affineScale.slopeData.heightScale ≠ 0 :=
    (lt_of_lt_of_le (by norm_num) data.affineScale.height_lower).ne'
  have htransverse : data.affineScale.slopeData.transverseScale ≠ 0 :=
    data.affineScale.transverse_pos.ne'
  have hderivFormula := node7ExactNormalizedSlopeValue_deriv source q
    data.affineScale.slopeData.anchor hheight htransverse t hDPos.ne'
  have hscaling :
      B * deriv source z / D ^ 2 /
          data.affineScale.slopeData.heightScale /
            data.affineScale.slopeData.transverseScale =
        B * deriv source z / D ^ 2 / gamma := by
    rw [data.affineScale.slopeData.heightScale_eq,
      data.affineScale.slopeData.transverseScale_eq,
      data.node7Scale.normalization_thousand]
    have hgammaPos : 0 < gamma := by
      dsimp only [gamma]
      exact data.affineScale.slopeData.rotatedSlopeScale_pos
    dsimp only [gamma]
    field_simp [data.affineScale.slopeData.rotatedSlopeScale_pos.ne']
  have hnumeric := node7_normalized_first_derivative_bounds
    hBOne commonSource.commonBand.band.slopeScale_pos hgamma hDPos
    hdenom.1 hdenom.2 hsourceDerivative.1 hxUpper
  change (6 / 5 : ℝ) ≤
      |deriv (node7ExactNormalizedSlopeValue source q
        data.affineScale.slopeData.anchor
        data.affineScale.slopeData.heightScale
        data.affineScale.slopeData.transverseScale) t| ∧
      |deriv (node7ExactNormalizedSlopeValue source q
        data.affineScale.slopeData.anchor
        data.affineScale.slopeData.heightScale
        data.affineScale.slopeData.transverseScale) t| ≤ 9 / 5
  rw [hderivFormula]
  change _ ≤ |B * deriv source z / D ^ 2 /
      data.affineScale.slopeData.heightScale /
        data.affineScale.slopeData.transverseScale| ∧
    |B * deriv source z / D ^ 2 /
      data.affineScale.slopeData.heightScale /
        data.affineScale.slopeData.transverseScale| ≤ 9 / 5
  rw [hscaling]
  exact hnumeric

theorem exactSlope_second_derivative_abs_le_on_active
    {logExponent : ℕ} {sigma epsilon delta t : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (ht : t ∈ Set.Icc data.activeLeft data.activeRight) :
    |deriv (deriv data.exactSlopeValue) t| ≤ 1 / 200 := by
  let source := commonSource.commonBand.band.lemma31.data.globalSlope
  let q := data.affineScale.slopeData.frameSlope
  let z := data.affineScale.slopeData.anchor +
    t / data.affineScale.slopeData.heightScale
  let B := 1 + q ^ 2
  let D := 1 + q * source z
  let m := commonSource.commonBand.band.slopeScale
  have hz := data.sourceHeight_mem_subband ht
  have hzBand : z ∈ Set.Icc commonSource.commonBand.band.left
      commonSource.commonBand.band.right :=
    ⟨commonSource.subband.left_mem.trans hz.1,
      hz.2.trans commonSource.subband.right_mem⟩
  have hzPaper : z ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨commonSource.commonBand.band.lemma31.data.scaleData.slabLeft_mem.trans
        (commonSource.commonBand.band.left_mem.trans hzBand.1),
      hzBand.2.trans <| commonSource.commonBand.band.right_mem.trans
        commonSource.commonBand.band.lemma31.data.scaleData.slabRight_mem⟩
  have hsourceTight :=
    commonSource.commonBand.band.derivative_tight_upper z hzBand
  have hfirst : |deriv source z| ≤ (51 / 50 : ℝ) * m := by
    calc
      |deriv source z| ≤ m +
          commonSource.commonBand.band.lemma31.data.rho.1 / 50 :=
        hsourceTight
      _ ≤ m + m / 50 := by
        gcongr
        exact commonSource.commonBand.band.slopeScale_lower
      _ = (51 / 50 : ℝ) * m := by ring
  have hsecond : |deriv (deriv source) z| ≤ 1 :=
    (commonSource.commonBand.band.lemma31.data.globalSlope_normalized
      z hzPaper).2.2
  have hq : |q| ≤ 1 := data.affineScale.slopeData.frameSlope_bound
  have hBOne : 1 ≤ B := by
    dsimp only [B]
    nlinarith [sq_nonneg q]
  have hBTwo : B ≤ 2 := by
    dsimp only [B]
    rcases abs_le.mp hq with ⟨hqLower, hqUpper⟩
    nlinarith [sq_nonneg (q - 1), sq_nonneg (q + 1)]
  have hdenom := data.denominator_bounds ht
  have hDPos : 0 < D := by
    dsimp only [D]
    exact (mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hBOne)).trans_le
      hdenom.1
  have hmobius := node7_mobius_second_derivative_abs_le_five
    hBOne hBTwo commonSource.commonBand.band.slopeScale_pos
    commonSource.commonBand.band.slopeScale_le_one hq hDPos
    hdenom.1 hfirst hsecond
  have hheight : data.affineScale.slopeData.heightScale ≠ 0 :=
    (lt_of_lt_of_le (by norm_num) data.affineScale.height_lower).ne'
  have htransverse : data.affineScale.slopeData.transverseScale ≠ 0 :=
    data.affineScale.transverse_pos.ne'
  have hformula := node7ExactNormalizedSlopeValue_second_deriv source q
    data.affineScale.slopeData.anchor hheight htransverse t hDPos.ne'
  have hscaleProduct : data.affineScale.slopeData.heightScale ^ 2 *
      data.affineScale.slopeData.transverseScale = 1000 := by
    rw [data.affineScale.slopeData.heightScale_eq,
      data.affineScale.slopeData.transverseScale_eq,
      data.node7Scale.normalization_thousand]
    have hgamma := data.affineScale.slopeData.rotatedSlopeScale_pos
    field_simp [hgamma.ne']
  change |deriv (deriv (node7ExactNormalizedSlopeValue source q
    data.affineScale.slopeData.anchor
    data.affineScale.slopeData.heightScale
    data.affineScale.slopeData.transverseScale)) t| ≤ _
  rw [hformula]
  change |(B * (deriv (deriv source) z * D -
      2 * q * (deriv source z) ^ 2) / D ^ 3) /
        data.affineScale.slopeData.heightScale ^ 2 /
          data.affineScale.slopeData.transverseScale| ≤ _
  rw [div_div, hscaleProduct, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 1000)]
  norm_num at hmobius ⊢
  linarith

/-- Canonical globally `C²` representation of the exact active slope.  Its
mathematical content remains confined to the active interval and `[-1,1]`. -/
noncomputable def slopeExtensionData
    {logExponent : ℕ} {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    PureWZ2Node7LocalIntervalSlopeExtensionData
      data.exactSlopeValue data.activeLeft data.activeRight
        data.active_ordered.le :=
  Classical.choice <| pureWZ2_node7_localIntervalSlopeExtension
    data.exactSlopeValue data.active_ordered.le
      data.exactSlope_contDiffAt_on_active

def analysisSlope
    {logExponent : ℕ} {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    SlopeFunction :=
  data.slopeExtensionData.slope

theorem analysisSlope_eq_on_active
    {logExponent : ℕ} {sigma epsilon delta t : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (ht : t ∈ Set.Icc data.activeLeft data.activeRight) :
    data.analysisSlope t = data.exactSlopeValue t :=
  data.slopeExtensionData.eq_on t ht

@[simp] theorem analysisSlope_zero
    {logExponent : ℕ} {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.analysisSlope 0 = 0 := by
  rw [data.analysisSlope_eq_on_active]
  · exact data.exactSlopeValue_zero
  · rw [data.activeLeft_eq_zero]
    refine ⟨le_rfl, ?_⟩
    rw [← data.activeLeft_eq_zero]
    exact data.active_ordered.le

theorem analysisSlope_nonsingular
    {logExponent : ℕ} {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.analysisSlope.IsNonsingular := by
  intro t ht
  let projected : ℝ := Set.projIcc data.activeLeft data.activeRight
    data.active_ordered.le t
  have hprojected : projected ∈
      Set.Icc data.activeLeft data.activeRight :=
    (Set.projIcc data.activeLeft data.activeRight
      data.active_ordered.le t).property
  have hcore := data.exactSlope_first_derivative_bounds_on_active hprojected
  have hactiveBounds := data.active_interval_bounds
  have hdistance : |t - projected| ≤ 2 := by
    rw [abs_le]
    constructor <;> dsimp only [projected] at * <;> linarith [ht.1, ht.2,
      hprojected.1, hprojected.2]
  have hderivDiff := data.slopeExtensionData.deriv_sub_proj_abs_le
    (fun x hx => data.exactSlope_second_derivative_abs_le_on_active hx) t
  have hderivDiffSmall :
      |deriv data.analysisSlope t - deriv data.exactSlopeValue projected| ≤
        1 / 100 := by
    calc
      |deriv data.analysisSlope t - deriv data.exactSlopeValue projected| ≤
          (1 / 200 : ℝ) * |t - projected| := hderivDiff
      _ ≤ (1 / 200 : ℝ) * 2 := by gcongr
      _ = 1 / 100 := by norm_num
  have hcoreToSlope :
      |deriv data.exactSlopeValue projected| ≤
        |deriv data.analysisSlope t| + 1 / 100 := by
    calc
      |deriv data.exactSlopeValue projected| ≤
          |deriv data.analysisSlope t| +
            |deriv data.analysisSlope t -
              deriv data.exactSlopeValue projected| := by
        calc
          |deriv data.exactSlopeValue projected| =
              |deriv data.analysisSlope t -
                  (deriv data.analysisSlope t -
                    deriv data.exactSlopeValue projected)| := by ring_nf
          _ ≤ |deriv data.analysisSlope t| +
              |deriv data.analysisSlope t -
                deriv data.exactSlopeValue projected| := abs_sub _ _
      _ ≤ |deriv data.analysisSlope t| + 1 / 100 := by gcongr
  have hSlopeToCore :
      |deriv data.analysisSlope t| ≤
        |deriv data.exactSlopeValue projected| + 1 / 100 := by
    calc
      |deriv data.analysisSlope t| ≤
          |deriv data.exactSlopeValue projected| +
            |deriv data.analysisSlope t -
              deriv data.exactSlopeValue projected| := by
        calc
          |deriv data.analysisSlope t| =
              |deriv data.exactSlopeValue projected +
                (deriv data.analysisSlope t -
                  deriv data.exactSlopeValue projected)| := by ring_nf
          _ ≤ |deriv data.exactSlopeValue projected| +
              |deriv data.analysisSlope t -
                deriv data.exactSlopeValue projected| := by
            exact abs_add_le
              (deriv data.exactSlopeValue projected)
              (deriv data.analysisSlope t -
                deriv data.exactSlopeValue projected)
      _ ≤ |deriv data.exactSlopeValue projected| + 1 / 100 := by gcongr
  have hcurvature := data.slopeExtensionData.second_deriv_abs_le
    (fun x hx => data.exactSlope_second_derivative_abs_le_on_active hx) t
  constructor
  · linarith [hcore.1]
  constructor
  · linarith [hcore.2]
  · exact hcurvature.trans (by norm_num)

end PureWZ2Node7AffineDiagonalPreparationData

end Kakeya.Assouad

end
