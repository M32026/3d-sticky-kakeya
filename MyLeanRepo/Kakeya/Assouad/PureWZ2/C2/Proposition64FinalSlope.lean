import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64IsotropicProjection

/-!
# Final slope after the Proposition 6.4 isotropic similarity

The similarity does not change horizontal slope values, but it changes the
height parameter.  This file records the inverse-height composition and the
margin condition that keeps its source argument inside `[-1,1]`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Pull a slope through the inverse height coordinate of the final isotropic
similarity. -/
def pureWZ2Proposition64FinalSlope
    (sourceSlope : SlopeFunction) (center : Point3) (scale : ℝ) :
    SlopeFunction where
  toFun z := sourceSlope (center 2 + z / scale)
  contDiff := by
    apply sourceSlope.contDiff.comp
    fun_prop

/-- The final slope with the literal domain used in WZ Proposition 6.5. -/
def pureWZ2Proposition64FinalIntervalSlope
    (sourceSlope : SlopeFunction) (center : Point3) (scale : ℝ) :
    PureWZ2C2SlopeFunction :=
  fun z => pureWZ2Proposition64FinalSlope sourceSlope center scale z.1

@[simp] theorem pureWZ2Proposition64FinalIntervalSlope_apply
    (sourceSlope : SlopeFunction) (center : Point3) (scale : ℝ)
    (z : PureWZ2UnitInterval) :
    pureWZ2Proposition64FinalIntervalSlope sourceSlope center scale z =
      sourceSlope (center 2 + z.1 / scale) := rfl

@[simp] theorem pureWZ2Proposition64FinalSlope_apply
    (sourceSlope : SlopeFunction) (center : Point3) (scale z : ℝ) :
    pureWZ2Proposition64FinalSlope sourceSlope center scale z =
      sourceSlope (center 2 + z / scale) := rfl

@[simp] theorem deriv_pureWZ2Proposition64FinalSlope
    (sourceSlope : SlopeFunction) (center : Point3)
    {scale : ℝ} (hscale : 0 < scale) (z : ℝ) :
    deriv (pureWZ2Proposition64FinalSlope sourceSlope center scale) z =
      deriv sourceSlope (center 2 + z / scale) / scale := by
  have hsource : DifferentiableAt ℝ sourceSlope (center 2 + z / scale) :=
    (sourceSlope.contDiff.differentiable (by norm_num)).differentiableAt
  have haffine : HasDerivAt (fun t : ℝ => center 2 + t / scale)
      (1 / scale) z :=
    ((hasDerivAt_id z).div_const scale).const_add (center 2)
  have hcomp := hsource.hasDerivAt.comp z haffine
  convert hcomp.deriv using 1 <;>
    simp [pureWZ2Proposition64FinalSlope, Function.comp_def, div_eq_mul_inv]

@[simp] theorem second_deriv_pureWZ2Proposition64FinalSlope
    (sourceSlope : SlopeFunction) (center : Point3)
    {scale : ℝ} (hscale : 0 < scale) (z : ℝ) :
    deriv (deriv (pureWZ2Proposition64FinalSlope sourceSlope center scale)) z =
      deriv (deriv sourceSlope) (center 2 + z / scale) / scale ^ 2 := by
  have hfirst : deriv (pureWZ2Proposition64FinalSlope sourceSlope center scale) =
      fun t => deriv sourceSlope (center 2 + t / scale) / scale := by
    funext t
    exact deriv_pureWZ2Proposition64FinalSlope sourceSlope center hscale t
  rw [hfirst]
  have hsource : DifferentiableAt ℝ (deriv sourceSlope)
      (center 2 + z / scale) :=
    ((sourceSlope.contDiff.deriv').differentiable_one).differentiableAt
  have haffine : HasDerivAt (fun t : ℝ => center 2 + t / scale)
      (1 / scale) z :=
    ((hasDerivAt_id z).div_const scale).const_add (center 2)
  have hcomp := hsource.hasDerivAt.comp z haffine
  change HasDerivAt
    (fun t : ℝ => deriv sourceSlope (center 2 + t / scale))
    (deriv (deriv sourceSlope) (center 2 + z / scale) * (1 / scale)) z
      at hcomp
  have hdiv := hcomp.div_const scale
  rw [hdiv.deriv]
  field_simp [hscale.ne']

/-- The grid-center margin and the isotropic scale ensure that every target
height in `[-1,1]` pulls back to a source height in the same interval. -/
theorem pureWZ2Proposition64FinalSlope_source_height_mem
    (center : Point3) {width scale z : ℝ}
    (hwidth : 0 < width)
    (hcenter : |center 2| ≤ 1 - width / 2)
    (hscale : 0 < scale)
    (hscaleWidth : 2 ≤ scale * width)
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    center 2 + z / scale ∈ Set.Icc (-1 : ℝ) 1 := by
  have hcenterBounds := abs_le.mp hcenter
  have hzAbs : |z| ≤ 1 := abs_le.mpr hz
  have hreciprocal : 1 / scale ≤ width / 2 := by
    rw [div_le_iff₀ hscale]
    nlinarith
  have hzScaled : |z / scale| ≤ width / 2 := by
    rw [abs_div, abs_of_pos hscale]
    calc
      |z| / scale ≤ 1 / scale := by gcongr
      _ ≤ width / 2 := hreciprocal
  rw [abs_le] at hzScaled
  constructor <;> linarith

/-- The inverse-height composition is normalized when the popular box has
the grid-center margin and the final dilation expands its width to at least
two. -/
theorem pureWZ2Proposition64FinalSlope_normalized
    (sourceSlope : SlopeFunction) (hsource : sourceSlope.IsNormalized)
    (center : Point3) {width scale : ℝ}
    (hwidth : 0 < width)
    (hcenter : |center 2| ≤ 1 - width / 2)
    (hscale : 1 ≤ scale)
    (hscaleWidth : 2 ≤ scale * width) :
    (pureWZ2Proposition64FinalSlope sourceSlope center scale).IsNormalized := by
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  intro z hz
  have hsourceHeight := pureWZ2Proposition64FinalSlope_source_height_mem center
    hwidth hcenter hscalePos hscaleWidth hz
  have hbounds := hsource (center 2 + z / scale) hsourceHeight
  constructor
  · simpa using hbounds.1
  constructor
  · rw [deriv_pureWZ2Proposition64FinalSlope sourceSlope center hscalePos,
      abs_div, abs_of_pos hscalePos]
    exact (div_le_self (abs_nonneg _) hscale).trans hbounds.2.1
  · rw [second_deriv_pureWZ2Proposition64FinalSlope sourceSlope center hscalePos,
      abs_div, abs_pow, abs_of_pos hscalePos]
    have hscaleSq : 1 ≤ scale ^ 2 := by nlinarith
    exact (div_le_self (abs_nonneg _) hscaleSq).trans hbounds.2.2

/-- The final affine reparameterization is normalized directly from the
global bounds retained by the Proposition-27 smooth segment construction.
This is the applicable version for the narrow popular box in Lemma 3.5. -/
theorem pureWZ2Proposition64FinalSlope_normalized_of_raw
    {delta sigma rawLoss extensionConstant : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (raw : PureWZ2RawC2GlobalGrainData
      shading sigma C rawLoss extensionConstant)
    (globalBounds : PureWZ2RawC2GlobalBoundData raw)
    {slabCenter anchorHeight halfHeight normalization : ℝ}
    (normalized : PureWZ2Proposition64NormalizedData
      raw slabCenter anchorHeight halfHeight normalization)
    (center : Point3) {scale : ℝ}
    (hscale : 1 ≤ scale)
    (hcenterHeight : |center 2| ≤ 1)
    (hvalueBudget :
      3 * halfHeight * extensionConstant *
        Real.rpow delta (-rawLoss) ≤ normalization)
    (hfirstBudget :
      halfHeight * extensionConstant * Real.rpow delta (-rawLoss) ≤
        normalization)
    (hsecondBudget :
      halfHeight ^ 2 * extensionConstant * Real.rpow delta (-rawLoss) ≤
        normalization) :
    (pureWZ2Proposition64FinalSlope normalized.slope center scale).IsNormalized := by
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have hnormalizationPos := normalized.normalization_pos
  intro z hz
  let sourceHeight := center 2 + z / scale
  have hfirstRaw := globalBounds.first_derivative_bound
    (slabCenter + halfHeight * sourceHeight)
  have hsecondRaw := globalBounds.second_derivative_bound
    (slabCenter + halfHeight * sourceHeight)
  constructor
  · rw [pureWZ2Proposition64FinalSlope_apply, normalized.slope_eq,
      pureWZ2Proposition64Slope_apply, abs_div, abs_of_pos hnormalizationPos]
    apply (div_le_one hnormalizationPos).2
    let B := extensionConstant * Real.rpow delta (-rawLoss)
    have hB : 0 ≤ B := by
      exact (abs_nonneg (deriv raw.slope anchorHeight)).trans
        (by simpa [B] using globalBounds.first_derivative_bound anchorHeight)
    have hdiff : Differentiable ℝ raw.slope :=
      raw.slope.contDiff.differentiable (by norm_num)
    have hderivNorm : ∀ t ∈ Set.univ, ‖deriv raw.slope t‖ ≤ B := by
      intro t _
      simpa [B, Real.norm_eq_abs] using globalBounds.first_derivative_bound t
    have hslopeDiff :
        |raw.slope (slabCenter + halfHeight * sourceHeight) -
            raw.slope anchorHeight| ≤
          B * |(slabCenter + halfHeight * sourceHeight) - anchorHeight| := by
      have h := Convex.norm_image_sub_le_of_norm_deriv_le
        (x := slabCenter + halfHeight * sourceHeight)
        (y := anchorHeight)
        (fun t _ => hdiff.differentiableAt) hderivNorm
        (convex_univ : Convex ℝ (Set.univ : Set ℝ))
        (Set.mem_univ _) (Set.mem_univ _)
      simpa [Real.norm_eq_abs, abs_sub_comm] using h
    have hzScale : |z / scale| ≤ 1 := by
      rw [abs_div, abs_of_pos hscalePos]
      have hzAbs : |z| ≤ 1 := abs_le.mpr hz
      exact (div_le_self (abs_nonneg z) hscale).trans hzAbs
    have hsourceHeight : |sourceHeight| ≤ 2 := by
      dsimp only [sourceHeight]
      calc
        |center 2 + z / scale| ≤ |center 2| + |z / scale| := abs_add_le _ _
        _ ≤ 1 + 1 := add_le_add hcenterHeight hzScale
        _ = 2 := by norm_num
    have hanchorRelative : |anchorHeight - slabCenter| ≤ halfHeight := by
      rw [abs_le]
      exact ⟨by linarith [normalized.anchor_mem.1],
        by linarith [normalized.anchor_mem.2]⟩
    have hdistance :
        |(slabCenter + halfHeight * sourceHeight) - anchorHeight| ≤
          3 * halfHeight := by
      calc
        |(slabCenter + halfHeight * sourceHeight) - anchorHeight| =
            |halfHeight * sourceHeight - (anchorHeight - slabCenter)| := by
              congr 1 <;> ring
        _ ≤ |halfHeight * sourceHeight| + |anchorHeight - slabCenter| :=
          abs_sub _ _
        _ ≤ halfHeight * 2 + halfHeight := by
          rw [abs_mul, abs_of_pos normalized.halfHeight_pos]
          exact add_le_add
            (mul_le_mul_of_nonneg_left hsourceHeight
              normalized.halfHeight_pos.le)
            hanchorRelative
        _ = 3 * halfHeight := by ring
    calc
      |raw.slope (slabCenter + halfHeight * sourceHeight) -
          raw.slope anchorHeight| ≤ B *
            |(slabCenter + halfHeight * sourceHeight) - anchorHeight| :=
        hslopeDiff
      _ ≤ B * (3 * halfHeight) := by
        exact mul_le_mul_of_nonneg_left hdistance hB
      _ = 3 * halfHeight * extensionConstant *
          Real.rpow delta (-rawLoss) := by simp [B]; ring
      _ ≤ normalization := hvalueBudget
  constructor
  · rw [deriv_pureWZ2Proposition64FinalSlope normalized.slope center hscalePos,
      normalized.slope_eq, deriv_pureWZ2Proposition64Slope,
      abs_div, abs_of_pos hscalePos,
      abs_div, abs_mul, abs_of_pos normalized.halfHeight_pos,
      abs_of_pos hnormalizationPos]
    have hnumerator : halfHeight *
        |deriv raw.slope (slabCenter + halfHeight * sourceHeight)| ≤
          normalization := by
      calc
        halfHeight * |deriv raw.slope
            (slabCenter + halfHeight * sourceHeight)| ≤
            halfHeight *
              (extensionConstant * Real.rpow delta (-rawLoss)) := by
          gcongr
          exact normalized.halfHeight_pos.le
        _ ≤ normalization := by simpa [mul_assoc] using hfirstBudget
    have hbase : halfHeight *
        |deriv raw.slope (slabCenter + halfHeight * sourceHeight)| /
          normalization ≤ 1 := (div_le_one hnormalizationPos).2 hnumerator
    have hbaseNonneg : 0 ≤ halfHeight *
        |deriv raw.slope (slabCenter + halfHeight * sourceHeight)| /
          normalization := div_nonneg
      (mul_nonneg normalized.halfHeight_pos.le (abs_nonneg _))
      hnormalizationPos.le
    exact (div_le_self hbaseNonneg hscale).trans hbase
  · rw [second_deriv_pureWZ2Proposition64FinalSlope normalized.slope center
        hscalePos, normalized.slope_eq, second_deriv_pureWZ2Proposition64Slope,
      abs_div, abs_pow, abs_of_pos hscalePos, abs_div, abs_mul,
      abs_pow, abs_of_pos normalized.halfHeight_pos,
      abs_of_pos hnormalizationPos]
    have hnumerator : halfHeight ^ 2 *
        |deriv (deriv raw.slope)
          (slabCenter + halfHeight * sourceHeight)| ≤ normalization := by
      calc
        halfHeight ^ 2 * |deriv (deriv raw.slope)
            (slabCenter + halfHeight * sourceHeight)| ≤
            halfHeight ^ 2 *
              (extensionConstant * Real.rpow delta (-rawLoss)) := by gcongr
        _ ≤ normalization := by simpa [mul_assoc] using hsecondBudget
    have hbase : halfHeight ^ 2 *
        |deriv (deriv raw.slope)
          (slabCenter + halfHeight * sourceHeight)| / normalization ≤ 1 :=
      (div_le_one hnormalizationPos).2 hnumerator
    have hscaleSq : 1 ≤ scale ^ 2 := by nlinarith
    exact (div_le_self (by positivity) hscaleSq).trans hbase

/--
Package the preceding ambient calculation as the paper's literal
`[-1,1] -> R` conclusion.  The globally `C²` slope is only an extension
witness used to reuse the existing derivative lemmas.
-/
theorem pureWZ2Proposition64FinalIntervalSlope_normalized_of_raw
    {delta sigma rawLoss extensionConstant : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (raw : PureWZ2RawC2GlobalGrainData
      shading sigma C rawLoss extensionConstant)
    (globalBounds : PureWZ2RawC2GlobalBoundData raw)
    {slabCenter anchorHeight halfHeight normalization : ℝ}
    (normalized : PureWZ2Proposition64NormalizedData
      raw slabCenter anchorHeight halfHeight normalization)
    (center : Point3) {scale : ℝ}
    (hscale : 1 ≤ scale)
    (hcenterHeight : |center 2| ≤ 1)
    (hvalueBudget :
      3 * halfHeight * extensionConstant *
        Real.rpow delta (-rawLoss) ≤ normalization)
    (hfirstBudget :
      halfHeight * extensionConstant * Real.rpow delta (-rawLoss) ≤
        normalization)
    (hsecondBudget :
      halfHeight ^ 2 * extensionConstant * Real.rpow delta (-rawLoss) ≤
        normalization) :
    PureWZ2C2SlopeIsNormalized
      (pureWZ2Proposition64FinalIntervalSlope
        normalized.slope center scale) := by
  let extension :=
    pureWZ2Proposition64FinalSlope normalized.slope center scale
  have hextension : extension.IsNormalized :=
    pureWZ2Proposition64FinalSlope_normalized_of_raw
      raw globalBounds normalized center hscale
      hcenterHeight hvalueBudget hfirstBudget hsecondBudget
  exact extension.isNormalized_restrict_unitInterval hextension

end Kakeya.Assouad

end
