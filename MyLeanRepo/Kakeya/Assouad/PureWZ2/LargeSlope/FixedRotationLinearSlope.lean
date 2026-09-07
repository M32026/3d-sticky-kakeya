import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6Lemma32DerivativeBand
import MyLeanRepo.Kakeya.Cinematic.TangencyIntervalExtension.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Public linear slope after the fixed horizontal rotation

The affine image of the source projection has the genuine Mobius slope
obtained from the fixed horizontal rotation.  Its second derivative need not
obey the frozen `1 / 100` bound with the literal paper constant `100`.
Consequently the public slope is its tangent at the distinguished height.
The later height-window refinement compares the genuine slope with this
tangent by `PureWZ2PaperADSet1.nearby_projection_transfer`.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The exact target slope produced by a fixed horizontal rotation followed
by an axis-parallel diagonal map. -/
def pureWZ2AffineDiagonalExactSlope
    (source : SlopeFunction)
    (frameSlope anchor heightScale transverseScale t : ℝ) : ℝ :=
  pureWZ2RotatedSlopeValue frameSlope
      (source (anchor + t / heightScale)) /
    transverseScale

/-- The globally linear public representative tangent to the exact rotated
slope at the target height zero. -/
def pureWZ2FixedRotationLinearSlope
    (source : SlopeFunction) (anchor slopeScale : ℝ) : SlopeFunction where
  toFun t := (deriv source anchor / slopeScale) * t
  contDiff := by fun_prop

@[simp] theorem pureWZ2FixedRotationLinearSlope_apply
    (source : SlopeFunction) (anchor slopeScale t : ℝ) :
    pureWZ2FixedRotationLinearSlope source anchor slopeScale t =
      (deriv source anchor / slopeScale) * t := rfl

@[simp] theorem pureWZ2FixedRotationLinearSlope_zero
    (source : SlopeFunction) (anchor slopeScale : ℝ) :
    pureWZ2FixedRotationLinearSlope source anchor slopeScale 0 = 0 := by
  simp

theorem pureWZ2FixedRotationLinearSlope_deriv
    (source : SlopeFunction) (anchor slopeScale t : ℝ) :
    deriv (pureWZ2FixedRotationLinearSlope source anchor slopeScale) t =
      deriv source anchor / slopeScale := by
  change deriv (fun x : ℝ => (deriv source anchor / slopeScale) * x) t = _
  simpa using ((hasDerivAt_id t).const_mul
    (deriv source anchor / slopeScale)).deriv

theorem pureWZ2FixedRotationLinearSlope_second_deriv
    (source : SlopeFunction) (anchor slopeScale t : ℝ) :
    deriv (deriv (pureWZ2FixedRotationLinearSlope source anchor slopeScale)) t =
      0 := by
  have hfirst : deriv
      (pureWZ2FixedRotationLinearSlope source anchor slopeScale) =
      fun _ : ℝ => deriv source anchor / slopeScale := by
    funext x
    exact pureWZ2FixedRotationLinearSlope_deriv source anchor slopeScale x
  rw [hfirst]
  exact (hasDerivAt_const t (deriv source anchor / slopeScale)).deriv

theorem pureWZ2FixedRotationLinearSlope_nonsingular
    (source : SlopeFunction) {anchor slopeScale width : ℝ}
    (hslopeScale : 0 < slopeScale)
    (hlower : slopeScale ≤ |deriv source anchor|)
    (hupper : |deriv source anchor| ≤ slopeScale + width / 50)
    (hwidth : width ≤ slopeScale) :
    (pureWZ2FixedRotationLinearSlope source anchor slopeScale).IsNonsingular := by
  intro t _ht
  rw [pureWZ2FixedRotationLinearSlope_deriv, abs_div,
    abs_of_pos hslopeScale]
  constructor
  · calc
      1 = slopeScale / slopeScale := by field_simp [hslopeScale.ne']
      _ ≤ |deriv source anchor| / slopeScale :=
        div_le_div_of_nonneg_right hlower hslopeScale.le
  constructor
  · calc
      |deriv source anchor| / slopeScale
          ≤ (slopeScale + width / 50) / slopeScale :=
            div_le_div_of_nonneg_right hupper hslopeScale.le
      _ ≤ (slopeScale + slopeScale / 50) / slopeScale := by
        gcongr
      _ ≤ 2 := by
        field_simp [hslopeScale.ne']
        linarith
  · rw [pureWZ2FixedRotationLinearSlope_second_deriv, abs_zero]
    norm_num

/-- Parameters shared by an affine-diagonal map, its exact transported slope,
and the historical linear tangent.  The canonical rotated constructor below
chooses `frameSlope = source anchor`; other constructors may choose a bounded
fixed rotation together with their own positive diagonal scale. -/
structure PureWZ2FixedRotationLinearSlopeData
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) where
  anchor : ℝ
  anchor_mem : anchor ∈ Set.Icc band.left band.right
  frameSlope : ℝ
  frameSlope_bound : |frameSlope| ≤ 1
  rotatedSlopeScale : ℝ
  rotatedSlopeScale_pos : 0 < rotatedSlopeScale
  normalizationConstant : ℝ
  normalizationConstant_pos : 0 < normalizationConstant
  heightScale : ℝ
  heightScale_eq : heightScale = normalizationConstant / rotatedSlopeScale
  transverseScale : ℝ
  transverseScale_eq : transverseScale =
    rotatedSlopeScale ^ 2 / normalizationConstant
  publicSlope : SlopeFunction
  publicSlope_eq : publicSlope =
    pureWZ2FixedRotationLinearSlope
      band.lemma31.data.globalSlope
      anchor band.slopeScale
  publicSlope_nonsingular : publicSlope.IsNonsingular
  publicSlope_zero : publicSlope 0 = 0
  exactSlope : ℝ → ℝ
  exactSlope_eq : exactSlope = pureWZ2AffineDiagonalExactSlope
    band.lemma31.data.globalSlope
    frameSlope anchor heightScale transverseScale

theorem PureWZ2Lemma32DerivativeBandAssembly.toFixedRotationLinearSlopeAt
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta)
    (anchor : ℝ) (hanchor : anchor ∈ Set.Icc band.left band.right) :
    ∃ data : PureWZ2FixedRotationLinearSlopeData band,
      data.anchor = anchor ∧
      data.frameSlope = band.lemma31.data.globalSlope anchor ∧
      data.rotatedSlopeScale =
        band.slopeScale / (1 + data.frameSlope ^ 2) ∧
      data.normalizationConstant = 100 := by
  let source := band.lemma31.data.globalSlope
  let frameSlope := source anchor
  let rotatedSlopeScale := band.slopeScale / (1 + frameSlope ^ 2)
  let normalizationConstant : ℝ := 100
  let heightScale := normalizationConstant / rotatedSlopeScale
  let transverseScale := rotatedSlopeScale ^ 2 / normalizationConstant
  let publicSlope :=
    pureWZ2FixedRotationLinearSlope source anchor band.slopeScale
  let exactSlope := pureWZ2AffineDiagonalExactSlope source frameSlope anchor
    heightScale transverseScale
  have hband : band.slopeScale ≤ |deriv source anchor| ∧
      |deriv source anchor| ≤ 2 * band.slopeScale := by
    simpa [source] using
      band.derivative_band anchor hanchor
  have htight : |deriv source anchor| ≤
      band.slopeScale + band.lemma31.data.rho.1 / 50 := by
    simpa [source] using
      band.derivative_tight_upper anchor hanchor
  have hrotated : 0 < rotatedSlopeScale := by
    dsimp only [rotatedSlopeScale]
    exact div_pos band.slopeScale_pos (by positivity)
  have hpublic : publicSlope.IsNonsingular := by
    dsimp only [publicSlope, source]
    exact pureWZ2FixedRotationLinearSlope_nonsingular _
      band.slopeScale_pos hband.1 htight band.slopeScale_lower
  have hframeBound : |frameSlope| ≤ 1 := by
    dsimp only [frameSlope, source]
    exact (band.lemma31.data.globalSlope_normalized anchor <| by
      exact ⟨band.lemma31.data.scaleData.slabLeft_mem.trans
          (band.left_mem.trans hanchor.1),
        hanchor.2.trans <| band.right_mem.trans
          band.lemma31.data.scaleData.slabRight_mem⟩).1
  refine ⟨{
    anchor := anchor
    anchor_mem := hanchor
    frameSlope := frameSlope
    frameSlope_bound := hframeBound
    rotatedSlopeScale := rotatedSlopeScale
    rotatedSlopeScale_pos := hrotated
    normalizationConstant := normalizationConstant
    normalizationConstant_pos := by norm_num
    heightScale := heightScale
    heightScale_eq := rfl
    transverseScale := transverseScale
    transverseScale_eq := rfl
    publicSlope := publicSlope
    publicSlope_eq := rfl
    publicSlope_nonsingular := hpublic
    publicSlope_zero := by simp [publicSlope]
    exactSlope := exactSlope
    exactSlope_eq := rfl
  }, rfl, rfl, rfl, rfl⟩

/-- Midpoint-compatible wrapper for callers that do not need to preserve a
geometrically distinguished occupied height. -/
theorem PureWZ2Lemma32DerivativeBandAssembly.toFixedRotationLinearSlope
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) :
    Nonempty (PureWZ2FixedRotationLinearSlopeData band) := by
  let anchor := (band.left + band.right) / 2
  have hanchor : anchor ∈ Set.Icc band.left band.right := by
    dsimp only [anchor]
    constructor <;> linarith [band.ordered]
  rcases band.toFixedRotationLinearSlopeAt anchor hanchor with ⟨data, _⟩
  exact ⟨data⟩

/-- The public affine-diagonal slope is uniformly bounded on the public
interval.  This estimate is intentionally stated for the transported slope
itself, so the terminal global-AD argument never reuses a source-coordinate
slope bound. -/
theorem PureWZ2FixedRotationLinearSlopeData.publicSlope_abs_le_two
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (data : PureWZ2FixedRotationLinearSlopeData band)
    {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |data.publicSlope t| ≤ 2 := by
  have hderiv : |deriv band.lemma31.data.globalSlope data.anchor| ≤
      2 * band.slopeScale := by
    simpa using
      (band.derivative_band data.anchor data.anchor_mem).2
  have hcoefficient :
      |deriv band.lemma31.data.globalSlope data.anchor / band.slopeScale| ≤
        2 := by
    rw [abs_div, abs_of_pos band.slopeScale_pos]
    exact (div_le_iff₀ band.slopeScale_pos).2 (by simpa [mul_comm] using hderiv)
  rw [data.publicSlope_eq, pureWZ2FixedRotationLinearSlope_apply, abs_mul]
  calc
    |deriv band.lemma31.data.globalSlope data.anchor / band.slopeScale| * |t|
        ≤ 2 * 1 := by
          gcongr
          exact abs_le.mpr ht
    _ = 2 := by norm_num

/-- A normalized source slope has the standard quadratic Taylor remainder
on any subinterval of the normalized height window. -/
theorem pureWZ2_normalized_slope_taylor_remainder
    (source : SlopeFunction) (hnormalized : source.IsNormalized)
    {left right anchor z : ℝ}
    (hleft : -1 ≤ left) (hright : right ≤ 1)
    (hordered : left ≤ right)
    (hanchor : anchor ∈ Set.Icc left right)
    (hz : z ∈ Set.Icc left right) :
    |source z - source anchor - deriv source anchor * (z - anchor)| ≤
      (1 / 2 : ℝ) * (z - anchor) ^ 2 := by
  have hdiff : Differentiable ℝ source :=
    source.contDiff.differentiable (by norm_num)
  have hdiff2 : Differentiable ℝ (deriv source) :=
    source.contDiff.differentiable_deriv_two
  apply Kakeya.Cinematic.taylor_remainder_bound_on_interval
    hdiff hdiff2 hordered hz hanchor
  intro point hpoint
  exact (hnormalized point
    ⟨hleft.trans hpoint.1, hpoint.2.trans hright⟩).2.2

/-- The value of a normalized source slope differs by at most the source
height displacement inside the normalized window. -/
theorem pureWZ2_normalized_slope_value_difference
    (source : SlopeFunction) (hnormalized : source.IsNormalized)
    {left right anchor z : ℝ}
    (hleft : -1 ≤ left) (hright : right ≤ 1)
    (hordered : left ≤ right)
    (hanchor : anchor ∈ Set.Icc left right)
    (hz : z ∈ Set.Icc left right) :
    |source z - source anchor| ≤ |z - anchor| := by
  have hdiff : Differentiable ℝ source :=
    source.contDiff.differentiable (by norm_num)
  have hbound : ∀ point ∈ Set.Icc left right,
      ‖deriv source point‖ ≤ (1 : ℝ) := by
    intro point hpoint
    simpa [Real.norm_eq_abs] using
      (hnormalized point
        ⟨hleft.trans hpoint.1, hpoint.2.trans hright⟩).2.1
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun point _ => hdiff.differentiableAt) hbound
    (convex_Icc left right) hanchor hz
  simpa [Real.norm_eq_abs] using h

/-- Pure algebra behind the tangent comparison after fixed rotation and the
literal paper diagonal dilation. -/
lemma pureWZ2_mobius_diagonal_linear_error
    {a q derivative slopeScale B u t : ℝ}
    (ha : |a| ≤ 1)
    (hslopeScale : 0 < slopeScale)
    (hslopeScaleOne : slopeScale ≤ 1)
    (hB : B = 1 + a ^ 2)
    (hu : u = t * slopeScale / (100 * B))
    (huSmall : |u| ≤ slopeScale / 50)
    (hq : |q| ≤ |u|)
    (hderivative : |derivative| ≤ (51 / 50 : ℝ) * slopeScale)
    (hremainder : |q - derivative * u| ≤ (1 / 2 : ℝ) * u ^ 2) :
    |q / (B + a * q) / ((slopeScale / B) ^ 2 / 100) -
        derivative / slopeScale * t| ≤
      t ^ 2 / 40 := by
  have haBounds := abs_le.mp ha
  have hBOne : 1 ≤ B := by
    rw [hB]
    nlinarith [sq_nonneg a]
  have hBPos : 0 < B := lt_of_lt_of_le (by norm_num) hBOne
  have hBTwo : B ≤ 2 := by
    rw [hB]
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]
  have hqSmall : |q| ≤ 1 / 50 := by
    calc
      |q| ≤ |u| := hq
      _ ≤ slopeScale / 50 := huSmall
      _ ≤ 1 / 50 := by gcongr
  have haqSmall : |a * q| ≤ 1 / 50 := by
    rw [abs_mul]
    calc
      |a| * |q| ≤ 1 * (1 / 50) := by gcongr
      _ = 1 / 50 := by ring
  have hdenom : (49 / 50 : ℝ) * B ≤ B + a * q := by
    have hneg : -(1 / 50 : ℝ) ≤ a * q := by
      exact (abs_le.mp haqSmall).1
    nlinarith
  have hdenomPos : 0 < B + a * q := by
    have : 0 < (49 / 50 : ℝ) * B := by positivity
    exact this.trans_le hdenom
  let numerator := B * (q - derivative * u) - a * q * derivative * u
  have hfirst : B * |q - derivative * u| ≤ u ^ 2 := by
    calc
      B * |q - derivative * u|
          ≤ 2 * ((1 / 2 : ℝ) * u ^ 2) := by gcongr
      _ = u ^ 2 := by ring
  have hsecond :
      |a| * |q| * |derivative| * |u| ≤
        (51 / 50 : ℝ) * slopeScale * u ^ 2 := by
    calc
      |a| * |q| * |derivative| * |u|
          ≤ 1 * |u| * ((51 / 50 : ℝ) * slopeScale) * |u| := by
            gcongr
      _ = (51 / 50 : ℝ) * slopeScale * u ^ 2 := by
            rw [← sq_abs]
            ring
  have hnumerator : |numerator| ≤ (101 / 50 : ℝ) * u ^ 2 := by
    calc
      |numerator|
          ≤ B * |q - derivative * u| +
              |a| * |q| * |derivative| * |u| := by
            dsimp only [numerator]
            calc
              |B * (q - derivative * u) - a * q * derivative * u|
                  ≤ |B * (q - derivative * u)| +
                      |a * q * derivative * u| := abs_sub _ _
              _ = _ := by rw [abs_mul, abs_mul, abs_mul, abs_mul,
                abs_of_pos hBPos]
      _ ≤ u ^ 2 + (51 / 50 : ℝ) * slopeScale * u ^ 2 :=
        add_le_add hfirst hsecond
      _ ≤ (101 / 50 : ℝ) * u ^ 2 := by
        nlinarith [sq_nonneg u]
  have hdenomRatio : B / (B + a * q) ≤ 50 / 49 := by
    rw [div_le_iff₀ hdenomPos]
    nlinarith
  have hidentity :
      q / (B + a * q) / ((slopeScale / B) ^ 2 / 100) -
          derivative / slopeScale * t =
        (100 / slopeScale ^ 2) * (B / (B + a * q)) * numerator := by
    dsimp only [numerator]
    rw [hu]
    have hdenomComm : q * a + B ≠ 0 := by
      rw [show q * a + B = B + a * q by ring]
      exact hdenomPos.ne'
    field_simp [hslopeScale.ne', hBPos.ne', hdenomPos.ne', hdenomComm]
    have hcancel : (q * a + B)⁻¹ * (q * a + B) = 1 :=
      inv_mul_cancel₀ hdenomComm
    linear_combination slopeScale * derivative * t * hcancel
  rw [hidentity, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (100 : ℝ) / slopeScale ^ 2),
    abs_of_pos (div_pos hBPos hdenomPos)]
  calc
    100 / slopeScale ^ 2 * (B / (B + a * q)) * |numerator|
        ≤ 100 / slopeScale ^ 2 * (50 / 49) *
            ((101 / 50 : ℝ) * u ^ 2) := by gcongr
    _ = (101 / 4900 : ℝ) * (t ^ 2 / B ^ 2) := by
      rw [hu]
      field_simp [hslopeScale.ne', hBPos.ne']
      ring
    _ ≤ (101 / 4900 : ℝ) * t ^ 2 := by
      gcongr
      rw [div_le_iff₀ (sq_pos_of_pos hBPos)]
      have hBsq : 1 ≤ B ^ 2 := by nlinarith [sq_nonneg (B - 1)]
      simpa using mul_le_mul_of_nonneg_left hBsq (sq_nonneg t)
    _ ≤ t ^ 2 / 40 := by
      nlinarith [sq_nonneg t]

/-- Concrete tangent error for the Lemma-32 fixed-rotation data.  The only
geometric side condition is that the target height comes from the selected
source interval. -/
theorem PureWZ2FixedRotationLinearSlopeData.exactSlope_close_publicSlope
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (data : PureWZ2FixedRotationLinearSlopeData band)
    (hframeSlope : data.frameSlope =
      band.lemma31.data.globalSlope data.anchor)
    (hrotatedSlopeScale : data.rotatedSlopeScale =
      band.slopeScale / (1 + data.frameSlope ^ 2))
    (hnormalization : data.normalizationConstant = 100)
    {t : ℝ}
    (hsource : data.anchor + t / data.heightScale ∈
      Set.Icc band.left band.right) :
    |data.exactSlope t - data.publicSlope t| ≤ t ^ 2 / 40 := by
  let source :=
    band.lemma31.data.globalSlope
  let a := source data.anchor
  let B := 1 + a ^ 2
  let q := source (data.anchor + t / data.heightScale) - a
  let derivative := deriv source data.anchor
  let u := t / data.heightScale
  have hanchor : data.anchor ∈ Set.Icc band.left band.right :=
    data.anchor_mem
  have hleft : -1 ≤ band.left :=
    band.lemma31.data.scaleData.slabLeft_mem.trans band.left_mem
  have hright : band.right ≤ 1 :=
    band.right_mem.trans band.lemma31.data.scaleData.slabRight_mem
  have ha : |a| ≤ 1 := by
    exact (band.lemma31.data.globalSlope_normalized
      data.anchor ⟨hleft.trans hanchor.1, hanchor.2.trans hright⟩).1
  have hBPos : 0 < B := by
    dsimp only [B]
    nlinarith [sq_nonneg a]
  have hheight : data.heightScale ≠ 0 := by
    rw [data.heightScale_eq]
    exact div_ne_zero data.normalizationConstant_pos.ne'
      data.rotatedSlopeScale_pos.ne'
  have hu : u = t * band.slopeScale / (100 * B) := by
    dsimp only [u, B, a]
    rw [data.heightScale_eq, hnormalization, hrotatedSlopeScale, hframeSlope]
    field_simp [band.slopeScale_pos.ne', hBPos.ne']
    ring
  have huBand : |u| ≤ band.right - band.left := by
    have hsource' : data.anchor + u ∈ Set.Icc band.left band.right := by
      simpa [u] using hsource
    rw [abs_le]
    constructor <;> linarith [hanchor.1, hanchor.2, hsource'.1, hsource'.2]
  have huSmall : |u| ≤ band.slopeScale / 50 := by
    calc
      |u| ≤ band.right - band.left := huBand
      _ = band.lemma31.data.rho.1 / 50 := by rw [band.length_eq]
      _ ≤ band.slopeScale / 50 := by
        exact div_le_div_of_nonneg_right band.slopeScale_lower (by norm_num)
  have hq : |q| ≤ |u| := by
    simpa [q, u, a, source] using
      pureWZ2_normalized_slope_value_difference source
        band.lemma31.data.globalSlope_normalized
        hleft hright band.ordered.le hanchor hsource
  have hremainder : |q - derivative * u| ≤ (1 / 2 : ℝ) * u ^ 2 := by
    simpa [q, derivative, u, a, source] using
      pureWZ2_normalized_slope_taylor_remainder source
        band.lemma31.data.globalSlope_normalized
        hleft hright band.ordered.le hanchor hsource
  have hderivative : |derivative| ≤ (51 / 50 : ℝ) * band.slopeScale := by
    have htight : |deriv source data.anchor| ≤
        band.slopeScale + band.lemma31.data.rho.1 / 50 := by
      simpa [source] using
        band.derivative_tight_upper data.anchor hanchor
    dsimp only [derivative, source]
    calc
      |deriv source data.anchor|
          ≤ band.slopeScale + band.lemma31.data.rho.1 / 50 := htight
      _ ≤ band.slopeScale + band.slopeScale / 50 := by
        gcongr
        exact band.slopeScale_lower
      _ = (51 / 50 : ℝ) * band.slopeScale := by ring
  have herror := pureWZ2_mobius_diagonal_linear_error
    (a := a) (q := q) (derivative := derivative)
    (slopeScale := band.slopeScale) (B := B) (u := u) (t := t)
    ha band.slopeScale_pos band.slopeScale_le_one rfl hu huSmall hq
    hderivative hremainder
  rw [data.exactSlope_eq, data.publicSlope_eq]
  simp only [pureWZ2AffineDiagonalExactSlope, pureWZ2RotatedSlopeValue,
    pureWZ2FixedRotationLinearSlope_apply]
  rw [hframeSlope]
  have hdenomIdentity :
      1 + source data.anchor *
          source (data.anchor + t / data.heightScale) =
        B + a * q := by
    dsimp only [B, a, q]
    ring
  rw [hdenomIdentity]
  rw [data.transverseScale_eq, hnormalization, hrotatedSlopeScale, hframeSlope]
  change
    |q / (B + a * q) / ((band.slopeScale / B) ^ 2 / 100) -
        derivative / band.slopeScale * t| ≤ t ^ 2 / 40
  exact herror

end Kakeya.Assouad

end
