import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Proof-local slope normalization for Node 7

This file isolates the scalar calculus in `node07.tex`.  It records the
Möbius change of slope induced by the fixed horizontal rotation and the final
anisotropic rescaling.  Selection of the active interval and extension away
from that interval are deliberately left to their geometric callers.
-/

noncomputable section

namespace Kakeya.Assouad

open Set
open scoped Topology

/-- The Möbius slope coordinate used after rotating the value `q` to zero. -/
def node7MobiusRotatedValue (q u : ℝ) : ℝ :=
  (u - q) / (1 + q * u)

@[simp] theorem node7MobiusRotatedValue_self (q : ℝ) :
    node7MobiusRotatedValue q q = 0 := by
  simp [node7MobiusRotatedValue]

/-- On the short interval used in Node 7, the Möbius denominator stays
uniformly separated from zero.  The fixed subdivision constant `100` leaves
ample room for the later quantitative estimates. -/
theorem node7Mobius_denominator_lower
    {q u : ℝ} (hq : |q| ≤ 1) (hu : |u - q| ≤ 1 / 100) :
    (99 / 100 : ℝ) ≤ 1 + q * u := by
  have hproduct : -(1 / 100 : ℝ) ≤ q * (u - q) := by
    have habs : |q * (u - q)| ≤ (1 / 100 : ℝ) := by
      rw [abs_mul]
      calc
        |q| * |u - q| ≤ 1 * (1 / 100 : ℝ) :=
          mul_le_mul hq hu (abs_nonneg _) (by norm_num)
        _ = 1 / 100 := by norm_num
    exact (abs_le.mp habs).1
  have hqSq : 0 ≤ q ^ 2 := sq_nonneg q
  rw [show 1 + q * u = 1 + q ^ 2 + q * (u - q) by ring]
  linarith

theorem node7Mobius_denominator_ne_zero
    {q u : ℝ} (hq : |q| ≤ 1) (hu : |u - q| ≤ 1 / 100) :
    1 + q * u ≠ 0 := by
  have hpositive : 0 < 1 + q * u :=
    (by norm_num : (0 : ℝ) < 99 / 100) |>.trans_le
      (node7Mobius_denominator_lower hq hu)
  exact hpositive.ne'

/-- First derivative of the Möbius-rotated slope. -/
theorem node7MobiusRotatedValue_hasDerivAt
    (source : SlopeFunction) (q t : ℝ)
    (hdenom : 1 + q * source t ≠ 0) :
    HasDerivAt (fun s => node7MobiusRotatedValue q (source s))
      (((1 + q ^ 2) * deriv source t) / (1 + q * source t) ^ 2) t := by
  have hsource : HasDerivAt source (deriv source t) t :=
    ((source.contDiff.differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hnum := hsource.sub_const q
  have hden := (hsource.const_mul q).const_add 1
  have hcalc := hnum.div hden hdenom
  change HasDerivAt (fun s => (source s - q) / (1 + q * source s)) _ t
  convert hcalc using 1 <;> first | rfl | ring

theorem node7MobiusRotatedValue_deriv
    (source : SlopeFunction) (q t : ℝ)
    (hdenom : 1 + q * source t ≠ 0) :
    deriv (fun s => node7MobiusRotatedValue q (source s)) t =
      ((1 + q ^ 2) * deriv source t) / (1 + q * source t) ^ 2 :=
  (node7MobiusRotatedValue_hasDerivAt source q t hdenom).deriv

/-- Second derivative formula for the Möbius-rotated slope. -/
theorem node7MobiusRotatedValue_second_deriv
    (source : SlopeFunction) (q t : ℝ)
    (hdenom : 1 + q * source t ≠ 0) :
    deriv (deriv (fun s => node7MobiusRotatedValue q (source s))) t =
      (1 + q ^ 2) *
        (deriv (deriv source) t * (1 + q * source t) -
          2 * q * (deriv source t) ^ 2) /
        (1 + q * source t) ^ 3 := by
  have hcontinuous : ContinuousAt (fun s => 1 + q * source s) t :=
    continuousAt_const.add
      (continuousAt_const.mul source.contDiff.continuous.continuousAt)
  have hne : ∀ᶠ s in 𝓝 t, 1 + q * source s ≠ 0 :=
    hcontinuous.eventually_ne hdenom
  have hfirst : deriv (fun s => node7MobiusRotatedValue q (source s)) =ᶠ[𝓝 t]
      fun s => ((1 + q ^ 2) * deriv source s) /
        (1 + q * source s) ^ 2 := by
    filter_upwards [hne] with s hs
    exact node7MobiusRotatedValue_deriv source q s hs
  rw [hfirst.deriv_eq]
  have hsource : HasDerivAt source (deriv source t) t :=
    ((source.contDiff.differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hsourceDeriv : HasDerivAt (deriv source)
      (deriv (deriv source) t) t :=
    ((source.contDiff.deriv').differentiable_one.differentiableAt).hasDerivAt
  have hnum := hsourceDeriv.const_mul (1 + q ^ 2)
  have hbase := (hsource.const_mul q).const_add 1
  have hden := hbase.pow 2
  have hcalc := hnum.div hden (pow_ne_zero 2 hdenom)
  change deriv ((fun y => (1 + q ^ 2) * deriv source y) /
      (fun x => 1 + q * source x) ^ 2) t = _
  rw [hcalc.deriv]
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [hdenom]

/-- The exact slope transported by height translation, horizontal rotation,
and the two anisotropic diagonal factors. -/
def node7ExactNormalizedSlopeValue
    (source : SlopeFunction)
    (q anchor heightScale transverseScale t : ℝ) : ℝ :=
  node7MobiusRotatedValue q (source (anchor + t / heightScale)) /
    transverseScale

theorem node7ExactNormalizedSlopeValue_contDiffAt
    (source : SlopeFunction)
    (q anchor heightScale transverseScale t : ℝ)
    (hdenom : 1 + q * source (anchor + t / heightScale) ≠ 0) :
    ContDiffAt ℝ 2
      (node7ExactNormalizedSlopeValue source q anchor heightScale
        transverseScale) t := by
  have hsource : ContDiffAt ℝ 2
      (fun x : ℝ => source (anchor + x / heightScale)) t := by
    exact source.contDiff.contDiffAt.comp t
      (contDiffAt_const.add (contDiffAt_id.div_const heightScale))
  have hnum : ContDiffAt ℝ 2
      (fun x : ℝ => source (anchor + x / heightScale) - q) t :=
    hsource.sub contDiffAt_const
  have hden : ContDiffAt ℝ 2
      (fun x : ℝ => 1 + q * source (anchor + x / heightScale)) t :=
    contDiffAt_const.add (contDiffAt_const.mul hsource)
  change ContDiffAt ℝ 2 (fun x : ℝ =>
    ((source (anchor + x / heightScale) - q) /
      (1 + q * source (anchor + x / heightScale))) / transverseScale) t
  exact (hnum.div hden hdenom).div_const transverseScale

theorem node7ExactNormalizedSlopeValue_deriv
    (source : SlopeFunction)
    (q anchor : ℝ) {heightScale transverseScale : ℝ}
    (hheight : heightScale ≠ 0) (htransverse : transverseScale ≠ 0)
    (t : ℝ)
    (hdenom : 1 + q * source (anchor + t / heightScale) ≠ 0) :
    deriv (node7ExactNormalizedSlopeValue source q anchor heightScale
      transverseScale) t =
      ((1 + q ^ 2) * deriv source (anchor + t / heightScale)) /
        (1 + q * source (anchor + t / heightScale)) ^ 2 /
          heightScale / transverseScale := by
  let inner : ℝ → ℝ := fun x => anchor + x / heightScale
  let rotated : ℝ → ℝ := fun x => node7MobiusRotatedValue q (source x)
  have hinner : HasDerivAt inner (1 / heightScale) t := by
    dsimp only [inner]
    simpa using ((hasDerivAt_id t).div_const heightScale).const_add anchor
  have hrotated : HasDerivAt rotated
      (((1 + q ^ 2) * deriv source (inner t)) /
        (1 + q * source (inner t)) ^ 2) (inner t) := by
    exact node7MobiusRotatedValue_hasDerivAt source q (inner t) hdenom
  have hcomp := (hrotated.comp t hinner).div_const transverseScale
  change deriv (fun x => rotated (inner x) / transverseScale) t = _
  have hvalue : deriv (fun x => rotated (inner x) / transverseScale) t =
      (((1 + q ^ 2) * deriv source (inner t)) /
        (1 + q * source (inner t)) ^ 2) * (1 / heightScale) /
          transverseScale := by
    simpa only [Function.comp_def] using hcomp.deriv
  rw [hvalue]
  dsimp only [rotated, inner]
  field_simp [hheight, htransverse]

theorem node7ExactNormalizedSlopeValue_second_deriv
    (source : SlopeFunction)
    (q anchor : ℝ) {heightScale transverseScale : ℝ}
    (hheight : heightScale ≠ 0) (htransverse : transverseScale ≠ 0)
    (t : ℝ)
    (hdenom : 1 + q * source (anchor + t / heightScale) ≠ 0) :
    deriv (deriv (node7ExactNormalizedSlopeValue source q anchor heightScale
      transverseScale)) t =
      ((1 + q ^ 2) *
        (deriv (deriv source) (anchor + t / heightScale) *
            (1 + q * source (anchor + t / heightScale)) -
          2 * q * (deriv source (anchor + t / heightScale)) ^ 2) /
        (1 + q * source (anchor + t / heightScale)) ^ 3) /
          heightScale ^ 2 / transverseScale := by
  let inner : ℝ → ℝ := fun x => anchor + x / heightScale
  let rotated : ℝ → ℝ := fun x => node7MobiusRotatedValue q (source x)
  have hinner : HasDerivAt inner (1 / heightScale) t := by
    dsimp only [inner]
    simpa using ((hasDerivAt_id t).div_const heightScale).const_add anchor
  have hrotatedSmooth : ContDiffAt ℝ 2 rotated (inner t) := by
    have hsource : ContDiffAt ℝ 2 source (inner t) := source.contDiff.contDiffAt
    have hnum : ContDiffAt ℝ 2 (fun x : ℝ => source x - q) (inner t) :=
      hsource.sub contDiffAt_const
    have hden : ContDiffAt ℝ 2 (fun x : ℝ => 1 + q * source x)
        (inner t) := contDiffAt_const.add (contDiffAt_const.mul hsource)
    exact hnum.div hden hdenom
  have hcompSmooth : ContDiffAt ℝ 2
      (fun x => rotated (inner x) / transverseScale) t := by
    exact (hrotatedSmooth.comp t
      (contDiffAt_const.add (contDiffAt_id.div_const heightScale)))
        |>.div_const transverseScale
  have hdenContinuous : ContinuousAt
      (fun x : ℝ => 1 + q * source (anchor + x / heightScale)) t :=
    continuousAt_const.add <| continuousAt_const.mul <|
      source.contDiff.continuous.continuousAt.comp <|
        continuousAt_const.add (continuousAt_id.div_const heightScale)
  have hdenEventually : ∀ᶠ x in 𝓝 t,
      1 + q * source (anchor + x / heightScale) ≠ 0 :=
    hdenContinuous.eventually_ne hdenom
  have hfirst : deriv
      (node7ExactNormalizedSlopeValue source q anchor heightScale
        transverseScale) =ᶠ[𝓝 t]
      fun x => deriv rotated (inner x) / heightScale / transverseScale := by
    filter_upwards [hdenEventually] with x hdenx
    have hrotatedFirst :=
      node7MobiusRotatedValue_deriv source q (inner x) hdenx
    rw [node7ExactNormalizedSlopeValue_deriv source q anchor hheight
      htransverse x hdenx, hrotatedFirst]
  rw [hfirst.deriv_eq]
  have hrotatedDeriv : HasDerivAt (deriv rotated)
      (deriv (deriv rotated) (inner t)) (inner t) :=
    ((hrotatedSmooth.derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  have hcalc := ((hrotatedDeriv.comp t hinner).div_const heightScale)
    |>.div_const transverseScale
  have hvalue : deriv
      (fun x => deriv rotated (inner x) / heightScale / transverseScale) t =
      deriv (deriv rotated) (inner t) * (1 / heightScale) /
        heightScale / transverseScale := by
    simpa only [Function.comp_def] using hcalc.deriv
  rw [hvalue]
  rw [show deriv (deriv rotated) (inner t) =
      (1 + q ^ 2) *
        (deriv (deriv source) (inner t) * (1 + q * source (inner t)) -
          2 * q * (deriv source (inner t)) ^ 2) /
        (1 + q * source (inner t)) ^ 3 by
    exact node7MobiusRotatedValue_second_deriv source q (inner t) hdenom]
  dsimp only [inner]
  field_simp [hheight, htransverse]

/-- Numerical first-derivative window used after the exact Mobius rotation. -/
theorem node7_normalized_first_derivative_bounds
    {B D m x gamma : ℝ}
    (hBOne : 1 ≤ B) (hm : 0 < m)
    (hgamma : gamma = (4 / 5 : ℝ) * m / B)
    (hDPos : 0 < D)
    (hDLower : (99 / 100 : ℝ) * B ≤ D)
    (hDUpper : D ≤ (101 / 100 : ℝ) * B)
    (hxLower : m ≤ |x|) (hxUpper : |x| ≤ (51 / 50 : ℝ) * m) :
    (6 / 5 : ℝ) ≤ |B * x / D ^ 2 / gamma| ∧
      |B * x / D ^ 2 / gamma| ≤ 9 / 5 := by
  have hBPos : 0 < B := lt_of_lt_of_le (by norm_num) hBOne
  have hgammaPos : 0 < gamma := by
    rw [hgamma]
    positivity
  have hDsqUpper : D ^ 2 ≤ ((101 / 100 : ℝ) * B) ^ 2 := by
    exact (sq_le_sq₀ hDPos.le (mul_nonneg (by norm_num) hBPos.le)).2 hDUpper
  have hDsqLower : ((99 / 100 : ℝ) * B) ^ 2 ≤ D ^ 2 := by
    exact (sq_le_sq₀ (mul_nonneg (by norm_num) hBPos.le) hDPos.le).2 hDLower
  rw [abs_div, abs_div, abs_mul, abs_of_pos hBPos, abs_pow,
    abs_of_pos hDPos, abs_of_pos hgammaPos]
  constructor
  · rw [le_div_iff₀ hgammaPos, le_div_iff₀ (sq_pos_of_pos hDPos)]
    calc
      (6 / 5 : ℝ) * gamma * D ^ 2 ≤
          (6 / 5 : ℝ) * gamma * ((101 / 100 : ℝ) * B) ^ 2 := by
        gcongr
      _ ≤ B * |x| := by
        rw [hgamma]
        field_simp [hBPos.ne']
        nlinarith [hxLower, abs_nonneg x]
  · rw [div_le_iff₀ hgammaPos, div_le_iff₀ (sq_pos_of_pos hDPos)]
    calc
      B * |x| ≤ B * ((51 / 50 : ℝ) * m) := by gcongr
      _ ≤ (9 / 5 : ℝ) * gamma *
          ((99 / 100 : ℝ) * B) ^ 2 := by
        rw [hgamma]
        field_simp [hBPos.ne']
        nlinarith [hm]
      _ ≤ (9 / 5 : ℝ) * gamma * D ^ 2 := by gcongr

/-- Uniform curvature bound for the exact Mobius-rotated slope before the
final division by the fixed normalization constant. -/
theorem node7_mobius_second_derivative_abs_le_five
    {B D m q first second : ℝ}
    (hBOne : 1 ≤ B) (hBTwo : B ≤ 2)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hq : |q| ≤ 1)
    (hDPos : 0 < D)
    (hDLower : (99 / 100 : ℝ) * B ≤ D)
    (hfirst : |first| ≤ (51 / 50 : ℝ) * m)
    (hsecond : |second| ≤ 1) :
    |B * (second * D - 2 * q * first ^ 2) / D ^ 3| ≤ 5 := by
  have hBPos : 0 < B := lt_of_lt_of_le (by norm_num) hBOne
  have hDsqLower : ((99 / 100 : ℝ) * B) ^ 2 ≤ D ^ 2 := by
    exact (sq_le_sq₀ (mul_nonneg (by norm_num) hBPos.le) hDPos.le).2 hDLower
  have hDcubeLower : (9 / 10 : ℝ) * B ^ 3 ≤ D ^ 3 := by
    have hpow : ((99 / 100 : ℝ) * B) ^ 3 ≤ D ^ 3 :=
      pow_le_pow_left₀ (mul_nonneg (by norm_num) hBPos.le) hDLower 3
    calc
      (9 / 10 : ℝ) * B ^ 3 ≤ ((99 / 100 : ℝ) * B) ^ 3 := by
        have hBcube : 0 ≤ B ^ 3 := by positivity
        nlinarith
      _ ≤ D ^ 3 := hpow
  have hfirstSq : first ^ 2 ≤ ((51 / 50 : ℝ) * m) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg first) (mul_nonneg (by norm_num) hm.le)).2
        hfirst
  have htermOne : B * (|second| * D) / D ^ 3 ≤ 2 := by
    rw [div_le_iff₀ (pow_pos hDPos 3)]
    have hbase : B * |second| ≤ 2 * D ^ 2 := by
      have hBsquared : B ≤ B ^ 2 := by nlinarith [sq_nonneg (B - 1)]
      calc
        B * |second| ≤ B * 1 := by gcongr
        _ ≤ B ^ 2 := by simpa using hBsquared
        _ ≤ 2 * D ^ 2 := by nlinarith [hDsqLower]
    have hmul := mul_le_mul_of_nonneg_right hbase hDPos.le
    calc
      B * (|second| * D) ≤ 2 * D ^ 2 * D := by
        simpa [mul_assoc] using hmul
      _ = 2 * D ^ 3 := by ring
  have htermTwo : B * (2 * |q| * first ^ 2) / D ^ 3 ≤ 3 := by
    rw [div_le_iff₀ (pow_pos hDPos 3)]
    have hBcube : B ≤ B ^ 3 := by nlinarith [sq_nonneg (B - 1)]
    have hleft : B * (2 * |q| * first ^ 2) ≤
        B * (2 * ((51 / 50 : ℝ) * m) ^ 2) := by
      gcongr
      nlinarith [hq]
    calc
      B * (2 * |q| * first ^ 2) ≤
          B * (2 * ((51 / 50 : ℝ) * m) ^ 2) := hleft
      _ ≤ (21 / 10 : ℝ) * B := by
        have hmSq : m ^ 2 ≤ 1 := by
          nlinarith [sq_nonneg m, sq_nonneg (m - 1)]
        nlinarith [hBPos]
      _ ≤ (27 / 10 : ℝ) * B := by nlinarith [hBPos]
      _ ≤ 3 * ((9 / 10 : ℝ) * B ^ 3) := by
        nlinarith [hBcube]
      _ ≤ 3 * D ^ 3 := by gcongr
  rw [abs_div, abs_mul, abs_of_pos hBPos, abs_pow, abs_of_pos hDPos]
  calc
    B * |second * D - 2 * q * first ^ 2| / D ^ 3 ≤
        B * (|second| * D + 2 * |q| * first ^ 2) / D ^ 3 := by
      gcongr
      calc
        |second * D - 2 * q * first ^ 2| ≤
            |second * D| + |2 * q * first ^ 2| :=
          abs_sub _ _
        _ = |second| * D + 2 * |q| * first ^ 2 := by
          rw [abs_mul, abs_of_pos hDPos, abs_mul, abs_mul, abs_pow]
          norm_num
    _ = B * (|second| * D) / D ^ 3 +
        B * (2 * |q| * first ^ 2) / D ^ 3 := by ring
    _ ≤ 2 + 3 := add_le_add htermOne htermTwo
    _ = 5 := by norm_num

/-- The anisotropically normalized slope from equation (6.X11). -/
def node7AnisotropicNormalizedSlope
    (source : SlopeFunction) (gamma C0 : ℝ) : SlopeFunction where
  toFun t := C0 / gamma ^ 2 * source (gamma * t / C0)
  contDiff := by
    have hinner : ContDiff ℝ 2 (fun t : ℝ => gamma * t / C0) :=
      (contDiff_const.mul contDiff_id).div_const C0
    exact contDiff_const.mul (source.contDiff.comp hinner)

@[simp] theorem node7AnisotropicNormalizedSlope_zero
    (source : SlopeFunction) {gamma C0 : ℝ}
    (hsource : source 0 = 0) :
    node7AnisotropicNormalizedSlope source gamma C0 0 = 0 := by
  simp [node7AnisotropicNormalizedSlope, hsource]

theorem node7AnisotropicNormalizedSlope_deriv
    (source : SlopeFunction) {gamma C0 : ℝ}
    (hgamma : gamma ≠ 0) (hC0 : C0 ≠ 0) (t : ℝ) :
    deriv (node7AnisotropicNormalizedSlope source gamma C0) t =
      deriv source (gamma * t / C0) / gamma := by
  have hinner : HasDerivAt (fun s : ℝ => gamma * s / C0)
      (gamma / C0) t := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id t).const_mul gamma).div_const C0
  have hsource : HasDerivAt source
      (deriv source (gamma * t / C0)) (gamma * t / C0) :=
    ((source.contDiff.differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hcalc := (hsource.comp t hinner).const_mul (C0 / gamma ^ 2)
  change deriv (fun s => C0 / gamma ^ 2 * source (gamma * s / C0)) t = _
  have hvalue : deriv (fun s => C0 / gamma ^ 2 *
      source (gamma * s / C0)) t =
      C0 / gamma ^ 2 * (deriv source (gamma * t / C0) *
        (gamma / C0)) := by
    simpa only [Function.comp_def] using hcalc.deriv
  rw [hvalue]
  field_simp [hgamma, hC0]

theorem node7AnisotropicNormalizedSlope_second_deriv
    (source : SlopeFunction) {gamma C0 : ℝ}
    (hgamma : gamma ≠ 0) (hC0 : C0 ≠ 0) (t : ℝ) :
    deriv (deriv (node7AnisotropicNormalizedSlope source gamma C0)) t =
      deriv (deriv source) (gamma * t / C0) / C0 := by
  have hfirst : deriv (node7AnisotropicNormalizedSlope source gamma C0) =
      fun s => deriv source (gamma * s / C0) / gamma := by
    funext s
    exact node7AnisotropicNormalizedSlope_deriv source hgamma hC0 s
  rw [hfirst]
  have hinner : HasDerivAt (fun s : ℝ => gamma * s / C0)
      (gamma / C0) t := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id t).const_mul gamma).div_const C0
  have hsource : HasDerivAt (deriv source)
      (deriv (deriv source) (gamma * t / C0)) (gamma * t / C0) :=
    ((source.contDiff.deriv').differentiable_one.differentiableAt).hasDerivAt
  have hcalc := (hsource.comp t hinner).div_const gamma
  have hvalue : deriv (fun s =>
      deriv source (gamma * s / C0) / gamma) t =
      (deriv (deriv source) (gamma * t / C0) *
        (gamma / C0)) / gamma := by
    simpa only [Function.comp_def] using hcalc.deriv
  rw [hvalue]
  field_simp [hgamma, hC0]

/-- Exact active-interval bounds after the final anisotropic normalization. -/
theorem node7AnisotropicNormalizedSlope_active_bounds
    (source : SlopeFunction) {gamma C0 : ℝ} {active : Set ℝ}
    (hgamma : 0 < gamma) (hC0 : 0 < C0)
    (hfirstLower : ∀ s ∈ active, (6 / 5 : ℝ) * gamma ≤ |deriv source s|)
    (hfirstUpper : ∀ s ∈ active, |deriv source s| ≤ (9 / 5 : ℝ) * gamma)
    (hsecond : ∀ s ∈ active, |deriv (deriv source) s| ≤ C0 / 200) :
    ∀ t, gamma * t / C0 ∈ active →
      (6 / 5 : ℝ) ≤
          |deriv (node7AnisotropicNormalizedSlope source gamma C0) t| ∧
        |deriv (node7AnisotropicNormalizedSlope source gamma C0) t| ≤ 9 / 5 ∧
        |deriv (deriv
          (node7AnisotropicNormalizedSlope source gamma C0)) t| ≤ 1 / 200 := by
  intro t ht
  rw [node7AnisotropicNormalizedSlope_deriv source hgamma.ne' hC0.ne',
    node7AnisotropicNormalizedSlope_second_deriv source hgamma.ne' hC0.ne',
    abs_div, abs_of_pos hgamma, abs_div, abs_of_pos hC0]
  constructor
  · exact (le_div_iff₀ hgamma).2 (hfirstLower _ ht)
  constructor
  · exact (div_le_iff₀ hgamma).2 (hfirstUpper _ ht)
  · exact (div_le_iff₀ hC0).2 <| by
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        hsecond _ ht

end Kakeya.Assouad

end
