import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicProjectionIdentity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.MassPopularSubband
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LineClassSlopeCompatibleNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.IntervalSlopeJetExtension
import MyLeanRepo.Kakeya.Assouad.SlopeRescaling
import MyLeanRepo.Kakeya.Cinematic.TangencyIntervalExtension.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Slope normalization coupled to the final isotropic dilation

If the final positive similarity has scale `lambda`, the anisotropic slope
parameter is `(9/10) * band.slopeScale / lambda`.  The fixed margin leaves
room for an exact C2 jet extension at a final box touching the paper-height
boundary.  The two height
reparameterizations then cancel in the first derivative.  The exact coupled
slope is retained as the paper-facing interval function; a globally smooth
bundle is used only as an internal calculus witness.  Its value at zero is
deliberately not normalized: the frozen Node-6 interface does not require
`f 0 = 0`.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- Anisotropic slope scale paired with a later isotropic dilation.  The
factor `9/10` is a genuine geometric margin: the same value is used by the
configuration map and by the transported slope. -/
def pureWZ2CoupledAnisotropicSlopeScale
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta)
    (lambda : ℝ) : ℝ :=
  ((9 : ℝ) / 10 * band.slopeScale) / lambda

/-- Source height corresponding to a pre-isotropic normalized height. -/
def pureWZ2CoupledSourceHeight
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (centerHeight : ℝ) : ℝ :=
  subband.left + (subband.right - subband.left) / 2 * (centerHeight + 1)

/-- The exact slope after the anisotropic map with scale `slopeScale/lambda`
and the final isotropic dilation about `centerHeight`. -/
def pureWZ2CoupledExactSlope
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (centerHeight lambda t : ℝ) : ℝ :=
  anisotropicRescaledSlope band.lemma31.data.globalSlope
    subband.left subband.right
      (pureWZ2CoupledAnisotropicSlopeScale band lambda)
      (centerHeight + t / lambda)

/-- Globally smooth internal representative of the exact coupled formula.
The public Node-6 slope is its restriction to `[-1,1]`; this bundle does not
add any global derivative bounds to the paper-facing interface. -/
def pureWZ2CoupledExactSlopeFunction
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (centerHeight lambda : ℝ) : SlopeFunction where
  toFun := pureWZ2CoupledExactSlope subband centerHeight lambda
  contDiff := by
    have haffine : ContDiff ℝ 2 (fun t : ℝ =>
        subband.left + (subband.right - subband.left) / 2 *
          (centerHeight + t / lambda + 1)) := by
      fun_prop
    have hcomposed : ContDiff ℝ 2 (fun t : ℝ =>
        band.lemma31.data.globalSlope
          (subband.left + (subband.right - subband.left) / 2 *
            (centerHeight + t / lambda + 1))) :=
      band.lemma31.data.globalSlope.contDiff.comp haffine
    unfold pureWZ2CoupledExactSlope anisotropicRescaledSlope
      pureWZ2CoupledAnisotropicSlopeScale
    exact (hcomposed.div_const _).sub (contDiff_const.div_const _)

@[simp] theorem pureWZ2CoupledExactSlopeFunction_apply
    {sigma epsilon delta centerHeight lambda t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    pureWZ2CoupledExactSlopeFunction subband centerHeight lambda t =
      pureWZ2CoupledExactSlope subband centerHeight lambda t := rfl

/-- The exact anisotropic slope on the mass-popular subband is a globally
smooth internal witness whose normalized bounds are used only on its public
parameter interval. -/
theorem exists_pureWZ2SubbandExactSlopeFunction
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    ∃ slope : SlopeFunction,
      slope.IsNonsingular ∧
      ∀ t : ℝ, slope t =
        anisotropicRescaledSlope band.lemma31.data.globalSlope
          subband.left subband.right ((9 : ℝ) / 10 * band.slopeScale) t := by
  let normalizedScale : ℝ := (9 : ℝ) / 10 * band.slopeScale
  have hnormalizedScale : 0 < normalizedScale := by
    dsimp only [normalizedScale]
    exact mul_pos (by norm_num) band.slopeScale_pos
  have hsub : Set.Icc subband.left subband.right ⊆
      Set.Icc (-1 : ℝ) 1 := by
    intro z hz
    exact
      ⟨band.lemma31.data.scaleData.slabLeft_mem.trans
          (band.left_mem.trans (subband.left_mem.trans hz.1)),
        (hz.2.trans subband.right_mem).trans
          (band.right_mem.trans
            band.lemma31.data.scaleData.slabRight_mem)⟩
  have hderiv : ∀ z ∈ Set.Icc subband.left subband.right,
      normalizedScale ≤ |deriv band.lemma31.data.globalSlope z| ∧
        |deriv band.lemma31.data.globalSlope z| ≤
          2 * normalizedScale := by
    intro z hz
    have hband := band.derivative_band z
      ⟨subband.left_mem.trans hz.1, hz.2.trans subband.right_mem⟩
    have htight := band.derivative_tight_upper z
      ⟨subband.left_mem.trans hz.1, hz.2.trans subband.right_mem⟩
    constructor
    · dsimp only [normalizedScale]
      nlinarith [band.slopeScale_pos]
    · dsimp only [normalizedScale]
      nlinarith [band.slopeScale_lower]
  have hsecond : ∀ z ∈ Set.Icc subband.left subband.right,
      |deriv (deriv band.lemma31.data.globalSlope) z| ≤ 1 := by
    intro z hz
    exact (band.lemma31.data.globalSlope_normalized z (hsub hz)).2.2
  have hlength : subband.right - subband.left ≤ normalizedScale / 50 := by
    calc
      subband.right - subband.left =
          band.lemma31.data.rho.1 / 5000 := by
        rw [subband.length_eq, band.length_eq]
        ring
      _ ≤ band.slopeScale / 5000 :=
        div_le_div_of_nonneg_right band.slopeScale_lower (by norm_num)
      _ ≤ normalizedScale / 50 := by
        dsimp only [normalizedScale]
        nlinarith [band.slopeScale_pos]
  rcases slope_rescaling_to_centered_nonsingular_of_second
      band.lemma31.data.globalSlope subband.ordered hnormalizedScale
      hsub hderiv hsecond hlength with
    ⟨slope, hslope, _unusedCentering, hslopeFormula⟩
  exact ⟨slope, hslope, hslopeFormula⟩

/-- Exact coupled nonsingularity under the honest height-window condition.
The condition is intentionally explicit: an arbitrary center merely lying in
`[-1,1]` does not imply that `centerHeight + t/lambda` remains there. -/
theorem pureWZ2CoupledExactSlopeFunction_nonsingular_of_mapsTo
    {sigma epsilon delta centerHeight lambda : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hlambda : 1 ≤ lambda)
    (hsourceHeight : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      centerHeight + t / lambda ∈ Set.Icc (-1 : ℝ) 1) :
    (pureWZ2CoupledExactSlopeFunction subband centerHeight lambda).IsNonsingular := by
  rcases exists_pureWZ2SubbandExactSlopeFunction subband with
    ⟨source, hsource, hsourceFormula⟩
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  have hnormalized :=
    pureWZ2LineClassNormalizedSlope_nonsingular_of_mapsTo
      source hsource centerHeight hlambda hsourceHeight
  have heq : (pureWZ2CoupledExactSlopeFunction
      subband centerHeight lambda : ℝ → ℝ) =
      pureWZ2LineClassNormalizedSlope source centerHeight lambda := by
    funext t
    rw [pureWZ2CoupledExactSlopeFunction_apply]
    simp only [pureWZ2LineClassNormalizedSlope]
    rw [hsourceFormula]
    unfold pureWZ2CoupledExactSlope pureWZ2CoupledAnisotropicSlopeScale
      anisotropicRescaledSlope
    field_simp [hlambdaPos.ne', band.slopeScale_pos.ne',
      sub_ne_zero.mpr subband.ordered.ne']
  change ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    1 ≤ |deriv (pureWZ2CoupledExactSlopeFunction
      subband centerHeight lambda) z| ∧
    |deriv (pureWZ2CoupledExactSlopeFunction
      subband centerHeight lambda) z| ≤ 2 ∧
    |deriv (deriv (pureWZ2CoupledExactSlopeFunction
      subband centerHeight lambda)) z| ≤ 1 / 100
  rw [heq]
  exact hnormalized

/-- Paper-facing interval-domain form of exact coupled nonsingularity. -/
theorem pureWZ2CoupledExactSlope_public_nonsingular_of_mapsTo
    {sigma epsilon delta centerHeight lambda : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hlambda : 1 ≤ lambda)
    (hsourceHeight : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      centerHeight + t / lambda ∈ Set.Icc (-1 : ℝ) 1) :
    PureWZ2C2SlopeIsNonsingular
      (pureWZ2CoupledExactSlopeFunction subband centerHeight lambda).onUnitInterval :=
  SlopeFunction.nonsingular_onUnitInterval _
    (pureWZ2CoupledExactSlopeFunction_nonsingular_of_mapsTo
      subband hlambda hsourceHeight)

/-- Canonical C2 extension of the original global slope's two-jet from the
paper height interval.  This is internal provenance only; the final public
slope remains a function on `[-1,1]`. -/
noncomputable def pureWZ2CoupledSourceJetExtensionData
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) :
    PureWZ2IntervalSlopeJetExtensionData band.lemma31.data.globalSlope
      band.left band.right band.ordered.le :=
  Classical.choice
    (pureWZ2_intervalSlopeJetExtension band.lemma31.data.globalSlope
      band.ordered.le)

/-- Globally C2 source witness agreeing with the original slope on every
paper height. -/
noncomputable def pureWZ2CoupledSourceJetExtension
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) :
    SlopeFunction :=
  (pureWZ2CoupledSourceJetExtensionData band).slope

theorem pureWZ2CoupledSourceJetExtension_eq
    {sigma epsilon delta z : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta)
    (hz : z ∈ Set.Icc band.left band.right) :
    pureWZ2CoupledSourceJetExtension band z =
      band.lemma31.data.globalSlope z :=
  (pureWZ2CoupledSourceJetExtensionData band).eq_on z hz

theorem pureWZ2CoupledSourceJetExtension_deriv_eq
    {sigma epsilon delta z : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta)
    (hz : z ∈ Set.Icc band.left band.right) :
    deriv (pureWZ2CoupledSourceJetExtension band) z =
      deriv band.lemma31.data.globalSlope z :=
  (pureWZ2CoupledSourceJetExtensionData band).deriv_eq_on z hz

theorem pureWZ2CoupledSourceJetExtension_second_abs_le
    {sigma epsilon delta z : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) :
    |deriv (deriv (pureWZ2CoupledSourceJetExtension band)) z| ≤ 1 := by
  apply (pureWZ2CoupledSourceJetExtensionData band).second_deriv_abs_le
  intro x hx
  exact (band.lemma31.data.globalSlope_normalized x
    ⟨band.lemma31.data.scaleData.slabLeft_mem.trans
        (band.left_mem.trans hx.1),
      (hx.2.trans band.right_mem).trans
        band.lemma31.data.scaleData.slabRight_mem⟩).2.2

/-- Exact subband slope formed from the safe source two-jet extension. -/
noncomputable def pureWZ2CoupledMarginSlopeFunction
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) : SlopeFunction where
  toFun t := anisotropicRescaledSlope
    (pureWZ2CoupledSourceJetExtension band) subband.left subband.right
      ((9 : ℝ) / 10 * band.slopeScale) t
  contDiff := by
    have haffine : ContDiff ℝ 2 (fun t : ℝ =>
        subband.left + (subband.right - subband.left) / 2 * (t + 1)) := by
      fun_prop
    have hcomposed : ContDiff ℝ 2 (fun t : ℝ =>
        pureWZ2CoupledSourceJetExtension band
          (subband.left + (subband.right - subband.left) / 2 * (t + 1))) :=
      (pureWZ2CoupledSourceJetExtension band).contDiff.comp haffine
    unfold anisotropicRescaledSlope
    exact (hcomposed.div_const _).sub (contDiff_const.div_const _)

/-- Paper-faithful exact slope after the coupled final similarity. -/
noncomputable def pureWZ2CoupledPublicExactSlopeFunction
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (centerHeight lambda : ℝ) : SlopeFunction :=
  pureWZ2LineClassNormalizedSlope
    (pureWZ2CoupledMarginSlopeFunction subband) centerHeight lambda

theorem pureWZ2CoupledPublicExactSlopeFunction_apply
    {sigma epsilon delta centerHeight lambda t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hlambda : 0 < lambda) :
    pureWZ2CoupledPublicExactSlopeFunction subband centerHeight lambda t =
      anisotropicRescaledSlope (pureWZ2CoupledSourceJetExtension band)
        subband.left subband.right
        (pureWZ2CoupledAnisotropicSlopeScale band lambda)
        (centerHeight + t / lambda) := by
  unfold pureWZ2CoupledPublicExactSlopeFunction
    pureWZ2LineClassNormalizedSlope pureWZ2CoupledMarginSlopeFunction
    pureWZ2CoupledAnisotropicSlopeScale anisotropicRescaledSlope
  field_simp [hlambda.ne', band.slopeScale_pos.ne',
    sub_ne_zero.mpr subband.ordered.ne']

theorem pureWZ2CoupledMarginSlopeFunction_deriv
    {sigma epsilon delta t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    deriv (pureWZ2CoupledMarginSlopeFunction subband) t =
      deriv (pureWZ2CoupledSourceJetExtension band)
          (subband.left + (subband.right - subband.left) / 2 * (t + 1)) /
        ((9 : ℝ) / 10 * band.slopeScale) := by
  exact anisotropicRescaledSlope_deriv
    (pureWZ2CoupledSourceJetExtension band) subband.ordered
      (mul_pos (by norm_num) band.slopeScale_pos) t

theorem pureWZ2CoupledMarginSlopeFunction_second_deriv
    {sigma epsilon delta t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    deriv (deriv (pureWZ2CoupledMarginSlopeFunction subband)) t =
      deriv (deriv (pureWZ2CoupledSourceJetExtension band))
          (subband.left + (subband.right - subband.left) / 2 * (t + 1)) *
        (subband.right - subband.left) /
          (2 * ((9 : ℝ) / 10 * band.slopeScale)) := by
  exact anisotropicRescaledSlope_second_deriv
    (pureWZ2CoupledSourceJetExtension band) subband.ordered
      (mul_pos (by norm_num) band.slopeScale_pos) t

theorem pureWZ2CoupledPublicExactSlopeFunction_deriv
    {sigma epsilon delta centerHeight lambda t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hlambda : 0 < lambda) :
    deriv (pureWZ2CoupledPublicExactSlopeFunction
      subband centerHeight lambda) t =
      deriv (pureWZ2CoupledSourceJetExtension band)
          (pureWZ2CoupledSourceHeight subband
            (centerHeight + t / lambda)) /
        ((9 : ℝ) / 10 * band.slopeScale) := by
  unfold pureWZ2CoupledPublicExactSlopeFunction
  rw [pureWZ2LineClassNormalizedSlope_deriv _ _ hlambda,
    pureWZ2CoupledMarginSlopeFunction_deriv]
  rfl

theorem pureWZ2CoupledPublicExactSlopeFunction_second_deriv
    {sigma epsilon delta centerHeight lambda t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hlambda : 0 < lambda) :
    deriv (deriv (pureWZ2CoupledPublicExactSlopeFunction
      subband centerHeight lambda)) t =
      (1 / lambda) *
        (deriv (deriv (pureWZ2CoupledSourceJetExtension band))
            (pureWZ2CoupledSourceHeight subband
              (centerHeight + t / lambda)) *
          (subband.right - subband.left) /
            (2 * ((9 : ℝ) / 10 * band.slopeScale))) := by
  unfold pureWZ2CoupledPublicExactSlopeFunction
  rw [pureWZ2LineClassNormalizedSlope_second_deriv _ _ hlambda,
    pureWZ2CoupledMarginSlopeFunction_second_deriv]
  rfl

/-- The safety-margin exact slope is nonsingular on the whole public interval,
even when the final box center touches a paper-height endpoint. -/
theorem pureWZ2CoupledPublicExactSlopeFunction_nonsingular
    {sigma epsilon delta centerHeight lambda : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hlambda : 1 ≤ lambda)
    (hcenter : centerHeight ∈ Set.Icc (-1 : ℝ) 1) :
    (pureWZ2CoupledPublicExactSlopeFunction
      subband centerHeight lambda).IsNonsingular := by
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  have hcenterSource : pureWZ2CoupledSourceHeight subband centerHeight ∈
      Set.Icc band.left band.right := by
    have hlength : 0 < subband.right - subband.left :=
      sub_pos.mpr subband.ordered
    have hsub : pureWZ2CoupledSourceHeight subband centerHeight ∈
        Set.Icc subband.left subband.right := by
      unfold pureWZ2CoupledSourceHeight
      constructor
      · have hnonneg : 0 ≤ centerHeight + 1 := by linarith [hcenter.1]
        have : 0 ≤ (subband.right - subband.left) / 2 *
            (centerHeight + 1) := by positivity
        linarith
      · have htwo : centerHeight + 1 ≤ 2 := by linarith [hcenter.2]
        have hprod : (subband.right - subband.left) / 2 *
            (centerHeight + 1) ≤ subband.right - subband.left := by
          calc
            _ ≤ (subband.right - subband.left) / 2 * 2 := by gcongr
            _ = subband.right - subband.left := by ring
        linarith
    exact ⟨subband.left_mem.trans hsub.1, hsub.2.trans subband.right_mem⟩
  have hcurvature : ∀ x ∈ Set.Icc band.left band.right,
      |deriv (deriv band.lemma31.data.globalSlope) x| ≤ 1 := by
    intro x hx
    exact (band.lemma31.data.globalSlope_normalized x
      ⟨band.lemma31.data.scaleData.slabLeft_mem.trans
          (band.left_mem.trans hx.1),
        (hx.2.trans band.right_mem).trans
          band.lemma31.data.scaleData.slabRight_mem⟩).2.2
  intro t ht
  let sourcePoint := pureWZ2CoupledSourceHeight subband
    (centerHeight + t / lambda)
  let projected : ℝ := Set.projIcc band.left band.right
    band.ordered.le sourcePoint
  have hsourceDifference : sourcePoint -
      pureWZ2CoupledSourceHeight subband centerHeight =
        (subband.right - subband.left) / 2 * (t / lambda) := by
    dsimp only [sourcePoint, pureWZ2CoupledSourceHeight]
    ring
  have hsourceDistance : |sourcePoint -
      pureWZ2CoupledSourceHeight subband centerHeight| ≤
        (subband.right - subband.left) / 2 := by
    rw [hsourceDifference, abs_mul,
      abs_of_pos (div_pos (sub_pos.mpr subband.ordered) (by norm_num)),
      abs_div, abs_of_pos hlambdaPos]
    have htAbs : |t| ≤ 1 := abs_le.mpr ht
    have htDiv : |t| / lambda ≤ 1 := by
      apply (div_le_iff₀ hlambdaPos).2
      nlinarith
    have hhalfNonnegative : 0 ≤ (subband.right - subband.left) / 2 :=
      (div_pos (sub_pos.mpr subband.ordered) (by norm_num)).le
    exact mul_le_of_le_one_right hhalfNonnegative htDiv
  have hprojDistance : |sourcePoint - projected| ≤
      (subband.right - subband.left) / 2 := by
    exact (abs_sub_projIcc_le_of_mem band.ordered.le hcenterSource).trans
      hsourceDistance
  have hlengthSmall : subband.right - subband.left ≤
      band.slopeScale / 5000 := by
    calc
      subband.right - subband.left =
          band.lemma31.data.rho.1 / 5000 := by
        rw [subband.length_eq, band.length_eq]
        ring
      _ ≤ band.slopeScale / 5000 :=
        div_le_div_of_nonneg_right band.slopeScale_lower (by norm_num)
  have hprojDerivative := band.derivative_band projected
    (Set.projIcc band.left band.right band.ordered.le sourcePoint).property
  have hprojTight := band.derivative_tight_upper projected
    (Set.projIcc band.left band.right band.ordered.le sourcePoint).property
  have hderivDifference :
      |deriv (pureWZ2CoupledSourceJetExtension band) sourcePoint -
        deriv band.lemma31.data.globalSlope projected| ≤
          band.slopeScale / 10000 := by
    have hraw := (pureWZ2CoupledSourceJetExtensionData band).deriv_sub_proj_abs_le
      hcurvature sourcePoint
    change |deriv (pureWZ2CoupledSourceJetExtension band) sourcePoint -
        deriv band.lemma31.data.globalSlope projected| ≤ _ at hraw ⊢
    apply hraw.trans
    rw [one_mul]
    nlinarith [hlengthSmall]
  let extendedDeriv :=
    deriv (pureWZ2CoupledSourceJetExtension band) sourcePoint
  let sourceDeriv := deriv band.lemma31.data.globalSlope projected
  have habsDifference :
      abs (abs extendedDeriv - abs sourceDeriv) ≤
        band.slopeScale / 10000 := by
    exact (abs_abs_sub_abs_le_abs_sub extendedDeriv sourceDeriv).trans <| by
      simpa only [extendedDeriv, sourceDeriv] using hderivDifference
  have habsBounds := (abs_le.mp habsDifference)
  have hfirstLower : ((9 : ℝ) / 10 * band.slopeScale) ≤
      |deriv (pureWZ2CoupledSourceJetExtension band) sourcePoint| := by
    have hslopePos := band.slopeScale_pos
    dsimp only [extendedDeriv, sourceDeriv] at habsBounds
    nlinarith [hprojDerivative.1]
  have hfirstUpper :
      |deriv (pureWZ2CoupledSourceJetExtension band) sourcePoint| ≤
        2 * ((9 : ℝ) / 10 * band.slopeScale) := by
    have hrho : (band.lemma31.data.rho : ℝ) ≤ band.slopeScale :=
      band.slopeScale_lower
    have hslopePos := band.slopeScale_pos
    dsimp only [extendedDeriv, sourceDeriv] at habsBounds
    nlinarith [hprojTight]
  rw [pureWZ2CoupledPublicExactSlopeFunction_deriv subband hlambdaPos,
    abs_div, abs_of_pos (mul_pos (by norm_num) band.slopeScale_pos)]
  constructor
  · apply (le_div_iff₀ (mul_pos (by norm_num) band.slopeScale_pos)).2
    simpa only [one_mul, sourcePoint] using hfirstLower
  constructor
  · apply (div_le_iff₀ (mul_pos (by norm_num) band.slopeScale_pos)).2
    simpa only [sourcePoint] using hfirstUpper
  · rw [pureWZ2CoupledPublicExactSlopeFunction_second_deriv
      subband hlambdaPos]
    have hlengthPos : 0 < subband.right - subband.left :=
      sub_pos.mpr subband.ordered
    have hdenomPos : 0 < 2 * ((9 : ℝ) / 10 * band.slopeScale) :=
      mul_pos (by norm_num) (mul_pos (by norm_num) band.slopeScale_pos)
    rw [abs_mul, abs_of_pos (one_div_pos.mpr hlambdaPos),
      abs_div, abs_mul, abs_of_pos hlengthPos, abs_of_pos hdenomPos]
    have hsecond := pureWZ2CoupledSourceJetExtension_second_abs_le
      (z := sourcePoint) band
    have hratio : (subband.right - subband.left) /
        (2 * ((9 : ℝ) / 10 * band.slopeScale)) ≤ 1 / 9000 := by
      apply (div_le_iff₀ (mul_pos (by norm_num)
        (mul_pos (by norm_num) band.slopeScale_pos))).2
      have hslopePos := band.slopeScale_pos
      nlinarith
    have hinv : 1 / lambda ≤ 1 := (div_le_one hlambdaPos).2 hlambda
    have hratioNonnegative : 0 ≤ (subband.right - subband.left) /
        (2 * ((9 : ℝ) / 10 * band.slopeScale)) := by positivity
    calc
      (1 / lambda) *
          (|deriv (deriv (pureWZ2CoupledSourceJetExtension band)) sourcePoint| *
            (subband.right - subband.left) /
              (2 * ((9 : ℝ) / 10 * band.slopeScale))) ≤
        1 * (1 * ((subband.right - subband.left) /
          (2 * ((9 : ℝ) / 10 * band.slopeScale)))) := by
            apply mul_le_mul hinv ?_ (by positivity) (by norm_num)
            calc
              |deriv (deriv (pureWZ2CoupledSourceJetExtension band)) sourcePoint| *
                    (subband.right - subband.left) /
                      (2 * ((9 : ℝ) / 10 * band.slopeScale)) =
                  |deriv (deriv (pureWZ2CoupledSourceJetExtension band)) sourcePoint| *
                    ((subband.right - subband.left) /
                      (2 * ((9 : ℝ) / 10 * band.slopeScale))) := by ring
              _ ≤ 1 * ((subband.right - subband.left) /
                    (2 * ((9 : ℝ) / 10 * band.slopeScale))) :=
                mul_le_mul_of_nonneg_right hsecond hratioNonnegative
      _ ≤ 1 / 9000 := by simpa using hratio
      _ ≤ 1 / 100 := by norm_num

/-- Paper-facing interval certificate for the exact coupled slope. -/
theorem pureWZ2CoupledPublicExactSlope_nonsingular
    {sigma epsilon delta centerHeight lambda : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hlambda : 1 ≤ lambda)
    (hcenter : centerHeight ∈ Set.Icc (-1 : ℝ) 1) :
    PureWZ2C2SlopeIsNonsingular
      (pureWZ2CoupledPublicExactSlopeFunction
        subband centerHeight lambda).onUnitInterval :=
  SlopeFunction.nonsingular_onUnitInterval _
    (pureWZ2CoupledPublicExactSlopeFunction_nonsingular
      subband hlambda hcenter)

/-- Globally affine tangent to the coupled exact slope at target height zero.
The intercept is kept because final isotropic localization is generally not
centered at anisotropic height zero. -/
def pureWZ2CoupledAffineSlope
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (centerHeight lambda : ℝ) : SlopeFunction where
  toFun t :=
    pureWZ2CoupledExactSlope subband centerHeight lambda 0 +
      deriv band.lemma31.data.globalSlope
          (pureWZ2CoupledSourceHeight subband centerHeight) /
        ((9 : ℝ) / 10 * band.slopeScale) * t
  contDiff := by fun_prop

theorem pureWZ2CoupledAnisotropicSlopeScale_pos
    {sigma epsilon delta lambda : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta)
    (hlambda : 0 < lambda) :
    0 < pureWZ2CoupledAnisotropicSlopeScale band lambda := by
  exact div_pos (mul_pos (by norm_num) band.slopeScale_pos) hlambda

theorem pureWZ2CoupledAnisotropicSlopeScale_le
    {sigma epsilon delta lambda : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta)
    (hlambda : 1 ≤ lambda) :
    pureWZ2CoupledAnisotropicSlopeScale band lambda ≤ band.slopeScale := by
  unfold pureWZ2CoupledAnisotropicSlopeScale
  exact (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hlambda)).2 <| by
    nlinarith [band.slopeScale_pos]

theorem pureWZ2CoupledSourceHeight_mem
    {sigma epsilon delta centerHeight : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hcenter : centerHeight ∈ Set.Icc (-1 : ℝ) 1) :
    pureWZ2CoupledSourceHeight subband centerHeight ∈
      Set.Icc subband.left subband.right := by
  unfold pureWZ2CoupledSourceHeight
  have hlength : 0 < subband.right - subband.left :=
    sub_pos.mpr subband.ordered
  constructor
  · have hnonneg : 0 ≤ (centerHeight + 1) := by linarith [hcenter.1]
    have : 0 ≤ (subband.right - subband.left) / 2 *
        (centerHeight + 1) := by positivity
    linarith
  · have htwo : centerHeight + 1 ≤ 2 := by linarith [hcenter.2]
    have hprod : (subband.right - subband.left) / 2 *
        (centerHeight + 1) ≤ subband.right - subband.left := by
      calc
        (subband.right - subband.left) / 2 * (centerHeight + 1) ≤
            (subband.right - subband.left) / 2 * 2 := by gcongr
        _ = subband.right - subband.left := by ring
    linarith

theorem pureWZ2CoupledAffineSlope_deriv
    {sigma epsilon delta centerHeight lambda t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    deriv (pureWZ2CoupledAffineSlope subband centerHeight lambda) t =
      deriv band.lemma31.data.globalSlope
          (pureWZ2CoupledSourceHeight subband centerHeight) /
        ((9 : ℝ) / 10 * band.slopeScale) := by
  change deriv (fun x : ℝ =>
    pureWZ2CoupledExactSlope subband centerHeight lambda 0 +
      deriv band.lemma31.data.globalSlope
          (pureWZ2CoupledSourceHeight subband centerHeight) /
        ((9 : ℝ) / 10 * band.slopeScale) * x) t = _
  simpa using
    (((hasDerivAt_id t).const_mul
      (deriv band.lemma31.data.globalSlope
        (pureWZ2CoupledSourceHeight subband centerHeight) /
          ((9 : ℝ) / 10 * band.slopeScale))).const_add
        (pureWZ2CoupledExactSlope subband centerHeight lambda 0)).deriv

theorem pureWZ2CoupledAffineSlope_second_deriv
    {sigma epsilon delta centerHeight lambda t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    deriv (deriv (pureWZ2CoupledAffineSlope subband centerHeight lambda)) t = 0 := by
  have hfirst : deriv (pureWZ2CoupledAffineSlope subband centerHeight lambda) =
      fun _ : ℝ =>
        deriv band.lemma31.data.globalSlope
            (pureWZ2CoupledSourceHeight subband centerHeight) /
          ((9 : ℝ) / 10 * band.slopeScale) := by
    funext x
    exact pureWZ2CoupledAffineSlope_deriv subband
  rw [hfirst]
  exact (hasDerivAt_const t _).deriv

/-- The affine public slope is nonsingular on all of `[-1,1]`; only its
derivative is normalized, while its intercept remains geometrically aligned
with the final isotropic center. -/
theorem pureWZ2CoupledAffineSlope_nonsingular
    {sigma epsilon delta centerHeight lambda : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hcenter : centerHeight ∈ Set.Icc (-1 : ℝ) 1) :
    (pureWZ2CoupledAffineSlope subband centerHeight lambda).IsNonsingular := by
  have hsourceSub := pureWZ2CoupledSourceHeight_mem subband hcenter
  have hsourceBand : pureWZ2CoupledSourceHeight subband centerHeight ∈
      Set.Icc band.left band.right :=
    ⟨subband.left_mem.trans hsourceSub.1,
      hsourceSub.2.trans subband.right_mem⟩
  have hderivative := band.derivative_band
    (pureWZ2CoupledSourceHeight subband centerHeight) hsourceBand
  intro t _ht
  constructor
  · rw [pureWZ2CoupledAffineSlope_deriv, abs_div,
      abs_of_pos (mul_pos (by norm_num) band.slopeScale_pos)]
    calc
      1 ≤ band.slopeScale / ((9 : ℝ) / 10 * band.slopeScale) := by
        field_simp [band.slopeScale_pos.ne']
        norm_num
      _ ≤ |deriv band.lemma31.data.globalSlope
          (pureWZ2CoupledSourceHeight subband centerHeight)| /
            ((9 : ℝ) / 10 * band.slopeScale) :=
        div_le_div_of_nonneg_right hderivative.1
          (mul_nonneg (by norm_num) band.slopeScale_pos.le)
  · constructor
    · rw [pureWZ2CoupledAffineSlope_deriv, abs_div,
        abs_of_pos (mul_pos (by norm_num) band.slopeScale_pos)]
      have htight := band.derivative_tight_upper
        (pureWZ2CoupledSourceHeight subband centerHeight) hsourceBand
      apply (div_le_iff₀ (mul_pos (by norm_num) band.slopeScale_pos)).2
      nlinarith [band.slopeScale_lower]
    · rw [pureWZ2CoupledAffineSlope_second_deriv, abs_zero]
      norm_num

/-- The coupled public slope has an explicit bound on the normalized target
height interval.  The intercept is not assumed to vanish: its size is
controlled by integrating the derivative bracket from the midpoint of `J₀`
to the source height corresponding to the final isotropic center. -/
theorem pureWZ2CoupledAffineSlope_abs_le
    {sigma epsilon delta centerHeight lambda : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hlambda : 0 < lambda)
    (hcenter : centerHeight ∈ Set.Icc (-1 : ℝ) 1) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      |pureWZ2CoupledAffineSlope subband centerHeight lambda t| ≤
        3 * lambda + 2 := by
  let source := band.lemma31.data.globalSlope
  let sourceCenter := pureWZ2CoupledSourceHeight subband centerHeight
  let sourceMid := subband.left + (subband.right - subband.left) / 2
  have hsourceCenter : sourceCenter ∈ Set.Icc subband.left subband.right :=
    pureWZ2CoupledSourceHeight_mem subband hcenter
  have hsourceMid : sourceMid ∈ Set.Icc subband.left subband.right := by
    dsimp only [sourceMid]
    constructor <;> linarith [subband.ordered]
  have hinterval : Set.Icc subband.left subband.right ⊆
      Set.Icc band.left band.right := fun _ hz =>
    ⟨subband.left_mem.trans hz.1, hz.2.trans subband.right_mem⟩
  have hderivative : ∀ z ∈ Set.Icc subband.left subband.right,
      ‖deriv source z‖ ≤ 2 * band.slopeScale := by
    intro z hz
    have h := (band.derivative_band z (hinterval hz)).2
    simpa [source, Real.norm_eq_abs] using h
  have hvariationNorm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => source.contDiff.differentiable (by norm_num) |>.differentiableAt)
    hderivative (convex_Icc subband.left subband.right)
    hsourceMid hsourceCenter
  have hvariation :
      |source sourceCenter - source sourceMid| ≤
        2 * band.slopeScale * |sourceCenter - sourceMid| := by
    simpa [Real.norm_eq_abs] using hvariationNorm
  have hsourceDistance : |sourceCenter - sourceMid| ≤
      (subband.right - subband.left) / 2 := by
    have hlength : 0 ≤ (subband.right - subband.left) / 2 := by
      linarith [subband.ordered]
    have hcenterAbs : |centerHeight| ≤ 1 := by
      exact abs_le.mpr hcenter
    have heq : sourceCenter - sourceMid =
        (subband.right - subband.left) / 2 * centerHeight := by
      dsimp only [sourceCenter, sourceMid, pureWZ2CoupledSourceHeight]
      ring
    rw [heq, abs_mul]
    calc
      |(subband.right - subband.left) / 2| * |centerHeight| =
          (subband.right - subband.left) / 2 * |centerHeight| := by
            rw [abs_of_nonneg hlength]
      _ ≤ (subband.right - subband.left) / 2 * 1 := by gcongr
      _ = (subband.right - subband.left) / 2 := by ring
  have hnumerator : |source sourceCenter - source sourceMid| ≤
      band.slopeScale * (subband.right - subband.left) := by
    calc
      |source sourceCenter - source sourceMid| ≤
          2 * band.slopeScale * |sourceCenter - sourceMid| := hvariation
      _ ≤ 2 * band.slopeScale *
          ((subband.right - subband.left) / 2) := by
            exact mul_le_mul_of_nonneg_left hsourceDistance
              (mul_nonneg (by norm_num) band.slopeScale_pos.le)
      _ = band.slopeScale * (subband.right - subband.left) := by ring
  have hlengthPos : 0 < subband.right - subband.left :=
    sub_pos.mpr subband.ordered
  have hdenomPos : 0 < pureWZ2CoupledAnisotropicSlopeScale band lambda *
      (subband.right - subband.left) / 2 := by
    exact div_pos
      (mul_pos (pureWZ2CoupledAnisotropicSlopeScale_pos band hlambda)
        hlengthPos) (by norm_num)
  have hexactZero : pureWZ2CoupledExactSlope subband centerHeight lambda 0 =
      (source sourceCenter - source sourceMid) /
        (pureWZ2CoupledAnisotropicSlopeScale band lambda *
          (subband.right - subband.left) / 2) := by
    change
      source (subband.left + (subband.right - subband.left) / 2 *
          (centerHeight + 0 / lambda + 1)) /
            (pureWZ2CoupledAnisotropicSlopeScale band lambda *
              (subband.right - subband.left) / 2) -
        source (subband.left + (subband.right - subband.left) / 2) /
            (pureWZ2CoupledAnisotropicSlopeScale band lambda *
              (subband.right - subband.left) / 2) = _
    rw [show subband.left + (subband.right - subband.left) / 2 *
        (centerHeight + 0 / lambda + 1) = sourceCenter by
      simp [sourceCenter, pureWZ2CoupledSourceHeight]]
    rw [show subband.left + (subband.right - subband.left) / 2 = sourceMid by
      rfl]
    ring
  have hexactBound :
      |pureWZ2CoupledExactSlope subband centerHeight lambda 0| ≤
        3 * lambda := by
    rw [hexactZero, abs_div, abs_of_pos hdenomPos]
    apply (div_le_iff₀ hdenomPos).2
    calc
      |source sourceCenter - source sourceMid| ≤
          band.slopeScale * (subband.right - subband.left) := hnumerator
      _ ≤ 3 * lambda *
          (pureWZ2CoupledAnisotropicSlopeScale band lambda *
            (subband.right - subband.left) / 2) := by
        unfold pureWZ2CoupledAnisotropicSlopeScale
        field_simp [hlambda.ne', band.slopeScale_pos.ne', hlengthPos.ne']
        nlinarith [band.slopeScale_pos, hlambda]
  have hsourceBand : sourceCenter ∈ Set.Icc band.left band.right :=
    hinterval hsourceCenter
  have hderivBound :
      |deriv source sourceCenter / ((9 : ℝ) / 10 * band.slopeScale)| ≤ 2 := by
    rw [abs_div, abs_of_pos (mul_pos (by norm_num) band.slopeScale_pos)]
    apply (div_le_iff₀ (mul_pos (by norm_num) band.slopeScale_pos)).2
    have h := band.derivative_tight_upper sourceCenter hsourceBand
    dsimp only [source] at h ⊢
    have hrho : (band.lemma31.data.rho : ℝ) ≤ band.slopeScale :=
      band.slopeScale_lower
    nlinarith [hrho, band.slopeScale_pos]
  intro t ht
  change |pureWZ2CoupledExactSlope subband centerHeight lambda 0 +
      deriv source sourceCenter / ((9 : ℝ) / 10 * band.slopeScale) * t| ≤ _
  calc
    |pureWZ2CoupledExactSlope subband centerHeight lambda 0 +
        deriv source sourceCenter / ((9 : ℝ) / 10 * band.slopeScale) * t| ≤
      |pureWZ2CoupledExactSlope subband centerHeight lambda 0| +
        |deriv source sourceCenter / ((9 : ℝ) / 10 * band.slopeScale) * t| :=
          abs_add_le _ _
    _ ≤ 3 * lambda + 2 * 1 := by
      rw [abs_mul]
      gcongr
      exact abs_le.mpr ht
    _ = 3 * lambda + 2 := by ring

/-- Algebraic form of the error made by replacing the exact coupled slope by
its affine tangent at the final isotropic center. -/
theorem pureWZ2CoupledExactSlope_sub_affine_eq
    {sigma epsilon delta centerHeight lambda t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hlambda : 0 < lambda) :
    pureWZ2CoupledExactSlope subband centerHeight lambda t -
        pureWZ2CoupledAffineSlope subband centerHeight lambda t =
      (band.lemma31.data.globalSlope
          (pureWZ2CoupledSourceHeight subband (centerHeight + t / lambda)) -
        band.lemma31.data.globalSlope
          (pureWZ2CoupledSourceHeight subband centerHeight) -
        deriv band.lemma31.data.globalSlope
            (pureWZ2CoupledSourceHeight subband centerHeight) *
          (pureWZ2CoupledSourceHeight subband (centerHeight + t / lambda) -
            pureWZ2CoupledSourceHeight subband centerHeight)) /
        (pureWZ2CoupledAnisotropicSlopeScale band lambda *
          (subband.right - subband.left) / 2) := by
  change pureWZ2CoupledExactSlope subband centerHeight lambda t -
      (pureWZ2CoupledExactSlope subband centerHeight lambda 0 +
      deriv band.lemma31.data.globalSlope
            (pureWZ2CoupledSourceHeight subband centerHeight) /
          ((9 : ℝ) / 10 * band.slopeScale) * t) = _
  have hzero : pureWZ2CoupledExactSlope subband centerHeight lambda 0 =
      band.lemma31.data.globalSlope
          (pureWZ2CoupledSourceHeight subband centerHeight) /
            (pureWZ2CoupledAnisotropicSlopeScale band lambda *
              (subband.right - subband.left) / 2) -
        band.lemma31.data.globalSlope
          (subband.left + (subband.right - subband.left) / 2) /
            (pureWZ2CoupledAnisotropicSlopeScale band lambda *
              (subband.right - subband.left) / 2) := by
    simp [pureWZ2CoupledExactSlope, anisotropicRescaledSlope,
      pureWZ2CoupledSourceHeight]
  rw [hzero]
  unfold pureWZ2CoupledExactSlope anisotropicRescaledSlope
  have hscale : band.slopeScale ≠ 0 := band.slopeScale_pos.ne'
  have hlength : subband.right - subband.left ≠ 0 :=
    (sub_pos.mpr subband.ordered).ne'
  unfold pureWZ2CoupledSourceHeight pureWZ2CoupledAnisotropicSlopeScale
  field_simp [hlambda.ne', hscale, hlength]
  ring

/-- The affine public slope is globally two-Lipschitz.  Only the base point
used to define its derivative must come from the selected subband. -/
theorem pureWZ2CoupledAffineSlope_sub_le
    {sigma epsilon delta centerHeight lambda s t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hcenter : pureWZ2CoupledSourceHeight subband centerHeight ∈
      Set.Icc subband.left subband.right) :
    |pureWZ2CoupledAffineSlope subband centerHeight lambda s -
        pureWZ2CoupledAffineSlope subband centerHeight lambda t| ≤
      2 * |s - t| := by
  have hsourceBand : pureWZ2CoupledSourceHeight subband centerHeight ∈
      Set.Icc band.left band.right :=
    ⟨subband.left_mem.trans hcenter.1, hcenter.2.trans subband.right_mem⟩
  have hderivative := band.derivative_band
    (pureWZ2CoupledSourceHeight subband centerHeight) hsourceBand |>.2
  have hcoefficient :
      |deriv band.lemma31.data.globalSlope
          (pureWZ2CoupledSourceHeight subband centerHeight) /
            ((9 : ℝ) / 10 * band.slopeScale)| ≤ 2 := by
    rw [abs_div, abs_of_pos (mul_pos (by norm_num) band.slopeScale_pos)]
    apply (div_le_iff₀ (mul_pos (by norm_num) band.slopeScale_pos)).2
    have htight := band.derivative_tight_upper
      (pureWZ2CoupledSourceHeight subband centerHeight) hsourceBand
    nlinarith [band.slopeScale_lower]
  change |(pureWZ2CoupledExactSlope subband centerHeight lambda 0 +
        deriv band.lemma31.data.globalSlope
            (pureWZ2CoupledSourceHeight subband centerHeight) /
          ((9 : ℝ) / 10 * band.slopeScale) * s) -
      (pureWZ2CoupledExactSlope subband centerHeight lambda 0 +
        deriv band.lemma31.data.globalSlope
            (pureWZ2CoupledSourceHeight subband centerHeight) /
          ((9 : ℝ) / 10 * band.slopeScale) * t)| ≤ _
  rw [show
      (pureWZ2CoupledExactSlope subband centerHeight lambda 0 +
          deriv band.lemma31.data.globalSlope
              (pureWZ2CoupledSourceHeight subband centerHeight) /
            ((9 : ℝ) / 10 * band.slopeScale) * s) -
        (pureWZ2CoupledExactSlope subband centerHeight lambda 0 +
          deriv band.lemma31.data.globalSlope
              (pureWZ2CoupledSourceHeight subband centerHeight) /
            ((9 : ℝ) / 10 * band.slopeScale) * t) =
      (deriv band.lemma31.data.globalSlope
          (pureWZ2CoupledSourceHeight subband centerHeight) /
        ((9 : ℝ) / 10 * band.slopeScale)) * (s - t) by ring, abs_mul]
  exact mul_le_mul hcoefficient le_rfl (abs_nonneg _) (by norm_num)

/-- On every target height whose source preimage stays in the global paper
window, the exact coupled slope differs from its affine tangent by a
quadratic error with an explicit `lambda⁻¹` gain.  The larger interval is
needed for lower faces of cubical source cells, which may lie just outside
the mass-popular subband. -/
theorem pureWZ2CoupledExactSlope_close_affine_on_unit
    {sigma epsilon delta centerHeight lambda t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hlambda : 0 < lambda)
    (hcenter : pureWZ2CoupledSourceHeight subband centerHeight ∈
      Set.Icc (-1 : ℝ) 1)
    (htarget : pureWZ2CoupledSourceHeight subband
      (centerHeight + t / lambda) ∈ Set.Icc (-1 : ℝ) 1) :
    |pureWZ2CoupledExactSlope subband centerHeight lambda t -
        pureWZ2CoupledAffineSlope subband centerHeight lambda t| ≤
      t ^ 2 / (18000 * lambda) := by
  let source := band.lemma31.data.globalSlope
  let sourceCenter := pureWZ2CoupledSourceHeight subband centerHeight
  let sourceTarget := pureWZ2CoupledSourceHeight subband
    (centerHeight + t / lambda)
  have htaylor :
      |source sourceTarget - source sourceCenter -
          deriv source sourceCenter * (sourceTarget - sourceCenter)| ≤
        (1 / 2 : ℝ) * (sourceTarget - sourceCenter) ^ 2 := by
    apply Kakeya.Cinematic.taylor_remainder_bound_on_interval
      (source.contDiff.differentiable (by norm_num))
      source.contDiff.differentiable_deriv_two (by norm_num : (-1 : ℝ) ≤ 1)
      htarget hcenter
    intro point hpoint
    exact (band.lemma31.data.globalSlope_normalized point hpoint).2.2
  have hsourceDifference : sourceTarget - sourceCenter =
      (subband.right - subband.left) / 2 * (t / lambda) := by
    dsimp only [sourceTarget, sourceCenter, pureWZ2CoupledSourceHeight]
    ring
  have hlengthPos : 0 < subband.right - subband.left :=
    sub_pos.mpr subband.ordered
  have hdenomPos : 0 <
      pureWZ2CoupledAnisotropicSlopeScale band lambda *
        (subband.right - subband.left) / 2 := by
    exact div_pos
      (mul_pos (pureWZ2CoupledAnisotropicSlopeScale_pos band hlambda)
        hlengthPos) (by norm_num)
  have hlengthSmall : subband.right - subband.left ≤
      band.slopeScale / 5000 := by
    calc
      subband.right - subband.left =
          band.lemma31.data.rho.1 / 5000 := by
        rw [subband.length_eq, band.length_eq]
        ring
      _ ≤ band.slopeScale / 5000 :=
        div_le_div_of_nonneg_right band.slopeScale_lower (by norm_num)
  rw [pureWZ2CoupledExactSlope_sub_affine_eq subband hlambda, abs_div,
    abs_of_pos hdenomPos]
  calc
    |source sourceTarget - source sourceCenter -
          deriv source sourceCenter * (sourceTarget - sourceCenter)| /
        (pureWZ2CoupledAnisotropicSlopeScale band lambda *
          (subband.right - subband.left) / 2)
        ≤ ((1 / 2 : ℝ) * (sourceTarget - sourceCenter) ^ 2) /
            (pureWZ2CoupledAnisotropicSlopeScale band lambda *
              (subband.right - subband.left) / 2) := by
          exact (div_le_div_iff_of_pos_right hdenomPos).2 htaylor
    _ = (subband.right - subband.left) * t ^ 2 /
          (((18 : ℝ) / 5) * band.slopeScale * lambda) := by
      rw [hsourceDifference]
      unfold pureWZ2CoupledAnisotropicSlopeScale
      field_simp [hlambda.ne', band.slopeScale_pos.ne', hlengthPos.ne']
      ring
    _ = ((subband.right - subband.left) / band.slopeScale) *
          (t ^ 2 / (((18 : ℝ) / 5) * lambda)) := by
      field_simp [hlambda.ne', band.slopeScale_pos.ne']
    _ ≤ (1 / 5000 : ℝ) *
          (t ^ 2 / (((18 : ℝ) / 5) * lambda)) := by
      have hratio : (subband.right - subband.left) / band.slopeScale ≤
          1 / 5000 := by
        apply (div_le_iff₀ band.slopeScale_pos).2
        calc
          subband.right - subband.left ≤ band.slopeScale / 5000 :=
            hlengthSmall
          _ = (1 / 5000 : ℝ) * band.slopeScale := by ring
      exact mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = t ^ 2 / (18000 * lambda) := by
      field_simp [hlambda.ne']
      ring

/-- Subband-local compatibility wrapper for the original callers. -/
theorem pureWZ2CoupledExactSlope_close_affine
    {sigma epsilon delta centerHeight lambda t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hlambda : 0 < lambda)
    (hcenter : pureWZ2CoupledSourceHeight subband centerHeight ∈
      Set.Icc subband.left subband.right)
    (htarget : pureWZ2CoupledSourceHeight subband
      (centerHeight + t / lambda) ∈ Set.Icc subband.left subband.right) :
    |pureWZ2CoupledExactSlope subband centerHeight lambda t -
        pureWZ2CoupledAffineSlope subband centerHeight lambda t| ≤
      t ^ 2 / (18000 * lambda) := by
  have hleft : -1 ≤ subband.left :=
    band.lemma31.data.scaleData.slabLeft_mem.trans
      (band.left_mem.trans subband.left_mem)
  have hright : subband.right ≤ 1 :=
    subband.right_mem.trans <| band.right_mem.trans
      band.lemma31.data.scaleData.slabRight_mem
  exact pureWZ2CoupledExactSlope_close_affine_on_unit subband hlambda
    ⟨hleft.trans hcenter.1, hcenter.2.trans hright⟩
    ⟨hleft.trans htarget.1, htarget.2.trans hright⟩

@[simp] theorem pureWZ2CoupledAffineSlope_zero
    {sigma epsilon delta centerHeight lambda : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    pureWZ2CoupledAffineSlope subband centerHeight lambda 0 =
      pureWZ2CoupledExactSlope subband centerHeight lambda 0 := by
  simp [pureWZ2CoupledAffineSlope]

/-- At target height zero the public jet extension is literally the exact
transported geometric slope. -/
theorem pureWZ2CoupledPublicExactSlopeFunction_zero
    {sigma epsilon delta centerHeight lambda : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hlambda : 0 < lambda)
    (hcenter : centerHeight ∈ Set.Icc (-1 : ℝ) 1) :
    pureWZ2CoupledPublicExactSlopeFunction subband centerHeight lambda 0 =
      pureWZ2CoupledAffineSlope subband centerHeight lambda 0 := by
  rw [pureWZ2CoupledAffineSlope_zero,
    pureWZ2CoupledPublicExactSlopeFunction_apply subband hlambda]
  have hcenterSub := pureWZ2CoupledSourceHeight_mem subband hcenter
  have hcenterBand : pureWZ2CoupledSourceHeight subband centerHeight ∈
      Set.Icc band.left band.right :=
    ⟨subband.left_mem.trans hcenterSub.1,
      hcenterSub.2.trans subband.right_mem⟩
  have hmidBand : subband.left + (subband.right - subband.left) / 2 ∈
      Set.Icc band.left band.right := by
    constructor <;> linarith [subband.left_mem, subband.right_mem,
      subband.ordered]
  have hzeroSource : subband.left + (subband.right - subband.left) / 2 *
      (centerHeight + 0 / lambda + 1) =
      pureWZ2CoupledSourceHeight subband centerHeight := by
    simp [pureWZ2CoupledSourceHeight]
  unfold pureWZ2CoupledExactSlope anisotropicRescaledSlope
  rw [hzeroSource]
  rw [pureWZ2CoupledSourceJetExtension_eq band hcenterBand,
    pureWZ2CoupledSourceJetExtension_eq band hmidBand]

/-- At target height zero the public jet extension and the affine comparison
slope also have the same first derivative. -/
theorem pureWZ2CoupledPublicExactSlopeFunction_deriv_zero
    {sigma epsilon delta centerHeight lambda : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hlambda : 0 < lambda)
    (hcenter : centerHeight ∈ Set.Icc (-1 : ℝ) 1) :
    deriv (pureWZ2CoupledPublicExactSlopeFunction
        subband centerHeight lambda) 0 =
      deriv (pureWZ2CoupledAffineSlope subband centerHeight lambda) 0 := by
  rw [pureWZ2CoupledPublicExactSlopeFunction_deriv subband hlambda,
    pureWZ2CoupledAffineSlope_deriv]
  have hcenterSub := pureWZ2CoupledSourceHeight_mem subband hcenter
  have hcenterBand : pureWZ2CoupledSourceHeight subband centerHeight ∈
      Set.Icc band.left band.right :=
    ⟨subband.left_mem.trans hcenterSub.1,
      hcenterSub.2.trans subband.right_mem⟩
  rw [show centerHeight + 0 / lambda = centerHeight by ring,
    pureWZ2CoupledSourceJetExtension_deriv_eq band hcenterBand]

/-- The exact public extension has a uniform global curvature bound. -/
theorem pureWZ2CoupledPublicExactSlopeFunction_second_abs_le
    {sigma epsilon delta centerHeight lambda t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hlambda : 1 ≤ lambda) :
    |deriv (deriv (pureWZ2CoupledPublicExactSlopeFunction
      subband centerHeight lambda)) t| ≤ 1 / 9000 := by
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  rw [pureWZ2CoupledPublicExactSlopeFunction_second_deriv subband hlambdaPos]
  have hlengthPos : 0 < subband.right - subband.left :=
    sub_pos.mpr subband.ordered
  have hdenomPos : 0 < 2 * ((9 : ℝ) / 10 * band.slopeScale) :=
    mul_pos (by norm_num) (mul_pos (by norm_num) band.slopeScale_pos)
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hlambdaPos),
    abs_div, abs_mul, abs_of_pos hlengthPos, abs_of_pos hdenomPos]
  have hsecond := pureWZ2CoupledSourceJetExtension_second_abs_le
    (z := pureWZ2CoupledSourceHeight subband (centerHeight + t / lambda)) band
  have hlengthSmall : subband.right - subband.left ≤
      band.slopeScale / 5000 := by
    calc
      subband.right - subband.left =
          band.lemma31.data.rho.1 / 5000 := by
        rw [subband.length_eq, band.length_eq]
        ring
      _ ≤ band.slopeScale / 5000 :=
        div_le_div_of_nonneg_right band.slopeScale_lower (by norm_num)
  have hratio : (subband.right - subband.left) /
      (2 * ((9 : ℝ) / 10 * band.slopeScale)) ≤ 1 / 9000 := by
    apply (div_le_iff₀ hdenomPos).2
    nlinarith [band.slopeScale_pos]
  have hinv : 1 / lambda ≤ 1 := (div_le_one hlambdaPos).2 hlambda
  have hratioNonnegative : 0 ≤ (subband.right - subband.left) /
      (2 * ((9 : ℝ) / 10 * band.slopeScale)) := by positivity
  calc
    (1 / lambda) *
        (|deriv (deriv (pureWZ2CoupledSourceJetExtension band))
            (pureWZ2CoupledSourceHeight subband
              (centerHeight + t / lambda))| *
          (subband.right - subband.left) /
            (2 * ((9 : ℝ) / 10 * band.slopeScale))) ≤
      1 * (1 * ((subband.right - subband.left) /
        (2 * ((9 : ℝ) / 10 * band.slopeScale)))) := by
          apply mul_le_mul hinv ?_ (by positivity) (by norm_num)
          calc
            _ = |deriv (deriv (pureWZ2CoupledSourceJetExtension band))
                  (pureWZ2CoupledSourceHeight subband
                    (centerHeight + t / lambda))| *
                ((subband.right - subband.left) /
                  (2 * ((9 : ℝ) / 10 * band.slopeScale))) := by ring
            _ ≤ 1 * ((subband.right - subband.left) /
                  (2 * ((9 : ℝ) / 10 * band.slopeScale))) :=
              mul_le_mul_of_nonneg_right hsecond hratioNonnegative
    _ ≤ 1 / 9000 := by simpa using hratio

/-- The exact public slope differs from the proof-only affine tangent by its
quadratic C2 remainder. -/
theorem pureWZ2CoupledPublicExactSlope_close_affine
    {sigma epsilon delta centerHeight lambda t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hlambda : 1 ≤ lambda)
    (hcenter : centerHeight ∈ Set.Icc (-1 : ℝ) 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |pureWZ2CoupledPublicExactSlopeFunction subband centerHeight lambda t -
        pureWZ2CoupledAffineSlope subband centerHeight lambda t| ≤
      t ^ 2 / 18000 := by
  let exact := pureWZ2CoupledPublicExactSlopeFunction
    subband centerHeight lambda
  have htaylor : |exact t - exact 0 - deriv exact 0 * (t - 0)| ≤
      (1 / 9000 : ℝ) / 2 * (t - 0) ^ 2 := by
    exact Kakeya.Cinematic.taylor_remainder_bound_on_interval
      (d := 1 / 9000) (a := -1) (b := 1) (x := t) (y := 0)
      (exact.contDiff.differentiable (by norm_num))
      exact.contDiff.differentiable_deriv_two (by norm_num : (-1 : ℝ) ≤ 1)
      ht (by norm_num)
      (fun point _hpoint =>
        pureWZ2CoupledPublicExactSlopeFunction_second_abs_le subband hlambda)
  rw [pureWZ2CoupledPublicExactSlopeFunction_zero subband
      (lt_of_lt_of_le (by norm_num) hlambda) hcenter,
    pureWZ2CoupledPublicExactSlopeFunction_deriv_zero subband
      (lt_of_lt_of_le (by norm_num) hlambda) hcenter] at htaylor
  have haffineFormula : pureWZ2CoupledAffineSlope subband centerHeight lambda t =
      pureWZ2CoupledAffineSlope subband centerHeight lambda 0 +
        deriv (pureWZ2CoupledAffineSlope subband centerHeight lambda) 0 * t := by
    simp [pureWZ2CoupledAffineSlope, pureWZ2CoupledAffineSlope_deriv]
  rw [haffineFormula]
  dsimp only [exact] at htaylor
  rw [show
      pureWZ2CoupledPublicExactSlopeFunction subband centerHeight lambda t -
          (pureWZ2CoupledAffineSlope subband centerHeight lambda 0 +
            deriv (pureWZ2CoupledAffineSlope subband centerHeight lambda) 0 * t) =
        pureWZ2CoupledPublicExactSlopeFunction subband centerHeight lambda t -
          pureWZ2CoupledAffineSlope subband centerHeight lambda 0 -
            deriv (pureWZ2CoupledAffineSlope subband centerHeight lambda) 0 *
              (t - 0) by ring]
  calc
    _ ≤ (1 / 9000 : ℝ) / 2 * (t - 0) ^ 2 := htaylor
    _ = t ^ 2 / 18000 := by ring

/-- Uniform value bound used by the final projection-thickening estimate. -/
theorem pureWZ2CoupledPublicExactSlope_abs_le
    {sigma epsilon delta centerHeight lambda t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hlambda : 1 ≤ lambda)
    (hcenter : centerHeight ∈ Set.Icc (-1 : ℝ) 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |pureWZ2CoupledPublicExactSlopeFunction subband centerHeight lambda t| ≤
      3 * lambda + 3 := by
  have hclose := pureWZ2CoupledPublicExactSlope_close_affine
    subband hlambda hcenter ht
  have haffine := pureWZ2CoupledAffineSlope_abs_le subband
    (lt_of_lt_of_le (by norm_num) hlambda) hcenter t ht
  have htriangle :
      |pureWZ2CoupledPublicExactSlopeFunction subband centerHeight lambda t| ≤
        |pureWZ2CoupledAffineSlope subband centerHeight lambda t| +
        |pureWZ2CoupledPublicExactSlopeFunction subband centerHeight lambda t -
          pureWZ2CoupledAffineSlope subband centerHeight lambda t| := by
    calc
      _ = |pureWZ2CoupledAffineSlope subband centerHeight lambda t +
          (pureWZ2CoupledPublicExactSlopeFunction subband centerHeight lambda t -
            pureWZ2CoupledAffineSlope subband centerHeight lambda t)| := by
              congr 1
              ring
      _ ≤ _ := abs_add_le _ _
  calc
    _ ≤ |pureWZ2CoupledAffineSlope subband centerHeight lambda t| +
        |pureWZ2CoupledPublicExactSlopeFunction subband centerHeight lambda t -
          pureWZ2CoupledAffineSlope subband centerHeight lambda t| := htriangle
    _ ≤ (3 * lambda + 2) + t ^ 2 / 18000 := add_le_add haffine hclose
    _ ≤ 3 * lambda + 3 := by
      have htAbs : |t| ≤ 1 := abs_le.mpr ht
      rw [← sq_abs t]
      nlinarith [sq_nonneg (|t| - 1), abs_nonneg t]

end Kakeya.Assouad

end
