import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicSection6ScaleBounds
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CoupledCompletedNormal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CoupledIsotropicSlope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicJointLocalGrainScale

/-!
# Coupled anisotropic and final-isotropic scales

The anisotropic parameter cannot be chosen independently of the final
similarity.  We use one fixed large similarity and set
`m = slopeScale / lambda`.  Lemma 31 makes the original scale small enough
for the centered-conflict estimate.  Fixing the similarity is essential:
it keeps the public slope and final cubical projection losses absolute.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The fixed final similarity selected before the small source scale. -/
def pureWZ2CoupledFinalScale
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (_subband : PureWZ2MassPopularSubbandData band) : ℝ :=
  pureWZ2CoupledScaleRequirement

/-- The anisotropic slope parameter paired with the selected final
similarity. -/
def pureWZ2CoupledFinalSlopeScale
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) : ℝ :=
  pureWZ2CoupledAnisotropicSlopeScale band
    (pureWZ2CoupledFinalScale subband)

/-- The final tube radius after the coupled similarity. -/
def pureWZ2CoupledFinalDelta
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) : ℝ :=
  16 * pureWZ2CoupledFinalScale subband *
      anisotropicPaperAlignedScale delta subband.left subband.right +
    2 * band.slopeScale * (subband.right - subband.left)

/-- Fixed coefficient comparing the final coupled radius with the Lemma-31
power scale. -/
def pureWZ2CoupledFinalDeltaUpperConstant : ℝ :=
  2560000 * pureWZ2CoupledScaleRequirement + 1

theorem pureWZ2CoupledFinalDeltaUpperConstant_pos :
    0 < pureWZ2CoupledFinalDeltaUpperConstant := by
  unfold pureWZ2CoupledFinalDeltaUpperConstant
  nlinarith [pureWZ2CoupledScaleRequirement_pos]

/-- All scale inequalities needed by the two retubings, the final cubical
saturation, and the completed common-slice normal. -/
structure PureWZ2CoupledScaleData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) where
  lambda_pos : 0 < pureWZ2CoupledFinalScale subband
  lambda_requirement : pureWZ2CoupledScaleRequirement ≤
    pureWZ2CoupledFinalScale subband
  m_pos : 0 < pureWZ2CoupledFinalSlopeScale subband
  m_le_band : pureWZ2CoupledFinalSlopeScale subband ≤ band.slopeScale
  conflict_width_le_one : anisotropicPaperConflictWidth
    (anisotropicPaperAlignedScale delta subband.left subband.right)
    subband.left subband.right (pureWZ2CoupledFinalSlopeScale subband) ≤ 1
  final_delta_pos : 0 < pureWZ2CoupledFinalDelta subband
  final_delta_le_twenty_four : pureWZ2CoupledFinalDelta subband ≤ 1 / 24

namespace PureWZ2CoupledScaleData

theorem lambda_one
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband) :
    1 ≤ pureWZ2CoupledFinalScale subband := by
  have hrequirement : 1 ≤ pureWZ2CoupledScaleRequirement := by
    unfold pureWZ2CoupledScaleRequirement
    exact (by norm_num : (1 : ℝ) ≤ 15000).trans (le_max_left _ _)
  exact hrequirement.trans data.lambda_requirement

theorem m_le_one
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband) :
    pureWZ2CoupledFinalSlopeScale subband ≤ 1 :=
  data.m_le_band.trans band.slopeScale_le_one

theorem lambda_mul_preDelta_eq
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (_data : PureWZ2CoupledScaleData subband) :
    pureWZ2CoupledFinalScale subband *
        anisotropicPaperAlignedScale delta subband.left subband.right =
      pureWZ2CoupledScaleRequirement *
        anisotropicPaperAlignedScale delta subband.left subband.right := rfl

theorem lambda_mul_preDelta_le
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband) :
    pureWZ2CoupledFinalScale subband *
        anisotropicPaperAlignedScale delta subband.left subband.right ≤
      1 / 1000 := by
  rw [data.lambda_mul_preDelta_eq]
  let rho := band.lemma31.data.rho.1
  have hrhoPos : 0 < rho :=
    band.lemma31.data.cfg.extremal.delta_pos.trans_le
      band.lemma31.data.rho.2.1
  have hpreUpper := subband.anisotropic_alignedScale_upper
  have hscaledRho : pureWZ2CoupledConflictConstant *
      pureWZ2CoupledScaleRequirement * rho ≤ 1 := by
    have hpositive : 0 < pureWZ2CoupledConflictConstant *
        pureWZ2CoupledScaleRequirement := mul_pos (by
      unfold pureWZ2CoupledConflictConstant
      norm_num) pureWZ2CoupledScaleRequirement_pos
    have h := (le_div_iff₀ hpositive).mp band.lemma31.rho_coupled_tiny
    simpa only [rho, mul_assoc, mul_left_comm, mul_comm] using h
  have hdeltaRho : delta / rho ≤ rho := by
    rw [div_le_iff₀ hrhoPos]
    simpa [pow_two] using band.lemma31.delta_le_rho_sq
  calc
    pureWZ2CoupledScaleRequirement *
        anisotropicPaperAlignedScale delta subband.left subband.right ≤
      pureWZ2CoupledScaleRequirement * (160000 * delta / rho) := by
        exact mul_le_mul_of_nonneg_left hpreUpper.le
          pureWZ2CoupledScaleRequirement_pos.le
    _ ≤ pureWZ2CoupledScaleRequirement * (160000 * rho) := by
      have hscaled : 160000 * delta / rho ≤ 160000 * rho := by
        calc
          160000 * delta / rho = 160000 * (delta / rho) := by ring
          _ ≤ 160000 * rho := by gcongr
      exact mul_le_mul_of_nonneg_left hscaled
        pureWZ2CoupledScaleRequirement_pos.le
    _ ≤ 1 / 1000 := by
      have hconflict : (0 : ℝ) < pureWZ2CoupledConflictConstant := by
        unfold pureWZ2CoupledConflictConstant
        norm_num
      unfold pureWZ2CoupledConflictConstant at hscaledRho
      nlinarith

theorem final_delta_eq
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (_data : PureWZ2CoupledScaleData subband) :
    pureWZ2CoupledFinalDelta subband =
      16 * pureWZ2CoupledScaleRequirement *
          anisotropicPaperAlignedScale delta subband.left subband.right +
        2 * band.slopeScale * (subband.right - subband.left) := by
  rfl

theorem final_radius_budget
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband) :
    pureWZ2CoupledFinalScale subband *
          (6 * anisotropicPaperAlignedScale delta subband.left subband.right) +
        pureWZ2CoupledFinalDelta subband * Real.sqrt 3 ≤
      6 * pureWZ2CoupledFinalDelta subband := by
  have hsqrt : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg 3]
  have hproductPos : 0 < pureWZ2CoupledFinalScale subband *
      anisotropicPaperAlignedScale delta subband.left subband.right :=
    mul_pos data.lambda_pos subband.anisotropic_alignedScale_pos
  have hlengthPos : 0 < subband.right - subband.left :=
    sub_pos.mpr subband.ordered
  have hbonusNonneg : 0 ≤
      2 * band.slopeScale * (subband.right - subband.left) :=
    mul_nonneg (mul_nonneg (by norm_num) band.slopeScale_pos.le) hlengthPos.le
  unfold pureWZ2CoupledFinalDelta
  nlinarith

theorem completed_targetK_budget
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband) :
    (96 : ℝ) ≤ (pureWZ2FinalIsotropicTargetK : ℝ) *
      pureWZ2CoupledFinalScale subband := by
  have hLPos : 0 < (lipschitzExtensionConstant Point3 : ℝ) :=
    lipschitzExtensionConstant_pos Point3
  have hscale : 1536 * (lipschitzExtensionConstant Point3 : ℝ) ≤
      pureWZ2CoupledFinalScale subband := by
    have hcomponent : 1536 * (lipschitzExtensionConstant Point3 : ℝ) ≤
        pureWZ2CoupledScaleRequirement := by
      unfold pureWZ2CoupledScaleRequirement
      exact le_max_right _ _
    exact hcomponent.trans data.lambda_requirement
  change 96 ≤ (1 / (16 * (lipschitzExtensionConstant Point3 : ℝ))) *
    pureWZ2CoupledFinalScale subband
  rw [show (1 / (16 * (lipschitzExtensionConstant Point3 : ℝ))) *
      pureWZ2CoupledFinalScale subband =
    pureWZ2CoupledFinalScale subband /
      (16 * (lipschitzExtensionConstant Point3 : ℝ)) by ring]
  apply (le_div_iff₀ (mul_pos (by norm_num) hLPos)).2
  calc
    96 * (16 * (lipschitzExtensionConstant Point3 : ℝ)) =
        1536 * (lipschitzExtensionConstant Point3 : ℝ) := by ring
    _ ≤ pureWZ2CoupledFinalScale subband := hscale

theorem completed_extension_one
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (_data : PureWZ2CoupledScaleData subband) :
    4 * ((lipschitzExtensionConstant Point3 *
      pureWZ2FinalIsotropicTargetK : NNReal) : ℝ) ≤ 1 := by
  have hLPos : 0 < (lipschitzExtensionConstant Point3 : ℝ) :=
    lipschitzExtensionConstant_pos Point3
  change 4 * ((lipschitzExtensionConstant Point3 : ℝ) *
    (1 / (16 * (lipschitzExtensionConstant Point3 : ℝ)))) ≤ 1
  field_simp [hLPos.ne']
  norm_num

theorem completed_extension_error_eq
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (_data : PureWZ2CoupledScaleData subband) :
    4 * ((lipschitzExtensionConstant Point3 *
        pureWZ2FinalIsotropicTargetK : NNReal) : ℝ) *
        (pureWZ2CoupledFinalDelta subband * Real.sqrt 3) =
      (pureWZ2CoupledFinalDelta subband * Real.sqrt 3) / 4 := by
  have hLPos : 0 < (lipschitzExtensionConstant Point3 : ℝ) :=
    lipschitzExtensionConstant_pos Point3
  change 4 * ((lipschitzExtensionConstant Point3 : ℝ) *
      (1 / (16 * (lipschitzExtensionConstant Point3 : ℝ)))) * _ = _
  field_simp [hLPos.ne']
  ring

theorem completed_extension_small
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband) :
    ((lipschitzExtensionConstant Point3 *
        pureWZ2FinalIsotropicTargetK : NNReal) : ℝ) *
        (pureWZ2CoupledFinalDelta subband * Real.sqrt 3) ≤ 1 / 2 := by
  have hsqrt : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg 3]
  have hLPos : 0 < (lipschitzExtensionConstant Point3 : ℝ) :=
    lipschitzExtensionConstant_pos Point3
  change (lipschitzExtensionConstant Point3 : ℝ) *
      (1 / (16 * (lipschitzExtensionConstant Point3 : ℝ))) *
        (pureWZ2CoupledFinalDelta subband * Real.sqrt 3) ≤ 1 / 2
  have hproduct : pureWZ2CoupledFinalDelta subband * Real.sqrt 3 ≤
      1 / 12 := by
    calc
      pureWZ2CoupledFinalDelta subband * Real.sqrt 3 ≤
          (1 / 24 : ℝ) * 2 := by
        exact mul_le_mul data.final_delta_le_twenty_four hsqrt
          (Real.sqrt_nonneg 3) (by norm_num)
      _ = 1 / 12 := by norm_num
  field_simp [hLPos.ne']
  nlinarith

theorem lambda_mul_m
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband) :
    pureWZ2CoupledFinalScale subband *
        pureWZ2CoupledFinalSlopeScale subband =
      (9 : ℝ) / 10 * band.slopeScale := by
  unfold pureWZ2CoupledFinalSlopeScale
    pureWZ2CoupledAnisotropicSlopeScale
  field_simp [data.lambda_pos.ne']

theorem m_mul_length_sq
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (_data : PureWZ2CoupledScaleData subband) :
    pureWZ2CoupledFinalSlopeScale subband *
        (subband.right - subband.left) ^ 2 =
      ((9 : ℝ) / 10 * band.slopeScale) /
          pureWZ2CoupledScaleRequirement *
        (subband.right - subband.left) ^ 2 := rfl

theorem source_delta_le_final
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband) :
    delta ≤ pureWZ2CoupledFinalDelta subband := by
  have hpre : delta ≤ anisotropicPaperAlignedScale delta
      subband.left subband.right := subband.delta_le_anisotropic_alignedScale
  have hpreNonneg : 0 ≤ anisotropicPaperAlignedScale delta
      subband.left subband.right := subband.anisotropic_alignedScale_pos.le
  have hbonusNonneg : 0 ≤
      2 * band.slopeScale * (subband.right - subband.left) :=
    mul_nonneg (mul_nonneg (by norm_num) band.slopeScale_pos.le)
      (sub_nonneg.mpr subband.ordered.le)
  unfold pureWZ2CoupledFinalDelta
  calc
    delta ≤ anisotropicPaperAlignedScale delta subband.left subband.right := hpre
    _ ≤ pureWZ2CoupledFinalScale subband *
        anisotropicPaperAlignedScale delta subband.left subband.right :=
      le_mul_of_one_le_left hpreNonneg data.lambda_one
    _ ≤ 16 * pureWZ2CoupledFinalScale subband *
          anisotropicPaperAlignedScale delta subband.left subband.right := by
      nlinarith [mul_pos data.lambda_pos subband.anisotropic_alignedScale_pos]
    _ ≤ 16 * pureWZ2CoupledFinalScale subband *
          anisotropicPaperAlignedScale delta subband.left subband.right +
        2 * band.slopeScale * (subband.right - subband.left) :=
      le_add_of_nonneg_right hbonusNonneg

/-- The final coupled radius is bounded by a fixed multiple of the selected
Lemma-31 scale.  In particular, its dependence on the runtime source scale
is exactly through `rho = delta^epsilon`. -/
theorem final_delta_le_rho
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (_data : PureWZ2CoupledScaleData subband) :
    pureWZ2CoupledFinalDelta subband ≤
      pureWZ2CoupledFinalDeltaUpperConstant *
        band.lemma31.data.rho.1 := by
  have hpre := subband.anisotropic_alignedScale_le_rho
  have hlength : subband.right - subband.left =
      band.lemma31.data.rho.1 / 5000 := by
    rw [subband.length_eq, band.length_eq]
    ring
  have hslope : band.slopeScale ≤ 1 := band.slopeScale_le_one
  have hrho : 0 ≤ band.lemma31.data.rho.1 :=
    (band.lemma31.data.cfg.extremal.delta_pos.trans_le
      band.lemma31.data.rho.2.1).le
  unfold pureWZ2CoupledFinalDelta pureWZ2CoupledFinalDeltaUpperConstant
    pureWZ2CoupledFinalScale
  rw [hlength]
  calc
    16 * pureWZ2CoupledScaleRequirement *
          anisotropicPaperAlignedScale delta subband.left subband.right +
        2 * band.slopeScale * (band.lemma31.data.rho.1 / 5000) ≤
      16 * pureWZ2CoupledScaleRequirement *
          (160000 * band.lemma31.data.rho.1) +
        2 * 1 * (band.lemma31.data.rho.1 / 5000) := by
      gcongr
      exact mul_nonneg (by norm_num) pureWZ2CoupledScaleRequirement_pos.le
    _ ≤ (2560000 * pureWZ2CoupledScaleRequirement + 1) *
          band.lemma31.data.rho.1 := by
      have hrequirement : 0 ≤ pureWZ2CoupledScaleRequirement :=
        pureWZ2CoupledScaleRequirement_pos.le
      nlinarith

theorem final_delta_le_source_power
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband) :
    pureWZ2CoupledFinalDelta subband ≤
      pureWZ2CoupledFinalDeltaUpperConstant *
        Real.rpow delta epsilon := by
  rw [← band.lemma31.data.rho_eq_power]
  exact data.final_delta_le_rho

/-- Any prescribed positive final-radius ceiling can be imposed before the
runtime derivative band and subband are selected. -/
theorem exists_sourceDelta_for_coupled_final_le
    (epsilon target : ℝ) (hepsilon : 0 < epsilon) (htarget : 0 < target) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sigma delta : ℝ}
        {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
        {subband : PureWZ2MassPopularSubbandData band},
        PureWZ2CoupledScaleData subband →
        0 < delta → delta ≤ delta₀ →
        pureWZ2CoupledFinalDelta subband ≤ target := by
  let cap : ℝ := min
    (target / pureWZ2CoupledFinalDeltaUpperConstant) (1 / 2)
  have hcap : 0 < cap := by
    dsimp only [cap]
    exact lt_min (div_pos htarget
      pureWZ2CoupledFinalDeltaUpperConstant_pos) (by norm_num)
  have hcapOne : cap < 1 :=
    (min_le_right _ _).trans_lt (by norm_num)
  rcases exists_delta_rpow_le_single epsilon cap hepsilon hcap hcapOne with
    ⟨delta₀, hdelta₀, hdelta₀One, hpower⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro sigma delta band subband scaleData hdelta hdeltaBound
  calc
    pureWZ2CoupledFinalDelta subband ≤
        pureWZ2CoupledFinalDeltaUpperConstant * Real.rpow delta epsilon :=
      scaleData.final_delta_le_source_power
    _ ≤ pureWZ2CoupledFinalDeltaUpperConstant * cap := by
      exact mul_le_mul_of_nonneg_left (hpower delta hdelta hdeltaBound)
        pureWZ2CoupledFinalDeltaUpperConstant_pos.le
    _ ≤ target := by
      have hcapUpper : cap ≤
          target / pureWZ2CoupledFinalDeltaUpperConstant := min_le_left _ _
      rw [le_div_iff₀ pureWZ2CoupledFinalDeltaUpperConstant_pos] at hcapUpper
      simpa [mul_comm] using hcapUpper

/-- After a uniform pre-runtime shrink, the coupled final radius is bounded
by a clean half-exponent source power.  This absorbs the fixed coefficient in
`final_delta_le_source_power` once and for all. -/
theorem exists_sourceDelta_for_coupled_final_power_upper
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sigma delta : ℝ}
        {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
        {subband : PureWZ2MassPopularSubbandData band},
        PureWZ2CoupledScaleData subband →
        0 < delta → delta ≤ delta₀ →
        pureWZ2CoupledFinalDelta subband ≤
          Real.rpow delta (epsilon / 2) := by
  rcases exists_delta_constant_mul_power_le_power
      (ENNReal.ofReal pureWZ2CoupledFinalDeltaUpperConstant)
      ENNReal.ofReal_ne_top (epsilon / 2) epsilon (by linarith) with
    ⟨delta₀, hdelta₀, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro sigma delta band subband scaleData hdelta hdeltaBound
  have hENN : ENNReal.ofReal pureWZ2CoupledFinalDeltaUpperConstant *
        Kakeya.realRpowENN delta epsilon ≤
      Kakeya.realRpowENN delta (epsilon / 2) :=
    habsorb hdelta hdeltaBound
  have hreal : pureWZ2CoupledFinalDeltaUpperConstant *
        Real.rpow delta epsilon ≤ Real.rpow delta (epsilon / 2) := by
    rw [Kakeya.realRpowENN, Kakeya.realRpowENN,
      ← ENNReal.ofReal_mul
        pureWZ2CoupledFinalDeltaUpperConstant_pos.le] at hENN
    exact (ENNReal.ofReal_le_ofReal_iff
      (Real.rpow_nonneg hdelta.le _)).mp hENN
  exact scaleData.final_delta_le_source_power.trans hreal

/-- A clean upper source-power bound on the final radius reverses under a
negative exponent. -/
theorem source_power_negative_le_final_negative
    {sigma epsilon delta loss : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband)
    (hloss : 0 ≤ loss)
    (hfinalUpper : pureWZ2CoupledFinalDelta subband ≤
      Real.rpow delta (epsilon / 2)) :
    Kakeya.realRpowENN delta (-(epsilon / 2 * loss)) ≤
      Kakeya.realRpowENN (pureWZ2CoupledFinalDelta subband) (-loss) := by
  have hsourcePowerPos : 0 < Real.rpow delta (epsilon / 2) :=
    Real.rpow_pos_of_pos band.lemma31.data.cfg.extremal.delta_pos _
  have hpositivePower : 0 <
      Real.rpow (pureWZ2CoupledFinalDelta subband) loss :=
    Real.rpow_pos_of_pos data.final_delta_pos _
  have hpower :
      Real.rpow (pureWZ2CoupledFinalDelta subband) loss ≤
        Real.rpow (Real.rpow delta (epsilon / 2)) loss :=
    Real.rpow_le_rpow data.final_delta_pos.le hfinalUpper hloss
  have hinv :
      (Real.rpow (Real.rpow delta (epsilon / 2)) loss)⁻¹ ≤
        (Real.rpow (pureWZ2CoupledFinalDelta subband) loss)⁻¹ := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le hpositivePower hpower)
  have hleft : Real.rpow delta (-(epsilon / 2 * loss)) =
      (Real.rpow (Real.rpow delta (epsilon / 2)) loss)⁻¹ := by
    calc
      Real.rpow delta (-(epsilon / 2 * loss)) =
          Real.rpow delta ((epsilon / 2) * (-loss)) := by
            congr 1 <;> ring
      _ = Real.rpow (Real.rpow delta (epsilon / 2)) (-loss) :=
        Real.rpow_mul band.lemma31.data.cfg.extremal.delta_pos.le _ _
      _ = (Real.rpow (Real.rpow delta (epsilon / 2)) loss)⁻¹ :=
        Real.rpow_neg hsourcePowerPos.le loss
  have hright : Real.rpow (pureWZ2CoupledFinalDelta subband) (-loss) =
      (Real.rpow (pureWZ2CoupledFinalDelta subband) loss)⁻¹ :=
    Real.rpow_neg data.final_delta_pos.le loss
  have hreal : Real.rpow delta (-(epsilon / 2 * loss)) ≤
      Real.rpow (pureWZ2CoupledFinalDelta subband) (-loss) := by
    rw [hleft, hright]
    exact hinv
  exact ENNReal.ofReal_mono hreal

/-- The coupled final radius also has a source-power lower bound.  The
derivative-band lower slope and the fixed subband length give one quadratic
power of the Lemma-31 radius. -/
theorem source_power_two_le_final_delta
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband) :
    Real.rpow delta (2 * epsilon) / 2500 ≤
      pureWZ2CoupledFinalDelta subband := by
  have hlength : subband.right - subband.left =
      band.lemma31.data.rho.1 / 5000 := by
    rw [subband.length_eq, band.length_eq]
    ring
  have hrhoPos : 0 < band.lemma31.data.rho.1 :=
    band.lemma31.data.cfg.extremal.delta_pos.trans_le
      band.lemma31.data.rho.2.1
  have hbonus : band.lemma31.data.rho.1 ^ 2 / 2500 ≤
      2 * band.slopeScale * (subband.right - subband.left) := by
    rw [hlength]
    nlinarith [mul_le_mul_of_nonneg_right band.slopeScale_lower hrhoPos.le]
  have hsourcePower : Real.rpow delta (2 * epsilon) =
      band.lemma31.data.rho.1 ^ 2 := by
    calc
      Real.rpow delta (2 * epsilon) =
          (Real.rpow delta epsilon) ^ (2 : ℕ) := by
        rw [rpow_nat_pow band.lemma31.data.cfg.extremal.delta_pos]
        congr 1
      _ = band.lemma31.data.rho.1 ^ 2 := by
        rw [band.lemma31.data.rho_eq_power]
  rw [hsourcePower]
  exact hbonus.trans <| by
    unfold pureWZ2CoupledFinalDelta
    exact le_add_of_nonneg_left <|
      mul_nonneg (mul_nonneg (by norm_num) data.lambda_pos.le)
        subband.anisotropic_alignedScale_pos.le

/-- The lower face of one original height cell moves by at most a fixed
fraction of the final radius under the coupled map. -/
theorem lower_cell_image_budget
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband) :
    pureWZ2CoupledFinalScale subband *
          (2 / (subband.right - subband.left)) * delta ≤
      pureWZ2CoupledFinalDelta subband / 128 := by
  have hraw := anisotropicPaperRawScale_le_aligned
    subband.anisotropic_rawScale_pos subband.anisotropic_rawScale_le_half
  have hlength : subband.right - subband.left ≠ 0 :=
    sub_ne_zero.mpr subband.ordered.ne'
  have hfirst : pureWZ2CoupledFinalScale subband *
        (2 / (subband.right - subband.left)) * delta ≤
      pureWZ2CoupledFinalScale subband *
        anisotropicPaperAlignedScale delta subband.left subband.right / 8 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).2
    calc
      pureWZ2CoupledFinalScale subband *
            (2 / (subband.right - subband.left)) * delta * 8 =
        pureWZ2CoupledFinalScale subband *
          anisotropicPaperRawScale delta subband.left subband.right := by
            unfold anisotropicPaperRawScale
            field_simp [hlength]
            ring
      _ ≤ pureWZ2CoupledFinalScale subband *
          anisotropicPaperAlignedScale delta subband.left subband.right :=
        mul_le_mul_of_nonneg_left hraw data.lambda_pos.le
  have hbonusNonnegative : 0 ≤
      2 * band.slopeScale * (subband.right - subband.left) :=
    mul_nonneg (mul_nonneg (by norm_num) band.slopeScale_pos.le)
      (sub_nonneg.mpr subband.ordered.le)
  apply hfirst.trans
  unfold pureWZ2CoupledFinalDelta
  nlinarith [mul_pos data.lambda_pos subband.anisotropic_alignedScale_pos]

/-- The final radius also absorbs the original cubical source scale after
the fixed final similarity. -/
theorem lambda_mul_source_delta_le_final
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband) :
    pureWZ2CoupledFinalScale subband * delta ≤
      pureWZ2CoupledFinalDelta subband := by
  have hsource := subband.delta_le_anisotropic_alignedScale
  have hscaled := mul_le_mul_of_nonneg_left hsource data.lambda_pos.le
  have hbonusNonnegative : 0 ≤
      2 * band.slopeScale * (subband.right - subband.left) :=
    mul_nonneg (mul_nonneg (by norm_num) band.slopeScale_pos.le)
      (sub_nonneg.mpr subband.ordered.le)
  unfold pureWZ2CoupledFinalDelta
  nlinarith [mul_pos data.lambda_pos subband.anisotropic_alignedScale_pos]

/-- Exact points selected in the narrow source box have target height at
most one thirty-second of the final radius. -/
theorem isotropic_exact_height_budget
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband) :
    pureWZ2CoupledFinalScale subband *
          anisotropicPaperAlignedScale delta subband.left subband.right / 2 ≤
      pureWZ2CoupledFinalDelta subband / 32 := by
  have hbonusNonnegative : 0 ≤
      2 * band.slopeScale * (subband.right - subband.left) :=
    mul_nonneg (mul_nonneg (by norm_num) band.slopeScale_pos.le)
      (sub_nonneg.mpr subband.ordered.le)
  unfold pureWZ2CoupledFinalDelta
  nlinarith [mul_pos data.lambda_pos subband.anisotropic_alignedScale_pos]

theorem completed_incidence_budget
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband) :
    2 * pureWZ2CoupledFinalSlopeScale subband *
          (subband.right - subband.left) ^ 2 +
        4 * ((lipschitzExtensionConstant Point3 *
          pureWZ2FinalIsotropicTargetK : NNReal) : ℝ) *
          (pureWZ2CoupledFinalDelta subband * Real.sqrt 3) ≤
      pureWZ2CoupledFinalDelta subband := by
  rw [data.completed_extension_error_eq]
  have hincidenceEq : 2 * pureWZ2CoupledFinalSlopeScale subband *
        (subband.right - subband.left) ^ 2 =
      2 * (((9 : ℝ) / 10 * band.slopeScale) /
        pureWZ2CoupledScaleRequirement) *
        (subband.right - subband.left) ^ 2 := by
    rw [show 2 * pureWZ2CoupledFinalSlopeScale subband *
        (subband.right - subband.left) ^ 2 =
      2 * (pureWZ2CoupledFinalSlopeScale subband *
        (subband.right - subband.left) ^ 2) by ring,
      data.m_mul_length_sq]
    ring
  rw [hincidenceEq]
  have hsqrt : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg 3]
  have herror : pureWZ2CoupledFinalDelta subband * Real.sqrt 3 / 4 ≤
      pureWZ2CoupledFinalDelta subband / 2 := by
    have := mul_le_mul_of_nonneg_left hsqrt data.final_delta_pos.le
    nlinarith
  have hlambda : 15000 ≤ pureWZ2CoupledFinalScale subband := by
    have hcomponent : (15000 : ℝ) ≤ pureWZ2CoupledScaleRequirement := by
      unfold pureWZ2CoupledScaleRequirement
      exact le_max_left _ _
    exact hcomponent.trans data.lambda_requirement
  have hprePos := subband.anisotropic_alignedScale_pos
  have hlengthPos : 0 < subband.right - subband.left :=
    sub_pos.mpr subband.ordered
  have hbonusNonneg : 0 ≤
      2 * band.slopeScale * (subband.right - subband.left) :=
    mul_nonneg (mul_nonneg (by norm_num) band.slopeScale_pos.le)
      (sub_nonneg.mpr subband.ordered.le)
  have hincidence : 2 * (band.slopeScale / pureWZ2CoupledScaleRequirement) *
        (subband.right - subband.left) ^ 2 ≤
      pureWZ2CoupledFinalDelta subband / 2 := by
    unfold pureWZ2CoupledFinalDelta
    have hleftNonnegative : 0 ≤
        band.slopeScale / pureWZ2CoupledScaleRequirement :=
      div_nonneg band.slopeScale_pos.le pureWZ2CoupledScaleRequirement_pos.le
    have hlengthSmall : subband.right - subband.left ≤ 1 := by
      rw [subband.length_eq, band.length_eq]
      linarith [band.lemma31.rho_tiny]
    have hsquareLinear : (subband.right - subband.left) ^ 2 ≤
        subband.right - subband.left := by
      nlinarith [sq_nonneg (subband.right - subband.left)]
    have hcoefficient :
        band.slopeScale / pureWZ2CoupledScaleRequirement ≤
          band.slopeScale / 15000 := by
      exact div_le_div_of_nonneg_left band.slopeScale_pos.le
        (by norm_num) hlambda
    calc
      2 * (band.slopeScale / pureWZ2CoupledScaleRequirement) *
          (subband.right - subband.left) ^ 2 ≤
        2 * (band.slopeScale / 15000) *
          (subband.right - subband.left) ^ 2 := by gcongr
      _ ≤ band.slopeScale * (subband.right - subband.left) := by
        have hscaledSquare :
            2 * (band.slopeScale / 15000) *
                (subband.right - subband.left) ^ 2 ≤
              2 * (band.slopeScale / 15000) *
                (subband.right - subband.left) :=
          mul_le_mul_of_nonneg_left hsquareLinear
            (mul_nonneg (by norm_num)
              (div_nonneg band.slopeScale_pos.le (by norm_num)))
        have hcoefficientSmall : 2 * (band.slopeScale / 15000) ≤
            band.slopeScale := by
          have hslopeNonnegative := band.slopeScale_pos.le
          nlinarith
        exact hscaledSquare.trans <|
          mul_le_mul_of_nonneg_right hcoefficientSmall hlengthPos.le
      _ ≤ pureWZ2CoupledFinalDelta subband / 2 := by
        have hmainNonnegative : 0 ≤ 8 * pureWZ2CoupledFinalScale subband *
            anisotropicPaperAlignedScale delta subband.left subband.right :=
          mul_nonneg (mul_nonneg (by norm_num) data.lambda_pos.le) hprePos.le
        rw [show pureWZ2CoupledFinalDelta subband / 2 =
          8 * pureWZ2CoupledFinalScale subband *
              anisotropicPaperAlignedScale delta subband.left subband.right +
            band.slopeScale * (subband.right - subband.left) by
          unfold pureWZ2CoupledFinalDelta
          ring]
        exact le_add_of_nonneg_left hmainNonnegative
  have hincidenceMargin :
      2 * (((9 : ℝ) / 10 * band.slopeScale) /
          pureWZ2CoupledScaleRequirement) *
          (subband.right - subband.left) ^ 2 ≤
        2 * (band.slopeScale / pureWZ2CoupledScaleRequirement) *
          (subband.right - subband.left) ^ 2 := by
    have hscaleNonnegative : 0 ≤ band.slopeScale := band.slopeScale_pos.le
    have hreqPositive := pureWZ2CoupledScaleRequirement_pos
    gcongr <;> nlinarith
  nlinarith [hincidenceMargin]

theorem completed_projection_budget
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband) :
    pureWZ2CoupledFinalDelta subband * Real.sqrt 3 +
        (Real.sqrt 3 / 4) *
          (4 * ((lipschitzExtensionConstant Point3 *
            pureWZ2FinalIsotropicTargetK : NNReal) : ℝ) *
              (pureWZ2CoupledFinalDelta subband * Real.sqrt 3)) ≤
      2 * pureWZ2CoupledFinalDelta subband := by
  rw [data.completed_extension_error_eq]
  have hsqrtNonneg := Real.sqrt_nonneg 3
  have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsqrt : Real.sqrt 3 ≤ 7 / 4 := by nlinarith
  have hsqrtMul : Real.sqrt 3 * Real.sqrt 3 = 3 := by nlinarith
  calc
    pureWZ2CoupledFinalDelta subband * Real.sqrt 3 +
        Real.sqrt 3 / 4 *
          (pureWZ2CoupledFinalDelta subband * Real.sqrt 3 / 4) =
      pureWZ2CoupledFinalDelta subband * (Real.sqrt 3 + 3 / 16) := by
        calc
          _ = pureWZ2CoupledFinalDelta subband *
              (Real.sqrt 3 + (Real.sqrt 3 * Real.sqrt 3) / 16) := by ring
          _ = _ := by rw [hsqrtMul]
    _ ≤ pureWZ2CoupledFinalDelta subband * (7 / 4 + 3 / 16) := by
      exact mul_le_mul_of_nonneg_left (by linarith) data.final_delta_pos.le
    _ ≤ 2 * pureWZ2CoupledFinalDelta subband := by
      nlinarith [data.final_delta_pos]

theorem completed_ball_budget
    {sigma epsilon delta rho : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband)
    (hrhoLower : pureWZ2CoupledFinalDelta subband ≤ rho)
    (hrhoOne : rho ≤ 1) :
    2 * (Real.sqrt rho +
          2 * (pureWZ2CoupledFinalDelta subband * Real.sqrt 3)) /
        pureWZ2CoupledFinalScale subband ≤ Real.sqrt rho := by
  have hrhoPos : 0 < rho := data.final_delta_pos.trans_le hrhoLower
  have hrhoSqrt : rho ≤ Real.sqrt rho := by
    nlinarith [Real.sq_sqrt hrhoPos.le, Real.sqrt_nonneg rho]
  have hsqrtThree : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg 3]
  have hwitness : pureWZ2CoupledFinalDelta subband * Real.sqrt 3 ≤
      2 * rho := by
    calc
      pureWZ2CoupledFinalDelta subband * Real.sqrt 3 ≤
          rho * Real.sqrt 3 :=
        mul_le_mul_of_nonneg_right hrhoLower (Real.sqrt_nonneg 3)
      _ ≤ rho * 2 := mul_le_mul_of_nonneg_left hsqrtThree hrhoPos.le
      _ = 2 * rho := by ring
  have hradius : Real.sqrt rho +
        2 * (pureWZ2CoupledFinalDelta subband * Real.sqrt 3) ≤
      5 * Real.sqrt rho := by nlinarith
  have hlambdaTen : 10 ≤ pureWZ2CoupledFinalScale subband := by
    have hcomponent : (10 : ℝ) ≤ pureWZ2CoupledScaleRequirement := by
      unfold pureWZ2CoupledScaleRequirement
      exact (by norm_num : (10 : ℝ) ≤ 15000).trans (le_max_left _ _)
    exact hcomponent.trans data.lambda_requirement
  apply (div_le_iff₀ data.lambda_pos).2
  calc
    2 * (Real.sqrt rho +
        2 * (pureWZ2CoupledFinalDelta subband * Real.sqrt 3)) ≤
      2 * (5 * Real.sqrt rho) := by gcongr
    _ = 10 * Real.sqrt rho := by ring
    _ ≤ Real.sqrt rho * pureWZ2CoupledFinalScale subband := by
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_right hlambdaTen (Real.sqrt_nonneg rho)

theorem completed_ad_scale_budget
    {sigma epsilon delta rho frameSlope : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband)
    (hframeClose : |frameSlope -
      band.lemma31.data.globalSlope
        (subband.left + (subband.right - subband.left) / 2)| ≤ 1 / 4)
    (hrhoLower : pureWZ2CoupledFinalDelta subband ≤ rho)
    (normal : Point3) (hnormal : ‖normal‖ = 1) :
    (pureWZ2CoupledFinalScale subband /
        ‖dPhiInvT band.lemma31.data.globalSlope subband.left subband.right
          (pureWZ2CoupledFinalSlopeScale subband)
          (pureWZ2NormalizedFrameCompletedNormal frameSlope normal)‖) * rho ≤
      rho := by
  have hnormLower :=
    dPhiInvT_normalizedFrameCompleted_norm_lower_of_close
      band.lemma31.data.globalSlope subband.ordered data.m_pos hframeClose
        normal hnormal
  have hdenomPos : 0 <
      2 * (pureWZ2CoupledFinalSlopeScale subband *
        (subband.right - subband.left)) :=
    mul_pos (by norm_num) (mul_pos data.m_pos (sub_pos.mpr subband.ordered))
  have hnormPos : 0 <
      ‖dPhiInvT band.lemma31.data.globalSlope subband.left subband.right
        (pureWZ2CoupledFinalSlopeScale subband)
        (pureWZ2NormalizedFrameCompletedNormal frameSlope normal)‖ := by
    exact (one_div_pos.mpr hdenomPos).trans_le hnormLower
  have hlengthOne : subband.right - subband.left ≤ 1 / 5000 := by
    rw [subband.length_eq, band.length_eq]
    have hrhoOne : band.lemma31.data.rho.1 ≤ 1 :=
      band.lemma31.rho_tiny.trans (by norm_num)
    linarith
  have hcoefficient : 2 * pureWZ2CoupledFinalScale subband *
        pureWZ2CoupledFinalSlopeScale subband *
          (subband.right - subband.left) ≤ 1 := by
    rw [show 2 * pureWZ2CoupledFinalScale subband *
        pureWZ2CoupledFinalSlopeScale subband *
          (subband.right - subband.left) =
      2 * (pureWZ2CoupledFinalScale subband *
        pureWZ2CoupledFinalSlopeScale subband) *
          (subband.right - subband.left) by ring, data.lambda_mul_m]
    nlinarith [band.slopeScale_pos, band.slopeScale_le_one]
  have hlambdaNorm : pureWZ2CoupledFinalScale subband ≤
      ‖dPhiInvT band.lemma31.data.globalSlope subband.left subband.right
        (pureWZ2CoupledFinalSlopeScale subband)
        (pureWZ2NormalizedFrameCompletedNormal frameSlope normal)‖ := by
    calc
      pureWZ2CoupledFinalScale subband ≤ 1 /
          (2 * (pureWZ2CoupledFinalSlopeScale subband *
            (subband.right - subband.left))) := by
        rw [le_div_iff₀ hdenomPos]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hcoefficient
      _ ≤ _ := hnormLower
  have hquotient : pureWZ2CoupledFinalScale subband /
      ‖dPhiInvT band.lemma31.data.globalSlope subband.left subband.right
        (pureWZ2CoupledFinalSlopeScale subband)
        (pureWZ2NormalizedFrameCompletedNormal frameSlope normal)‖ ≤ 1 :=
    (div_le_one hnormPos).2 hlambdaNorm
  exact mul_le_of_le_one_left
    (data.final_delta_pos.trans_le hrhoLower).le hquotient

/-- At source scale one, the completed-normal projection dilation is paid by
the additional linear term in the final radius. -/
theorem completed_ad_one_budget
    {sigma epsilon delta frameSlope : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2CoupledScaleData subband)
    (hframeClose : |frameSlope -
      band.lemma31.data.globalSlope
        (subband.left + (subband.right - subband.left) / 2)| ≤ 1 / 4)
    (normal : Point3) (hnormal : ‖normal‖ = 1) :
    pureWZ2CoupledFinalScale subband /
        ‖dPhiInvT band.lemma31.data.globalSlope subband.left subband.right
          (pureWZ2CoupledFinalSlopeScale subband)
          (pureWZ2NormalizedFrameCompletedNormal frameSlope normal)‖ ≤
      pureWZ2CoupledFinalDelta subband := by
  let transported := dPhiInvT band.lemma31.data.globalSlope
    subband.left subband.right (pureWZ2CoupledFinalSlopeScale subband)
      (pureWZ2NormalizedFrameCompletedNormal frameSlope normal)
  have hnormLower :
      1 / (2 * (pureWZ2CoupledFinalSlopeScale subband *
        (subband.right - subband.left))) ≤ ‖transported‖ := by
    simpa only [transported] using
      dPhiInvT_normalizedFrameCompleted_norm_lower_of_close
        band.lemma31.data.globalSlope subband.ordered data.m_pos hframeClose
          normal hnormal
  have hdenomPos : 0 <
      2 * (pureWZ2CoupledFinalSlopeScale subband *
        (subband.right - subband.left)) :=
    mul_pos (by norm_num) <|
      mul_pos data.m_pos (sub_pos.mpr subband.ordered)
  have hnormPos : 0 < ‖transported‖ :=
    (one_div_pos.mpr hdenomPos).trans_le hnormLower
  have hproduct : 1 ≤
      (2 * (pureWZ2CoupledFinalSlopeScale subband *
        (subband.right - subband.left))) * ‖transported‖ := by
    calc
      1 = (2 * (pureWZ2CoupledFinalSlopeScale subband *
          (subband.right - subband.left))) *
            (1 / (2 * (pureWZ2CoupledFinalSlopeScale subband *
              (subband.right - subband.left)))) := by
            rw [one_div]
            exact (mul_inv_cancel₀ hdenomPos.ne').symm
      _ ≤ (2 * (pureWZ2CoupledFinalSlopeScale subband *
          (subband.right - subband.left))) * ‖transported‖ :=
        mul_le_mul_of_nonneg_left hnormLower hdenomPos.le
  have hquotient : pureWZ2CoupledFinalScale subband / ‖transported‖ ≤
      2 * pureWZ2CoupledFinalScale subband *
        pureWZ2CoupledFinalSlopeScale subband *
          (subband.right - subband.left) := by
    rw [div_le_iff₀ hnormPos]
    have hscaled := mul_le_mul_of_nonneg_left hproduct data.lambda_pos.le
    nlinarith
  calc
    pureWZ2CoupledFinalScale subband /
          ‖dPhiInvT band.lemma31.data.globalSlope subband.left subband.right
            (pureWZ2CoupledFinalSlopeScale subband)
            (pureWZ2NormalizedFrameCompletedNormal frameSlope normal)‖ =
        pureWZ2CoupledFinalScale subband / ‖transported‖ := rfl
    _ ≤ 2 * pureWZ2CoupledFinalScale subband *
          pureWZ2CoupledFinalSlopeScale subband *
            (subband.right - subband.left) := hquotient
    _ = 2 * ((9 : ℝ) / 10 * band.slopeScale) *
          (subband.right - subband.left) := by
      rw [show 2 * pureWZ2CoupledFinalScale subband *
          pureWZ2CoupledFinalSlopeScale subband *
            (subband.right - subband.left) =
        2 * (pureWZ2CoupledFinalScale subband *
          pureWZ2CoupledFinalSlopeScale subband) *
            (subband.right - subband.left) by ring, data.lambda_mul_m]
    _ ≤ 2 * band.slopeScale *
          (subband.right - subband.left) := by
      have hslope := band.slopeScale_pos.le
      have hlength := (sub_pos.mpr subband.ordered).le
      gcongr <;> nlinarith
    _ ≤ pureWZ2CoupledFinalDelta subband := by
      unfold pureWZ2CoupledFinalDelta
      exact le_add_of_nonneg_left <|
        mul_nonneg (mul_nonneg (by norm_num) data.lambda_pos.le)
          subband.anisotropic_alignedScale_pos.le

end PureWZ2CoupledScaleData

/-- The canonical coupled scale satisfies every defining budget. -/
theorem exists_pureWZ2CoupledScaleData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    Nonempty (PureWZ2CoupledScaleData subband) := by
  let rho := band.lemma31.data.rho.1
  let preDelta := anisotropicPaperAlignedScale delta subband.left subband.right
  let lambda := pureWZ2CoupledFinalScale subband
  let m := pureWZ2CoupledFinalSlopeScale subband
  have hrhoPos : 0 < rho :=
    band.lemma31.data.cfg.extremal.delta_pos.trans_le band.lemma31.data.rho.2.1
  have hrhoOne : rho ≤ 1 := band.lemma31.rho_tiny.trans (by norm_num)
  have hlengthPos : 0 < subband.right - subband.left :=
    sub_pos.mpr subband.ordered
  have hlength : subband.right - subband.left = rho / 5000 := by
    dsimp only [rho]
    rw [subband.length_eq, band.length_eq]
    ring
  have hprePos : 0 < preDelta := by
    exact subband.anisotropic_alignedScale_pos
  have hpreUpper : preDelta < 160000 * delta / rho := by
    exact subband.anisotropic_alignedScale_upper
  have hrequirementPos : 0 < pureWZ2CoupledScaleRequirement :=
    pureWZ2CoupledScaleRequirement_pos
  have hconflictPos : 0 < pureWZ2CoupledConflictConstant := by
    unfold pureWZ2CoupledConflictConstant
    norm_num
  have hscaledRho : pureWZ2CoupledConflictConstant *
      pureWZ2CoupledScaleRequirement * rho ≤ 1 := by
    have h := (le_div_iff₀ (mul_pos hconflictPos hrequirementPos)).mp
      band.lemma31.rho_coupled_tiny
    simpa only [rho, mul_assoc, mul_left_comm, mul_comm] using h
  have hrhoThree : rho ^ 3 ≤ 1 := by
    simpa using pow_le_pow_left₀ hrhoPos.le hrhoOne 3
  have hscaledRhoFour : pureWZ2CoupledConflictConstant *
      pureWZ2CoupledScaleRequirement * rho ^ 4 ≤ 1 := by
    calc
      pureWZ2CoupledConflictConstant * pureWZ2CoupledScaleRequirement *
          rho ^ 4 =
        (pureWZ2CoupledConflictConstant * pureWZ2CoupledScaleRequirement *
          rho) * rho ^ 3 := by ring
      _ ≤ 1 * 1 := mul_le_mul hscaledRho hrhoThree
        (pow_nonneg hrhoPos.le 3) (by norm_num)
      _ = 1 := by norm_num
  have hscaledDelta : pureWZ2CoupledConflictConstant *
      pureWZ2CoupledScaleRequirement * delta ≤ rho ^ 4 := by
    calc
      pureWZ2CoupledConflictConstant * pureWZ2CoupledScaleRequirement * delta ≤
          pureWZ2CoupledConflictConstant * pureWZ2CoupledScaleRequirement *
            rho ^ 8 := by
              exact mul_le_mul_of_nonneg_left band.lemma31.delta_le_rho_eight
                (mul_nonneg hconflictPos.le hrequirementPos.le)
      _ = (pureWZ2CoupledConflictConstant *
          pureWZ2CoupledScaleRequirement * rho ^ 4) * rho ^ 4 := by ring
      _ ≤ 1 * rho ^ 4 := mul_le_mul_of_nonneg_right hscaledRhoFour
        (pow_nonneg hrhoPos.le 4)
      _ = rho ^ 4 := by ring
  have hnumerator : pureWZ2CoupledScaleRequirement * (60000 * preDelta) ≤
      ((9 : ℝ) / 10 * band.slopeScale) *
        (subband.right - subband.left) ^ 2 := by
    calc
      pureWZ2CoupledScaleRequirement * (60000 * preDelta) ≤
          pureWZ2CoupledScaleRequirement *
            (60000 * (160000 * delta / rho)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hpreUpper.le (by norm_num))
                hrequirementPos.le
      _ = (pureWZ2CoupledConflictConstant *
            pureWZ2CoupledScaleRequirement * delta) /
              (50000000 * rho) := by
            unfold pureWZ2CoupledConflictConstant
            ring
      _ ≤ rho ^ 4 / (50000000 * rho) := by
            exact div_le_div_of_nonneg_right hscaledDelta (by positivity)
      _ = (1 / 2 : ℝ) * rho * (rho / 5000) ^ 2 := by
            field_simp [hrhoPos.ne']
            ring
      _ ≤ ((9 : ℝ) / 10 * band.slopeScale) *
          (subband.right - subband.left) ^ 2 := by
            rw [hlength]
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            nlinarith [band.slopeScale_lower, band.slopeScale_pos]
  have hlambdaPreDelta : lambda * preDelta ≤ 1 / 1000 := by
    calc
      lambda * preDelta ≤
          pureWZ2CoupledScaleRequirement * (160000 * delta / rho) := by
        dsimp only [lambda]
        exact mul_le_mul_of_nonneg_left hpreUpper.le hrequirementPos.le
      _ ≤ pureWZ2CoupledScaleRequirement * (160000 * rho) := by
        have hdeltaRho : delta / rho ≤ rho := by
          rw [div_le_iff₀ hrhoPos]
          simpa [pow_two] using band.lemma31.delta_le_rho_sq
        have hscaled : 160000 * (delta / rho) ≤ 160000 * rho :=
          mul_le_mul_of_nonneg_left hdeltaRho (by norm_num)
        exact mul_le_mul_of_nonneg_left (by simpa [mul_div_assoc] using hscaled)
          hrequirementPos.le
      _ ≤ 1 / 1000 := by
        unfold pureWZ2CoupledConflictConstant at hscaledRho
        nlinarith
  have hlambdaRequirement : pureWZ2CoupledScaleRequirement ≤ lambda := by
    exact le_rfl
  have hlambdaPos : 0 < lambda :=
    hrequirementPos.trans_le hlambdaRequirement
  have hlambdaOne : 1 ≤ lambda :=
    have hrequirement : 1 ≤ pureWZ2CoupledScaleRequirement := by
      unfold pureWZ2CoupledScaleRequirement
      exact (by norm_num : (1 : ℝ) ≤ 15000).trans (le_max_left _ _)
    hrequirement.trans hlambdaRequirement
  have hmPos : 0 < m := by
    dsimp only [m, pureWZ2CoupledFinalSlopeScale]
    exact pureWZ2CoupledAnisotropicSlopeScale_pos band hlambdaPos
  have hmBand : m ≤ band.slopeScale := by
    dsimp only [m, pureWZ2CoupledFinalSlopeScale]
    exact pureWZ2CoupledAnisotropicSlopeScale_le band hlambdaOne
  have hconflict : anisotropicPaperConflictWidth preDelta subband.left
      subband.right m ≤ 1 := by
    unfold anisotropicPaperConflictWidth
    have hdenominator : 0 < m * (subband.right - subband.left) ^ 2 :=
      mul_pos hmPos (sq_pos_of_pos hlengthPos)
    rw [div_le_one hdenominator]
    dsimp only [m, pureWZ2CoupledFinalSlopeScale,
      pureWZ2CoupledAnisotropicSlopeScale, lambda,
      pureWZ2CoupledFinalScale]
    rw [show ((9 : ℝ) / 10 * band.slopeScale) /
          pureWZ2CoupledScaleRequirement *
          (subband.right - subband.left) ^ 2 =
        (((9 : ℝ) / 10 * band.slopeScale) *
          (subband.right - subband.left) ^ 2) /
          pureWZ2CoupledScaleRequirement by ring]
    apply (le_div_iff₀ hrequirementPos).2
    calc
      100 * (600 * preDelta) * pureWZ2CoupledScaleRequirement =
          pureWZ2CoupledScaleRequirement * (60000 * preDelta) := by ring
      _ ≤ ((9 : ℝ) / 10 * band.slopeScale) *
          (subband.right - subband.left) ^ 2 := hnumerator
  have hfinalPos : 0 < pureWZ2CoupledFinalDelta subband := by
    unfold pureWZ2CoupledFinalDelta
    exact add_pos_of_pos_of_nonneg
      (mul_pos (mul_pos (by norm_num) hlambdaPos) hprePos)
      (mul_nonneg (mul_nonneg (by norm_num) band.slopeScale_pos.le)
        hlengthPos.le)
  have hfinalUpper : pureWZ2CoupledFinalDelta subband ≤ 1 / 24 := by
    have hfirst : 16 * lambda * preDelta ≤ 16 / 1000 := by
      nlinarith [hlambdaPreDelta]
    have hsecond :
        2 * band.slopeScale * (subband.right - subband.left) ≤
          2 / 5000 := by
      calc
        _ ≤ 2 * 1 * (subband.right - subband.left) := by
          gcongr
          exact band.slopeScale_le_one
        _ ≤ 2 * 1 * (1 / 5000 : ℝ) := by
          gcongr
          rw [hlength]
          exact div_le_div_of_nonneg_right hrhoOne (by norm_num)
        _ = 2 / 5000 := by norm_num
    unfold pureWZ2CoupledFinalDelta
    exact (add_le_add hfirst hsecond).trans (by norm_num)
  exact ⟨{
    lambda_pos := hlambdaPos
    lambda_requirement := hlambdaRequirement
    m_pos := hmPos
    m_le_band := hmBand
    conflict_width_le_one := hconflict
    final_delta_pos := hfinalPos
    final_delta_le_twenty_four := hfinalUpper
  }⟩

end Kakeya.Assouad

end
