import MyLeanRepo.Kakeya.Assouad.PureWZ2.CenteredStrictFiberPreparation
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound

/-!
# Quantitative centered strict-fiber bounds

The centered literal affine rescaling has Jacobian
`10⁻⁶ rho⁻²`.  Comparing the source and target tube volumes gives a
scale-independent lower bound for the transferred pointwise density.

The inherited body Convex-Wolff constant times one target tube volume has the
corresponding explicit upper bound.  These are the two quantitative inputs
for the Bernoulli thinning parameters.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Elementary upper bound for the common volume of radius-`scale` unit
tubes. -/
theorem pure_wz2_deltaTubeVolume_upper_twelve
    {scale : ℝ}
    (hscale : 0 < scale)
    (hscaleOne : scale ≤ 1) :
    Kakeya.deltaTubeVolume scale ≤
      (12 : ENNReal) * Kakeya.realRpowENN scale 2 := by
  calc
    Kakeya.deltaTubeVolume scale ≤
        ENNReal.ofReal
          ((1 + 2 * scale) * (2 * scale) * (2 * scale)) :=
      canonical_volume_upper_tight hscale hscaleOne
    _ ≤ ENNReal.ofReal (12 * scale ^ 2) := by
      apply ENNReal.ofReal_mono
      nlinarith
    _ = (12 : ENNReal) *
        Kakeya.realRpowENN scale 2 := by
      rw [show (12 : ENNReal) = ENNReal.ofReal (12 : ℝ) by
        norm_num]
      rw [Kakeya.realRpowENN,
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      exact congrArg (fun value : ℝ => 12 * value)
        (Real.rpow_two scale).symm

private theorem centered_jacobian_source_volume_lower
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (densityConstant : ENNReal) :
    ENNReal.ofReal (1 / 1000000 : ℝ) *
          densityConstant *
          Kakeya.realRpowENN (delta / rho) 2 ≤
      pureWZ2CenteredJacobian rho *
          densityConstant *
          Kakeya.deltaTubeVolume delta := by
  have hsourceVolume :
      Kakeya.realRpowENN delta 2 ≤
        Kakeya.deltaTubeVolume delta := by
    simpa [Kakeya.realRpowENN, Real.rpow_two] using
      canonical_volume_lower hdelta
  have hjacobian :
      pureWZ2CenteredJacobian rho =
        ENNReal.ofReal (1 / 1000000 : ℝ) *
          Kakeya.realRpowENN rho (-2) := by
    rw [pureWZ2CenteredJacobian, Kakeya.realRpowENN]
    have hrhoInvNonneg :
        0 ≤ Real.rpow rho (-2) :=
      Real.rpow_nonneg hrho.le _
    rw [← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    have hrpowNeg :
        Real.rpow rho (-2) = (1 / rho) ^ 2 := by
      calc
        Real.rpow rho (-2) =
            (Real.rpow rho 2)⁻¹ :=
          Real.rpow_neg hrho.le (2 : ℝ)
        _ = (rho ^ 2)⁻¹ :=
          congrArg Inv.inv (Real.rpow_two rho)
        _ = (1 / rho) ^ 2 := by
          field_simp [hrho.ne']
    rw [hrpowNeg]
    norm_num
  have hscaleIdentity :
      Kakeya.realRpowENN (delta / rho) 2 =
        Kakeya.realRpowENN rho (-2) *
          Kakeya.realRpowENN delta 2 := by
    simp only [Kakeya.realRpowENN]
    have hrhoPowNonneg :
        0 ≤ Real.rpow rho (-2) :=
      Real.rpow_nonneg hrho.le _
    rw [← ENNReal.ofReal_mul hrhoPowNonneg]
    congr 1
    have hdeltaTwo :
        Real.rpow delta 2 = delta ^ 2 :=
      Real.rpow_two delta
    have hrhoTwo :
        Real.rpow rho 2 = rho ^ 2 :=
      Real.rpow_two rho
    have hquotientTwo :
        Real.rpow (delta / rho) 2 =
          (delta / rho) ^ 2 :=
      Real.rpow_two (delta / rho)
    have hrhoNegTwo :
        Real.rpow rho (-2) = (rho ^ 2)⁻¹ := by
      calc
        Real.rpow rho (-2) =
            (Real.rpow rho 2)⁻¹ :=
          Real.rpow_neg hrho.le (2 : ℝ)
        _ = (rho ^ 2)⁻¹ :=
          congrArg Inv.inv hrhoTwo
    rw [hquotientTwo, hdeltaTwo, hrhoNegTwo]
    field_simp [hrho.ne']
  rw [hjacobian, hscaleIdentity]
  calc
    ENNReal.ofReal (1 / 1000000 : ℝ) *
          densityConstant *
          (Kakeya.realRpowENN rho (-2) *
            Kakeya.realRpowENN delta 2) =
        (ENNReal.ofReal (1 / 1000000 : ℝ) *
          Kakeya.realRpowENN rho (-2)) *
          densityConstant *
          Kakeya.realRpowENN delta 2 := by ring
    _ ≤
        (ENNReal.ofReal (1 / 1000000 : ℝ) *
          Kakeya.realRpowENN rho (-2)) *
          densityConstant *
          Kakeya.deltaTubeVolume delta := by
      gcongr

/-- The exact centered pointwise density is bounded below by
`(12 * 10^6)⁻¹` times the source pointwise density. -/
theorem pure_wz2_centeredDensityConstant_lower
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (htargetOne : delta / rho ≤ 1)
    (densityConstant : ENNReal) :
    ENNReal.ofReal (1 / 12000000 : ℝ) *
          densityConstant ≤
      pureWZ2CenteredDensityConstant
        delta rho densityConstant := by
  let targetScale := delta / rho
  have htarget : 0 < targetScale := div_pos hdelta hrho
  have htargetVolumeZero :
      Kakeya.deltaTubeVolume targetScale ≠ 0 :=
    (tube_volume_scaling.2.1 targetScale
      htarget htargetOne).1.ne'
  have htargetVolumeTop :
      Kakeya.deltaTubeVolume targetScale ≠ ⊤ :=
    (tube_volume_scaling.2.1 targetScale
      htarget htargetOne).2
  have htargetUpper :=
    pure_wz2_deltaTubeVolume_upper_twelve
      htarget htargetOne
  have hmul :
    (ENNReal.ofReal (1 / 12000000 : ℝ) *
        densityConstant) *
        Kakeya.deltaTubeVolume targetScale ≤
      pureWZ2CenteredJacobian rho *
        densityConstant *
        Kakeya.deltaTubeVolume delta := by
    calc
      (ENNReal.ofReal (1 / 12000000 : ℝ) *
          densityConstant) *
          Kakeya.deltaTubeVolume targetScale ≤
        (ENNReal.ofReal (1 / 12000000 : ℝ) *
          densityConstant) *
          ((12 : ENNReal) *
            Kakeya.realRpowENN targetScale 2) := by
        gcongr
    _ =
      ENNReal.ofReal (1 / 1000000 : ℝ) *
        densityConstant *
        Kakeya.realRpowENN targetScale 2 := by
      rw [show
        ENNReal.ofReal (1 / 12000000 : ℝ) *
              densityConstant *
              ((12 : ENNReal) *
                Kakeya.realRpowENN targetScale 2) =
            (ENNReal.ofReal (1 / 12000000 : ℝ) *
              (12 : ENNReal)) *
              densityConstant *
              Kakeya.realRpowENN targetScale 2 by
                ring,
        show
        ENNReal.ofReal (1 / 12000000 : ℝ) *
            (12 : ENNReal) =
          ENNReal.ofReal (1 / 1000000 : ℝ) by
        rw [show (12 : ENNReal) = ENNReal.ofReal (12 : ℝ) by
          norm_num]
        rw [← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        norm_num]
    _ ≤
      pureWZ2CenteredJacobian rho *
        densityConstant *
        Kakeya.deltaTubeVolume delta :=
      centered_jacobian_source_volume_lower
        hdelta hrho densityConstant
  have hscaled :=
    mul_le_mul_right' hmul
      (Kakeya.deltaTubeVolume targetScale)⁻¹
  rw [show
    (ENNReal.ofReal (1 / 12000000 : ℝ) *
        densityConstant) *
          Kakeya.deltaTubeVolume targetScale *
          (Kakeya.deltaTubeVolume targetScale)⁻¹ =
      ENNReal.ofReal (1 / 12000000 : ℝ) *
        densityConstant by
      rw [mul_assoc,
        ENNReal.mul_inv_cancel
          htargetVolumeZero htargetVolumeTop,
        mul_one]] at hscaled
  simpa [pureWZ2CenteredDensityConstant, targetScale,
    mul_assoc] using hscaled

/-- The exact centered density constant is positive. -/
theorem pure_wz2_centeredDensityConstant_pos
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (htargetOne : delta / rho ≤ 1)
    (densityConstant : ENNReal)
    (hdensity : 0 < densityConstant) :
    0 <
      pureWZ2CenteredDensityConstant
        delta rho densityConstant := by
  have hlower :=
    pure_wz2_centeredDensityConstant_lower
      hdelta hrho htargetOne densityConstant
  have hpositive :
      0 <
        ENNReal.ofReal (1 / 12000000 : ℝ) *
          densityConstant :=
    ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
      hdensity.ne'
  exact hpositive.trans_le hlower

/-- The inherited centered body-CWA constant times one target tube volume
has an explicit monomial upper bound. -/
theorem pure_wz2_centeredCWA_volume_upper
    {delta rho inputEta pruneEta : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (htargetOne : delta / rho ≤ 1) :
    ((Kakeya.realRpowENN delta pruneEta)⁻¹ *
        ((4000000 : ENNReal) *
          Kakeya.realRpowENN delta (-inputEta))) *
        Kakeya.deltaTubeVolume (delta / rho) ≤
      (48000000 : ENNReal) *
        Kakeya.realRpowENN delta
          (-(inputEta + pruneEta)) *
        Kakeya.realRpowENN (delta / rho) 2 := by
  have htarget : 0 < delta / rho := div_pos hdelta hrho
  have hvolume :=
    pure_wz2_deltaTubeVolume_upper_twelve
      htarget htargetOne
  have hinverse :
      (Kakeya.realRpowENN delta pruneEta)⁻¹ =
        Kakeya.realRpowENN delta (-pruneEta) := by
    simp only [Kakeya.realRpowENN]
    have hpowPositive :
        0 < Real.rpow delta pruneEta :=
      Real.rpow_pos_of_pos hdelta pruneEta
    calc
      (ENNReal.ofReal
        (Real.rpow delta pruneEta))⁻¹ =
          ENNReal.ofReal
            ((Real.rpow delta pruneEta)⁻¹) :=
        (ENNReal.ofReal_inv_of_pos hpowPositive).symm
      _ =
          ENNReal.ofReal
            (Real.rpow delta (-pruneEta)) := by
        exact congrArg ENNReal.ofReal
          (Real.rpow_neg hdelta.le pruneEta).symm
  have hproduct :
      Kakeya.realRpowENN delta (-pruneEta) *
          Kakeya.realRpowENN delta (-inputEta) =
        Kakeya.realRpowENN delta
          (-(inputEta + pruneEta)) := by
    simp only [Kakeya.realRpowENN]
    have hnonneg :
        0 ≤ Real.rpow delta (-pruneEta) :=
      Real.rpow_nonneg hdelta.le _
    rw [← ENNReal.ofReal_mul hnonneg]
    congr 1
    calc
      Real.rpow delta (-pruneEta) *
          Real.rpow delta (-inputEta) =
        Real.rpow delta ((-pruneEta) + (-inputEta)) :=
          (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta (-(inputEta + pruneEta)) := by
        congr 1
        ring
  rw [hinverse]
  calc
    (Kakeya.realRpowENN delta (-pruneEta) *
        ((4000000 : ENNReal) *
          Kakeya.realRpowENN delta (-inputEta))) *
        Kakeya.deltaTubeVolume (delta / rho) ≤
      (Kakeya.realRpowENN delta (-pruneEta) *
        ((4000000 : ENNReal) *
          Kakeya.realRpowENN delta (-inputEta))) *
        ((12 : ENNReal) *
          Kakeya.realRpowENN (delta / rho) 2) := by
      gcongr
    _ =
      (48000000 : ENNReal) *
        (Kakeya.realRpowENN delta (-pruneEta) *
          Kakeya.realRpowENN delta (-inputEta)) *
        Kakeya.realRpowENN (delta / rho) 2 := by
      ring
    _ =
      (48000000 : ENNReal) *
        Kakeya.realRpowENN delta
          (-(inputEta + pruneEta)) *
        Kakeya.realRpowENN (delta / rho) 2 := by
      rw [hproduct]

/-- The centered selected-family CWA constant is positive and finite. -/
theorem pure_wz2_centeredCWA_constant_pos_finite
    {delta inputEta pruneEta : ℝ}
    (hdelta : 0 < delta) :
    let C :=
      (Kakeya.realRpowENN delta pruneEta)⁻¹ *
        ((4000000 : ENNReal) *
          Kakeya.realRpowENN delta (-inputEta))
    0 < C ∧ C ≠ ⊤ := by
  let prunePower := Kakeya.realRpowENN delta pruneEta
  let inputPower := Kakeya.realRpowENN delta (-inputEta)
  have hpruneZero : prunePower ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hdelta pruneEta)).ne'
  have hpruneTop : prunePower ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hinputZero : inputPower ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hdelta (-inputEta))).ne'
  have hinputTop : inputPower ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  constructor
  · exact ENNReal.mul_pos
      (ENNReal.inv_ne_zero.mpr hpruneTop)
      (mul_ne_zero (by norm_num) hinputZero)
  · exact ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr hpruneZero)
      (ENNReal.mul_ne_top (by norm_num) hinputTop)

end Kakeya.Assouad

end
