import MyLeanRepo.Kakeya.Assouad.Subunit.AsymptoticHelper

/-!
# Asymptotic helpers for the pure WZ2 Node 1 assembly

These lemmas package the repeated small-scale and cross-scale power
comparisons.  They contain no tube-family assumptions.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Powers are antitone in the exponent on `(0, 1]`. -/
theorem pure_wz2_rpowENN_antitone
    {delta first second : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hexponent : first ≤ second) :
    Kakeya.realRpowENN delta second ≤
      Kakeya.realRpowENN delta first := by
  apply ENNReal.ofReal_mono
  exact
    Real.rpow_le_rpow_of_exponent_ge
      hdelta hdeltaOne hexponent

/-- Inverse of an ENNReal-encoded positive real power. -/
theorem pure_wz2_realRpowENN_inv
    {delta exponent : ℝ}
    (hdelta : 0 < delta) :
    (Kakeya.realRpowENN delta exponent)⁻¹ =
      Kakeya.realRpowENN delta (-exponent) := by
  simp only [Kakeya.realRpowENN]
  have hpower : 0 < Real.rpow delta exponent :=
    Real.rpow_pos_of_pos hdelta exponent
  calc
    (ENNReal.ofReal (Real.rpow delta exponent))⁻¹ =
        ENNReal.ofReal
          ((Real.rpow delta exponent)⁻¹) :=
      (ENNReal.ofReal_inv_of_pos hpower).symm
    _ = ENNReal.ofReal
        (Real.rpow delta (-exponent)) := by
      congr 1
      exact (Real.rpow_neg hdelta.le exponent).symm

/-- A target scale bounded by `delta^s` inherits every nonnegative power
bound. -/
theorem pure_wz2_target_power_upper
    {delta target s exponent : ℝ}
    (hdelta : 0 < delta)
    (htargetNonnegative : 0 ≤ target)
    (htarget : target ≤ Real.rpow delta s)
    (hexponent : 0 ≤ exponent) :
    Kakeya.realRpowENN target exponent ≤
      Kakeya.realRpowENN delta (s * exponent) := by
  apply ENNReal.ofReal_mono
  calc
    Real.rpow target exponent ≤
        Real.rpow (Real.rpow delta s) exponent :=
      Real.rpow_le_rpow htargetNonnegative htarget hexponent
    _ = Real.rpow delta (s * exponent) :=
      (Real.rpow_mul hdelta.le s exponent).symm

/-- If `delta ≤ target`, negative target powers are bounded above by the
corresponding negative source power. -/
theorem pure_wz2_target_negative_power_upper
    {delta target exponent : ℝ}
    (hdelta : 0 < delta)
    (hdeltaTarget : delta ≤ target)
    (hexponent : 0 ≤ exponent) :
    Kakeya.realRpowENN target (-exponent) ≤
      Kakeya.realRpowENN delta (-exponent) := by
  apply ENNReal.ofReal_mono
  exact
    Real.rpow_le_rpow_of_nonpos
      hdelta hdeltaTarget (by linarith)

/-- If `target ≤ delta^s`, negative target powers dominate the corresponding
source monomial. -/
theorem pure_wz2_target_negative_power_lower
    {delta target s exponent : ℝ}
    (hdelta : 0 < delta)
    (htarget : 0 < target)
    (htargetUpper : target ≤ Real.rpow delta s)
    (hexponent : 0 ≤ exponent) :
    Kakeya.realRpowENN delta (-(s * exponent)) ≤
      Kakeya.realRpowENN target (-exponent) := by
  apply ENNReal.ofReal_mono
  have hpositive : 0 < Real.rpow delta s :=
    Real.rpow_pos_of_pos hdelta s
  have hmain :
      Real.rpow (Real.rpow delta s) (-exponent) ≤
        Real.rpow target (-exponent) :=
    Real.rpow_le_rpow_of_nonpos
      htarget htargetUpper (by linarith)
  have hidentity :
      Real.rpow (Real.rpow delta s) (-exponent) =
        Real.rpow delta (-(s * exponent)) := by
    calc
      Real.rpow (Real.rpow delta s) (-exponent) =
          Real.rpow delta (s * (-exponent)) :=
        (Real.rpow_mul hdelta.le s (-exponent)).symm
      _ = Real.rpow delta (-(s * exponent)) := by
        congr 1
        ring
  rw [hidentity] at hmain
  exact hmain

/-- Any positive target threshold is eventually larger than `delta^s`. -/
theorem pure_wz2_exists_delta₀_rpow_le
    {threshold s : ℝ}
    (hthreshold : 0 < threshold)
    (hs : 0 < s) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        Real.rpow delta s ≤ threshold := by
  rcases
      Subunit.exists_delta₀_mul_pow_le_one
        threshold⁻¹ (inv_pos.mpr hthreshold) s hs with
    ⟨delta₀, hdelta₀, hdelta₀One, hbound⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaBound
  have hmain := hbound delta hdelta hdeltaBound
  have hscaled :
      threshold *
          (threshold⁻¹ * Real.rpow delta s) ≤
        threshold * 1 :=
    mul_le_mul_of_nonneg_left hmain hthreshold.le
  have hcancel : threshold * threshold⁻¹ = 1 :=
    mul_inv_cancel₀ hthreshold.ne'
  calc
    Real.rpow delta s =
        threshold *
          (threshold⁻¹ * Real.rpow delta s) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ threshold * 1 := hscaled
    _ = threshold := mul_one _

/-- A fixed positive real constant is absorbed by any positive power of a
sufficiently small scale. -/
theorem pure_wz2_exists_delta₀_constant_rpow_le_one
    {constant gap : ℝ}
    (hconstant : 0 < constant)
    (hgap : 0 < gap) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ENNReal.ofReal constant *
            Kakeya.realRpowENN delta gap ≤
          1 := by
  rcases
      Subunit.exists_delta₀_mul_pow_le_one
        constant hconstant gap hgap with
    ⟨delta₀, hdelta₀, hdelta₀One, hbound⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaBound
  have hmain := hbound delta hdelta hdeltaBound
  rw [Kakeya.realRpowENN,
    ← ENNReal.ofReal_mul hconstant.le]
  simpa using ENNReal.ofReal_mono hmain

/-- Convert a small real-power inequality into the density-pruning
inequality used by the indexed source refinement. -/
theorem pure_wz2_pruning_power_bound
    {delta inputEta pruneEta : ℝ}
    (hdelta : 0 < delta)
    (hreal :
      2 * Real.rpow delta (pruneEta - inputEta) ≤ 1) :
    Kakeya.realRpowENN delta pruneEta ≤
      (1 / 2 : ENNReal) *
        Kakeya.realRpowENN delta inputEta := by
  have hpow :
      (2 : ENNReal) *
          Kakeya.realRpowENN delta
            (pruneEta - inputEta) ≤
        1 := by
    rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by
      norm_num, Kakeya.realRpowENN,
      ← ENNReal.ofReal_mul (by norm_num)]
    simpa using ENNReal.ofReal_mono hreal
  have hsplit :
      Kakeya.realRpowENN delta
          (pruneEta - inputEta) *
        Kakeya.realRpowENN delta inputEta =
      Kakeya.realRpowENN delta pruneEta := by
    calc
      Kakeya.realRpowENN delta
            (pruneEta - inputEta) *
          Kakeya.realRpowENN delta inputEta =
        Kakeya.realRpowENN delta
          ((pruneEta - inputEta) + inputEta) :=
            Subunit.realRpowENN_mul hdelta
      _ = Kakeya.realRpowENN delta pruneEta := by
        congr 1
        ring
  have hdouble :
      (2 : ENNReal) *
          Kakeya.realRpowENN delta pruneEta ≤
        Kakeya.realRpowENN delta inputEta := by
    rw [← hsplit]
    calc
      (2 : ENNReal) *
          (Kakeya.realRpowENN delta
            (pruneEta - inputEta) *
            Kakeya.realRpowENN delta inputEta) =
        ((2 : ENNReal) *
          Kakeya.realRpowENN delta
            (pruneEta - inputEta)) *
          Kakeya.realRpowENN delta inputEta := by ring
      _ ≤ 1 * Kakeya.realRpowENN delta inputEta := by
        gcongr
      _ = Kakeya.realRpowENN delta inputEta := one_mul _
  have hscaled :=
    mul_le_mul_left' hdouble (1 / 2 : ENNReal)
  have hhalfTwo :
      (1 / 2 : ENNReal) * 2 = 1 := by
    rw [show (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ by
      norm_num]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  calc
    Kakeya.realRpowENN delta pruneEta =
        (1 / 2 : ENNReal) *
          (2 * Kakeya.realRpowENN delta pruneEta) := by
      rw [← mul_assoc, hhalfTwo, one_mul]
    _ ≤ (1 / 2 : ENNReal) *
        Kakeya.realRpowENN delta inputEta := hscaled

/-- Absorb a fixed reciprocal constant between two source powers. -/
theorem pure_wz2_density_power_from_absorption
    {delta sourceEta targetEta constant : ℝ}
    (hdelta : 0 < delta)
    (hconstant : 0 < constant)
    (habsorb :
      ENNReal.ofReal constant *
          Kakeya.realRpowENN delta
            (sourceEta - targetEta) ≤
        1) :
    Kakeya.realRpowENN delta sourceEta ≤
      ENNReal.ofReal constant⁻¹ *
        Kakeya.realRpowENN delta targetEta := by
  have hconstantENNPositive :
      ENNReal.ofReal constant ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hconstant).ne'
  have hconstantENNTop :
      ENNReal.ofReal constant ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hsplit :
      Kakeya.realRpowENN delta sourceEta =
        Kakeya.realRpowENN delta
            (sourceEta - targetEta) *
          Kakeya.realRpowENN delta targetEta := by
    rw [Subunit.realRpowENN_mul hdelta]
    congr 1
    ring
  have hinverse :
      (ENNReal.ofReal constant)⁻¹ =
        ENNReal.ofReal constant⁻¹ :=
    (ENNReal.ofReal_inv_of_pos hconstant).symm
  rw [hsplit, ← hinverse]
  have hscaled :=
    mul_le_mul_left'
      habsorb (ENNReal.ofReal constant)⁻¹
  rw [show
    (ENNReal.ofReal constant)⁻¹ *
        (ENNReal.ofReal constant *
          Kakeya.realRpowENN delta
            (sourceEta - targetEta)) =
      Kakeya.realRpowENN delta
        (sourceEta - targetEta) by
      rw [← mul_assoc,
        ENNReal.inv_mul_cancel
          hconstantENNPositive hconstantENNTop,
        one_mul]] at hscaled
  simpa [mul_assoc] using
    mul_le_mul_right' hscaled
      (Kakeya.realRpowENN delta targetEta)

/-- Absorb a fixed constant directly at a target scale satisfying
`target ≤ delta^s`. -/
theorem pure_wz2_target_negative_power_absorption
    {delta target s smaller larger constant : ℝ}
    (hdelta : 0 < delta)
    (htarget : 0 < target)
    (htargetUpper : target ≤ Real.rpow delta s)
    (hs : 0 ≤ s)
    (hgap : 0 ≤ larger - smaller)
    (habsorb :
      ENNReal.ofReal constant *
          Kakeya.realRpowENN delta
            (s * (larger - smaller)) ≤
        1) :
    ENNReal.ofReal constant *
        Kakeya.realRpowENN target (-smaller) ≤
      Kakeya.realRpowENN target (-larger) := by
  have htargetGap :
      Kakeya.realRpowENN target (larger - smaller) ≤
        Kakeya.realRpowENN delta
          (s * (larger - smaller)) :=
    pure_wz2_target_power_upper
      hdelta htarget.le htargetUpper hgap
  have hcoefficient :
      ENNReal.ofReal constant *
          Kakeya.realRpowENN target
            (larger - smaller) ≤
        1 :=
    (mul_le_mul_left'
      htargetGap (ENNReal.ofReal constant)).trans habsorb
  have hsplit :
      Kakeya.realRpowENN target (-smaller) =
        Kakeya.realRpowENN target
            (larger - smaller) *
          Kakeya.realRpowENN target (-larger) := by
    rw [Subunit.realRpowENN_mul htarget]
    congr 1
    ring
  rw [hsplit]
  calc
    ENNReal.ofReal constant *
          (Kakeya.realRpowENN target
              (larger - smaller) *
            Kakeya.realRpowENN target (-larger)) =
        (ENNReal.ofReal constant *
          Kakeya.realRpowENN target
            (larger - smaller)) *
          Kakeya.realRpowENN target (-larger) := by ring
    _ ≤ 1 * Kakeya.realRpowENN target (-larger) := by
      gcongr
    _ = Kakeya.realRpowENN target (-larger) := one_mul _

/-- Cancel a positive finite `ofReal` reciprocal from an ENNReal
inequality. -/
theorem pure_wz2_ofReal_inv_mul_le_one
    {constant : ℝ} {value : ENNReal}
    (hconstant : 0 < constant)
    (h : ENNReal.ofReal constant⁻¹ * value ≤ 1) :
    value ≤ ENNReal.ofReal constant := by
  let coefficient := ENNReal.ofReal constant
  have hcoefficientZero : coefficient ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hconstant).ne'
  have hcoefficientTop : coefficient ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hinverse :
      ENNReal.ofReal constant⁻¹ = coefficient⁻¹ :=
    ENNReal.ofReal_inv_of_pos hconstant
  rw [hinverse] at h
  have hscaled :=
    mul_le_mul_left' h coefficient
  rw [show
    coefficient * (coefficient⁻¹ * value) = value by
      rw [← mul_assoc,
        ENNReal.mul_inv_cancel
          hcoefficientZero hcoefficientTop,
        one_mul],
    mul_one] at hscaled
  exact hscaled

end Kakeya.Assouad

end
