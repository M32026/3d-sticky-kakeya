import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalExactVolume
import MyLeanRepo.Kakeya.Assouad.ExponentArithmetic

/-!
# Uniform power schedule for the exact terminal carrier volume
-/

noncomputable section

namespace Kakeya.Assouad

theorem pureWZ2_fixedLineParentFiberBound_real_le
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    (pureWZ2FixedLineParentFiberBound delta : ℝ) ≤
      12 * Real.rpow delta (-(1 / 2 : ℝ)) := by
  let root := Real.sqrt delta
  have hroot : 0 < root := Real.sqrt_pos.mpr hdelta
  have hrootOne : root ≤ 1 := Real.sqrt_le_one.mpr hdeltaOne
  have hrootSq : root ^ 2 = delta := Real.sq_sqrt hdelta.le
  have hsqrtThree : Real.sqrt 3 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  let x := (root + delta) / (delta / Real.sqrt 3)
  have hxNonneg : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hx : x ≤ 4 / root := by
    have hsqrtThreePos : 0 < Real.sqrt 3 := by positivity
    have hxEq : x = (root + delta) * Real.sqrt 3 / delta := by
      dsimp only [x]
      field_simp [hdelta.ne', hsqrtThreePos.ne']
      <;> ring
    have hdeltaRoot : delta ≤ root := by
      nlinarith [hrootSq, hrootOne]
    have hlhs : (root + delta) * Real.sqrt 3 ≤ 2 * (root + delta) := by
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_left hsqrtThree
          (show 0 ≤ root + delta by positivity))
    have hbound : (root + delta) * Real.sqrt 3 ≤ 4 * root := by
      exact hlhs.trans (by linarith)
    have hrhs : 4 / root * delta = 4 * root := by
      rw [← hrootSq]
      field_simp [hroot.ne']
    rw [hxEq, div_le_iff₀ hdelta, hrhs]
    exact hbound
  have hceil : (Nat.ceil x : ℝ) ≤ x + 1 :=
    (Nat.ceil_lt_add_one hxNonneg).le
  have htwo : 2 ≤ 2 / root := by
    rw [le_div_iff₀ hroot]
    nlinarith
  have hy : (pureWZ2FixedLineParentYBound delta : ℝ) ≤ 6 / root := by
    dsimp only [pureWZ2FixedLineParentYBound]
    norm_num only [Nat.cast_add, Nat.cast_one]
    change (Nat.ceil x : ℝ) + 1 ≤ 6 / root
    calc
      (Nat.ceil x : ℝ) + 1 ≤ x + 2 := by linarith
      _ ≤ 4 / root + 2 := by linarith
      _ ≤ 4 / root + 2 / root := by linarith
      _ = 6 / root := by ring
  have hfiber :
      (pureWZ2FixedLineParentFiberBound delta : ℝ) ≤ 12 / root := by
    calc
      (pureWZ2FixedLineParentFiberBound delta : ℝ) =
          2 * (pureWZ2FixedLineParentYBound delta : ℝ) := by
        simp [pureWZ2FixedLineParentFiberBound]
      _ ≤ 2 * (6 / root) := by gcongr
      _ = 12 / root := by ring
  have hrpow : Real.rpow delta (-(1 / 2 : ℝ)) = 1 / root := by
    have hsqrtEq : Real.rpow delta (1 / 2 : ℝ) = Real.sqrt delta :=
      (Real.sqrt_eq_rpow delta).symm
    calc
      Real.rpow delta (-(1 / 2 : ℝ)) =
          (Real.rpow delta (1 / 2 : ℝ))⁻¹ :=
        Real.rpow_neg hdelta.le (1 / 2 : ℝ)
      _ = (Real.sqrt delta)⁻¹ := by rw [hsqrtEq]
      _ = 1 / root := by simp [root, one_div]
  rw [hrpow]
  simpa [div_eq_mul_inv] using hfiber

theorem pureWZ2_fixedLineParentFiberBound_ennreal_le
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    (pureWZ2FixedLineParentFiberBound delta : ENNReal) ≤
      12 * Kakeya.realRpowENN delta (-(1 / 2 : ℝ)) := by
  have hreal := pureWZ2_fixedLineParentFiberBound_real_le hdelta hdeltaOne
  rw [Kakeya.realRpowENN]
  have hcast : (pureWZ2FixedLineParentFiberBound delta : ENNReal) =
      ENNReal.ofReal (pureWZ2FixedLineParentFiberBound delta : ℝ) := by
    norm_cast
  rw [hcast, ← ENNReal.ofReal_ofNat 12, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_mono hreal

private theorem pureWZ2_realRpowENN_one_div
    {delta exponent : ℝ} (hdelta : 0 < delta) :
    Kakeya.realRpowENN (1 / delta) exponent =
      Kakeya.realRpowENN delta (-exponent) := by
  simp only [Kakeya.realRpowENN]
  congr 1
  calc
    Real.rpow (1 / delta) exponent =
        Real.rpow 1 exponent / Real.rpow delta exponent :=
      Real.div_rpow (by norm_num) hdelta.le exponent
    _ = (Real.rpow delta exponent)⁻¹ := by simp
    _ = Real.rpow delta (-exponent) :=
      (Real.rpow_neg hdelta.le exponent).symm

def pureWZ2TerminalExactVolumeConstant : ENNReal :=
  3 * 4 * (132 * 10) * 12 *
    pureWZ2TerminalExactParentThinning * pureWZ2TerminalExactAnchorCost

theorem pureWZ2_terminalExact_volumeCost_upper
    {delta sigma inputLoss : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
      pureWZ2TerminalExactVolumeConstant *
        Kakeya.realRpowENN delta (1 + sigma - inputLoss) := by
  have hdeltaRoot : delta ≤ Real.sqrt delta := by
    nlinarith [Real.sqrt_nonneg delta, Real.sq_sqrt hdelta.le, hdeltaOne]
  have hthicknessReal : Real.sqrt delta + 2 * delta ≤ 3 * Real.sqrt delta := by
    linarith
  have hthickness : ENNReal.ofReal (Real.sqrt delta + 2 * delta) ≤
      3 * Kakeya.realRpowENN delta (1 / 2 : ℝ) := by
    rw [show Kakeya.realRpowENN delta (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt delta) by
        simp [Kakeya.realRpowENN, Real.sqrt_eq_rpow]]
    calc
      ENNReal.ofReal (Real.sqrt delta + 2 * delta) ≤
          ENNReal.ofReal (3 * Real.sqrt delta) :=
        ENNReal.ofReal_mono hthicknessReal
      _ = 3 * ENNReal.ofReal (Real.sqrt delta) := by
        rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num)]
  have hdisk : ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi ≤
      4 * Kakeya.realRpowENN delta 2 := by
    have hdeltaNonneg : 0 ≤ delta := hdelta.le
    have hpow : ENNReal.ofReal delta ^ 2 =
        Kakeya.realRpowENN delta 2 := by
      simp [Kakeya.realRpowENN, Real.rpow_two, ← ENNReal.ofReal_mul hdeltaNonneg,
        pow_two]
    have hpi : ENNReal.ofReal Real.pi ≤ 4 := by
      simpa using ENNReal.ofReal_le_ofReal Real.pi_le_four
    calc
      ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi =
          Kakeya.realRpowENN delta 2 * ENNReal.ofReal Real.pi := by rw [hpow]
      _ ≤ Kakeya.realRpowENN delta 2 * 4 := by gcongr
      _ = 4 * Kakeya.realRpowENN delta 2 := by ring
  have hglobal :
      132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
          Kakeya.realRpowENN (1 / delta) (1 - sigma) ≤
        (132 * 10 : ENNReal) *
          Kakeya.realRpowENN delta (-inputLoss - (1 - sigma)) := by
    rw [pureWZ2_realRpowENN_one_div hdelta]
    calc
      132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
            Kakeya.realRpowENN delta (-(1 - sigma)) =
          (132 * 10 : ENNReal) *
            (Kakeya.realRpowENN delta (-inputLoss) *
              Kakeya.realRpowENN delta (-(1 - sigma))) := by ring
      _ = (132 * 10 : ENNReal) *
          Kakeya.realRpowENN delta
            ((-inputLoss) + (-(1 - sigma))) := by
        rw [realRpowENN_add hdelta]
      _ ≤ (132 * 10 : ENNReal) *
          Kakeya.realRpowENN delta (-inputLoss - (1 - sigma)) := le_rfl
  have hparent :=
    pureWZ2_fixedLineParentFiberBound_ennreal_le hdelta hdeltaOne
  have hpowers :
      Kakeya.realRpowENN delta (1 / 2 : ℝ) *
          Kakeya.realRpowENN delta 2 *
          Kakeya.realRpowENN delta (-inputLoss - (1 - sigma)) *
          Kakeya.realRpowENN delta (-(1 / 2 : ℝ)) =
        Kakeya.realRpowENN delta (1 + sigma - inputLoss) := by
    calc
      Kakeya.realRpowENN delta (1 / 2 : ℝ) *
            Kakeya.realRpowENN delta 2 *
            Kakeya.realRpowENN delta (-inputLoss - (1 - sigma)) *
            Kakeya.realRpowENN delta (-(1 / 2 : ℝ)) =
          Kakeya.realRpowENN delta ((1 / 2 : ℝ) + 2) *
            Kakeya.realRpowENN delta (-inputLoss - (1 - sigma)) *
            Kakeya.realRpowENN delta (-(1 / 2 : ℝ)) := by
        rw [realRpowENN_add hdelta]
      _ = Kakeya.realRpowENN delta
            (((1 / 2 : ℝ) + 2) + (-inputLoss - (1 - sigma))) *
            Kakeya.realRpowENN delta (-(1 / 2 : ℝ)) := by
        exact congrArg
          (fun value => value *
            Kakeya.realRpowENN delta (-(1 / 2 : ℝ)))
          (realRpowENN_add hdelta
            ((1 / 2 : ℝ) + 2) (-inputLoss - (1 - sigma))).symm
      _ = Kakeya.realRpowENN delta
          ((((1 / 2 : ℝ) + 2) + (-inputLoss - (1 - sigma))) +
            (-(1 / 2 : ℝ))) := by
        exact (realRpowENN_add hdelta
          (((1 / 2 : ℝ) + 2) + (-inputLoss - (1 - sigma)))
          (-(1 / 2 : ℝ))).symm
      _ = Kakeya.realRpowENN delta (1 + sigma - inputLoss) := by
        congr 1
        ring
  rw [pureWZ2TerminalExactVolumeCost]
  calc
    ENNReal.ofReal (Real.sqrt delta + 2 * delta) *
          (ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi) *
          (132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
            Kakeya.realRpowENN (1 / delta) (1 - sigma)) *
          (pureWZ2FixedLineParentFiberBound delta : ENNReal) *
          pureWZ2TerminalExactParentThinning *
          pureWZ2TerminalExactAnchorCost ≤
        (3 * Kakeya.realRpowENN delta (1 / 2 : ℝ)) *
          (4 * Kakeya.realRpowENN delta 2) *
          ((132 * 10 : ENNReal) *
            Kakeya.realRpowENN delta (-inputLoss - (1 - sigma))) *
          (12 * Kakeya.realRpowENN delta (-(1 / 2 : ℝ))) *
          pureWZ2TerminalExactParentThinning *
          pureWZ2TerminalExactAnchorCost := by gcongr
    _ = pureWZ2TerminalExactVolumeConstant *
        Kakeya.realRpowENN delta (1 + sigma - inputLoss) := by
      simp only [pureWZ2TerminalExactVolumeConstant]
      calc
        3 * Kakeya.realRpowENN delta (1 / 2) *
                (4 * Kakeya.realRpowENN delta 2) *
                (132 * 10 *
                  Kakeya.realRpowENN delta (-inputLoss - (1 - sigma))) *
                (12 * Kakeya.realRpowENN delta (-(1 / 2))) *
              ↑pureWZ2TerminalExactParentThinning *
            pureWZ2TerminalExactAnchorCost =
          3 * 4 * (132 * 10) * 12 *
              ↑pureWZ2TerminalExactParentThinning *
            pureWZ2TerminalExactAnchorCost *
            (Kakeya.realRpowENN delta (1 / 2) *
              Kakeya.realRpowENN delta 2 *
              Kakeya.realRpowENN delta (-inputLoss - (1 - sigma)) *
              Kakeya.realRpowENN delta (-(1 / 2))) := by ring
        _ = _ := by rw [hpowers]

theorem pureWZ2_terminalExact_windowSupply_lower
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (hdeltaOne : delta ≤ 1) :
    (4 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
        (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) ≤
      pureWZ2TerminalExactWindowSupply
          (MeasureTheory.volume prepared.shadow.union) delta *
        terminal.sticky.balanced.cellMass := by
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hrootOne : Real.sqrt delta ≤ 1 := Real.sqrt_le_one.mpr hdeltaOne
  have hdenomReal : 2 + delta + Real.sqrt delta ≤ 4 := by linarith
  have hdenom : ENNReal.ofReal (2 + delta + Real.sqrt delta) ≤ 4 := by
    simpa using ENNReal.ofReal_le_ofReal hdenomReal
  have hsource : Kakeya.realRpowENN delta (sigma + stickyLoss) ≤
      MeasureTheory.volume prepared.shadow.union := by
    rw [prepared.shadow_union]
    exact terminalSource.volume_lower
  have hroot : ENNReal.ofReal (Real.sqrt delta) =
      Kakeya.realRpowENN delta (1 / 2 : ℝ) := by
    simp [Kakeya.realRpowENN, Real.sqrt_eq_rpow]
  have hwindow :
      (4 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (sigma + stickyLoss + 1 / 2) ≤
        pureWZ2TerminalExactWindowSupply
          (MeasureTheory.volume prepared.shadow.union) delta := by
    have hnum : Kakeya.realRpowENN delta (sigma + stickyLoss + 1 / 2) ≤
        MeasureTheory.volume prepared.shadow.union *
          ENNReal.ofReal (Real.sqrt delta) := by
      rw [realRpowENN_add hdelta, hroot]
      gcongr
    calc
      (4 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
            (sigma + stickyLoss + 1 / 2) ≤
          (4 : ENNReal)⁻¹ *
            (MeasureTheory.volume prepared.shadow.union *
              ENNReal.ofReal (Real.sqrt delta)) := by gcongr
      _ = (MeasureTheory.volume prepared.shadow.union *
              ENNReal.ofReal (Real.sqrt delta)) / 4 := by
        change (4 : ENNReal)⁻¹ *
            (MeasureTheory.volume prepared.shadow.union *
              ENNReal.ofReal (Real.sqrt delta)) =
          (MeasureTheory.volume prepared.shadow.union *
              ENNReal.ofReal (Real.sqrt delta)) * (4 : ENNReal)⁻¹
        ac_rfl
      _ ≤ (MeasureTheory.volume prepared.shadow.union *
              ENNReal.ofReal (Real.sqrt delta)) /
            ENNReal.ofReal (2 + delta + Real.sqrt delta) :=
        ENNReal.div_le_div_left hdenom _
      _ = pureWZ2TerminalExactWindowSupply
          (MeasureTheory.volume prepared.shadow.union) delta := rfl
  have hcell := terminal.source_floor_power
  have hpowers :
      Kakeya.realRpowENN delta (sigma + stickyLoss + 1 / 2) *
          Kakeya.realRpowENN delta
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) =
        Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) := by
    rw [← realRpowENN_add hdelta]
    congr 1
    ring
  calc
    (4 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) =
        ((4 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (sigma + stickyLoss + 1 / 2)) *
          Kakeya.realRpowENN delta
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) := by
      rw [← hpowers]
      ac_rfl
    _ ≤ pureWZ2TerminalExactWindowSupply
          (MeasureTheory.volume prepared.shadow.union) delta *
        terminal.sticky.balanced.cellMass := by gcongr

/-- Every admitted terminal window carries a quarter of the canonical global
window supply.  The factor four is the only extra cost paid by the terminal
multi-window route. -/
theorem pureWZ2_terminalExact_windowSupply_lower_of_window
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (window : PureWZ2TerminalCertifiedWindow prepared)
    (hdeltaOne : delta ≤ 1) :
    (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
        (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) ≤
      window.volumeSupply * terminal.sticky.balanced.cellMass := by
  have hraw := pureWZ2_terminalExact_windowSupply_lower
    (prepared := prepared) hdeltaOne
  let average := pureWZ2TerminalExactWindowSupply
    (MeasureTheory.volume prepared.shadow.union) delta
  have hquarter : (4 : ENNReal)⁻¹ * average ≤ window.volumeSupply := by
    simpa [average, pureWZ2TerminalExactWindowSupply] using window.minimum_supply
  calc
    (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) =
        (4 : ENNReal)⁻¹ *
          ((4 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
            (2 + 3 * sigma / 2 + 5 * stickyLoss / 2)) := by
      rw [show (16 : ENNReal)⁻¹ = (4 : ENNReal)⁻¹ * (4 : ENNReal)⁻¹ by
        rw [← ENNReal.mul_inv] <;> norm_num <;> tauto]
      ac_rfl
    _ ≤ (4 : ENNReal)⁻¹ *
        (average * terminal.sticky.balanced.cellMass) := by gcongr
    _ = ((4 : ENNReal)⁻¹ * average) *
        terminal.sticky.balanced.cellMass := by ring
    _ ≤ window.volumeSupply * terminal.sticky.balanced.cellMass := by gcongr

def pureWZ2TerminalExactVolumeConstantReal : ℝ :=
  3 * 4 * (132 * 10) * 12 *
    pureWZ2TerminalExactParentThinning * (512 * (2 * 512 * 57))

theorem pureWZ2_terminalExact_volumeConstant_eq :
    pureWZ2TerminalExactVolumeConstant =
      ENNReal.ofReal pureWZ2TerminalExactVolumeConstantReal := by
  norm_num [pureWZ2TerminalExactVolumeConstant,
    pureWZ2TerminalExactVolumeConstantReal,
    pureWZ2TerminalExactParentThinning,
    pureWZ2TerminalExactAnchorCost]

theorem pureWZ2_terminalExact_volume_budget_schedule
    {inputLoss stickyLoss volumeLoss : ℝ}
    (hgap : inputLoss + 5 * stickyLoss / 2 < volumeLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sigma delta : ℝ}, 0 < delta → delta ≤ delta₀ →
        Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) *
            pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
          (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
            (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) := by
  have hconstant : 0 < 16 * pureWZ2TerminalExactVolumeConstantReal := by
    norm_num [pureWZ2TerminalExactVolumeConstantReal,
      pureWZ2TerminalExactParentThinning]
  have hexponent : 5 * stickyLoss / 2 < volumeLoss - inputLoss := by
    linarith
  rcases exists_delta₀_const_mul_rpow_le
      (16 * pureWZ2TerminalExactVolumeConstantReal) hconstant
      (5 * stickyLoss / 2) (volumeLoss - inputLoss) hexponent with
    ⟨delta₀, hdelta₀, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro sigma delta hdelta hdeltaSmall
  have hdeltaOne : delta ≤ 1 := hdeltaSmall.trans hdelta₀One
  have hcost := pureWZ2_terminalExact_volumeCost_upper
    (sigma := sigma) (inputLoss := inputLoss) hdelta hdeltaOne
  have habsorb' := habsorb delta hdelta hdeltaSmall
  have hconstantCast :
      ENNReal.ofReal (16 * pureWZ2TerminalExactVolumeConstantReal) =
        16 * pureWZ2TerminalExactVolumeConstant := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
      ← pureWZ2_terminalExact_volumeConstant_eq]
    norm_num
  rw [hconstantCast] at habsorb'
  let base : ℝ := 2 + 3 * sigma / 2
  have htargetCombine :
      Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) *
          Kakeya.realRpowENN delta (1 + sigma - inputLoss) =
        Kakeya.realRpowENN delta (base + (volumeLoss - inputLoss)) := by
    rw [← realRpowENN_add hdelta]
    congr 1
    dsimp only [base]
    ring
  have hsupplyCombine :
      Kakeya.realRpowENN delta base *
          Kakeya.realRpowENN delta (5 * stickyLoss / 2) =
        Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) := by
    rw [← realRpowENN_add hdelta]
  have habsorbed :
      pureWZ2TerminalExactVolumeConstant *
          Kakeya.realRpowENN delta (base + (volumeLoss - inputLoss)) ≤
        (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) := by
    have hscaled :
        16 * (pureWZ2TerminalExactVolumeConstant *
          Kakeya.realRpowENN delta (base + (volumeLoss - inputLoss))) ≤
          Kakeya.realRpowENN delta
            (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) := by
      calc
        16 * (pureWZ2TerminalExactVolumeConstant *
              Kakeya.realRpowENN delta (base + (volumeLoss - inputLoss))) =
            Kakeya.realRpowENN delta base *
              ((16 * pureWZ2TerminalExactVolumeConstant) *
                Kakeya.realRpowENN delta (volumeLoss - inputLoss)) := by
          rw [realRpowENN_add hdelta]
          ring
        _ ≤ Kakeya.realRpowENN delta base *
              Kakeya.realRpowENN delta (5 * stickyLoss / 2) := by
          gcongr
        _ = Kakeya.realRpowENN delta
            (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) := hsupplyCombine
    have hdiv :
        pureWZ2TerminalExactVolumeConstant *
              Kakeya.realRpowENN delta (base + (volumeLoss - inputLoss)) ≤
            Kakeya.realRpowENN delta
              (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) / 16 := by
      apply (ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).2
      simpa [mul_comm] using hscaled
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  calc
    Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
        Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) *
          (pureWZ2TerminalExactVolumeConstant *
            Kakeya.realRpowENN delta (1 + sigma - inputLoss)) := by gcongr
    _ = pureWZ2TerminalExactVolumeConstant *
        Kakeya.realRpowENN delta (base + (volumeLoss - inputLoss)) := by
      rw [← htargetCombine]
      ring
    _ ≤ _ := habsorbed

theorem PureWZ2TerminalExactGraphPreparation.power_volume_lower_of_schedule
    {sigma inputLoss delta stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    {residue : PureWZ2TerminalParentYResidueData selection}
    {retained : PureWZ2TerminalRetainedShadingData residue}
    {sources : PureWZ2TerminalSourceFamily retained}
    {band : PureWZ2TerminalFixedBandSelection sources}
    {phase : PureWZ2TerminalHeightPhaseSelection band}
    {anchored : PureWZ2TerminalAnchoredPieceData phase}
    (prep : PureWZ2TerminalExactGraphPreparation anchored)
    (hminimum :
      (4 : ENNReal)⁻¹ *
          (MeasureTheory.volume prepared.shadow.union *
            ENNReal.ofReal (Real.sqrt delta) /
            ENNReal.ofReal (2 + delta + Real.sqrt delta)) ≤
        window.volumeSupply)
    (hbudget :
      Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
        (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2)) :
    Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) ≤
      MeasureTheory.volume prep.shadow.union := by
  apply prep.power_volume_lower
  exact hbudget.trans
    (by
      have hglobal := pureWZ2_terminalExact_windowSupply_lower
        (prepared := prepared) source.extremal.delta_le_one
      let average := pureWZ2TerminalExactWindowSupply
        (MeasureTheory.volume prepared.shadow.union) delta
      calc
        (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
              (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) =
            (4 : ENNReal)⁻¹ *
              ((4 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
                (2 + 3 * sigma / 2 + 5 * stickyLoss / 2)) := by
          rw [show (16 : ENNReal)⁻¹ =
              (4 : ENNReal)⁻¹ * (4 : ENNReal)⁻¹ by
            rw [← ENNReal.mul_inv] <;> norm_num <;> tauto]
          ac_rfl
        _ ≤ (4 : ENNReal)⁻¹ *
            (average * terminal.sticky.balanced.cellMass) := by
          gcongr
        _ = ((4 : ENNReal)⁻¹ * average) *
            terminal.sticky.balanced.cellMass := by ring
        _ ≤ window.volumeSupply *
            terminal.sticky.balanced.cellMass := by
          gcongr
          simpa [average, pureWZ2TerminalExactWindowSupply] using hminimum)

end Kakeya.Assouad

end
