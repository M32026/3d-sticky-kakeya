import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalGlobalScalarBudget

/-!
# Ceiling bound for the direct half-offset finite-slice global AD

This file isolates the conversion of the literal `Nat.ceil` cover factor to
the `6 * epsilon` source-scale loss.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

namespace PureWZ2DirectCommonYSourceAssembly

variable {logExponent : ℕ}
  {sigma epsilon delta : ℝ}
  (commonSource : PureWZ2DirectCommonYSourceAssembly
    logExponent sigma epsilon delta)

namespace TerminalGeometry

theorem finiteSlice_cover_base_le_rho_inv_sq
    (_hdelta : 0 < delta) :
    ENNReal.ofReal ((2 * (Nat.ceil
        (((finiteSliceAbsorbableSlopeBound commonSource + 3) *
            Real.sqrt 3) + 1) + 1) : ℕ) : ℝ) ≤
      ENNReal.ofReal
        ((2 * (((402 * pureWZ2DirectHalfOffsetTerminalLambda + 5) *
          Real.sqrt 3) + 3)) *
          (commonSource.halfOffsetAssembly.rho.1)⁻¹ ^ 2) := by
  let x : ℝ := ((finiteSliceAbsorbableSlopeBound commonSource + 3) *
    Real.sqrt 3) + 1
  let n : ℕ := 2 * (Nat.ceil x + 1)
  let B : ℝ := 2 *
    ((402 * pureWZ2DirectHalfOffsetTerminalLambda + 5) * Real.sqrt 3 + 3)
  have hrho : 0 < commonSource.halfOffsetAssembly.rho.1 :=
    commonSource.halfOffsetAssembly.cfg.extremal.delta_pos.trans_le
      commonSource.halfOffsetAssembly.rho.2.1
  have hrhoOne : commonSource.halfOffsetAssembly.rho.1 ≤ 1 :=
    commonSource.halfOffsetAssembly.rho.2.2
  have hinvOne : 1 ≤ commonSource.halfOffsetAssembly.rho.1⁻¹ ^ 2 := by
    have hinv : 1 ≤ commonSource.halfOffsetAssembly.rho.1⁻¹ :=
      (one_le_inv₀ hrho).2 hrhoOne
    nlinarith [sq_nonneg
      (commonSource.halfOffsetAssembly.rho.1⁻¹ - 1)]
  have hx : 0 ≤ x := by
    dsimp only [x]
    unfold finiteSliceAbsorbableSlopeBound
    positivity [pureWZ2DirectHalfOffsetTerminalLambda_pos]
  have hceil : (Nat.ceil x : ℝ) < x + 1 :=
    Nat.ceil_lt_add_one hx
  have hraw : (n : ℝ) ≤
      2 * ((finiteSliceAbsorbableSlopeBound commonSource + 3) *
        Real.sqrt 3 + 3) := by
    dsimp only [n, x]
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hslope : finiteSliceAbsorbableSlopeBound commonSource + 3 ≤
      (402 * pureWZ2DirectHalfOffsetTerminalLambda + 5) *
        commonSource.halfOffsetAssembly.rho.1⁻¹ ^ 2 := by
    unfold finiteSliceAbsorbableSlopeBound
    have hlambdaOne : 1 ≤ pureWZ2DirectHalfOffsetTerminalLambda :=
      pureWZ2DirectHalfOffsetTerminalLambda_one_le
    have htwo :
        2 * pureWZ2DirectHalfOffsetTerminalLambda ≤
          2 * pureWZ2DirectHalfOffsetTerminalLambda *
            commonSource.halfOffsetAssembly.rho.1⁻¹ ^ 2 := by
      have hproduct : 0 ≤
          pureWZ2DirectHalfOffsetTerminalLambda *
            (commonSource.halfOffsetAssembly.rho.1⁻¹ ^ 2 - 1) :=
        mul_nonneg (le_trans (by norm_num) hlambdaOne)
          (sub_nonneg.mpr hinvOne)
      nlinarith
    have hfive : (5 : ℝ) ≤
        5 * commonSource.halfOffsetAssembly.rho.1⁻¹ ^ 2 := by
      nlinarith [hinvOne]
    calc
      pureWZ2DirectHalfOffsetTerminalLambda *
            (2 + 400 * commonSource.halfOffsetAssembly.rho.1⁻¹ ^ 2) + 2 + 3 =
          400 * pureWZ2DirectHalfOffsetTerminalLambda *
              commonSource.halfOffsetAssembly.rho.1⁻¹ ^ 2 +
            2 * pureWZ2DirectHalfOffsetTerminalLambda + 5 := by ring
      _ ≤ 400 * pureWZ2DirectHalfOffsetTerminalLambda *
              commonSource.halfOffsetAssembly.rho.1⁻¹ ^ 2 +
            2 * pureWZ2DirectHalfOffsetTerminalLambda *
              commonSource.halfOffsetAssembly.rho.1⁻¹ ^ 2 +
            5 * commonSource.halfOffsetAssembly.rho.1⁻¹ ^ 2 :=
        add_le_add (add_le_add le_rfl htwo) hfive
      _ = _ := by ring
  have hreal : (n : ℝ) ≤
      B * commonSource.halfOffsetAssembly.rho.1⁻¹ ^ 2 := by
    have hsqrt : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
    have hslopeSqrt := mul_le_mul_of_nonneg_right hslope hsqrt
    have hthree : (3 : ℝ) ≤
        3 * commonSource.halfOffsetAssembly.rho.1⁻¹ ^ 2 := by
      nlinarith [hinvOne]
    dsimp only [B]
    exact hraw.trans (by nlinarith)
  change ENNReal.ofReal (n : ℝ) ≤ ENNReal.ofReal
    (B * commonSource.halfOffsetAssembly.rho.1⁻¹ ^ 2)
  exact ENNReal.ofReal_mono hreal

/-- The literal finite-slice constant has exactly the advertised six-epsilon
source loss. -/
theorem finiteSliceGlobalADRawConstant_le_source_power :
    finiteSliceGlobalADRawConstant commonSource ≤
      finiteSliceGlobalFiniteConstant *
        Kakeya.realRpowENN delta
          (-(finiteSliceGlobalSourceLoss commonSource)) := by
  let rho := commonSource.halfOffsetAssembly.rho.1
  let B : ℝ := 2 *
    ((402 * pureWZ2DirectHalfOffsetTerminalLambda + 5) * Real.sqrt 3 + 3)
  let H : ENNReal := ((2 * finiteSliceHeightCellRadius + 1 : ℕ) : ENNReal)
  let n : ℕ := 2 * (Nat.ceil
    (((finiteSliceAbsorbableSlopeBound commonSource + 3) * Real.sqrt 3) + 1) + 1)
  have hdelta : 0 < delta := commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hrho : 0 < rho :=
    commonSource.halfOffsetAssembly.cfg.extremal.delta_pos.trans_le
      commonSource.halfOffsetAssembly.rho.2.1
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity [pureWZ2DirectHalfOffsetTerminalLambda_pos]
  have hbase := finiteSlice_cover_base_le_rho_inv_sq commonSource hdelta
  have hbase' : (n : ENNReal) ≤ ENNReal.ofReal (B * rho⁻¹ ^ 2) := by
    calc
      (n : ENNReal) = ENNReal.ofReal (n : ℝ) := by simp
      _ ≤ ENNReal.ofReal (B * rho⁻¹ ^ 2) := by
        simpa [n, B, rho] using hbase
  have hcover : (n : ENNReal) ^ 3 ≤
      (ENNReal.ofReal (B * rho⁻¹ ^ 2)) ^ 3 :=
    pow_le_pow_left₀ bot_le hbase' 3
  have hrhoSix : rho⁻¹ ^ 6 =
      50 ^ 6 * Real.rpow delta (-(6 * epsilon)) := by
    have hp : 0 < Real.rpow delta epsilon := Real.rpow_pos_of_pos hdelta _
    have hp6 : (Real.rpow delta epsilon) ^ 6 =
        Real.rpow delta (6 * epsilon) := by
      simpa [mul_comm] using rpow_nat_pow hdelta epsilon 6
    have hneg : Real.rpow delta (-(6 * epsilon)) =
        (Real.rpow delta (6 * epsilon))⁻¹ :=
      Real.rpow_neg hdelta.le (6 * epsilon)
    change (commonSource.halfOffsetAssembly.rho.1)⁻¹ ^ 6 = _
    rw [commonSource.halfOffsetAssembly_rho_eq_power_div, hneg, ← hp6]
    field_simp [hp.ne']
  have hcoverPower :
      (n : ENNReal) ^ 3 ≤
        ENNReal.ofReal (B ^ 3 * 50 ^ 6) *
          Kakeya.realRpowENN delta (-(6 * epsilon)) := by
    calc
      _ ≤ (ENNReal.ofReal (B * rho⁻¹ ^ 2)) ^ 3 := hcover
      _ = ENNReal.ofReal ((B * rho⁻¹ ^ 2) ^ 3) := by
        rw [ENNReal.ofReal_pow (mul_nonneg hB (sq_nonneg _))]
      _ = ENNReal.ofReal (B ^ 3 * 50 ^ 6) *
          Kakeya.realRpowENN delta (-(6 * epsilon)) := by
        rw [show (B * rho⁻¹ ^ 2) ^ 3 = B ^ 3 * rho⁻¹ ^ 6 by ring,
          hrhoSix, Kakeya.realRpowENN]
        rw [show B ^ 3 * (50 ^ 6 * Real.rpow delta (-(6 * epsilon))) =
          (B ^ 3 * 50 ^ 6) * Real.rpow delta (-(6 * epsilon)) by ring]
        rw [ENNReal.ofReal_mul
          (mul_nonneg (pow_nonneg hB 3) (by norm_num : (0 : ℝ) ≤ 50 ^ 6))]
  have hpowers :
      Kakeya.realRpowENN delta (-(6 * epsilon)) *
          Kakeya.realRpowENN delta
            (-commonSource.halfOffsetAssembly.technicalLoss) =
        Kakeya.realRpowENN delta
          (-(finiteSliceGlobalSourceLoss commonSource)) := by
    rw [← realRpowENN_add hdelta]
    unfold finiteSliceGlobalSourceLoss
    congr 1
    ring
  have hfinal : (n : ENNReal) ^ 3 *
      (H * Kakeya.realRpowENN delta
        (-commonSource.halfOffsetAssembly.technicalLoss)) ≤
      ENNReal.ofReal (B ^ 3 * 50 ^ 6) * H *
        Kakeya.realRpowENN delta
          (-(finiteSliceGlobalSourceLoss commonSource)) := by
    calc
      _ ≤ (ENNReal.ofReal (B ^ 3 * 50 ^ 6) *
          Kakeya.realRpowENN delta (-(6 * epsilon))) *
        (H * Kakeya.realRpowENN delta
          (-commonSource.halfOffsetAssembly.technicalLoss)) := by
        exact mul_le_mul_right' hcoverPower _
      _ = ENNReal.ofReal (B ^ 3 * 50 ^ 6) * H *
        Kakeya.realRpowENN delta
          (-(finiteSliceGlobalSourceLoss commonSource)) := by
        rw [← hpowers]
        ring
  simpa [finiteSliceGlobalADRawConstant, finiteSliceGlobalFiniteConstant,
    n, B, H] using hfinal

/-- Final public global-AD closure for the literal actual terminal.  Both the
ceiling cover and the fixed coefficient are discharged before the runtime
source is chosen. -/
theorem exists_delta_for_cubicalShading_global_ad_at_outputLoss
    (technicalLoss outputLoss : ℝ)
    (hepsilon : 0 < epsilon)
    (houtputLoss : 0 ≤ outputLoss)
    (hgap : technicalLoss + 6 * epsilon <
      (1 - 2 * epsilon) * outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        commonSource.halfOffsetAssembly.technicalLoss = technicalLoss →
        0 < sigma → sigma < 1 →
        0 < delta → delta ≤ delta₀ →
        ∀ terminal : commonSource.TerminalGeometry,
          ∀ z ∈ Set.Icc (-1 : ℝ) 1,
            PureWZ2PaperADSet1
              (scalarProjection
                (globalGrainDirection
                  (safePublicSlope commonSource terminal z))
                (horizontalSlice terminal.cubicalShading.union z))
              terminal.targetDelta (1 - sigma)
              (Kakeya.realRpowENN terminal.targetDelta (-outputLoss)) := by
  rcases exists_delta_for_finiteSliceGlobal_source_to_target
      (epsilon := epsilon) technicalLoss outputLoss
      finiteSliceGlobalFiniteConstant finiteSliceGlobalFiniteConstant_ne_top
      hepsilon houtputLoss hgap with
    ⟨delta₀, hdelta₀Pos, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀Pos, hdelta₀One, ?_⟩
  intro logExponent sigma delta commonSource htechnical hsigma hsigmaOne
    hdelta hdeltaBound terminal z hz
  have hraw := finiteSliceGlobalADRawConstant_le_source_power commonSource
  have htarget := habsorb commonSource htechnical hdelta hdeltaBound
  have htargetOne : 1 ≤
      Kakeya.realRpowENN terminal.targetDelta (-outputLoss) := by
    simpa [Kakeya.realRpowENN] using
      (pure_wz2_rpowENN_antitone
        commonSource.halfOffsetLineClassTargetDelta_pos
        (commonSource.halfOffsetLineClassTargetDelta_small.le.trans (by norm_num))
        (by linarith : -outputLoss ≤ 0))
  have htargetTop :
      Kakeya.realRpowENN terminal.targetDelta (-outputLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  exact (cubicalShading_global_ad_finiteSlice commonSource terminal
    hsigma hsigmaOne z hz).weaken_constant (hraw.trans htarget)
      htargetOne htargetTop

/-- Uniform public closure when the source terminal AD loss is at most
`2 * epsilon`.  The threshold is chosen from the fixed `8 * epsilon` loss,
so it is independent of the runtime technical loss. -/
theorem exists_delta_for_cubicalShading_global_ad_uniform_at_outputLoss
    (outputLoss : ℝ)
    (hepsilon : 0 < epsilon)
    (houtputLoss : 0 ≤ outputLoss)
    (hgap : 8 * epsilon < (1 - 2 * epsilon) * outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        commonSource.halfOffsetAssembly.technicalLoss ≤ 2 * epsilon →
        0 < sigma → sigma < 1 →
        0 < delta → delta ≤ delta₀ →
        ∀ terminal : commonSource.TerminalGeometry,
          ∀ z ∈ Set.Icc (-1 : ℝ) 1,
            PureWZ2PaperADSet1
              (scalarProjection
                (globalGrainDirection
                  (safePublicSlope commonSource terminal z))
                (horizontalSlice terminal.cubicalShading.union z))
              terminal.targetDelta (1 - sigma)
              (Kakeya.realRpowENN terminal.targetDelta (-outputLoss)) := by
  rcases exists_delta_for_cubicalShading_global_ad_scalar_budget
      (epsilon := epsilon) (8 * epsilon) outputLoss
      finiteSliceGlobalFiniteConstant finiteSliceGlobalFiniteConstant_ne_top
      hepsilon houtputLoss hgap with
    ⟨delta₀, hdelta₀Pos, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀Pos, hdelta₀One, ?_⟩
  intro logExponent sigma delta commonSource htechnical hsigma hsigmaOne
    hdelta hdeltaBound terminal z hz
  have hsourceLoss : finiteSliceGlobalSourceLoss commonSource ≤ 8 * epsilon := by
    unfold finiteSliceGlobalSourceLoss
    linarith
  have hpower : Kakeya.realRpowENN delta
      (-(finiteSliceGlobalSourceLoss commonSource)) ≤
      Kakeya.realRpowENN delta (-(8 * epsilon)) := by
    exact realRpowENN_antitone hdelta
      (hdeltaBound.trans hdelta₀One) (by linarith)
  have hraw := finiteSliceGlobalADRawConstant_le_source_power commonSource
  have htarget := habsorb commonSource hdelta hdeltaBound
  have htargetOne : 1 ≤
      Kakeya.realRpowENN terminal.targetDelta (-outputLoss) := by
    simpa [Kakeya.realRpowENN] using
      (pure_wz2_rpowENN_antitone
        commonSource.halfOffsetLineClassTargetDelta_pos
        (commonSource.halfOffsetLineClassTargetDelta_small.le.trans (by norm_num))
        (by linarith : -outputLoss ≤ 0))
  have htargetTop :
      Kakeya.realRpowENN terminal.targetDelta (-outputLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  exact (cubicalShading_global_ad_finiteSlice commonSource terminal
    hsigma hsigmaOne z hz).weaken_constant
      (hraw.trans ((mul_le_mul_left' hpower _).trans htarget))
      htargetOne htargetTop

end TerminalGeometry
end PureWZ2DirectCommonYSourceAssembly
end Kakeya.Assouad
