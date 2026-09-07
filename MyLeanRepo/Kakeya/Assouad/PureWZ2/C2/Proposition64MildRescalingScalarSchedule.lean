import Mathlib.Tactic

/-!
# Proposition 6.4 family-independent mild-rescaling scalar schedule

This module isolates only the scalar quantifier order in the `P0`/`P7`
checkpoint for Proposition 6.4.  The absolute constants are fixed before the
schedule is chosen.  No tube family, shading, affine map, packet, or CWA datum
occurs in the statement.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The base-change inequality used after mild rescaling.

For a source scale in `(0, 1]`, increasing the scale from `sourceDelta` to
`finalDelta` and spending at most
`(1 - C * epsilon₂) * outputLoss` preserves the requested output power. -/
theorem pureWZ2Proposition64_mildRescaling_baseChange
    {sourceDelta finalDelta totalLoss outputLoss C epsilon₂ : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceDeltaOne : sourceDelta ≤ 1)
    (houtputLoss : 0 < outputLoss)
    (_hrescalingExponent : 0 < 1 - C * epsilon₂)
    (hsourceFinal : sourceDelta ≤ finalDelta)
    (hfinalUpper :
      finalDelta ≤ sourceDelta ^ (1 - C * epsilon₂))
    (htotalLoss :
      totalLoss ≤ (1 - C * epsilon₂) * outputLoss) :
    sourceDelta ^ (-totalLoss) ≤ finalDelta ^ (-outputLoss) := by
  have hfinalDelta : 0 < finalDelta :=
    hsourceDelta.trans_le hsourceFinal
  have hlossExponent :
      -((1 - C * epsilon₂) * outputLoss) ≤ -totalLoss := by
    linarith
  have hsourcePower :
      sourceDelta ^ (-totalLoss) ≤
        sourceDelta ^ (-((1 - C * epsilon₂) * outputLoss)) :=
    Real.rpow_le_rpow_of_exponent_ge
      hsourceDelta hsourceDeltaOne hlossExponent
  have hfactor :
      sourceDelta ^ (-((1 - C * epsilon₂) * outputLoss)) =
        (sourceDelta ^ (1 - C * epsilon₂)) ^ (-outputLoss) := by
    rw [← Real.rpow_mul hsourceDelta.le]
    congr 1
    ring
  calc
    sourceDelta ^ (-totalLoss) ≤
        sourceDelta ^ (-((1 - C * epsilon₂) * outputLoss)) :=
      hsourcePower
    _ = (sourceDelta ^ (1 - C * epsilon₂)) ^ (-outputLoss) := hfactor
    _ ≤ finalDelta ^ (-outputLoss) :=
      Real.rpow_le_rpow_of_nonpos
        hfinalDelta hfinalUpper (by linarith)

/-- A family-independent scalar schedule for the `P0`/`P7` part of
Proposition 6.4.

The schedule fixes `N`, `epsilon₂`, and a positive working loss before any
runtime family is chosen.  Its source cutoff simultaneously enforces the
target-scale power bound and the positive-log regime. -/
structure PureWZ2Proposition64MildRescalingScalarSchedule
    (outputLoss targetDelta₀ C Ctotal : ℝ) where
  outputLoss_pos : 0 < outputLoss
  targetDelta₀_pos : 0 < targetDelta₀
  C_pos : 0 < C
  Ctotal_pos : 0 < Ctotal
  levelCount : ℕ
  levelCount_ge_two : 2 ≤ levelCount
  levelCount_ge_four : 4 ≤ levelCount
  epsilon₂ : ℝ
  epsilon₂_eq : epsilon₂ = 1 / (levelCount : ℝ)
  epsilon₂_pos : 0 < epsilon₂
  workLoss : ℝ
  workLoss_eq : workLoss = epsilon₂
  workLoss_pos : 0 < workLoss
  workLoss_le_epsilon₂ : workLoss ≤ epsilon₂
  ten_epsilon₂_lt_half_output : 10 * epsilon₂ < outputLoss / 2
  rescaling_loss_lt_half : C * epsilon₂ < 1 / 2
  total_loss_margin :
    Ctotal * epsilon₂ ≤ (1 - C * epsilon₂) * outputLoss
  sourceDelta₀ : ℝ
  sourceDelta₀_pos : 0 < sourceDelta₀
  sourceDelta_power_cutoff :
    ∀ {sourceDelta : ℝ}, 0 < sourceDelta → sourceDelta ≤ sourceDelta₀ →
      sourceDelta ^ (1 - C * epsilon₂) ≤ targetDelta₀
  sourceDelta_le_one :
    ∀ {sourceDelta : ℝ}, 0 < sourceDelta → sourceDelta ≤ sourceDelta₀ →
      sourceDelta ≤ 1
  sourceDelta_log_cutoff :
    ∀ {sourceDelta : ℝ}, 0 < sourceDelta → sourceDelta ≤ sourceDelta₀ →
      1 ≤ Real.log (1 / sourceDelta)

namespace PureWZ2Proposition64MildRescalingScalarSchedule

/-- The rescaling exponent selected by a scalar schedule is positive (in
fact, it is strictly larger than `1/2`). -/
theorem rescalingExponent_pos
    {outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2Proposition64MildRescalingScalarSchedule
      outputLoss targetDelta₀ C Ctotal) :
    0 < 1 - C * schedule.epsilon₂ := by
  linarith [schedule.rescaling_loss_lt_half]

/-- Apply the family-free schedule to the runtime source and final scales.
The first conclusion is the target cutoff; the second is the `P7`
base-change inequality. -/
theorem power_cutoff_and_baseChange
    {outputLoss targetDelta₀ C Ctotal sourceDelta finalDelta totalLoss : ℝ}
    (schedule : PureWZ2Proposition64MildRescalingScalarSchedule
      outputLoss targetDelta₀ C Ctotal)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceCutoff : sourceDelta ≤ schedule.sourceDelta₀)
    (hsourceFinal : sourceDelta ≤ finalDelta)
    (hfinalUpper :
      finalDelta ≤ sourceDelta ^ (1 - C * schedule.epsilon₂))
    (htotalLoss :
      totalLoss ≤ (1 - C * schedule.epsilon₂) * outputLoss) :
    finalDelta ≤ targetDelta₀ ∧
      sourceDelta ^ (-totalLoss) ≤ finalDelta ^ (-outputLoss) := by
  have hpower :=
    schedule.sourceDelta_power_cutoff hsourceDelta hsourceCutoff
  exact ⟨hfinalUpper.trans hpower,
    pureWZ2Proposition64_mildRescaling_baseChange
      hsourceDelta
      (schedule.sourceDelta_le_one hsourceDelta hsourceCutoff)
      schedule.outputLoss_pos schedule.rescalingExponent_pos
      hsourceFinal hfinalUpper
      htotalLoss⟩

end PureWZ2Proposition64MildRescalingScalarSchedule

/-- Choose the complete family-independent scalar schedule after the positive
public losses and positive absolute constants have been fixed. -/
theorem exists_pureWZ2Proposition64MildRescalingScalarSchedule
    {outputLoss targetDelta₀ C Ctotal : ℝ}
    (houtputLoss : 0 < outputLoss)
    (htargetDelta₀ : 0 < targetDelta₀)
    (hC : 0 < C)
    (hCtotal : 0 < Ctotal) :
    Nonempty (PureWZ2Proposition64MildRescalingScalarSchedule
      outputLoss targetDelta₀ C Ctotal) := by
  obtain ⟨N, hN⟩ := exists_nat_gt
    (max 4
      (max (20 / outputLoss)
        (max (2 * C)
          ((Ctotal + C * outputLoss) / outputLoss))))
  have hNfourReal : (4 : ℝ) < (N : ℝ) :=
    (le_max_left 4
      (max (20 / outputLoss)
        (max (2 * C)
          ((Ctotal + C * outputLoss) / outputLoss)))).trans_lt hN
  have hNfour : 4 ≤ N := by exact_mod_cast hNfourReal.le
  have hNtwo : 2 ≤ N := by
    omega
  have hNpos : 0 < (N : ℝ) := by
    linarith
  let epsilon₂ : ℝ := 1 / (N : ℝ)
  have hepsilon₂ : 0 < epsilon₂ := by
    dsimp only [epsilon₂]
    positivity
  have hClt :
      C * epsilon₂ < 1 / 2 := by
    have hNC : 2 * C < (N : ℝ) :=
      ((le_max_left (2 * C)
          ((Ctotal + C * outputLoss) / outputLoss)).trans
        ((le_max_right (20 / outputLoss)
          (max (2 * C)
            ((Ctotal + C * outputLoss) / outputLoss))).trans
          (le_max_right 4
            (max (20 / outputLoss)
              (max (2 * C)
                ((Ctotal + C * outputLoss) / outputLoss)))))).trans_lt hN
    dsimp only [epsilon₂]
    rw [show C * (1 / (N : ℝ)) = C / (N : ℝ) by ring]
    exact (div_lt_iff₀ hNpos).2 (by linarith)
  have hNmargin :
      (Ctotal + C * outputLoss) / outputLoss < (N : ℝ) :=
    ((le_max_right (2 * C)
        ((Ctotal + C * outputLoss) / outputLoss)).trans
      ((le_max_right (20 / outputLoss)
        (max (2 * C)
          ((Ctotal + C * outputLoss) / outputLoss))).trans
        (le_max_right 4
          (max (20 / outputLoss)
            (max (2 * C)
              ((Ctotal + C * outputLoss) / outputLoss)))))).trans_lt hN
  have hmarginNumerator :
      Ctotal ≤ (N : ℝ) * outputLoss - C * outputLoss := by
    have hstrict :
        Ctotal + C * outputLoss < (N : ℝ) * outputLoss :=
      (div_lt_iff₀ houtputLoss).mp hNmargin
    linarith
  have hmargin :
      Ctotal * epsilon₂ ≤ (1 - C * epsilon₂) * outputLoss := by
    have hdiv :
        Ctotal / (N : ℝ) ≤
          ((N : ℝ) * outputLoss - C * outputLoss) / (N : ℝ) :=
      (div_le_div_iff_of_pos_right hNpos).2 hmarginNumerator
    dsimp only [epsilon₂]
    calc
      Ctotal * (1 / (N : ℝ)) = Ctotal / (N : ℝ) := by ring
      _ ≤ ((N : ℝ) * outputLoss - C * outputLoss) / (N : ℝ) := hdiv
      _ = (1 - C * (1 / (N : ℝ))) * outputLoss := by
        field_simp [hNpos.ne']
  let rescalingExponent : ℝ := 1 - C * epsilon₂
  have hrescalingExponent : 0 < rescalingExponent := by
    dsimp only [rescalingExponent]
    linarith
  let powerCutoff : ℝ :=
    targetDelta₀ ^ (1 / rescalingExponent)
  have hpowerCutoff : 0 < powerCutoff := by
    dsimp only [powerCutoff]
    positivity
  let sourceDelta₀ : ℝ :=
    min (Real.exp (-1)) powerCutoff
  have hsourceDelta₀ : 0 < sourceDelta₀ := by
    dsimp only [sourceDelta₀]
    exact lt_min (Real.exp_pos _) hpowerCutoff
  refine ⟨{
    outputLoss_pos := houtputLoss
    targetDelta₀_pos := htargetDelta₀
    C_pos := hC
    Ctotal_pos := hCtotal
    levelCount := N
    levelCount_ge_two := hNtwo
    levelCount_ge_four := hNfour
    epsilon₂ := epsilon₂
    epsilon₂_eq := rfl
    epsilon₂_pos := hepsilon₂
    workLoss := epsilon₂
    workLoss_eq := rfl
    workLoss_pos := hepsilon₂
    workLoss_le_epsilon₂ := le_rfl
    ten_epsilon₂_lt_half_output := by
      have hNoutput : 20 / outputLoss < (N : ℝ) :=
        (le_max_left (20 / outputLoss)
          (max (2 * C)
            ((Ctotal + C * outputLoss) / outputLoss))).trans
          (le_max_right 4
            (max (20 / outputLoss)
              (max (2 * C)
                ((Ctotal + C * outputLoss) / outputLoss)))) |>.trans_lt hN
      dsimp only [epsilon₂]
      have htwenty : 20 < (N : ℝ) * outputLoss :=
        (div_lt_iff₀ houtputLoss).mp hNoutput
      rw [show 10 * (1 / (N : ℝ)) = 10 / (N : ℝ) by ring]
      apply (div_lt_iff₀ hNpos).2
      nlinarith
    rescaling_loss_lt_half := hClt
    total_loss_margin := hmargin
    sourceDelta₀ := sourceDelta₀
    sourceDelta₀_pos := hsourceDelta₀
    sourceDelta_power_cutoff := ?_
    sourceDelta_le_one := ?_
    sourceDelta_log_cutoff := ?_
  }⟩
  · intro sourceDelta hsourceDelta hsourceCutoff
    have hsourcePowerCutoff : sourceDelta ≤ powerCutoff :=
      hsourceCutoff.trans (min_le_right _ _)
    have hpower :
        sourceDelta ^ rescalingExponent ≤
          powerCutoff ^ rescalingExponent :=
      Real.rpow_le_rpow hsourceDelta.le hsourcePowerCutoff
        hrescalingExponent.le
    have hcancel :
        powerCutoff ^ rescalingExponent = targetDelta₀ := by
      dsimp only [powerCutoff]
      rw [← Real.rpow_mul htargetDelta₀.le]
      have hne : rescalingExponent ≠ 0 := hrescalingExponent.ne'
      rw [show (1 / rescalingExponent) * rescalingExponent = 1 by
        field_simp]
      exact Real.rpow_one targetDelta₀
    simpa only [rescalingExponent] using hpower.trans_eq hcancel
  · intro sourceDelta hsourceDelta hsourceCutoff
    have hsourceExp :
        sourceDelta ≤ Real.exp (-1) :=
      hsourceCutoff.trans (min_le_left _ _)
    exact hsourceExp.trans <|
      (Real.exp_lt_one_iff.mpr (by norm_num)).le
  · intro sourceDelta hsourceDelta hsourceCutoff
    have hsourceExp :
        sourceDelta ≤ Real.exp (-1) :=
      hsourceCutoff.trans (min_le_left _ _)
    have hinverse :
        Real.exp 1 ≤ 1 / sourceDelta := by
      have hinv :=
        one_div_le_one_div_of_le hsourceDelta hsourceExp
      simpa [Real.exp_neg] using hinv
    have hlog :=
      Real.log_le_log (Real.exp_pos 1) hinverse
    simpa using hlog

end Kakeya.Assouad
