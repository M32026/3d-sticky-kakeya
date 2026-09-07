import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalConflictDegree

/-!
# Numerical closure for actual half-offset terminal conflict cleanup

This module closes the two source-Frostman radius range conditions for the
literal terminal conflict width.  It is intentionally separate from the
geometric conflict-degree proof.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

namespace TerminalGeometry

/-- The actual conflict radius always dominates the original tube radius.
This uses the terminal-scale lower bound `10 * delta ≤ targetDelta`, while
the source denominator is at most one. -/
theorem delta_le_actualConflictWidth
    (terminal : commonSource.TerminalGeometry) :
    delta ≤ actualConflictWidth commonSource terminal := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  have hdelta : 0 < delta := commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have htarget : 10 * delta ≤ terminal.targetDelta := by
    have hpre := commonSource.halfOffsetAssembly.delta_le_directPreHorizontalScale
    have hraw := commonSource.halfOffsetAssembly.directHorizontalRawTargetScale_le_target
    have hscale : (3 : ℝ) ≤ pureWZ2DirectHorizontalScale :=
      pureWZ2DirectHorizontalScale_three_le
    unfold pureWZ2DirectHorizontalRawTargetScale at hraw
    calc
      10 * delta ≤ 10 * commonSource.halfOffsetAssembly.directPreHorizontalScale := by
        gcongr
      _ ≤ 4 * pureWZ2DirectHorizontalScale *
          commonSource.halfOffsetAssembly.directPreHorizontalScale := by
        nlinarith [commonSource.halfOffsetAssembly.directPreHorizontalScale_pos]
      _ ≤ terminal.targetDelta := hraw
  have hlengthPos : 0 < source.d - source.c := sub_pos.mpr source.ordered
  have hlengthOne : source.d - source.c ≤ 1 := by
    rw [source.length_eq, commonSource.halfOffsetAssembly.horizontalSource_scale]
    linarith [commonSource.halfOffsetAssembly.rho_tiny]
  have hdenomPos : 0 < source.m * (source.d - source.c) ^ 2 := by
    exact mul_pos source.slopeScale_pos (sq_pos_of_pos hlengthPos)
  have hdenomOne : source.m * (source.d - source.c) ^ 2 ≤ 1 := by
    have hm := source.slopeScale_le_one
    nlinarith [sq_nonneg (source.d - source.c)]
  have hlambda : 1 ≤ pureWZ2DirectHalfOffsetTerminalLambda :=
    pureWZ2DirectHalfOffsetTerminalLambda_one_le
  unfold actualConflictWidth
  have htargetPos := commonSource.halfOffsetLineClassTargetDelta_pos
  have hfrac : terminal.targetDelta ≤
      (1200 * pureWZ2DirectHalfOffsetTerminalLambda * terminal.targetDelta) /
        (source.m * (source.d - source.c) ^ 2) := by
    apply (le_div_iff₀ hdenomPos).mpr
    nlinarith
  have hdeltaFrac : delta ≤
      (1200 * pureWZ2DirectHalfOffsetTerminalLambda * terminal.targetDelta) /
        (source.m * (source.d - source.c) ^ 2) := by
    nlinarith
  calc
    delta ≤ 100 *
        ((1200 * pureWZ2DirectHalfOffsetTerminalLambda * terminal.targetDelta) /
          (source.m * (source.d - source.c) ^ 2)) := by nlinarith
    _ = actualConflictWidth commonSource terminal := by
      unfold actualConflictWidth
      ring

/-- The fixed coefficient obtained by the exact half-offset denominator
identities `m ≥ rho / 50`, `d - c = rho / 100`, and
`rho = delta^epsilon / 50`. -/
def actualConflictWidthCoefficient : ℝ :=
  100 * 1200 * pureWZ2DirectHalfOffsetTerminalLambda * 100 ^ 2 * 50 ^ 3

theorem actualConflictWidthCoefficient_pos :
    0 < actualConflictWidthCoefficient := by
  unfold actualConflictWidthCoefficient
  positivity [pureWZ2DirectHalfOffsetTerminalLambda_pos]

private theorem rpow_cube
    (hdelta : 0 < delta) :
    Real.rpow delta epsilon ^ 3 = Real.rpow delta (3 * epsilon) := by
  calc
    Real.rpow delta epsilon ^ 3 = Real.rpow delta epsilon ^ (3 : ℝ) :=
      (Real.rpow_natCast _ 3).symm
    _ = Real.rpow delta (epsilon * (3 : ℝ)) :=
      (Real.rpow_mul hdelta.le epsilon 3).symm
    _ = Real.rpow delta (3 * epsilon) := by ring

/-- The exact source-power upper bound for the actual conflict width. -/
theorem actualConflictWidth_le_source_power
    (terminal : commonSource.TerminalGeometry)
    (htarget : terminal.targetDelta ≤ Real.rpow delta (1 - 2 * epsilon)) :
    actualConflictWidth commonSource terminal ≤
      actualConflictWidthCoefficient * Real.rpow delta (1 - 5 * epsilon) := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let rho := commonSource.halfOffsetAssembly.rho.1
  have hdelta : 0 < delta := commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hrho : 0 < rho := by
    dsimp [rho]
    rw [commonSource.halfOffsetAssembly_rho_eq_power_div]
    exact div_pos (Real.rpow_pos_of_pos hdelta epsilon) (by norm_num)
  have hlength : source.d - source.c = rho / 100 := by
    rw [source.length_eq, commonSource.halfOffsetAssembly.horizontalSource_scale]
  have hm : rho ≤ source.m := by
    dsimp [rho]
    calc
      commonSource.halfOffsetAssembly.rho.1 = source.source_length :=
        commonSource.halfOffsetAssembly.horizontalSource_scale.symm
      _ ≤ source.m := source.slopeScale_lower
  have hdenom : rho * (rho / 100) ^ 2 ≤
      source.m * (source.d - source.c) ^ 2 := by
    rw [hlength]
    exact mul_le_mul_of_nonneg_right hm (sq_nonneg _)
  have hdenomPos : 0 < source.m * (source.d - source.c) ^ 2 := by
    rw [hlength]
    exact mul_pos source.slopeScale_pos (sq_pos_of_pos (by positivity))
  have hnumeratorNonneg : 0 ≤
      1200 * pureWZ2DirectHalfOffsetTerminalLambda *
        Real.rpow delta (1 - 2 * epsilon) := by
    apply mul_nonneg
    · exact mul_nonneg (by norm_num)
        pureWZ2DirectHalfOffsetTerminalLambda_pos.le
    · exact Real.rpow_nonneg hdelta.le _
  have hratio :
      (1200 * pureWZ2DirectHalfOffsetTerminalLambda * terminal.targetDelta) /
          (source.m * (source.d - source.c) ^ 2) ≤
        (1200 * pureWZ2DirectHalfOffsetTerminalLambda *
          Real.rpow delta (1 - 2 * epsilon)) / (rho * (rho / 100) ^ 2) := by
    calc
      (1200 * pureWZ2DirectHalfOffsetTerminalLambda * terminal.targetDelta) /
          (source.m * (source.d - source.c) ^ 2) ≤
        (1200 * pureWZ2DirectHalfOffsetTerminalLambda *
          Real.rpow delta (1 - 2 * epsilon)) /
          (source.m * (source.d - source.c) ^ 2) := by
            apply div_le_div_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left
                htarget
                (by positivity [pureWZ2DirectHalfOffsetTerminalLambda_pos])
            · exact hdenomPos.le
      _ ≤ (1200 * pureWZ2DirectHalfOffsetTerminalLambda *
          Real.rpow delta (1 - 2 * epsilon)) / (rho * (rho / 100) ^ 2) := by
        apply div_le_div_of_nonneg_left hnumeratorNonneg
        · exact mul_pos hrho (sq_pos_of_pos (by positivity))
        · exact hdenom
  unfold actualConflictWidth
  rw [show commonSource.halfOffsetAssembly.horizontalSource = source by rfl]
  calc
    100 * (1200 * pureWZ2DirectHalfOffsetTerminalLambda * terminal.targetDelta) /
        (source.m * (source.d - source.c) ^ 2) =
      100 * ((1200 * pureWZ2DirectHalfOffsetTerminalLambda * terminal.targetDelta) /
        (source.m * (source.d - source.c) ^ 2)) := by ring
    _ ≤ 100 * ((1200 * pureWZ2DirectHalfOffsetTerminalLambda *
        Real.rpow delta (1 - 2 * epsilon)) / (rho * (rho / 100) ^ 2)) := by
      gcongr
    _ = actualConflictWidthCoefficient * Real.rpow delta (1 - 5 * epsilon) := by
      dsimp [rho]
      rw [commonSource.halfOffsetAssembly_rho_eq_power_div]
      field_simp [Real.rpow_pos_of_pos hdelta epsilon |>.ne']
      rw [rpow_cube (delta := delta) (epsilon := epsilon) hdelta]
      unfold actualConflictWidthCoefficient
      have hpowProduct : Real.rpow delta (3 * epsilon) *
          Real.rpow delta (1 - 5 * epsilon) =
          Real.rpow delta (1 - 2 * epsilon) := by
        calc
          Real.rpow delta (3 * epsilon) * Real.rpow delta (1 - 5 * epsilon) =
              Real.rpow delta ((3 * epsilon) + (1 - 5 * epsilon)) :=
            (Real.rpow_add hdelta (3 * epsilon) (1 - 5 * epsilon)).symm
          _ = Real.rpow delta (1 - 2 * epsilon) := by ring
      change 100 ^ 3 * 1200 * pureWZ2DirectHalfOffsetTerminalLambda *
          Real.rpow delta (1 - 2 * epsilon) * 50 ^ 3 = _
      rw [← hpowProduct]
      rw [show 3 * epsilon = epsilon * 3 by ring]
      change _ = _ * Real.rpow delta (1 - epsilon * 5)
      rw [show 1 - 5 * epsilon = 1 - epsilon * 5 by ring]
      ring

/-- If `epsilon < 1/5`, a runtime-independent threshold puts every actual
conflict width into the source Frostman range. -/
theorem exists_delta_for_actualConflictWidth_le_one
    (epsilon : ℝ) (hepsilonPos : 0 < epsilon)
    (hepsilon : epsilon < 1 / 5) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        0 < delta → delta ≤ delta₀ →
        ∀ terminal : commonSource.TerminalGeometry,
          actualConflictWidth commonSource terminal ≤ 1 := by
  have hgap : 0 < 1 - 5 * epsilon := by linarith
  rcases exists_delta_for_halfOffsetLineClassTargetDelta_power_upper
      epsilon hepsilonPos with
    ⟨targetDelta₀, htargetDelta₀Pos, htargetDelta₀One, htargetDelta⟩
  rcases exists_delta_constant_mul_power_le_power
      (ENNReal.ofReal actualConflictWidthCoefficient) ENNReal.ofReal_ne_top
      0 (1 - 5 * epsilon) hgap with
    ⟨widthDelta₀, hwidthDelta₀Pos, hwidthDelta₀One, hpower⟩
  refine ⟨min targetDelta₀ widthDelta₀,
    lt_min htargetDelta₀Pos hwidthDelta₀Pos,
    min_le_iff.mpr (Or.inl htargetDelta₀One), ?_⟩
  intro logExponent sigma delta commonSource hdelta hdeltaBound terminal
  have htarget := htargetDelta commonSource hdelta
    (hdeltaBound.trans (min_le_left _ _))
  have hwidth := actualConflictWidth_le_source_power commonSource terminal htarget
  have hpower' := hpower hdelta (hdeltaBound.trans (min_le_right _ _))
  have hcoefficient : 0 ≤ actualConflictWidthCoefficient :=
    actualConflictWidthCoefficient_pos.le
  have hreal : actualConflictWidthCoefficient *
      Real.rpow delta (1 - 5 * epsilon) ≤ 1 := by
    rw [Kakeya.realRpowENN, ← ENNReal.ofReal_mul hcoefficient] at hpower'
    have hpowerOne : ENNReal.ofReal
        (actualConflictWidthCoefficient * Real.rpow delta (1 - 5 * epsilon)) ≤ 1 := by
      simpa [Kakeya.realRpowENN, Real.rpow_zero] using hpower'
    exact ENNReal.ofReal_le_one.mp hpowerOne
  exact hwidth.trans hreal

/-- A single pre-runtime threshold simultaneously supplies both radius-range
inputs to the actual centered distinct-cleanup constructor. -/
theorem exists_delta_for_toDistinctCleanup
    (epsilon : ℝ) (hepsilonPos : 0 < epsilon)
    (hepsilon : epsilon < 1 / 5) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        0 < delta → delta ≤ delta₀ →
        ∀ terminal : commonSource.TerminalGeometry,
          Nonempty (PureWZ2HalfOffsetTerminalDistinctCleanupData
            commonSource terminal (actualConflictDegreeBound commonSource terminal)) := by
  rcases exists_delta_for_actualConflictWidth_le_one epsilon hepsilonPos hepsilon with
    ⟨delta₀, hdelta₀Pos, hdelta₀One, hwidth⟩
  refine ⟨delta₀, hdelta₀Pos, hdelta₀One, ?_⟩
  intro logExponent sigma delta commonSource hdelta hdeltaBound terminal
  exact toDistinctCleanup commonSource anisotropic_tube_params_inverse_cluster terminal
    (delta_le_actualConflictWidth commonSource terminal)
    (hwidth commonSource hdelta hdeltaBound terminal)

end TerminalGeometry

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
