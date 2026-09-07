import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalRequestedCWAConstructor

/-!
# Affine-factor bound for the direct half-offset terminal CWA

The only runtime growth in the affine carrier factor is the vertical
coefficient `2 / (d - c)`.  For the actual source,
`d - c = rho / 100` and `rho = delta ^ epsilon / 50`, so this costs exactly
one copy of `delta ^ (-epsilon)`.  The shear, slope scale, both centers, and
the final line-class dilation are uniformly bounded.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2DirectCommonYSourceAssembly
namespace TerminalGeometry
namespace PureWZ2ExternalWeightRegularizationData
namespace DirectHalfOffsetTerminalCWAScheduleData

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}

private theorem point3_norm_le_sum_abs (vector : Point3) :
    ‖vector‖ ≤ |vector 0| + |vector 1| + |vector 2| := by
  have hnorm :
      ‖vector‖ ^ 2 = vector 0 ^ 2 + vector 1 ^ 2 + vector 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    ring
  have hsquare :
      ‖vector‖ ^ 2 ≤ (|vector 0| + |vector 1| + |vector 2|) ^ 2 := by
    rw [hnorm]
    nlinarith [sq_nonneg (vector 0), sq_nonneg (vector 1),
      sq_nonneg (vector 2), abs_nonneg (vector 0), abs_nonneg (vector 1),
      abs_nonneg (vector 2), sq_abs (vector 0), sq_abs (vector 1),
      sq_abs (vector 2)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsquare

private theorem offsetProjectiveTotalLinear_norm_le
    {a b S lambda : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hS : 1 ≤ S) (hlambda : 1 ≤ lambda) (vector : Point3) :
    ‖pureWZ2OffsetProjectiveTotalLinear a b S lambda vector‖ ≤
      4 * lambda * S * ‖vector‖ := by
  have hcoord (coordinate : Fin 3) : |vector coordinate| ≤ ‖vector‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le vector coordinate
  have hlambdaNonneg : 0 ≤ lambda := le_trans (by norm_num) hlambda
  have hSNonneg : 0 ≤ S := le_trans (by norm_num) hS
  calc
    ‖pureWZ2OffsetProjectiveTotalLinear a b S lambda vector‖ ≤
        |(pureWZ2OffsetProjectiveTotalLinear a b S lambda vector) 0| +
          |(pureWZ2OffsetProjectiveTotalLinear a b S lambda vector) 1| +
          |(pureWZ2OffsetProjectiveTotalLinear a b S lambda vector) 2| :=
      point3_norm_le_sum_abs _
    _ = lambda * |vector 0 + a * vector 1| +
        |b| * |vector 1| + lambda * S * |vector 2| := by
      simp [pureWZ2OffsetProjectiveTotalLinear, point3, abs_mul,
        abs_of_nonneg hlambdaNonneg, abs_of_nonneg hSNonneg]
    _ ≤ lambda * (|vector 0| + |a| * |vector 1|) +
        |b| * |vector 1| + lambda * S * |vector 2| := by
      have hsum : |vector 0 + a * vector 1| ≤
          |vector 0| + |a| * |vector 1| := by
        simpa only [abs_mul] using abs_add_le (vector 0) (a * vector 1)
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hsum hlambdaNonneg) le_rfl) le_rfl
    _ ≤ lambda * (‖vector‖ + 1 * ‖vector‖) +
        1 * ‖vector‖ + lambda * S * ‖vector‖ := by
      have haCoord : |a| * |vector 1| ≤ 1 * ‖vector‖ :=
        mul_le_mul ha (hcoord 1) (abs_nonneg _) (by norm_num)
      have hbCoord : |b| * |vector 1| ≤ 1 * ‖vector‖ :=
        mul_le_mul hb (hcoord 1) (abs_nonneg _) (by norm_num)
      have hzeroCoord : |vector 0| + |a| * |vector 1| ≤
          ‖vector‖ + 1 * ‖vector‖ := add_le_add (hcoord 0) haCoord
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hzeroCoord hlambdaNonneg) hbCoord)
        (mul_le_mul_of_nonneg_left (hcoord 2)
          (mul_nonneg hlambdaNonneg hSNonneg))
    _ ≤ 4 * lambda * S * ‖vector‖ := by
      have hnorm : 0 ≤ ‖vector‖ := norm_nonneg _
      have hlambdaS : 0 ≤ lambda * S := mul_nonneg hlambdaNonneg hSNonneg
      have hnormS : ‖vector‖ ≤ S * ‖vector‖ :=
        le_mul_of_one_le_left hnorm hS
      have htwo : 2 * lambda * ‖vector‖ ≤
          2 * lambda * S * ‖vector‖ := by
        calc
          2 * lambda * ‖vector‖ ≤ 2 * lambda * (S * ‖vector‖) :=
            mul_le_mul_of_nonneg_left hnormS (by positivity)
          _ = 2 * lambda * S * ‖vector‖ := by ring
      have hone : ‖vector‖ ≤ lambda * S * ‖vector‖ := by
        calc
          ‖vector‖ ≤ S * ‖vector‖ := hnormS
          _ ≤ lambda * (S * ‖vector‖) :=
            le_mul_of_one_le_left (mul_nonneg hSNonneg hnorm) hlambda
          _ = lambda * S * ‖vector‖ := by ring
      calc
        lambda * (‖vector‖ + 1 * ‖vector‖) + 1 * ‖vector‖ +
            lambda * S * ‖vector‖ =
          2 * lambda * ‖vector‖ + ‖vector‖ +
            lambda * S * ‖vector‖ := by ring
        _ ≤ 2 * lambda * S * ‖vector‖ +
            lambda * S * ‖vector‖ + lambda * S * ‖vector‖ := by
          exact add_le_add (add_le_add htwo hone) le_rfl
        _ = 4 * lambda * S * ‖vector‖ := by ring

private theorem source_vertical_factor_eq :
    let source := commonSource.halfOffsetAssembly.horizontalSource
    2 / (source.d - source.c) =
      10000 * Real.rpow delta (-epsilon) := by
  dsimp only
  have hdelta : 0 < delta :=
    commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hp : 0 < Real.rpow delta epsilon := Real.rpow_pos_of_pos hdelta _
  rw [commonSource.halfOffsetAssembly.horizontalSource.length_eq,
    commonSource.halfOffsetAssembly.horizontalSource_scale,
    commonSource.halfOffsetAssembly_rho_eq_power_div]
  calc
    2 / (Real.rpow delta epsilon / 50 / 100) =
        10000 * (Real.rpow delta epsilon)⁻¹ := by
      field_simp [hp.ne']
      ring
    _ = 10000 * Real.rpow delta (-epsilon) := by
      exact congrArg (fun x : ℝ => 10000 * x)
        (Real.rpow_neg hdelta.le epsilon).symm

private theorem source_vertical_factor_one_le :
    let source := commonSource.halfOffsetAssembly.horizontalSource
    1 ≤ 2 / (source.d - source.c) := by
  dsimp only
  have hlengthPos : 0 <
      commonSource.halfOffsetAssembly.horizontalSource.d -
        commonSource.halfOffsetAssembly.horizontalSource.c :=
    sub_pos.mpr commonSource.halfOffsetAssembly.horizontalSource.ordered
  apply (le_div_iff₀ hlengthPos).2
  nlinarith [commonSource.halfOffsetAssembly.horizontalSource.left_mem,
    commonSource.halfOffsetAssembly.horizontalSource.right_mem]

/-- The operator norm of the actual total affine map has exactly one
`delta ^ (-epsilon)` loss. -/
theorem totalAffineEquiv_linear_norm_le_source_power
    (terminal : commonSource.TerminalGeometry) :
    ‖(totalAffineEquiv commonSource terminal).linear
        |>.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤
      (40000 * pureWZ2DirectHalfOffsetTerminalLambda) *
        Real.rpow delta (-epsilon) := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let equivalence := totalAffineEquiv commonSource terminal
  let linear := equivalence.linear.toContinuousLinearEquiv.toContinuousLinearMap
  let a := PureWZ2HalfOffsetHorizontalSourceData.offset source
  let b := source.m * (source.d - source.c) / 2
  let S := 2 / (source.d - source.c)
  have ha : |a| ≤ 1 :=
    (PureWZ2HalfOffsetHorizontalSourceData.offset_abs_le
      commonSource.halfOffsetAssembly_compatibility).trans (by norm_num)
  have hlengthPos : 0 < source.d - source.c := sub_pos.mpr source.ordered
  have hlength : source.d - source.c ≤ 2 := by
    linarith [source.left_mem, source.right_mem]
  have hbNonneg : 0 ≤ b := by
    dsimp only [b]
    exact div_nonneg
      (mul_nonneg source.slopeScale_pos.le hlengthPos.le) (by norm_num)
  have hb : |b| ≤ 1 := by
    rw [abs_of_nonneg hbNonneg]
    dsimp only [b]
    nlinarith [source.slopeScale_le_one]
  have hS : 1 ≤ S := by
    dsimp only [S, source]
    exact source_vertical_factor_one_le (commonSource := commonSource)
  have hlambda : 1 ≤ pureWZ2DirectHalfOffsetTerminalLambda :=
    pureWZ2DirectHalfOffsetTerminalLambda_one_le
  have hlinearApply : ∀ vector : Point3,
      linear vector = pureWZ2OffsetProjectiveTotalLinear a b S
        pureWZ2DirectHalfOffsetTerminalLambda vector := by
    intro vector
    have haffine : equivalence.linear vector =
        equivalence vector - equivalence 0 := by
      simpa using equivalence.toAffineMap.linearMap_vsub vector 0
    rw [show linear vector = equivalence.linear vector by rfl, haffine,
      totalAffineEquiv_apply, totalAffineEquiv_apply,
      totalAffineMap_sub]
    dsimp only [a, b, S, source]
    simp only [sub_zero]
  have hop : ‖linear‖ ≤
      4 * pureWZ2DirectHalfOffsetTerminalLambda * S := by
    apply ContinuousLinearMap.opNorm_le_bound _
    · positivity [pureWZ2DirectHalfOffsetTerminalLambda_pos]
    · intro vector
      rw [hlinearApply]
      exact offsetProjectiveTotalLinear_norm_le ha hb hS hlambda vector
  rw [show (40000 * pureWZ2DirectHalfOffsetTerminalLambda) *
      Real.rpow delta (-epsilon) =
        4 * pureWZ2DirectHalfOffsetTerminalLambda * S by
      rw [show S = 10000 * Real.rpow delta (-epsilon) by
        dsimp only [S, source]
        exact source_vertical_factor_eq (commonSource := commonSource)]
      ring]
  exact hop

/-- The translation part of the actual total affine map has the same single
source-power loss. -/
theorem totalAffineEquiv_zero_norm_le_source_power
    (terminal : commonSource.TerminalGeometry) :
    ‖totalAffineEquiv commonSource terminal 0‖ ≤
      (80000 * pureWZ2DirectHalfOffsetTerminalLambda) *
        Real.rpow delta (-epsilon) := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let S := 2 / (source.d - source.c)
  let image := totalAffineEquiv commonSource terminal 0
  have hsourceCenter : ∀ coordinate : Fin 3,
      |terminal.retubing.popular.popular.center coordinate| ≤ 1 := by
    intro coordinate
    simpa [wz1MildRescalingSourceWindow, Set.mem_setOf_eq] using
      terminal.retubing.popular.popular.center_mem coordinate
  have hterminalCenter : ∀ coordinate : Fin 3,
      |terminal.box.center coordinate| ≤ 1 := by
    intro coordinate
    simpa [wz1MildRescalingSourceWindow, Set.mem_setOf_eq] using
      terminal.box.center_mem coordinate
  have ha :
      |pureWZ2DirectGeometrySlope source
        (source.c + (source.d - source.c) / 2)| ≤ 1 := by
    change |source.geometrySlope
      (source.c + (source.d - source.c) / 2)| ≤ 1
    rw [show source.geometrySlope
        (source.c + (source.d - source.c) / 2) =
      PureWZ2HalfOffsetHorizontalSourceData.offset source by
        simpa only [source] using
          commonSource.halfOffsetAssembly_geometry_fixedShear _]
    exact (PureWZ2HalfOffsetHorizontalSourceData.offset_abs_le
      commonSource.halfOffsetAssembly_compatibility).trans
      (by norm_num)
  have hc : |source.c| ≤ 1 := abs_le.mpr
    ⟨source.left_mem, source.ordered.le.trans source.right_mem⟩
  have hS : 1 ≤ S := by
    dsimp only [S, source]
    exact source_vertical_factor_one_le (commonSource := commonSource)
  have hlambda : 1 ≤ pureWZ2DirectHalfOffsetTerminalLambda :=
    pureWZ2DirectHalfOffsetTerminalLambda_one_le
  have hlambdaNonneg : 0 ≤ pureWZ2DirectHalfOffsetTerminalLambda :=
    le_trans (by norm_num) hlambda
  have himage : image = point3
      (pureWZ2DirectHalfOffsetTerminalLambda *
        (-terminal.retubing.popular.popular.center 0 -
          pureWZ2DirectGeometrySlope source
              (source.c + (source.d - source.c) / 2) *
            terminal.retubing.popular.popular.center 1 -
          terminal.box.center 0))
      (-terminal.box.center 1)
      (pureWZ2DirectHalfOffsetTerminalLambda *
        (2 * (-source.c) / (source.d - source.c) - 1 -
          terminal.box.center 2)) := by
    dsimp only [image]
    rw [totalAffineEquiv_apply]
    ext coordinate
    fin_cases coordinate
    all_goals simp [source, totalAffineMap, anisotropicCenteredRescalingMap,
        anisotropicRescalingMap, pureWZ2LineClassNormalizationMap,
        pureWZ2DirectAnisotropicCenter, point3]
    all_goals ring_nf
    all_goals simp
  have hcoordZero : |image 0| ≤
      3 * pureWZ2DirectHalfOffsetTerminalLambda := by
    rw [himage, point3_coord0]
    rw [abs_mul, abs_of_nonneg hlambdaNonneg]
    have hinside :
      |-terminal.retubing.popular.popular.center 0 -
          pureWZ2DirectGeometrySlope source
              (source.c + (source.d - source.c) / 2) *
            terminal.retubing.popular.popular.center 1 -
          terminal.box.center 0| ≤ 3 := by
      have htriangle :
          |-terminal.retubing.popular.popular.center 0 -
              pureWZ2DirectGeometrySlope source
                  (source.c + (source.d - source.c) / 2) *
                terminal.retubing.popular.popular.center 1 -
              terminal.box.center 0| ≤
          |terminal.retubing.popular.popular.center 0| +
            |pureWZ2DirectGeometrySlope source
                (source.c + (source.d - source.c) / 2)| *
              |terminal.retubing.popular.popular.center 1| +
            |terminal.box.center 0| := by
        have h := abs_add_three
          (-terminal.retubing.popular.popular.center 0)
          (-(pureWZ2DirectGeometrySlope source
              (source.c + (source.d - source.c) / 2) *
            terminal.retubing.popular.popular.center 1))
          (-terminal.box.center 0)
        simpa only [sub_eq_add_neg, abs_neg, abs_mul] using h
      exact htriangle.trans <| by
        nlinarith [hsourceCenter 0, hsourceCenter 1, hterminalCenter 0,
          mul_le_mul ha (hsourceCenter 1) (abs_nonneg _) (by norm_num)]
    exact (mul_le_mul_of_nonneg_left hinside hlambdaNonneg).trans_eq
      (mul_comm _ _ )
  have hcoordOne : |image 1| ≤ 1 := by
    rw [himage, point3_coord1, abs_neg]
    exact
      hterminalCenter (1 : Fin 3)
  have hcoordTwo : |image 2| ≤
      3 * pureWZ2DirectHalfOffsetTerminalLambda * S := by
    rw [himage, point3_coord2]
    rw [abs_mul, abs_of_nonneg hlambdaNonneg]
    have hlengthPos : 0 < source.d - source.c := sub_pos.mpr source.ordered
    have hquotient : |2 * (-source.c) / (source.d - source.c)| ≤ S := by
      rw [abs_div, abs_mul, abs_of_pos hlengthPos,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      dsimp only [S]
      have hcneg : |-source.c| ≤ 1 := by simpa only [abs_neg] using hc
      have hnumerator : 2 * |-source.c| ≤ 2 := by nlinarith
      exact div_le_div_of_nonneg_right hnumerator hlengthPos.le
    have hraw :
        |2 * (-source.c) / (source.d - source.c) - 1 -
            terminal.box.center 2| ≤ S + 2 := by
      calc
        |_ - terminal.box.center 2| ≤
            |2 * (-source.c) / (source.d - source.c) - 1| +
              |terminal.box.center 2| := abs_sub _ _
        _ ≤ |2 * (-source.c) / (source.d - source.c)| + 1 +
              |terminal.box.center 2| := by
          gcongr
          exact (abs_sub _ _).trans_eq (by rw [abs_one])
        _ ≤ S + 2 := by linarith [hterminalCenter 2]
    have hrawThree :
        |2 * (-source.c) / (source.d - source.c) - 1 -
            terminal.box.center 2| ≤ 3 * S := by
      nlinarith
    exact (mul_le_mul_of_nonneg_left hrawThree hlambdaNonneg).trans_eq
      (by ring)
  calc
    ‖image‖ ≤ |image 0| + |image 1| + |image 2| :=
      point3_norm_le_sum_abs image
    _ ≤ 3 * pureWZ2DirectHalfOffsetTerminalLambda + 1 +
        3 * pureWZ2DirectHalfOffsetTerminalLambda * S := by gcongr
    _ ≤ 8 * pureWZ2DirectHalfOffsetTerminalLambda * S := by
      nlinarith [mul_nonneg hlambdaNonneg (le_trans (by norm_num) hS)]
    _ = (80000 * pureWZ2DirectHalfOffsetTerminalLambda) *
        Real.rpow delta (-epsilon) := by
      rw [show S = 10000 * Real.rpow delta (-epsilon) by
        dsimp only [S, source]
        exact source_vertical_factor_eq (commonSource := commonSource)]
      ring

/-- Runtime-independent coefficient for the literal packet homothety factor. -/
def packetFactorFiniteConstant : ENNReal :=
  ENNReal.ofReal (4000000 * pureWZ2DirectHalfOffsetTerminalLambda)

theorem packetFactorFiniteConstant_ne_top :
    packetFactorFiniteConstant ≠ ⊤ := by
  exact ENNReal.ofReal_ne_top

theorem packetFactorFiniteConstant_ne_zero :
    packetFactorFiniteConstant ≠ 0 := by
  exact ne_of_gt <| ENNReal.ofReal_pos.mpr <|
    mul_pos (by norm_num) pureWZ2DirectHalfOffsetTerminalLambda_pos

/-- The actual packet factor costs exactly one source `epsilon` power. -/
theorem packetFactor_le_source_power
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (scheduleData : DirectHalfOffsetTerminalCWAScheduleData
      (sourceScheduleConstant := sourceScheduleConstant)
      (parentLevelCount := parentLevelCount) regularization) :
    ENNReal.ofReal scheduleData.packetFactor ≤
      packetFactorFiniteConstant * Kakeya.realRpowENN delta (-epsilon) := by
  have hdelta : 0 < delta :=
    commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hdeltaOne : delta ≤ 1 :=
    commonSource.halfOffsetAssembly.cfg.extremal.delta_le_one
  have hepsilon : 0 ≤ epsilon := commonSource.lemma31.epsilon_pos.le
  have hpowerOne : 1 ≤ Real.rpow delta (-epsilon) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdeltaOne (by linarith)
  have hlinear := totalAffineEquiv_linear_norm_le_source_power
    (commonSource := commonSource) terminal
  have hzero := totalAffineEquiv_zero_norm_le_source_power
    (commonSource := commonSource) terminal
  have hlambdaPower : 1 ≤
      pureWZ2DirectHalfOffsetTerminalLambda * Real.rpow delta (-epsilon) :=
    by
      simpa only [one_mul] using
        (mul_le_mul pureWZ2DirectHalfOffsetTerminalLambda_one_le hpowerOne
          (by norm_num) pureWZ2DirectHalfOffsetTerminalLambda_pos.le)
  have hreal : scheduleData.packetFactor ≤
      (4000000 * pureWZ2DirectHalfOffsetTerminalLambda) *
        Real.rpow delta (-epsilon) := by
    unfold packetFactor
    dsimp only
    nlinarith
  calc
    ENNReal.ofReal scheduleData.packetFactor ≤
        ENNReal.ofReal
          ((4000000 * pureWZ2DirectHalfOffsetTerminalLambda) *
            Real.rpow delta (-epsilon)) := ENNReal.ofReal_mono hreal
    _ = packetFactorFiniteConstant *
        Kakeya.realRpowENN delta (-epsilon) := by
      rw [ENNReal.ofReal_mul (by
        positivity [pureWZ2DirectHalfOffsetTerminalLambda_pos])]
      rfl

/-- Runtime-independent coefficient for the cubic actual-John homothety
factor. -/
def packetFactorCubicFiniteConstant : ENNReal :=
  216 * packetFactorFiniteConstant ^ 3

theorem packetFactorCubicFiniteConstant_ne_top :
    packetFactorCubicFiniteConstant ≠ ⊤ := by
  unfold packetFactorCubicFiniteConstant
  exact ENNReal.mul_ne_top (by norm_num) <|
    ENNReal.pow_ne_top packetFactorFiniteConstant_ne_top

theorem packetFactorCubicFiniteConstant_ne_zero :
    packetFactorCubicFiniteConstant ≠ 0 := by
  unfold packetFactorCubicFiniteConstant
  exact mul_ne_zero (by norm_num) <|
    pow_ne_zero 3 packetFactorFiniteConstant_ne_zero

/-- Cubing the actual packet homothety factor triples, and only triples, its
source-scale loss.  The coordinate is retained in the interface because this
is the factor occurring in `bodyConstant coordinate`; `packetFactor` itself
is uniform over the finite schedule. -/
theorem packetFactor_cubic_le_source_power
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (scheduleData : DirectHalfOffsetTerminalCWAScheduleData
      (sourceScheduleConstant := sourceScheduleConstant)
      (parentLevelCount := parentLevelCount) regularization)
    (_coordinate : Fin scheduleData.sourceSchedule.scaleCount) :
    ENNReal.ofReal (27 * (2 * scheduleData.packetFactor - 1) ^ 3) ≤
      packetFactorCubicFiniteConstant *
        Kakeya.realRpowENN delta (-3 * epsilon) := by
  have hdelta : 0 < delta :=
    commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hpacketOne : 1 ≤ scheduleData.packetFactor := by
    unfold packetFactor
    dsimp only
    have hlinear : 0 ≤
        ‖(totalAffineEquiv commonSource terminal).linear
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ := norm_nonneg _
    have hzero : 0 ≤ ‖totalAffineEquiv commonSource terminal 0‖ := norm_nonneg _
    nlinarith
  have hpacketNonneg : 0 ≤ scheduleData.packetFactor :=
    le_trans (by norm_num) hpacketOne
  have hshiftNonneg : 0 ≤ 2 * scheduleData.packetFactor - 1 := by
    linarith
  have hshiftLe : 2 * scheduleData.packetFactor - 1 ≤
      2 * scheduleData.packetFactor := by linarith
  have hcubicReal :
      27 * (2 * scheduleData.packetFactor - 1) ^ 3 ≤
        216 * scheduleData.packetFactor ^ 3 := by
    calc
      27 * (2 * scheduleData.packetFactor - 1) ^ 3 ≤
          27 * (2 * scheduleData.packetFactor) ^ 3 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hshiftNonneg hshiftLe 3) (by norm_num)
      _ = 216 * scheduleData.packetFactor ^ 3 := by ring
  have hpacket := packetFactor_le_source_power scheduleData
  have hpowerCube :
      Kakeya.realRpowENN delta (-epsilon) ^ 3 =
        Kakeya.realRpowENN delta (-3 * epsilon) := by
    rw [show Kakeya.realRpowENN delta (-epsilon) ^ 3 =
        Kakeya.realRpowENN delta (-epsilon) *
          Kakeya.realRpowENN delta (-epsilon) *
          Kakeya.realRpowENN delta (-epsilon) by ring,
      ← realRpowENN_add hdelta, ← realRpowENN_add hdelta]
    congr 1
    ring
  calc
    ENNReal.ofReal (27 * (2 * scheduleData.packetFactor - 1) ^ 3) ≤
        ENNReal.ofReal (216 * scheduleData.packetFactor ^ 3) :=
      ENNReal.ofReal_mono hcubicReal
    _ = 216 * (ENNReal.ofReal scheduleData.packetFactor) ^ 3 := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 216),
        ENNReal.ofReal_pow hpacketNonneg]
      norm_num
    _ ≤ 216 *
        (packetFactorFiniteConstant *
          Kakeya.realRpowENN delta (-epsilon)) ^ 3 := by
      exact mul_le_mul_right (pow_le_pow_left₀ bot_le hpacket 3) 216
    _ = packetFactorCubicFiniteConstant *
        Kakeya.realRpowENN delta (-3 * epsilon) := by
      unfold packetFactorCubicFiniteConstant
      rw [mul_pow, hpowerCube]
      ring

end DirectHalfOffsetTerminalCWAScheduleData
end PureWZ2ExternalWeightRegularizationData
end TerminalGeometry
end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
