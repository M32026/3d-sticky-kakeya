import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CanonicalBalancingFromDensity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TerminalCoarseMultiplicity

/-!
# Proposition 6.2 four-degree regularity bound

The canonical peeling parameter is bounded by a fixed coefficient times the
fourth power of the physical logarithmic envelope. The terminal coarse
multiplicity loss is exactly `4 * A0^2`. Two elementary steps convert this
into a fixed tenth power of the direction-level count:

* `1 + log(delta⁻¹)` is at most twice the direction-level count;
* after shrinking `delta`, the remaining fixed coefficient is at most the
  square of that same count.

This module is independent of the frozen V4 statement namespace. Its geometric
inputs are only a supplied fine-cardinality logarithm bound and a fixed
schedule-depth bound.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem pureWZ2Prop62_one_add_log_inv_le_two_directionLevelCount
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1) :
    1 + Real.log delta⁻¹ ≤
      2 * (pureWZ2Prop62DirectionLevelCount delta : ℝ) := by
  have logNonnegative : 0 ≤ Real.log delta⁻¹ := by
    apply Real.log_nonneg
    exact (one_le_inv₀ deltaPos).mpr deltaLeOne
  have logTwoPos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  have logTwoLeOne : Real.log 2 ≤ 1 := by
    have bound :=
      Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ) by norm_num)
    norm_num at bound ⊢
    exact bound
  have logLeQuotient :
      Real.log delta⁻¹ ≤ Real.log delta⁻¹ / Real.log 2 := by
    rw [le_div_iff₀ logTwoPos]
    nlinarith
  have quotientLt :
      Real.log delta⁻¹ / Real.log 2 <
        (Nat.floor (Real.log delta⁻¹ / Real.log 2) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have levelCast :
      (pureWZ2Prop62DirectionLevelCount delta : ℝ) =
        (Nat.floor (Real.log delta⁻¹ / Real.log 2) : ℝ) + 1 := by
    simp [pureWZ2Prop62DirectionLevelCount, one_div]
  rw [levelCast]
  nlinarith

theorem pureWZ2Prop62_log_inv_le_directionLevelCount
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1) :
    Real.log delta⁻¹ ≤
      (pureWZ2Prop62DirectionLevelCount delta : ℝ) := by
  have logNonnegative : 0 ≤ Real.log delta⁻¹ := by
    apply Real.log_nonneg
    exact (one_le_inv₀ deltaPos).mpr deltaLeOne
  have logTwoPos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  have logTwoLeOne : Real.log 2 ≤ 1 := by
    have bound :=
      Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ) by norm_num)
    norm_num at bound ⊢
    exact bound
  have logLeQuotient :
      Real.log delta⁻¹ ≤ Real.log delta⁻¹ / Real.log 2 := by
    rw [le_div_iff₀ logTwoPos]
    nlinarith
  have quotientLt :
      Real.log delta⁻¹ / Real.log 2 <
        (Nat.floor (Real.log delta⁻¹ / Real.log 2) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have levelCast :
      (pureWZ2Prop62DirectionLevelCount delta : ℝ) =
        (Nat.floor (Real.log delta⁻¹ / Real.log 2) : ℝ) + 1 := by
    simp [pureWZ2Prop62DirectionLevelCount, one_div]
  rw [levelCast]
  exact logLeQuotient.trans quotientLt.le

/-- Fixed coefficient left after squaring the canonical `A0` bound. -/
def pureWZ2Prop62RegularityCoefficient
    (depthBound : ℕ) (logCoefficient : ℝ) : ENNReal :=
  4 *
    (ENNReal.ofReal (8 * (depthBound + 2) * 8 ^ 4 : ℝ) *
      (ENNReal.ofReal
        (2 *
          PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient
            logCoefficient)) ^ 4) ^ 2

theorem pureWZ2Prop62RegularityCoefficient_ne_top
    (depthBound : ℕ) (logCoefficient : ℝ) :
    pureWZ2Prop62RegularityCoefficient
        depthBound logCoefficient ≠ ⊤ := by
  unfold pureWZ2Prop62RegularityCoefficient
  exact ENNReal.mul_ne_top (by norm_num) <|
    ENNReal.pow_ne_top <|
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top <|
        ENNReal.pow_ne_top ENNReal.ofReal_ne_top

structure PureWZ2Prop62RegularitySmallData
    (depthBound : ℕ) (logCoefficient : ℝ) where
  delta0 : ℝ
  delta0_pos : 0 < delta0
  delta0_le_one_hundred : delta0 ≤ 1 / 100
  coefficient_le_directionLevelCount_sq :
    ∀ {delta : ℝ},
      0 < delta →
      delta ≤ delta0 →
        pureWZ2Prop62RegularityCoefficient
            depthBound logCoefficient ≤
          (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 2

theorem exists_pureWZ2Prop62RegularitySmallData
    (depthBound : ℕ) (logCoefficient : ℝ) :
    Nonempty
      (PureWZ2Prop62RegularitySmallData
        depthBound logCoefficient) := by
  let coefficient :=
    pureWZ2Prop62RegularityCoefficient depthBound logCoefficient
  rcases
      exists_delta_boundary_log_square
        coefficient.toReal ENNReal.toReal_nonneg
    with
    ⟨threshold, thresholdPos, thresholdLeOne, logarithmicBound⟩
  let delta0 := min threshold (1 / 100 : ℝ)
  refine
    ⟨{
      delta0 := delta0
      delta0_pos := lt_min thresholdPos (by norm_num)
      delta0_le_one_hundred := min_le_right _ _
      coefficient_le_directionLevelCount_sq := ?_
    }⟩
  intro delta deltaPos deltaLe
  have deltaLeThreshold : delta ≤ threshold :=
    deltaLe.trans (min_le_left _ _)
  have deltaLeOne : delta ≤ 1 :=
    deltaLeThreshold.trans thresholdLeOne
  have logarithmic := logarithmicBound delta deltaPos deltaLeThreshold
  have logNonnegative : 0 ≤ Real.log delta⁻¹ := by
    linarith [logarithmic.1]
  have coefficientLeLogSq :
      coefficient.toReal ≤ (Real.log delta⁻¹) ^ 2 := by
    calc
      coefficient.toReal ≤
          coefficient.toReal * (1 + Real.log delta⁻¹) := by
        have oneLe : 1 ≤ 1 + Real.log delta⁻¹ := by
          linarith [logarithmic.1]
        simpa using
          mul_le_mul_of_nonneg_left oneLe ENNReal.toReal_nonneg
      _ ≤ (Real.log delta⁻¹) ^ 2 := logarithmic.2
  have logLeLevel :
      Real.log delta⁻¹ ≤
        (pureWZ2Prop62DirectionLevelCount delta : ℝ) :=
    pureWZ2Prop62_log_inv_le_directionLevelCount
      deltaPos deltaLeOne
  have realBound :
      coefficient.toReal ≤
        (pureWZ2Prop62DirectionLevelCount delta : ℝ) ^ 2 :=
    coefficientLeLogSq.trans (by gcongr)
  have converted := ENNReal.ofReal_mono realBound
  rw [ENNReal.ofReal_toReal
    (pureWZ2Prop62RegularityCoefficient_ne_top
      depthBound logCoefficient)] at converted
  have levelNonnegative :
      0 ≤ (pureWZ2Prop62DirectionLevelCount delta : ℝ) := by
    positivity
  rw [ENNReal.ofReal_pow levelNonnegative] at converted
  simpa only [coefficient, ENNReal.ofReal_natCast] using converted

namespace PureWZ2Prop62RegularitySmallData

variable
    {depthBound : ℕ} {logCoefficient : ℝ}
    (small :
      PureWZ2Prop62RegularitySmallData
        depthBound logCoefficient)

theorem delta_le_one
    {delta : ℝ}
    (deltaLe : delta ≤ small.delta0) :
    delta ≤ 1 :=
  deltaLe.trans <| small.delta0_le_one_hundred.trans (by norm_num)

end PureWZ2Prop62RegularitySmallData

namespace PureWZ2Prop62PacketCellInput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput cover shading)
    (multiplicity : input.FineMultiplicityClassData)
    (parentClass : input.ParentClassData multiplicity)
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        coarse ambientConstant scaleWindow}
    (treeCleanup :
      input.ParentTreeCleanupData
        multiplicity parentClass schedule)
    (exactification :
      input.PacketCellExactificationData
        multiplicity parentClass treeCleanup)
    (parentDegree :
      input.ReferenceParentDegreeData
        multiplicity parentClass treeCleanup exactification)
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}

theorem canonicalPeelingA0_le_directionLevelCount_four
    (depthBound : ℕ)
    {logCoefficient : ℝ}
    (depthLe : schedule.levelCount ≤ depthBound)
    (deltaLeOne : delta ≤ 1)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹)) :
    (input.canonicalPeelingA0
        multiplicity parentClass treeCleanup exactification bins : ENNReal) ≤
      (ENNReal.ofReal (8 * (depthBound + 2) * 8 ^ 4 : ℝ) *
        (ENNReal.ofReal
          (2 *
            fineLogEnvelopeCoefficient logCoefficient)) ^ 4) *
        (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 4 := by
  have raw :=
    input.canonicalPeelingA0_le_logFourthENN_of_fineLog
      multiplicity parentClass treeCleanup exactification
        (bins := bins) depthBound depthLe deltaLeOne
        boundaryCoefficientLe fineLogBound
  have envelopeNonnegative :
      0 ≤ fineLogEnvelopeCoefficient logCoefficient := by
    unfold fineLogEnvelopeCoefficient
    have boundaryNonnegative : 0 ≤ wz2PaperBoundaryLogCoefficient := by
      unfold wz2PaperBoundaryLogCoefficient
      positivity
    linarith
  have logarithmBound :=
    pureWZ2Prop62_one_add_log_inv_le_two_directionLevelCount
      input.delta_pos deltaLeOne
  have envelopeBound :
      ENNReal.ofReal
          (fineLogEnvelopeCoefficient logCoefficient *
            (1 + Real.log delta⁻¹)) ≤
        ENNReal.ofReal
            (2 * fineLogEnvelopeCoefficient logCoefficient) *
          (pureWZ2Prop62DirectionLevelCount delta : ENNReal) := by
    have realBound :
        fineLogEnvelopeCoefficient logCoefficient *
              (1 + Real.log delta⁻¹) ≤
            (2 * fineLogEnvelopeCoefficient logCoefficient) *
              (pureWZ2Prop62DirectionLevelCount delta : ℝ) := by
      nlinarith
    have converted := ENNReal.ofReal_mono realBound
    rw [ENNReal.ofReal_mul
      (mul_nonneg (by norm_num) envelopeNonnegative)] at converted
    simpa only [ENNReal.ofReal_natCast] using converted
  calc
    (input.canonicalPeelingA0
          multiplicity parentClass treeCleanup exactification bins :
          ENNReal) ≤
        ENNReal.ofReal (8 * (depthBound + 2) * 8 ^ 4 : ℝ) *
          (ENNReal.ofReal
            (fineLogEnvelopeCoefficient logCoefficient *
              (1 + Real.log delta⁻¹))) ^ 4 := raw
    _ ≤
        ENNReal.ofReal (8 * (depthBound + 2) * 8 ^ 4 : ℝ) *
          (ENNReal.ofReal
              (2 * fineLogEnvelopeCoefficient logCoefficient) *
            (pureWZ2Prop62DirectionLevelCount delta : ENNReal)) ^ 4 := by
      gcongr
    _ =
        (ENNReal.ofReal (8 * (depthBound + 2) * 8 ^ 4 : ℝ) *
          (ENNReal.ofReal
            (2 * fineLogEnvelopeCoefficient logCoefficient)) ^ 4) *
          (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 4 := by
      ring

theorem terminalCoarseMultiplicityLoss_le_directionLevelCount_ten
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup exactification parentDegree bins
          (input.canonicalPeelingA0
            multiplicity parentClass treeCleanup exactification bins))
    (depthBound : ℕ)
    {logCoefficient : ℝ}
    (small :
      PureWZ2Prop62RegularitySmallData
        depthBound logCoefficient)
    (deltaLe : delta ≤ small.delta0)
    (depthLe : schedule.levelCount ≤ depthBound)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹)) :
    (core.terminalCoarseMultiplicityLoss
        input multiplicity parentClass treeCleanup exactification
          parentDegree : ENNReal) ≤
      (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 := by
  let A0 : ENNReal :=
    input.canonicalPeelingA0
      multiplicity parentClass treeCleanup exactification bins
  let coefficientRoot : ENNReal :=
    ENNReal.ofReal (8 * (depthBound + 2) * 8 ^ 4 : ℝ) *
      (ENNReal.ofReal
        (2 * fineLogEnvelopeCoefficient logCoefficient)) ^ 4
  let levelCount : ENNReal :=
    pureWZ2Prop62DirectionLevelCount delta
  have A0Bound :
      A0 ≤ coefficientRoot * levelCount ^ 4 := by
    simpa only [A0, coefficientRoot, levelCount] using
      input.canonicalPeelingA0_le_directionLevelCount_four
        multiplicity parentClass treeCleanup exactification
          depthBound depthLe (small.delta_le_one deltaLe)
          boundaryCoefficientLe fineLogBound
  have coefficientBound :
      4 * coefficientRoot ^ 2 ≤ levelCount ^ 2 := by
    simpa only [
      pureWZ2Prop62RegularityCoefficient, coefficientRoot, levelCount
    ] using
      small.coefficient_le_directionLevelCount_sq
        input.delta_pos deltaLe
  have lossEq :
      (core.terminalCoarseMultiplicityLoss
          input multiplicity parentClass treeCleanup exactification
            parentDegree : ENNReal) =
        4 * A0 ^ 2 := by
    simp [
      FourDegreeCoreAssemblyData.terminalCoarseMultiplicityLoss,
      A0, Nat.cast_mul, Nat.cast_pow
    ]
  rw [lossEq]
  calc
    (4 : ENNReal) * A0 ^ 2 ≤
        4 * (coefficientRoot * levelCount ^ 4) ^ 2 := by
      gcongr
    _ =
        (4 * coefficientRoot ^ 2) * levelCount ^ 8 := by ring
    _ ≤ levelCount ^ 2 * levelCount ^ 8 := by
      gcongr
    _ = levelCount ^ 10 := by ring

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
