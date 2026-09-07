import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CanonicalBalancingFromDensity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4SchedulePowerCore
import Mathlib.Tactic

/-!
# Generic scalar threshold for the four-degree packet construction

This module contains only the packet-cell and scalar part of the fourth
Proposition 6.2 lemma.  In particular, it does not import the frozen V4
statement or any metric-parent output record.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

open PureWZ2Prop62PacketCellInput

/-- The packet-density exponent spends one copy of `eta` beyond the input
density exponent. -/
def pureWZ2Prop62FourDegreePacketDensityExponent (D : ℕ) : ℕ :=
  D + 1

/-- The prebalancing loss spends half of `eta`. -/
def pureWZ2Prop62FourDegreePrebalanceLossExponent (eta : ℝ) : ℝ :=
  eta / 2

/-- The fixed regularity exponent in the fourth paper lemma. -/
def pureWZ2Prop62FourDegreePolylogExponent : ℕ :=
  10

/-- Fixed coefficient before the seventh logarithmic power in the terminal
parent-CWA structural loss. -/
def pureWZ2Prop62FourDegreeParentStructuralCoefficient
    (depthBound : ℕ) (tubeMassConstant : ENNReal) : ENNReal :=
  (2 : ENNReal) ^ depthBound *
    ENNReal.ofReal (8 * (depthBound + 2) * 8 ^ 4 : ℝ) *
    (8 * tubeMassConstant)

theorem pureWZ2Prop62FourDegreeParentStructuralCoefficient_ne_top
    (depthBound : ℕ) {tubeMassConstant : ENNReal}
    (tubeMassConstant_ne_top : tubeMassConstant ≠ ⊤) :
    pureWZ2Prop62FourDegreeParentStructuralCoefficient
        depthBound tubeMassConstant ≠ ⊤ := by
  unfold pureWZ2Prop62FourDegreeParentStructuralCoefficient
  exact
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
        ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top (by norm_num) tubeMassConstant_ne_top)

/-- Fixed coefficient before the eighth logarithmic power in the final
coarse-multiplicity regularity. -/
def pureWZ2Prop62FourDegreeRegularityCoefficient
    (depthBound : ℕ) (logCoefficient : ℝ) : ENNReal :=
  4 *
    (ENNReal.ofReal (8 * (depthBound + 2) * 8 ^ 4 : ℝ)) ^ 2 *
    (ENNReal.ofReal
      (2 *
        PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient
          logCoefficient)) ^ 8

theorem pureWZ2Prop62FourDegreeRegularityCoefficient_ne_top
    (depthBound : ℕ) (logCoefficient : ℝ) :
    pureWZ2Prop62FourDegreeRegularityCoefficient
        depthBound logCoefficient ≠ ⊤ := by
  unfold pureWZ2Prop62FourDegreeRegularityCoefficient
  exact
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (by norm_num)
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

theorem pureWZ2Prop62FourDegreeDirectionLogEnvelope_le
    {delta logCoefficient : ℝ}
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    (logCoefficientOne : 1 ≤ logCoefficient) :
    ENNReal.ofReal
        (PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient
            logCoefficient *
          (1 + Real.log delta⁻¹)) ≤
      ENNReal.ofReal
          (2 *
            PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient
              logCoefficient) *
        (pureWZ2Prop62DirectionLevelCount delta : ENNReal) := by
  have logTwoPos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  have logInvNonnegative : 0 ≤ Real.log delta⁻¹ := by
    apply Real.log_nonneg
    exact (one_le_inv₀ deltaPos).mpr deltaLeOne
  have quotientNonnegative :
      0 ≤ Real.log delta⁻¹ / Real.log 2 :=
    div_nonneg logInvNonnegative logTwoPos.le
  have quotientLt :
      Real.log delta⁻¹ / Real.log 2 <
        (pureWZ2Prop62DirectionLevelCount delta : ℝ) := by
    simpa only [
      pureWZ2Prop62DirectionLevelCount,
      one_div, Nat.cast_add, Nat.cast_one
    ] using
      (Nat.lt_floor_add_one
        (Real.log delta⁻¹ / Real.log 2))
  have logTwoLeOne : Real.log 2 ≤ 1 := by
    exact (Real.log_two_lt_d9.trans (by norm_num)).le
  have logInvLe :
      Real.log delta⁻¹ ≤
        (pureWZ2Prop62DirectionLevelCount delta : ℝ) := by
    calc
      Real.log delta⁻¹ =
          (Real.log delta⁻¹ / Real.log 2) * Real.log 2 := by
        field_simp [logTwoPos.ne']
      _ ≤
          (pureWZ2Prop62DirectionLevelCount delta : ℝ) *
            Real.log 2 := by
        gcongr
      _ ≤
          (pureWZ2Prop62DirectionLevelCount delta : ℝ) * 1 := by
        gcongr
      _ = _ := by ring
  have levelOne :
      (1 : ℝ) ≤
        (pureWZ2Prop62DirectionLevelCount delta : ℝ) := by
    unfold pureWZ2Prop62DirectionLevelCount
    norm_num
  have realEnvelope :
      PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient
          logCoefficient *
          (1 + Real.log delta⁻¹) ≤
        (2 *
          PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient
            logCoefficient) *
          (pureWZ2Prop62DirectionLevelCount delta : ℝ) := by
    have coefficientNonnegative :
        0 ≤
          PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient
            logCoefficient :=
      zero_le_one.trans <|
        PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient_one_le
          logCoefficientOne
    have envelopeLe :
        1 + Real.log delta⁻¹ ≤
          2 * (pureWZ2Prop62DirectionLevelCount delta : ℝ) := by
      nlinarith
    calc
      PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient
            logCoefficient *
          (1 + Real.log delta⁻¹) ≤
        PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient
            logCoefficient *
          (2 * (pureWZ2Prop62DirectionLevelCount delta : ℝ)) :=
        mul_le_mul_of_nonneg_left envelopeLe coefficientNonnegative
      _ =
        (2 *
          PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient
            logCoefficient) *
          (pureWZ2Prop62DirectionLevelCount delta : ℝ) := by
        ring
  have converted := ENNReal.ofReal_mono realEnvelope
  have rightFactorNonnegative :
      0 ≤
        (2 : ℝ) *
          PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient
            logCoefficient := by
    have coefficientNonnegative :
        0 ≤
          PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient
            logCoefficient :=
      zero_le_one.trans <|
        PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient_one_le
          logCoefficientOne
    exact mul_nonneg (by norm_num) coefficientNonnegative
  rw [ENNReal.ofReal_mul rightFactorNonnegative] at converted
  simpa only [ENNReal.ofReal_natCast] using converted

/-- All scalar smallness data needed after fixing `D`, `B`, `eta`, the
fine-cardinality logarithmic coefficient, and the tube-mass constant. -/
structure PureWZ2Prop62FourDegreeThresholdCoreData
    (D B : ℕ) (eta logCoefficient : ℝ)
    (tubeMassConstant : ENNReal) where
  logCoefficient_one : 1 ≤ logCoefficient
  packet_exponent_gap :
    (D : ℝ) * eta <
      ((pureWZ2Prop62FourDegreePacketDensityExponent D : ℕ) : ℝ) * eta
  schedulePower :
    PureWZ2Prop62MetricParentsV4SchedulePowerCertificate D B eta
  delta0 : ℝ
  delta0_pos : 0 < delta0
  delta0_le_one_hundred : delta0 ≤ 1 / 100
  schedule_small :
    ∀ {delta : ℝ},
      0 < delta →
      delta ≤ delta0 →
        delta ≤ schedulePower.delta0
  prebalance_small :
    ∀ {delta : ℝ},
      0 < delta →
      delta ≤ delta0 →
        PureWZ2Prop62PacketCellInput.PrebalanceSmallDataOfFineLog
          delta
          (pureWZ2Prop62MetricParentsV4FourDegreeDepthBound D B eta)
          ((D : ℝ) * eta)
          (pureWZ2Prop62FourDegreePrebalanceLossExponent eta)
          logCoefficient
  packet_density_small :
    ∀ {delta : ℝ},
      0 < delta →
      delta ≤ delta0 →
        delta ≤
          PureWZ2Prop62PacketCellInput.FourDegreeCoreAssemblyData.canonicalPacketDensityThresholdOfFineLog
              (pureWZ2Prop62MetricParentsV4FourDegreeDepthBound D B eta)
              ((D : ℝ) * eta)
              (((pureWZ2Prop62FourDegreePacketDensityExponent D : ℕ) : ℝ) *
                eta)
              logCoefficient logCoefficient_one packet_exponent_gap
  mass_retention_small :
    ∀ {delta : ℝ},
      0 < delta →
      delta ≤ delta0 →
        delta ≤
          PureWZ2Prop62PacketCellInput.FourDegreeCoreAssemblyData.canonicalMassRetentionThresholdOfFineLog
              (pureWZ2Prop62MetricParentsV4FourDegreeDepthBound D B eta)
              logCoefficient
  parent_structural_coefficient :
    ∀ {delta : ℝ},
      0 < delta →
      delta ≤ delta0 →
        pureWZ2Prop62FourDegreeParentStructuralCoefficient
              (pureWZ2Prop62MetricParentsV4FourDegreeDepthBound D B eta)
              tubeMassConstant *
            (ENNReal.ofReal
              (PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient
                  logCoefficient *
                (1 + Real.log delta⁻¹))) ^ 7 ≤
          Kakeya.realRpowENN delta (-3 * eta)
  regularity_coefficient :
    ∀ {delta : ℝ},
      0 < delta →
      delta ≤ delta0 →
        pureWZ2Prop62FourDegreeRegularityCoefficient
            (pureWZ2Prop62MetricParentsV4FourDegreeDepthBound D B eta)
            logCoefficient ≤
          (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 2

theorem exists_pureWZ2Prop62FourDegreeThresholdCoreData
    (D B : ℕ) (eta logCoefficient : ℝ)
    (tubeMassConstant : ENNReal)
    (eta_pos : 0 < eta)
    (packetExponent_lt_one :
      ((pureWZ2Prop62FourDegreePacketDensityExponent D : ℕ) : ℝ) *
          eta < 1)
    (logCoefficientOne : 1 ≤ logCoefficient)
    (tubeMassConstant_ne_top : tubeMassConstant ≠ ⊤) :
    Nonempty
      (PureWZ2Prop62FourDegreeThresholdCoreData
        D B eta logCoefficient tubeMassConstant) := by
  let depthBound :=
    pureWZ2Prop62MetricParentsV4FourDegreeDepthBound D B eta
  let densityExponent : ℝ := (D : ℝ) * eta
  let lossExponent : ℝ :=
    pureWZ2Prop62FourDegreePrebalanceLossExponent eta
  let packetExponent : ℝ :=
    ((pureWZ2Prop62FourDegreePacketDensityExponent D : ℕ) : ℝ) * eta
  have lossExponentPos : 0 < lossExponent := by
    dsimp only [lossExponent,
      pureWZ2Prop62FourDegreePrebalanceLossExponent]
    positivity
  have balancingExponentGap :
      densityExponent + lossExponent < 1 := by
    dsimp only [densityExponent, lossExponent,
      pureWZ2Prop62FourDegreePrebalanceLossExponent]
    simp only [pureWZ2Prop62FourDegreePacketDensityExponent,
      Nat.cast_add, Nat.cast_one] at packetExponent_lt_one
    nlinarith
  have packetExponentGap :
      densityExponent < packetExponent := by
    dsimp only [densityExponent, packetExponent]
    unfold pureWZ2Prop62FourDegreePacketDensityExponent
    push_cast
    nlinarith
  let schedulePower :=
    Classical.choice <|
      exists_pureWZ2Prop62MetricParentsV4SchedulePowerCertificate
        D B eta eta_pos
  let prebalanceThreshold :=
    PureWZ2Prop62PacketCellInput.prebalanceSmallThresholdOfFineLog
      depthBound densityExponent lossExponent logCoefficient
        lossExponentPos balancingExponentGap logCoefficientOne
  let packetThreshold :=
    PureWZ2Prop62PacketCellInput.FourDegreeCoreAssemblyData.canonicalPacketDensityThresholdOfFineLog
        depthBound densityExponent packetExponent logCoefficient
          logCoefficientOne packetExponentGap
  let massThreshold :=
    PureWZ2Prop62PacketCellInput.FourDegreeCoreAssemblyData.canonicalMassRetentionThresholdOfFineLog
        depthBound logCoefficient
  let parentCoefficient :=
    pureWZ2Prop62FourDegreeParentStructuralCoefficient
      depthBound tubeMassConstant
  rcases
      exists_delta_C_pow_log_absorbed_ennreal
        parentCoefficient
        (pureWZ2Prop62FourDegreeParentStructuralCoefficient_ne_top
          depthBound tubeMassConstant_ne_top)
        (PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient
          logCoefficient)
        (zero_le_one.trans <|
          PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient_one_le
            logCoefficientOne)
        (show 0 < 3 * eta by positivity)
        (n := 7) (by norm_num)
    with
    ⟨parentThreshold, parentThresholdPos, _parentThresholdLeOne,
      parentAbsorption⟩
  let regularityCoefficient :=
    pureWZ2Prop62FourDegreeRegularityCoefficient
      depthBound logCoefficient
  rcases
      exists_delta_boundary_log_square
        regularityCoefficient.toReal ENNReal.toReal_nonneg
    with
    ⟨regularityThreshold, regularityThresholdPos,
      regularityThresholdLeOne, regularityAbsorption⟩
  let delta0 :=
    min schedulePower.delta0 <|
      min prebalanceThreshold <|
        min packetThreshold <|
          min massThreshold <|
            min parentThreshold regularityThreshold
  have delta0_pos : 0 < delta0 := by
    dsimp only [delta0]
    exact
      lt_min schedulePower.delta0_pos <|
        lt_min
          (Classical.choose_spec <|
            PureWZ2Prop62PacketCellInput.exists_prebalanceSmallThresholdOfFineLog
                depthBound densityExponent lossExponent logCoefficient
                  lossExponentPos balancingExponentGap
                  logCoefficientOne).1 <|
          lt_min
            (Classical.choose_spec <|
              PureWZ2Prop62PacketCellInput.FourDegreeCoreAssemblyData.exists_canonicalPacketDensityThresholdOfFineLog
                  depthBound densityExponent packetExponent logCoefficient
                    logCoefficientOne packetExponentGap).1 <|
            lt_min
              (Classical.choose_spec <|
                PureWZ2Prop62PacketCellInput.FourDegreeCoreAssemblyData.exists_canonicalMassRetentionThresholdOfFineLog
                    depthBound logCoefficient).1 <|
              lt_min parentThresholdPos regularityThresholdPos
  refine
    ⟨{
      logCoefficient_one := logCoefficientOne
      packet_exponent_gap := by
        simpa only [densityExponent, packetExponent] using packetExponentGap
      schedulePower := schedulePower
      delta0 := delta0
      delta0_pos := delta0_pos
      delta0_le_one_hundred :=
        (min_le_left _ _).trans schedulePower.delta0_le_one_hundred
      schedule_small := ?_
      prebalance_small := ?_
      packet_density_small := ?_
      mass_retention_small := ?_
      parent_structural_coefficient := ?_
      regularity_coefficient := ?_
    }⟩
  · intro delta _deltaPos deltaLe
    exact deltaLe.trans (min_le_left _ _)
  · intro delta deltaPos deltaLe
    apply
      PureWZ2Prop62PacketCellInput.prebalanceSmallDataOfFineLog_of_smallDelta
          depthBound densityExponent lossExponent logCoefficient
            lossExponentPos balancingExponentGap logCoefficientOne
          deltaPos
    exact
      deltaLe.trans <|
        (min_le_right _ _).trans <|
          min_le_left _ _
  · intro delta _deltaPos deltaLe
    exact
      deltaLe.trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            min_le_left _ _
  · intro delta _deltaPos deltaLe
    exact
      deltaLe.trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans <|
              min_le_left _ _
  · intro delta deltaPos deltaLe
    have absorbed :=
      parentAbsorption delta deltaPos <|
        deltaLe.trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans <|
              (min_le_right _ _).trans <|
                (min_le_right _ _).trans <|
                  min_le_left _ _
    simpa only [parentCoefficient, depthBound] using
      (show
        parentCoefficient *
              (ENNReal.ofReal
                (PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient
                    logCoefficient *
                  (1 + Real.log delta⁻¹))) ^ 7 ≤
            Kakeya.realRpowENN delta (-3 * eta) by
          convert absorbed using 1 <;> ring)
  · intro delta deltaPos deltaLe
    have deltaLeRegularity :
        delta ≤ regularityThreshold :=
      deltaLe.trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans <|
              (min_le_right _ _).trans <|
                min_le_right _ _
    have logData :=
      regularityAbsorption delta deltaPos deltaLeRegularity
    have deltaLeOne :
        delta ≤ 1 :=
      deltaLeRegularity.trans regularityThresholdLeOne
    have logNonnegative : 0 ≤ Real.log delta⁻¹ := by
      linarith [logData.1]
    have coefficientFinite :
        regularityCoefficient ≠ ⊤ := by
      exact
        pureWZ2Prop62FourDegreeRegularityCoefficient_ne_top
          depthBound logCoefficient
    have coefficientReal :
        regularityCoefficient.toReal ≤
          (Real.log delta⁻¹) ^ 2 := by
      calc
        regularityCoefficient.toReal ≤
            regularityCoefficient.toReal *
              (1 + Real.log delta⁻¹) := by
          nlinarith [ENNReal.toReal_nonneg (a := regularityCoefficient)]
        _ ≤ (Real.log delta⁻¹) ^ 2 := logData.2
    have levelLog :
        Real.log delta⁻¹ ≤
          (pureWZ2Prop62DirectionLevelCount delta : ℝ) := by
      have logTwoPos : 0 < Real.log 2 :=
        Real.log_pos (by norm_num)
      have quotientLt :
          Real.log delta⁻¹ / Real.log 2 <
            (pureWZ2Prop62DirectionLevelCount delta : ℝ) := by
        simpa only [
          pureWZ2Prop62DirectionLevelCount,
          one_div, Nat.cast_add, Nat.cast_one
        ] using
          (Nat.lt_floor_add_one
            (Real.log delta⁻¹ / Real.log 2))
      calc
        Real.log delta⁻¹ =
            (Real.log delta⁻¹ / Real.log 2) * Real.log 2 := by
          field_simp [logTwoPos.ne']
        _ ≤
            (pureWZ2Prop62DirectionLevelCount delta : ℝ) *
              Real.log 2 := by
          gcongr
        _ ≤
            (pureWZ2Prop62DirectionLevelCount delta : ℝ) := by
          have logTwoLeOne : Real.log 2 ≤ 1 :=
            (Real.log_two_lt_d9.trans (by norm_num)).le
          nlinarith
    have coefficientRealLeLevel :
        regularityCoefficient.toReal ≤
          (pureWZ2Prop62DirectionLevelCount delta : ℝ) ^ 2 := by
      exact coefficientReal.trans <| by
        nlinarith
    calc
      regularityCoefficient =
          ENNReal.ofReal regularityCoefficient.toReal :=
        (ENNReal.ofReal_toReal coefficientFinite).symm
      _ ≤
          ENNReal.ofReal
            ((pureWZ2Prop62DirectionLevelCount delta : ℝ) ^ 2) :=
        ENNReal.ofReal_mono coefficientRealLeLevel
      _ =
          (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 2 := by
        rw [ENNReal.ofReal_pow (by positivity)]
        simp

noncomputable def pureWZ2Prop62FourDegreeThresholdCore
    (D B : ℕ) (eta logCoefficient : ℝ)
    (tubeMassConstant : ENNReal)
    (eta_pos : 0 < eta)
    (packetExponent_lt_one :
      ((pureWZ2Prop62FourDegreePacketDensityExponent D : ℕ) : ℝ) *
          eta < 1)
    (logCoefficientOne : 1 ≤ logCoefficient)
    (tubeMassConstant_ne_top : tubeMassConstant ≠ ⊤) :
    PureWZ2Prop62FourDegreeThresholdCoreData
      D B eta logCoefficient tubeMassConstant :=
  Classical.choice <|
    exists_pureWZ2Prop62FourDegreeThresholdCoreData
      D B eta logCoefficient tubeMassConstant eta_pos
        packetExponent_lt_one logCoefficientOne tubeMassConstant_ne_top

namespace PureWZ2Prop62FourDegreeThresholdCoreData

variable
    {D B : ℕ} {eta logCoefficient : ℝ}
    {tubeMassConstant : ENNReal}
    (threshold :
      PureWZ2Prop62FourDegreeThresholdCoreData
        D B eta logCoefficient tubeMassConstant)

include threshold

theorem delta_lt_one
    {delta : ℝ}
    (deltaLe : delta ≤ threshold.delta0) :
    delta < 1 :=
  deltaLe.trans_lt <|
    threshold.delta0_le_one_hundred.trans_lt (by norm_num)

theorem schedule_delta_le
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaLe : delta ≤ threshold.delta0) :
    delta ≤ threshold.schedulePower.delta0 :=
  threshold.schedule_small
    deltaPos
    deltaLe

theorem terminalParentStructuralAbsorption
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
      input.ParentTreeCleanupData multiplicity parentClass schedule)
    (exactification :
      input.PacketCellExactificationData
        multiplicity parentClass treeCleanup)
    (parentDegree :
      input.ReferenceParentDegreeData
        multiplicity parentClass treeCleanup exactification)
    (bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges)
    (depthLe :
      schedule.levelCount ≤
        pureWZ2Prop62MetricParentsV4FourDegreeDepthBound D B eta)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹))
    (deltaPos : 0 < delta)
    (deltaLe : delta ≤ threshold.delta0) :
    (((2 ^ schedule.levelCount *
          input.canonicalPeelingA0
            multiplicity parentClass treeCleanup exactification bins :
            ℕ) : ENNReal) *
        (2 *
          ((multiplicity.binCount : ENNReal) *
            parentClass.weightBinCount *
            parentClass.fiberBinCount) *
          tubeMassConstant)) ≤
      Kakeya.realRpowENN delta (-3 * eta) := by
  let depthBound :=
    pureWZ2Prop62MetricParentsV4FourDegreeDepthBound D B eta
  let envelope :=
    ENNReal.ofReal
      (PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient
          logCoefficient *
        (1 + Real.log delta⁻¹))
  let depthCoefficient :=
    ENNReal.ofReal (8 * (depthBound + 2) * 8 ^ 4 : ℝ)
  have levelPower :
      (2 : ENNReal) ^ schedule.levelCount ≤
        (2 : ENNReal) ^ depthBound :=
    pow_le_pow_right₀ (by norm_num) depthLe
  have A0Bound :
      (input.canonicalPeelingA0
          multiplicity parentClass treeCleanup exactification bins :
          ENNReal) ≤
        depthCoefficient * envelope ^ 4 := by
    simpa only [depthBound, depthCoefficient, envelope] using
      input.canonicalPeelingA0_le_logFourthENN_of_fineLog
        multiplicity parentClass treeCleanup exactification
          (bins := bins) depthBound depthLe
          (threshold.delta_lt_one deltaLe).le
          boundaryCoefficientLe fineLogBound
  have selectionBound :
      (multiplicity.binCount : ENNReal) *
          parentClass.weightBinCount *
          parentClass.fiberBinCount ≤
        4 * envelope ^ 3 := by
    simpa only [envelope] using
      input.prebalanceDyadicProduct_le_logCube_of_fineLog
        multiplicity parentClass
          (threshold.delta_lt_one deltaLe).le
          boundaryCoefficientLe fineLogBound
  calc
    (((2 ^ schedule.levelCount *
          input.canonicalPeelingA0
            multiplicity parentClass treeCleanup exactification bins :
            ℕ) : ENNReal) *
        (2 *
          ((multiplicity.binCount : ENNReal) *
            parentClass.weightBinCount *
            parentClass.fiberBinCount) *
          tubeMassConstant)) =
        ((2 : ENNReal) ^ schedule.levelCount *
          (input.canonicalPeelingA0
            multiplicity parentClass treeCleanup exactification bins :
            ENNReal)) *
          (2 *
            ((multiplicity.binCount : ENNReal) *
              parentClass.weightBinCount *
              parentClass.fiberBinCount) *
            tubeMassConstant) := by
      norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤
        ((2 : ENNReal) ^ depthBound *
          (depthCoefficient * envelope ^ 4)) *
          (2 * (4 * envelope ^ 3) * tubeMassConstant) := by
      gcongr
    _ =
        pureWZ2Prop62FourDegreeParentStructuralCoefficient
            depthBound tubeMassConstant *
          envelope ^ 7 := by
      unfold pureWZ2Prop62FourDegreeParentStructuralCoefficient
      ring
    _ ≤ Kakeya.realRpowENN delta (-3 * eta) := by
      simpa only [depthBound, envelope] using
        threshold.parent_structural_coefficient deltaPos deltaLe

theorem terminalCoarseMultiplicityLoss_le_logTen
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
      input.ParentTreeCleanupData multiplicity parentClass schedule)
    (exactification :
      input.PacketCellExactificationData
        multiplicity parentClass treeCleanup)
    (parentDegree :
      input.ReferenceParentDegreeData
        multiplicity parentClass treeCleanup exactification)
    (bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges)
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup exactification parentDegree bins
          (input.canonicalPeelingA0
            multiplicity parentClass treeCleanup exactification bins))
    (logCoefficientOne : 1 ≤ logCoefficient)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹))
    (depthLe :
      schedule.levelCount ≤
        pureWZ2Prop62MetricParentsV4FourDegreeDepthBound D B eta)
    (deltaPos : 0 < delta)
    (deltaLe : delta ≤ threshold.delta0) :
    (core.terminalCoarseMultiplicityLoss
        input multiplicity parentClass treeCleanup
          exactification parentDegree : ENNReal) ≤
      (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^
        pureWZ2Prop62FourDegreePolylogExponent := by
  let depthBound :=
    pureWZ2Prop62MetricParentsV4FourDegreeDepthBound D B eta
  let envelope :=
    ENNReal.ofReal
      (fineLogEnvelopeCoefficient logCoefficient *
        (1 + Real.log delta⁻¹))
  let level : ENNReal :=
    pureWZ2Prop62DirectionLevelCount delta
  let depthCoefficient :=
    ENNReal.ofReal (8 * (depthBound + 2) * 8 ^ 4 : ℝ)
  let envelopeCoefficient :=
    ENNReal.ofReal
      (2 *
        PureWZ2Prop62PacketCellInput.fineLogEnvelopeCoefficient
          logCoefficient)
  have A0Bound :
      (input.canonicalPeelingA0
          multiplicity parentClass treeCleanup exactification bins :
          ENNReal) ≤
        depthCoefficient * envelope ^ 4 := by
    simpa only [depthBound, depthCoefficient, envelope] using
      input.canonicalPeelingA0_le_logFourthENN_of_fineLog
        multiplicity parentClass treeCleanup exactification
          (bins := bins) depthBound depthLe
          (threshold.delta_lt_one deltaLe).le
          boundaryCoefficientLe fineLogBound
  have envelopeBound :
      envelope ≤ envelopeCoefficient * level := by
    simpa only [envelope, envelopeCoefficient, level] using
      pureWZ2Prop62FourDegreeDirectionLogEnvelope_le
        deltaPos (threshold.delta_lt_one deltaLe).le
          logCoefficientOne
  have coefficientBound :
      pureWZ2Prop62FourDegreeRegularityCoefficient
          depthBound logCoefficient ≤ level ^ 2 := by
    simpa only [depthBound, level] using
      threshold.regularity_coefficient deltaPos deltaLe
  simp only [
    PureWZ2Prop62PacketCellInput.FourDegreeCoreAssemblyData.terminalCoarseMultiplicityLoss,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat
  ]
  calc
    (4 : ENNReal) *
          (input.canonicalPeelingA0
            multiplicity parentClass treeCleanup exactification bins :
            ENNReal) ^ 2 ≤
        4 * (depthCoefficient * envelope ^ 4) ^ 2 := by
      gcongr
    _ ≤
        4 *
          (depthCoefficient * (envelopeCoefficient * level) ^ 4) ^ 2 := by
      gcongr
    _ =
        pureWZ2Prop62FourDegreeRegularityCoefficient
            depthBound logCoefficient *
          level ^ 8 := by
      unfold pureWZ2Prop62FourDegreeRegularityCoefficient
      dsimp only [depthCoefficient, envelopeCoefficient]
      ring
    _ ≤ level ^ 2 * level ^ 8 := by
      gcongr
    _ = level ^ pureWZ2Prop62FourDegreePolylogExponent := by
      unfold pureWZ2Prop62FourDegreePolylogExponent
      ring

end PureWZ2Prop62FourDegreeThresholdCoreData

end Kakeya.Assouad

end
