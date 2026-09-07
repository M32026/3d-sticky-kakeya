import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CanonicalFourDegreeOutput
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreePrefix
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PrebalanceParentDegree

/-!
# Proposition 6.2: canonical balancing from source density

This module combines the pre-balancing parent-degree floor with the
fixed-quota lower-tail argument.  The source density and the complete metric
family are unchanged throughout this bridge.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

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
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup exactification parentDegree bins
          (input.canonicalPeelingA0
            multiplicity parentClass treeCleanup exactification bins))

namespace FourDegreeCoreAssemblyData

def canonicalPacketDensityCoefficient
    (depthBound : ℕ) : ENNReal :=
  512 *
    (ENNReal.ofReal
      (8 * (depthBound + 2) * 8 ^ 4 : ℝ)) ^ 3

theorem canonicalPacketDensityCoefficient_ne_top
    (depthBound : ℕ) :
    canonicalPacketDensityCoefficient depthBound ≠ ⊤ := by
  unfold canonicalPacketDensityCoefficient
  exact ENNReal.mul_ne_top (by norm_num) <|
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top

theorem canonicalPacketDensityLoss_le_logFifteen
    (depthBound : ℕ)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4)
    (depthLe : schedule.levelCount ≤ depthBound)
    (deltaLtOne : delta < 1) :
    (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree : ENNReal) *
        input.prebalancePacketDensityLoss multiplicity parentClass *
        (input.canonicalPeelingA0
          multiplicity parentClass treeCleanup exactification bins :
            ENNReal) ≤
      canonicalPacketDensityCoefficient depthBound *
        (ENNReal.ofReal
          (prebalanceLogCoefficient *
            (1 + Real.log delta⁻¹))) ^ 15 := by
  let A0 : ENNReal :=
    input.canonicalPeelingA0
      multiplicity parentClass treeCleanup exactification bins
  let envelope : ENNReal :=
    ENNReal.ofReal
      (prebalanceLogCoefficient * (1 + Real.log delta⁻¹))
  let depthCoefficient : ENNReal :=
    ENNReal.ofReal (8 * (depthBound + 2) * 8 ^ 4 : ℝ)
  have packetLoss :
      input.prebalancePacketDensityLoss multiplicity parentClass ≤
        64 * envelope ^ 3 := by
    simpa only [envelope] using
      input.prebalancePacketDensityLoss_le_logCube
        multiplicity parentClass input.delta_pos deltaLtOne.le
          fineNonempty fineDistinct fineBoundedBase
  have A0Bound :
      A0 ≤ depthCoefficient * envelope ^ 4 := by
    simpa only [A0, depthCoefficient, envelope] using
      input.canonicalPeelingA0_le_prebalanceLogFourthENN
        multiplicity parentClass treeCleanup exactification
          depthBound depthLe input.delta_pos deltaLtOne.le
          fineNonempty fineDistinct fineBoundedBase
  have degreeLossEq :
      (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree : ENNReal) =
        8 * A0 ^ 2 := by
    simp [
      FourDegreeCoreAssemblyData.balancingDegreeLoss,
      FourDegreeCoreAssemblyData.balancingRateLoss,
      A0, Nat.cast_mul, Nat.cast_pow
    ]
    ring
  rw [degreeLossEq]
  calc
    (8 : ENNReal) * A0 ^ 2 *
          input.prebalancePacketDensityLoss multiplicity parentClass *
          A0 ≤
        8 * (depthCoefficient * envelope ^ 4) ^ 2 *
          (64 * envelope ^ 3) *
          (depthCoefficient * envelope ^ 4) := by
      gcongr
    _ =
        canonicalPacketDensityCoefficient depthBound *
          envelope ^ 15 := by
      simp only [canonicalPacketDensityCoefficient, depthCoefficient]
      ring
    _ = _ := rfl

theorem exists_canonicalPacketDensityThreshold
    (depthBound : ℕ)
    (densityExponent packetExponent : ℝ)
    (exponentGap : densityExponent < packetExponent) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 / 2 ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₀ →
          canonicalPacketDensityCoefficient depthBound *
              (ENNReal.ofReal
                (prebalanceLogCoefficient *
                  (1 + Real.log delta⁻¹))) ^ 15 ≤
            Kakeya.realRpowENN delta
              (-(packetExponent - densityExponent)) := by
  rcases
      exists_delta_C_pow_log_absorbed_ennreal
        (canonicalPacketDensityCoefficient depthBound)
        (canonicalPacketDensityCoefficient_ne_top depthBound)
        prebalanceLogCoefficient
        (zero_le_one.trans one_le_prebalanceLogCoefficient)
        (sub_pos.mpr exponentGap) (n := 15)
        (by norm_num)
    with ⟨threshold, thresholdPos, thresholdLeOne, absorbed⟩
  let delta₀ := min threshold (1 / 2 : ℝ)
  refine
    ⟨delta₀, lt_min thresholdPos (by norm_num),
      min_le_right _ _, ?_⟩
  intro delta deltaPos deltaLe
  exact absorbed delta deltaPos <|
    deltaLe.trans (min_le_left _ _)

noncomputable def canonicalPacketDensityThreshold
    (depthBound : ℕ)
    (densityExponent packetExponent : ℝ)
    (exponentGap : densityExponent < packetExponent) : ℝ :=
  Classical.choose <|
    exists_canonicalPacketDensityThreshold
      depthBound densityExponent packetExponent exponentGap

theorem canonicalPacketDensityThreshold_pos
    (depthBound : ℕ)
    (densityExponent packetExponent : ℝ)
    (exponentGap : densityExponent < packetExponent) :
    0 <
      canonicalPacketDensityThreshold
        depthBound densityExponent packetExponent exponentGap :=
  (Classical.choose_spec <|
    exists_canonicalPacketDensityThreshold
      depthBound densityExponent packetExponent exponentGap).1

theorem canonicalPacketDensityLoss_absorbed_of_smallDelta
    (depthBound : ℕ)
    (densityExponent packetExponent : ℝ)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4)
    (depthLe : schedule.levelCount ≤ depthBound)
    (exponentGap : densityExponent < packetExponent)
    (deltaLe :
      delta ≤
        canonicalPacketDensityThreshold
          depthBound densityExponent packetExponent exponentGap) :
    (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree : ENNReal) *
        Kakeya.realRpowENN delta packetExponent *
        input.prebalancePacketDensityLoss multiplicity parentClass *
        (input.canonicalPeelingA0
          multiplicity parentClass treeCleanup exactification bins :
            ENNReal) ≤
      Kakeya.realRpowENN delta densityExponent := by
  have deltaLtOne : delta < 1 := by
    exact deltaLe.trans_lt <|
      (Classical.choose_spec <|
        exists_canonicalPacketDensityThreshold
          depthBound densityExponent packetExponent exponentGap).2.1.trans_lt
        (by norm_num)
  have lossBound :=
    core.canonicalPacketDensityLoss_le_logFifteen
      input multiplicity parentClass treeCleanup exactification parentDegree
      depthBound fineNonempty fineDistinct fineBoundedBase depthLe deltaLtOne
  have powerBound :=
    (Classical.choose_spec <|
      exists_canonicalPacketDensityThreshold
        depthBound densityExponent packetExponent exponentGap).2.2
      delta input.delta_pos deltaLe
  calc
    (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree : ENNReal) *
        Kakeya.realRpowENN delta packetExponent *
        input.prebalancePacketDensityLoss multiplicity parentClass *
        (input.canonicalPeelingA0
          multiplicity parentClass treeCleanup exactification bins :
            ENNReal) =
      Kakeya.realRpowENN delta packetExponent *
        ((core.balancingDegreeLoss
            input multiplicity parentClass treeCleanup
              exactification parentDegree : ENNReal) *
          input.prebalancePacketDensityLoss multiplicity parentClass *
          (input.canonicalPeelingA0
            multiplicity parentClass treeCleanup exactification bins :
              ENNReal)) := by
        simp only [mul_assoc, mul_left_comm, mul_comm]
    _ ≤
      Kakeya.realRpowENN delta packetExponent *
        (canonicalPacketDensityCoefficient depthBound *
          (ENNReal.ofReal
            (prebalanceLogCoefficient *
              (1 + Real.log delta⁻¹))) ^ 15) := by
        gcongr
    _ ≤
      Kakeya.realRpowENN delta packetExponent *
        Kakeya.realRpowENN delta
          (-(packetExponent - densityExponent)) := by
        gcongr
    _ = Kakeya.realRpowENN delta densityExponent := by
      rw [← realRpowENN_add input.delta_pos]
      congr 1
      ring

theorem balancingAmbientLogSmallData_of_prebalanceSmall
    {depthBound : ℕ}
    {densityExponent lossExponent : ℝ}
    (small :
      PrebalanceSmallData
        delta depthBound densityExponent lossExponent)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4)
    (depthLe : schedule.levelCount ≤ depthBound)
    (exponentGap : densityExponent + lossExponent < 1)
    (density :
      Kakeya.realRpowENN delta densityExponent *
          fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass) :
    core.BalancingAmbientLogSmallData
      input multiplicity parentClass treeCleanup
        exactification parentDegree := by
  apply
    core.balancingAmbientLogSmallData_of_scaled_referenceDegree
      input multiplicity parentClass treeCleanup
        exactification parentDegree
  exact
    input.canonical_scaled_referenceDegree_lt_of_absorptions
      multiplicity parentClass treeCleanup exactification parentDegree
        core depthBound densityExponent lossExponent
        small.delta_lt_one fineNonempty fineDistinct fineBoundedBase
        depthLe exponentGap density small.loss_bound small.tail_bound

theorem exists_canonical_good_balancing_sample_of_prebalanceSmall
    {depthBound : ℕ}
    {densityExponent lossExponent : ℝ}
    (small :
      PrebalanceSmallData
        delta depthBound densityExponent lossExponent)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4)
    (depthLe : schedule.levelCount ≤ depthBound)
    (exponentGap : densityExponent + lossExponent < 1)
    (density :
      Kakeya.realRpowENN delta densityExponent *
          fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass) :
    Nonempty
      (core.ranges.GoodBalancingSampleData
        (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree)) :=
  core.exists_canonical_good_balancing_sample_of_ambientLog
    input multiplicity parentClass treeCleanup
      exactification parentDegree <|
    core.balancingAmbientLogSmallData_of_prebalanceSmall
      input multiplicity parentClass treeCleanup
        exactification parentDegree
      small fineNonempty fineDistinct fineBoundedBase
      depthLe exponentGap density

theorem exists_canonical_good_balancing_sample_of_smallDelta
    {depthBound : ℕ}
    {densityExponent lossExponent : ℝ}
    (lossExponentPos : 0 < lossExponent)
    (exponentGap : densityExponent + lossExponent < 1)
    (deltaLe :
      delta ≤
        prebalanceSmallThreshold
          depthBound densityExponent lossExponent
            lossExponentPos exponentGap)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4)
    (depthLe : schedule.levelCount ≤ depthBound)
    (density :
      Kakeya.realRpowENN delta densityExponent *
          fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass) :
    Nonempty
      (core.ranges.GoodBalancingSampleData
        (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree)) := by
  apply
    core.exists_canonical_good_balancing_sample_of_prebalanceSmall
      input multiplicity parentClass treeCleanup
        exactification parentDegree
      (prebalanceSmallData_of_smallDelta
        depthBound densityExponent lossExponent
          lossExponentPos exponentGap input.delta_pos deltaLe)
      fineNonempty fineDistinct fineBoundedBase depthLe exponentGap density

theorem packetDensityAbsorption_of_prebalance
    {densityBase densityConstant : ENNReal}
    (good :
      core.ranges.GoodBalancingSampleData
        (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree))
    (density :
      densityBase * fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass)
    (absorption :
      (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree : ENNReal) *
          densityConstant *
          input.prebalancePacketDensityLoss multiplicity parentClass *
          (input.canonicalPeelingA0
            multiplicity parentClass treeCleanup exactification bins :
              ENNReal) ≤
        densityBase) :
    TerminalFineShading.PacketDensityAbsorptionData
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good densityConstant := by
  let preLoss :=
    input.prebalancePacketDensityLoss multiplicity parentClass
  let A0 :=
    input.canonicalPeelingA0
      multiplicity parentClass treeCleanup exactification bins
  have prebalance :=
    input.prebalance_parent_packet_density
      multiplicity parentClass treeCleanup exactification
        parentDegree densityBase density
  have thresholdBound :
      parentDegree.K ≤
        A0 *
          input.parentThreshold
            multiplicity parentClass treeCleanup
              exactification parentDegree A0 := by
    simpa [
      A0, PureWZ2Prop62PacketCellInput.parentThreshold,
      Nat.mul_comm
    ] using
      (le_smul_ceilDiv core.A0_pos :
        parentDegree.K ≤
          A0 * (parentDegree.K ⌈/⌉ A0))
  have factorPos : 0 < (preLoss * A0 : ENNReal) := by
    have preLossPos :
        0 < input.prebalancePacketDensityLoss multiplicity parentClass :=
      input.prebalancePacketDensityLoss_pos multiplicity parentClass
    have A0Pos : 0 < (A0 : ENNReal) := by
      exact_mod_cast core.A0_pos
    exact ENNReal.mul_pos preLossPos.ne' A0Pos.ne'
  have factorTop : (preLoss * A0 : ENNReal) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (input.prebalancePacketDensityLoss_ne_top
        multiplicity parentClass)
      (ENNReal.natCast_ne_top A0)
  constructor
  have absorbed :
      (preLoss * A0) *
          ((core.balancingDegreeLoss
              input multiplicity parentClass treeCleanup
                exactification parentDegree : ENNReal) *
            densityConstant) ≤
        densityBase := by
    simpa [preLoss, A0, mul_assoc, mul_left_comm, mul_comm] using
      absorption
  have absorbedWithFiber :
      ((core.balancingDegreeLoss
              input multiplicity parentClass treeCleanup
                exactification parentDegree : ENNReal) *
            densityConstant *
            (parentClass.fiberFloor : ENNReal) *
            Kakeya.realRpowENN delta 2) *
          (preLoss * A0) ≤
        densityBase *
          (parentClass.fiberFloor : ENNReal) *
          Kakeya.realRpowENN delta 2 := by
    calc
      ((core.balancingDegreeLoss
                input multiplicity parentClass treeCleanup
                  exactification parentDegree : ENNReal) *
              densityConstant *
              (parentClass.fiberFloor : ENNReal) *
              Kakeya.realRpowENN delta 2) *
            (preLoss * A0) =
          ((preLoss * A0) *
            ((core.balancingDegreeLoss
                input multiplicity parentClass treeCleanup
                  exactification parentDegree : ENNReal) *
              densityConstant)) *
            (parentClass.fiberFloor : ENNReal) *
            Kakeya.realRpowENN delta 2 := by
        simp only [mul_assoc, mul_left_comm, mul_comm]
      _ ≤
          densityBase *
            (parentClass.fiberFloor : ENNReal) *
            Kakeya.realRpowENN delta 2 := by
        gcongr
  have thresholdScaled :
      preLoss * (multiplicity.muFine : ENNReal) *
            (parentDegree.K : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0)) ≤
        (preLoss * A0) *
          (((multiplicity.muFine *
            input.parentThreshold
              multiplicity parentClass treeCleanup
                exactification parentDegree A0 : ℕ) : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0))) := by
    calc
      preLoss * (multiplicity.muFine : ENNReal) *
            (parentDegree.K : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0)) ≤
          preLoss * (multiplicity.muFine : ENNReal) *
            ((A0 *
              input.parentThreshold
                multiplicity parentClass treeCleanup
                  exactification parentDegree A0 : ℕ) : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
        gcongr
      _ =
          (preLoss * A0) *
            (((multiplicity.muFine *
              input.parentThreshold
                multiplicity parentClass treeCleanup
                  exactification parentDegree A0 : ℕ) : ENNReal) *
              volume (wz1PaperGridCube delta (0, 0, 0))) := by
        norm_num only [Nat.cast_mul]
        simp only [mul_assoc, mul_left_comm, mul_comm]
  have scaled :
      ((core.balancingDegreeLoss
              input multiplicity parentClass treeCleanup
                exactification parentDegree : ENNReal) *
            densityConstant *
            (parentClass.fiberFloor : ENNReal) *
            Kakeya.realRpowENN delta 2) *
          (preLoss * A0) ≤
        (((multiplicity.muFine *
            input.parentThreshold
              multiplicity parentClass treeCleanup
                exactification parentDegree A0 : ℕ) : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0))) *
          (preLoss * A0) := by
    calc
      ((core.balancingDegreeLoss
                input multiplicity parentClass treeCleanup
                  exactification parentDegree : ENNReal) *
              densityConstant *
              (parentClass.fiberFloor : ENNReal) *
              Kakeya.realRpowENN delta 2) *
            (preLoss * A0) ≤
        densityBase *
          (parentClass.fiberFloor : ENNReal) *
          Kakeya.realRpowENN delta 2 :=
      absorbedWithFiber
    _ ≤
        preLoss * (multiplicity.muFine : ENNReal) *
          (parentDegree.K : ENNReal) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := by
      simpa only [preLoss] using prebalance
    _ ≤
        (((multiplicity.muFine *
            input.parentThreshold
              multiplicity parentClass treeCleanup
                exactification parentDegree A0 : ℕ) : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0))) *
          (preLoss * A0) := by
      simpa only [mul_comm] using thresholdScaled
  have cancelled :=
    (ENNReal.mul_le_mul_iff_left
      factorPos.ne' factorTop).mp scaled
  simpa [mul_assoc, mul_left_comm, mul_comm] using cancelled

theorem packetDensityAbsorption_of_smallDelta
    {depthBound : ℕ}
    {densityExponent packetExponent : ℝ}
    (good :
      core.ranges.GoodBalancingSampleData
        (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree))
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4)
    (depthLe : schedule.levelCount ≤ depthBound)
    (exponentGap : densityExponent < packetExponent)
    (deltaLe :
      delta ≤
        canonicalPacketDensityThreshold
          depthBound densityExponent packetExponent exponentGap)
    (density :
      Kakeya.realRpowENN delta densityExponent *
          fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass) :
    TerminalFineShading.PacketDensityAbsorptionData
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good
        (Kakeya.realRpowENN delta packetExponent) := by
  apply
    core.packetDensityAbsorption_of_prebalance
      input multiplicity parentClass treeCleanup exactification parentDegree
      good density
  exact
    core.canonicalPacketDensityLoss_absorbed_of_smallDelta
      input multiplicity parentClass treeCleanup exactification parentDegree
      depthBound densityExponent packetExponent
      fineNonempty fineDistinct fineBoundedBase depthLe exponentGap deltaLe

def canonicalMassRetentionCoefficient
    (depthBound : ℕ) : ENNReal :=
  1024 * (2 : ENNReal) ^ (depthBound + 1) *
    (ENNReal.ofReal
      (8 * (depthBound + 2) * 8 ^ 4 : ℝ)) ^ 2

theorem canonicalMassRetentionCoefficient_ne_top
    (depthBound : ℕ) :
    canonicalMassRetentionCoefficient depthBound ≠ ⊤ := by
  unfold canonicalMassRetentionCoefficient
  exact
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top (by norm_num)))
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

theorem canonicalTerminalMassRetentionLoss_le_logFourteen
    (good :
      core.ranges.GoodBalancingSampleData
        (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree))
    (depthBound : ℕ)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4)
    (depthLe : schedule.levelCount ≤ depthBound)
    (deltaLtOne : delta < 1) :
    input.terminalMassRetentionLoss
        multiplicity parentClass treeCleanup exactification
          parentDegree core good ≤
      canonicalMassRetentionCoefficient depthBound *
        (ENNReal.ofReal
          (prebalanceLogCoefficient *
            (1 + Real.log delta⁻¹))) ^ 14 := by
  let dyadicLoss : ENNReal :=
    (multiplicity.binCount : ENNReal) *
      parentClass.weightBinCount *
      parentClass.fiberBinCount
  let degreeBinLoss : ENNReal :=
    (bins.fineCellBin.binCount : ENNReal) *
      bins.parentCoarseBin.binCount *
      bins.coarseCellBin.binCount
  let A0 : ENNReal :=
    input.canonicalPeelingA0
      multiplicity parentClass treeCleanup exactification bins
  let envelope : ENNReal :=
    ENNReal.ofReal
      (prebalanceLogCoefficient * (1 + Real.log delta⁻¹))
  let depthCoefficient : ENNReal :=
    ENNReal.ofReal (8 * (depthBound + 2) * 8 ^ 4 : ℝ)
  have dyadicBound : dyadicLoss ≤ 4 * envelope ^ 3 := by
    simpa only [dyadicLoss, envelope] using
      input.prebalanceDyadicProduct_le_logCube
        multiplicity parentClass input.delta_pos deltaLtOne.le
          fineNonempty fineDistinct fineBoundedBase
  have degreeBinBound : degreeBinLoss ≤ 8 * envelope ^ 3 := by
    simpa only [degreeBinLoss, envelope] using
      input.threeDegreeBinProduct_le_prebalanceLogCube
        multiplicity parentClass treeCleanup exactification
          input.delta_pos deltaLtOne.le fineNonempty
          fineDistinct fineBoundedBase
  have A0Bound : A0 ≤ depthCoefficient * envelope ^ 4 := by
    simpa only [A0, depthCoefficient, envelope] using
      input.canonicalPeelingA0_le_prebalanceLogFourthENN
        multiplicity parentClass treeCleanup exactification
          depthBound depthLe input.delta_pos deltaLtOne.le
          fineNonempty fineDistinct fineBoundedBase
  have treeBound :
      (2 : ENNReal) ^ (schedule.levelCount + 1) ≤
        (2 : ENNReal) ^ (depthBound + 1) := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have degreeLossEq :
      (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree : ENNReal) =
        8 * A0 ^ 2 := by
    simp [
      FourDegreeCoreAssemblyData.balancingDegreeLoss,
      FourDegreeCoreAssemblyData.balancingRateLoss,
      A0, Nat.cast_mul, Nat.cast_pow
    ]
    ring
  calc
    input.terminalMassRetentionLoss
          multiplicity parentClass treeCleanup exactification
            parentDegree core good =
        dyadicLoss *
          (2 : ENNReal) ^ (schedule.levelCount + 1) *
          4 * degreeBinLoss *
          (core.balancingDegreeLoss
            input multiplicity parentClass treeCleanup
              exactification parentDegree : ENNReal) := by
      simp [PureWZ2Prop62PacketCellInput.terminalMassRetentionLoss,
        dyadicLoss, degreeBinLoss]
      ring
    _ =
        dyadicLoss *
          (2 : ENNReal) ^ (schedule.levelCount + 1) *
          4 * degreeBinLoss * (8 * A0 ^ 2) := by
      rw [degreeLossEq]
    _ ≤
        (4 * envelope ^ 3) *
          ((2 : ENNReal) ^ (depthBound + 1)) *
          4 * (8 * envelope ^ 3) *
          (8 * (depthCoefficient * envelope ^ 4) ^ 2) := by
      gcongr
    _ =
        canonicalMassRetentionCoefficient depthBound *
          envelope ^ 14 := by
      simp only [canonicalMassRetentionCoefficient, depthCoefficient]
      ring

def canonicalMassRetentionLogCoefficient
    (depthBound : ℕ) : ℝ :=
  max
    (canonicalMassRetentionCoefficient depthBound).toReal
    prebalanceLogCoefficient

theorem canonicalMassRetentionLogCoefficient_nonneg
    (depthBound : ℕ) :
    0 ≤ canonicalMassRetentionLogCoefficient depthBound := by
  exact ENNReal.toReal_nonneg.trans <| le_max_left _ _

theorem exists_canonicalMassRetentionThreshold
    (depthBound : ℕ) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 / 2 ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₀ →
          3 ≤ Real.log delta⁻¹ ∧
            canonicalMassRetentionLogCoefficient depthBound *
                (1 + Real.log delta⁻¹) ≤
              (Real.log delta⁻¹) ^ 2 := by
  rcases
      exists_delta_boundary_log_square
        (canonicalMassRetentionLogCoefficient depthBound)
        (canonicalMassRetentionLogCoefficient_nonneg depthBound)
    with ⟨threshold, thresholdPos, thresholdLeOne, absorbed⟩
  let delta₀ := min threshold (1 / 2 : ℝ)
  refine
    ⟨delta₀, lt_min thresholdPos (by norm_num),
      min_le_right _ _, ?_⟩
  intro delta deltaPos deltaLe
  exact absorbed delta deltaPos <|
    deltaLe.trans (min_le_left _ _)

noncomputable def canonicalMassRetentionThreshold
    (depthBound : ℕ) : ℝ :=
  Classical.choose <|
    exists_canonicalMassRetentionThreshold depthBound

theorem canonicalMassRetentionThreshold_pos
    (depthBound : ℕ) :
    0 < canonicalMassRetentionThreshold depthBound :=
  (Classical.choose_spec <|
    exists_canonicalMassRetentionThreshold depthBound).1

theorem massRetentionAbsorption_fifty_of_smallDelta
    (good :
      core.ranges.GoodBalancingSampleData
        (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree))
    (depthBound : ℕ)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4)
    (depthLe : schedule.levelCount ≤ depthBound)
    (deltaLe :
      delta ≤ canonicalMassRetentionThreshold depthBound) :
    input.MassRetentionAbsorptionData
      multiplicity parentClass treeCleanup exactification
        parentDegree core good 50 := by
  let coefficient : ENNReal :=
    canonicalMassRetentionCoefficient depthBound
  let envelope : ENNReal :=
    ENNReal.ofReal
      (prebalanceLogCoefficient * (1 + Real.log delta⁻¹))
  let logTerm : ENNReal :=
    ENNReal.ofReal (Real.log (1 / delta))
  have thresholdData :=
    (Classical.choose_spec <|
      exists_canonicalMassRetentionThreshold depthBound).2.2
      delta input.delta_pos deltaLe
  have deltaLtOne : delta < 1 := by
    exact deltaLe.trans_lt <|
      (Classical.choose_spec <|
        exists_canonicalMassRetentionThreshold depthBound).2.1.trans_lt
        (by norm_num)
  have lossBound :
      input.terminalMassRetentionLoss
          multiplicity parentClass treeCleanup exactification
            parentDegree core good ≤
        coefficient * envelope ^ 14 := by
    simpa only [coefficient, envelope] using
      core.canonicalTerminalMassRetentionLoss_le_logFourteen
        input multiplicity parentClass treeCleanup exactification
          parentDegree good depthBound fineNonempty fineDistinct
          fineBoundedBase depthLe deltaLtOne
  have logIdentity :
      Real.log (1 / delta) = Real.log delta⁻¹ := by
    congr 1
    field_simp [input.delta_pos.ne']
  have logRealNonnegative : 0 ≤ Real.log delta⁻¹ := by
    linarith [thresholdData.1]
  have logTermOne : (1 : ENNReal) ≤ logTerm := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_mono <| by
      rw [logIdentity]
      linarith [thresholdData.1]
  have coefficientFinite : coefficient ≠ ⊤ :=
    canonicalMassRetentionCoefficient_ne_top depthBound
  have coefficientRepresentation :
      coefficient = ENNReal.ofReal coefficient.toReal :=
    (ENNReal.ofReal_toReal coefficientFinite).symm
  have coefficientBound :
      coefficient ≤ logTerm ^ 2 := by
    calc
      coefficient = ENNReal.ofReal coefficient.toReal :=
        coefficientRepresentation
      _ ≤
          ENNReal.ofReal
            (canonicalMassRetentionLogCoefficient depthBound *
              (1 + Real.log delta⁻¹)) := by
        apply ENNReal.ofReal_mono
        have logFactorOne : 1 ≤ 1 + Real.log delta⁻¹ := by
          linarith
        calc
          coefficient.toReal ≤
              canonicalMassRetentionLogCoefficient depthBound :=
            le_max_left _ _
          _ ≤
              canonicalMassRetentionLogCoefficient depthBound *
                (1 + Real.log delta⁻¹) := by
            calc
              canonicalMassRetentionLogCoefficient depthBound =
                  canonicalMassRetentionLogCoefficient depthBound * 1 := by
                ring
              _ ≤
                  canonicalMassRetentionLogCoefficient depthBound *
                    (1 + Real.log delta⁻¹) := by
                exact mul_le_mul_of_nonneg_left logFactorOne <|
                  canonicalMassRetentionLogCoefficient_nonneg depthBound
      _ ≤ ENNReal.ofReal ((Real.log delta⁻¹) ^ 2) :=
        ENNReal.ofReal_mono thresholdData.2
      _ = logTerm ^ 2 := by
        dsimp only [logTerm]
        rw [logIdentity]
        exact ENNReal.ofReal_pow logRealNonnegative 2
  have envelopeBound : envelope ≤ logTerm ^ 2 := by
    calc
      envelope ≤
          ENNReal.ofReal
            (canonicalMassRetentionLogCoefficient depthBound *
              (1 + Real.log delta⁻¹)) := by
        apply ENNReal.ofReal_mono
        exact mul_le_mul_of_nonneg_right
          (le_max_right _ _) (by linarith)
      _ ≤ ENNReal.ofReal ((Real.log delta⁻¹) ^ 2) :=
        ENNReal.ofReal_mono thresholdData.2
      _ = logTerm ^ 2 := by
        dsimp only [logTerm]
        rw [logIdentity]
        exact ENNReal.ofReal_pow logRealNonnegative 2
  have lossPower :
      input.terminalMassRetentionLoss
          multiplicity parentClass treeCleanup exactification
            parentDegree core good ≤
        logTerm ^ 30 := by
    calc
      input.terminalMassRetentionLoss
            multiplicity parentClass treeCleanup exactification
              parentDegree core good ≤
          coefficient * envelope ^ 14 := lossBound
      _ ≤ (logTerm ^ 2) * (logTerm ^ 2) ^ 14 := by
        gcongr
      _ = logTerm ^ 30 := by ring
  have lossFifty :
      input.terminalMassRetentionLoss
          multiplicity parentClass treeCleanup exactification
            parentDegree core good ≤
        logTerm ^ 50 := by
    exact lossPower.trans <|
      pow_le_pow_right₀ logTermOne (by norm_num)
  have logTermZero : logTerm ≠ 0 := by
    exact ne_of_gt (zero_lt_one.trans_le logTermOne)
  have logTermTop : logTerm ≠ ⊤ := by
    dsimp only [logTerm]
    exact ENNReal.ofReal_ne_top
  constructor
  calc
    wz2PaperPureRefinementFraction delta 50 *
          input.terminalMassRetentionLoss
            multiplicity parentClass treeCleanup exactification
              parentDegree core good ≤
        wz2PaperPureRefinementFraction delta 50 * logTerm ^ 50 := by
      gcongr
    _ = (logTerm ^ 50)⁻¹ * logTerm ^ 50 := by
      simp [wz2PaperPureRefinementFraction, logTerm,
        ENNReal.inv_pow]
    _ = 1 :=
      ENNReal.inv_mul_cancel
        (pow_ne_zero 50 logTermZero)
        (ENNReal.pow_ne_top logTermTop)

theorem pureWZ2_prop62_canonical_four_degree_output_of_prebalanceSmall
    {depthBound : ℕ}
    {densityExponent lossExponent : ℝ}
    {fiberConstant densityConstant : ENNReal}
    {logExponent : ℕ}
    (families :
      input.TerminalCompleteFamiliesData
        multiplicity parentClass treeCleanup exactification
          core.ranges)
    (small :
      PrebalanceSmallData
        delta depthBound densityExponent lossExponent)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4)
    (depthLe : schedule.levelCount ≤ depthBound)
    (exponentGap : densityExponent + lossExponent < 1)
    (density :
      Kakeya.realRpowENN delta densityExponent *
          fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass)
    (packetAbsorption :
      ∀ good :
          core.ranges.GoodBalancingSampleData
            (core.balancingDegreeLoss
              input multiplicity parentClass treeCleanup
                exactification parentDegree),
        TerminalFineShading.PacketDensityAbsorptionData
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good densityConstant)
    (massAbsorption :
      ∀ good :
          core.ranges.GoodBalancingSampleData
            (core.balancingDegreeLoss
              input multiplicity parentClass treeCleanup
                exactification parentDegree),
        input.MassRetentionAbsorptionData
          multiplicity parentClass treeCleanup exactification
            parentDegree core good logExponent) :
    Nonempty
      (core.CanonicalFourDegreeOutputData
        input multiplicity parentClass treeCleanup
          exactification parentDegree families
          fiberConstant densityConstant logExponent) := by
  apply
    core.pureWZ2_prop62_canonical_four_degree_output_of_ambientLog
      input multiplicity parentClass treeCleanup
        exactification parentDegree families
  · exact
      core.balancingAmbientLogSmallData_of_prebalanceSmall
        input multiplicity parentClass treeCleanup
          exactification parentDegree
        small fineNonempty fineDistinct fineBoundedBase
        depthLe exponentGap density
  · exact packetAbsorption
  · exact massAbsorption

theorem pureWZ2_prop62_canonical_four_degree_output_of_smallDelta
    {depthBound : ℕ}
    {densityExponent lossExponent : ℝ}
    {fiberConstant densityConstant : ENNReal}
    {logExponent : ℕ}
    (families :
      input.TerminalCompleteFamiliesData
        multiplicity parentClass treeCleanup exactification
          core.ranges)
    (lossExponentPos : 0 < lossExponent)
    (exponentGap : densityExponent + lossExponent < 1)
    (deltaLe :
      delta ≤
        prebalanceSmallThreshold
          depthBound densityExponent lossExponent
            lossExponentPos exponentGap)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4)
    (depthLe : schedule.levelCount ≤ depthBound)
    (density :
      Kakeya.realRpowENN delta densityExponent *
          fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass)
    (packetAbsorption :
      ∀ good :
          core.ranges.GoodBalancingSampleData
            (core.balancingDegreeLoss
              input multiplicity parentClass treeCleanup
                exactification parentDegree),
        TerminalFineShading.PacketDensityAbsorptionData
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good densityConstant)
    (massAbsorption :
      ∀ good :
          core.ranges.GoodBalancingSampleData
            (core.balancingDegreeLoss
              input multiplicity parentClass treeCleanup
                exactification parentDegree),
        input.MassRetentionAbsorptionData
          multiplicity parentClass treeCleanup exactification
            parentDegree core good logExponent) :
    Nonempty
      (core.CanonicalFourDegreeOutputData
        input multiplicity parentClass treeCleanup
          exactification parentDegree families
          fiberConstant densityConstant logExponent) := by
  apply
    core.pureWZ2_prop62_canonical_four_degree_output_of_prebalanceSmall
      input multiplicity parentClass treeCleanup
        exactification parentDegree families
      (prebalanceSmallData_of_smallDelta
        depthBound densityExponent lossExponent
          lossExponentPos exponentGap input.delta_pos deltaLe)
      fineNonempty fineDistinct fineBoundedBase depthLe exponentGap density
      packetAbsorption massAbsorption

theorem pureWZ2_prop62_canonical_four_degree_output_fifty_of_prebalanceSmall
    {depthBound : ℕ}
    {densityExponent lossExponent packetExponent : ℝ}
    {fiberConstant : ENNReal}
    (families :
      input.TerminalCompleteFamiliesData
        multiplicity parentClass treeCleanup exactification
          core.ranges)
    (small :
      PrebalanceSmallData
        delta depthBound densityExponent lossExponent)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4)
    (depthLe : schedule.levelCount ≤ depthBound)
    (balancingExponentGap :
      densityExponent + lossExponent < 1)
    (packetExponentGap : densityExponent < packetExponent)
    (packetDeltaLe :
      delta ≤
        canonicalPacketDensityThreshold
          depthBound densityExponent packetExponent packetExponentGap)
    (massDeltaLe :
      delta ≤ canonicalMassRetentionThreshold depthBound)
    (density :
      Kakeya.realRpowENN delta densityExponent *
          fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass) :
    Nonempty
      (core.CanonicalFourDegreeOutputData
        input multiplicity parentClass treeCleanup
          exactification parentDegree families fiberConstant
          (Kakeya.realRpowENN delta packetExponent) 50) := by
  apply
    core.pureWZ2_prop62_canonical_four_degree_output_of_prebalanceSmall
      input multiplicity parentClass treeCleanup
        exactification parentDegree families
      small fineNonempty fineDistinct fineBoundedBase depthLe
        balancingExponentGap density
  · intro good
    exact
      core.packetDensityAbsorption_of_smallDelta
        input multiplicity parentClass treeCleanup exactification
          parentDegree good
          (depthBound := depthBound)
          (densityExponent := densityExponent)
          (packetExponent := packetExponent)
          fineNonempty fineDistinct
          fineBoundedBase depthLe packetExponentGap packetDeltaLe density
  · intro good
    exact
      core.massRetentionAbsorption_fifty_of_smallDelta
        input multiplicity parentClass treeCleanup exactification
          parentDegree good depthBound fineNonempty fineDistinct
          fineBoundedBase depthLe massDeltaLe

theorem canonicalPacketDensityLoss_le_logFifteen_of_fineLog
    (depthBound : ℕ)
    {logCoefficient : ℝ}
    (deltaLeOne : delta ≤ 1)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹))
    (depthLe : schedule.levelCount ≤ depthBound) :
    (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree : ENNReal) *
        input.prebalancePacketDensityLoss multiplicity parentClass *
        (input.canonicalPeelingA0
          multiplicity parentClass treeCleanup exactification bins :
            ENNReal) ≤
      canonicalPacketDensityCoefficient depthBound *
        (ENNReal.ofReal
          (fineLogEnvelopeCoefficient logCoefficient *
            (1 + Real.log delta⁻¹))) ^ 15 := by
  let A0 : ENNReal :=
    input.canonicalPeelingA0
      multiplicity parentClass treeCleanup exactification bins
  let envelope : ENNReal :=
    ENNReal.ofReal
      (fineLogEnvelopeCoefficient logCoefficient *
        (1 + Real.log delta⁻¹))
  let depthCoefficient : ENNReal :=
    ENNReal.ofReal (8 * (depthBound + 2) * 8 ^ 4 : ℝ)
  have packetLoss :
      input.prebalancePacketDensityLoss multiplicity parentClass ≤
        64 * envelope ^ 3 := by
    simpa only [envelope] using
      input.prebalancePacketDensityLoss_le_logCube_of_fineLog
        multiplicity parentClass deltaLeOne boundaryCoefficientLe
          fineLogBound
  have A0Bound :
      A0 ≤ depthCoefficient * envelope ^ 4 := by
    simpa only [A0, depthCoefficient, envelope] using
      input.canonicalPeelingA0_le_logFourthENN_of_fineLog
        multiplicity parentClass treeCleanup exactification
          (bins := bins) depthBound depthLe deltaLeOne
          boundaryCoefficientLe fineLogBound
  have degreeLossEq :
      (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree : ENNReal) =
        8 * A0 ^ 2 := by
    simp [
      FourDegreeCoreAssemblyData.balancingDegreeLoss,
      FourDegreeCoreAssemblyData.balancingRateLoss,
      A0, Nat.cast_mul, Nat.cast_pow
    ]
    ring
  rw [degreeLossEq]
  calc
    (8 : ENNReal) * A0 ^ 2 *
          input.prebalancePacketDensityLoss multiplicity parentClass *
          A0 ≤
        8 * (depthCoefficient * envelope ^ 4) ^ 2 *
          (64 * envelope ^ 3) *
          (depthCoefficient * envelope ^ 4) := by
      gcongr
    _ =
        canonicalPacketDensityCoefficient depthBound *
          envelope ^ 15 := by
      simp only [canonicalPacketDensityCoefficient, depthCoefficient]
      ring
    _ = _ := rfl

theorem balancingAmbientLogSmallData_of_fineLog
    {depthBound : ℕ}
    {densityExponent lossExponent logCoefficient : ℝ}
    (small :
      PrebalanceSmallDataOfFineLog
        delta depthBound densityExponent lossExponent logCoefficient)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹))
    (depthLe : schedule.levelCount ≤ depthBound)
    (exponentGap : densityExponent + lossExponent < 1)
    (density :
      Kakeya.realRpowENN delta densityExponent *
          fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass) :
    core.BalancingAmbientLogSmallData
      input multiplicity parentClass treeCleanup
        exactification parentDegree := by
  apply
    core.balancingAmbientLogSmallData_of_scaled_referenceDegree
      input multiplicity parentClass treeCleanup
        exactification parentDegree
  exact
    input.canonical_scaled_referenceDegree_lt_of_fineLog
      multiplicity parentClass treeCleanup exactification parentDegree
        core depthBound densityExponent lossExponent logCoefficient
        small boundaryCoefficientLe fineLogBound depthLe exponentGap density

def canonicalPacketDensityCoefficientOfFineLog
    (depthBound : ℕ) : ENNReal :=
  canonicalPacketDensityCoefficient depthBound

theorem canonicalPacketDensityCoefficientOfFineLog_ne_top
    (depthBound : ℕ) :
    canonicalPacketDensityCoefficientOfFineLog depthBound ≠ ⊤ :=
  canonicalPacketDensityCoefficient_ne_top depthBound

theorem exists_canonicalPacketDensityThresholdOfFineLog
    (depthBound : ℕ)
    (densityExponent packetExponent logCoefficient : ℝ)
    (logCoefficientOne : 1 ≤ logCoefficient)
    (exponentGap : densityExponent < packetExponent) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 / 2 ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₀ →
          canonicalPacketDensityCoefficientOfFineLog depthBound *
              (ENNReal.ofReal
                (fineLogEnvelopeCoefficient logCoefficient *
                  (1 + Real.log delta⁻¹))) ^ 15 ≤
            Kakeya.realRpowENN delta
              (-(packetExponent - densityExponent)) := by
  rcases
      exists_delta_C_pow_log_absorbed_ennreal
        (canonicalPacketDensityCoefficientOfFineLog depthBound)
        (canonicalPacketDensityCoefficientOfFineLog_ne_top depthBound)
        (fineLogEnvelopeCoefficient logCoefficient)
        (zero_le_one.trans <|
          fineLogEnvelopeCoefficient_one_le logCoefficientOne)
        (sub_pos.mpr exponentGap) (n := 15)
        (by norm_num)
    with ⟨threshold, thresholdPos, thresholdLeOne, absorbed⟩
  let delta₀ := min threshold (1 / 2 : ℝ)
  refine
    ⟨delta₀, lt_min thresholdPos (by norm_num),
      min_le_right _ _, ?_⟩
  intro delta deltaPos deltaLe
  exact absorbed delta deltaPos <|
    deltaLe.trans (min_le_left _ _)

noncomputable def canonicalPacketDensityThresholdOfFineLog
    (depthBound : ℕ)
    (densityExponent packetExponent logCoefficient : ℝ)
    (logCoefficientOne : 1 ≤ logCoefficient)
    (exponentGap : densityExponent < packetExponent) : ℝ :=
  Classical.choose <|
    exists_canonicalPacketDensityThresholdOfFineLog
      depthBound densityExponent packetExponent logCoefficient
        logCoefficientOne exponentGap

theorem canonicalPacketDensityLoss_absorbed_of_smallDelta_of_fineLog
    (depthBound : ℕ)
    (densityExponent packetExponent logCoefficient : ℝ)
    (logCoefficientOne : 1 ≤ logCoefficient)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹))
    (depthLe : schedule.levelCount ≤ depthBound)
    (exponentGap : densityExponent < packetExponent)
    (deltaLe :
      delta ≤
        canonicalPacketDensityThresholdOfFineLog
          depthBound densityExponent packetExponent logCoefficient
            logCoefficientOne exponentGap) :
    (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree : ENNReal) *
        Kakeya.realRpowENN delta packetExponent *
        input.prebalancePacketDensityLoss multiplicity parentClass *
        (input.canonicalPeelingA0
          multiplicity parentClass treeCleanup exactification bins :
            ENNReal) ≤
      Kakeya.realRpowENN delta densityExponent := by
  have deltaLtOne : delta < 1 := by
    exact deltaLe.trans_lt <|
      (Classical.choose_spec <|
        exists_canonicalPacketDensityThresholdOfFineLog
          depthBound densityExponent packetExponent logCoefficient
            logCoefficientOne exponentGap).2.1.trans_lt
        (by norm_num)
  have lossBound :=
    core.canonicalPacketDensityLoss_le_logFifteen_of_fineLog
      input multiplicity parentClass treeCleanup exactification parentDegree
        depthBound deltaLtOne.le boundaryCoefficientLe fineLogBound depthLe
  have powerBound :=
    (Classical.choose_spec <|
      exists_canonicalPacketDensityThresholdOfFineLog
        depthBound densityExponent packetExponent logCoefficient
          logCoefficientOne exponentGap).2.2
      delta input.delta_pos deltaLe
  calc
    (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree : ENNReal) *
        Kakeya.realRpowENN delta packetExponent *
        input.prebalancePacketDensityLoss multiplicity parentClass *
        (input.canonicalPeelingA0
          multiplicity parentClass treeCleanup exactification bins :
            ENNReal) =
      Kakeya.realRpowENN delta packetExponent *
        ((core.balancingDegreeLoss
            input multiplicity parentClass treeCleanup
              exactification parentDegree : ENNReal) *
          input.prebalancePacketDensityLoss multiplicity parentClass *
          (input.canonicalPeelingA0
            multiplicity parentClass treeCleanup exactification bins :
              ENNReal)) := by
        simp only [mul_assoc, mul_left_comm, mul_comm]
    _ ≤
      Kakeya.realRpowENN delta packetExponent *
        (canonicalPacketDensityCoefficientOfFineLog depthBound *
          (ENNReal.ofReal
            (fineLogEnvelopeCoefficient logCoefficient *
              (1 + Real.log delta⁻¹))) ^ 15) := by
        apply mul_le_mul_left'
        simpa only [canonicalPacketDensityCoefficientOfFineLog] using
          lossBound
    _ ≤
      Kakeya.realRpowENN delta packetExponent *
        Kakeya.realRpowENN delta
          (-(packetExponent - densityExponent)) := by
        exact mul_le_mul_left' powerBound _
    _ = Kakeya.realRpowENN delta densityExponent := by
      rw [← realRpowENN_add input.delta_pos]
      congr 1
      ring

theorem packetDensityAbsorption_of_smallDelta_of_fineLog
    {depthBound : ℕ}
    {densityExponent packetExponent logCoefficient : ℝ}
    (good :
      core.ranges.GoodBalancingSampleData
        (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree))
    (logCoefficientOne : 1 ≤ logCoefficient)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹))
    (depthLe : schedule.levelCount ≤ depthBound)
    (exponentGap : densityExponent < packetExponent)
    (deltaLe :
      delta ≤
        canonicalPacketDensityThresholdOfFineLog
          depthBound densityExponent packetExponent logCoefficient
            logCoefficientOne exponentGap)
    (density :
      Kakeya.realRpowENN delta densityExponent *
          fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass) :
    TerminalFineShading.PacketDensityAbsorptionData
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good
        (Kakeya.realRpowENN delta packetExponent) := by
  apply
    core.packetDensityAbsorption_of_prebalance
      input multiplicity parentClass treeCleanup exactification parentDegree
      good density
  exact
    core.canonicalPacketDensityLoss_absorbed_of_smallDelta_of_fineLog
      input multiplicity parentClass treeCleanup exactification parentDegree
        depthBound densityExponent packetExponent logCoefficient
        logCoefficientOne boundaryCoefficientLe fineLogBound depthLe
        exponentGap deltaLe

theorem canonicalTerminalMassRetentionLoss_le_logFourteen_of_fineLog
    (good :
      core.ranges.GoodBalancingSampleData
        (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree))
    (depthBound : ℕ)
    {logCoefficient : ℝ}
    (deltaLeOne : delta ≤ 1)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹))
    (depthLe : schedule.levelCount ≤ depthBound) :
    input.terminalMassRetentionLoss
        multiplicity parentClass treeCleanup exactification
          parentDegree core good ≤
      canonicalMassRetentionCoefficient depthBound *
        (ENNReal.ofReal
          (fineLogEnvelopeCoefficient logCoefficient *
            (1 + Real.log delta⁻¹))) ^ 14 := by
  let dyadicLoss : ENNReal :=
    (multiplicity.binCount : ENNReal) *
      parentClass.weightBinCount *
      parentClass.fiberBinCount
  let degreeBinLoss : ENNReal :=
    (bins.fineCellBin.binCount : ENNReal) *
      bins.parentCoarseBin.binCount *
      bins.coarseCellBin.binCount
  let A0 : ENNReal :=
    input.canonicalPeelingA0
      multiplicity parentClass treeCleanup exactification bins
  let envelope : ENNReal :=
    ENNReal.ofReal
      (fineLogEnvelopeCoefficient logCoefficient *
        (1 + Real.log delta⁻¹))
  let depthCoefficient : ENNReal :=
    ENNReal.ofReal (8 * (depthBound + 2) * 8 ^ 4 : ℝ)
  have dyadicBound : dyadicLoss ≤ 4 * envelope ^ 3 := by
    simpa only [dyadicLoss, envelope] using
      input.prebalanceDyadicProduct_le_logCube_of_fineLog
        multiplicity parentClass deltaLeOne boundaryCoefficientLe
          fineLogBound
  have degreeBinBound : degreeBinLoss ≤ 8 * envelope ^ 3 := by
    simpa only [degreeBinLoss, envelope] using
      input.threeDegreeBinProduct_le_logCube_of_fineLog
        multiplicity parentClass treeCleanup exactification
          deltaLeOne boundaryCoefficientLe fineLogBound
  have A0Bound : A0 ≤ depthCoefficient * envelope ^ 4 := by
    simpa only [A0, depthCoefficient, envelope] using
      input.canonicalPeelingA0_le_logFourthENN_of_fineLog
        multiplicity parentClass treeCleanup exactification
          (bins := bins) depthBound depthLe deltaLeOne
          boundaryCoefficientLe fineLogBound
  have treeBound :
      (2 : ENNReal) ^ (schedule.levelCount + 1) ≤
        (2 : ENNReal) ^ (depthBound + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have degreeLossEq :
      (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree : ENNReal) =
        8 * A0 ^ 2 := by
    simp [
      FourDegreeCoreAssemblyData.balancingDegreeLoss,
      FourDegreeCoreAssemblyData.balancingRateLoss,
      A0, Nat.cast_mul, Nat.cast_pow
    ]
    ring
  calc
    input.terminalMassRetentionLoss
          multiplicity parentClass treeCleanup exactification
            parentDegree core good =
        dyadicLoss *
          (2 : ENNReal) ^ (schedule.levelCount + 1) *
          4 * degreeBinLoss *
          (core.balancingDegreeLoss
            input multiplicity parentClass treeCleanup
              exactification parentDegree : ENNReal) := by
      simp [PureWZ2Prop62PacketCellInput.terminalMassRetentionLoss,
        dyadicLoss, degreeBinLoss]
      ring
    _ =
        dyadicLoss *
          (2 : ENNReal) ^ (schedule.levelCount + 1) *
          4 * degreeBinLoss * (8 * A0 ^ 2) := by
      rw [degreeLossEq]
    _ ≤
        (4 * envelope ^ 3) *
          ((2 : ENNReal) ^ (depthBound + 1)) *
          4 * (8 * envelope ^ 3) *
          (8 * (depthCoefficient * envelope ^ 4) ^ 2) := by
      gcongr
    _ =
        canonicalMassRetentionCoefficient depthBound *
          envelope ^ 14 := by
      simp only [canonicalMassRetentionCoefficient, depthCoefficient]
      ring

def canonicalMassRetentionLogCoefficientOfFineLog
    (depthBound : ℕ) (logCoefficient : ℝ) : ℝ :=
  max
    (canonicalMassRetentionCoefficient depthBound).toReal
    (fineLogEnvelopeCoefficient logCoefficient)

theorem canonicalMassRetentionLogCoefficientOfFineLog_nonneg
    (depthBound : ℕ)
    (logCoefficient : ℝ) :
    0 ≤ canonicalMassRetentionLogCoefficientOfFineLog
      depthBound logCoefficient :=
  ENNReal.toReal_nonneg.trans <| le_max_left _ _

theorem exists_canonicalMassRetentionThresholdOfFineLog
    (depthBound : ℕ)
    (logCoefficient : ℝ) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 / 2 ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₀ →
          3 ≤ Real.log delta⁻¹ ∧
            canonicalMassRetentionLogCoefficientOfFineLog
                depthBound logCoefficient *
                (1 + Real.log delta⁻¹) ≤
              (Real.log delta⁻¹) ^ 2 := by
  rcases
      exists_delta_boundary_log_square
        (canonicalMassRetentionLogCoefficientOfFineLog
          depthBound logCoefficient)
        (canonicalMassRetentionLogCoefficientOfFineLog_nonneg
          depthBound logCoefficient)
    with ⟨threshold, thresholdPos, thresholdLeOne, absorbed⟩
  let delta₀ := min threshold (1 / 2 : ℝ)
  refine
    ⟨delta₀, lt_min thresholdPos (by norm_num),
      min_le_right _ _, ?_⟩
  intro delta deltaPos deltaLe
  exact absorbed delta deltaPos <|
    deltaLe.trans (min_le_left _ _)

noncomputable def canonicalMassRetentionThresholdOfFineLog
    (depthBound : ℕ)
    (logCoefficient : ℝ) : ℝ :=
  Classical.choose <|
    exists_canonicalMassRetentionThresholdOfFineLog
      depthBound logCoefficient

theorem massRetentionAbsorption_fifty_of_smallDelta_of_fineLog
    (good :
      core.ranges.GoodBalancingSampleData
        (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree))
    (depthBound : ℕ)
    {logCoefficient : ℝ}
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹))
    (depthLe : schedule.levelCount ≤ depthBound)
    (deltaLe :
      delta ≤
        canonicalMassRetentionThresholdOfFineLog
          depthBound logCoefficient) :
    input.MassRetentionAbsorptionData
      multiplicity parentClass treeCleanup exactification
        parentDegree core good 50 := by
  let coefficient : ENNReal :=
    canonicalMassRetentionCoefficient depthBound
  let envelope : ENNReal :=
    ENNReal.ofReal
      (fineLogEnvelopeCoefficient logCoefficient *
        (1 + Real.log delta⁻¹))
  let logTerm : ENNReal :=
    ENNReal.ofReal (Real.log (1 / delta))
  have thresholdData :=
    (Classical.choose_spec <|
      exists_canonicalMassRetentionThresholdOfFineLog
        depthBound logCoefficient).2.2
      delta input.delta_pos deltaLe
  have deltaLtOne : delta < 1 := by
    exact deltaLe.trans_lt <|
      (Classical.choose_spec <|
        exists_canonicalMassRetentionThresholdOfFineLog
          depthBound logCoefficient).2.1.trans_lt
        (by norm_num)
  have lossBound :
      input.terminalMassRetentionLoss
          multiplicity parentClass treeCleanup exactification
            parentDegree core good ≤
        coefficient * envelope ^ 14 := by
    simpa only [coefficient, envelope] using
      core.canonicalTerminalMassRetentionLoss_le_logFourteen_of_fineLog
        input multiplicity parentClass treeCleanup exactification
          parentDegree good depthBound deltaLtOne.le
          boundaryCoefficientLe fineLogBound depthLe
  have logIdentity :
      Real.log (1 / delta) = Real.log delta⁻¹ := by
    congr 1
    field_simp [input.delta_pos.ne']
  have logRealNonnegative : 0 ≤ Real.log delta⁻¹ := by
    linarith [thresholdData.1]
  have logTermOne : (1 : ENNReal) ≤ logTerm := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_mono <| by
      rw [logIdentity]
      linarith [thresholdData.1]
  have coefficientFinite : coefficient ≠ ⊤ :=
    canonicalMassRetentionCoefficient_ne_top depthBound
  have coefficientRepresentation :
      coefficient = ENNReal.ofReal coefficient.toReal :=
    (ENNReal.ofReal_toReal coefficientFinite).symm
  have coefficientBound : coefficient ≤ logTerm ^ 2 := by
    calc
      coefficient = ENNReal.ofReal coefficient.toReal :=
        coefficientRepresentation
      _ ≤
          ENNReal.ofReal
            (canonicalMassRetentionLogCoefficientOfFineLog
                depthBound logCoefficient *
              (1 + Real.log delta⁻¹)) := by
        apply ENNReal.ofReal_mono
        have logFactorOne : 1 ≤ 1 + Real.log delta⁻¹ := by
          linarith
        calc
          coefficient.toReal ≤
              canonicalMassRetentionLogCoefficientOfFineLog
                depthBound logCoefficient :=
            le_max_left _ _
          _ ≤
              canonicalMassRetentionLogCoefficientOfFineLog
                  depthBound logCoefficient *
                (1 + Real.log delta⁻¹) := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left logFactorOne
                (canonicalMassRetentionLogCoefficientOfFineLog_nonneg
                  depthBound logCoefficient)
      _ ≤ ENNReal.ofReal ((Real.log delta⁻¹) ^ 2) :=
        ENNReal.ofReal_mono thresholdData.2
      _ = logTerm ^ 2 := by
        dsimp only [logTerm]
        rw [logIdentity]
        exact ENNReal.ofReal_pow logRealNonnegative 2
  have envelopeBound : envelope ≤ logTerm ^ 2 := by
    calc
      envelope ≤
          ENNReal.ofReal
            (canonicalMassRetentionLogCoefficientOfFineLog
                depthBound logCoefficient *
              (1 + Real.log delta⁻¹)) := by
        apply ENNReal.ofReal_mono
        exact mul_le_mul_of_nonneg_right
          (le_max_right _ _) (by linarith)
      _ ≤ ENNReal.ofReal ((Real.log delta⁻¹) ^ 2) :=
        ENNReal.ofReal_mono thresholdData.2
      _ = logTerm ^ 2 := by
        dsimp only [logTerm]
        rw [logIdentity]
        exact ENNReal.ofReal_pow logRealNonnegative 2
  have lossPower :
      input.terminalMassRetentionLoss
          multiplicity parentClass treeCleanup exactification
            parentDegree core good ≤
        logTerm ^ 30 := by
    calc
      input.terminalMassRetentionLoss
            multiplicity parentClass treeCleanup exactification
              parentDegree core good ≤
          coefficient * envelope ^ 14 := lossBound
      _ ≤ (logTerm ^ 2) * (logTerm ^ 2) ^ 14 := by
        gcongr
      _ = logTerm ^ 30 := by ring
  have lossFifty :
      input.terminalMassRetentionLoss
          multiplicity parentClass treeCleanup exactification
            parentDegree core good ≤
        logTerm ^ 50 :=
    lossPower.trans <| pow_le_pow_right₀ logTermOne (by norm_num)
  have logTermZero : logTerm ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le logTermOne)
  have logTermTop : logTerm ≠ ⊤ := by
    dsimp only [logTerm]
    exact ENNReal.ofReal_ne_top
  constructor
  calc
    wz2PaperPureRefinementFraction delta 50 *
          input.terminalMassRetentionLoss
            multiplicity parentClass treeCleanup exactification
              parentDegree core good ≤
        wz2PaperPureRefinementFraction delta 50 * logTerm ^ 50 := by
      gcongr
    _ = (logTerm ^ 50)⁻¹ * logTerm ^ 50 := by
      simp [wz2PaperPureRefinementFraction, logTerm,
        ENNReal.inv_pow]
    _ = 1 :=
      ENNReal.inv_mul_cancel
        (pow_ne_zero 50 logTermZero)
        (ENNReal.pow_ne_top logTermTop)

end FourDegreeCoreAssemblyData

structure CanonicalFourDegreeProducerData
    (fiberConstant densityConstant : ENNReal) where
  initial : input.FourDegreePrefixData schedule
  core :
    input.FourDegreeCoreAssemblyData
      initial.multiplicity initial.parentClass initial.treeCleanup
        initial.exactification initial.parentDegree initial.bins
        (input.canonicalPeelingA0
          initial.multiplicity initial.parentClass initial.treeCleanup
            initial.exactification initial.bins)
  families :
    input.TerminalCompleteFamiliesData
      initial.multiplicity initial.parentClass initial.treeCleanup
        initial.exactification core.ranges
  output :
    core.CanonicalFourDegreeOutputData
      input initial.multiplicity initial.parentClass initial.treeCleanup
        initial.exactification initial.parentDegree families
        fiberConstant densityConstant 50

theorem pureWZ2_prop62_canonical_four_degree_producer_fifty
    {depthBound : ℕ}
    {densityExponent lossExponent packetExponent : ℝ}
    {fiberConstant : ENNReal}
    (small :
      PrebalanceSmallData
        delta depthBound densityExponent lossExponent)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4)
    (depthLe : schedule.levelCount ≤ depthBound)
    (balancingExponentGap :
      densityExponent + lossExponent < 1)
    (packetExponentGap : densityExponent < packetExponent)
    (packetDeltaLe :
      delta ≤
        FourDegreeCoreAssemblyData.canonicalPacketDensityThreshold
          depthBound densityExponent packetExponent packetExponentGap)
    (massDeltaLe :
      delta ≤
        FourDegreeCoreAssemblyData.canonicalMassRetentionThreshold
          depthBound)
    (density :
      Kakeya.realRpowENN delta densityExponent *
          fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass) :
    Nonempty
      (CanonicalFourDegreeProducerData
        (input := input) (schedule := schedule)
        fiberConstant (Kakeya.realRpowENN delta packetExponent)) := by
  rcases
      PureWZ2Prop62PacketCellInput.pureWZ2_prop62_four_degree_prefix
        input schedule
    with
    ⟨initial⟩
  rcases
      input.pureWZ2_prop62_canonical_four_degree_core_assembly
        initial.multiplicity initial.parentClass initial.treeCleanup
          initial.exactification initial.parentDegree initial.bins
    with ⟨core⟩
  have terminalEdgesNonempty : core.ranges.terminalEdges.Nonempty := by
    unfold PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.terminalEdges
    rw [core.ranges_peeling_eq]
    exact core.core_nonempty
  rcases
      input.pureWZ2_prop62_terminal_complete_families
        initial.multiplicity initial.parentClass initial.treeCleanup
          initial.exactification core.ranges terminalEdgesNonempty
    with ⟨families⟩
  rcases
      core.pureWZ2_prop62_canonical_four_degree_output_fifty_of_prebalanceSmall
        input initial.multiplicity initial.parentClass initial.treeCleanup
          initial.exactification initial.parentDegree families
        small fineNonempty fineDistinct fineBoundedBase depthLe
          balancingExponentGap packetExponentGap
          packetDeltaLe massDeltaLe density
    with ⟨output⟩
  exact
    ⟨{
      initial := initial
      core := core
      families := families
      output := output
    }⟩

/--
The canonical four-degree producer driven by an external logarithmic
cardinality estimate and an external one-pass cleanup oracle.  In particular,
this route does not require global ordinary distinctness or bounded-base data
for the fine family.
-/
theorem pureWZ2_prop62_canonical_four_degree_producer_fifty_of_fineLog
    {depthBound : ℕ}
    {densityExponent lossExponent packetExponent logCoefficient : ℝ}
    {fiberConstant : ENNReal}
    (cleanupOracle : PureWZ2Prop62CleanupOracle)
    (small :
      PrebalanceSmallDataOfFineLog
        delta depthBound densityExponent lossExponent logCoefficient)
    (logCoefficientOne : 1 ≤ logCoefficient)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹))
    (depthLe : schedule.levelCount ≤ depthBound)
    (balancingExponentGap :
      densityExponent + lossExponent < 1)
    (packetExponentGap : densityExponent < packetExponent)
    (packetDeltaLe :
      delta ≤
        FourDegreeCoreAssemblyData.canonicalPacketDensityThresholdOfFineLog
          depthBound densityExponent packetExponent logCoefficient
            logCoefficientOne packetExponentGap)
    (massDeltaLe :
      delta ≤
        FourDegreeCoreAssemblyData.canonicalMassRetentionThresholdOfFineLog
          depthBound logCoefficient)
    (density :
      Kakeya.realRpowENN delta densityExponent *
          fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass) :
    Nonempty
      (CanonicalFourDegreeProducerData
        (input := input) (schedule := schedule)
        fiberConstant (Kakeya.realRpowENN delta packetExponent)) := by
  rcases
      input.pureWZ2_prop62_four_degree_prefix_of_cleanupOracle
        schedule cleanupOracle
    with
    ⟨initial⟩
  rcases
      input.pureWZ2_prop62_canonical_four_degree_core_assembly
        initial.multiplicity initial.parentClass initial.treeCleanup
          initial.exactification initial.parentDegree initial.bins
    with ⟨core⟩
  have terminalEdgesNonempty : core.ranges.terminalEdges.Nonempty := by
    unfold PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.terminalEdges
    rw [core.ranges_peeling_eq]
    exact core.core_nonempty
  rcases
      input.pureWZ2_prop62_terminal_complete_families
        initial.multiplicity initial.parentClass initial.treeCleanup
          initial.exactification core.ranges terminalEdgesNonempty
    with ⟨families⟩
  have logSmall :
      core.BalancingAmbientLogSmallData
        input initial.multiplicity initial.parentClass initial.treeCleanup
          initial.exactification initial.parentDegree :=
    core.balancingAmbientLogSmallData_of_fineLog
      input initial.multiplicity initial.parentClass initial.treeCleanup
        initial.exactification initial.parentDegree
      small boundaryCoefficientLe fineLogBound depthLe
        balancingExponentGap density
  have packetAbsorption :
      ∀ good :
          core.ranges.GoodBalancingSampleData
            (core.balancingDegreeLoss
              input initial.multiplicity initial.parentClass
                initial.treeCleanup initial.exactification
                initial.parentDegree),
        TerminalFineShading.PacketDensityAbsorptionData
          input initial.multiplicity initial.parentClass initial.treeCleanup
            initial.exactification initial.parentDegree core good
            (Kakeya.realRpowENN delta packetExponent) := by
    intro good
    exact
      core.packetDensityAbsorption_of_smallDelta_of_fineLog
        input initial.multiplicity initial.parentClass initial.treeCleanup
          initial.exactification initial.parentDegree good
        logCoefficientOne boundaryCoefficientLe fineLogBound depthLe
          packetExponentGap packetDeltaLe density
  have massAbsorption :
      ∀ good :
          core.ranges.GoodBalancingSampleData
            (core.balancingDegreeLoss
              input initial.multiplicity initial.parentClass
                initial.treeCleanup initial.exactification
                initial.parentDegree),
        input.MassRetentionAbsorptionData
          initial.multiplicity initial.parentClass initial.treeCleanup
            initial.exactification initial.parentDegree core good 50 := by
    intro good
    exact
      core.massRetentionAbsorption_fifty_of_smallDelta_of_fineLog
        input initial.multiplicity initial.parentClass initial.treeCleanup
          initial.exactification initial.parentDegree good depthBound
          boundaryCoefficientLe fineLogBound depthLe massDeltaLe
  rcases
      core.pureWZ2_prop62_canonical_four_degree_output_of_ambientLog
        input initial.multiplicity initial.parentClass initial.treeCleanup
          initial.exactification initial.parentDegree families
          logSmall packetAbsorption massAbsorption
    with ⟨output⟩
  exact
    ⟨{
      initial := initial
      core := core
      families := families
      output := output
    }⟩

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
