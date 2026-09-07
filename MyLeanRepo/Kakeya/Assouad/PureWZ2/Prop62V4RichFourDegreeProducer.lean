import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4RichCertificateCompanion
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4FourDegreeThresholdCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4ParentCWABound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4RegularityBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4SchedulePower
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4TwoLayerCardinality
import Mathlib.Tactic

/-!
# Proposition 6.2 V4 rich four-degree producer

This module repeats the current scalar choices of
`four_degree_packet_core_closed`, but runs the ordinary canonical producer on
the deterministic metric projection of a rich Target-3 certificate.  The
result keeps the canonical producer and all pure coarse/fiber receipts in one
dependent companion.

No historical paper-metric target is invoked, and no final Proposition 6.2
assembly is performed here.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The current Target-4 CWA loss exponent. -/
def pureWZ2Prop62RichFourDegreeCWALossExponent
    (inputDensityExponent inputCWAExponent : ℕ) : ℕ :=
  2 * inputDensityExponent + 5 * inputCWAExponent + 9

/-- The logarithmic coefficient used by the current Target-4 threshold. -/
def pureWZ2Prop62RichFourDegreeLogCoefficient : ℝ :=
  max PureWZ2Prop62PacketCellInput.prebalanceLogCoefficient
    pureWZ2Prop62TwoLayerCardLogConstant

/-- The tube-mass constant used by the current Target-4 threshold. -/
def pureWZ2Prop62RichFourDegreeTubeMassConstant : ENNReal :=
  55296 * Kakeya.deltaTubeVolume 1

theorem pureWZ2Prop62RichFourDegreeLogCoefficient_one :
    1 ≤ pureWZ2Prop62RichFourDegreeLogCoefficient := by
  unfold pureWZ2Prop62RichFourDegreeLogCoefficient
  exact le_trans
    PureWZ2Prop62PacketCellInput.one_le_prebalanceLogCoefficient
    (le_max_left _ _)

theorem pureWZ2Prop62RichFourDegreeTubeMassConstant_ne_top :
    pureWZ2Prop62RichFourDegreeTubeMassConstant ≠ ⊤ := by
  unfold pureWZ2Prop62RichFourDegreeTubeMassConstant
  exact ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top

/--
Run the canonical Target-4 producer on the deterministic metric projection of
one rich Target-3 certificate.

The exponents and threshold are exactly the current choices in
`four_degree_packet_core_closed`:

* polylog exponent `10`;
* packet-density exponent `D + 1`;
* CWA-loss exponent `2 * D + 5 * B + 9`;
* `pureWZ2Prop62FourDegreeThresholdCore` with the current logarithmic and
  tube-mass constants.
-/
theorem exists_prop62V4RichCertificateCompanion
    (cleanupOracle : PureWZ2Prop62CleanupOracle)
    (inputDensityExponent inputCWAExponent : ℕ)
    (eta : ℝ)
    (eta_pos : 0 < eta)
    (packetExponent_lt_one :
      (pureWZ2Prop62FourDegreePacketDensityExponent
          inputDensityExponent : ℝ) * eta < 1) :
    let packetDensityExponent :=
      pureWZ2Prop62FourDegreePacketDensityExponent inputDensityExponent
    let cwaLossExponent :=
      pureWZ2Prop62RichFourDegreeCWALossExponent
        inputDensityExponent inputCWAExponent
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 / 100 ∧
      ∀ (delta : ℝ), ∀ (hdelta : 0 < delta),
        delta ≤ delta₀ →
        ∀ (source : Kakeya.Streamlined.TubeFamily delta),
          ∀ (sourceShading : WZ1PaperTubeShading source),
            ∀ (rho : Kakeya.Streamlined.AdmissibleScale delta),
              ∀ (fineParentDistanceConstant : ℝ),
                ∀ (parentConstant fiberConstant : ENNReal),
                  ∀ (metricCompanion :
                      Prop62V4MetricParentsRichCompanionData
                        sourceShading rho fineParentDistanceConstant
                          parentConstant fiberConstant),
                    parentConstant ≤
                        Kakeya.realRpowENN delta
                          (-(inputCWAExponent : ℝ) * eta) →
                    fiberConstant ≤
                        Kakeya.realRpowENN delta
                          (-(inputCWAExponent : ℝ) * eta) →
                    metricCompanion.metric.refinement.refined.IsLambdaDense
                        (Kakeya.realRpowENN delta
                          ((inputDensityExponent : ℝ) * eta)) →
                    (∀ sourceIndex cell,
                      wz1PaperGridCube delta cell ⊆
                          metricCompanion.metric.refinement.refined.carrier
                            sourceIndex →
                        ∃! coarseCell,
                          wz1PaperGridCube delta cell ⊆
                              wz1PaperGridCube rho.1 coarseCell ∧
                            wz1PaperGridCube rho.1 coarseCell ⊆
                              wz1PaperTubeCarrier
                                (metricCompanion.metric.scaleData.coarse.tube
                                  (metricCompanion.metric.scaleData.cover.parent
                                    sourceIndex))) →
                      Nonempty
                        (Prop62V4RichCertificateCompanionData
                          (eta := eta)
                          (packetDensityExponent := packetDensityExponent)
                          (cwaLossExponent := cwaLossExponent)
                          (polylogExponent :=
                            pureWZ2Prop62FourDegreePolylogExponent)
                          hdelta metricCompanion) := by
  dsimp only
  let logCoefficient := pureWZ2Prop62RichFourDegreeLogCoefficient
  let tubeMassConstant := pureWZ2Prop62RichFourDegreeTubeMassConstant
  let threshold :=
    pureWZ2Prop62FourDegreeThresholdCore
      inputDensityExponent inputCWAExponent eta logCoefficient
      tubeMassConstant eta_pos packetExponent_lt_one
      pureWZ2Prop62RichFourDegreeLogCoefficient_one
      pureWZ2Prop62RichFourDegreeTubeMassConstant_ne_top
  refine
    ⟨threshold.delta0, threshold.delta0_pos,
      threshold.delta0_le_one_hundred, ?_⟩
  intro delta hdelta deltaLe source sourceShading rho
    fineParentDistanceConstant parentConstant fiberConstant
    metricCompanion parentConstantLe fiberConstantLe refinedDense coarseCell
  let metric := metricCompanion.metric
  let localInput : MetricParentsV4PacketCellLocalInput metric :=
    {
      delta_pos := hdelta
      delta_le_one_hundred :=
        deltaLe.trans threshold.delta0_le_one_hundred
      densityConstant :=
        Kakeya.realRpowENN delta
          ((inputDensityExponent : ℝ) * eta)
      densityConstant_pos := by
        simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hdelta]
      refined_dense := refinedDense
      coarse_cell := coarseCell
    }
  let packetInput := localInput.toPacketCellInput
  have deltaLeOne :
      delta ≤ 1 :=
    (deltaLe.trans threshold.delta0_le_one_hundred).trans (by norm_num)
  have fineLog :
      (Nat.log 2
          (2 * metric.refinement.selected.family.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹) := by
    have raw :=
      MetricParentsAtPrescribedScaleData.fineLog_le_twoLayer
        metric
    have coefficientLe :
        pureWZ2Prop62TwoLayerCardLogConstant ≤ logCoefficient := by
      unfold logCoefficient pureWZ2Prop62RichFourDegreeLogCoefficient
      exact le_max_right _ _
    have logNonnegative : 0 ≤ Real.log delta⁻¹ := by
      exact Real.log_nonneg ((one_le_inv₀ hdelta).mpr deltaLeOne)
    exact raw.trans <| by
      gcongr
  have boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient := by
    calc
      wz2PaperBoundaryLogCoefficient ≤
          wz2PaperBoundaryLogCoefficient + 1 := by linarith
      _ ≤ PureWZ2Prop62PacketCellInput.prebalanceLogCoefficient := by
        exact le_max_right _ _
      _ ≤ logCoefficient := by
        unfold logCoefficient pureWZ2Prop62RichFourDegreeLogCoefficient
        exact le_max_left _ _
  have scheduleDeltaLe :
      delta ≤ threshold.schedulePower.delta0 :=
    threshold.schedule_delta_le hdelta deltaLe
  let scheduleData :=
    metric.fourDegreeSchedulePowerData
      threshold.schedulePower eta_pos hdelta scheduleDeltaLe
        (by simpa only [neg_mul] using parentConstantLe)
  let schedule := scheduleData.schedule
  have balancingExponentGap :
      (inputDensityExponent : ℝ) * eta +
          pureWZ2Prop62FourDegreePrebalanceLossExponent eta < 1 := by
    unfold pureWZ2Prop62FourDegreePrebalanceLossExponent
    have packetBound :
        ((inputDensityExponent : ℝ) + 1) * eta < 1 := by
      simpa [pureWZ2Prop62FourDegreePacketDensityExponent,
        Nat.cast_add, Nat.cast_one] using packetExponent_lt_one
    nlinarith
  have density :
      Kakeya.realRpowENN delta
            ((inputDensityExponent : ℝ) * eta) *
          metric.refinement.selected.family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        metric.refinement.refined.mass := by
    calc
      Kakeya.realRpowENN delta
              ((inputDensityExponent : ℝ) * eta) *
            metric.refinement.selected.family.enncard *
            Kakeya.realRpowENN delta 2 =
          Kakeya.realRpowENN delta
              ((inputDensityExponent : ℝ) * eta) *
            (metric.refinement.selected.family.enncard *
              Kakeya.realRpowENN delta 2) := by ring
      _ ≤
          Kakeya.realRpowENN delta
              ((inputDensityExponent : ℝ) * eta) *
            (wz1PaperBodyFamily
              metric.refinement.selected.family).mass := by
        gcongr
        exact
          pureWZ2_prop62_paper_body_mass_lower
            hdelta
            ((deltaLe.trans threshold.delta0_le_one_hundred).trans
              (by norm_num))
            metric.scaleData.section6Cover.fine_line_class
      _ ≤ metric.refinement.refined.mass := refinedDense
  rcases
      packetInput.pureWZ2_prop62_canonical_four_degree_producer_fifty_of_fineLog
        (schedule := schedule)
        (fiberConstant := fiberConstant)
        cleanupOracle
        (threshold.prebalance_small hdelta deltaLe)
        pureWZ2Prop62RichFourDegreeLogCoefficient_one
        boundaryCoefficientLe fineLog scheduleData.levelCount_le
        balancingExponentGap threshold.packet_exponent_gap
        (threshold.packet_density_small hdelta deltaLe)
        (threshold.mass_retention_small hdelta deltaLe)
        density
    with ⟨producer⟩
  let outputConstant :=
    Kakeya.realRpowENN delta
      (-(pureWZ2Prop62RichFourDegreeCWALossExponent
          inputDensityExponent inputCWAExponent : ℝ) * eta)
  have outputConstantFinite : outputConstant ≠ ⊤ := by
    simp [outputConstant, Kakeya.realRpowENN]
  have fiberConstantOutput :
      fiberConstant ≤ outputConstant := by
    refine fiberConstantLe.trans ?_
    apply pure_wz2_rpowENN_antitone hdelta deltaLeOne
    unfold pureWZ2Prop62RichFourDegreeCWALossExponent
    push_cast
    nlinarith [eta_pos]
  have scheduleAmbientConstantLe :
      pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
          inputCWAExponent eta delta ≤
        Kakeya.realRpowENN delta
          (-((inputCWAExponent : ℝ) + 1) * eta) := by
    unfold pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
      pureWZ2Prop62MetricParentsV4FourDegreeScheduleStep
    apply le_of_eq
    congr 1
    ring
  have scaleWindowPower :
      pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
            inputCWAExponent eta delta *
          ENNReal.ofReal
            (pureWZ2Prop62MetricParentsV4FourDegreeRatio
              inputCWAExponent eta delta) ≤
        pureWZ2Prop62FourDegreeCWATarget delta eta
          inputDensityExponent inputCWAExponent := by
    refine scheduleData.scaleWindow_le.trans ?_
    apply pure_wz2_rpowENN_antitone hdelta deltaLeOne
    dsimp only [pureWZ2Prop62MetricParentsV4FourDegreeWindowPower,
      pureWZ2Prop62FourDegreeCWATarget,
      pureWZ2Prop62FourDegreeCWALossExponent
    ]
    push_cast
    nlinarith [eta_pos]
  have parentStructural :
      ((2 ^ schedule.levelCount *
            packetInput.canonicalPeelingA0
              producer.initial.multiplicity producer.initial.parentClass
              producer.initial.treeCleanup producer.initial.exactification
              producer.initial.bins : ℕ) : ENNReal) *
          (2 *
            ((producer.initial.multiplicity.binCount : ENNReal) *
              producer.initial.parentClass.weightBinCount *
              producer.initial.parentClass.fiberBinCount) *
            tubeMassConstant) ≤
        Kakeya.realRpowENN delta (-3 * eta) :=
    threshold.terminalParentStructuralAbsorption
      packetInput producer.initial.multiplicity producer.initial.parentClass
      producer.initial.treeCleanup producer.initial.exactification
      producer.initial.parentDegree producer.initial.bins
      scheduleData.levelCount_le boundaryCoefficientLe fineLog hdelta deltaLe
  have parentBound :=
    localInput.terminalParentCWA_power_bound
      schedule producer.initial producer.core producer.families eta
      inputDensityExponent inputCWAExponent rfl parentConstantLe
      scheduleAmbientConstantLe scaleWindowPower parentStructural
  have oldTargetLeOutput :
      pureWZ2Prop62FourDegreeCWATarget
          delta eta inputDensityExponent inputCWAExponent ≤
        outputConstant := by
    apply pure_wz2_rpowENN_antitone hdelta deltaLeOne
    dsimp only [pureWZ2Prop62FourDegreeCWATarget,
      pureWZ2Prop62FourDegreeCWALossExponent,
      pureWZ2Prop62RichFourDegreeCWALossExponent
    ]
    push_cast
    nlinarith [eta_pos]
  have producerParentOutputBound :
      producer.output.output.parentConstant ≤ outputConstant := by
    rw [producer.output.output.parentConstant_eq]
    exact parentBound.1.trans oldTargetLeOutput
  have regularityBound :
      (producer.output.output.coarseLoss : ENNReal) ≤
        logarithmicLoss delta ^
          pureWZ2Prop62FourDegreePolylogExponent := by
    rw [producer.output.output.coarseLoss_eq]
    exact
      threshold.terminalCoarseMultiplicityLoss_le_logTen
        packetInput producer.initial.multiplicity
        producer.initial.parentClass producer.initial.treeCleanup
        producer.initial.exactification producer.initial.parentDegree
        producer.initial.bins producer.core
        pureWZ2Prop62RichFourDegreeLogCoefficient_one
        boundaryCoefficientLe fineLog scheduleData.levelCount_le hdelta deltaLe
  let fourDegree :=
    prop62V4FourDegreeCompanion_ofCanonicalProducer
      localInput schedule producer producerParentOutputBound
      fiberConstantOutput regularityBound
  exact
    ⟨prop62V4RichCertificateCompanion metricCompanion fourDegree⟩

end Kakeya.Assouad.Prop62PaperAudit.V4

end
