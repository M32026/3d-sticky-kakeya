import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichHierarchyProducer

/-!
# Proposition 6.4 final nearby-CWA scalar absorption

The authoritative `wz2_64.tex` proof chooses `N`, hence `epsilon₂ = N⁻¹`,
and every small-scale cutoff before the runtime source family.  The exact
same joint paper-ED and transported combined selection must then supply all
nearby-scale covers.

The final actual-John constant contains only fixed coefficients, two
ordinary-family logarithms, and explicit source powers.  The conservative
ledger used here reserves `48 * epsilon₂` for those source powers and
`4 * N + 10` copies of the common logarithmic envelope.  The remaining
strict gap to `nearbyLoss` absorbs the fixed coefficient and all logarithms
before `sourceDelta` and the runtime family are selected.
-/

noncomputable section

namespace Kakeya.Assouad

open PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

def pureWZ2Node05P7ScalePowerLoss
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal) : ℝ :=
  48 * schedule.ordinary.mild.epsilon₂

def pureWZ2Node05P7ScaleLogPower
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal) : ℕ :=
  4 * pureWZ2Prop62RequestedScaleLevelCount schedule.p7Scale.gridLoss + 10

theorem pureWZ2Node05P7ScaleLogPower_pos
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal) :
    0 < pureWZ2Node05P7ScaleLogPower schedule := by
  unfold pureWZ2Node05P7ScaleLogPower
  omega

theorem pureWZ2Node05P7ScalePowerGap_pos
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal) :
    0 < schedule.p7Scale.nearbyLoss -
      pureWZ2Node05P7ScalePowerLoss schedule := by
  unfold pureWZ2Node05P7ScalePowerLoss
  linarith [schedule.p7ScalePowerLoss_lt_nearby]

def pureWZ2Node05P7ScaleCoordinateCount
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal) : ℕ :=
  pureWZ2Prop62RequestedScaleLevelCount schedule.p7Scale.gridLoss

noncomputable def pureWZ2Node05P7ScaleLogEnvelope
    (sourceDelta : ℝ) : ENNReal :=
  ENNReal.ofReal
    (pureWZ2BoundedSourceCardLogConstant *
      (1 + Real.log sourceDelta⁻¹))

theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_initialCardLog_le_envelope
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual)
    (frostman :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.SelectedSourceFrostmanReceipt
        p6.geometry) :
    let initialED :=
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalPaperED
        p6.normalized p6.geometry frostman
    (Nat.log 2 (2 * initialED.subfamily.family.card) + 1 : ENNReal) ≤
      pureWZ2Node05P7ScaleLogEnvelope sourceDelta := by
  dsimp only
  have hreal := (p6.p7_cardLog_bounds frostman).1
  have hconverted := ENNReal.ofReal_mono hreal
  have hcast :
      ENNReal.ofReal
          (Nat.log 2
              (2 *
                (PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalPaperED
                  p6.normalized p6.geometry frostman).subfamily.family.card) +
            1 : ℝ) =
        (Nat.log 2
              (2 *
                (PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalPaperED
                  p6.normalized p6.geometry frostman).subfamily.family.card) +
            1 : ENNReal) := by
    norm_cast
  simpa only [pureWZ2Node05P7ScaleLogEnvelope, hcast] using hconverted

theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_positiveCardLog_le_envelope
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual)
    (frostman :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.SelectedSourceFrostmanReceipt
        p6.geometry) :
    (Nat.log 2
        (2 *
          (paperPositiveMassSubfamily
            p6.geometry.cleanup.finalShading).family.card) + 1 : ENNReal) ≤
      pureWZ2Node05P7ScaleLogEnvelope sourceDelta := by
  have hreal := (p6.p7_cardLog_bounds frostman).2
  have hconverted := ENNReal.ofReal_mono hreal
  have hcast :
      ENNReal.ofReal
          (Nat.log 2
              (2 *
                (paperPositiveMassSubfamily
                  p6.geometry.cleanup.finalShading).family.card) + 1 : ℝ) =
        (Nat.log 2
              (2 *
                (paperPositiveMassSubfamily
                  p6.geometry.cleanup.finalShading).family.card) + 1 :
            ENNReal) := by
    norm_cast
  simpa only [pureWZ2Node05P7ScaleLogEnvelope, hcast] using hconverted

noncomputable def pureWZ2Node05P7CleanupCoefficient : ENNReal :=
  8 * (ENNReal.ofReal pureWZ2Node05P7ConflictCoefficient + 1)

theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_cleanupLoss_le_envelope
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual)
    (frostman :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.SelectedSourceFrostmanReceipt
        p6.geometry) :
    PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalPaperEDLoss
        p6.normalized p6.geometry ≤
      pureWZ2Node05P7CleanupCoefficient *
        pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^ 2 *
        Kakeya.realRpowENN sourceDelta
          (-18 * schedule.ordinary.mild.epsilon₂) := by
  let power :=
    Kakeya.realRpowENN sourceDelta
      (-18 * schedule.ordinary.mild.epsilon₂)
  have hpowerOne : (1 : ENNReal) ≤ power := by
    dsimp only [power, Kakeya.realRpowENN]
    rw [ENNReal.one_le_ofReal]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      p6.normalized.normalized.source.extremal.delta_pos
      p6.normalized.normalized.source.extremal.delta_le_one
      (by linarith [schedule.ordinary.mild.epsilon₂_pos])
  have hconflict := p6.p7_conflictDegree_le_source_power
  have hconflictOne :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalJointPaperEDConflictLoss
            p6.normalized p6.geometry + 1 ≤
        (ENNReal.ofReal pureWZ2Node05P7ConflictCoefficient + 1) * power := by
    calc
      _ ≤ ENNReal.ofReal pureWZ2Node05P7ConflictCoefficient * power +
          power := add_le_add hconflict hpowerOne
      _ = _ := by ring
  have hlog := p6.p7_positiveCardLog_le_envelope frostman
  unfold
    PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalPaperEDLoss
    pureWZ2Proposition64JointCleanupLoss
    pureWZ2Proposition64JointWeightRegularizationLoss
  dsimp only [power] at hconflictOne ⊢
  calc
    8 *
          (Nat.log 2
                (2 *
                  (paperPositiveMassSubfamily
                    p6.geometry.cleanup.finalShading).family.card) +
              1 : ENNReal) ^
            2 *
        (PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalJointPaperEDConflictLoss
            p6.normalized p6.geometry +
          1) ≤
      8 * pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^ 2 *
        ((ENNReal.ofReal pureWZ2Node05P7ConflictCoefficient + 1) *
          Kakeya.realRpowENN sourceDelta
            (-18 * schedule.ordinary.mild.epsilon₂)) := by gcongr
    _ = pureWZ2Node05P7CleanupCoefficient *
        pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^ 2 *
        Kakeya.realRpowENN sourceDelta
          (-18 * schedule.ordinary.mild.epsilon₂) := by
      unfold pureWZ2Node05P7CleanupCoefficient
      ring

theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_topWeight_inv_eq
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual) :
    (pureWZ2Proposition64TopWeight
        (quantitativeOutput := p6.normalized))⁻¹ =
      pureWZ2Proposition64JointDensityFixedMassCoefficient⁻¹ *
        Kakeya.realRpowENN sourceDelta
          (-(5 * schedule.ordinary.mild.epsilon₂ + 2)) := by
  have hmass :
      pureWZ2Proposition64QuantitativeMassCoefficient p6.normalized =
        pureWZ2Proposition64JointDensityFixedMassCoefficient *
          Kakeya.realRpowENN sourceDelta
            (5 * schedule.ordinary.mild.epsilon₂) := by
    change
      pureWZ2Proposition64JointDensityMassCoefficient sourceDelta
          p6.normalized.densityLoss
          p6.normalized.normalized.prepared.normalization
          p6.normalized.normalized.prepared.slab.halfHeight =
        pureWZ2Proposition64JointDensityFixedMassCoefficient *
          Kakeya.realRpowENN sourceDelta
            (5 * schedule.ordinary.mild.epsilon₂)
    rw [p6.normalized.normalized.normalization_eq,
      pureWZ2Proposition64_jointDensityMassCoefficient_eq
        p6.normalized.normalized.prepared.slab.halfHeight_pos,
      p6.densityLoss_eq, schedule.slabDensityLoss_eq]
  have hweight :
      pureWZ2Proposition64TopWeight
          (quantitativeOutput := p6.normalized) =
        pureWZ2Proposition64JointDensityFixedMassCoefficient *
          Kakeya.realRpowENN sourceDelta
            (5 * schedule.ordinary.mild.epsilon₂ + 2) := by
    unfold pureWZ2Proposition64TopWeight
    rw [hmass, mul_assoc, realRpowENN_mul'
      p6.normalized.normalized.source.extremal.delta_pos]
  rw [hweight, ENNReal.mul_inv
      (Or.inl pureWZ2Proposition64JointDensityFixedMassCoefficient_pos.ne')
      (Or.inl pureWZ2Proposition64JointDensityFixedMassCoefficient_ne_top),
    pure_wz2_realRpowENN_inv
      p6.normalized.normalized.source.extremal.delta_pos]

noncomputable def pureWZ2Node05P7TopRetentionCoefficient : ENNReal :=
  (147 * (pureWZ2Node05P7CleanupCoefficient + 1)) *
    ((55296 * Kakeya.deltaTubeVolume 1) *
      Kakeya.realRpowENN
        (45 * pureWZ2Proposition64Lemma35Scale) 2)

theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_topRetention_le_envelope
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual)
    (frostman :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.SelectedSourceFrostmanReceipt
        p6.geometry) :
    pureWZ2Proposition64TopRetention
        (sourceDelta := sourceDelta)
        (PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalPaperEDLoss
          p6.normalized p6.geometry) ≤
      pureWZ2Node05P7TopRetentionCoefficient *
        pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^ 2 *
        Kakeya.realRpowENN sourceDelta
          (-18 * schedule.ordinary.mild.epsilon₂ + 2) := by
  let power :=
    Kakeya.realRpowENN sourceDelta
      (-18 * schedule.ordinary.mild.epsilon₂)
  let envelope := pureWZ2Node05P7ScaleLogEnvelope sourceDelta
  have hpowerOne : (1 : ENNReal) ≤ power := by
    dsimp only [power, Kakeya.realRpowENN]
    rw [ENNReal.one_le_ofReal]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      p6.normalized.normalized.source.extremal.delta_pos
      p6.normalized.normalized.source.extremal.delta_le_one
      (by linarith [schedule.ordinary.mild.epsilon₂_pos])
  have henvelopeOne : (1 : ENNReal) ≤ envelope := by
    have hlog := p6.p7_positiveCardLog_le_envelope frostman
    exact (show (1 : ENNReal) ≤
        (Nat.log 2
            (2 *
              (paperPositiveMassSubfamily
                p6.geometry.cleanup.finalShading).family.card) + 1 :
          ENNReal) by norm_num).trans hlog
  have hcleanup := p6.p7_cleanupLoss_le_envelope frostman
  have hcleanupOne :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalPaperEDLoss
            p6.normalized p6.geometry + 1 ≤
        (pureWZ2Node05P7CleanupCoefficient + 1) *
          envelope ^ 2 * power := by
    calc
      _ ≤ pureWZ2Node05P7CleanupCoefficient * envelope ^ 2 * power +
          envelope ^ 2 * power := by
        apply add_le_add hcleanup
        calc
          1 = 1 ^ 2 * 1 := by norm_num
          _ ≤ envelope ^ 2 * power :=
            mul_le_mul (pow_le_pow_left' henvelopeOne 2) hpowerOne bot_le bot_le
      _ = _ := by ring
  unfold pureWZ2Proposition64TopRetention
  have hfinal :
      Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2 =
        Kakeya.realRpowENN
            (45 * pureWZ2Proposition64Lemma35Scale) 2 *
          Kakeya.realRpowENN sourceDelta 2 := by
    unfold pureWZ2Proposition64Lemma35FinalDelta
    exact realRpowENN_mul
      (mul_pos (by norm_num) pureWZ2Proposition64Lemma35Scale_pos)
      p6.normalized.normalized.source.extremal.delta_pos 2
  rw [hfinal]
  dsimp only [envelope, power] at hcleanupOne ⊢
  calc
    (147 *
          (PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalPaperEDLoss
              p6.normalized p6.geometry +
            1)) *
        (55296 * Kakeya.deltaTubeVolume 1 *
          (Kakeya.realRpowENN
              (45 * pureWZ2Proposition64Lemma35Scale) 2 *
            Kakeya.realRpowENN sourceDelta 2)) ≤
      (147 *
          ((pureWZ2Node05P7CleanupCoefficient + 1) *
            pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^ 2 *
            Kakeya.realRpowENN sourceDelta
              (-18 * schedule.ordinary.mild.epsilon₂))) *
        (55296 * Kakeya.deltaTubeVolume 1 *
          (Kakeya.realRpowENN
              (45 * pureWZ2Proposition64Lemma35Scale) 2 *
            Kakeya.realRpowENN sourceDelta 2)) := by gcongr
    _ = pureWZ2Node05P7TopRetentionCoefficient *
        pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^ 2 *
        Kakeya.realRpowENN sourceDelta
          (-18 * schedule.ordinary.mild.epsilon₂ + 2) := by
      unfold pureWZ2Node05P7TopRetentionCoefficient
      rw [← realRpowENN_mul'
        p6.normalized.normalized.source.extremal.delta_pos]
      ring

noncomputable def pureWZ2Node05P7SelectionRetentionCoefficient
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal) : ENNReal :=
  (((PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalTransportedQuotientConflictDegree +
          1) ^ pureWZ2Node05P7ScaleCoordinateCount schedule : ℕ) :
      ENNReal) * 8

noncomputable def pureWZ2Node05P7GlobalRetentionCoefficient
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal) : ENNReal :=
  pureWZ2Proposition64JointDensityFixedMassCoefficient⁻¹ *
    (2 * pureWZ2Node05P7TopRetentionCoefficient *
      pureWZ2Node05P7SelectionRetentionCoefficient schedule)

theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_globalRetention_le_envelope
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual)
    (frostman :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.SelectedSourceFrostmanReceipt
        p6.geometry)
    {raw :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.QuantitativeVerticalTransportedSourceParentScheduleData
        p6.normalized p6.geometry frostman schedule.p7Scale}
    {quotient :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.QuantitativeVerticalTransportedSourceParentQuotientData
        p6.normalized p6.geometry frostman schedule.p7Scale raw}
    (selected :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.QuantitativeVerticalTransportedSourceParentQuotientData.QuantitativeVerticalTransportedCombinedSelectionData
        p6.normalized p6.geometry frostman schedule.p7Scale quotient) :
    (pureWZ2Proposition64TopWeight
          (quantitativeOutput := p6.normalized))⁻¹ *
        selected.globalRetentionConstant p6.normalized p6.geometry frostman
          schedule.p7Scale ≤
      pureWZ2Node05P7GlobalRetentionCoefficient schedule *
        pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
          (2 * pureWZ2Node05P7ScaleCoordinateCount schedule + 3) *
        Kakeya.realRpowENN sourceDelta
          (-23 * schedule.ordinary.mild.epsilon₂) := by
  have htopWeight := p6.p7_topWeight_inv_eq
  have htopRetention := p6.p7_topRetention_le_envelope frostman
  have hselection :
      selected.retentionConstant ≤
        pureWZ2Node05P7SelectionRetentionCoefficient schedule *
          pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
            (2 * pureWZ2Node05P7ScaleCoordinateCount schedule + 1) := by
    rw [selected.retentionConstant_eq]
    unfold
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalTransportedSelectionRetention
      pureWZ2Node05P7SelectionRetentionCoefficient
    rw [PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalTransportedScheduleLevelCount_eq,
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalTransportedSelectorCoordinateCount_eq]
    have hgrid :
        pureWZ2Proposition64TargetGridLoss schedule.p7Scale =
          schedule.p7Scale.gridLoss := rfl
    rw [hgrid]
    simp only [pureWZ2Node05P7ScaleCoordinateCount]
    have hlog := p6.p7_initialCardLog_le_envelope frostman
    gcongr
  rw [htopWeight]
  unfold
    PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.QuantitativeVerticalTransportedSourceParentQuotientData.QuantitativeVerticalTransportedCombinedSelectionData.globalRetentionConstant
  calc
    (pureWZ2Proposition64JointDensityFixedMassCoefficient⁻¹ *
          Kakeya.realRpowENN sourceDelta
            (-(5 * schedule.ordinary.mild.epsilon₂ + 2))) *
        (2 *
          pureWZ2Proposition64TopRetention
            (PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalPaperEDLoss
              p6.normalized p6.geometry) *
          selected.retentionConstant) ≤
      (pureWZ2Proposition64JointDensityFixedMassCoefficient⁻¹ *
          Kakeya.realRpowENN sourceDelta
            (-(5 * schedule.ordinary.mild.epsilon₂ + 2))) *
        (2 *
          (pureWZ2Node05P7TopRetentionCoefficient *
            pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^ 2 *
            Kakeya.realRpowENN sourceDelta
              (-18 * schedule.ordinary.mild.epsilon₂ + 2)) *
          (pureWZ2Node05P7SelectionRetentionCoefficient schedule *
            pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
              (2 * pureWZ2Node05P7ScaleCoordinateCount schedule + 1))) := by
        gcongr
    _ = pureWZ2Node05P7GlobalRetentionCoefficient schedule *
        pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
          (2 * pureWZ2Node05P7ScaleCoordinateCount schedule + 3) *
        Kakeya.realRpowENN sourceDelta
          (-23 * schedule.ordinary.mild.epsilon₂) := by
      unfold pureWZ2Node05P7GlobalRetentionCoefficient
      have hpower :
          Kakeya.realRpowENN sourceDelta
                (-(5 * schedule.ordinary.mild.epsilon₂ + 2)) *
              Kakeya.realRpowENN sourceDelta
                (-18 * schedule.ordinary.mild.epsilon₂ + 2) =
            Kakeya.realRpowENN sourceDelta
              (-23 * schedule.ordinary.mild.epsilon₂) := by
        rw [realRpowENN_mul'
          p6.normalized.normalized.source.extremal.delta_pos]
        congr 1
        ring
      have hlog :
          pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^ 2 *
              pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
                (2 * pureWZ2Node05P7ScaleCoordinateCount schedule + 1) =
            pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
              (2 * pureWZ2Node05P7ScaleCoordinateCount schedule + 3) := by
        rw [← pow_add]
        congr 1
        omega
      calc
        _ = pureWZ2Proposition64JointDensityFixedMassCoefficient⁻¹ *
              (2 * pureWZ2Node05P7TopRetentionCoefficient *
                pureWZ2Node05P7SelectionRetentionCoefficient schedule) *
              (pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^ 2 *
                pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
                  (2 * pureWZ2Node05P7ScaleCoordinateCount schedule + 1)) *
              (Kakeya.realRpowENN sourceDelta
                  (-(5 * schedule.ordinary.mild.epsilon₂ + 2)) *
                Kakeya.realRpowENN sourceDelta
                  (-18 * schedule.ordinary.mild.epsilon₂ + 2)) := by ring
        _ = _ := by rw [hpower, hlog]

noncomputable def pureWZ2Node05P7InverseVolumeRealCoefficient : ℝ :=
  let transport := quantitativeVerticalSourceTransportScaleFactor
  let quotient := 57600004 * transport
  432 * quotient ^ 2 * (1 + 2 * 57600004) *
    pureWZ2Proposition64NormalizationConstant

noncomputable def pureWZ2Node05P7InverseVolumeCoefficient : ENNReal :=
  ENNReal.ofReal pureWZ2Node05P7InverseVolumeRealCoefficient

theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_inverseVolume_le_source_power
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual)
    (frostman : SelectedSourceFrostmanReceipt p6.geometry)
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      p6.normalized p6.geometry frostman schedule.p7Scale}
    {quotient : QuantitativeVerticalTransportedSourceParentQuotientData
      p6.normalized p6.geometry frostman schedule.p7Scale raw}
    (selected :
      QuantitativeVerticalTransportedSourceParentQuotientData.QuantitativeVerticalTransportedCombinedSelectionData
        p6.normalized p6.geometry frostman schedule.p7Scale quotient)
    (coordinate : Fin
      (quantitativeVerticalRequestedScaleScheduleFor
        p6.normalized p6.geometry schedule.p7Scale).levelCount) :
    selected.inverseVolumeConstant p6.normalized p6.geometry frostman
        schedule.p7Scale coordinate ≤
      pureWZ2Node05P7InverseVolumeCoefficient *
        Kakeya.realRpowENN sourceDelta
          (-3 * p6.normalized.normalized.inputLoss) := by
  let q := quantitativeVerticalTransportedQuotientScale
    p6.normalized p6.geometry schedule.p7Scale coordinate
  let rho := (quantitativeVerticalMatchedSourceNearby
    p6.normalized p6.geometry schedule.p7Scale coordinate).rho
  let target := ((quantitativeVerticalRequestedScaleScheduleFor
    p6.normalized p6.geometry schedule.p7Scale).requested coordinate).1
  let power := Real.rpow sourceDelta
    (-p6.normalized.normalized.inputLoss)
  let transport := quantitativeVerticalSourceTransportScaleFactor
  let quotientCoefficient := 57600004 * transport
  have hsource := p6.normalized.normalized.source.extremal.delta_pos
  have hsourceOne := p6.normalized.normalized.source.extremal.delta_le_one
  have hpowerPos : 0 < power := by
    exact Real.rpow_pos_of_pos hsource _
  have hpowerOne : 1 ≤ power := by
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hsource hsourceOne
      (by linarith [p6.inputLoss_pos])
  have htargetPos : 0 < target := by
    exact lt_of_lt_of_le p6.geometry.scales.finalDelta_pos
      ((quantitativeVerticalRequestedScaleScheduleFor
        p6.normalized p6.geometry schedule.p7Scale).requested coordinate).2.1
  have htargetOne : target ≤ 1 :=
    ((quantitativeVerticalRequestedScaleScheduleFor
      p6.normalized p6.geometry schedule.p7Scale).requested coordinate).2.2
  have htransportPos : 0 < transport := by
    exact lt_of_lt_of_le zero_lt_one <|
      quantitativeVerticalSourceTransportScaleFactor_one_le
        p6.geometry.scales.scale_one
  have hrhoPos : 0 < rho :=
    (quantitativeVerticalMatchedSourceNearby
      p6.normalized p6.geometry schedule.p7Scale coordinate).scaleData.rho_pos
  have htargetRho : target ≤ transport * rho := by
    have hrequest :
        target / transport ≤
          (quantitativeVerticalMatchedSourceRequested
            p6.normalized p6.geometry schedule.p7Scale coordinate).1 := by
      exact le_max_right _ _
    have hnearby :=
      (quantitativeVerticalMatchedSourceNearby
        p6.normalized p6.geometry schedule.p7Scale coordinate).requested_le
    rw [div_le_iff₀ htransportPos] at hrequest
    exact hrequest.trans <| by
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hnearby htransportPos.le
  have hqPos : 0 < q :=
    quotient.quotientScale_pos p6.normalized p6.geometry frostman
      schedule.p7Scale coordinate
  have hqTarget : q ≤ 57600004 * power * target :=
    (quantitativeVerticalTransportedQuotientScale_lt_requested
      p6.normalized p6.geometry schedule.p7Scale p6.inputLoss_pos.le
        coordinate).le
  have hqRho : q ≤ quotientCoefficient * power * rho := by
    calc
      q ≤ 57600004 * power * target := hqTarget
      _ ≤ 57600004 * power * (transport * rho) := by gcongr
      _ = quotientCoefficient * power * rho := by
        unfold quotientCoefficient
        ring
  have hqOne :
      1 + 2 * q ≤ (1 + 2 * 57600004) * power := by
    calc
      1 + 2 * q ≤ power + 2 * (57600004 * power * target) := by
        exact add_le_add hpowerOne
          (mul_le_mul_of_nonneg_left hqTarget (by norm_num))
      _ ≤ power + 2 * (57600004 * power * 1) := by gcongr
      _ = (1 + 2 * 57600004) * power := by ring
  have hscaleOne : 1 ≤ pureWZ2Proposition64Lemma35Scale :=
    p6.geometry.scales.scale_one
  have hratio :
      q ^ 2 *
          (p6.normalized.normalized.prepared.normalization *
            p6.normalized.normalized.prepared.slab.halfHeight /
            (pureWZ2Proposition64Lemma35Scale ^ 3 * rho ^ 2)) ≤
        (quotientCoefficient * power) ^ 2 *
          pureWZ2Proposition64NormalizationConstant := by
    have hratioNonneg :
        0 ≤
          p6.normalized.normalized.prepared.normalization *
            p6.normalized.normalized.prepared.slab.halfHeight /
            (pureWZ2Proposition64Lemma35Scale ^ 3 * rho ^ 2) := by
      exact div_nonneg
        (mul_nonneg
          (p6.normalized.normalized.normalization_nine.trans' (by norm_num))
          p6.normalized.normalized.prepared.slab.halfHeight_pos.le)
        (mul_nonneg (pow_nonneg pureWZ2Proposition64Lemma35Scale_pos.le 3)
          (sq_nonneg rho))
    calc
      _ ≤ (quotientCoefficient * power * rho) ^ 2 *
          (p6.normalized.normalized.prepared.normalization *
            p6.normalized.normalized.prepared.slab.halfHeight /
            (pureWZ2Proposition64Lemma35Scale ^ 3 * rho ^ 2)) := by
        gcongr
      _ = (quotientCoefficient * power) ^ 2 *
          (p6.normalized.normalized.prepared.normalization *
            p6.normalized.normalized.prepared.slab.halfHeight /
              pureWZ2Proposition64Lemma35Scale ^ 3) := by
        field_simp [hrhoPos.ne']
      _ ≤ (quotientCoefficient * power) ^ 2 *
          pureWZ2Proposition64NormalizationConstant := by
        rw [p6.normalized.normalized.normalization_eq]
        rw [mul_div_assoc]
        have hhalfDiv :
            p6.normalized.normalized.prepared.slab.halfHeight /
                pureWZ2Proposition64Lemma35Scale ^ 3 ≤ 1 :=
          (div_le_one
          (pow_pos pureWZ2Proposition64Lemma35Scale_pos 3)).2 <| by
            calc
              p6.normalized.normalized.prepared.slab.halfHeight ≤ 1 :=
                p6.normalized.normalized.prepared.slab.halfHeight_le_one
              _ ≤ pureWZ2Proposition64Lemma35Scale ^ 3 := by
                nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
                  hscaleOne 3]
        calc
          _ ≤ (quotientCoefficient * power) ^ 2 *
              (pureWZ2Proposition64NormalizationConstant * 1) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_left hhalfDiv
                pureWZ2Proposition64NormalizationConstant_pos.le
            · positivity
          _ = _ := by ring
  have hreal :
      432 * q ^ 2 * (1 + 2 * q) *
          (p6.normalized.normalized.prepared.normalization *
            p6.normalized.normalized.prepared.slab.halfHeight /
            (pureWZ2Proposition64Lemma35Scale ^ 3 * rho ^ 2)) ≤
        pureWZ2Node05P7InverseVolumeRealCoefficient * power ^ 3 := by
    calc
      _ = 432 *
          (q ^ 2 *
            (p6.normalized.normalized.prepared.normalization *
              p6.normalized.normalized.prepared.slab.halfHeight /
              (pureWZ2Proposition64Lemma35Scale ^ 3 * rho ^ 2))) *
          (1 + 2 * q) := by ring
      _ ≤ 432 *
          ((quotientCoefficient * power) ^ 2 *
            pureWZ2Proposition64NormalizationConstant) *
          ((1 + 2 * 57600004) * power) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hratio (by norm_num))
          hqOne (by nlinarith [hqPos])
          (mul_nonneg (by norm_num) <|
            mul_nonneg (sq_nonneg (quotientCoefficient * power))
              pureWZ2Proposition64NormalizationConstant_pos.le)
      _ = pureWZ2Node05P7InverseVolumeRealCoefficient * power ^ 3 := by
        unfold pureWZ2Node05P7InverseVolumeRealCoefficient
          quotientCoefficient transport
        ring
  have hqPower : Real.rpow q 2 = q ^ 2 :=
    Real.rpow_two q
  unfold
    QuantitativeVerticalTransportedSourceParentQuotientData.QuantitativeVerticalTransportedCombinedSelectionData.inverseVolumeConstant
    pureWZ2Node05P7InverseVolumeCoefficient
  change
    432 * ENNReal.ofReal (Real.rpow q 2) * ENNReal.ofReal (1 + 2 * q) *
        ENNReal.ofReal
          (p6.normalized.normalized.prepared.normalization *
            p6.normalized.normalized.prepared.slab.halfHeight /
            (pureWZ2Proposition64Lemma35Scale ^ 3 * rho ^ 2)) ≤
      ENNReal.ofReal pureWZ2Node05P7InverseVolumeRealCoefficient *
        ENNReal.ofReal
          (Real.rpow sourceDelta
            (-3 * p6.normalized.normalized.inputLoss))
  have hpowerCube :
      power ^ 3 =
        Real.rpow sourceDelta
          (-3 * p6.normalized.normalized.inputLoss) := by
    calc
      Real.rpow sourceDelta (-p6.normalized.normalized.inputLoss) ^ 3 =
          Real.rpow sourceDelta
            ((-p6.normalized.normalized.inputLoss) * (3 : ℝ)) :=
        (Real.rpow_mul_natCast hsource.le
          (-p6.normalized.normalized.inputLoss) 3).symm
      _ = _ := by
        congr 1
        ring
  rw [← hpowerCube]
  have hconverted := ENNReal.ofReal_mono hreal
  have hcoefficientNonneg :
      0 ≤ pureWZ2Node05P7InverseVolumeRealCoefficient := by
    unfold pureWZ2Node05P7InverseVolumeRealCoefficient
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (sq_nonneg (57600004 * quantitativeVerticalSourceTransportScaleFactor)))
        (by norm_num))
      pureWZ2Proposition64NormalizationConstant_pos.le
  calc
    432 * ENNReal.ofReal (Real.rpow q 2) *
          ENNReal.ofReal (1 + 2 * q) *
          ENNReal.ofReal
            (p6.normalized.normalized.prepared.normalization *
              p6.normalized.normalized.prepared.slab.halfHeight /
              (pureWZ2Proposition64Lemma35Scale ^ 3 * rho ^ 2)) =
        432 * ENNReal.ofReal (q ^ 2) * ENNReal.ofReal (1 + 2 * q) *
          ENNReal.ofReal
            (p6.normalized.normalized.prepared.normalization *
              p6.normalized.normalized.prepared.slab.halfHeight /
              (pureWZ2Proposition64Lemma35Scale ^ 3 * rho ^ 2)) := by
      rw [hqPower]
    _ = ENNReal.ofReal
          (432 * q ^ 2 * (1 + 2 * q) *
            (p6.normalized.normalized.prepared.normalization *
              p6.normalized.normalized.prepared.slab.halfHeight /
              (pureWZ2Proposition64Lemma35Scale ^ 3 * rho ^ 2))) := by
      rw [show (432 : ENNReal) = ENNReal.ofReal (432 : ℝ) by norm_num]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 432),
        ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (sq_nonneg q)),
        ← ENNReal.ofReal_mul
          (mul_nonneg
            (mul_nonneg (by norm_num) (sq_nonneg q))
            (by nlinarith [hqPos]))]
    _ ≤ ENNReal.ofReal
          (pureWZ2Node05P7InverseVolumeRealCoefficient * power ^ 3) :=
      hconverted
    _ = ENNReal.ofReal pureWZ2Node05P7InverseVolumeRealCoefficient *
          ENNReal.ofReal (power ^ 3) :=
      ENNReal.ofReal_mul hcoefficientNonneg

noncomputable def pureWZ2Node05P7JohnCoefficient : ENNReal :=
  ENNReal.ofReal
    (27 * (2 * (1 + 80 * pureWZ2Proposition64Lemma35Scale)) ^ 3)

noncomputable def pureWZ2Node05P7DegreeCoefficient
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal) : ENNReal :=
  16 * (2 * pureWZ2Node05P7ScaleCoordinateCount schedule : ENNReal)

noncomputable def pureWZ2Node05P7RawScaleCoefficient
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal) : ENNReal :=
  pureWZ2Node05P7InverseVolumeCoefficient *
    pureWZ2Node05P7JohnCoefficient *
    pureWZ2Node05P7GlobalRetentionCoefficient schedule *
    pureWZ2Node05P7DegreeCoefficient schedule

theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_rawScaleConstant_le_envelope
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual)
    (frostman : SelectedSourceFrostmanReceipt p6.geometry)
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      p6.normalized p6.geometry frostman schedule.p7Scale}
    {quotient : QuantitativeVerticalTransportedSourceParentQuotientData
      p6.normalized p6.geometry frostman schedule.p7Scale raw}
    (selected :
      QuantitativeVerticalTransportedSourceParentQuotientData.QuantitativeVerticalTransportedCombinedSelectionData
        p6.normalized p6.geometry frostman schedule.p7Scale quotient)
    (coordinate : Fin
      (quantitativeVerticalRequestedScaleScheduleFor
        p6.normalized p6.geometry schedule.p7Scale).levelCount) :
    selected.rawActualJohnConstant p6.normalized p6.geometry frostman
        schedule.p7Scale coordinate ≤
      pureWZ2Node05P7RawScaleCoefficient schedule *
        pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
          (4 * pureWZ2Node05P7ScaleCoordinateCount schedule + 3) *
        Kakeya.realRpowENN sourceDelta
          (-37 * schedule.ordinary.mild.epsilon₂) := by
  let inputPower :=
    Kakeya.realRpowENN sourceDelta
      (-p6.normalized.normalized.inputLoss)
  let epsilonPower :=
    Kakeya.realRpowENN sourceDelta
      (-schedule.ordinary.mild.epsilon₂)
  have hinputPower : inputPower ≤ epsilonPower := by
    exact pure_wz2_rpowENN_antitone
      p6.normalized.normalized.source.extremal.delta_pos
      p6.normalized.normalized.source.extremal.delta_le_one
      (by linarith [p6.inputLoss_le_epsilon₂])
  have hinverse :=
    p6.p7_inverseVolume_le_source_power frostman selected coordinate
  have hinverse' :
      selected.inverseVolumeConstant p6.normalized p6.geometry frostman
          schedule.p7Scale coordinate ≤
        pureWZ2Node05P7InverseVolumeCoefficient *
          Kakeya.realRpowENN sourceDelta
            (-3 * schedule.ordinary.mild.epsilon₂) := by
    calc
      _ ≤ pureWZ2Node05P7InverseVolumeCoefficient *
          Kakeya.realRpowENN sourceDelta
            (-3 * p6.normalized.normalized.inputLoss) := hinverse
      _ ≤ _ := by
        gcongr
        exact pure_wz2_rpowENN_antitone
          p6.normalized.normalized.source.extremal.delta_pos
          p6.normalized.normalized.source.extremal.delta_le_one
          (by linarith [p6.inputLoss_le_epsilon₂])
  have hjohn := p6.p7_johnFactor_le_source_power frostman selected coordinate
  have hglobal := p6.p7_globalRetention_le_envelope frostman selected
  have hdegree :
      selected.degreeConstant ≤
        pureWZ2Node05P7DegreeCoefficient schedule *
          pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
            (2 * pureWZ2Node05P7ScaleCoordinateCount schedule) := by
    rw [selected.degreeConstant_eq]
    unfold
      quantitativeVerticalTransportedPairDegreeConstant
      pureWZ2Node05P7DegreeCoefficient
    rw [quantitativeVerticalTransportedSelectorCoordinateCount_eq]
    have hgrid :
        pureWZ2Proposition64TargetGridLoss schedule.p7Scale =
          schedule.p7Scale.gridLoss := rfl
    rw [hgrid]
    simp only [pureWZ2Node05P7ScaleCoordinateCount, Nat.cast_mul,
      Nat.cast_ofNat]
    have hlog := p6.p7_initialCardLog_le_envelope frostman
    gcongr
  have hpower :
      Kakeya.realRpowENN sourceDelta
            (-3 * schedule.ordinary.mild.epsilon₂) *
          Kakeya.realRpowENN sourceDelta
            (-9 * schedule.ordinary.mild.epsilon₂) *
          Kakeya.realRpowENN sourceDelta
            (-23 * schedule.ordinary.mild.epsilon₂) *
          epsilonPower * epsilonPower =
        Kakeya.realRpowENN sourceDelta
          (-37 * schedule.ordinary.mild.epsilon₂) := by
    dsimp only [epsilonPower]
    rw [realRpowENN_mul'
        p6.normalized.normalized.source.extremal.delta_pos,
      realRpowENN_mul'
        p6.normalized.normalized.source.extremal.delta_pos,
      realRpowENN_mul'
        p6.normalized.normalized.source.extremal.delta_pos,
      realRpowENN_mul'
        p6.normalized.normalized.source.extremal.delta_pos]
    congr 1
    ring
  have hlog :
      pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
            (2 * pureWZ2Node05P7ScaleCoordinateCount schedule + 3) *
          pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
            (2 * pureWZ2Node05P7ScaleCoordinateCount schedule) =
        pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
          (4 * pureWZ2Node05P7ScaleCoordinateCount schedule + 3) := by
    rw [← pow_add]
    congr 1
    omega
  unfold
    QuantitativeVerticalTransportedSourceParentQuotientData.QuantitativeVerticalTransportedCombinedSelectionData.rawActualJohnConstant
  change
    (selected.inverseVolumeConstant p6.normalized p6.geometry frostman
          schedule.p7Scale coordinate *
        ENNReal.ofReal
          (27 * (2 * selected.factor p6.normalized p6.geometry frostman
            schedule.p7Scale coordinate - 1) ^ 3)) *
      (((pureWZ2Proposition64TopWeight
          (quantitativeOutput := p6.normalized))⁻¹ *
        (inputPower *
          selected.globalRetentionConstant p6.normalized p6.geometry frostman
            schedule.p7Scale * 1 * selected.degreeConstant)) *
        inputPower) ≤ _
  calc
    _ = selected.inverseVolumeConstant p6.normalized p6.geometry frostman
          schedule.p7Scale coordinate *
        ENNReal.ofReal
          (27 * (2 * selected.factor p6.normalized p6.geometry frostman
            schedule.p7Scale coordinate - 1) ^ 3) *
        ((pureWZ2Proposition64TopWeight
          (quantitativeOutput := p6.normalized))⁻¹ *
          selected.globalRetentionConstant p6.normalized p6.geometry frostman
            schedule.p7Scale) *
        selected.degreeConstant * inputPower * inputPower := by ring
    _ ≤
        (pureWZ2Node05P7InverseVolumeCoefficient *
          Kakeya.realRpowENN sourceDelta
            (-3 * schedule.ordinary.mild.epsilon₂)) *
        (pureWZ2Node05P7JohnCoefficient *
          Kakeya.realRpowENN sourceDelta
            (-9 * schedule.ordinary.mild.epsilon₂)) *
        (pureWZ2Node05P7GlobalRetentionCoefficient schedule *
          pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
            (2 * pureWZ2Node05P7ScaleCoordinateCount schedule + 3) *
          Kakeya.realRpowENN sourceDelta
            (-23 * schedule.ordinary.mild.epsilon₂)) *
        (pureWZ2Node05P7DegreeCoefficient schedule *
          pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
            (2 * pureWZ2Node05P7ScaleCoordinateCount schedule)) *
        epsilonPower * epsilonPower := by
      gcongr
      · simpa only [pureWZ2Node05P7JohnCoefficient] using hjohn
    _ = pureWZ2Node05P7RawScaleCoefficient schedule *
        pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
          (4 * pureWZ2Node05P7ScaleCoordinateCount schedule + 3) *
        Kakeya.realRpowENN sourceDelta
          (-37 * schedule.ordinary.mild.epsilon₂) := by
      unfold pureWZ2Node05P7RawScaleCoefficient
      calc
        _ = (pureWZ2Node05P7InverseVolumeCoefficient *
              pureWZ2Node05P7JohnCoefficient *
              pureWZ2Node05P7GlobalRetentionCoefficient schedule *
              pureWZ2Node05P7DegreeCoefficient schedule) *
            (pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
                (2 * pureWZ2Node05P7ScaleCoordinateCount schedule + 3) *
              pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
                (2 * pureWZ2Node05P7ScaleCoordinateCount schedule)) *
            (Kakeya.realRpowENN sourceDelta
                  (-3 * schedule.ordinary.mild.epsilon₂) *
                Kakeya.realRpowENN sourceDelta
                  (-9 * schedule.ordinary.mild.epsilon₂) *
                Kakeya.realRpowENN sourceDelta
                  (-23 * schedule.ordinary.mild.epsilon₂) *
                epsilonPower * epsilonPower) := by ring
        _ = _ := by rw [hpower, hlog]

theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_selectionDegree_le_envelope
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual)
    (frostman :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.SelectedSourceFrostmanReceipt
        p6.geometry)
    {raw :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.QuantitativeVerticalTransportedSourceParentScheduleData
        p6.normalized p6.geometry frostman schedule.p7Scale}
    {quotient :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.QuantitativeVerticalTransportedSourceParentQuotientData
        p6.normalized p6.geometry frostman schedule.p7Scale raw}
    (selected :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.QuantitativeVerticalTransportedSourceParentQuotientData.QuantitativeVerticalTransportedCombinedSelectionData
        p6.normalized p6.geometry frostman schedule.p7Scale quotient) :
    selected.degreeConstant ≤
      (16 * (2 * pureWZ2Node05P7ScaleCoordinateCount schedule : ENNReal)) *
        pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
          (2 * pureWZ2Node05P7ScaleCoordinateCount schedule) := by
  rw [selected.degreeConstant_eq]
  unfold
    PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalTransportedPairDegreeConstant
  rw [PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalTransportedSelectorCoordinateCount_eq]
  have hgrid :
      pureWZ2Proposition64TargetGridLoss schedule.p7Scale =
        schedule.p7Scale.gridLoss := rfl
  rw [hgrid]
  simp only [pureWZ2Node05P7ScaleCoordinateCount, Nat.cast_mul,
    Nat.cast_ofNat]
  have hlog := p6.p7_initialCardLog_le_envelope frostman
  gcongr

theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_selectionRetention_le_envelope
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual)
    (frostman :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.SelectedSourceFrostmanReceipt
        p6.geometry)
    {raw :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.QuantitativeVerticalTransportedSourceParentScheduleData
        p6.normalized p6.geometry frostman schedule.p7Scale}
    {quotient :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.QuantitativeVerticalTransportedSourceParentQuotientData
        p6.normalized p6.geometry frostman schedule.p7Scale raw}
    (selected :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.QuantitativeVerticalTransportedSourceParentQuotientData.QuantitativeVerticalTransportedCombinedSelectionData
        p6.normalized p6.geometry frostman schedule.p7Scale quotient) :
    selected.retentionConstant ≤
      (((PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalTransportedQuotientConflictDegree +
            1) ^ pureWZ2Node05P7ScaleCoordinateCount schedule : ℕ) :
          ENNReal) *
        8 *
        pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
          (2 * pureWZ2Node05P7ScaleCoordinateCount schedule + 1) := by
  rw [selected.retentionConstant_eq]
  unfold
    PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalTransportedSelectionRetention
  rw [PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalTransportedScheduleLevelCount_eq,
    PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalTransportedSelectorCoordinateCount_eq]
  have hgrid :
      pureWZ2Proposition64TargetGridLoss schedule.p7Scale =
        schedule.p7Scale.gridLoss := rfl
  rw [hgrid]
  simp only [pureWZ2Node05P7ScaleCoordinateCount]
  have hlog := p6.p7_initialCardLog_le_envelope frostman
  gcongr

noncomputable def pureWZ2Node05P7ScaleCoefficient
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal) : ENNReal :=
  max (pureWZ2Node05P7DegreeCoefficient schedule)
    (pureWZ2Node05P7RawScaleCoefficient schedule)

theorem pureWZ2Node05P7ScaleCoefficient_ne_top
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal) :
    pureWZ2Node05P7ScaleCoefficient schedule ≠ ⊤ := by
  unfold pureWZ2Node05P7ScaleCoefficient
  apply (max_lt_iff.mpr ?_).ne
  constructor
  · unfold pureWZ2Node05P7DegreeCoefficient
    exact ENNReal.mul_lt_top (by norm_num) <|
      ENNReal.mul_lt_top (by norm_num) (ENNReal.natCast_lt_top _)
  · have hcleanup : pureWZ2Node05P7CleanupCoefficient < ⊤ := by
      unfold pureWZ2Node05P7CleanupCoefficient
      exact ENNReal.mul_lt_top (by norm_num) <|
        ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, by norm_num⟩
    have hfixedInv :
        pureWZ2Proposition64JointDensityFixedMassCoefficient⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.mpr
        pureWZ2Proposition64JointDensityFixedMassCoefficient_pos.ne'
    have hinverse : pureWZ2Node05P7InverseVolumeCoefficient ≠ ⊤ := by
      unfold pureWZ2Node05P7InverseVolumeCoefficient
      exact ENNReal.ofReal_ne_top
    have hjohn : pureWZ2Node05P7JohnCoefficient ≠ ⊤ := by
      unfold pureWZ2Node05P7JohnCoefficient
      exact ENNReal.ofReal_ne_top
    have htopRetention :
        pureWZ2Node05P7TopRetentionCoefficient ≠ ⊤ := by
      unfold pureWZ2Node05P7TopRetentionCoefficient
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) <|
          ENNReal.add_ne_top.mpr ⟨hcleanup.ne, by norm_num⟩) <|
        ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top)
          (by simp [Kakeya.realRpowENN])
    have hselection :
        pureWZ2Node05P7SelectionRetentionCoefficient schedule ≠ ⊤ := by
      unfold pureWZ2Node05P7SelectionRetentionCoefficient
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by norm_num)
    have hdegree :
        pureWZ2Node05P7DegreeCoefficient schedule ≠ ⊤ := by
      unfold pureWZ2Node05P7DegreeCoefficient
      exact ENNReal.mul_ne_top (by norm_num) <|
        ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)
    have hglobal :
        pureWZ2Node05P7GlobalRetentionCoefficient schedule ≠ ⊤ := by
      unfold pureWZ2Node05P7GlobalRetentionCoefficient
      exact ENNReal.mul_ne_top hfixedInv <|
        ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num) htopRetention) hselection
    unfold pureWZ2Node05P7RawScaleCoefficient
    exact lt_top_iff_ne_top.mpr <|
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top hinverse hjohn) hglobal) hdegree

theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_scaleConstant_le_envelope
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual)
    (frostman : SelectedSourceFrostmanReceipt p6.geometry)
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      p6.normalized p6.geometry frostman schedule.p7Scale}
    {quotient : QuantitativeVerticalTransportedSourceParentQuotientData
      p6.normalized p6.geometry frostman schedule.p7Scale raw}
    (selected :
      QuantitativeVerticalTransportedSourceParentQuotientData.QuantitativeVerticalTransportedCombinedSelectionData
        p6.normalized p6.geometry frostman schedule.p7Scale quotient)
    (coordinate : Fin
      (quantitativeVerticalRequestedScaleScheduleFor
        p6.normalized p6.geometry schedule.p7Scale).levelCount) :
    selected.scaleConstant p6.normalized p6.geometry frostman
        schedule.p7Scale coordinate ≤
      pureWZ2Node05P7ScaleCoefficient schedule *
        pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
          pureWZ2Node05P7ScaleLogPower schedule *
        Kakeya.realRpowENN sourceDelta
          (-pureWZ2Node05P7ScalePowerLoss schedule) := by
  have hdegree := p6.p7_selectionDegree_le_envelope frostman selected
  have hraw := p6.p7_rawScaleConstant_le_envelope frostman selected coordinate
  have henvelopeOne :
      (1 : ENNReal) ≤ pureWZ2Node05P7ScaleLogEnvelope sourceDelta := by
    have hlog := p6.p7_initialCardLog_le_envelope frostman
    exact (show (1 : ENNReal) ≤
        (Nat.log 2
            (2 *
              (quantitativeVerticalPaperED
                p6.normalized p6.geometry frostman).subfamily.family.card) +
          1 : ENNReal) by norm_num).trans hlog
  have hpowerOne :
      (1 : ENNReal) ≤ Kakeya.realRpowENN sourceDelta
        (-pureWZ2Node05P7ScalePowerLoss schedule) := by
    unfold pureWZ2Node05P7ScalePowerLoss Kakeya.realRpowENN
    rw [ENNReal.one_le_ofReal]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      p6.normalized.normalized.source.extremal.delta_pos
      p6.normalized.normalized.source.extremal.delta_le_one
      (by linarith [schedule.ordinary.mild.epsilon₂_pos])
  have hrawPower :
      Kakeya.realRpowENN sourceDelta
          (-37 * schedule.ordinary.mild.epsilon₂) ≤
        Kakeya.realRpowENN sourceDelta
          (-pureWZ2Node05P7ScalePowerLoss schedule) := by
    exact pure_wz2_rpowENN_antitone
      p6.normalized.normalized.source.extremal.delta_pos
      p6.normalized.normalized.source.extremal.delta_le_one
      (by
        unfold pureWZ2Node05P7ScalePowerLoss
        linarith [schedule.ordinary.mild.epsilon₂_pos])
  unfold
    QuantitativeVerticalTransportedSourceParentQuotientData.QuantitativeVerticalTransportedCombinedSelectionData.scaleConstant
  apply max_le
  · calc
      selected.degreeConstant ≤
          pureWZ2Node05P7DegreeCoefficient schedule *
            pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
              (2 * pureWZ2Node05P7ScaleCoordinateCount schedule) := by
        simpa only [pureWZ2Node05P7DegreeCoefficient] using hdegree
      _ ≤ pureWZ2Node05P7ScaleCoefficient schedule *
            pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
              pureWZ2Node05P7ScaleLogPower schedule *
            Kakeya.realRpowENN sourceDelta
              (-pureWZ2Node05P7ScalePowerLoss schedule) := by
        have hcoefficient :
            pureWZ2Node05P7DegreeCoefficient schedule ≤
              pureWZ2Node05P7ScaleCoefficient schedule :=
          le_max_left _ _
        have hlogPower :
            pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
                (2 * pureWZ2Node05P7ScaleCoordinateCount schedule) ≤
              pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
                pureWZ2Node05P7ScaleLogPower schedule := by
          apply pow_le_pow_right₀ henvelopeOne
          unfold pureWZ2Node05P7ScaleLogPower
            pureWZ2Node05P7ScaleCoordinateCount
          omega
        calc
          _ ≤ pureWZ2Node05P7ScaleCoefficient schedule *
              pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
                pureWZ2Node05P7ScaleLogPower schedule := by gcongr
          _ ≤ _ := by
            simpa only [mul_assoc, mul_one] using
              mul_le_mul_of_nonneg_left hpowerOne
                (mul_nonneg (by positivity) (by positivity))
  · calc
      selected.rawActualJohnConstant p6.normalized p6.geometry frostman
          schedule.p7Scale coordinate ≤
        pureWZ2Node05P7RawScaleCoefficient schedule *
          pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
            (4 * pureWZ2Node05P7ScaleCoordinateCount schedule + 3) *
          Kakeya.realRpowENN sourceDelta
            (-37 * schedule.ordinary.mild.epsilon₂) := hraw
      _ ≤ pureWZ2Node05P7ScaleCoefficient schedule *
          pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
            pureWZ2Node05P7ScaleLogPower schedule *
          Kakeya.realRpowENN sourceDelta
            (-pureWZ2Node05P7ScalePowerLoss schedule) := by
        have hcoefficient :
            pureWZ2Node05P7RawScaleCoefficient schedule ≤
              pureWZ2Node05P7ScaleCoefficient schedule :=
          le_max_right _ _
        have hlogPower :
            pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
                (4 * pureWZ2Node05P7ScaleCoordinateCount schedule + 3) ≤
              pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
                pureWZ2Node05P7ScaleLogPower schedule := by
          apply pow_le_pow_right₀ henvelopeOne
          unfold pureWZ2Node05P7ScaleLogPower
            pureWZ2Node05P7ScaleCoordinateCount
          omega
        gcongr

/-- Pre-runtime cutoff which absorbs one family-free coefficient and the
entire common-log envelope after the explicit `48 * epsilon₂` power ledger.
-/
structure PureWZ2Node05P7ScaleConstantCutoff
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal)
    (coefficient : ENNReal) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorb :
    ∀ {sourceDelta : ℝ}, 0 < sourceDelta → sourceDelta ≤ delta₀ →
      Kakeya.realRpowENN sourceDelta
          (-pureWZ2Node05P7ScalePowerLoss schedule) *
        (coefficient *
          ENNReal.ofReal
            (pureWZ2BoundedSourceCardLogConstant *
              (1 + Real.log sourceDelta⁻¹)) ^
            pureWZ2Node05P7ScaleLogPower schedule) ≤
        Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-schedule.p7Scale.nearbyLoss)

theorem exists_pureWZ2Node05P7ScaleConstantCutoff
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal)
    (coefficient : ENNReal)
    (hcoefficient : coefficient ≠ ⊤) :
    Nonempty (PureWZ2Node05P7ScaleConstantCutoff
      schedule coefficient) := by
  let gap :=
    schedule.p7Scale.nearbyLoss -
      pureWZ2Node05P7ScalePowerLoss schedule
  have hgap : 0 < gap := by
    dsimp only [gap]
    exact pureWZ2Node05P7ScalePowerGap_pos schedule
  have hlogCoefficient :
      0 ≤ pureWZ2BoundedSourceCardLogConstant := by
    unfold pureWZ2BoundedSourceCardLogConstant
    positivity
  let finalFactor : ℝ := 45 * pureWZ2Proposition64Lemma35Scale
  let baseChange : ENNReal :=
    Kakeya.realRpowENN finalFactor schedule.p7Scale.nearbyLoss
  have hfinalFactor : 0 < finalFactor := by
    dsimp only [finalFactor]
    exact mul_pos (by norm_num) pureWZ2Proposition64Lemma35Scale_pos
  have hbaseChangeZero : baseChange ≠ 0 := by
    dsimp only [baseChange, Kakeya.realRpowENN]
    exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hfinalFactor _)).ne'
  have hbaseChangeTop : baseChange ≠ ⊤ := by
    simp [baseChange, Kakeya.realRpowENN]
  have hcombinedTop : baseChange * coefficient ≠ ⊤ :=
    ENNReal.mul_ne_top hbaseChangeTop hcoefficient
  rcases exists_delta_C_pow_log_absorbed_ennreal
      (baseChange * coefficient) hcombinedTop
      pureWZ2BoundedSourceCardLogConstant
      hlogCoefficient hgap (pureWZ2Node05P7ScaleLogPower_pos schedule) with
    ⟨delta₀, hdelta₀, hdelta₀One, habsorb⟩
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := hdelta₀
    delta₀_le_one := hdelta₀One
    absorb := ?_
  }⟩
  intro sourceDelta hsourceDelta hsourceSmall
  have hlog := habsorb sourceDelta hsourceDelta hsourceSmall
  let envelope :=
    ENNReal.ofReal
      (pureWZ2BoundedSourceCardLogConstant *
        (1 + Real.log sourceDelta⁻¹))
  let body :=
    Kakeya.realRpowENN sourceDelta
        (-pureWZ2Node05P7ScalePowerLoss schedule) *
      (coefficient *
        envelope ^ pureWZ2Node05P7ScaleLogPower schedule)
  have hscaled :
      baseChange * body ≤
        Kakeya.realRpowENN sourceDelta
          (-schedule.p7Scale.nearbyLoss) := by
    calc
      baseChange * body =
        Kakeya.realRpowENN sourceDelta
          (-pureWZ2Node05P7ScalePowerLoss schedule) *
          ((baseChange * coefficient) *
            envelope ^ pureWZ2Node05P7ScaleLogPower schedule) := by
            dsimp only [body]
            ring
      _ ≤
        Kakeya.realRpowENN sourceDelta
          (-pureWZ2Node05P7ScalePowerLoss schedule) *
          Kakeya.realRpowENN sourceDelta (-gap) := by
            gcongr
      _ = Kakeya.realRpowENN sourceDelta
          (-schedule.p7Scale.nearbyLoss) := by
        rw [← realRpowENN_add hsourceDelta]
        congr 1
        dsimp only [gap]
        ring
  have hbody :
      body ≤ baseChange⁻¹ *
        Kakeya.realRpowENN sourceDelta
          (-schedule.p7Scale.nearbyLoss) :=
    (ENNReal.mul_le_iff_le_inv hbaseChangeZero hbaseChangeTop).mp hscaled
  change body ≤
    Kakeya.realRpowENN
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
      (-schedule.p7Scale.nearbyLoss)
  calc
    body ≤ baseChange⁻¹ *
        Kakeya.realRpowENN sourceDelta
          (-schedule.p7Scale.nearbyLoss) := hbody
    _ = Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
        (-schedule.p7Scale.nearbyLoss) := by
      have hbaseInverse :
          baseChange⁻¹ =
            Kakeya.realRpowENN finalFactor
              (-schedule.p7Scale.nearbyLoss) := by
        dsimp only [baseChange]
        exact pure_wz2_realRpowENN_inv hfinalFactor
      rw [hbaseInverse]
      unfold pureWZ2Proposition64Lemma35FinalDelta
      exact (realRpowENN_mul hfinalFactor hsourceDelta
        (-schedule.p7Scale.nearbyLoss)).symm

theorem exists_pureWZ2Node05P7CanonicalScaleConstantCutoff
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal) :
    Nonempty (PureWZ2Node05P7ScaleConstantCutoff schedule
      (pureWZ2Node05P7ScaleCoefficient schedule)) :=
  exists_pureWZ2Node05P7ScaleConstantCutoff schedule
    (pureWZ2Node05P7ScaleCoefficient schedule)
    (pureWZ2Node05P7ScaleCoefficient_ne_top schedule)

theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_scaleAbsorptionReceipt
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual)
    (frostman : SelectedSourceFrostmanReceipt p6.geometry)
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      p6.normalized p6.geometry frostman schedule.p7Scale}
    {quotient : QuantitativeVerticalTransportedSourceParentQuotientData
      p6.normalized p6.geometry frostman schedule.p7Scale raw}
    (selected :
      QuantitativeVerticalTransportedSourceParentQuotientData.QuantitativeVerticalTransportedCombinedSelectionData
        p6.normalized p6.geometry frostman schedule.p7Scale quotient)
    (cutoff : PureWZ2Node05P7ScaleConstantCutoff schedule
      (pureWZ2Node05P7ScaleCoefficient schedule))
    (hsourceSmall : sourceDelta ≤ cutoff.delta₀) :
    selected.NearbyScaleAbsorptionReceipt
      p6.normalized p6.geometry frostman schedule.p7Scale
        schedule.p7Scale.nearbyLoss := by
  refine ⟨?_⟩
  intro coordinate
  calc
    selected.scaleConstant p6.normalized p6.geometry frostman
          schedule.p7Scale coordinate ≤
      pureWZ2Node05P7ScaleCoefficient schedule *
        pureWZ2Node05P7ScaleLogEnvelope sourceDelta ^
          pureWZ2Node05P7ScaleLogPower schedule *
        Kakeya.realRpowENN sourceDelta
          (-pureWZ2Node05P7ScalePowerLoss schedule) :=
      p6.p7_scaleConstant_le_envelope frostman selected coordinate
    _ = Kakeya.realRpowENN sourceDelta
          (-pureWZ2Node05P7ScalePowerLoss schedule) *
        (pureWZ2Node05P7ScaleCoefficient schedule *
          ENNReal.ofReal
            (pureWZ2BoundedSourceCardLogConstant *
              (1 + Real.log sourceDelta⁻¹)) ^
            pureWZ2Node05P7ScaleLogPower schedule) := by
      unfold pureWZ2Node05P7ScaleLogEnvelope
      ring
    _ ≤ Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
        (-schedule.p7Scale.nearbyLoss) :=
      cutoff.absorb p6.normalized.normalized.source.extremal.delta_pos
        hsourceSmall

theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7NearbyCWA_ofScaleCutoff
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual)
    (frostman : SelectedSourceFrostmanReceipt p6.geometry)
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      p6.normalized p6.geometry frostman schedule.p7Scale}
    {quotient : QuantitativeVerticalTransportedSourceParentQuotientData
      p6.normalized p6.geometry frostman schedule.p7Scale raw}
    (selected :
      QuantitativeVerticalTransportedSourceParentQuotientData.QuantitativeVerticalTransportedCombinedSelectionData
        p6.normalized p6.geometry frostman schedule.p7Scale quotient)
    (cutoff : PureWZ2Node05P7ScaleConstantCutoff schedule
      (pureWZ2Node05P7ScaleCoefficient schedule))
    (hsourceSmall : sourceDelta ≤ cutoff.delta₀) :
    WZ2PaperPureCWAAtNearbyScales
      (selected.finalED p6.normalized p6.geometry frostman schedule.p7Scale
        ).subfamily.family
      (Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
        (-schedule.p7Scale.nearbyLoss)) :=
  p6.p7NearbyCWA frostman selected
    (p6.p7_scaleAbsorptionReceipt frostman selected cutoff hsourceSmall)

end Kakeya.Assouad

