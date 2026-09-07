import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichEndpointHierarchyAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyInitialReentrantSourceProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64QuantitativeVerticalProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64TransportedSourceParents
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64TransportedActualJohnCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.BoundedSourceCardLog

/-! # Production quantitative hierarchy producer for Node 5 -/

noncomputable section

namespace Kakeya.Assouad

/-- The actual P6 source loss fits the target-grid ceiling fixed before the
runtime source scale is chosen. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.inputLoss_le_p7Ceiling
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (data : schedule.ActualRichEndpointP6Data actual) :
    data.normalized.normalized.inputLoss ≤ outputLoss / 20 := by
  have hepsilon :
      schedule.ordinary.mild.epsilon₂ < outputLoss / 20 := by
    linarith [schedule.ordinary.mild.ten_epsilon₂_lt_half_output]
  exact data.inputLoss_le_epsilon₂.trans hepsilon.le

/-- Strict positive target-rounding gap on the literal P6 input loss. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_roundingGap
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (data : schedule.ActualRichEndpointP6Data actual) :
    data.normalized.normalized.inputLoss + schedule.p7Scale.gridLoss <
      schedule.p7Scale.nearbyLoss :=
  schedule.p7Scale.inputLoss_add_grid_lt_nearby data.inputLoss_le_p7Ceiling

/-- The pre-runtime P7 cutoff absorbs the honest transported-quotient scale
constant on the literal P6 source loss. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_roundingAbsorption
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (data : schedule.ActualRichEndpointP6Data actual) :
    ENNReal.ofReal 57600004 *
          Kakeya.realRpowENN sourceDelta
            (-data.normalized.normalized.inputLoss) *
          Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (-schedule.p7Scale.gridLoss) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
        (-schedule.p7Scale.nearbyLoss) :=
  schedule.p7Rounding.absorption sourceDelta
    data.normalized.normalized.inputLoss
    data.normalized.normalized.source.extremal.delta_pos
    data.sourceSmall_p7Rounding data.inputLoss_pos.le
    data.inputLoss_le_p7Ceiling

/-- The P7 target grid attached to the same P6 geometry, with no
critical-floor witness. -/
noncomputable def
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7RequestedScaleSchedule
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (data : schedule.ActualRichEndpointP6Data actual) :=
  PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalP7RequestedScaleSchedule
    data.normalized data.geometry schedule.p7Scale

/-- Every requested final scale is rounded upward inside the independent P7
grid with exactly the reserved `gridLoss`. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7RequestedScale_rounding
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (data : schedule.ActualRichEndpointP6Data actual)
    (requested : WZ2PaperRequestedScale
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)) :
    ∃ coordinate : Fin data.p7RequestedScaleSchedule.levelCount,
      requested.1 ≤
          (data.p7RequestedScaleSchedule.requested coordinate).1 ∧
        ENNReal.ofReal
            (data.p7RequestedScaleSchedule.requested coordinate).1 <
          Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
              (-schedule.p7Scale.gridLoss) *
            ENNReal.ofReal requested.1 :=
  data.p7RequestedScaleSchedule.rounding requested

/-- The same pre-runtime grid rounds every final request through the honest
transported quotient scale, with the final nearby loss. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7TransportedQuotient_rounding
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (data : schedule.ActualRichEndpointP6Data actual)
    (requested : WZ2PaperRequestedScale
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)) :
    ∃ coordinate : Fin data.p7RequestedScaleSchedule.levelCount,
      requested.1 ≤
          PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalTransportedQuotientScale
            data.normalized data.geometry schedule.p7Scale coordinate ∧
        ENNReal.ofReal
            (PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalTransportedQuotientScale
              data.normalized data.geometry schedule.p7Scale coordinate) <
          Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
              (-schedule.p7Scale.nearbyLoss) *
            ENNReal.ofReal requested.1 :=
  PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.exists_transportedQuotientScale_rounding
    data.normalized data.geometry schedule.p7Scale data.inputLoss_pos.le
    data.p7_roundingAbsorption requested

/-- All geometric and rounding inputs to final nearby CWA are now
construction-internal; only the coordinatewise scale-constant absorption
receipt remains. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7NearbyCWA
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
        p6.normalized p6.geometry frostman schedule.p7Scale quotient)
    (absorption :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.QuantitativeVerticalTransportedSourceParentQuotientData.QuantitativeVerticalTransportedCombinedSelectionData.NearbyScaleAbsorptionReceipt
        p6.normalized p6.geometry frostman schedule.p7Scale selected
          schedule.p7Scale.nearbyLoss) :
    WZ2PaperPureCWAAtNearbyScales
      (selected.finalED p6.normalized p6.geometry frostman schedule.p7Scale
        ).subfamily.family
      (Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
        (-schedule.p7Scale.nearbyLoss)) :=
  selected.nearbyCWA p6.normalized p6.geometry frostman schedule.p7Scale
    p6.source_bounded_base schedule.p7Scale.nearbyLoss_pos absorption
    p6.p7TransportedQuotient_rounding

/-- Both runtime logarithms used by the final joint-ED and combined-selection
steps are bounded by the same family-free ordinary-tube source envelope. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_cardLog_bounds
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
    let positive := paperPositiveMassSubfamily p6.geometry.cleanup.finalShading
    (Nat.log 2 (2 * initialED.subfamily.family.card) + 1 : ℝ) ≤
        pureWZ2BoundedSourceCardLogConstant *
          (1 + Real.log sourceDelta⁻¹) ∧
      (Nat.log 2 (2 * positive.family.card) + 1 : ℝ) ≤
        pureWZ2BoundedSourceCardLogConstant *
          (1 + Real.log sourceDelta⁻¹) := by
  dsimp only
  have hsourceCard := pureWZ2_bounded_source_card_le
    p6.normalized.normalized.source.extremal.delta_pos
    p6.normalized.normalized.source.extremal.cwa_nearby_scales.2.2.1
    p6.source_bounded_base
  have hsourceLog := pureWZ2_bounded_source_card_log_bound
    p6.normalized.normalized.source.extremal.delta_pos
    p6.normalized.normalized.source.extremal.delta_le_one
    p6.normalized.normalized.source.extremal.nonempty hsourceCard
  have hinitialCard :
      (PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalPaperED
          p6.normalized p6.geometry frostman).subfamily.family.card ≤
        p6.normalized.normalized.source.family.card := by
    have h := p6.geometry.paperED_enncard_le_source
      (PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalPaperED
        p6.normalized p6.geometry frostman)
    change
      ((PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalPaperED
          p6.normalized p6.geometry frostman).subfamily.family.card : ENNReal) ≤
        (p6.normalized.normalized.source.family.card : ENNReal) at h
    exact_mod_cast h
  have hpositiveCard :
      (paperPositiveMassSubfamily p6.geometry.cleanup.finalShading).family.card ≤
        p6.normalized.normalized.source.family.card := by
    have h := p6.geometry.positiveFinal_enncard_le_source p6.normalized
    change
      ((paperPositiveMassSubfamily
          p6.geometry.cleanup.finalShading).family.card : ENNReal) ≤
        (p6.normalized.normalized.source.family.card : ENNReal) at h
    exact_mod_cast h
  constructor
  · have hlogNat :
        Nat.log 2 (2 *
            (PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalPaperED
              p6.normalized p6.geometry frostman).subfamily.family.card) + 1 ≤
          Nat.log 2 (2 * p6.normalized.normalized.source.family.card) + 1 :=
      Nat.add_le_add_right
        (Nat.log_mono_right (Nat.mul_le_mul_left 2 hinitialCard)) 1
    exact (by exact_mod_cast hlogNat :
      (Nat.log 2 (2 *
          (PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalPaperED
            p6.normalized p6.geometry frostman).subfamily.family.card) + 1 : ℝ) ≤
        (Nat.log 2 (2 * p6.normalized.normalized.source.family.card) + 1 : ℝ)
      ).trans hsourceLog
  · have hlogNat :
        Nat.log 2 (2 *
            (paperPositiveMassSubfamily
              p6.geometry.cleanup.finalShading).family.card) + 1 ≤
          Nat.log 2 (2 * p6.normalized.normalized.source.family.card) + 1 :=
      Nat.add_le_add_right
        (Nat.log_mono_right (Nat.mul_le_mul_left 2 hpositiveCard)) 1
    exact (by exact_mod_cast hlogNat :
      (Nat.log 2 (2 *
          (paperPositiveMassSubfamily
            p6.geometry.cleanup.finalShading).family.card) + 1 : ℝ) ≤
        (Nat.log 2 (2 * p6.normalized.normalized.source.family.card) + 1 : ℝ)
      ).trans hsourceLog

/-- Fixed real coefficient in the local source-line packing bound for the
final paper conflict graph. -/
noncomputable def pureWZ2Node05P7ConflictCoefficient : ℝ :=
  2561 *
    (2 *
      (60000 *
        (24000 * pureWZ2Proposition64NormalizationConstant *
          (45 * pureWZ2Proposition64Lemma35Scale)) * 2) +
      3) ^ 6

/-- The ordinary local-packing conflict degree spends exactly
`18 * epsilon₂`: six line parameters at inverse slab-height scale, while the
seventh longitudinal parameter contributes only the fixed factor `2561`. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_conflictDegree_le_source_power
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual) :
    PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalJointPaperEDConflictLoss
        p6.normalized p6.geometry ≤
      ENNReal.ofReal pureWZ2Node05P7ConflictCoefficient *
        Kakeya.realRpowENN sourceDelta
          (-18 * schedule.ordinary.mild.epsilon₂) := by
  let power : ℝ :=
    Real.rpow sourceDelta (-3 * schedule.ordinary.mild.epsilon₂)
  let baseCoefficient : ℝ :=
    60000 *
      (24000 * pureWZ2Proposition64NormalizationConstant *
        (45 * pureWZ2Proposition64Lemma35Scale)) * 2
  let x : ℝ :=
    6 *
      (24000 * p6.normalized.normalized.prepared.normalization *
        pureWZ2Proposition64Lemma35FinalDelta sourceDelta /
          p6.normalized.normalized.prepared.slab.halfHeight) /
        (sourceDelta / 10000)
  have hsourceDelta :=
    p6.normalized.normalized.source.extremal.delta_pos
  have hsourceOne :=
    p6.normalized.normalized.source.extremal.delta_le_one
  have hpositivePower : 0 < power := by
    dsimp only [power]
    exact Real.rpow_pos_of_pos hsourceDelta _
  have hpowerOne : 1 ≤ power := by
    dsimp only [power]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hsourceDelta hsourceOne
      (by linarith [schedule.ordinary.mild.epsilon₂_pos])
  have hhalfHeight :
      p6.normalized.normalized.prepared.slab.halfHeight =
        Real.rpow sourceDelta
            (3 * schedule.ordinary.mild.epsilon₂) / 2 := by
    rw [p6.normalized.normalized.prepared.slab.halfHeight_eq,
      p6.levelCount_eq]
    unfold pureWZ2Proposition64HalfHeight
    rw [schedule.ordinary.mild.epsilon₂_eq]
    ring
  have hnegative :
      Real.rpow sourceDelta
          (-3 * schedule.ordinary.mild.epsilon₂) =
        (Real.rpow sourceDelta
          (3 * schedule.ordinary.mild.epsilon₂))⁻¹ := by
    calc
      Real.rpow sourceDelta
          (-3 * schedule.ordinary.mild.epsilon₂) =
        Real.rpow sourceDelta
          (-(3 * schedule.ordinary.mild.epsilon₂)) := by
            congr 1
            ring
      _ = (Real.rpow sourceDelta
          (3 * schedule.ordinary.mild.epsilon₂))⁻¹ :=
        Real.rpow_neg hsourceDelta.le _
  have hx : x = baseCoefficient * power := by
    dsimp only [x, baseCoefficient, power]
    rw [p6.normalized.normalized.normalization_eq, hhalfHeight, hnegative]
    unfold pureWZ2Proposition64Lemma35FinalDelta
    field_simp [hsourceDelta.ne',
      (Real.rpow_pos_of_pos hsourceDelta
        (3 * schedule.ordinary.mild.epsilon₂)).ne']
    ring
  have hbaseCoefficient : 0 ≤ baseCoefficient := by
    dsimp only [baseCoefficient]
    exact mul_nonneg
      (mul_nonneg (by norm_num) <|
        mul_nonneg
          (mul_nonneg (by norm_num)
            pureWZ2Proposition64NormalizationConstant_pos.le) <|
          mul_nonneg (by norm_num) pureWZ2Proposition64Lemma35Scale_pos.le)
      (by norm_num)
  have hxNonneg : 0 ≤ x := by
    rw [hx]
    positivity
  have hceil : (Nat.ceil x : ℝ) ≤ x + 1 :=
    (Nat.ceil_lt_add_one hxNonneg).le
  have hbase :
      ((2 * Nat.ceil x + 1 : ℕ) : ℝ) ≤
        (2 * baseCoefficient + 3) * power := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    calc
      2 * (Nat.ceil x : ℝ) + 1 ≤
          2 * (baseCoefficient * power + 1) + 1 := by
        have hceil' : (Nat.ceil x : ℝ) ≤ baseCoefficient * power + 1 := by
          simpa only [hx] using hceil
        gcongr
      _ = 2 * baseCoefficient * power + 3 := by ring
      _ ≤ 2 * baseCoefficient * power + 3 * power := by
        exact add_le_add_right
          (show (3 : ℝ) ≤ 3 * power by nlinarith [hpowerOne]) _
      _ = (2 * baseCoefficient + 3) * power := by ring
  have hpowerSix :
      power ^ 6 =
        Real.rpow sourceDelta
          (-18 * schedule.ordinary.mild.epsilon₂) := by
    dsimp only [power]
    calc
      Real.rpow sourceDelta
          (-3 * schedule.ordinary.mild.epsilon₂) ^ 6 =
        Real.rpow sourceDelta
          ((-3 * schedule.ordinary.mild.epsilon₂) * (6 : ℝ)) :=
        (Real.rpow_mul_natCast hsourceDelta.le
          (-3 * schedule.ordinary.mild.epsilon₂) 6).symm
      _ = Real.rpow sourceDelta
          (-18 * schedule.ordinary.mild.epsilon₂) := by
        congr 1
        ring
  have hcoefficientNonneg :
      0 ≤ pureWZ2Node05P7ConflictCoefficient := by
    dsimp only [pureWZ2Node05P7ConflictCoefficient]
    positivity
  have hreal :
      ((2561 * (2 * Nat.ceil x + 1) ^ 6 : ℕ) : ℝ) ≤
        pureWZ2Node05P7ConflictCoefficient * power ^ 6 := by
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    dsimp only [pureWZ2Node05P7ConflictCoefficient]
    calc
      (2561 : ℝ) * ((2 * Nat.ceil x + 1 : ℕ) : ℝ) ^ 6 ≤
          2561 * (((2 * baseCoefficient + 3) * power) ^ 6) := by
        gcongr
      _ = 2561 * (2 * baseCoefficient + 3) ^ 6 * power ^ 6 := by ring
  unfold
    PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalJointPaperEDConflictLoss
    Kakeya.Assouad.pureWZ2Proposition64PaperConflictPackingDegree
  change ((2561 * (2 * Nat.ceil x + 1) ^ 6 : ℕ) : ENNReal) ≤ _
  calc
    ((2561 * (2 * Nat.ceil x + 1) ^ 6 : ℕ) : ENNReal) =
        ENNReal.ofReal
          (((2561 * (2 * Nat.ceil x + 1) ^ 6 : ℕ) : ℝ)) := by
          rw [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal
        (pureWZ2Node05P7ConflictCoefficient * power ^ 6) :=
      ENNReal.ofReal_mono hreal
    _ = ENNReal.ofReal pureWZ2Node05P7ConflictCoefficient *
        Kakeya.realRpowENN sourceDelta
          (-18 * schedule.ordinary.mild.epsilon₂) := by
      rw [ENNReal.ofReal_mul hcoefficientNonneg, hpowerSix]
      rfl

/-- Runtime joint-density scalar receipt at the paper's `6 * epsilon₂`
rescaling loss, selected before the runtime family. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7JointDensityScalars
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual) :
    PureWZ2Proposition64JointDensityScalarReceipt
      sourceDelta
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
      p6.normalized.densityLoss
      p6.normalized.normalized.prepared.normalization
      p6.normalized.normalized.prepared.slab.halfHeight
      schedule.rescalingLoss targetDelta₀ :=
  schedule.jointDensity.runtime_receipt_exact
    p6.normalized.normalized.source.extremal.delta_pos
    p6.sourceSmall_jointDensity p6.normalized p6.geometry
    p6.levelCount_eq p6.densityLoss_eq

/-- Final density on the same combined-selected shading, weakened from the
paper's `6 * epsilon₂` receipt to the public output loss. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7FinalShadingDense
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
    (selected.finalED p6.normalized p6.geometry frostman schedule.p7Scale
      ).finalShading.IsLambdaDense
      (Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) outputLoss) := by
  have hdenseRescaling :=
    selected.finalShading_dense_of_jointAverage p6.normalized p6.geometry
      frostman schedule.p7Scale p6.p7JointDensityScalars
  have hrescalingOutput : schedule.rescalingLoss ≤ outputLoss := by
    rw [schedule.rescalingLoss_eq]
    linarith [schedule.ordinary.mild.epsilon₂_pos,
      schedule.ordinary.mild.ten_epsilon₂_lt_half_output]
  have hpower :
      Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) outputLoss ≤
        Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          schedule.rescalingLoss := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge
      p6.geometry.scales.finalDelta_pos
      (p6.geometry.scales.finalDelta_le_one_ninety_six.trans (by norm_num))
      hrescalingOutput
  change
    (restrictPaperShading selected.selected.toTubeSubfamily
      (PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalPaperED
        p6.normalized p6.geometry frostman).finalShading).IsLambdaDense _
  exact (mul_le_mul_right' hpower _).trans hdenseRescaling

/-- Raw union-volume upper on the same combined-selected final shading.
Only its family-free source-to-final power absorption remains. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7FinalVolumeUpperRaw
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
    MeasureTheory.volume
        (selected.finalED p6.normalized p6.geometry frostman schedule.p7Scale
          ).finalShading.union ≤
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.pureWZ2Proposition64VolumeCoefficient
          p6.normalized.normalized *
        Kakeya.realRpowENN sourceDelta
          (sigma - p6.normalized.normalized.inputLoss) :=
  p6.geometry.paperED_union_volume_upper
    (selected.finalED p6.normalized p6.geometry frostman schedule.p7Scale)

/-- The cubical union-volume coefficient spends only the inverse slab-height
loss `3 * epsilon₂`; all remaining factors are absolute. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_volumeCoefficient_le_source_power
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual) :
    PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.pureWZ2Proposition64VolumeCoefficient
        p6.normalized.normalized ≤
      (117 : ENNReal) *
          ENNReal.ofReal
            ((45 * pureWZ2Proposition64Lemma35Scale) ^ 3) *
        Kakeya.realRpowENN sourceDelta
          (-3 * schedule.ordinary.mild.epsilon₂) := by
  let power : ℝ :=
    Real.rpow sourceDelta (3 * schedule.ordinary.mild.epsilon₂)
  let cellCount : ℕ :=
    2 * Nat.ceil
      (2 / (45 * p6.normalized.normalized.prepared.slab.halfHeight)) + 1
  have hsourceDelta :=
    p6.normalized.normalized.source.extremal.delta_pos
  have hsourceOne :=
    p6.normalized.normalized.source.extremal.delta_le_one
  have hpowerPos : 0 < power :=
    Real.rpow_pos_of_pos hsourceDelta _
  have hpowerOne : power ≤ 1 := by
    dsimp only [power]
    exact Real.rpow_le_one hsourceDelta.le hsourceOne
      (mul_nonneg (by norm_num) schedule.ordinary.mild.epsilon₂_pos.le)
  have hinverseOne : 1 ≤ power⁻¹ :=
    (one_le_inv₀ hpowerPos).mpr hpowerOne
  have hhalfHeight :
      p6.normalized.normalized.prepared.slab.halfHeight = power / 2 := by
    dsimp only [power]
    rw [p6.normalized.normalized.prepared.slab.halfHeight_eq,
      p6.levelCount_eq]
    unfold pureWZ2Proposition64HalfHeight
    rw [schedule.ordinary.mild.epsilon₂_eq]
    ring
  let x : ℝ :=
    2 / (45 * p6.normalized.normalized.prepared.slab.halfHeight)
  have hxNonneg : 0 ≤ x := by
    dsimp only [x]
    exact div_nonneg (by norm_num)
      (mul_nonneg (by norm_num)
        p6.normalized.normalized.prepared.slab.halfHeight_pos.le)
  have hx :
      x ≤ 4 * power⁻¹ := by
    have hfraction :
        2 / (45 * p6.normalized.normalized.prepared.slab.halfHeight) ≤
          4 * power⁻¹ := by
      rw [hhalfHeight]
      field_simp [hpowerPos.ne']
      nlinarith
    exact hfraction
  have hceil :
      (Nat.ceil x : ℝ) ≤ x + 1 :=
    (Nat.ceil_lt_add_one hxNonneg).le
  dsimp only [x] at hceil
  have hcellReal :
      (cellCount : ℝ) ≤ 13 * power⁻¹ := by
    dsimp only [cellCount]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  have hcellENN :
      (cellCount : ENNReal) ≤ ENNReal.ofReal (13 * power⁻¹) := by
    have := ENNReal.ofReal_mono hcellReal
    simpa [ENNReal.ofReal_natCast] using this
  have hnegative :
      ENNReal.ofReal (13 * power⁻¹) =
        13 * Kakeya.realRpowENN sourceDelta
          (-3 * schedule.ordinary.mild.epsilon₂) := by
    have hpowerNegative :
        Real.rpow sourceDelta
            (-3 * schedule.ordinary.mild.epsilon₂) = power⁻¹ := by
      dsimp only [power]
      calc
        Real.rpow sourceDelta
            (-3 * schedule.ordinary.mild.epsilon₂) =
          Real.rpow sourceDelta
            (-(3 * schedule.ordinary.mild.epsilon₂)) := by
              congr 1
              ring
        _ = (Real.rpow sourceDelta
            (3 * schedule.ordinary.mild.epsilon₂))⁻¹ :=
          Real.rpow_neg hsourceDelta.le _
    rw [← hpowerNegative]
    simp only [Kakeya.realRpowENN]
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_num
  unfold
    PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.pureWZ2Proposition64VolumeCoefficient
  change ((3 * 3 * cellCount : ℕ) : ENNReal) *
      ENNReal.ofReal ((45 * pureWZ2Proposition64Lemma35Scale) ^ 3) ≤ _
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    (9 : ENNReal) * (cellCount : ENNReal) *
        ENNReal.ofReal ((45 * pureWZ2Proposition64Lemma35Scale) ^ 3) ≤
      9 * ENNReal.ofReal (13 * power⁻¹) *
        ENNReal.ofReal
          ((45 * pureWZ2Proposition64Lemma35Scale) ^ 3) := by
      gcongr
    _ = 117 *
          ENNReal.ofReal
            ((45 * pureWZ2Proposition64Lemma35Scale) ^ 3) *
        Kakeya.realRpowENN sourceDelta
          (-3 * schedule.ordinary.mild.epsilon₂) := by
      rw [hnegative]
      ring

/-- Public union-volume upper bound on the same combined-selected final
shading. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7FinalVolumeUpper
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
    MeasureTheory.volume
        (selected.finalED p6.normalized p6.geometry frostman schedule.p7Scale
          ).finalShading.union ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
        (sigma - outputLoss) := by
  apply p6.p7FinalVolumeUpperRaw frostman selected |>.trans
  calc
    PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.pureWZ2Proposition64VolumeCoefficient
          p6.normalized.normalized *
        Kakeya.realRpowENN sourceDelta
          (sigma - p6.normalized.normalized.inputLoss) ≤
      ((117 : ENNReal) *
          ENNReal.ofReal
            ((45 * pureWZ2Proposition64Lemma35Scale) ^ 3) *
        Kakeya.realRpowENN sourceDelta
          (-3 * schedule.ordinary.mild.epsilon₂)) *
        Kakeya.realRpowENN sourceDelta
          (sigma - p6.normalized.normalized.inputLoss) := by
      exact mul_le_mul_right'
        p6.p7_volumeCoefficient_le_source_power _
    _ = (117 : ENNReal) *
          ENNReal.ofReal
            ((45 * pureWZ2Proposition64Lemma35Scale) ^ 3) *
        Kakeya.realRpowENN sourceDelta
          (-3 * schedule.ordinary.mild.epsilon₂) *
        Kakeya.realRpowENN sourceDelta
          (sigma - p6.normalized.normalized.inputLoss) := by ring
    _ ≤ Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (sigma - outputLoss) :=
      schedule.p7Volume.absorption sourceDelta
        p6.normalized.normalized.inputLoss
        p6.normalized.normalized.source.extremal.delta_pos
        p6.sourceSmall_p7Volume p6.inputLoss_pos.le
        p6.inputLoss_le_epsilon₂

/-- Prop-6.5-style nearby-to-top-level absorption on the final target scale. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7TopLevelAbsorption
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual) :
    (4 : ENNReal) *
        Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-schedule.p7Scale.nearbyLoss) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
        (-outputLoss) :=
  schedule.p7Terminal.top_level_absorption sourceDelta
    p6.normalized.normalized.source.extremal.delta_pos
    p6.sourceSmall_p7Terminal

/-- Final local-grain constant absorption, ported from the Prop-6.5 terminal
cutoff pattern. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7LocalConstantAbsorption
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual) :
    (192 : ENNReal) *
        Kakeya.realRpowENN sourceDelta (-(outputLoss / 2)) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
        (-outputLoss) :=
  schedule.p7Terminal.local_absorption sourceDelta
    p6.normalized.normalized.source.extremal.delta_pos
    p6.sourceSmall_p7Terminal

/-- Final global-AD constant absorption, on the same pre-runtime terminal
cutoff. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7GlobalConstantAbsorption
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal sourceDelta initialLoss : ℝ}
    {schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (p6 : schedule.ActualRichEndpointP6Data actual) :
    (7077888 : ENNReal) *
        (24000 * Kakeya.realRpowENN sourceDelta (-(outputLoss / 2))) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
        (-outputLoss) :=
  schedule.p7Terminal.global_absorption sourceDelta
    p6.normalized.normalized.source.extremal.delta_pos
    p6.sourceSmall_p7Terminal

/-- The exact-child homothety factor spends precisely the paper's
`3 * epsilon₂` slab-normalization loss. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_factor_le_source_power
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
        p6.normalized p6.geometry frostman schedule.p7Scale quotient)
    (coordinate : Fin p6.p7RequestedScaleSchedule.levelCount) :
    selected.factor p6.normalized p6.geometry frostman schedule.p7Scale
        coordinate ≤
      (1 + 80 * pureWZ2Proposition64Lemma35Scale) *
        Real.rpow sourceDelta (-3 * schedule.ordinary.mild.epsilon₂) := by
  have hsourceDelta :=
    p6.normalized.normalized.source.extremal.delta_pos
  have hsourceOne :=
    p6.normalized.normalized.source.extremal.delta_le_one
  have hhalfHeight :
      p6.normalized.normalized.prepared.slab.halfHeight =
        Real.rpow sourceDelta (3 * schedule.ordinary.mild.epsilon₂) / 2 := by
    rw [p6.normalized.normalized.prepared.slab.halfHeight_eq,
      p6.levelCount_eq]
    unfold pureWZ2Proposition64HalfHeight
    rw [schedule.ordinary.mild.epsilon₂_eq]
    ring
  have hpowerPos :
      0 < Real.rpow sourceDelta
        (3 * schedule.ordinary.mild.epsilon₂) :=
    Real.rpow_pos_of_pos hsourceDelta _
  have haxial :
      40 * pureWZ2Proposition64Lemma35Scale /
          p6.normalized.normalized.prepared.slab.halfHeight =
        80 * pureWZ2Proposition64Lemma35Scale *
          Real.rpow sourceDelta
            (-3 * schedule.ordinary.mild.epsilon₂) := by
    have hnegative :
        Real.rpow sourceDelta
            (-3 * schedule.ordinary.mild.epsilon₂) =
          (Real.rpow sourceDelta
            (3 * schedule.ordinary.mild.epsilon₂))⁻¹ := by
      calc
        Real.rpow sourceDelta
            (-3 * schedule.ordinary.mild.epsilon₂) =
          Real.rpow sourceDelta
            (-(3 * schedule.ordinary.mild.epsilon₂)) := by
              congr 1
              ring
        _ = (Real.rpow sourceDelta
            (3 * schedule.ordinary.mild.epsilon₂))⁻¹ :=
          Real.rpow_neg hsourceDelta.le _
    rw [hhalfHeight, hnegative]
    field_simp [hpowerPos.ne']
    ring
  have hpowerOne :
      1 ≤ Real.rpow sourceDelta
        (-3 * schedule.ordinary.mild.epsilon₂) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hsourceDelta hsourceOne
      (by linarith [schedule.ordinary.mild.epsilon₂_pos])
  calc
    selected.factor p6.normalized p6.geometry frostman schedule.p7Scale
        coordinate ≤
      1 + 40 * pureWZ2Proposition64Lemma35Scale /
        p6.normalized.normalized.prepared.slab.halfHeight :=
      selected.factor_le_one_add_axial p6.normalized p6.geometry frostman
        schedule.p7Scale coordinate
    _ = 1 + 80 * pureWZ2Proposition64Lemma35Scale *
        Real.rpow sourceDelta
          (-3 * schedule.ordinary.mild.epsilon₂) := by rw [haxial]
    _ ≤ Real.rpow sourceDelta
          (-3 * schedule.ordinary.mild.epsilon₂) +
        80 * pureWZ2Proposition64Lemma35Scale *
          Real.rpow sourceDelta
            (-3 * schedule.ordinary.mild.epsilon₂) := by
      simpa [add_comm] using
        add_le_add_right hpowerOne
          (80 * pureWZ2Proposition64Lemma35Scale *
            Real.rpow sourceDelta
              (-3 * schedule.ordinary.mild.epsilon₂))
    _ = (1 + 80 * pureWZ2Proposition64Lemma35Scale) *
        Real.rpow sourceDelta
          (-3 * schedule.ordinary.mild.epsilon₂) := by ring

/-- Cubing the exact-child homothety factor spends `9 * epsilon₂`, exactly
as required by the three-dimensional John-volume comparison. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.ActualRichEndpointP6Data.p7_johnFactor_le_source_power
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
        p6.normalized p6.geometry frostman schedule.p7Scale quotient)
    (coordinate : Fin p6.p7RequestedScaleSchedule.levelCount) :
    ENNReal.ofReal
        (27 * (2 * selected.factor p6.normalized p6.geometry frostman
          schedule.p7Scale coordinate - 1) ^ 3) ≤
      ENNReal.ofReal
          (27 * (2 * (1 + 80 * pureWZ2Proposition64Lemma35Scale)) ^ 3) *
        Kakeya.realRpowENN sourceDelta
          (-9 * schedule.ordinary.mild.epsilon₂) := by
  let factor :=
    selected.factor p6.normalized p6.geometry frostman schedule.p7Scale
      coordinate
  let coefficient : ℝ :=
    1 + 80 * pureWZ2Proposition64Lemma35Scale
  let power : ℝ :=
    Real.rpow sourceDelta (-3 * schedule.ordinary.mild.epsilon₂)
  have hsourceDelta :=
    p6.normalized.normalized.source.extremal.delta_pos
  have hfactorOne : 1 ≤ factor :=
    selected.factor_one p6.normalized p6.geometry frostman schedule.p7Scale
      coordinate
  have hfactor :
      factor ≤ coefficient * power := by
    exact p6.p7_factor_le_source_power frostman selected coordinate
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    nlinarith [pureWZ2Proposition64Lemma35Scale_pos]
  have hpower : 0 ≤ power := by
    dsimp only [power]
    exact Real.rpow_nonneg hsourceDelta.le _
  have hlinearNonneg : 0 ≤ 2 * factor - 1 := by linarith
  have hlinear :
      2 * factor - 1 ≤ 2 * coefficient * power := by
    have hfactorNonneg : 0 ≤ factor := hfactorOne.trans' (by norm_num)
    calc
      2 * factor - 1 ≤ 2 * factor := by linarith
      _ ≤ 2 * (coefficient * power) := by gcongr
      _ = 2 * coefficient * power := by ring
  have hcube :
      (2 * factor - 1) ^ 3 ≤ (2 * coefficient * power) ^ 3 := by
    gcongr
  have hpowerCube :
      power ^ 3 =
        Real.rpow sourceDelta
          (-9 * schedule.ordinary.mild.epsilon₂) := by
    dsimp only [power]
    calc
      Real.rpow sourceDelta
          (-3 * schedule.ordinary.mild.epsilon₂) ^ 3 =
        Real.rpow sourceDelta
          ((-3 * schedule.ordinary.mild.epsilon₂) * (3 : ℝ)) :=
        (Real.rpow_mul_natCast hsourceDelta.le
          (-3 * schedule.ordinary.mild.epsilon₂) 3).symm
      _ = Real.rpow sourceDelta
          (-9 * schedule.ordinary.mild.epsilon₂) := by
        congr 1
        ring
  have hreal :
      27 * (2 * factor - 1) ^ 3 ≤
        (27 * (2 * coefficient) ^ 3) *
          Real.rpow sourceDelta
            (-9 * schedule.ordinary.mild.epsilon₂) := by
    calc
      27 * (2 * factor - 1) ^ 3 ≤
          27 * (2 * coefficient * power) ^ 3 := by gcongr
      _ = (27 * (2 * coefficient) ^ 3) * power ^ 3 := by ring
      _ = (27 * (2 * coefficient) ^ 3) *
          Real.rpow sourceDelta
            (-9 * schedule.ordinary.mild.epsilon₂) := by rw [hpowerCube]
  have hconstantNonneg :
      0 ≤ 27 * (2 * coefficient) ^ 3 := by positivity
  calc
    ENNReal.ofReal
        (27 * (2 * selected.factor p6.normalized p6.geometry frostman
          schedule.p7Scale coordinate - 1) ^ 3) =
      ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) := rfl
    _ ≤ ENNReal.ofReal
        ((27 * (2 * coefficient) ^ 3) *
          Real.rpow sourceDelta
            (-9 * schedule.ordinary.mild.epsilon₂)) :=
      ENNReal.ofReal_mono hreal
    _ = ENNReal.ofReal (27 * (2 * coefficient) ^ 3) *
        Kakeya.realRpowENN sourceDelta
          (-9 * schedule.ordinary.mild.epsilon₂) := by
      rw [ENNReal.ofReal_mul hconstantNonneg]
      rfl
    _ = ENNReal.ofReal
          (27 * (2 * (1 + 80 * pureWZ2Proposition64Lemma35Scale)) ^ 3) *
        Kakeya.realRpowENN sourceDelta
          (-9 * schedule.ordinary.mild.epsilon₂) := rfl

private theorem PureWZ2C2RichEndpointClosureSchedule.normalizedFromInitial
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal)
    {sourceDelta initialLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent)
    (hinitialLoss : 0 ≤ initialLoss)
    (hinitialCeiling : initialLoss ≤
      schedule.ordinary.ordinaryPrefix.sourceLossCeiling
        ⟨0, by
          have hN := schedule.ordinary.mild.levelCount_ge_two
          omega⟩)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma (outputLoss / 2) sourceDelta) := by
  let actual := schedule.ordinary.actualJointHeightPrefix hsourceDelta
    (hsourceSmall.trans schedule.commonDelta₀_le_ordinary) initial
    hinitialLoss hinitialCeiling hbridge
  rcases schedule.actualRichEndpointP6 hsourceDelta hsourceSmall actual
      hbridge with ⟨p6⟩
  exact ⟨p6.normalized⟩

/-- Production P0--P7 selected-source prefix.  It uses the same unique
Proposition-6.3 source and returns the exact P6 geometry together with the
Frostman receipt consumed by the canonical paper-ED construction. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.p6WithSelectedSourceFrostmanFromInitial
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal)
    {sourceDelta initialLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent)
    (hinitialLoss : 0 ≤ initialLoss)
    (hinitialCeiling : initialLoss ≤
      schedule.ordinary.ordinaryPrefix.sourceLossCeiling
        ⟨0, by
          have hN := schedule.ordinary.mild.levelCount_ge_two
          omega⟩)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    ∃ (actual : schedule.ordinary.ActualJointHeightPrefixData initial)
        (p6 : schedule.ActualRichEndpointP6Data actual),
      Nonempty
        (PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.SelectedSourceFrostmanReceipt
          p6.geometry) := by
  let actual := schedule.ordinary.actualJointHeightPrefix hsourceDelta
    (hsourceSmall.trans schedule.commonDelta₀_le_ordinary) initial
    hinitialLoss hinitialCeiling hbridge
  rcases schedule.actualRichEndpointP6 hsourceDelta hsourceSmall actual
      hbridge with ⟨p6⟩
  exact ⟨actual, p6, ⟨p6.selectedSourceFrostman schedule⟩⟩

/-- Production P7 source-cover prefix.  It retains the P0--P6 witness, its
selected-source Frostman receipt, and the raw exact-`Phi` transported parents
for the prescribed independent P7 target grid.  No target packing or
partitioning conclusion is asserted at this stage. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.p7TransportedSourceParentsFromInitial
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal)
    {sourceDelta initialLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent)
    (hinitialLoss : 0 ≤ initialLoss)
    (hinitialCeiling : initialLoss ≤
      schedule.ordinary.ordinaryPrefix.sourceLossCeiling
        ⟨0, by
          have hN := schedule.ordinary.mild.levelCount_ge_two
          omega⟩)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    ∃ (actual : schedule.ordinary.ActualJointHeightPrefixData initial)
        (p6 : schedule.ActualRichEndpointP6Data actual)
        (frostman :
          PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.SelectedSourceFrostmanReceipt
            p6.geometry),
      Nonempty
        (PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.QuantitativeVerticalTransportedSourceParentScheduleData
          p6.normalized p6.geometry frostman schedule.p7Scale) := by
  rcases schedule.p6WithSelectedSourceFrostmanFromInitial
      hsourceDelta hsourceSmall initial hinitialLoss hinitialCeiling hbridge with
    ⟨actual, p6, ⟨frostman⟩⟩
  exact ⟨actual, p6, frostman,
    p6.geometry.exists_quantitativeVerticalTransportedSourceParents
      p6.normalized frostman schedule.p7Scale p6.source_bounded_base⟩

/-- Production P7 exact-`Phi` cover/fibre prefix.  This extends the same P0--P6
witness through fixed-ratio quotienting, one combined weighted selection,
literal target covers, owner-pair regularity, local fanout one, and actual-John
rescaled-fibre CWA.  Only the final family-free scalar absorption and nearby
rounding remain outside this theorem. -/
theorem
    PureWZ2C2RichEndpointClosureSchedule.p7ActualJohnScaleCoversFromInitial
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal)
    {sourceDelta initialLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent)
    (hinitialLoss : 0 ≤ initialLoss)
    (hinitialCeiling : initialLoss ≤
      schedule.ordinary.ordinaryPrefix.sourceLossCeiling
        ⟨0, by
          have hN := schedule.ordinary.mild.levelCount_ge_two
          omega⟩)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    ∃ (actual : schedule.ordinary.ActualJointHeightPrefixData initial)
        (p6 : schedule.ActualRichEndpointP6Data actual)
        (frostman :
          PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.SelectedSourceFrostmanReceipt
            p6.geometry)
        (raw :
          PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.QuantitativeVerticalTransportedSourceParentScheduleData
            p6.normalized p6.geometry frostman schedule.p7Scale)
        (quotient :
          PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.QuantitativeVerticalTransportedSourceParentQuotientData
            p6.normalized p6.geometry frostman schedule.p7Scale raw)
        (selected :
          PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.QuantitativeVerticalTransportedSourceParentQuotientData.QuantitativeVerticalTransportedCombinedSelectionData
            p6.normalized p6.geometry frostman schedule.p7Scale quotient),
      Nonempty (∀ coordinate, WZ2PaperPureScaleCoverData selected.selected.family
          (PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.quantitativeVerticalTransportedQuotientScale
            p6.normalized p6.geometry schedule.p7Scale coordinate)
          (selected.scaleConstant p6.normalized p6.geometry frostman
            schedule.p7Scale
            coordinate)) := by
  rcases schedule.p7TransportedSourceParentsFromInitial hsourceDelta
      hsourceSmall initial hinitialLoss hinitialCeiling hbridge with
    ⟨actual, p6, frostman, ⟨raw⟩⟩
  rcases p6.geometry.exists_quantitativeVerticalTransportedSourceParentQuotient
      p6.normalized frostman schedule.p7Scale raw with ⟨quotient⟩
  rcases PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.QuantitativeVerticalTransportedSourceParentQuotientData.QuantitativeVerticalTransportedCombinedSelectionCoreData.exists_quantitativeVerticalTransportedCombinedSelection
      p6.normalized p6.geometry frostman schedule.p7Scale quotient with
    ⟨selected⟩
  exact ⟨actual, p6, frostman, raw, quotient, selected,
    ⟨selected.rawScaleData p6.normalized p6.geometry frostman schedule.p7Scale
      p6.source_bounded_base⟩⟩

/-- Production P0--P6 producer from the frozen Node-5 inputs.  The initial
Proposition-6.3 source is selected once below the already fixed global cutoff,
and the dependent ordinary/endpoint/P5/P6 chain is then run on that literal
source. -/
theorem pureWZ2_quantitativeNormalizedHierarchyFromCritical_directRich :
    PureWZ2QuantitativeNormalizedHierarchyFromCriticalStatement := by
  intro capability hbridge _grainsFromCritical sigma critical
    workLoss sourceDelta₀ hworkLoss hsourceDelta₀
  let publicLoss : ℝ := 2 * workLoss
  have hpublicLoss : 0 < publicLoss := by
    dsimp only [publicLoss]
    positivity
  rcases exists_pureWZ2C2RichEndpointClosureSchedule capability critical
      hpublicLoss hsourceDelta₀ (show (0 : ℝ) < 1 by norm_num)
      (show (64 : ℝ) ≤ 64 by norm_num) with ⟨schedule⟩
  let zero : Fin (schedule.ordinary.mild.levelCount - 1) :=
    ⟨0, by
      have hN := schedule.ordinary.mild.levelCount_ge_two
      omega⟩
  let initialCeiling :=
    schedule.ordinary.ordinaryPrefix.sourceLossCeiling zero
  have hinitialCeiling : 0 < initialCeiling :=
    schedule.ordinary.ordinaryPrefix.sourceLossCeiling_pos zero
  let requestedCutoff := min schedule.commonDelta₀ sourceDelta₀
  have hrequestedCutoff : 0 < requestedCutoff :=
    lt_min schedule.commonDelta₀_pos hsourceDelta₀
  rcases pureWZ2_hierarchy_initial_reentrant_source_production
      capability critical initialCeiling requestedCutoff
      hinitialCeiling hrequestedCutoff with
    ⟨initialLoss, sourceDelta, hinitialLoss, hinitialCeiling',
      hsourceDelta, hsourceRequested, ⟨initial⟩⟩
  have hsourceSchedule : sourceDelta ≤ schedule.commonDelta₀ :=
    hsourceRequested.trans (min_le_left _ _)
  have hsourceCaller : sourceDelta ≤ sourceDelta₀ :=
    hsourceRequested.trans (min_le_right _ _)
  refine ⟨sourceDelta, hsourceDelta, hsourceCaller, ?_⟩
  simpa only [publicLoss, mul_div_cancel_left₀ workLoss (by norm_num :
    (2 : ℝ) ≠ 0)] using schedule.normalizedFromInitial hsourceDelta
      hsourceSchedule initial hinitialLoss.le hinitialCeiling'.le hbridge

end Kakeya.Assouad

end
