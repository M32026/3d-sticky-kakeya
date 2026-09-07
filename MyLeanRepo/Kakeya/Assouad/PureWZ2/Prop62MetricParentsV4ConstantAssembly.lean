import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4Threshold
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientUpperSchedule

/-!
# Proposition 6.2 metric-parent V4 constant assembly

This module isolates the proof-irrelevant canonical-bound identities and the
scalar consequences of the canonical density and power certificates.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem pureWZ2Prop62MetricParentsV4CanonicalMassBounds_eq
    (A : ℕ) (epsilon eta c0 : ℝ)
    (A_ge_one : 1 ≤ A)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
        epsilon / 100)
    (c0_pos : 0 < c0)
    (baseStructural_ne_top :
      pureWZ2Prop62MetricParentsV4BaseStructural A eta c0 ≠ ⊤) :
    (pureWZ2Prop62MetricParentsV4CanonicalInput
      A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos
      ).massBounds =
        pureWZ2Prop62ProxyQuotientGeometryMassBounds
          A eta c0
          (Nat.ceil (1 / pureWZ2Prop62CallerStep A eta) + 2)
          (PureWZ2Prop62MetricParentsV4AllScaleSourceColor A eta)
          (pureWZ2Prop62MetricParentsV4BaseStructural A eta c0)
          baseStructural_ne_top := by
  unfold pureWZ2Prop62MetricParentsV4CanonicalInput
  rw [pureWZ2Prop62MetricParentsV4ThresholdInput_massBounds]
  unfold pureWZ2Prop62MetricParentsV4MassBounds
  unfold pureWZ2Prop62MetricParentsV4DepthBound
  unfold pureWZ2Prop62CallerAnchoredDepthBound
  rw [pureWZ2Prop62CallerStep_eq]

theorem pureWZ2Prop62_quotientDensityLoss_eq_cleanupDensityRatio
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    {metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {Color : Type*}
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    {baseSelectedParents strongUpperSelectedParents :
      Finset (Fin metric.metricParents.card)}
    {completeFiber :
      Fin metric.metricParents.card → Finset (Fin fine.card)}
    {fiberCard : Fin metric.metricParents.card → ℕ}
    {parentWeight : Fin metric.metricParents.card → ENNReal}
    {owner : Fin fine.card → Fin metric.metricParents.card}
    {sourceColor : Fin fine.card → Color}
    {fiberCardBound : ℕ}
    {preCore :
      PureWZ2Prop62PreCoreSelectionData
        (Fin fine.card) (Fin metric.metricParents.card) Color
        strongUpperSelectedParents completeFiber fiberCard parentWeight owner
        sourceColor weight fiberCardBound}
    {preliminarySubsetSelection :
      preCore.preliminary ⊆
        (quotient.selectProxyResidueUpperAncestryPerCell
          rho width packetCoordinate strideBase weight).selected}
    {receipt :
      PureWZ2Prop62CleanupReceipt
        (pureWZ2Prop62ProxyQuotientAuxiliaryLevel
          schedule fineNonempty quotient rho width packetCoordinate).tree
        preCore.preliminary}
    {metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    (ledger :
      PureWZ2Prop62ProxyQuotientMassLedger
        schedule fineNonempty quotient width packetCoordinate
        strideBase weight metric baseSelectedParents
        strongUpperSelectedParents completeFiber fiberCard
        parentWeight owner sourceColor fiberCardBound preCore
        preliminarySubsetSelection receipt metricCore) :
    metricCore.quotientDensityLoss = ledger.cleanupDensityRatio := by
  rw [PureWZ2Prop62ProxyQuotientMetricCoreOutput.quotientDensityLoss,
    PureWZ2Prop62ProxyQuotientMassLedger.cleanupDensityRatio,
    pureWZ2Prop62CleanupDensityRatio, ledger.cleanup_provenance]
  rfl

def pureWZ2Prop62MetricParentsV4DensityEnvelope
    (A : ℕ) (eta c0 delta : ℝ) : ENNReal :=
  pureWZ2Prop62MetricParentsV4DensityFixedLoss A eta c0 *
    (pureWZ2Prop62CallerCstar delta A eta) ^ 2

@[simp] theorem pureWZ2Prop62MetricParentsV4_two_mul_densityEnvelope
    (A : ℕ) (eta c0 delta : ℝ) :
    2 * pureWZ2Prop62MetricParentsV4DensityEnvelope A eta c0 delta =
      2 * pureWZ2Prop62MetricParentsV4DensityFixedLoss A eta c0 *
        (pureWZ2Prop62CallerCstar delta A eta) ^ 2 := by
  simp [pureWZ2Prop62MetricParentsV4DensityEnvelope, mul_assoc]

def pureWZ2Prop62MetricParentsV4TargetConstant
    (A : ℕ) (eta delta : ℝ) : ENNReal :=
  Kakeya.realRpowENN delta
    (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta)

def pureWZ2Prop62MetricParentsV4SourceConstant
    (A : ℕ) (eta delta : ℝ) : ENNReal :=
  pureWZ2Prop62MetricParentsV4TargetConstant A eta delta / 81000000

structure PureWZ2Prop62MetricParentsV4ConstantAssemblyData
    (A : ℕ) (eta c0 delta : ℝ) : Type where
  sourceConstant : ENNReal
  sourceConstant_eq :
    sourceConstant =
      pureWZ2Prop62MetricParentsV4SourceConstant A eta delta
  sourceConstant_finite :
    WZ2PaperFiniteErrorConstant sourceConstant
  target_finite :
    WZ2PaperFiniteErrorConstant
      (pureWZ2Prop62MetricParentsV4TargetConstant A eta delta)
  fiber_target :
    (81000000 : ENNReal) * sourceConstant =
      pureWZ2Prop62MetricParentsV4TargetConstant A eta delta
  uniformity_absorption :
    2 * pureWZ2Prop62MetricParentsV4DensityEnvelope A eta c0 delta ≤
      pureWZ2Prop62MetricParentsV4TargetConstant A eta delta
  upper_parent_absorption :
    (pureWZ2Prop62MetricParentsV4DensityEnvelope A eta c0 delta *
        pureWZ2Prop62CallerCstar delta A eta) *
        pureWZ2Prop62MetricParentsV4UpperCoefficient ≤
      pureWZ2Prop62MetricParentsV4TargetConstant A eta delta
  upper_final_scale_constant_le :
    PureWZ2Prop62ProxyQuotientMetricCoreOutput.finalUpperScaleConstant
        pureWZ2Prop62ProxyCenterCopyPackingBound
        (pureWZ2Prop62CallerCstar delta A eta)
        (pureWZ2Prop62MetricParentsV4DensityEnvelope A eta c0 delta)
        (pureWZ2Prop62CallerCstar delta A eta) ≤
      pureWZ2Prop62MetricParentsV4TargetConstant A eta delta
  envelope_absorption :
    (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) *
        (pureWZ2Prop62CallerCstar delta A eta) ^ 5 ≤
      pureWZ2Prop62MetricParentsV4TargetConstant A eta delta
  insertedConstant_le :
    ∀ {rho scale : ℝ},
      0 ≤ rho / scale →
      rho / scale ≤
        pureWZ2Prop62CallerK c0 *
          (pureWZ2Prop62CallerCstar delta A eta).toReal →
        pureWZ2Prop62InsertedCWALoss rho scale
              (pureWZ2Prop62CallerCstar delta A eta) *
            pureWZ2Prop62MetricParentsV4DensityEnvelope A eta c0 delta ≤
          sourceConstant

noncomputable def pureWZ2_prop62_metric_parents_v4_constant_assembly
    (A : ℕ) (epsilon eta c0 : ℝ)
    (A_ge_one : 1 ≤ A)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
        epsilon / 100)
    (c0_pos : 0 < c0)
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_le :
      delta ≤
        pureWZ2Prop62MetricParentsV4Threshold
          A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos) :
    PureWZ2Prop62MetricParentsV4ConstantAssemblyData
      A eta c0 delta := by
  let input :=
    pureWZ2Prop62MetricParentsV4CanonicalInput
      A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos
  let budget :=
    input.power_certificate delta_pos delta_le
  let target :=
    pureWZ2Prop62MetricParentsV4TargetConstant A eta delta
  let sourceConstant :=
    pureWZ2Prop62MetricParentsV4SourceConstant A eta delta
  let densityEnvelope :=
    pureWZ2Prop62MetricParentsV4DensityEnvelope A eta c0 delta
  have targetNeTop : target ≠ ⊤ := by
    simp [target, pureWZ2Prop62MetricParentsV4TargetConstant,
      Kakeya.realRpowENN]
  have cstarOne :
      (1 : ENNReal) ≤ pureWZ2Prop62CallerCstar delta A eta := by
    simpa only [pureWZ2Prop62CallerCstar,
      pureWZ2Prop62CallerLoss] using budget.Cstar_one
  have strongWindow :
      (81000000 : ENNReal) *
          (pureWZ2Prop62CallerCstar delta A eta) ^ 5 ≤ target := by
    have raw := input.scale_window_to_target delta_pos delta_le
    have coefficientLe :
        (81000000 : ENNReal) ≤ input.powerWindowCoefficient := by
      dsimp only [input, pureWZ2Prop62MetricParentsV4CanonicalInput,
        pureWZ2Prop62MetricParentsV4ThresholdInput]
      unfold pureWZ2Prop62MetricParentsV4WindowCoefficient
      exact le_max_left _ _
    calc
      (81000000 : ENNReal) *
            (pureWZ2Prop62CallerCstar delta A eta) ^ 5 ≤
          input.powerWindowCoefficient *
            (pureWZ2Prop62CallerCstar delta A eta) ^ 5 := by
        gcongr
      _ ≤ target := by
        simpa only [target, pureWZ2Prop62MetricParentsV4TargetConstant,
          pureWZ2Prop62CallerCstar, pureWZ2Prop62CallerLoss] using raw
  have envelopeAbsorption :
      (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) *
          (pureWZ2Prop62CallerCstar delta A eta) ^ 5 ≤ target := by
    exact (mul_le_mul_right'
      (by norm_num [pureWZ2Prop62UpperEnvelopeFactor] :
        (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) ≤ 81000000)
      ((pureWZ2Prop62CallerCstar delta A eta) ^ 5)).trans strongWindow
  have targetOne : 1 ≤ target := by
    have oneLeStrongWindow :
        (1 : ENNReal) ≤
          81000000 *
            (pureWZ2Prop62CallerCstar delta A eta) ^ 5 := by
      calc
        (1 : ENNReal) = 1 * 1 := by simp
        _ ≤
            81000000 *
              (pureWZ2Prop62CallerCstar delta A eta) ^ 5 :=
          mul_le_mul (by norm_num)
            (one_le_pow₀ cstarOne) (by simp) (by simp)
    exact oneLeStrongWindow.trans strongWindow
  have sourceConstantOne : 1 ≤ sourceConstant := by
    apply
      (ENNReal.le_div_iff_mul_le
        (Or.inl (by norm_num)) (Or.inl (by norm_num))).2
    simpa only [one_mul] using
      (show (81000000 : ENNReal) ≤ target from
        (show (81000000 : ENNReal) ≤
            81000000 *
              (pureWZ2Prop62CallerCstar delta A eta) ^ 5 by
          simpa only [mul_one] using
            mul_le_mul_left'
              (one_le_pow₀ cstarOne) (81000000 : ENNReal)
        ).trans strongWindow)
  have sourceConstantNeTop : sourceConstant ≠ ⊤ := by
    change target / 81000000 ≠ ⊤
    exact ENNReal.div_ne_top targetNeTop (by norm_num)
  have fiberTarget :
      (81000000 : ENNReal) * sourceConstant = target := by
    exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  have upperParentAbsorption :
      (densityEnvelope *
          pureWZ2Prop62CallerCstar delta A eta) *
          pureWZ2Prop62MetricParentsV4UpperCoefficient ≤
        target := by
    have raw :=
      input.upper_parent_to_target delta_pos delta_le
        (Λ := densityEnvelope) (by rfl)
    change
      (densityEnvelope *
          pureWZ2Prop62CallerCstar delta A eta) *
          pureWZ2Prop62MetricParentsV4UpperCoefficient ≤
        target at raw
    exact raw
  have uniformityAbsorption :
      2 * densityEnvelope ≤ target := by
    have raw :=
      input.upper_uniformity_to_target delta_pos delta_le
        (Λ := densityEnvelope) (by rfl)
    change
      pureWZ2Prop62MetricParentsV4UniformityCoefficient *
          pureWZ2Prop62CallerCstar delta A eta * densityEnvelope ≤
        target at raw
    have packingOne :
        (1 : ENNReal) ≤
          (pureWZ2Prop62ProxyCenterCopyPackingBound : ENNReal) := by
      change
        (1 : ENNReal) ≤
          (pureWZ2Prop62ProxyCenterCopySmallScaleBound +
            pureWZ2Prop62ProxyCenterCopyLargeScaleBound : ℕ)
      exact_mod_cast
        (Nat.succ_le_iff.mpr <|
          Nat.add_pos_right
            pureWZ2Prop62ProxyCenterCopySmallScaleBound (by
              unfold pureWZ2Prop62ProxyCenterCopyLargeScaleBound
              positivity))
    have coeffOne :
        (1 : ENNReal) ≤
          (pureWZ2Prop62ProxyCenterCopyPackingBound : ENNReal) *
            pureWZ2Prop62CallerCstar delta A eta := by
      simpa only [one_mul] using
        mul_le_mul packingOne cstarOne (by simp) (by simp)
    calc
      2 * densityEnvelope ≤
          pureWZ2Prop62MetricParentsV4UniformityCoefficient *
            pureWZ2Prop62CallerCstar delta A eta * densityEnvelope := by
        unfold pureWZ2Prop62MetricParentsV4UniformityCoefficient
        calc
          2 * densityEnvelope = (2 * 1) * densityEnvelope := by simp
          _ ≤
              (2 *
                ((pureWZ2Prop62ProxyCenterCopyPackingBound : ENNReal) *
                  pureWZ2Prop62CallerCstar delta A eta)) *
                densityEnvelope :=
            mul_le_mul_right' (mul_le_mul_left' coeffOne 2) densityEnvelope
          _ =
              (2 *
                (pureWZ2Prop62ProxyCenterCopyPackingBound : ENNReal)) *
                pureWZ2Prop62CallerCstar delta A eta * densityEnvelope := by
            ring
      _ ≤ target := raw
  have upperFinalScaleConstantLe :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput.finalUpperScaleConstant
          pureWZ2Prop62ProxyCenterCopyPackingBound
          (pureWZ2Prop62CallerCstar delta A eta)
          densityEnvelope
          (pureWZ2Prop62CallerCstar delta A eta) ≤ target := by
    apply max_le
    · have raw :=
        input.upper_uniformity_to_target delta_pos delta_le
          (Λ := densityEnvelope) (by rfl)
      change
        pureWZ2Prop62MetricParentsV4UniformityCoefficient *
            pureWZ2Prop62CallerCstar delta A eta * densityEnvelope ≤
          target at raw
      simpa [pureWZ2Prop62MetricParentsV4UniformityCoefficient,
        mul_assoc] using raw
    · have coefficientLe :
          pureWZ2Prop62UpperEnvelopeGeometricLoss * 2 ≤
            pureWZ2Prop62MetricParentsV4UpperCoefficient :=
        le_max_left _ _
      calc
        PureWZ2Prop62ProxyQuotientMetricCoreOutput.finalUpperBodyConstant
              densityEnvelope
              (pureWZ2Prop62CallerCstar delta A eta) =
            (densityEnvelope *
              pureWZ2Prop62CallerCstar delta A eta) *
                (pureWZ2Prop62UpperEnvelopeGeometricLoss * 2) := by
          simp only [
            PureWZ2Prop62ProxyQuotientMetricCoreOutput.finalUpperBodyConstant]
          ring
        _ ≤
            (densityEnvelope *
              pureWZ2Prop62CallerCstar delta A eta) *
                pureWZ2Prop62MetricParentsV4UpperCoefficient := by
          exact mul_le_mul_left' coefficientLe _
        _ ≤ target := upperParentAbsorption
  refine
    {
      sourceConstant := sourceConstant
      sourceConstant_eq := rfl
      sourceConstant_finite := ⟨sourceConstantOne, sourceConstantNeTop⟩
      target_finite := ⟨targetOne, targetNeTop⟩
      fiber_target := fiberTarget
      uniformity_absorption := ?_
      upper_parent_absorption := ?_
      upper_final_scale_constant_le := ?_
      envelope_absorption := ?_
      insertedConstant_le := ?_
    }
  · simpa [densityEnvelope] using uniformityAbsorption
  · simpa [densityEnvelope] using upperParentAbsorption
  · simpa [densityEnvelope,
      PureWZ2Prop62ProxyQuotientMetricCoreOutput.finalUpperScaleConstant,
      PureWZ2Prop62ProxyQuotientMetricCoreOutput.finalUpperBodyConstant,
      pureWZ2Prop62MetricParentsV4UniformityCoefficient,
      pureWZ2Prop62MetricParentsV4UpperCoefficient,
      mul_assoc, mul_comm, mul_left_comm] using upperFinalScaleConstantLe
  · exact envelopeAbsorption
  · intro rho scale ratio_nonneg ratio_le
    change
      pureWZ2Prop62InsertedCWALoss rho scale
            (pureWZ2Prop62CallerCstar delta A eta) *
          pureWZ2Prop62MetricParentsV4DensityEnvelope A eta c0 delta ≤
        target / 81000000
    apply
      (ENNReal.le_div_iff_mul_le
        (a :=
          pureWZ2Prop62InsertedCWALoss rho scale
              (pureWZ2Prop62CallerCstar delta A eta) *
            pureWZ2Prop62MetricParentsV4DensityEnvelope A eta c0 delta)
        (b := 81000000) (c := target)
        (Or.inl (by norm_num)) (Or.inl (by norm_num))).2
    have raw :=
      input.inserted_fiber_to_target delta_pos delta_le
        (Λ := densityEnvelope) ratio_nonneg ratio_le (by rfl)
    change
      pureWZ2Prop62MetricParentsV4InsertedCoefficient *
          ENNReal.ofReal ((rho / scale) ^ 2) *
          pureWZ2Prop62CallerCstar delta A eta * densityEnvelope ≤
        target at raw
    calc
      (pureWZ2Prop62InsertedCWALoss rho scale
            (pureWZ2Prop62CallerCstar delta A eta) *
          pureWZ2Prop62MetricParentsV4DensityEnvelope A eta c0 delta) *
          81000000 =
        pureWZ2Prop62MetricParentsV4InsertedCoefficient *
            ENNReal.ofReal ((rho / scale) ^ 2) *
            pureWZ2Prop62CallerCstar delta A eta * densityEnvelope := by
          simp only [pureWZ2Prop62InsertedCWALoss,
            pureWZ2Prop62MetricParentsV4InsertedCoefficient,
            densityEnvelope,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4000000)]
          norm_num
          ring
      _ ≤ target := raw

end Kakeya.Assouad

end
