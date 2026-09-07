import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientDensityLoss
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientMassAbsorption
import Mathlib.Tactic

/-!
# Proposition 6.2 quotient cleanup-density power

This module converts the exact quotient cleanup-density ratio into the power
bound used by the final CWA budget.  The source density contributes one copy
of `Cstar`; the two dyadic logarithmic factors in the pre-cleanup loss are
absorbed into one further copy.

All constants in `densityFixedLoss` are fixed before the runtime scale and
tube family are introduced.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Canonical depth bound for the caller-anchored geometric schedule. -/
def pureWZ2Prop62CallerAnchoredDepthBound
    (A : ℕ) (eta : ℝ) : ℕ :=
  Nat.ceil (1 / (2 * (A : ℝ) * eta)) + 2

/--
The fixed coefficient left after separating the two logarithmic factors from
the quotient density loss.
-/
def pureWZ2Prop62ProxyQuotientDensityFixedLoss
    (A : ℕ) (eta c0 : ℝ)
    (bounds :
      PureWZ2Prop62ProxyQuotientMassFixedBounds A eta c0) :
    ENNReal :=
  (2 : ENNReal) ^
      (pureWZ2Prop62CallerAnchoredDepthBound A eta + 1) *
    bounds.baseStructural *
    bounds.strongUpperVector *
    ENNReal.ofReal bounds.fiberBinCoefficient *
    bounds.sourceColor *
    ENNReal.ofReal bounds.leafBinCoefficient *
    (55296 * Kakeya.deltaTubeVolume 1)

theorem pureWZ2Prop62ProxyQuotientDensityFixedLoss_ne_top
    (A : ℕ) (eta c0 : ℝ)
    (bounds :
      PureWZ2Prop62ProxyQuotientMassFixedBounds A eta c0) :
    pureWZ2Prop62ProxyQuotientDensityFixedLoss
        A eta c0 bounds ≠ ⊤ := by
  unfold pureWZ2Prop62ProxyQuotientDensityFixedLoss
  exact
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top
              (ENNReal.mul_ne_top
                (ENNReal.pow_ne_top (by simp))
                bounds.baseStructural_ne_top)
              bounds.strongUpperVector_ne_top)
            ENNReal.ofReal_ne_top)
          bounds.sourceColor_ne_top)
        ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top
        (by norm_num)
        (tube_volume_scaling.2.1 (1 : ℝ)
          (by norm_num) (by norm_num)).2)

/--
A scale threshold, chosen from `A`, `eta`, and `c0` before any runtime family,
which absorbs the two logarithmic factors into one copy of `Cstar`.
-/
structure PureWZ2Prop62ProxyQuotientDensityPowerCertificate
    (A : ℕ) (eta c0 : ℝ) where
  delta0 : ℝ
  delta0_pos : 0 < delta0
  delta0_le_one : delta0 ≤ 1
  log_square_le_Cstar :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
      (ENNReal.ofReal (1 + Real.log delta⁻¹)) ^ 2 ≤
        pureWZ2Prop62CallerCstar delta A eta

theorem exists_pureWZ2Prop62ProxyQuotientDensityPowerCertificate
    (A : ℕ) (A_ge_one : 1 ≤ A)
    (eta c0 : ℝ) (eta_pos : 0 < eta) :
    Nonempty
      (PureWZ2Prop62ProxyQuotientDensityPowerCertificate
        A eta c0) := by
  have loss_pos :
      0 < pureWZ2Prop62CallerLoss A eta :=
    pureWZ2Prop62CallerLoss_pos A_ge_one eta_pos
  rcases
      exists_delta_log_absorbed_ennreal
        (1 : ENNReal) (by simp)
        (B := pureWZ2Prop62CallerLoss A eta)
        loss_pos (n := 2) (by norm_num) with
    ⟨delta0, delta0_pos, delta0_le_one, absorbed⟩
  refine
    ⟨{
      delta0 := delta0
      delta0_pos := delta0_pos
      delta0_le_one := delta0_le_one
      log_square_le_Cstar := ?_
    }⟩
  intro delta delta_pos delta_le
  simpa [pureWZ2Prop62CallerCstar] using
    absorbed delta delta_pos delta_le

namespace PureWZ2Prop62ProxyQuotientMassLedger

variable
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
    {baseSelectedParents :
      Finset (Fin metric.metricParents.card)}
    {strongUpperSelectedParents :
      Finset (Fin metric.metricParents.card)}
    {completeFiber :
      Fin metric.metricParents.card →
        Finset (Fin fine.card)}
    {fiberCard :
      Fin metric.metricParents.card → ℕ}
    {parentWeight :
      Fin metric.metricParents.card → ENNReal}
    {owner :
      Fin fine.card → Fin metric.metricParents.card}
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
        preliminarySubsetSelection receipt metricCore)

theorem densityFiniteLoss_le_fixed_mul_log_square
    {A : ℕ} {eta c0 : ℝ}
    (bounds :
      PureWZ2Prop62ProxyQuotientMassFixedBounds A eta c0)
    {shading : WZ1PaperTubeShading fine}
    (densityData :
      ledger.DensityLossData shading
        (Kakeya.realRpowENN delta
          (pureWZ2Prop62CallerLoss A eta))
        (55296 * Kakeya.deltaTubeVolume 1))
    (depth_le :
      schedule.levelCount ≤
        pureWZ2Prop62CallerAnchoredDepthBound A eta)
    (base_le :
      ledger.baseSelectionLoss ≤ bounds.baseStructural)
    (upper_le :
      ledger.upperColorLoss ≤ bounds.strongUpperVector)
    (fiber_le :
      ledger.fiberBinLoss ≤
        ENNReal.ofReal
          (bounds.fiberBinCoefficient *
            (1 + Real.log delta⁻¹)))
    (source_le :
      ledger.sourceColorLoss ≤ bounds.sourceColor)
    (leaf_le :
      ledger.leafBinLoss ≤
        ENNReal.ofReal
          (bounds.leafBinCoefficient *
            (1 + Real.log delta⁻¹)))
    (delta_pos : 0 < delta)
    (delta_le_one : delta ≤ 1) :
    densityData.finiteLoss ≤
      pureWZ2Prop62ProxyQuotientDensityFixedLoss
          A eta c0 bounds *
        (ENNReal.ofReal (1 + Real.log delta⁻¹)) ^ 2 := by
  have logarithm_nonneg : 0 ≤ 1 + Real.log delta⁻¹ := by
    have inverse_one : 1 ≤ delta⁻¹ := by
      calc
        (1 : ℝ) = (1 : ℝ)⁻¹ := by norm_num
        _ ≤ delta⁻¹ := by gcongr
    linarith [Real.log_nonneg inverse_one]
  have fiber_le' :
      ledger.fiberBinLoss ≤
        ENNReal.ofReal bounds.fiberBinCoefficient *
          ENNReal.ofReal (1 + Real.log delta⁻¹) := by
    calc
      ledger.fiberBinLoss ≤
          ENNReal.ofReal
            (bounds.fiberBinCoefficient *
              (1 + Real.log delta⁻¹)) := fiber_le
      _ =
          ENNReal.ofReal bounds.fiberBinCoefficient *
            ENNReal.ofReal (1 + Real.log delta⁻¹) :=
        ENNReal.ofReal_mul bounds.fiberBinCoefficient_nonneg
  have leaf_le' :
      ledger.leafBinLoss ≤
        ENNReal.ofReal bounds.leafBinCoefficient *
          ENNReal.ofReal (1 + Real.log delta⁻¹) := by
    calc
      ledger.leafBinLoss ≤
          ENNReal.ofReal
            (bounds.leafBinCoefficient *
              (1 + Real.log delta⁻¹)) := leaf_le
      _ =
          ENNReal.ofReal bounds.leafBinCoefficient *
            ENNReal.ofReal (1 + Real.log delta⁻¹) :=
        ENNReal.ofReal_mul bounds.leafBinCoefficient_nonneg
  have tree_le :
      (2 ^ (schedule.levelCount + 1) : ENNReal) ≤
        2 ^
          (pureWZ2Prop62CallerAnchoredDepthBound A eta + 1) := by
    exact pow_le_pow_right₀ (by norm_num) <|
      Nat.add_le_add_right depth_le 1
  rw [densityData.finiteLoss_eq_factors]
  calc
    (2 ^ (schedule.levelCount + 1) : ENNReal) *
          (ledger.baseSelectionLoss * ledger.upperColorLoss *
            ledger.fiberBinLoss * ledger.sourceColorLoss *
            ledger.leafBinLoss) *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        2 ^
            (pureWZ2Prop62CallerAnchoredDepthBound A eta + 1) *
          (bounds.baseStructural * bounds.strongUpperVector *
            (ENNReal.ofReal bounds.fiberBinCoefficient *
              ENNReal.ofReal (1 + Real.log delta⁻¹)) *
            bounds.sourceColor *
            (ENNReal.ofReal bounds.leafBinCoefficient *
              ENNReal.ofReal (1 + Real.log delta⁻¹))) *
          (55296 * Kakeya.deltaTubeVolume 1) := by
      gcongr
    _ =
        pureWZ2Prop62ProxyQuotientDensityFixedLoss
            A eta c0 bounds *
          (ENNReal.ofReal (1 + Real.log delta⁻¹)) ^ 2 := by
      unfold pureWZ2Prop62ProxyQuotientDensityFixedLoss
      ring

theorem cleanupDensityRatio_le_fixedLoss_mul_Cstar_sq
    {A : ℕ} {eta c0 : ℝ}
    (bounds :
      PureWZ2Prop62ProxyQuotientMassFixedBounds A eta c0)
    (certificate :
      PureWZ2Prop62ProxyQuotientDensityPowerCertificate
        A eta c0)
    {shading : WZ1PaperTubeShading fine}
    (densityData :
      ledger.DensityLossData shading
        (Kakeya.realRpowENN delta
          (pureWZ2Prop62CallerLoss A eta))
        (55296 * Kakeya.deltaTubeVolume 1))
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ certificate.delta0)
    (depth_le :
      schedule.levelCount ≤
        pureWZ2Prop62CallerAnchoredDepthBound A eta)
    (base_le :
      ledger.baseSelectionLoss ≤ bounds.baseStructural)
    (upper_le :
      ledger.upperColorLoss ≤ bounds.strongUpperVector)
    (fiber_le :
      ledger.fiberBinLoss ≤
        ENNReal.ofReal
          (bounds.fiberBinCoefficient *
            (1 + Real.log delta⁻¹)))
    (source_le :
      ledger.sourceColorLoss ≤ bounds.sourceColor)
    (leaf_le :
      ledger.leafBinLoss ≤
        ENNReal.ofReal
          (bounds.leafBinCoefficient *
            (1 + Real.log delta⁻¹))) :
    ledger.cleanupDensityRatio ≤
      pureWZ2Prop62ProxyQuotientDensityFixedLoss
          A eta c0 bounds *
        (pureWZ2Prop62CallerCstar delta A eta) ^ 2 := by
  have delta_le_one : delta ≤ 1 :=
    delta_le.trans certificate.delta0_le_one
  have finiteLoss_le :=
    ledger.densityFiniteLoss_le_fixed_mul_log_square
      bounds densityData depth_le base_le upper_le
      fiber_le source_le leaf_le delta_pos delta_le_one
  have density_inv :
      (Kakeya.realRpowENN delta
        (pureWZ2Prop62CallerLoss A eta))⁻¹ =
          pureWZ2Prop62CallerCstar delta A eta := by
    rw [pure_wz2_realRpowENN_inv delta_pos]
    rfl
  calc
    ledger.cleanupDensityRatio ≤
        densityData.finiteLoss *
          (Kakeya.realRpowENN delta
            (pureWZ2Prop62CallerLoss A eta))⁻¹ :=
      densityData.cleanup_density_ratio
    _ ≤
        (pureWZ2Prop62ProxyQuotientDensityFixedLoss
            A eta c0 bounds *
          (ENNReal.ofReal (1 + Real.log delta⁻¹)) ^ 2) *
          pureWZ2Prop62CallerCstar delta A eta := by
      rw [density_inv]
      gcongr
    _ ≤
        (pureWZ2Prop62ProxyQuotientDensityFixedLoss
            A eta c0 bounds *
          pureWZ2Prop62CallerCstar delta A eta) *
          pureWZ2Prop62CallerCstar delta A eta := by
      gcongr
      exact certificate.log_square_le_Cstar delta delta_pos delta_le
    _ =
        pureWZ2Prop62ProxyQuotientDensityFixedLoss
            A eta c0 bounds *
          (pureWZ2Prop62CallerCstar delta A eta) ^ 2 := by
      ring

end PureWZ2Prop62ProxyQuotientMassLedger

end Kakeya.Assouad

end
