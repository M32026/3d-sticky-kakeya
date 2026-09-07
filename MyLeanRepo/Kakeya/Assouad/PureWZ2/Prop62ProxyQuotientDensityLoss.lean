import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientMassLedger
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FixedGridBoundaryMass

/-!
# Proposition 6.2 quotient cleanup density loss

This module converts source density and the pre-core weighted retention
ledger into a bound for the single normalized density loss used by the
quotient cleanup.  It does not perform another selection or cleanup.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

def pureWZ2Prop62CleanupDensityRatio
    (depth ambientCard selectedCard : ℕ) : ENNReal :=
  (2 ^ (depth + 1) : ENNReal) *
    ambientCard * (selectedCard : ENNReal)⁻¹

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

def preCleanupLoss : ENNReal :=
  ledger.baseSelectionLoss * ledger.upperColorLoss *
    ledger.fiberBinLoss * ledger.sourceColorLoss *
    ledger.leafBinLoss

def cleanupDensityRatio : ENNReal :=
  let _ := ledger
  pureWZ2Prop62CleanupDensityRatio schedule.levelCount
    fine.card preCore.preliminary.card

structure DensityLossData
    (shading : WZ1PaperTubeShading fine)
    (density carrierVolumeConstant : ENNReal) where
  preCleanupLoss_eq :
    ledger.preCleanupLoss =
      ledger.baseSelectionLoss * ledger.upperColorLoss *
        ledger.fiberBinLoss * ledger.sourceColorLoss *
        ledger.leafBinLoss
  preliminary_weight_retention :
    (∑ source : Fin fine.card, weight source) ≤
      ledger.preCleanupLoss *
        ∑ source ∈ preCore.preliminary, weight source
  leaf_weight_band :
    ∀ source ∈ preCore.preliminary,
      preCore.leafBin.weightLevel ≤ weight source ∧
        weight source ≤ 2 * preCore.leafBin.weightLevel
  preliminary_weight_upper :
    (∑ source ∈ preCore.preliminary, weight source) ≤
      carrierVolumeConstant * Kakeya.realRpowENN delta 2 *
        (preCore.preliminary.card : ENNReal)
  weighted_cardinality :
    density * fine.enncard ≤
      (ledger.preCleanupLoss * carrierVolumeConstant) *
        (preCore.preliminary.card : ENNReal)
  cleanup_weighted_retention :
    (∑ source ∈ preCore.preliminary, weight source) ≤
      ledger.cleanupLoss *
        ∑ source ∈ receipt.core, weight source
  treeDensityLoss : ENNReal
  treeDensityLoss_eq :
    treeDensityLoss = 2 ^ (schedule.levelCount + 1)
  finiteLoss : ENNReal
  finiteLoss_eq :
    finiteLoss =
      treeDensityLoss * ledger.preCleanupLoss *
        carrierVolumeConstant
  finiteLoss_eq_factors :
    finiteLoss =
      (2 ^ (schedule.levelCount + 1) : ENNReal) *
        (ledger.baseSelectionLoss * ledger.upperColorLoss *
          ledger.fiberBinLoss * ledger.sourceColorLoss *
          ledger.leafBinLoss) * carrierVolumeConstant
  finiteLoss_ne_top : finiteLoss ≠ ⊤
  cleanup_density_ratio :
    ledger.cleanupDensityRatio ≤ finiteLoss * density⁻¹

theorem preliminary_weight_retention :
    (∑ source : Fin fine.card, weight source) ≤
      ledger.preCleanupLoss *
        ∑ source ∈ preCore.preliminary, weight source := by
  calc
    (∑ source : Fin fine.card, weight source) ≤
        ledger.baseSelectionLoss *
          ∑ parent ∈ baseSelectedParents,
            parentWeight parent :=
      ledger.base_selection_retention
    _ ≤
        ledger.baseSelectionLoss *
          (ledger.upperColorLoss *
            ∑ parent ∈ strongUpperSelectedParents,
              parentWeight parent) := by
      gcongr
      exact ledger.upper_color_retention
    _ ≤
        ledger.baseSelectionLoss *
          (ledger.upperColorLoss *
            (preCore.retention.totalLoss *
              ∑ source ∈ preCore.preliminary,
                weight source)) := by
      gcongr
      exact preCore.retention.combined_retention
    _ =
        ledger.preCleanupLoss *
          ∑ source ∈ preCore.preliminary,
            weight source := by
      simp only [preCleanupLoss,
        preCore.retention.totalLoss_eq,
        ledger.fiberBinLoss_eq,
        ledger.sourceColorLoss_eq,
        ledger.leafBinLoss_eq]
      ring

noncomputable def densityLoss
    (shading : WZ1PaperTubeShading fine)
    (density carrierVolumeConstant : ENNReal)
    (deltaPos : 0 < delta)
    (deltaSmall : delta ≤ 1 / 12)
    (fineLine : WZ1PaperIsLineClass fine)
    (density_ne_zero : density ≠ 0)
    (density_ne_top : density ≠ ⊤)
    (sourceDense : shading.IsLambdaDense density)
    (ambientWeightEq :
      ∀ source, weight source = volume (shading.carrier source))
    (carrierVolumeUpper :
      ∀ source,
        volume (shading.carrier source) ≤
          carrierVolumeConstant *
            Kakeya.realRpowENN delta 2)
    (baseSelectionLoss_ne_top :
      ledger.baseSelectionLoss ≠ ⊤)
    (upperColorLoss_ne_top :
      ledger.upperColorLoss ≠ ⊤)
    (carrierVolumeConstant_ne_top :
      carrierVolumeConstant ≠ ⊤) :
    ledger.DensityLossData
      shading density carrierVolumeConstant := by
  let scaleMass := Kakeya.realRpowENN delta 2
  have scaleMassPos :
      0 < scaleMass := by
    exact ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos deltaPos 2)
  have scaleMass_ne_top :
      scaleMass ≠ ⊤ := by
    simp [scaleMass, Kakeya.realRpowENN]
  have sourceBodyMassLower :
      fine.enncard * scaleMass ≤
        (wz1PaperBodyFamily fine).mass :=
    pureWZ2_prop62_paper_body_mass_lower
      deltaPos deltaSmall fineLine
  have sourceMassEq :
      shading.mass =
        ∑ source : Fin fine.card, weight source := by
    apply Finset.sum_congr rfl
    intro source _
    exact (ambientWeightEq source).symm
  have preRetention :=
    ledger.preliminary_weight_retention
  have preliminaryWeightUpper :
      (∑ source ∈ preCore.preliminary, weight source) ≤
        carrierVolumeConstant * scaleMass *
          (preCore.preliminary.card : ENNReal) := by
    calc
      (∑ source ∈ preCore.preliminary, weight source) ≤
          ∑ _source ∈ preCore.preliminary,
            carrierVolumeConstant * scaleMass := by
        apply Finset.sum_le_sum
        intro source _sourceMem
        rw [ambientWeightEq source]
        exact carrierVolumeUpper source
      _ =
          (preCore.preliminary.card : ENNReal) *
            (carrierVolumeConstant * scaleMass) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ =
          carrierVolumeConstant * scaleMass *
            (preCore.preliminary.card : ENNReal) := by
        ring
  have weightedWithVolume :
      scaleMass * (density * fine.enncard) ≤
        scaleMass *
          ((ledger.preCleanupLoss * carrierVolumeConstant) *
            (preCore.preliminary.card : ENNReal)) := by
    calc
      scaleMass * (density * fine.enncard) =
          density * (fine.enncard * scaleMass) := by ring
      _ ≤
          density * (wz1PaperBodyFamily fine).mass := by
        gcongr
      _ ≤ shading.mass := sourceDense
      _ =
          ∑ source : Fin fine.card, weight source :=
        sourceMassEq
      _ ≤
          ledger.preCleanupLoss *
            ∑ source ∈ preCore.preliminary, weight source :=
        preRetention
      _ ≤
          ledger.preCleanupLoss *
            (carrierVolumeConstant * scaleMass *
              (preCore.preliminary.card : ENNReal)) := by
        gcongr
      _ =
          scaleMass *
            ((ledger.preCleanupLoss * carrierVolumeConstant) *
              (preCore.preliminary.card : ENNReal)) := by
        ring
  have weightedCardinality :
      density * fine.enncard ≤
        (ledger.preCleanupLoss * carrierVolumeConstant) *
          (preCore.preliminary.card : ENNReal) :=
    (ENNReal.mul_le_mul_iff_right
      scaleMassPos.ne' scaleMass_ne_top).mp
      weightedWithVolume
  have selectedCardPos :
      0 < preCore.preliminary.card :=
    Finset.card_pos.mpr preCore.preliminary_nonempty
  have selectedCard_ne_zero :
      (preCore.preliminary.card : ENNReal) ≠ 0 := by
    exact_mod_cast selectedCardPos.ne'
  have selectedCard_ne_top :
      (preCore.preliminary.card : ENNReal) ≠ ⊤ := by
    simp
  have ambientCardBound :
      fine.enncard *
          (preCore.preliminary.card : ENNReal)⁻¹ ≤
        (ledger.preCleanupLoss * carrierVolumeConstant) *
          density⁻¹ := by
    have withoutDensity :
        fine.enncard ≤
          density⁻¹ *
            ((ledger.preCleanupLoss * carrierVolumeConstant) *
              (preCore.preliminary.card : ENNReal)) := by
      calc
        fine.enncard =
            density⁻¹ * (density * fine.enncard) := by
          rw [ENNReal.inv_mul_cancel_left
            density_ne_zero density_ne_top]
        _ ≤
            density⁻¹ *
              ((ledger.preCleanupLoss * carrierVolumeConstant) *
                (preCore.preliminary.card : ENNReal)) := by
          gcongr
    calc
      fine.enncard *
            (preCore.preliminary.card : ENNReal)⁻¹ ≤
          (density⁻¹ *
            ((ledger.preCleanupLoss * carrierVolumeConstant) *
              (preCore.preliminary.card : ENNReal))) *
            (preCore.preliminary.card : ENNReal)⁻¹ := by
        gcongr
      _ =
          (ledger.preCleanupLoss * carrierVolumeConstant) *
            density⁻¹ := by
        rw [show
          density⁻¹ *
                ((ledger.preCleanupLoss * carrierVolumeConstant) *
                  (preCore.preliminary.card : ENNReal)) *
                (preCore.preliminary.card : ENNReal)⁻¹ =
            (ledger.preCleanupLoss * carrierVolumeConstant) *
              density⁻¹ *
              ((preCore.preliminary.card : ENNReal) *
                (preCore.preliminary.card : ENNReal)⁻¹) by ring]
        rw [ENNReal.mul_inv_cancel
          selectedCard_ne_zero selectedCard_ne_top, mul_one]
  let treeDensityLoss : ENNReal :=
    2 ^ (schedule.levelCount + 1)
  let finiteLoss :=
    treeDensityLoss * ledger.preCleanupLoss *
      carrierVolumeConstant
  have cleanupDensityRatioBound :
      ledger.cleanupDensityRatio ≤
        finiteLoss * density⁻¹ := by
    unfold cleanupDensityRatio pureWZ2Prop62CleanupDensityRatio
    calc
      (2 ^ (schedule.levelCount + 1) : ENNReal) *
            fine.card *
            (preCore.preliminary.card : ENNReal)⁻¹ =
          treeDensityLoss *
            (fine.enncard *
              (preCore.preliminary.card : ENNReal)⁻¹) := by
        simp only [treeDensityLoss,
          Kakeya.Streamlined.TubeFamily.enncard]
        ring
      _ ≤
          treeDensityLoss *
            ((ledger.preCleanupLoss * carrierVolumeConstant) *
              density⁻¹) := by
        gcongr
      _ = finiteLoss * density⁻¹ := by
        simp only [finiteLoss]
        ring
  have fiberBinLoss_ne_top :
      ledger.fiberBinLoss ≠ ⊤ := by
    rw [ledger.fiberBinLoss_eq,
      preCore.retention.fiberBinLoss_eq]
    simp
  have sourceColorLoss_ne_top :
      ledger.sourceColorLoss ≠ ⊤ := by
    rw [ledger.sourceColorLoss_eq,
      preCore.retention.sourceColorLoss_eq]
    simp
  have leafBinLoss_ne_top :
      ledger.leafBinLoss ≠ ⊤ := by
    rw [ledger.leafBinLoss_eq,
      preCore.retention.leafBinLoss_eq]
    exact ENNReal.mul_ne_top (by norm_num) (by simp)
  have treeDensityLoss_ne_top :
      treeDensityLoss ≠ ⊤ := by
    simp [treeDensityLoss]
  have preCleanupLoss_ne_top :
      ledger.preCleanupLoss ≠ ⊤ := by
    unfold preCleanupLoss
    exact
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top
              baseSelectionLoss_ne_top upperColorLoss_ne_top)
              fiberBinLoss_ne_top)
            sourceColorLoss_ne_top)
        leafBinLoss_ne_top
  have finiteLoss_ne_top :
      finiteLoss ≠ ⊤ := by
    exact
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          treeDensityLoss_ne_top preCleanupLoss_ne_top)
        carrierVolumeConstant_ne_top
  exact
    {
      preCleanupLoss_eq := rfl
      preliminary_weight_retention := preRetention
      leaf_weight_band := preCore.leaf_weight_band
      preliminary_weight_upper := preliminaryWeightUpper
      weighted_cardinality := weightedCardinality
      cleanup_weighted_retention :=
        ledger.weighted_cleanup_retention
      treeDensityLoss := treeDensityLoss
      treeDensityLoss_eq := rfl
      finiteLoss := finiteLoss
      finiteLoss_eq := rfl
      finiteLoss_eq_factors := by
        simp only [finiteLoss, treeDensityLoss, preCleanupLoss]
      finiteLoss_ne_top := finiteLoss_ne_top
      cleanup_density_ratio := cleanupDensityRatioBound
    }

noncomputable def densityLossOfPaperGeometry
    (shading : WZ1PaperTubeShading fine)
    (density : ENNReal)
    (deltaPos : 0 < delta)
    (deltaSmall : delta ≤ 1 / 24)
    (fineLine : WZ1PaperIsLineClass fine)
    (density_ne_zero : density ≠ 0)
    (density_ne_top : density ≠ ⊤)
    (sourceDense : shading.IsLambdaDense density)
    (ambientWeightEq :
      ∀ source, weight source = volume (shading.carrier source))
    (baseSelectionLoss_ne_top :
      ledger.baseSelectionLoss ≠ ⊤)
    (upperColorLoss_ne_top :
      ledger.upperColorLoss ≠ ⊤) :
    ledger.DensityLossData shading density
      (55296 * Kakeya.deltaTubeVolume 1) := by
  apply ledger.densityLoss
    shading density
      (55296 * Kakeya.deltaTubeVolume 1)
      deltaPos (deltaSmall.trans (by norm_num))
      fineLine density_ne_zero density_ne_top sourceDense
      ambientWeightEq
  · intro source
    have carrierSubset :
        shading.carrier source ⊆
          wz1PaperTubeCarrier (fine.tube source) :=
      shading.subset_body source
    have carrierBound :
        volume (wz1PaperTubeCarrier (fine.tube source)) ≤
          (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN delta 2 :=
      (wz2PaperTubeCarrier_convex_and_volume_quadratic
        wz2_paper_tube_carrier_geometry deltaPos deltaSmall
        (fine.tube source) (fineLine source)).2
    exact (measure_mono carrierSubset).trans carrierBound
  · exact baseSelectionLoss_ne_top
  · exact upperColorLoss_ne_top
  · exact ENNReal.mul_ne_top
      (by norm_num)
      (tube_volume_scaling.2.1 (1 : ℝ)
        (by norm_num) (by norm_num)).2

end PureWZ2Prop62ProxyQuotientMassLedger

end Kakeya.Assouad

end
