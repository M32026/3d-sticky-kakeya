import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PreCoreSelectionAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientMetricCore

/-!
# Proposition 6.2 quotient mass ledger

This module composes the already chosen base selection, whole-fiber
cardinality bin, parentwise source colors, global leaf-weight bin, and one
weighted tree cleanup.  It neither performs a new selection nor constructs a
new cleanup.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62ProxyQuotientMassLedger
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    {Color : Type*}
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    (baseSelectedParents :
      Finset (Fin metric.metricParents.card))
    (strongUpperSelectedParents :
      Finset (Fin metric.metricParents.card))
    (completeFiber :
      Fin metric.metricParents.card →
        Finset (Fin fine.card))
    (fiberCard :
      Fin metric.metricParents.card → ℕ)
    (parentWeight :
      Fin metric.metricParents.card → ENNReal)
    (owner :
      Fin fine.card → Fin metric.metricParents.card)
    (sourceColor : Fin fine.card → Color)
    (fiberCardBound : ℕ)
    (preCore :
      PureWZ2Prop62PreCoreSelectionData
        (Fin fine.card) (Fin metric.metricParents.card) Color
        strongUpperSelectedParents completeFiber fiberCard parentWeight owner
        sourceColor weight fiberCardBound)
    (preliminarySubsetSelection :
      preCore.preliminary ⊆
        (quotient.selectProxyResidueUpperAncestryPerCell
          rho width packetCoordinate strideBase weight).selected)
    (receipt :
      PureWZ2Prop62CleanupReceipt
        (pureWZ2Prop62ProxyQuotientAuxiliaryLevel
          schedule fineNonempty quotient rho width packetCoordinate).tree
        preCore.preliminary)
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight) where
  metric_provenance :
    metricCore.metric = metric
  cleanup_provenance :
    metricCore.cleanup =
      pureWZ2Prop62ProxyQuotientOnePassCleanupOfReceipt
        schedule fineNonempty quotient rho width
          packetCoordinate strideBase weight
          preCore.preliminary preCore.preliminary_nonempty
          preliminarySubsetSelection receipt
  baseSelectionLoss : ENNReal
  upperColorLoss : ENNReal
  fiberBinLoss : ENNReal
  fiberBinLoss_eq :
    fiberBinLoss = preCore.retention.fiberBinLoss
  sourceColorLoss : ENNReal
  sourceColorLoss_eq :
    sourceColorLoss = preCore.retention.sourceColorLoss
  leafBinLoss : ENNReal
  leafBinLoss_eq :
    leafBinLoss = preCore.retention.leafBinLoss
  cleanupLoss : ENNReal
  cleanupLoss_eq :
    cleanupLoss = 2 ^ (schedule.levelCount + 2)
  totalLoss : ENNReal
  totalLoss_eq :
    totalLoss =
      baseSelectionLoss * upperColorLoss * fiberBinLoss *
        sourceColorLoss * leafBinLoss * cleanupLoss
  base_selection_retention :
    (∑ source : Fin fine.card, weight source) ≤
      baseSelectionLoss *
        ∑ parent ∈ baseSelectedParents, parentWeight parent
  upper_color_retention :
    (∑ parent ∈ baseSelectedParents, parentWeight parent) ≤
      upperColorLoss *
        ∑ parent ∈ strongUpperSelectedParents,
          parentWeight parent
  fiber_bin_retention :
    (∑ parent ∈ strongUpperSelectedParents,
        parentWeight parent) ≤
      fiberBinLoss *
        ∑ parent ∈ preCore.fiberBin.selectedParents,
          parentWeight parent
  source_color_retention :
    (∑ source ∈ preCore.wholeLeaves, weight source) ≤
      sourceColorLoss *
        ∑ source ∈ preCore.leafBin.colorSelected,
          weight source
  leaf_bin_retention :
    (∑ source ∈ preCore.leafBin.colorSelected,
        weight source) ≤
      leafBinLoss *
        ∑ source ∈ preCore.preliminary, weight source
  weighted_cleanup_retention :
    (∑ source ∈ preCore.preliminary, weight source) ≤
      cleanupLoss *
        ∑ source ∈ receipt.core, weight source
  ambientCore_eq_receipt :
    metricCore.ambientCore = receipt.core
  pulledBack_image_eq_receipt :
    Finset.image
        metricCore.metric.mesh.complete.selectedFine.embedding
        metricCore.pulledBack =
      receipt.core
  pulledBack_mass_eq_receipt :
    (∑ source ∈ metricCore.pulledBack,
        weight
          (metricCore.metric.mesh.complete.selectedFine.embedding
            source)) =
      ∑ source ∈ receipt.core, weight source
  final_mass_retention :
    (∑ source : Fin fine.card, weight source) ≤
      totalLoss *
        ∑ source ∈ metricCore.pulledBack,
          weight
            (metricCore.metric.mesh.complete.selectedFine.embedding
              source)

noncomputable def pureWZ2_prop62_proxy_quotient_mass_ledger
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    {Color : Type*}
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    (baseSelectedParents :
      Finset (Fin metric.metricParents.card))
    (strongUpperSelectedParents :
      Finset (Fin metric.metricParents.card))
    (completeFiber :
      Fin metric.metricParents.card →
        Finset (Fin fine.card))
    (fiberCard :
      Fin metric.metricParents.card → ℕ)
    (parentWeight :
      Fin metric.metricParents.card → ENNReal)
    (owner :
      Fin fine.card → Fin metric.metricParents.card)
    (sourceColor : Fin fine.card → Color)
    (fiberCardBound : ℕ)
    (preCore :
      PureWZ2Prop62PreCoreSelectionData
        (Fin fine.card) (Fin metric.metricParents.card) Color
        strongUpperSelectedParents completeFiber fiberCard parentWeight owner
        sourceColor weight fiberCardBound)
    (receipt :
      PureWZ2Prop62CleanupReceipt
        (pureWZ2Prop62ProxyQuotientAuxiliaryLevel
          schedule fineNonempty quotient rho width packetCoordinate).tree
        preCore.preliminary)
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (metricProvenance :
      metricCore.metric = metric)
    (preliminarySubsetSelection :
      preCore.preliminary ⊆
        (quotient.selectProxyResidueUpperAncestryPerCell
          rho width packetCoordinate strideBase weight).selected)
    (cleanupProvenance :
      metricCore.cleanup =
        pureWZ2Prop62ProxyQuotientOnePassCleanupOfReceipt
          schedule fineNonempty quotient rho width
            packetCoordinate strideBase weight
            preCore.preliminary preCore.preliminary_nonempty
            preliminarySubsetSelection receipt)
    (baseSelectionLoss : ENNReal)
    (baseSelectionRetention :
      (∑ source : Fin fine.card, weight source) ≤
        baseSelectionLoss *
          ∑ parent ∈ baseSelectedParents,
            parentWeight parent)
    (upperColorLoss : ENNReal)
    (upperColorRetention :
      (∑ parent ∈ baseSelectedParents,
          parentWeight parent) ≤
        upperColorLoss *
          ∑ parent ∈ strongUpperSelectedParents,
            parentWeight parent) :
    PureWZ2Prop62ProxyQuotientMassLedger
      schedule fineNonempty quotient width packetCoordinate
      strideBase weight metric baseSelectedParents
      strongUpperSelectedParents completeFiber fiberCard
      parentWeight owner sourceColor fiberCardBound preCore
      preliminarySubsetSelection receipt metricCore := by
  let fiberBinLoss := preCore.retention.fiberBinLoss
  let sourceColorLoss := preCore.retention.sourceColorLoss
  let leafBinLoss := preCore.retention.leafBinLoss
  let cleanupLoss : ENNReal :=
    2 ^ (schedule.levelCount + 2)
  let totalLoss :=
    baseSelectionLoss * upperColorLoss * fiberBinLoss *
      sourceColorLoss * leafBinLoss * cleanupLoss
  have cleanupPreliminaryEq :
      metricCore.cleanup.preliminary =
        preCore.preliminary := by
    rw [cleanupProvenance]
    rfl
  have cleanupCoreEq :
      metricCore.cleanup.core.core =
        receipt.core := by
    rw [cleanupProvenance]
    rfl
  have ambientCoreEqReceipt :
      metricCore.ambientCore = receipt.core := by
    rw [metricCore.ambientCore_eq, cleanupCoreEq]
  have pulledBackImageEqReceipt :
      Finset.image
          metricCore.metric.mesh.complete.selectedFine.embedding
          metricCore.pulledBack =
        receipt.core := by
    rw [metricCore.image_eq, ambientCoreEqReceipt]
  have cleanupRetention :
      (∑ source ∈ preCore.preliminary, weight source) ≤
        cleanupLoss *
          ∑ source ∈ receipt.core, weight source := by
    have receiptRetention :=
      receipt.weighted_retention
        weight preCore.leafBin.weightLevel
        (fun source sourceMem =>
          (preCore.leaf_weight_band source sourceMem).1)
        (fun source sourceMem =>
          (preCore.leaf_weight_band source sourceMem).2)
    simpa only [cleanupLoss, Nat.add_assoc] using
      receiptRetention
  have pulledBackMassEqReceipt :
      (∑ source ∈ metricCore.pulledBack,
          weight
            (metricCore.metric.mesh.complete.selectedFine.embedding
              source)) =
        ∑ source ∈ receipt.core, weight source := by
    have imageSum :
        (∑ ambientSource ∈
            Finset.image
              metricCore.metric.mesh.complete.selectedFine.embedding
              metricCore.pulledBack,
            weight ambientSource) =
          ∑ source ∈ metricCore.pulledBack,
            weight
              (metricCore.metric.mesh.complete.selectedFine.embedding
                source) :=
      Finset.sum_image
        metricCore.metric.mesh.complete.selectedFine.embedding.injective.injOn
    rw [pulledBackImageEqReceipt] at imageSum
    exact imageSum.symm
  have finalMassRetention :
      (∑ source : Fin fine.card, weight source) ≤
        totalLoss *
          ∑ source ∈ metricCore.pulledBack,
            weight
              (metricCore.metric.mesh.complete.selectedFine.embedding
                source) := by
    calc
      (∑ source : Fin fine.card, weight source) ≤
          baseSelectionLoss *
            ∑ parent ∈ baseSelectedParents,
              parentWeight parent :=
        baseSelectionRetention
      _ ≤
          baseSelectionLoss *
            (upperColorLoss *
              ∑ parent ∈ strongUpperSelectedParents,
                parentWeight parent) := by
        gcongr
      _ ≤
          baseSelectionLoss *
            (upperColorLoss *
              (preCore.retention.totalLoss *
                ∑ source ∈ preCore.preliminary,
                  weight source)) := by
        gcongr
        exact preCore.retention.combined_retention
      _ ≤
          baseSelectionLoss *
            (upperColorLoss *
              (preCore.retention.totalLoss *
                (cleanupLoss *
                  ∑ source ∈ receipt.core,
                    weight source))) := by
        gcongr
      _ =
          totalLoss *
            ∑ source ∈ receipt.core, weight source := by
        simp only [totalLoss, fiberBinLoss, sourceColorLoss,
          leafBinLoss, preCore.retention.totalLoss_eq]
        ring
      _ =
          totalLoss *
            ∑ source ∈ metricCore.pulledBack,
              weight
                (metricCore.metric.mesh.complete.selectedFine.embedding
                  source) := by
        rw [pulledBackMassEqReceipt]
  exact
    {
      metric_provenance := metricProvenance
      cleanup_provenance := by
        simpa only [cleanupPreliminaryEq] using cleanupProvenance
      baseSelectionLoss := baseSelectionLoss
      upperColorLoss := upperColorLoss
      fiberBinLoss := fiberBinLoss
      fiberBinLoss_eq := rfl
      sourceColorLoss := sourceColorLoss
      sourceColorLoss_eq := rfl
      leafBinLoss := leafBinLoss
      leafBinLoss_eq := rfl
      cleanupLoss := cleanupLoss
      cleanupLoss_eq := rfl
      totalLoss := totalLoss
      totalLoss_eq := by
        simp only [totalLoss]
      base_selection_retention := baseSelectionRetention
      upper_color_retention := upperColorRetention
      fiber_bin_retention :=
        preCore.retention.whole_fiber_retention
      source_color_retention :=
        preCore.retention.source_color_retention
      leaf_bin_retention :=
        preCore.retention.leaf_bin_retention
      weighted_cleanup_retention := cleanupRetention
      ambientCore_eq_receipt := ambientCoreEqReceipt
      pulledBack_image_eq_receipt := pulledBackImageEqReceipt
      pulledBack_mass_eq_receipt := pulledBackMassEqReceipt
      final_mass_retention := finalMassRetention
    }

end Kakeya.Assouad

end
