import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryMetricParentsOutput

/-!
# Proposition 6.2: ancestry metric-parent mass retention

This module records the complete finite loss before the final metric-parent
output:

1. one upper-ancestry color in every occupied metric cell;
2. one global dependent color vector;
3. one global leaf-weight dyadic bin;
4. the pre-core complete metric-fiber cardinality bin `D_-`;
5. the one augmented-tree cleanup.

The exact finite factor is separated from its eventual small-`delta`
polylogarithmic absorption.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62AncestryMetricPreliminaryOutput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow}
    {scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {coordinateCount : ℕ}
    {Color : Fin coordinateCount → Type*}
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    {color : ∀ coordinate, Fin fine.card → Color coordinate}
    {weight : Fin fine.card → ENNReal}
    {preliminary :
      PureWZ2Prop62AncestryPreliminarySelectionData
        schedule scheduled rho width packetCoordinate
        Color color weight}
    {M : ℝ}
    (output :
      PureWZ2Prop62AncestryMetricPreliminaryOutput
        schedule scheduled width packetCoordinate
        Color color weight preliminary M)

/-- The exact product of all finite losses before the final output. -/
def finalMetricMassRetentionLoss : ENNReal :=
  ((Fintype.card
      (Fin 4 → ZMod (preliminary.residueStrideBase + 1)) : ENNReal) *
    (Fintype.card
      (schedule.UpperColorVector rho packetCoordinate) : ENNReal)) *
    (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
    (2 * preliminary.preliminary.dyadicBinCount : ENNReal) *
    (output.metricFiberCardinalityBin.fiberBinCount : ENNReal) *
    (2 ^ (schedule.levelCount + 2) : ENNReal)

theorem sum_activeWeight_eq_perCell :
    (∑ source : Fin fine.card, preliminary.activeWeight source) =
      ∑ source ∈ preliminary.perCell.selected, weight source := by
  rw [preliminary.activeWeight_eq]
  calc
    (∑ source : Fin fine.card,
        if source ∈ preliminary.perCell.selected then weight source else 0) =
        ∑ source ∈
            (Finset.univ.filter fun source =>
              source ∈ preliminary.perCell.selected),
          weight source := by
      exact
        (Finset.sum_filter
          (s := (Finset.univ : Finset (Fin fine.card)))
          (p := fun source => source ∈ preliminary.perCell.selected)
          (f := weight)).symm
    _ = ∑ source ∈ preliminary.perCell.selected, weight source := by
      congr 1
      ext source
      simp

theorem sum_selectedPreliminary_weight :
    (∑ source ∈ preliminary.preliminary.selected,
        preliminary.activeWeight source) =
      ∑ source ∈ output.selectedPreliminary,
        output.preliminarySourceWeight source := by
  rw [← output.selectedPreliminary_image_eq]
  exact
    Finset.sum_image
      (fun first _ second _ indexEq =>
        output.metric.mesh.complete.selectedFine.embedding.injective indexEq)

theorem sum_binnedAmbientPreliminary_weight :
    (∑ source ∈ output.binnedAmbientPreliminary,
        preliminary.activeWeight source) =
      ∑ source ∈ output.metricFiberCardinalityBin.binnedPreliminary,
        output.preliminarySourceWeight source := by
  unfold binnedAmbientPreliminary
  unfold MetricFiberCardinalityBinData.ambientPreliminary
  exact
    Finset.sum_image
      (fun first _ second _ indexEq =>
        output.metric.mesh.complete.selectedFine.embedding.injective indexEq)

theorem ambientCore_subset_perCell :
    output.ancestryAuxiliaryCore.ambientCore ⊆
      preliminary.perCell.selected := by
  exact
    output.ancestryAuxiliaryCore.ambientCore_subset_preliminary |>.trans <|
      output.binnedAmbientPreliminary_subset_original |>.trans
        preliminary.selected_subset_perCell

theorem ambientCore_activeWeight_eq_weight
    {source : Fin fine.card}
    (sourceMem : source ∈ output.ancestryAuxiliaryCore.ambientCore) :
    preliminary.activeWeight source = weight source := by
  rw [preliminary.activeWeight_eq]
  simp [output.ambientCore_subset_perCell sourceMem]

theorem finalMetricWeight_eq_ambientCore :
    (∑ source :
        Fin output.finalMetricRestriction.fineSelected.family.card,
        weight
          (output.metric.mesh.complete.selectedFine.embedding
            (output.finalMetricRestriction.fineSelected.embedding source))) =
      ∑ source ∈ output.ancestryAuxiliaryCore.ambientCore,
        weight source := by
  let ambientCore := output.ancestryAuxiliaryCore.ambientCore
  let ambientFamily :=
    output.ancestryAuxiliaryCore.pullback.ambientCoreFine
  calc
    (∑ source :
        Fin output.finalMetricRestriction.fineSelected.family.card,
        weight
          (output.metric.mesh.complete.selectedFine.embedding
            (output.finalMetricRestriction.fineSelected.embedding source))) =
        ∑ source : Fin ambientFamily.family.card,
          weight (ambientFamily.embedding source) := by
      exact
        Fintype.sum_equiv output.finalToAmbientCoreEquiv
          (fun source :
              Fin output.finalMetricRestriction.fineSelected.family.card =>
            weight
              (output.metric.mesh.complete.selectedFine.embedding
                (output.finalMetricRestriction.fineSelected.embedding
                  source)))
          (fun source : Fin ambientFamily.family.card =>
            weight (ambientFamily.embedding source))
          (fun source => by
            exact congrArg weight
              (output.finalToAmbientCoreEquiv_embedding source).symm)
    _ =
        ∑ source : ambientCore, weight source.1 := by
      let equivalence : Fin ambientCore.card ≃ ambientCore :=
        (ambientCore.orderIsoOfFin rfl).toEquiv
      exact
        Fintype.sum_equiv equivalence
          (fun source : Fin ambientFamily.family.card =>
            weight (ambientFamily.embedding source))
          (fun source : ambientCore => weight source.1)
          (fun _ => rfl)
    _ =
        ∑ source ∈ output.ancestryAuxiliaryCore.ambientCore,
          weight source := by
      exact Finset.sum_coe_sort ambientCore weight

theorem binnedPreliminary_to_ambientCore_weight :
    (∑ source ∈ output.binnedAmbientPreliminary,
        preliminary.activeWeight source) ≤
      (2 ^ (schedule.levelCount + 2) : ENNReal) *
        ∑ source ∈ output.ancestryAuxiliaryCore.ambientCore,
          preliminary.activeWeight source := by
  have treeRetention :=
    output.ancestryAuxiliary.tree.dyadic_weight_retention
      output.binnedAmbientPreliminary preliminary.activeWeight
      preliminary.preliminary.weightLevel
      (fun source sourceMem =>
        (preliminary.preliminary.selected_weight_band source
          (output.binnedAmbientPreliminary_subset_original sourceMem)).1)
      (fun source sourceMem =>
        (preliminary.preliminary.selected_weight_band source
          (output.binnedAmbientPreliminary_subset_original sourceMem)).2)
  have canonical :
      (∑ source ∈ output.binnedAmbientPreliminary,
          preliminary.activeWeight source) ≤
        (2 ^ (schedule.levelCount + 2) : ENNReal) *
          ∑ source ∈
              output.ancestryAuxiliary.coreIndices
                output.binnedAmbientPreliminary,
            preliminary.activeWeight source := by
    simpa only [
      PureWZ2Prop62AuxiliaryLevel.tree,
      PureWZ2Prop62AuxiliaryLevel.coreIndices,
      PureWZ2Prop62AuxiliaryLevel.coreOutput,
      Nat.add_assoc
    ] using treeRetention
  rw [← output.ancestryAuxiliaryCore.ambientCore_eq] at canonical
  exact canonical

/--
The full paper-order exact finite-factor inequality, including the `D_-`
parent bin and the unique augmented-tree cleanup.
-/
theorem totalWeight_le_finalMetricMassRetentionLoss_mul_final :
    (∑ source : Fin fine.card, weight source) ≤
      output.finalMetricMassRetentionLoss *
        ∑ source :
            Fin output.finalMetricRestriction.fineSelected.family.card,
          weight
            (output.metric.mesh.complete.selectedFine.embedding
              (output.finalMetricRestriction.fineSelected.embedding
                source)) := by
  let perCellLoss : ENNReal :=
    (Fintype.card
      (Fin 4 → ZMod (preliminary.residueStrideBase + 1)) : ENNReal) *
      (Fintype.card
        (schedule.UpperColorVector rho packetCoordinate) : ENNReal)
  let globalColorLoss : ENNReal :=
    Fintype.card (∀ coordinate, Color coordinate)
  let leafBinLoss : ENNReal :=
    2 * preliminary.preliminary.dyadicBinCount
  let fiberBinLoss : ENNReal :=
    output.metricFiberCardinalityBin.fiberBinCount
  let treeLoss : ENNReal :=
    2 ^ (schedule.levelCount + 2)
  calc
    (∑ source : Fin fine.card, weight source) ≤
        perCellLoss *
          ∑ source ∈ preliminary.perCell.selected, weight source :=
      preliminary.perCell.weight_retention
    _ =
        perCellLoss *
          ∑ source : Fin fine.card, preliminary.activeWeight source := by
      rw [sum_activeWeight_eq_perCell]
    _ ≤
        perCellLoss *
          (globalColorLoss *
            ∑ source ∈ preliminary.preliminary.colorClass,
              preliminary.activeWeight source) := by
      gcongr
      exact preliminary.preliminary.color_retention
    _ ≤
        perCellLoss *
          (globalColorLoss *
            (leafBinLoss *
              ∑ source ∈ preliminary.preliminary.selected,
                preliminary.activeWeight source)) := by
      gcongr
      exact preliminary.preliminary.dyadic_retention
    _ =
        perCellLoss *
          (globalColorLoss *
            (leafBinLoss *
              ∑ source ∈ output.selectedPreliminary,
                output.preliminarySourceWeight source)) := by
      rw [output.sum_selectedPreliminary_weight]
    _ ≤
        perCellLoss *
          (globalColorLoss *
            (leafBinLoss *
              (fiberBinLoss *
                ∑ source ∈
                    output.metricFiberCardinalityBin.binnedPreliminary,
                  output.preliminarySourceWeight source))) := by
      gcongr
      exact
        output.metricFiberCardinalityBin.binnedPreliminary_weight_retention
    _ =
        perCellLoss *
          (globalColorLoss *
            (leafBinLoss *
              (fiberBinLoss *
                ∑ source ∈ output.binnedAmbientPreliminary,
                  preliminary.activeWeight source))) := by
      rw [output.sum_binnedAmbientPreliminary_weight]
    _ ≤
        perCellLoss *
          (globalColorLoss *
            (leafBinLoss *
              (fiberBinLoss *
                (treeLoss *
                  ∑ source ∈ output.ancestryAuxiliaryCore.ambientCore,
                    preliminary.activeWeight source)))) := by
      gcongr
      exact output.binnedPreliminary_to_ambientCore_weight
    _ =
        perCellLoss *
          (globalColorLoss *
            (leafBinLoss *
              (fiberBinLoss *
                (treeLoss *
                  ∑ source ∈ output.ancestryAuxiliaryCore.ambientCore,
                    weight source)))) := by
      have sumEq :
          (∑ source ∈ output.ancestryAuxiliaryCore.ambientCore,
              preliminary.activeWeight source) =
            ∑ source ∈ output.ancestryAuxiliaryCore.ambientCore,
              weight source := by
        apply Finset.sum_congr rfl
        intro source sourceMem
        exact output.ambientCore_activeWeight_eq_weight sourceMem
      rw [sumEq]
    _ =
        output.finalMetricMassRetentionLoss *
          ∑ source :
              Fin output.finalMetricRestriction.fineSelected.family.card,
            weight
              (output.metric.mesh.complete.selectedFine.embedding
                (output.finalMetricRestriction.fineSelected.embedding
                  source)) := by
      rw [output.finalMetricWeight_eq_ambientCore]
      simp only [finalMetricMassRetentionLoss, perCellLoss,
        globalColorLoss, leafBinLoss, fiberBinLoss, treeLoss]
      ring

/-- The outer small-scale gate converting the exact finite factor to a log loss. -/
structure FinalMetricMassRetentionAbsorptionData
    (logExponent : ℕ) : Prop where
  scalar :
    wz2PaperPureRefinementFraction delta logExponent *
        output.finalMetricMassRetentionLoss ≤
      1

/--
Paper-level budget for the five finite losses.  Bounding each loss by two
logarithms gives the absolute exponent `10` used in
`prop62-metric-parent-mass`.
-/
structure FinalMetricMassRetentionLogBudget : Prop where
  logBase_pos :
    0 < ENNReal.ofReal (Real.log (1 / delta))
  perCell :
    (Fintype.card
        (Fin 4 → ZMod (preliminary.residueStrideBase + 1)) : ENNReal) *
      (Fintype.card
        (schedule.UpperColorVector rho packetCoordinate) : ENNReal) ≤
      (ENNReal.ofReal (Real.log (1 / delta))) ^ 2
  globalColor :
    (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) ≤
      (ENNReal.ofReal (Real.log (1 / delta))) ^ 2
  leafBin :
    (2 * preliminary.preliminary.dyadicBinCount : ENNReal) ≤
      (ENNReal.ofReal (Real.log (1 / delta))) ^ 2
  fiberBin :
    (output.metricFiberCardinalityBin.fiberBinCount : ENNReal) ≤
      (ENNReal.ofReal (Real.log (1 / delta))) ^ 2
  tree :
    (2 ^ (schedule.levelCount + 2) : ENNReal) ≤
      (ENNReal.ofReal (Real.log (1 / delta))) ^ 2

theorem finalMetricMassRetentionLoss_le_log_ten
    (budget : output.FinalMetricMassRetentionLogBudget) :
    output.finalMetricMassRetentionLoss ≤
      (ENNReal.ofReal (Real.log (1 / delta))) ^ 10 := by
  unfold finalMetricMassRetentionLoss
  calc
    ((Fintype.card
          (Fin 4 → ZMod (preliminary.residueStrideBase + 1)) : ENNReal) *
        (Fintype.card
          (schedule.UpperColorVector rho packetCoordinate) : ENNReal)) *
        (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
        (2 * preliminary.preliminary.dyadicBinCount : ENNReal) *
        (output.metricFiberCardinalityBin.fiberBinCount : ENNReal) *
        (2 ^ (schedule.levelCount + 2) : ENNReal) ≤
      (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 *
        (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
        (2 * preliminary.preliminary.dyadicBinCount : ENNReal) *
        (output.metricFiberCardinalityBin.fiberBinCount : ENNReal) *
        (2 ^ (schedule.levelCount + 2) : ENNReal) := by
      gcongr
      exact budget.perCell
    _ ≤
      (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 *
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 *
        (2 * preliminary.preliminary.dyadicBinCount : ENNReal) *
        (output.metricFiberCardinalityBin.fiberBinCount : ENNReal) *
        (2 ^ (schedule.levelCount + 2) : ENNReal) := by
      gcongr
      exact budget.globalColor
    _ ≤
      (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 *
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 *
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 *
        (output.metricFiberCardinalityBin.fiberBinCount : ENNReal) *
        (2 ^ (schedule.levelCount + 2) : ENNReal) := by
      gcongr
      exact budget.leafBin
    _ ≤
      (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 *
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 *
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 *
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 *
        (2 ^ (schedule.levelCount + 2) : ENNReal) := by
      gcongr
      exact budget.fiberBin
    _ ≤
      (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 *
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 *
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 *
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 *
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 := by
      exact
        mul_le_mul_left'
          budget.tree
          ((ENNReal.ofReal (Real.log (1 / delta))) ^ 2 *
            (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 *
            (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 *
            (ENNReal.ofReal (Real.log (1 / delta))) ^ 2)
    _ = (ENNReal.ofReal (Real.log (1 / delta))) ^ 10 := by
      ring

theorem finalMetricMassRetentionAbsorption_ten
    (budget : output.FinalMetricMassRetentionLogBudget) :
    output.FinalMetricMassRetentionAbsorptionData 10 := by
  let logBase : ENNReal :=
    ENNReal.ofReal (Real.log (1 / delta))
  have logBase_ne_zero : logBase ≠ 0 :=
    budget.logBase_pos.ne'
  have logBase_ne_top : logBase ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have logPower_ne_zero : logBase ^ 10 ≠ 0 :=
    pow_ne_zero 10 logBase_ne_zero
  have logPower_ne_top : logBase ^ 10 ≠ ⊤ :=
    ENNReal.pow_ne_top logBase_ne_top
  refine ⟨?_⟩
  calc
    wz2PaperPureRefinementFraction delta 10 *
        output.finalMetricMassRetentionLoss ≤
      wz2PaperPureRefinementFraction delta 10 *
        logBase ^ 10 := by
      gcongr
      exact output.finalMetricMassRetentionLoss_le_log_ten budget
    _ = (logBase ^ 10)⁻¹ * (logBase ^ 10) := by
      simp only [wz2PaperPureRefinementFraction, logBase,
        ENNReal.inv_pow]
    _ = 1 :=
      ENNReal.inv_mul_cancel logPower_ne_zero logPower_ne_top

theorem finalMetric_core_weight_retention
    {logExponent : ℕ}
    (absorption :
      output.FinalMetricMassRetentionAbsorptionData logExponent) :
    wz2PaperPureRefinementFraction delta logExponent *
        (∑ source : Fin fine.card, weight source) ≤
      ∑ source :
          Fin output.finalMetricRestriction.fineSelected.family.card,
        weight
          (output.metric.mesh.complete.selectedFine.embedding
            (output.finalMetricRestriction.fineSelected.embedding source)) := by
  calc
    wz2PaperPureRefinementFraction delta logExponent *
        (∑ source : Fin fine.card, weight source) ≤
      wz2PaperPureRefinementFraction delta logExponent *
        (output.finalMetricMassRetentionLoss *
          ∑ source :
              Fin output.finalMetricRestriction.fineSelected.family.card,
            weight
              (output.metric.mesh.complete.selectedFine.embedding
                (output.finalMetricRestriction.fineSelected.embedding
                  source))) := by
      gcongr
      exact output.totalWeight_le_finalMetricMassRetentionLoss_mul_final
    _ =
      (wz2PaperPureRefinementFraction delta logExponent *
        output.finalMetricMassRetentionLoss) *
          ∑ source :
              Fin output.finalMetricRestriction.fineSelected.family.card,
            weight
              (output.metric.mesh.complete.selectedFine.embedding
                (output.finalMetricRestriction.fineSelected.embedding
                  source)) := by
      ring
    _ ≤
        1 *
          ∑ source :
              Fin output.finalMetricRestriction.fineSelected.family.card,
            weight
              (output.metric.mesh.complete.selectedFine.embedding
                (output.finalMetricRestriction.fineSelected.embedding
                  source)) := by
      gcongr
      exact absorption.scalar
    _ = _ := by simp

/--
The paper-facing ancestry metric-parent constructor.  Its only quantitative
input is the outer small-scale absorption of the exact finite loss; the full
mass-retention inequality is generated internally.
-/
theorem metricParentsOutput
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (conflict :
      PureWZ2Prop62SourceConflictCoordinateData Color color)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (actualScaleLeOne :
      ∀ coordinate, schedule.actualScale coordinate ≤ 1)
    (widthPos : 0 < width)
    (packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (scaleSeparation : 100 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.finalMetricRestriction.fineSelected.family.tube
          source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (fineBoundedBase : HasBoundedBase fine 4)
    (logExponent : ℕ)
    (absorption :
      output.FinalMetricMassRetentionAbsorptionData logExponent) :
    Nonempty
      (PureWZ2Prop62MetricParentsOutput
        (rho := rho) (schedule.scaleData packetCoordinate)
        weight logExponent) := by
  exact
    output.metricParentsOutput_of_massRetention
      coordinates conflict rhoPos rhoLeOne actualScaleLeOne
      widthPos packetScaleLtRho
      sixWidthLe allAncestryCoordinatesUpper scaleSeparation
      fineAxisBox fineBoundedBase logExponent
      (output.finalMetric_core_weight_retention absorption)

/--
Fixed-exponent paper-facing constructor.  The five explicit logarithmic
budgets imply the `log^-10` mass retention internally.
-/
theorem metricParentsOutput_logTen
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (conflict :
      PureWZ2Prop62SourceConflictCoordinateData Color color)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (actualScaleLeOne :
      ∀ coordinate, schedule.actualScale coordinate ≤ 1)
    (widthPos : 0 < width)
    (packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (scaleSeparation : 100 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.finalMetricRestriction.fineSelected.family.tube
          source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (fineBoundedBase : HasBoundedBase fine 4)
    (budget : output.FinalMetricMassRetentionLogBudget) :
    Nonempty
      (PureWZ2Prop62MetricParentsOutput
        (rho := rho) (schedule.scaleData packetCoordinate)
        weight 10) := by
  exact
    output.metricParentsOutput
      coordinates conflict rhoPos rhoLeOne actualScaleLeOne
      widthPos packetScaleLtRho
      sixWidthLe allAncestryCoordinatesUpper scaleSeparation
      fineAxisBox fineBoundedBase 10
      (output.finalMetricMassRetentionAbsorption_ten budget)

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
