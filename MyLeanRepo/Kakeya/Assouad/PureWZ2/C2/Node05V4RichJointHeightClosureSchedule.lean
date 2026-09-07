import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightScheduledOneScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichNeighborhoodDensity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichNeighborhoodCommonBinBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSourcePopularCapacityScalar
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64MildRescalingScalarSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64JointDensitySchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalProjectionThreshold
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalUniformBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantOrdinaryScalarClosure

/-!
# Global closure schedule for Node 5

The direct-rich two-call kernel must be selected before the accepted source
loss is frozen.  The source ceiling is the minimum of the density allocation
and the actual first-kernel source loss.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2C2OrdinaryLossSchedule
    (capability : PureWZ2PropStickyCapability)
    {sigma floorLoss structuralBudget : ℝ}
    (floorSchedule : PureWZ2ReentryTraceFloorSchedule
      sigma floorLoss structuralBudget)
    (scaleLoss : ℝ) where
  finalLoss : ℝ := floorSchedule.densityLoss / 8
  finalLoss_eq : finalLoss = floorSchedule.densityLoss / 8
  finalLoss_pos : 0 < finalLoss
  finalLoss_le_one : finalLoss ≤ 1
  stickyLoss : ℝ
  stickyLoss_pos : 0 < stickyLoss
  stickyLoss_le_final : stickyLoss ≤ finalLoss
  calls : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss
  sourceLossCeiling : ℝ :=
    min (floorSchedule.densityLoss / 8)
      (calls.firstCallSchedule capability).kernel.sourceLoss
  sourceLossCeiling_eq :
    sourceLossCeiling =
      min (floorSchedule.densityLoss / 8)
        (calls.firstCallSchedule capability).kernel.sourceLoss
  sourceLossCeiling_pos : 0 < sourceLossCeiling
  sourceLossCeiling_le_firstKernel :
    sourceLossCeiling ≤
      (calls.firstCallSchedule capability).kernel.sourceLoss
  sourceLossCeiling_le_density_eighth :
    sourceLossCeiling ≤ floorSchedule.densityLoss / 8
  density_gap :
    sourceLossCeiling + (1 - calls.firstOutputLoss) * finalLoss <
      floorSchedule.densityLoss
  densityThreshold : PureWZ2Node05V4RichJointDensityThreshold
    sourceLossCeiling floorSchedule.densityLoss finalLoss calls.firstOutputLoss

theorem PureWZ2ReentryTraceFloorSchedule.c2OrdinaryLossSchedule
    (capability : PureWZ2PropStickyCapability)
    {sigma floorLoss structuralBudget scaleLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (floorSchedule : PureWZ2ReentryTraceFloorSchedule
      sigma floorLoss structuralBudget)
    (hfloorOne : floorLoss ≤ 1)
    (stickyLoss : ℝ)
    (hstickyPos : 0 < stickyLoss)
    (hstickyFinal : stickyLoss ≤ floorSchedule.densityLoss / 8)
    (hscaleNonneg : 0 ≤ scaleLoss) :
    Nonempty { ordinary : PureWZ2C2OrdinaryLossSchedule
      capability floorSchedule scaleLoss // ordinary.stickyLoss = stickyLoss } := by
  let finalLoss := floorSchedule.densityLoss / 8
  have hfinalPos : 0 < finalLoss := by
    dsimp only [finalLoss]
    exact div_pos floorSchedule.densityLoss_pos (by norm_num)
  have hfinalOne : finalLoss ≤ 1 := by
    dsimp only [finalLoss]
    have hdensityOne :=
      floorSchedule.densityLoss_le_floor.trans hfloorOne
    linarith
  have hstickyOne : stickyLoss ≤ 1 :=
    hstickyFinal.trans hfinalOne
  rcases pureWZ2Node05V4RichSecondCallSchedule_nonempty
      sigma critical stickyLoss hstickyPos hstickyOne with ⟨calls⟩
  let sourceLossCeiling :=
    min (floorSchedule.densityLoss / 8)
      (calls.firstCallSchedule capability).kernel.sourceLoss
  have hsourcePos : 0 < sourceLossCeiling := by
    dsimp only [sourceLossCeiling]
    exact lt_min hfinalPos
      (calls.firstCallSchedule capability).kernel.sourceLoss_pos
  have hsourceFirst :
      sourceLossCeiling ≤
        (calls.firstCallSchedule capability).kernel.sourceLoss :=
    min_le_right _ _
  have hsourceDensity :
      sourceLossCeiling ≤ floorSchedule.densityLoss / 8 :=
    min_le_left _ _
  have hgap :
      sourceLossCeiling + (1 - calls.firstOutputLoss) * finalLoss <
        floorSchedule.densityLoss := by
    have hdensityPos := floorSchedule.densityLoss_pos
    have hfirstPos := calls.calls.firstOutputLoss_pos
    dsimp only [finalLoss]
    nlinarith
  rcases pureWZ2Node05V4RichJoint_density_threshold
      hfinalPos hfinalOne hgap with ⟨densityThreshold⟩
  exact ⟨⟨{
    finalLoss := finalLoss
    finalLoss_eq := rfl
    finalLoss_pos := hfinalPos
    finalLoss_le_one := hfinalOne
    stickyLoss := stickyLoss
    stickyLoss_pos := hstickyPos
    stickyLoss_le_final := hstickyFinal
    calls := calls
    sourceLossCeiling := sourceLossCeiling
    sourceLossCeiling_eq := rfl
    sourceLossCeiling_pos := hsourcePos
    sourceLossCeiling_le_firstKernel := hsourceFirst
    sourceLossCeiling_le_density_eighth := hsourceDensity
    density_gap := hgap
    densityThreshold := densityThreshold
  }, rfl⟩⟩

/-- The two nested trace floors needed at one ordinary level.  The outer
schedule refreshes the hierarchy source at `transitionLoss`; its scalar
closure fixes the strictly smaller `grainLoss`.  The inner schedule then
proves the P3 one-scale geometry at a still smaller working loss. -/
structure PureWZ2C2OrdinaryTransitionLayer
    (sigma nextSourceCeiling scaleLoss : ℝ) where
  transitionLoss : ℝ
  transitionLoss_pos : 0 < transitionLoss
  transitionLoss_le_next : transitionLoss ≤ nextSourceCeiling
  transitionLoss_le_next_eighth : transitionLoss ≤ nextSourceCeiling / 8
  transitionLoss_le_graphBudget :
    transitionLoss ≤ scaleLoss * sigma / 8192
  transitionStructuralBudget : ℝ
  transitionStructuralBudget_pos : 0 < transitionStructuralBudget
  transitionStructuralBudget_le_half :
    transitionStructuralBudget ≤ transitionLoss / 2
  traceSchedule : PureWZ2ReentryTraceFloorSchedule
    sigma transitionLoss transitionStructuralBudget
  scalarClosure :
    PureWZ2HierarchyReentrantOrdinaryScalarClosure traceSchedule
  grainLoss : ℝ := scalarClosure.grainLoss
  grainLoss_eq : grainLoss = scalarClosure.grainLoss
  grainLoss_pos : 0 < grainLoss
  grainLoss_le_transition : grainLoss ≤ transitionLoss
  grainLoss_le_next : grainLoss ≤ nextSourceCeiling
  grainLoss_le_one : grainLoss ≤ 1
  finalStructuralBudget : ℝ
  finalStructuralBudget_pos : 0 < finalStructuralBudget
  finalStructuralBudget_le_grain : finalStructuralBudget ≤ grainLoss
  finalFloorSchedule : PureWZ2ReentryTraceFloorSchedule
    sigma grainLoss finalStructuralBudget

theorem PureWZ2CriticalPackage.c2OrdinaryTransitionLayer
    {sigma nextSourceCeiling scaleLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (hnext : 0 < nextSourceCeiling)
    (hnextOne : nextSourceCeiling ≤ 1)
    (hnextGraph : nextSourceCeiling ≤ scaleLoss * sigma / 1024) :
    Nonempty (PureWZ2C2OrdinaryTransitionLayer
      sigma nextSourceCeiling scaleLoss) := by
  let transitionLoss := nextSourceCeiling / 8
  have htransitionPos : 0 < transitionLoss := by
    dsimp only [transitionLoss]
    positivity
  have htransitionNext : transitionLoss ≤ nextSourceCeiling := by
    dsimp only [transitionLoss]
    linarith
  have htransitionGraph :
      transitionLoss ≤ scaleLoss * sigma / 8192 := by
    dsimp only [transitionLoss]
    calc
      nextSourceCeiling / 8 ≤
          (scaleLoss * sigma / 1024) / 8 := by gcongr
      _ = scaleLoss * sigma / 8192 := by ring
  let transitionStructuralBudget := transitionLoss / 2
  have htransitionStructuralPos : 0 < transitionStructuralBudget := by
    dsimp only [transitionStructuralBudget]
    positivity
  rcases critical.reentryTraceFloorSchedule htransitionPos
      htransitionStructuralPos (by
        dsimp only [transitionStructuralBudget]
        linarith) with
    ⟨traceSchedule⟩
  rcases pureWZ2_reentrantOrdinary_scalarClosure traceSchedule le_rfl with
    ⟨scalarClosure⟩
  let grainLoss := scalarClosure.grainLoss
  have hgrainPos : 0 < grainLoss := by
    dsimp only [grainLoss]
    rw [scalarClosure.grainLoss_eq]
    exact div_pos traceSchedule.densityLoss_pos (by norm_num)
  have hgrainTransition : grainLoss ≤ transitionLoss := by
    dsimp only [grainLoss]
    rw [scalarClosure.grainLoss_eq]
    exact (div_le_self traceSchedule.densityLoss_pos.le
      (by norm_num)).trans traceSchedule.densityLoss_le_floor
  have hgrainNext := hgrainTransition.trans htransitionNext
  let finalStructuralBudget := min (grainLoss / 2) (sigma / 2)
  have hfinalStructuralPos : 0 < finalStructuralBudget := by
    dsimp only [finalStructuralBudget]
    exact lt_min (div_pos hgrainPos (by norm_num))
      (div_pos critical.sigma_pos (by norm_num))
  have hfinalStructuralGrain : finalStructuralBudget ≤ grainLoss :=
    (min_le_left _ _).trans (by linarith)
  rcases critical.reentryTraceFloorSchedule hgrainPos hfinalStructuralPos
      hfinalStructuralGrain with ⟨finalFloorSchedule⟩
  exact ⟨{
    transitionLoss := transitionLoss
    transitionLoss_pos := htransitionPos
    transitionLoss_le_next := htransitionNext
    transitionLoss_le_next_eighth := le_rfl
    transitionLoss_le_graphBudget := htransitionGraph
    transitionStructuralBudget := transitionStructuralBudget
    transitionStructuralBudget_pos := htransitionStructuralPos
    transitionStructuralBudget_le_half := le_rfl
    traceSchedule := traceSchedule
    scalarClosure := scalarClosure
    grainLoss := grainLoss
    grainLoss_eq := rfl
    grainLoss_pos := hgrainPos
    grainLoss_le_transition := hgrainTransition
    grainLoss_le_next := hgrainNext
    grainLoss_le_one := hgrainNext.trans hnextOne
    finalStructuralBudget := finalStructuralBudget
    finalStructuralBudget_pos := hfinalStructuralPos
    finalStructuralBudget_le_grain := hfinalStructuralGrain
    finalFloorSchedule := finalFloorSchedule
  }⟩

structure PureWZ2C2OrdinaryLevelSchedule
    (capability : PureWZ2PropStickyCapability)
    (sigma nextSourceCeiling scaleLoss : ℝ) where
  transition : PureWZ2C2OrdinaryTransitionLayer
    sigma nextSourceCeiling scaleLoss
  grainLoss : ℝ := transition.grainLoss
  grainLoss_eq : grainLoss = transition.grainLoss
  floorSchedule : PureWZ2ReentryTraceFloorSchedule
    sigma grainLoss transition.finalStructuralBudget
  ordinary : PureWZ2C2OrdinaryLossSchedule
    capability floorSchedule scaleLoss
  outputLoss : ℝ := ordinary.finalLoss
  outputLoss_eq : outputLoss = ordinary.finalLoss
  outputLoss_pos : 0 < outputLoss
  outputLoss_le_next : outputLoss ≤ nextSourceCeiling
  outputLoss_le_next_eighth : outputLoss ≤ nextSourceCeiling / 8
  outputLoss_le_graphBudget : outputLoss ≤ scaleLoss * sigma / 8192
  outputLoss_le_grain : outputLoss ≤ grainLoss
  sourceLossCeiling : ℝ := ordinary.sourceLossCeiling
  sourceLossCeiling_eq :
    sourceLossCeiling = ordinary.sourceLossCeiling
  sourceLossCeiling_pos : 0 < sourceLossCeiling
  sourceLossCeiling_le_output : sourceLossCeiling ≤ outputLoss
  sourceLossCeiling_le_one : sourceLossCeiling ≤ 1
  sourceLossCeiling_le_firstKernel :
    sourceLossCeiling ≤
      (ordinary.calls.firstCallSchedule capability).kernel.sourceLoss
  sourceLossCeiling_le_scalar :
    sourceLossCeiling ≤ transition.scalarClosure.sourceLossCeiling
  sourceLossCeiling_le_finalTrace :
    sourceLossCeiling ≤ floorSchedule.traceSourceCeiling
  finalLoss_lt_one : outputLoss < 1
  finalLoss_half_lt_sigma : outputLoss / 2 < sigma
  projection : PureWZ2SourceHorizontalProjectionThreshold sigma
    (floorSchedule.densityLoss / 8)
  analytic : PureWZ2SourceHorizontalAnalyticThreshold projection.theoremEta
  normalEta : ℝ
  normalEta_pos : 0 < normalEta
  normalEta_sigma : 8 * normalEta < sigma
  neighborhoodLoss : ℝ := normalEta
  neighborhoodLoss_eq : neighborhoodLoss = normalEta
  geometric : PureWZ2SourceHorizontalGeometricThreshold
    sigma normalEta (floorSchedule.densityLoss / 8)
  graphThreshold : PureWZ2Node05V4RichSaturatedGraphThreshold
    sigma sourceLossCeiling ordinary.calls.firstOutputLoss ordinary.stickyLoss
      normalEta neighborhoodLoss analytic.budget.volumeLoss
      analytic.budget.constantLoss
      projection.sourceCostLossCeiling scaleLoss
  capacityThreshold : PureWZ2Node05V4RichSourcePopularCapacityThreshold
    sigma sourceLossCeiling ordinary.calls.firstOutputLoss normalEta
      analytic.budget.volumeLoss scaleLoss
  neighborhoodThreshold :
    PureWZ2Node05V4RichSecondCallData.PureWZ2Node05V4RichNeighborhoodBudgetThreshold
      sigma sourceLossCeiling ordinary.calls.firstOutputLoss ordinary.stickyLoss
        neighborhoodLoss scaleLoss
  outerDelta₀ : ℝ
  outerDelta₀_pos : 0 < outerDelta₀
  outerDelta₀_le_one : outerDelta₀ ≤ 1
  outerScale :
    ∀ {delta targetScale : ℝ},
      0 < delta → delta ≤ outerDelta₀ →
      Real.rpow delta (1 - outputLoss) ≤ targetScale →
      targetScale ≤ Real.rpow delta outputLoss →
      Nonempty (PureWZ2SourceHorizontalFlexibleOuterScaleData
        delta targetScale ordinary.calls.firstOutputLoss outputLoss)

/-- One backward-selected ordinary level.  Its output loss is automatically
small enough to be accepted by the already selected next level. -/
theorem PureWZ2CriticalPackage.c2OrdinaryLevelSchedule
    (capability : PureWZ2PropStickyCapability)
    {sigma nextSourceCeiling scaleLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (hnext : 0 < nextSourceCeiling)
    (hnextOne : nextSourceCeiling ≤ 1)
    (hnextSigma : nextSourceCeiling ≤ sigma / 16)
    (hnextGraph : nextSourceCeiling ≤ scaleLoss * sigma / 1024)
    (hscalePos : 0 < scaleLoss)
    (hscaleOne : scaleLoss ≤ 1) :
    Nonempty (PureWZ2C2OrdinaryLevelSchedule
      capability sigma nextSourceCeiling scaleLoss) := by
  rcases critical.c2OrdinaryTransitionLayer hnext hnextOne hnextGraph with
    ⟨transition⟩
  let grainLoss := transition.grainLoss
  let floorSchedule := transition.finalFloorSchedule
  have hgrainScalar :
      grainLoss = transition.scalarClosure.sourceLossCeiling := by
    calc
      grainLoss = transition.grainLoss := rfl
      _ = transition.scalarClosure.grainLoss := transition.grainLoss_eq
      _ = transition.scalarClosure.sourceLossCeiling :=
        transition.scalarClosure.sourceLossCeiling_eq.symm
  let finalLoss := floorSchedule.densityLoss / 8
  have hfinalPos : 0 < finalLoss := by
    dsimp only [finalLoss]
    exact div_pos floorSchedule.densityLoss_pos (by norm_num)
  have hfinalOne : finalLoss ≤ 1 := by
    dsimp only [finalLoss]
    exact (div_le_self floorSchedule.densityLoss_pos.le (by norm_num)).trans <|
      floorSchedule.densityLoss_le_floor.trans transition.grainLoss_le_one
  have houtputNext :
      finalLoss ≤ nextSourceCeiling := by
    exact (div_le_self floorSchedule.densityLoss_pos.le (by norm_num)).trans <|
      floorSchedule.densityLoss_le_floor.trans transition.grainLoss_le_next
  have houtputNextEighth :
      finalLoss ≤ nextSourceCeiling / 8 := by
    have hfinalTransition : finalLoss ≤ transition.transitionLoss :=
      (div_le_self floorSchedule.densityLoss_pos.le (by norm_num)).trans <|
        floorSchedule.densityLoss_le_floor.trans
          transition.grainLoss_le_transition
    exact hfinalTransition.trans transition.transitionLoss_le_next_eighth
  have houtputSigma :
      finalLoss ≤ sigma / 128 := by
    have hnextSigma' :
        nextSourceCeiling / 8 ≤ sigma / 128 := by
      nlinarith
    exact houtputNextEighth.trans hnextSigma'
  have houtputGraph :
      finalLoss ≤ scaleLoss * sigma / 8192 := by
    calc
      finalLoss ≤ nextSourceCeiling / 8 := houtputNextEighth
      _ ≤ (scaleLoss * sigma / 1024) / 8 := by gcongr
      _ = scaleLoss * sigma / 8192 := by ring
  have houtputOne : finalLoss < 1 := by
    linarith
  have houtputHalfSigma : finalLoss / 2 < sigma := by
    have hsigma := critical.sigma_pos
    linarith [houtputSigma]
  rcases pureWZ2_sourceHorizontal_projection_threshold
      critical.sigma_pos hfinalPos houtputOne houtputHalfSigma with
    ⟨projection⟩
  rcases pureWZ2_sourceHorizontal_analytic_threshold
      projection.theoremEta_pos with ⟨analytic⟩
  let normalEta :=
    min (sigma / 16)
      (min (analytic.budget.volumeLoss / 4)
        (projection.sourceCostLossCeiling / 8))
  have hnormalEta : 0 < normalEta := by
    dsimp only [normalEta]
    exact lt_min (div_pos critical.sigma_pos (by norm_num)) <|
      lt_min (div_pos analytic.budget.volumeLoss_pos (by norm_num))
        (div_pos projection.sourceCostLossCeiling_pos (by norm_num))
  have hnormalSigma : 8 * normalEta < sigma := by
    have hetaSigma : normalEta ≤ sigma / 16 := min_le_left _ _
    linarith [critical.sigma_pos]
  rcases pureWZ2_sourceHorizontal_geometric_threshold
      critical.sigma_pos hnormalEta hnormalSigma hfinalPos with
    ⟨geometric⟩
  let stickyLoss :=
    min finalLoss
      (min (scaleLoss * normalEta / 32)
        (scaleLoss * analytic.budget.constantLoss / 8))
  have hstickyPos : 0 < stickyLoss := by
    dsimp only [stickyLoss]
    exact lt_min hfinalPos <|
      lt_min
        (div_pos (mul_pos hscalePos hnormalEta) (by norm_num))
        (div_pos
          (mul_pos hscalePos analytic.budget.constantLoss_pos) (by norm_num))
  have hstickyFinal : stickyLoss ≤ floorSchedule.densityLoss / 8 := by
    dsimp only [stickyLoss, finalLoss]
    exact min_le_left _ _
  have hstickyEtaBudget :
      stickyLoss ≤ scaleLoss * normalEta / 32 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hstickyConstantBudget :
      stickyLoss ≤ scaleLoss * analytic.budget.constantLoss / 8 :=
    (min_le_right _ _).trans (min_le_right _ _)
  rcases floorSchedule.c2OrdinaryLossSchedule capability critical
      transition.grainLoss_le_one
      stickyLoss hstickyPos hstickyFinal hscalePos.le with
    ⟨⟨ordinary, hordinarySticky⟩⟩
  have hfirstSticky :
      ordinary.calls.firstOutputLoss < ordinary.stickyLoss := by
    exact ordinary.calls.calls.firstOutputLoss_lt_secondSource.trans <|
      ordinary.calls.secondKernel.sourceLoss_le_half.trans_lt <|
        (half_lt_self ordinary.calls.secondKernel.normalizationLoss_pos).trans <|
          ordinary.calls.secondKernel.normalizationLoss_lt_output
  have hsourceSticky :
      ordinary.sourceLossCeiling < ordinary.stickyLoss := by
    calc
      ordinary.sourceLossCeiling ≤
          (ordinary.calls.firstCallSchedule capability).kernel.sourceLoss :=
        ordinary.sourceLossCeiling_le_firstKernel
      _ ≤
          (ordinary.calls.firstCallSchedule capability).kernel.normalizationLoss /
            2 :=
        (ordinary.calls.firstCallSchedule capability).kernel.sourceLoss_le_half
      _ <
          (ordinary.calls.firstCallSchedule capability).kernel.normalizationLoss :=
        half_lt_self
          (ordinary.calls.firstCallSchedule capability).kernel.normalizationLoss_pos
      _ < ordinary.calls.firstOutputLoss :=
        (ordinary.calls.firstCallSchedule capability).kernel
          |>.normalizationLoss_lt_output
      _ < ordinary.stickyLoss := hfirstSticky
  have hstickyEta : ordinary.stickyLoss < normalEta := by
    have hbudget :
        ordinary.stickyLoss ≤ scaleLoss * normalEta / 32 := by
      rw [hordinarySticky]
      exact hstickyEtaBudget
    nlinarith
  have hsaturationGap :
      ordinary.sourceLossCeiling + 2 * ordinary.calls.firstOutputLoss <
        scaleLoss * (normalEta - ordinary.stickyLoss) := by
    have hleft :
        ordinary.sourceLossCeiling + 2 * ordinary.calls.firstOutputLoss <
          3 * ordinary.stickyLoss := by
      linarith
    have hbudget :
        ordinary.stickyLoss ≤ scaleLoss * normalEta / 32 := by
      rw [hordinarySticky]
      exact hstickyEtaBudget
    calc
      ordinary.sourceLossCeiling + 2 * ordinary.calls.firstOutputLoss <
          3 * ordinary.stickyLoss := hleft
      _ ≤ 3 * (scaleLoss * normalEta / 32) := by gcongr
      _ < scaleLoss * (normalEta - ordinary.stickyLoss) := by
        nlinarith
  have hconstantGap :
      ordinary.sourceLossCeiling <
        scaleLoss * analytic.budget.constantLoss := by
    have hbudget :
        ordinary.stickyLoss ≤
          scaleLoss * analytic.budget.constantLoss / 8 := by
      rw [hordinarySticky]
      exact hstickyConstantBudget
    calc
      ordinary.sourceLossCeiling < ordinary.stickyLoss := hsourceSticky
      _ ≤ scaleLoss * analytic.budget.constantLoss / 8 := hbudget
      _ < scaleLoss * analytic.budget.constantLoss := by
        have hproduct :=
          mul_pos hscalePos analytic.budget.constantLoss_pos
        linarith
  let neighborhoodLoss := normalEta
  have hvolumeGap :
      neighborhoodLoss + normalEta < analytic.budget.volumeLoss := by
    have hetaVolume :
        normalEta ≤ analytic.budget.volumeLoss / 4 :=
      (min_le_right _ _).trans (min_le_left _ _)
    dsimp only [neighborhoodLoss]
    linarith [analytic.budget.volumeLoss_pos]
  have hsourceCostGap :
      normalEta < (1 / 2 : ℝ) * projection.sourceCostLossCeiling := by
    have hetaSource :
        normalEta ≤ projection.sourceCostLossCeiling / 8 :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith [projection.sourceCostLossCeiling_pos]
  rcases pureWZ2Node05V4Rich_saturatedGraph_threshold
      (sigma := sigma)
      (sourceLossCeiling := ordinary.sourceLossCeiling)
      (firstLossCeiling := ordinary.calls.firstOutputLoss)
      (secondLossCeiling := ordinary.stickyLoss)
      (eta := normalEta) (neighborhoodLoss := neighborhoodLoss)
      (volumeLoss := analytic.budget.volumeLoss)
      (constantLoss := analytic.budget.constantLoss)
      (sourceCostLoss := projection.sourceCostLossCeiling)
      (scaleLoss := scaleLoss)
      critical.sigma_pos ordinary.sourceLossCeiling_pos.le
      ordinary.calls.calls.firstOutputLoss_pos.le
      ordinary.stickyLoss_pos.le hnormalEta hnormalEta.le hscalePos
      analytic.budget.constantLoss_pos hconstantGap hstickyEta hsaturationGap
      hvolumeGap projection.sourceCostLossCeiling_pos hsourceCostGap with
    ⟨graphThreshold⟩
  have hcapacityGap :
      2 * ordinary.sourceLossCeiling +
          2 * ordinary.calls.firstOutputLoss <
        scaleLoss *
          ((normalEta - 2 * ordinary.calls.firstOutputLoss) / 2) := by
    have hleft :
        2 * ordinary.sourceLossCeiling +
            2 * ordinary.calls.firstOutputLoss <
          4 * ordinary.stickyLoss := by
      nlinarith
    have hbudget :
        ordinary.stickyLoss ≤ scaleLoss * normalEta / 32 := by
      rw [hordinarySticky]
      exact hstickyEtaBudget
    have hscaleFirst :
        scaleLoss * ordinary.calls.firstOutputLoss ≤ ordinary.stickyLoss := by
      calc
        scaleLoss * ordinary.calls.firstOutputLoss ≤
            scaleLoss * ordinary.stickyLoss := by gcongr
        _ ≤ ordinary.stickyLoss := by
          nlinarith [ordinary.stickyLoss_pos, hscaleOne]
    nlinarith
  rcases pureWZ2Node05V4Rich_sourcePopularCapacity_threshold
      (sigma := sigma)
      (sourceLossCeiling := ordinary.sourceLossCeiling)
      (firstLossCeiling := ordinary.calls.firstOutputLoss)
      (eta := normalEta) (volumeLoss := analytic.budget.volumeLoss)
      (scaleLoss := scaleLoss)
      critical.sigma_pos ordinary.sourceLossCeiling_pos.le
      ordinary.calls.calls.firstOutputLoss_pos.le hnormalEta hscalePos hcapacityGap
      (by
        have hetaVolume : normalEta ≤ analytic.budget.volumeLoss / 4 :=
          (min_le_right _ _).trans (min_le_left _ _)
        linarith [analytic.budget.volumeLoss_pos]) with
    ⟨capacityThreshold⟩
  have hneighborhoodScaleGap :
      PureWZ2Node05V4RichSecondCallData.pureWZ2Node05V4RichNeighborhoodPointDensityLoss
            ordinary.sourceLossCeiling ordinary.calls.firstOutputLoss +
            2 * ordinary.calls.firstOutputLoss ≤
        scaleLoss * (sigma - ordinary.stickyLoss) := by
    have hetaSigma : normalEta ≤ sigma / 16 := min_le_left _ _
    have hleft :
        PureWZ2Node05V4RichSecondCallData.pureWZ2Node05V4RichNeighborhoodPointDensityLoss
              ordinary.sourceLossCeiling ordinary.calls.firstOutputLoss +
              2 * ordinary.calls.firstOutputLoss <
          7 * ordinary.stickyLoss := by
      unfold PureWZ2Node05V4RichSecondCallData.pureWZ2Node05V4RichNeighborhoodPointDensityLoss
      linarith
    have hbudget :
        ordinary.stickyLoss ≤ scaleLoss * normalEta / 32 := by
      rw [hordinarySticky]
      exact hstickyEtaBudget
    have hscaleOneNonneg : 0 ≤ scaleLoss := hscalePos.le
    have hscaleUpper : scaleLoss ≤ 1 := hscaleOne
    calc
      _ ≤ 7 * ordinary.stickyLoss := hleft.le
      _ ≤ 7 * (scaleLoss * normalEta / 32) := by gcongr
      _ ≤ scaleLoss * (sigma - ordinary.stickyLoss) := by
        nlinarith [mul_nonneg hscaleOneNonneg ordinary.stickyLoss_pos.le,
          mul_le_mul_of_nonneg_left hetaSigma hscaleOneNonneg]
  have hneighborhoodBudgetGap :
      ordinary.sourceLossCeiling + 2 * ordinary.calls.firstOutputLoss <
        scaleLoss * (neighborhoodLoss -
          3 * ordinary.calls.firstOutputLoss) := by
    have hleft :
        ordinary.sourceLossCeiling + 2 * ordinary.calls.firstOutputLoss <
          3 * ordinary.stickyLoss := by linarith
    have hbudget :
        ordinary.stickyLoss ≤ scaleLoss * normalEta / 32 := by
      rw [hordinarySticky]
      exact hstickyEtaBudget
    have hscaleNonneg : 0 ≤ scaleLoss := hscalePos.le
    have hscaleUpper : scaleLoss ≤ 1 := hscaleOne
    dsimp only [neighborhoodLoss]
    nlinarith [mul_nonneg hscaleNonneg ordinary.calls.calls.firstOutputLoss_pos.le]
  rcases
      PureWZ2Node05V4RichSecondCallData.pureWZ2Node05V4Rich_neighborhoodBudget_threshold
        (sigma := sigma) (sourceLossCeiling := ordinary.sourceLossCeiling)
        (firstOutputLoss := ordinary.calls.firstOutputLoss)
        (secondLossCeiling := ordinary.stickyLoss)
        (neighborhoodLoss := neighborhoodLoss) (scaleLoss := scaleLoss)
        ordinary.sourceLossCeiling_pos.le
        ordinary.calls.calls.firstOutputLoss_pos ordinary.stickyLoss_pos.le
        hscalePos hneighborhoodScaleGap hneighborhoodBudgetGap with
    ⟨neighborhoodThreshold⟩
  have hfirstFinal :
      ordinary.calls.firstOutputLoss < ordinary.finalLoss :=
    hfirstSticky.trans_le ordinary.stickyLoss_le_final
  rcases pureWZ2_sourceHorizontal_outerScale_flexible_schedule
      ordinary.calls.calls.firstOutputLoss_pos hfirstFinal with
    ⟨outerDelta₀, houterDelta₀, houterDelta₀One, outerScale⟩
  exact ⟨{
    transition := transition
    grainLoss := grainLoss
    grainLoss_eq := rfl
    floorSchedule := floorSchedule
    ordinary := ordinary
    outputLoss := ordinary.finalLoss
    outputLoss_eq := rfl
    outputLoss_pos := ordinary.finalLoss_pos
    outputLoss_le_next := by
      simpa only [ordinary.finalLoss_eq] using houtputNext
    outputLoss_le_next_eighth := by
      simpa only [ordinary.finalLoss_eq] using houtputNextEighth
    outputLoss_le_graphBudget := by
      simpa only [ordinary.finalLoss_eq] using houtputGraph
    outputLoss_le_grain := by
      rw [ordinary.finalLoss_eq]
      exact (div_le_self floorSchedule.densityLoss_pos.le
        (by norm_num)).trans floorSchedule.densityLoss_le_floor
    sourceLossCeiling := ordinary.sourceLossCeiling
    sourceLossCeiling_eq := rfl
    sourceLossCeiling_pos := ordinary.sourceLossCeiling_pos
    sourceLossCeiling_le_output :=
      ordinary.sourceLossCeiling_le_density_eighth.trans_eq
        ordinary.finalLoss_eq.symm
    sourceLossCeiling_le_one :=
      ordinary.sourceLossCeiling_le_density_eighth.trans <| by
        rw [← ordinary.finalLoss_eq]
        exact ordinary.finalLoss_le_one
    sourceLossCeiling_le_firstKernel :=
      ordinary.sourceLossCeiling_le_firstKernel
    sourceLossCeiling_le_scalar :=
      ordinary.sourceLossCeiling_le_density_eighth.trans <|
        (div_le_self floorSchedule.densityLoss_pos.le (by norm_num)).trans <|
          floorSchedule.densityLoss_le_floor.trans_eq hgrainScalar
    sourceLossCeiling_le_finalTrace :=
      ordinary.sourceLossCeiling_le_density_eighth.trans <| by
        rw [floorSchedule.densityLoss_eq,
          floorSchedule.traceSourceCeiling_eq]
        linarith [floorSchedule.criticalFloor.structuralLoss_pos]
    finalLoss_lt_one := by
      simpa only [ordinary.finalLoss_eq] using houtputOne
    finalLoss_half_lt_sigma := by
      simpa only [ordinary.finalLoss_eq] using houtputHalfSigma
    projection := projection
    analytic := analytic
    normalEta := normalEta
    normalEta_pos := hnormalEta
    normalEta_sigma := hnormalSigma
    neighborhoodLoss := neighborhoodLoss
    neighborhoodLoss_eq := rfl
    geometric := geometric
    graphThreshold := graphThreshold
    capacityThreshold := capacityThreshold
    neighborhoodThreshold := neighborhoodThreshold
    outerDelta₀ := outerDelta₀
    outerDelta₀_pos := houterDelta₀
    outerDelta₀_le_one := houterDelta₀One
    outerScale := by
      intro delta targetScale hdelta hdeltaSmall htargetLower htargetUpper
      simpa only [ordinary.finalLoss_eq] using
        outerScale delta hdelta hdeltaSmall targetScale htargetLower htargetUpper
  }⟩

structure PureWZ2C2PackedOrdinaryLevel
    (capability : PureWZ2PropStickyCapability)
    (sigma scaleLoss : ℝ) where
  nextSourceCeiling : ℝ
  nextSourceCeiling_pos : 0 < nextSourceCeiling
  nextSourceCeiling_le_one : nextSourceCeiling ≤ 1
  nextSourceCeiling_le_sigma : nextSourceCeiling ≤ sigma / 16
  nextSourceCeiling_le_graph :
    nextSourceCeiling ≤ scaleLoss * sigma / 1024
  level : PureWZ2C2OrdinaryLevelSchedule
    capability sigma nextSourceCeiling scaleLoss

private noncomputable def pureWZ2C2BuildReversedLevels
    (capability : PureWZ2PropStickyCapability)
    {sigma terminalSourceCeiling scaleLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (hterminal : 0 < terminalSourceCeiling)
    (hterminalOne : terminalSourceCeiling ≤ 1)
    (hterminalSigma : terminalSourceCeiling ≤ sigma / 16)
    (hterminalGraph :
      terminalSourceCeiling ≤ scaleLoss * sigma / 1024)
    (hscalePos : 0 < scaleLoss)
    (hscaleOne : scaleLoss ≤ 1) :
    ℕ → PureWZ2C2PackedOrdinaryLevel capability sigma scaleLoss
  | 0 => by
      let level := Classical.choice
        (critical.c2OrdinaryLevelSchedule capability
          hterminal hterminalOne hterminalSigma hterminalGraph
            hscalePos hscaleOne)
      exact {
        nextSourceCeiling := terminalSourceCeiling
        nextSourceCeiling_pos := hterminal
        nextSourceCeiling_le_one := hterminalOne
        nextSourceCeiling_le_sigma := hterminalSigma
        nextSourceCeiling_le_graph := hterminalGraph
        level := level }
  | index + 1 => by
      let next := pureWZ2C2BuildReversedLevels capability critical
        hterminal hterminalOne hterminalSigma hterminalGraph
          hscalePos hscaleOne index
      have hnextSourceSigma :
          next.level.sourceLossCeiling ≤ sigma / 16 :=
        next.level.sourceLossCeiling_le_output.trans <|
          next.level.outputLoss_le_next.trans next.nextSourceCeiling_le_sigma
      have hnextSourceGraph :
          next.level.sourceLossCeiling ≤ scaleLoss * sigma / 1024 :=
        next.level.sourceLossCeiling_le_output.trans <|
          next.level.outputLoss_le_next.trans next.nextSourceCeiling_le_graph
      let level := Classical.choice
        (critical.c2OrdinaryLevelSchedule capability
          next.level.sourceLossCeiling_pos
          next.level.sourceLossCeiling_le_one hnextSourceSigma
            hnextSourceGraph hscalePos hscaleOne)
      exact {
        nextSourceCeiling := next.level.sourceLossCeiling
        nextSourceCeiling_pos := next.level.sourceLossCeiling_pos
        nextSourceCeiling_le_one := next.level.sourceLossCeiling_le_one
        nextSourceCeiling_le_sigma := hnextSourceSigma
        nextSourceCeiling_le_graph := hnextSourceGraph
        level := level }

private theorem pureWZ2C2BuildReversedLevels_succ_output_le_previous_ceiling
    (capability : PureWZ2PropStickyCapability)
    {sigma terminalSourceCeiling scaleLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (hterminal : 0 < terminalSourceCeiling)
    (hterminalOne : terminalSourceCeiling ≤ 1)
    (hterminalSigma : terminalSourceCeiling ≤ sigma / 16)
    (hterminalGraph :
      terminalSourceCeiling ≤ scaleLoss * sigma / 1024)
    (hscalePos : 0 < scaleLoss)
    (hscaleOne : scaleLoss ≤ 1)
    (index : ℕ) :
    (pureWZ2C2BuildReversedLevels capability critical hterminal
      hterminalOne hterminalSigma hterminalGraph hscalePos hscaleOne
        (index + 1)).level.transition.transitionLoss ≤
    (pureWZ2C2BuildReversedLevels capability critical hterminal
      hterminalOne hterminalSigma hterminalGraph hscalePos hscaleOne
        index).level.sourceLossCeiling := by
  simp [pureWZ2C2BuildReversedLevels]
  exact
    (Classical.choice
      (critical.c2OrdinaryLevelSchedule capability
        (pureWZ2C2BuildReversedLevels capability critical hterminal
          hterminalOne hterminalSigma hterminalGraph hscalePos hscaleOne
            index).level.sourceLossCeiling_pos
        (pureWZ2C2BuildReversedLevels capability critical hterminal
          hterminalOne hterminalSigma hterminalGraph hscalePos hscaleOne
            index).level.sourceLossCeiling_le_one
        (by
          exact
            (pureWZ2C2BuildReversedLevels capability critical hterminal
              hterminalOne hterminalSigma hterminalGraph hscalePos hscaleOne
                index).level
                |>.sourceLossCeiling_le_output.trans <|
              (pureWZ2C2BuildReversedLevels capability critical hterminal
                hterminalOne hterminalSigma hterminalGraph hscalePos hscaleOne
                  index).level
                  |>.outputLoss_le_next.trans <|
                (pureWZ2C2BuildReversedLevels capability critical hterminal
                  hterminalOne hterminalSigma hterminalGraph hscalePos hscaleOne
                    index)
                    |>.nextSourceCeiling_le_sigma)
        (by
          exact
            (pureWZ2C2BuildReversedLevels capability critical hterminal
              hterminalOne hterminalSigma hterminalGraph hscalePos hscaleOne
                index).level
                |>.sourceLossCeiling_le_output.trans <|
              (pureWZ2C2BuildReversedLevels capability critical hterminal
                hterminalOne hterminalSigma hterminalGraph hscalePos hscaleOne
                  index).level
                  |>.outputLoss_le_next.trans <|
                (pureWZ2C2BuildReversedLevels capability critical hterminal
                  hterminalOne hterminalSigma hterminalGraph hscalePos hscaleOne
                    index)
                    |>.nextSourceCeiling_le_graph)
        hscalePos hscaleOne)).transition.transitionLoss_le_next

private theorem pureWZ2C2BuildReversedLevels_sum_with_last_le
    (capability : PureWZ2PropStickyCapability)
    {sigma terminalSourceCeiling scaleLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (hterminal : 0 < terminalSourceCeiling)
    (hterminalOne : terminalSourceCeiling ≤ 1)
    (hterminalSigma : terminalSourceCeiling ≤ sigma / 16)
    (hterminalGraph :
      terminalSourceCeiling ≤ scaleLoss * sigma / 1024)
    (hscalePos : 0 < scaleLoss)
    (hscaleOne : scaleLoss ≤ 1) :
    ∀ index : ℕ,
      (∑ reverseIndex ∈ Finset.range (index + 1),
          (pureWZ2C2BuildReversedLevels capability critical hterminal
            hterminalOne hterminalSigma hterminalGraph hscalePos hscaleOne
              reverseIndex).level.transition.transitionLoss) +
        (pureWZ2C2BuildReversedLevels capability critical hterminal
          hterminalOne hterminalSigma hterminalGraph hscalePos hscaleOne
            index).level.transition.transitionLoss / 7 ≤
      terminalSourceCeiling / 7
  | 0 => by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add]
      have hbase :=
        (pureWZ2C2BuildReversedLevels capability critical hterminal
          hterminalOne hterminalSigma hterminalGraph hscalePos hscaleOne
            0).level.transition.transitionLoss_le_next_eighth
      simp only [pureWZ2C2BuildReversedLevels] at hbase
      simp only [pureWZ2C2BuildReversedLevels]
      nlinarith
  | index + 1 => by
      have ih := pureWZ2C2BuildReversedLevels_sum_with_last_le
        capability critical hterminal hterminalOne hterminalSigma
          hterminalGraph hscalePos hscaleOne index
      have hstep :=
        pureWZ2C2BuildReversedLevels_succ_output_le_previous_ceiling
          capability critical hterminal hterminalOne hterminalSigma
            hterminalGraph hscalePos hscaleOne index
      let currentLevel :=
        (pureWZ2C2BuildReversedLevels capability critical hterminal
          hterminalOne hterminalSigma hterminalGraph hscalePos hscaleOne
            index).level
      have hceiling : currentLevel.sourceLossCeiling ≤
          currentLevel.transition.transitionLoss := by
        calc
          currentLevel.sourceLossCeiling ≤ currentLevel.outputLoss :=
            currentLevel.sourceLossCeiling_le_output
          _ ≤ currentLevel.grainLoss := currentLevel.outputLoss_le_grain
          _ = currentLevel.transition.grainLoss := currentLevel.grainLoss_eq
          _ ≤ currentLevel.transition.transitionLoss :=
            currentLevel.transition.grainLoss_le_transition
      have hdecay :
          (pureWZ2C2BuildReversedLevels capability critical hterminal
              hterminalOne hterminalSigma hterminalGraph hscalePos hscaleOne
                (index + 1)).level.transition.transitionLoss ≤
            (pureWZ2C2BuildReversedLevels capability critical hterminal
              hterminalOne hterminalSigma hterminalGraph hscalePos hscaleOne
                index).level.transition.transitionLoss / 8 := by
        have heighth :=
          (pureWZ2C2BuildReversedLevels capability critical hterminal
            hterminalOne hterminalSigma hterminalGraph hscalePos hscaleOne
              (index + 1)).level
              |>.transition.transitionLoss_le_next_eighth
        simp only [pureWZ2C2BuildReversedLevels] at heighth
        exact heighth.trans (div_le_div_of_nonneg_right hceiling (by norm_num))
      rw [show index + 1 + 1 = (index + 1) + 1 by rfl,
        Finset.sum_range_succ]
      nlinarith

structure PureWZ2C2OrdinaryPrefixLossSchedule
    (capability : PureWZ2PropStickyCapability)
    (sigma : ℝ) (N : ℕ)
    (terminalSourceCeiling scaleLoss : ℝ) where
  levelCount_two : 2 ≤ N
  level : Fin (N - 1) →
    PureWZ2C2PackedOrdinaryLevel capability sigma scaleLoss
  outputLoss : Fin (N - 1) → ℝ :=
    fun index => (level index).level.transition.transitionLoss
  outputLoss_eq_level : ∀ index,
    outputLoss index = (level index).level.transition.transitionLoss
  sourceLossCeiling : Fin (N - 1) → ℝ :=
    fun index => (level index).level.sourceLossCeiling
  sourceLossCeiling_eq_level : ∀ index,
    sourceLossCeiling index = (level index).level.sourceLossCeiling
  outputLoss_pos : ∀ index, 0 < outputLoss index
  sourceLossCeiling_pos : ∀ index, 0 < sourceLossCeiling index
  sourceLossCeiling_le_firstKernel :
    ∀ index, sourceLossCeiling index ≤
      (((level index).level.ordinary.calls.firstCallSchedule
        capability).kernel.sourceLoss)
  outputLoss_le_next_ceiling :
    ∀ index : Fin (N - 1), ∀ hnext : (index : ℕ) + 1 < N - 1,
      outputLoss index ≤
        sourceLossCeiling ⟨(index : ℕ) + 1, hnext⟩
  outputLoss_last_le_terminal :
    outputLoss ⟨N - 2, by omega⟩ ≤ terminalSourceCeiling
  totalOutputLoss : ℝ := ∑ index, outputLoss index
  totalOutputLoss_eq : totalOutputLoss = ∑ index, outputLoss index
  totalOutputLoss_le_terminal_seventh :
    totalOutputLoss ≤ terminalSourceCeiling / 7

/-- Select all `N-1` ordinary loss schedules backwards before runtime. -/
noncomputable def PureWZ2CriticalPackage.c2OrdinaryPrefixLossSchedule
    (capability : PureWZ2PropStickyCapability)
    {sigma terminalSourceCeiling scaleLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    {N : ℕ} (hN : 2 ≤ N)
    (hterminal : 0 < terminalSourceCeiling)
    (hterminalOne : terminalSourceCeiling ≤ 1)
    (hterminalSigma : terminalSourceCeiling ≤ sigma / 16)
    (hterminalGraph :
      terminalSourceCeiling ≤ scaleLoss * sigma / 1024)
    (hscalePos : 0 < scaleLoss)
    (hscaleOne : scaleLoss ≤ 1) :
    PureWZ2C2OrdinaryPrefixLossSchedule
      capability sigma N terminalSourceCeiling scaleLoss := by
  let reversed := pureWZ2C2BuildReversedLevels capability critical
    hterminal hterminalOne hterminalSigma hterminalGraph hscalePos hscaleOne
  let level : Fin (N - 1) →
      PureWZ2C2PackedOrdinaryLevel capability sigma scaleLoss :=
    fun index => reversed (N - 2 - (index : ℕ))
  let outputLoss : Fin (N - 1) → ℝ :=
    fun index => (level index).level.transition.transitionLoss
  let sourceLossCeiling : Fin (N - 1) → ℝ :=
    fun index => (level index).level.sourceLossCeiling
  have hlastIndex : N - 2 - (N - 2) = 0 := by omega
  have hreversedTotal :
      (∑ reverseIndex ∈ Finset.range (N - 1),
          (reversed reverseIndex).level.transition.transitionLoss) ≤
        terminalSourceCeiling / 7 := by
    have hinvariant := pureWZ2C2BuildReversedLevels_sum_with_last_le
      capability critical hterminal hterminalOne hterminalSigma
        hterminalGraph hscalePos hscaleOne (N - 2)
    have hlength : N - 2 + 1 = N - 1 := by omega
    rw [hlength] at hinvariant
    have hlastNonneg :
        0 ≤ (reversed (N - 2)).level.transition.transitionLoss / 7 := by
      exact div_nonneg
        (reversed (N - 2)).level.transition.transitionLoss_pos.le
        (by norm_num)
    linarith
  have htotal :
      (∑ index : Fin (N - 1), outputLoss index) =
        ∑ reverseIndex ∈ Finset.range (N - 1),
          (reversed reverseIndex).level.transition.transitionLoss := by
    let reverseEquiv : Fin (N - 1) ≃ Fin (N - 1) :=
      { toFun := Fin.rev
        invFun := Fin.rev
        left_inv := Fin.rev_involutive
        right_inv := Fin.rev_involutive }
    calc
      (∑ index : Fin (N - 1), outputLoss index) =
          ∑ index : Fin (N - 1),
            (reversed ((reverseEquiv index : Fin (N - 1)) : ℕ)).level.transition.transitionLoss := by
        apply Finset.sum_congr rfl
        intro index _
        simp [outputLoss, level, reverseEquiv, Fin.rev]
        rw [Nat.sub_sub, Nat.sub_sub]
        rw [show 2 + (index : ℕ) = 1 + ((index : ℕ) + 1) by omega]
      _ = ∑ index : Fin (N - 1),
          (reversed (index : ℕ)).level.transition.transitionLoss :=
        Equiv.sum_comp reverseEquiv
          (fun index : Fin (N - 1) =>
            (reversed (index : ℕ)).level.transition.transitionLoss)
      _ = ∑ reverseIndex ∈ Finset.range (N - 1),
          (reversed reverseIndex).level.transition.transitionLoss :=
        Fin.sum_univ_eq_sum_range
          (fun reverseIndex =>
            (reversed reverseIndex).level.transition.transitionLoss) (N - 1)
  exact {
    levelCount_two := hN
    level := level
    outputLoss := outputLoss
    outputLoss_eq_level := fun _ => rfl
    sourceLossCeiling := sourceLossCeiling
    sourceLossCeiling_eq_level := fun _ => rfl
    outputLoss_pos := fun index =>
      (level index).level.transition.transitionLoss_pos
    sourceLossCeiling_pos :=
      fun index => (level index).level.sourceLossCeiling_pos
    sourceLossCeiling_le_firstKernel :=
      fun index => (level index).level.sourceLossCeiling_le_firstKernel
    outputLoss_le_next_ceiling := by
      intro index hnext
      have hindex : ∃ reverseIndex,
          N - 2 - (index : ℕ) = reverseIndex + 1 := by
        exact ⟨N - 3 - (index : ℕ), by omega⟩
      rcases hindex with ⟨reverseIndex, hindex⟩
      have hnextIndex :
          N - 2 - ((index : ℕ) + 1) = reverseIndex := by omega
      dsimp only [outputLoss, sourceLossCeiling, level]
      rw [hindex, hnextIndex]
      exact pureWZ2C2BuildReversedLevels_succ_output_le_previous_ceiling
        capability critical hterminal hterminalOne hterminalSigma
          hterminalGraph hscalePos hscaleOne reverseIndex
    outputLoss_last_le_terminal := by
      dsimp only [outputLoss, level]
      rw [hlastIndex]
      exact (reversed 0).level.transition.transitionLoss_le_next
    totalOutputLoss := ∑ index, outputLoss index
    totalOutputLoss_eq := rfl
    totalOutputLoss_le_terminal_seventh := by
      rw [htotal]
      exact hreversedTotal
  }

namespace PureWZ2C2OrdinaryPrefixLossSchedule

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma terminalSourceCeiling scaleLoss : ℝ}
    {N : ℕ}
    (schedule : PureWZ2C2OrdinaryPrefixLossSchedule
      capability sigma N terminalSourceCeiling scaleLoss)

def levelDeltaThreshold (index : Fin (N - 1)) : ℝ :=
  min
    (min
      (min
        (min (schedule.level index).level.floorSchedule.delta₀
          (schedule.level index).level.transition.scalarClosure.delta₀)
        (min (schedule.level index).level.ordinary.densityThreshold.delta₀
          (min
            (((schedule.level index).level.ordinary.calls.firstCallSchedule
              capability).kernel.delta₀)
            (min ((schedule.level index).level.ordinary.calls.secondKernel.delta₀)
              (schedule.level index).level.graphThreshold.delta₀))))
      (schedule.level index).level.outerDelta₀)
    (min (schedule.level index).level.neighborhoodThreshold.delta₀
      (schedule.level index).level.capacityThreshold.delta₀)

theorem levelDeltaThreshold_pos (index : Fin (N - 1)) :
    0 < schedule.levelDeltaThreshold index := by
  unfold levelDeltaThreshold
  exact lt_min
    (lt_min
      (lt_min
        (lt_min (schedule.level index).level.floorSchedule.delta₀_pos
          (schedule.level index).level.transition.scalarClosure.delta₀_pos) <|
        lt_min
          (schedule.level index).level.ordinary.densityThreshold.delta₀_pos <|
          lt_min
            (((schedule.level index).level.ordinary.calls.firstCallSchedule
              capability).kernel.delta₀_pos)
            <| lt_min
              ((schedule.level index).level.ordinary.calls.secondKernel.delta₀_pos)
              (schedule.level index).level.graphThreshold.delta₀_pos)
      (schedule.level index).level.outerDelta₀_pos)
    (lt_min (schedule.level index).level.neighborhoodThreshold.delta₀_pos
      (schedule.level index).level.capacityThreshold.delta₀_pos)

noncomputable def commonDeltaThreshold : ℝ :=
  let image := Finset.image schedule.levelDeltaThreshold Finset.univ
  have hnonempty : image.Nonempty := by
    let zero : Fin (N - 1) := ⟨0, by
      have hN := schedule.levelCount_two
      omega⟩
    exact ⟨schedule.levelDeltaThreshold zero,
      Finset.mem_image.mpr ⟨zero, Finset.mem_univ _, rfl⟩⟩
  Finset.min' image hnonempty

theorem commonDeltaThreshold_pos :
    0 < schedule.commonDeltaThreshold := by
  let image := Finset.image schedule.levelDeltaThreshold Finset.univ
  let zero : Fin (N - 1) := ⟨0, by
    have hN := schedule.levelCount_two
    omega⟩
  have hnonempty : image.Nonempty :=
    ⟨schedule.levelDeltaThreshold zero,
      Finset.mem_image.mpr ⟨zero, Finset.mem_univ _, rfl⟩⟩
  have hmem := Finset.min'_mem image hnonempty
  rcases Finset.mem_image.mp hmem with ⟨index, _hindex, heq⟩
  change 0 < Finset.min' image hnonempty
  rw [← heq]
  exact schedule.levelDeltaThreshold_pos index

theorem commonDeltaThreshold_le (index : Fin (N - 1)) :
    schedule.commonDeltaThreshold ≤ schedule.levelDeltaThreshold index := by
  let image := Finset.image schedule.levelDeltaThreshold Finset.univ
  let zero : Fin (N - 1) := ⟨0, by
    have hN := schedule.levelCount_two
    omega⟩
  have hnonempty : image.Nonempty :=
    ⟨schedule.levelDeltaThreshold zero,
      Finset.mem_image.mpr ⟨zero, Finset.mem_univ _, rfl⟩⟩
  exact Finset.min'_le image _
    (Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩)

def levelRhoThreshold (index : Fin (N - 1)) : ℝ :=
  min
    (min (schedule.level index).level.ordinary.calls.secondKernel.delta₀
      (min (schedule.level index).level.ordinary.densityThreshold.rho₀
        (min (schedule.level index).level.projection.rho₀
          (min (schedule.level index).level.analytic.rho0
            (min (schedule.level index).level.geometric.rho0
              (schedule.level index).level.graphThreshold.rho₀)))))
    (min (schedule.level index).level.neighborhoodThreshold.rho₀
      (schedule.level index).level.capacityThreshold.rho₀)

theorem levelRhoThreshold_pos (index : Fin (N - 1)) :
    0 < schedule.levelRhoThreshold index := by
  unfold levelRhoThreshold
  exact lt_min
    (lt_min
      (schedule.level index).level.ordinary.calls.secondKernel.delta₀_pos <|
        lt_min
          (schedule.level index).level.ordinary.densityThreshold.rho₀_pos <|
          lt_min (schedule.level index).level.projection.rho₀_pos <|
            lt_min (schedule.level index).level.analytic.rho0_pos
              <| lt_min (schedule.level index).level.geometric.rho0_pos
                (schedule.level index).level.graphThreshold.rho₀_pos)
    (lt_min (schedule.level index).level.neighborhoodThreshold.rho₀_pos
      (schedule.level index).level.capacityThreshold.rho₀_pos)

noncomputable def commonRhoThreshold : ℝ :=
  let image := Finset.image schedule.levelRhoThreshold Finset.univ
  have hnonempty : image.Nonempty := by
    let zero : Fin (N - 1) := ⟨0, by
      have hN := schedule.levelCount_two
      omega⟩
    exact ⟨schedule.levelRhoThreshold zero,
      Finset.mem_image.mpr ⟨zero, Finset.mem_univ _, rfl⟩⟩
  Finset.min' image hnonempty

theorem commonRhoThreshold_pos :
    0 < schedule.commonRhoThreshold := by
  let image := Finset.image schedule.levelRhoThreshold Finset.univ
  let zero : Fin (N - 1) := ⟨0, by
    have hN := schedule.levelCount_two
    omega⟩
  have hnonempty : image.Nonempty :=
    ⟨schedule.levelRhoThreshold zero,
      Finset.mem_image.mpr ⟨zero, Finset.mem_univ _, rfl⟩⟩
  have hmem := Finset.min'_mem image hnonempty
  rcases Finset.mem_image.mp hmem with ⟨index, _hindex, heq⟩
  change 0 < Finset.min' image hnonempty
  rw [← heq]
  exact schedule.levelRhoThreshold_pos index

theorem commonRhoThreshold_le (index : Fin (N - 1)) :
    schedule.commonRhoThreshold ≤ schedule.levelRhoThreshold index := by
  let image := Finset.image schedule.levelRhoThreshold Finset.univ
  let zero : Fin (N - 1) := ⟨0, by
    have hN := schedule.levelCount_two
    omega⟩
  have hnonempty : image.Nonempty :=
    ⟨schedule.levelRhoThreshold zero,
      Finset.mem_image.mpr ⟨zero, Finset.mem_univ _, rfl⟩⟩
  exact Finset.min'_le image _
    (Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩)

theorem commonRhoThreshold_le_one :
    schedule.commonRhoThreshold ≤ 1 := by
  let zero : Fin (N - 1) := ⟨0, by
    have hN := schedule.levelCount_two
    omega⟩
  exact (schedule.commonRhoThreshold_le zero).trans
    ((min_le_left _ _).trans <| (min_le_left _ _).trans
      (schedule.level zero).level.ordinary.calls.secondKernel.delta₀_le_one)

end PureWZ2C2OrdinaryPrefixLossSchedule

structure PureWZ2C2OrdinaryGlobalSchedule
    (capability : PureWZ2PropStickyCapability)
    (sigma outputLoss targetDelta₀ C Ctotal : ℝ) where
  sigma_pos : 0 < sigma
  sigma_lt_one : sigma < 1
  mild : PureWZ2Proposition64MildRescalingScalarSchedule
    outputLoss targetDelta₀ C Ctotal
  endpointBound : ℝ
  endpointBound_pos : 0 < endpointBound
  endpointOutputLoss : ℝ :=
    min endpointBound <|
      min mild.workLoss (min (sigma / 16) (mild.epsilon₂ * sigma / 512))
  endpointOutputLoss_eq :
    endpointOutputLoss =
      min endpointBound
        (min mild.workLoss (min (sigma / 16) (mild.epsilon₂ * sigma / 512)))
  endpointOutputLoss_pos : 0 < endpointOutputLoss
  endpointOutputLoss_le_bound : endpointOutputLoss ≤ endpointBound
  endpointOutputLoss_le_work : endpointOutputLoss ≤ mild.workLoss
  endpointOutputLoss_le_sigma_sixteenth :
    endpointOutputLoss ≤ sigma / 16
  endpointKernel : PureWZ2.Proposition63RichStickyKernelScheduleData
    sigma endpointOutputLoss
  ordinaryPrefix : PureWZ2C2OrdinaryPrefixLossSchedule
    (capability := capability) (sigma := sigma) (N := mild.levelCount)
    (terminalSourceCeiling := endpointKernel.sourceLoss)
    (scaleLoss := mild.epsilon₂)
  ordinaryEndpointLoss : ℝ :=
    ordinaryPrefix.totalOutputLoss + endpointOutputLoss
  ordinaryEndpointLoss_eq :
    ordinaryEndpointLoss = ordinaryPrefix.totalOutputLoss + endpointOutputLoss
  ordinaryEndpointLoss_le_two_epsilon₂ :
    ordinaryEndpointLoss ≤ 2 * mild.epsilon₂
  ordinaryEndpointLoss_le_totalMargin :
    ordinaryEndpointLoss ≤ Ctotal * mild.epsilon₂
  ordinaryEndpointLoss_le_outputMargin :
    ordinaryEndpointLoss ≤ (1 - C * mild.epsilon₂) * outputLoss
  commonDelta₀ : ℝ :=
    min mild.sourceDelta₀
      (min endpointKernel.delta₀
        (min
          (PureWZ2C2OrdinaryPrefixLossSchedule.commonDeltaThreshold
            ordinaryPrefix)
          ((PureWZ2C2OrdinaryPrefixLossSchedule.commonRhoThreshold
            ordinaryPrefix) ^ mild.levelCount)))
  commonDelta₀_eq :
    commonDelta₀ =
      min mild.sourceDelta₀
        (min endpointKernel.delta₀
          (min
            (PureWZ2C2OrdinaryPrefixLossSchedule.commonDeltaThreshold
              ordinaryPrefix)
            ((PureWZ2C2OrdinaryPrefixLossSchedule.commonRhoThreshold
              ordinaryPrefix) ^ mild.levelCount)))
  commonDelta₀_pos : 0 < commonDelta₀
  commonDelta₀_le_mild : commonDelta₀ ≤ mild.sourceDelta₀
  commonDelta₀_le_endpoint : commonDelta₀ ≤ endpointKernel.delta₀
  commonDelta₀_le_prefix : commonDelta₀ ≤
    PureWZ2C2OrdinaryPrefixLossSchedule.commonDeltaThreshold ordinaryPrefix
  commonDelta₀_le_rho_power : commonDelta₀ ≤
    (PureWZ2C2OrdinaryPrefixLossSchedule.commonRhoThreshold ordinaryPrefix) ^
      mild.levelCount

/-- Assemble the complete ordinary-prefix and endpoint scalar schedule before
runtime.  P5–P7 losses are added by the final closure schedule. -/
theorem pureWZ2C2_ordinaryGlobalSchedule
    (capability : PureWZ2PropStickyCapability)
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (houtput : 0 < outputLoss)
    (htarget : 0 < targetDelta₀)
    (hC : 0 < C)
    (hCtotal : 2 ≤ Ctotal) :
    Nonempty (PureWZ2C2OrdinaryGlobalSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal) := by
  rcases exists_pureWZ2Proposition64MildRescalingScalarSchedule
      houtput htarget hC (lt_of_lt_of_le (by norm_num) hCtotal) with
    ⟨mild⟩
  have hworkOne : mild.workLoss ≤ 1 := by
    have hepsilonHalf : mild.epsilon₂ ≤ 1 / 2 := by
      rw [mild.epsilon₂_eq]
      have hN : (2 : ℝ) ≤ mild.levelCount := by
        exact_mod_cast mild.levelCount_ge_two
      exact one_div_le_one_div_of_le (by norm_num) hN
    exact mild.workLoss_le_epsilon₂.trans (hepsilonHalf.trans (by norm_num))
  have hepsilonOne : mild.epsilon₂ ≤ 1 := by
    rw [mild.epsilon₂_eq]
    have hN : (1 : ℝ) ≤ mild.levelCount := by
      exact_mod_cast (le_trans (by omega) mild.levelCount_ge_two)
    simpa using one_div_le_one_div_of_le (by norm_num) hN
  let endpointOutputLoss :=
    min mild.workLoss <|
      min mild.workLoss (min (sigma / 16) (mild.epsilon₂ * sigma / 512))
  have hendpointPos : 0 < endpointOutputLoss := by
    exact lt_min mild.workLoss_pos <| lt_min mild.workLoss_pos <|
      lt_min (div_pos critical.sigma_pos (by norm_num))
        (div_pos (mul_pos mild.epsilon₂_pos critical.sigma_pos) (by norm_num))
  have hendpointWork : endpointOutputLoss ≤ mild.workLoss :=
    min_le_left _ _
  have hendpointSigma : endpointOutputLoss ≤ sigma / 16 :=
    (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have hendpointOne : endpointOutputLoss ≤ 1 :=
    hendpointWork.trans hworkOne
  rcases PureWZ2.proposition63_rich_sticky_kernel sigma critical
      endpointOutputLoss hendpointPos hendpointOne with ⟨endpointKernel⟩
  have hendpointGraph :
      endpointKernel.sourceLoss ≤ mild.epsilon₂ * sigma / 1024 := by
    have houtputGraph :
        endpointOutputLoss ≤ mild.epsilon₂ * sigma / 512 :=
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
    have hsourceOutput :
        endpointKernel.sourceLoss ≤ endpointOutputLoss / 2 := by
      exact endpointKernel.sourceLoss_le_half.trans <|
        div_le_div_of_nonneg_right
          endpointKernel.normalizationLoss_lt_output.le (by norm_num)
    calc
      endpointKernel.sourceLoss ≤ endpointOutputLoss / 2 := hsourceOutput
      _ ≤ (mild.epsilon₂ * sigma / 512) / 2 := by gcongr
      _ = mild.epsilon₂ * sigma / 1024 := by ring
  let ordinaryPrefix := critical.c2OrdinaryPrefixLossSchedule capability
    mild.levelCount_ge_two endpointKernel.sourceLoss_pos
      (endpointKernel.sourceLoss_le_half.trans <|
        (half_le_self endpointKernel.normalizationLoss_pos.le).trans <|
          endpointKernel.normalizationLoss_lt_output.le.trans hendpointOne)
      (endpointKernel.sourceLoss_le_half.trans <| by
        have hnormal :
            endpointKernel.normalizationLoss ≤ endpointOutputLoss :=
          endpointKernel.normalizationLoss_lt_output.le
        have hsigma := critical.sigma_pos
        nlinarith [hnormal, hendpointSigma])
      hendpointGraph mild.epsilon₂_pos hepsilonOne
  let ordinaryEndpointLoss :=
    ordinaryPrefix.totalOutputLoss + endpointOutputLoss
  have hprefixWork :
      ordinaryPrefix.totalOutputLoss ≤ endpointOutputLoss / 7 := by
    exact ordinaryPrefix.totalOutputLoss_le_terminal_seventh.trans <| by
      gcongr
      exact endpointKernel.sourceLoss_le_half.trans <|
        (half_le_self endpointKernel.normalizationLoss_pos.le).trans
          endpointKernel.normalizationLoss_lt_output.le
  have hlossTwo :
      ordinaryEndpointLoss ≤ 2 * mild.epsilon₂ := by
    dsimp only [ordinaryEndpointLoss]
    have hwork := mild.workLoss_le_epsilon₂
    nlinarith [mild.epsilon₂_pos, hendpointWork]
  have hlossTotal :
      ordinaryEndpointLoss ≤ Ctotal * mild.epsilon₂ := by
    exact hlossTwo.trans <|
      mul_le_mul_of_nonneg_right hCtotal mild.epsilon₂_pos.le
  have hlossOutput :
      ordinaryEndpointLoss ≤
        (1 - C * mild.epsilon₂) * outputLoss :=
    hlossTotal.trans mild.total_loss_margin
  let commonDelta₀ :=
    min mild.sourceDelta₀
      (min endpointKernel.delta₀
        (min ordinaryPrefix.commonDeltaThreshold
          (ordinaryPrefix.commonRhoThreshold ^ mild.levelCount)))
  exact ⟨{
    sigma_pos := critical.sigma_pos
    sigma_lt_one := critical.sigma_lt_one
    mild := mild
    endpointBound := mild.workLoss
    endpointBound_pos := mild.workLoss_pos
    endpointOutputLoss := endpointOutputLoss
    endpointOutputLoss_eq := rfl
    endpointOutputLoss_pos := hendpointPos
    endpointOutputLoss_le_bound := min_le_left _ _
    endpointOutputLoss_le_work := hendpointWork
    endpointOutputLoss_le_sigma_sixteenth := hendpointSigma
    endpointKernel := endpointKernel
    ordinaryPrefix := ordinaryPrefix
    ordinaryEndpointLoss := ordinaryEndpointLoss
    ordinaryEndpointLoss_eq := rfl
    ordinaryEndpointLoss_le_two_epsilon₂ := hlossTwo
    ordinaryEndpointLoss_le_totalMargin := hlossTotal
    ordinaryEndpointLoss_le_outputMargin := hlossOutput
    commonDelta₀ := commonDelta₀
    commonDelta₀_eq := by
      dsimp only [commonDelta₀]
    commonDelta₀_pos := lt_min mild.sourceDelta₀_pos <|
      lt_min endpointKernel.delta₀_pos <|
        lt_min ordinaryPrefix.commonDeltaThreshold_pos <|
          pow_pos ordinaryPrefix.commonRhoThreshold_pos mild.levelCount
    commonDelta₀_le_mild := min_le_left _ _
    commonDelta₀_le_endpoint :=
      (min_le_right _ _).trans (min_le_left _ _)
    commonDelta₀_le_prefix :=
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
    commonDelta₀_le_rho_power :=
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
  }⟩

/-- Variant of the ordinary schedule in which the endpoint output loss has
already been fixed by an outer terminal schedule.  This is the production
quantifier order for the direct-rich endpoint. -/
theorem pureWZ2C2_ordinaryGlobalScheduleWithEndpointBound
    (capability : PureWZ2PropStickyCapability)
    {sigma outputLoss targetDelta₀ C Ctotal endpointBound : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (mild : PureWZ2Proposition64MildRescalingScalarSchedule
      outputLoss targetDelta₀ C Ctotal)
    (houtput : 0 < outputLoss)
    (htarget : 0 < targetDelta₀)
    (hC : 0 < C)
    (hCtotal : 2 ≤ Ctotal)
    (hendpointBound : 0 < endpointBound) :
    ∃ schedule : PureWZ2C2OrdinaryGlobalSchedule
        capability sigma outputLoss targetDelta₀ C Ctotal,
      schedule.mild = mild ∧ schedule.endpointBound = endpointBound := by
  have hworkOne : mild.workLoss ≤ 1 := by
    have hepsilonHalf : mild.epsilon₂ ≤ 1 / 2 := by
      rw [mild.epsilon₂_eq]
      have hN : (2 : ℝ) ≤ mild.levelCount := by
        exact_mod_cast mild.levelCount_ge_two
      exact one_div_le_one_div_of_le (by norm_num) hN
    exact mild.workLoss_le_epsilon₂.trans (hepsilonHalf.trans (by norm_num))
  have hepsilonOne : mild.epsilon₂ ≤ 1 := by
    rw [mild.epsilon₂_eq]
    have hN : (1 : ℝ) ≤ mild.levelCount := by
      exact_mod_cast (le_trans (by omega) mild.levelCount_ge_two)
    simpa using one_div_le_one_div_of_le (by norm_num) hN
  let endpointOutputLoss := min endpointBound <|
    min mild.workLoss (min (sigma / 16) (mild.epsilon₂ * sigma / 512))
  have hendpointPos : 0 < endpointOutputLoss := by
    exact lt_min hendpointBound <| lt_min mild.workLoss_pos <|
      lt_min (div_pos critical.sigma_pos (by norm_num))
        (div_pos (mul_pos mild.epsilon₂_pos critical.sigma_pos) (by norm_num))
  have hendpointWork : endpointOutputLoss ≤ mild.workLoss :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hendpointSigma : endpointOutputLoss ≤ sigma / 16 :=
    (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have hendpointOne : endpointOutputLoss ≤ 1 := hendpointWork.trans hworkOne
  rcases PureWZ2.proposition63_rich_sticky_kernel sigma critical
      endpointOutputLoss hendpointPos hendpointOne with ⟨endpointKernel⟩
  have hendpointGraph :
      endpointKernel.sourceLoss ≤ mild.epsilon₂ * sigma / 1024 := by
    have houtputGraph : endpointOutputLoss ≤ mild.epsilon₂ * sigma / 512 :=
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
    have hsourceOutput : endpointKernel.sourceLoss ≤ endpointOutputLoss / 2 :=
      endpointKernel.sourceLoss_le_half.trans <|
        div_le_div_of_nonneg_right
          endpointKernel.normalizationLoss_lt_output.le (by norm_num)
    calc
      endpointKernel.sourceLoss ≤ endpointOutputLoss / 2 := hsourceOutput
      _ ≤ (mild.epsilon₂ * sigma / 512) / 2 := by gcongr
      _ = mild.epsilon₂ * sigma / 1024 := by ring
  let ordinaryPrefix := critical.c2OrdinaryPrefixLossSchedule capability
    mild.levelCount_ge_two endpointKernel.sourceLoss_pos
      (endpointKernel.sourceLoss_le_half.trans <|
        (half_le_self endpointKernel.normalizationLoss_pos.le).trans <|
          endpointKernel.normalizationLoss_lt_output.le.trans hendpointOne)
      (endpointKernel.sourceLoss_le_half.trans <| by
        have hnormal := endpointKernel.normalizationLoss_lt_output.le
        nlinarith [critical.sigma_pos, hnormal, hendpointSigma])
      hendpointGraph mild.epsilon₂_pos hepsilonOne
  let ordinaryEndpointLoss := ordinaryPrefix.totalOutputLoss + endpointOutputLoss
  have hprefixWork : ordinaryPrefix.totalOutputLoss ≤ endpointOutputLoss / 7 :=
    ordinaryPrefix.totalOutputLoss_le_terminal_seventh.trans <| by
      gcongr
      exact endpointKernel.sourceLoss_le_half.trans <|
        (half_le_self endpointKernel.normalizationLoss_pos.le).trans
          endpointKernel.normalizationLoss_lt_output.le
  have hlossTwo : ordinaryEndpointLoss ≤ 2 * mild.epsilon₂ := by
    dsimp only [ordinaryEndpointLoss]
    linarith [mild.epsilon₂_pos, mild.workLoss_le_epsilon₂, hendpointWork]
  have hlossTotal : ordinaryEndpointLoss ≤ Ctotal * mild.epsilon₂ :=
    hlossTwo.trans <| mul_le_mul_of_nonneg_right hCtotal mild.epsilon₂_pos.le
  have hlossOutput : ordinaryEndpointLoss ≤
      (1 - C * mild.epsilon₂) * outputLoss :=
    hlossTotal.trans mild.total_loss_margin
  let commonDelta₀ := min mild.sourceDelta₀
    (min endpointKernel.delta₀
      (min ordinaryPrefix.commonDeltaThreshold
        (ordinaryPrefix.commonRhoThreshold ^ mild.levelCount)))
  refine ⟨{
    sigma_pos := critical.sigma_pos
    sigma_lt_one := critical.sigma_lt_one
    mild := mild
    endpointBound := endpointBound
    endpointBound_pos := hendpointBound
    endpointOutputLoss := endpointOutputLoss
    endpointOutputLoss_eq := rfl
    endpointOutputLoss_pos := hendpointPos
    endpointOutputLoss_le_bound := min_le_left _ _
    endpointOutputLoss_le_work := hendpointWork
    endpointOutputLoss_le_sigma_sixteenth := hendpointSigma
    endpointKernel := endpointKernel
    ordinaryPrefix := ordinaryPrefix
    ordinaryEndpointLoss := ordinaryEndpointLoss
    ordinaryEndpointLoss_eq := rfl
    ordinaryEndpointLoss_le_two_epsilon₂ := hlossTwo
    ordinaryEndpointLoss_le_totalMargin := hlossTotal
    ordinaryEndpointLoss_le_outputMargin := hlossOutput
    commonDelta₀ := commonDelta₀
    commonDelta₀_eq := rfl
    commonDelta₀_pos := lt_min mild.sourceDelta₀_pos <|
      lt_min endpointKernel.delta₀_pos <|
        lt_min ordinaryPrefix.commonDeltaThreshold_pos <|
          pow_pos ordinaryPrefix.commonRhoThreshold_pos mild.levelCount
    commonDelta₀_le_mild := min_le_left _ _
    commonDelta₀_le_endpoint := (min_le_right _ _).trans (min_le_left _ _)
    commonDelta₀_le_prefix := (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
    commonDelta₀_le_rho_power := (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_right _ _) }, ?_, ?_⟩
  · rfl
  · rfl

namespace PureWZ2C2OrdinaryGlobalSchedule

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2OrdinaryGlobalSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal)

structure ActualTwoCallPullbackData
    {sourceDelta inputLoss : ℝ}
    (level : Fin (schedule.mild.levelCount - 1))
    (current : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent) where
  rhoRequested : WZ2PaperRequestedScale sourceDelta
  rhoRequested_eq :
    rhoRequested.1 =
      wz1Corollary26Scale sourceDelta schedule.mild.levelCount
        ⟨level, by omega⟩
  inputLossLe :
    inputLoss ≤
      ((((schedule.ordinaryPrefix.level level).level.ordinary.calls
        ).firstCallSchedule capability).kernel.sourceLoss)
  sqrtRequested : WZ2PaperRequestedScale rhoRequested.1
  sqrtRequested_eq : sqrtRequested.1 = Real.sqrt rhoRequested.1
  twoScale : PureWZ2Node05V4RichSecondCallData
    (schedule.ordinaryPrefix.level level).level.ordinary.calls
    current rhoRequested inputLossLe sqrtRequested
  pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
    (rho := wz1Corollary26Scale sourceDelta schedule.mild.levelCount
      ⟨level, by omega⟩) twoScale

/-- The production two-call witness for one ordinary hierarchy level.  The
two direct-rich calls run at the internal sticky scale `targetRho / 1280`;
their trapezoids return at the exact hierarchy scale `targetRho`. -/
structure ActualInternalTwoCallPullbackData
    {sourceDelta inputLoss : ℝ}
    (level : Fin (schedule.mild.levelCount - 1))
    (current : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent) where
  targetRho : ℝ :=
    wz1Corollary26Scale sourceDelta schedule.mild.levelCount
      ⟨level, by omega⟩
  targetRho_eq :
    targetRho = wz1Corollary26Scale sourceDelta schedule.mild.levelCount
      ⟨level, by omega⟩
  outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
    sourceDelta targetRho
      (schedule.ordinaryPrefix.level level).level.ordinary.calls.firstOutputLoss
      (schedule.ordinaryPrefix.level level).level.outputLoss
  rhoRequested : WZ2PaperRequestedScale sourceDelta
  rhoRequested_eq :
    rhoRequested.1 = pureWZ2SourceHorizontalInternalScale targetRho
  inputLossLe :
    inputLoss ≤
      ((((schedule.ordinaryPrefix.level level).level.ordinary.calls
        ).firstCallSchedule capability).kernel.sourceLoss)
  sqrtRequested : WZ2PaperRequestedScale rhoRequested.1
  sqrtRequested_eq : sqrtRequested.1 = Real.sqrt rhoRequested.1
  twoScale : PureWZ2Node05V4RichSecondCallData
    (schedule.ordinaryPrefix.level level).level.ordinary.calls
    current rhoRequested inputLossLe sqrtRequested
  pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
    (rho := rhoRequested.1) twoScale
  final_scale_eq :
    pureWZ2SourceHorizontalFinalScale rhoRequested.1 = targetRho

/-- The first production P3 object at one actual ordinary hierarchy level:
the exact internal two-call witness together with all paper-heavy prescribed-
slab neighborhoods constructed from the common P0 schedule. -/
structure ActualHeavySlabNeighborhoodData
    {sourceDelta inputLoss : ℝ}
    (level : Fin (schedule.mild.levelCount - 1))
    (current : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent) where
  internal : schedule.ActualInternalTwoCallPullbackData level current
  family : PureWZ2Node05V4RichHeavySlabNeighborhoodFamily
    internal.pullback
      (schedule.ordinaryPrefix.level level).level.neighborhoodLoss

/-- The actual ordinary P3 prefix through common-bin selection.  Each output
envelope is indexed by its exact heavy-slab neighborhood and reuses that
neighborhood's `Z_S`, outer reference height, and fixed line. -/
structure ActualNeighborhoodCommonBinData
    {sourceDelta inputLoss : ℝ}
    (level : Fin (schedule.mild.levelCount - 1))
    (current : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent) where
  neighborhoods : schedule.ActualHeavySlabNeighborhoodData level current
  commonBins : PureWZ2Node05V4RichNeighborhoodCommonBinFamilyData
    neighborhoods.family

/-- The paper-order heavy-slab construction through Theorem 5.2, exact
trapezoids, and the single mod-64 residue, on one actual internal witness. -/
structure ActualSaturatedResidueData
    {sourceDelta inputLoss : ℝ}
    (level : Fin (schedule.mild.levelCount - 1))
    (current : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent)
    (hbridge : PureWZ2PaperADBridgeStatement) where
  neighborhoods : schedule.ActualHeavySlabNeighborhoodData level current
  tail : PureWZ2Node05V4RichHeavySlabSaturatedTailFamily
    (eta := (schedule.ordinaryPrefix.level level).level.normalEta)
    neighborhoods.family hbridge
      (schedule.ordinaryPrefix.level level).level.projection
  trapezoids : PureWZ2Node05V4RichSaturatedTrapezoidFamily tail
  residue : PureWZ2Node05V4RichSaturatedResidueData trapezoids

theorem actualScale_le_epsilon₂_power
    {sourceDelta : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (level : Fin (schedule.mild.levelCount - 1)) :
    wz1Corollary26Scale sourceDelta schedule.mild.levelCount
        ⟨level, by omega⟩ ≤
      Real.rpow sourceDelta schedule.mild.epsilon₂ := by
  have hsourceOne :
      sourceDelta ≤ 1 :=
    (hsourceSmall.trans schedule.commonDelta₀_le_mild) |>
      schedule.mild.sourceDelta_le_one hsourceDelta
  have hNpos : (0 : ℝ) < schedule.mild.levelCount := by
    exact_mod_cast
      (lt_of_lt_of_le (by omega) schedule.mild.levelCount_ge_two)
  have hexponent :
      1 / (schedule.mild.levelCount : ℝ) ≤
        ((level : ℝ) + 1) /
          (schedule.mild.levelCount : ℝ) := by
    gcongr
    exact_mod_cast (show 1 ≤ (level : ℕ) + 1 by omega)
  rw [schedule.mild.epsilon₂_eq]
  unfold wz1Corollary26Scale
  rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
  exact Real.rpow_le_rpow_of_exponent_ge hsourceDelta hsourceOne <| by
    simpa using hexponent

/-- Every actual ordinary hierarchy scale lies below the one common runtime
rho cutoff selected before the source scale. -/
theorem actualScale_le_commonRho
    {sourceDelta : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (level : Fin (schedule.mild.levelCount - 1)) :
    wz1Corollary26Scale sourceDelta schedule.mild.levelCount
        ⟨level, by omega⟩ ≤
      schedule.ordinaryPrefix.commonRhoThreshold := by
  let N := schedule.mild.levelCount
  let r := schedule.ordinaryPrefix.commonRhoThreshold
  have hNtwo : 2 ≤ N := schedule.mild.levelCount_ge_two
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hr : 0 < r := schedule.ordinaryPrefix.commonRhoThreshold_pos
  have hrOne : r ≤ 1 :=
    schedule.ordinaryPrefix.commonRhoThreshold_le_one
  have hsourceRhoPower : sourceDelta ≤ r ^ N :=
    hsourceSmall.trans schedule.commonDelta₀_le_rho_power
  have hsourceOne : sourceDelta ≤ 1 := by
    exact hsourceRhoPower.trans <|
      pow_le_one₀ (by positivity) hrOne
  have hlevelExponent :
      1 / (N : ℝ) ≤ (((level : ℕ) + 1 : ℝ) / (N : ℝ)) := by
    apply div_le_div_of_nonneg_right
    · norm_num
    · positivity
  have hscaleFirst :
      wz1Corollary26Scale sourceDelta N ⟨level, by omega⟩ ≤
        Real.rpow sourceDelta (1 / (N : ℝ)) := by
    unfold wz1Corollary26Scale
    exact Real.rpow_le_rpow_of_exponent_ge
      hsourceDelta hsourceOne hlevelExponent
  have hrootPower :
      Real.rpow sourceDelta (1 / (N : ℝ)) ≤
        Real.rpow (r ^ N) (1 / (N : ℝ)) :=
    Real.rpow_le_rpow hsourceDelta.le hsourceRhoPower (by positivity)
  have hpowerRoot :
      Real.rpow (r ^ N) (1 / (N : ℝ)) = r := by
    have hcancel : (N : ℝ) * (1 / (N : ℝ)) = 1 := by
      field_simp [hNpos.ne']
    calc
      Real.rpow (r ^ N) (1 / (N : ℝ)) =
          Real.rpow (Real.rpow r (N : ℝ)) (1 / (N : ℝ)) := by
        congr 1
        exact (Real.rpow_natCast r N).symm
      _ = Real.rpow r ((N : ℝ) * (1 / (N : ℝ))) :=
        (Real.rpow_mul hr.le (N : ℝ) (1 / (N : ℝ))).symm
      _ = r := by
        rw [hcancel]
        exact Real.rpow_one r
  exact hscaleFirst.trans (hrootPower.trans_eq hpowerRoot)

/-- All scalar premises of the scheduled one-scale consumer hold at each
actual ordinary hierarchy scale, apart from runtime source data themselves. -/
theorem actualLevel_thresholds
    {sourceDelta : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (level : Fin (schedule.mild.levelCount - 1)) :
    let rho := wz1Corollary26Scale sourceDelta schedule.mild.levelCount
      ⟨level, by omega⟩
    sourceDelta ≤
      (schedule.ordinaryPrefix.level level).level.floorSchedule.delta₀ ∧
    sourceDelta ≤
      (schedule.ordinaryPrefix.level level).level.ordinary.densityThreshold.delta₀ ∧
    sourceDelta ≤
      (((schedule.ordinaryPrefix.level level).level.ordinary.calls
        ).firstCallSchedule capability).kernel.delta₀ ∧
    sourceDelta ≤
      (schedule.ordinaryPrefix.level level).level.ordinary.calls.secondKernel.delta₀ ∧
    sourceDelta ≤
      (schedule.ordinaryPrefix.level level).level.graphThreshold.delta₀ ∧
    rho ≤
      (schedule.ordinaryPrefix.level level).level.ordinary.calls.secondKernel.delta₀ ∧
    rho ≤
      (schedule.ordinaryPrefix.level level).level.ordinary.densityThreshold.rho₀ ∧
    rho ≤
      (schedule.ordinaryPrefix.level level).level.projection.rho₀ ∧
    rho ≤
      (schedule.ordinaryPrefix.level level).level.analytic.rho0 ∧
    rho ≤
      (schedule.ordinaryPrefix.level level).level.geometric.rho0 ∧
    rho ≤
      (schedule.ordinaryPrefix.level level).level.graphThreshold.rho₀ ∧
    sourceDelta ≤ rho ∧
    Real.rpow sourceDelta (1 - schedule.mild.epsilon₂) ≤ rho ∧
    rho ≤ Real.rpow sourceDelta schedule.mild.epsilon₂ := by
  dsimp only
  have hlevelDelta :
      sourceDelta ≤ schedule.ordinaryPrefix.levelDeltaThreshold level :=
    hsourceSmall.trans <|
      schedule.commonDelta₀_le_prefix.trans
        (schedule.ordinaryPrefix.commonDeltaThreshold_le level)
  have hlevelRho :
      wz1Corollary26Scale sourceDelta schedule.mild.levelCount
          ⟨level, by omega⟩ ≤
        schedule.ordinaryPrefix.levelRhoThreshold level :=
    schedule.actualScale_le_commonRho hsourceDelta hsourceSmall level |>.trans
      (schedule.ordinaryPrefix.commonRhoThreshold_le level)
  have hsourceOne :
      sourceDelta ≤ 1 :=
    (hsourceSmall.trans schedule.commonDelta₀_le_mild) |>
      schedule.mild.sourceDelta_le_one hsourceDelta
  have hdeltaScale :
      sourceDelta ≤
        wz1Corollary26Scale sourceDelta schedule.mild.levelCount
          ⟨level, by omega⟩ :=
    pureWZ2Hierarchy_delta_le_scale schedule.mild.levelCount_ge_two
      hsourceDelta hsourceOne ⟨level, by omega⟩
  have hscaleExponent :
      (((level : ℕ) + 1 : ℕ) : ℝ) /
          (schedule.mild.levelCount : ℝ) ≤
        1 - schedule.mild.epsilon₂ := by
    rw [schedule.mild.epsilon₂_eq]
    have hNpos : (0 : ℝ) < schedule.mild.levelCount := by
      exact_mod_cast (lt_of_lt_of_le (by omega) schedule.mild.levelCount_ge_two)
    have hlevelNat :
        (level : ℕ) + 2 ≤ schedule.mild.levelCount := by omega
    have hlevelRealRaw :
        (((level : ℕ) + 2 : ℕ) : ℝ) ≤
          (schedule.mild.levelCount : ℝ) := by
      exact_mod_cast hlevelNat
    have hlevelReal :
        (((level : ℕ) + 1 : ℕ) : ℝ) ≤
          (schedule.mild.levelCount : ℝ) - 1 := by
      norm_num at hlevelRealRaw ⊢
      linarith
    calc
      (((level : ℕ) + 1 : ℕ) : ℝ) /
          (schedule.mild.levelCount : ℝ) ≤
        ((schedule.mild.levelCount : ℝ) - 1) /
          (schedule.mild.levelCount : ℝ) := by gcongr
      _ = 1 - 1 / (schedule.mild.levelCount : ℝ) := by
        field_simp [hNpos.ne']
  have hscaleLower :
      Real.rpow sourceDelta (1 - schedule.mild.epsilon₂) ≤
        wz1Corollary26Scale sourceDelta schedule.mild.levelCount
          ⟨level, by omega⟩ := by
    simpa [wz1Corollary26Scale] using
      Real.rpow_le_rpow_of_exponent_ge hsourceDelta hsourceOne hscaleExponent
  have hscaleUpper :=
    schedule.actualScale_le_epsilon₂_power hsourceDelta hsourceSmall level
  unfold PureWZ2C2OrdinaryPrefixLossSchedule.levelDeltaThreshold at hlevelDelta
  unfold PureWZ2C2OrdinaryPrefixLossSchedule.levelRhoThreshold at hlevelRho
  have hlevelDeltaOld := hlevelDelta.trans <|
    (min_le_left _ _).trans (min_le_left _ _)
  have hlevelRhoOld := hlevelRho.trans (min_le_left _ _)
  refine ⟨hlevelDeltaOld.trans ((min_le_left _ _).trans (min_le_left _ _)),
    hlevelDeltaOld.trans ((min_le_right _ _).trans (min_le_left _ _)),
    hlevelDeltaOld.trans ((min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)),
    hlevelDeltaOld.trans ((min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_left _ _)),
    hlevelDeltaOld.trans ((min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_right _ _)),
    hlevelRhoOld.trans (min_le_left _ _),
    hlevelRhoOld.trans ((min_le_right _ _).trans (min_le_left _ _)),
    hlevelRhoOld.trans ((min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)),
    hlevelRhoOld.trans ((min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_left _ _)),
    hlevelRhoOld.trans ((min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)),
    hlevelRhoOld.trans ((min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)),
    hdeltaScale, hscaleLower, hscaleUpper⟩

/-- The newly added all-heavy-slab budget cutoffs also hold at every actual
ordinary hierarchy scale.  Kept separate from `actualLevel_thresholds` so the
existing tuple ABI remains unchanged. -/
theorem actualLevel_neighborhoodThresholds
    {sourceDelta : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (level : Fin (schedule.mild.levelCount - 1)) :
    sourceDelta ≤
        (schedule.ordinaryPrefix.level level).level.neighborhoodThreshold.delta₀ ∧
      wz1Corollary26Scale sourceDelta schedule.mild.levelCount
          ⟨level, by omega⟩ ≤
        (schedule.ordinaryPrefix.level level).level.neighborhoodThreshold.rho₀ := by
  have hlevelDelta :
      sourceDelta ≤ schedule.ordinaryPrefix.levelDeltaThreshold level :=
    hsourceSmall.trans <|
      schedule.commonDelta₀_le_prefix.trans
        (schedule.ordinaryPrefix.commonDeltaThreshold_le level)
  have hlevelRho :
      wz1Corollary26Scale sourceDelta schedule.mild.levelCount
          ⟨level, by omega⟩ ≤
        schedule.ordinaryPrefix.levelRhoThreshold level :=
    schedule.actualScale_le_commonRho hsourceDelta hsourceSmall level |>.trans
      (schedule.ordinaryPrefix.commonRhoThreshold_le level)
  unfold PureWZ2C2OrdinaryPrefixLossSchedule.levelDeltaThreshold at hlevelDelta
  unfold PureWZ2C2OrdinaryPrefixLossSchedule.levelRhoThreshold at hlevelRho
  exact ⟨hlevelDelta.trans ((min_le_right _ _).trans (min_le_left _ _)),
    hlevelRho.trans ((min_le_right _ _).trans (min_le_left _ _))⟩

/-- The source-popular capacity cutoffs also hold at every actual ordinary
hierarchy scale. -/
theorem actualLevel_capacityThresholds
    {sourceDelta : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (level : Fin (schedule.mild.levelCount - 1)) :
    sourceDelta ≤
        (schedule.ordinaryPrefix.level level).level.capacityThreshold.delta₀ ∧
      wz1Corollary26Scale sourceDelta schedule.mild.levelCount
          ⟨level, by omega⟩ ≤
        (schedule.ordinaryPrefix.level level).level.capacityThreshold.rho₀ := by
  have hlevelDelta :
      sourceDelta ≤ schedule.ordinaryPrefix.levelDeltaThreshold level :=
    hsourceSmall.trans <|
      schedule.commonDelta₀_le_prefix.trans
        (schedule.ordinaryPrefix.commonDeltaThreshold_le level)
  have hlevelRho :
      wz1Corollary26Scale sourceDelta schedule.mild.levelCount
          ⟨level, by omega⟩ ≤
        schedule.ordinaryPrefix.levelRhoThreshold level :=
    schedule.actualScale_le_commonRho hsourceDelta hsourceSmall level |>.trans
      (schedule.ordinaryPrefix.commonRhoThreshold_le level)
  unfold PureWZ2C2OrdinaryPrefixLossSchedule.levelDeltaThreshold at hlevelDelta
  unfold PureWZ2C2OrdinaryPrefixLossSchedule.levelRhoThreshold at hlevelRho
  exact ⟨hlevelDelta.trans ((min_le_right _ _).trans (min_le_right _ _)),
    hlevelRho.trans ((min_le_right _ _).trans (min_le_right _ _))⟩

/-- The transition scalar closure selected by P0 is valid at every actual
ordinary hierarchy level. -/
theorem actualLevel_transitionScalarThreshold
    {sourceDelta : ℝ}
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (level : Fin (schedule.mild.levelCount - 1)) :
    sourceDelta ≤
      (schedule.ordinaryPrefix.level level).level.transition.scalarClosure.delta₀ := by
  have hlevelDelta :
      sourceDelta ≤ schedule.ordinaryPrefix.levelDeltaThreshold level :=
    hsourceSmall.trans <|
      schedule.commonDelta₀_le_prefix.trans
        (schedule.ordinaryPrefix.commonDeltaThreshold_le level)
  unfold PureWZ2C2OrdinaryPrefixLossSchedule.levelDeltaThreshold at hlevelDelta
  exact hlevelDelta.trans <|
    (min_le_left _ _).trans <|
      (min_le_left _ _).trans <|
        (min_le_left _ _).trans (min_le_right _ _)

/-- Build the exact internal scale `targetRho / 1280` at every actual ordinary
level.  Its final trapezoid scale is definitionally the hierarchy target. -/
theorem actualLevel_outerScale
    {sourceDelta : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (level : Fin (schedule.mild.levelCount - 1)) :
    Nonempty (PureWZ2SourceHorizontalFlexibleOuterScaleData
      sourceDelta
      (wz1Corollary26Scale sourceDelta schedule.mild.levelCount
        ⟨level, by omega⟩)
      (schedule.ordinaryPrefix.level level).level.ordinary.calls.firstOutputLoss
      (schedule.ordinaryPrefix.level level).level.outputLoss) := by
  rcases schedule.actualLevel_thresholds hsourceDelta hsourceSmall level with
    ⟨_hfloor, _hdensity, _hfirst, _hsecond, _hgraphDelta, _hsecondRho,
      _hdensityRho, _hprojectionRho, _hanalyticRho, _hgeometricRho,
      _hgraphRho, hdeltaRho, hscaleLower, hscaleUpper⟩
  have hlevelDelta :
      sourceDelta ≤ schedule.ordinaryPrefix.levelDeltaThreshold level :=
    hsourceSmall.trans <|
      schedule.commonDelta₀_le_prefix.trans
        (schedule.ordinaryPrefix.commonDeltaThreshold_le level)
  unfold PureWZ2C2OrdinaryPrefixLossSchedule.levelDeltaThreshold at hlevelDelta
  have houterDelta :
      sourceDelta ≤ (schedule.ordinaryPrefix.level level).level.outerDelta₀ :=
    hlevelDelta.trans <| (min_le_left _ _).trans (min_le_right _ _)
  let levelSchedule := (schedule.ordinaryPrefix.level level).level
  have htargetOne :
      wz1Corollary26Scale sourceDelta schedule.mild.levelCount
          ⟨level, by omega⟩ ≤ 1 :=
    _hgeometricRho.trans levelSchedule.geometric.rho0_le_one
  have hsourceOne : sourceDelta ≤ 1 := hdeltaRho.trans htargetOne
  have houtputEpsilon :
      levelSchedule.outputLoss ≤ schedule.mild.epsilon₂ := by
    calc
      levelSchedule.outputLoss ≤
          schedule.mild.epsilon₂ * sigma / 8192 :=
        levelSchedule.outputLoss_le_graphBudget
      _ ≤ schedule.mild.epsilon₂ := by
        have hepsilon := schedule.mild.epsilon₂_pos
        nlinarith [schedule.sigma_lt_one]
  have houtputLower :
      Real.rpow sourceDelta (1 - levelSchedule.outputLoss) ≤
        wz1Corollary26Scale sourceDelta schedule.mild.levelCount
          ⟨level, by omega⟩ := by
    calc
      Real.rpow sourceDelta (1 - levelSchedule.outputLoss) ≤
          Real.rpow sourceDelta (1 - schedule.mild.epsilon₂) :=
        Real.rpow_le_rpow_of_exponent_ge hsourceDelta hsourceOne (by linarith)
      _ ≤ _ := hscaleLower
  have houtputUpper :
      wz1Corollary26Scale sourceDelta schedule.mild.levelCount
          ⟨level, by omega⟩ ≤
        Real.rpow sourceDelta levelSchedule.outputLoss := by
    calc
      wz1Corollary26Scale sourceDelta schedule.mild.levelCount
          ⟨level, by omega⟩ ≤
        Real.rpow sourceDelta schedule.mild.epsilon₂ := hscaleUpper
      _ ≤ Real.rpow sourceDelta levelSchedule.outputLoss :=
        Real.rpow_le_rpow_of_exponent_ge hsourceDelta hsourceOne houtputEpsilon
  exact (schedule.ordinaryPrefix.level level).level.outerScale
    hsourceDelta houterDelta houtputLower houtputUpper

/-- Execute the two dependent direct-rich calls at the internal scale attached
to one actual hierarchy target.  The exact final-scale identity is retained in
the result rather than recovered by a later existential cast. -/
theorem actualLevel_internalTwoCallPullback
    {sourceDelta inputLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (level : Fin (schedule.mild.levelCount - 1))
    (current : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent)
    (hinputCeiling :
      inputLoss ≤
        (schedule.ordinaryPrefix.level level).level.sourceLossCeiling) :
    Nonempty (schedule.ActualInternalTwoCallPullbackData level current) := by
  rcases schedule.actualLevel_thresholds hsourceDelta hsourceSmall level with
    ⟨_hfloor, _hdensity, hfirstDelta, _hsourceSecond, _hgraphDelta,
      htargetSecond, _hdensityRho, _hprojectionRho, _hanalyticRho,
      _hgeometricRho, _hgraphRho, _hdeltaTarget, _hscaleLower,
      _hscaleUpper⟩
  rcases schedule.actualLevel_outerScale hsourceDelta hsourceSmall level with
    ⟨outer⟩
  let levelSchedule := (schedule.ordinaryPrefix.level level).level
  let targetRho := wz1Corollary26Scale sourceDelta schedule.mild.levelCount
    ⟨level, by omega⟩
  let internalRho := pureWZ2SourceHorizontalInternalScale targetRho
  let rhoRequested : WZ2PaperRequestedScale sourceDelta :=
    ⟨internalRho, outer.delta_le_internal, outer.internal_le_one⟩
  have hinputFirst :
      inputLoss ≤
        (levelSchedule.ordinary.calls.firstCallSchedule capability
          ).kernel.sourceLoss :=
    hinputCeiling.trans levelSchedule.sourceLossCeiling_le_firstKernel
  rcases (levelSchedule.ordinary.calls.firstCallSchedule capability).run
      current hinputFirst hfirstDelta rhoRequested
      (by simpa only [rhoRequested, internalRho] using outer.sticky_lower)
      (by simpa only [rhoRequested, internalRho] using outer.sticky_upper) with
    ⟨first⟩
  have htargetPos : 0 < targetRho := by
    dsimp only [targetRho, wz1Corollary26Scale]
    exact Real.rpow_pos_of_pos hsourceDelta _
  have hinternalTarget : internalRho ≤ targetRho := by
    dsimp only [internalRho, pureWZ2SourceHorizontalInternalScale]
    exact div_le_self htargetPos.le (by norm_num)
  have hinternalSecond :
      rhoRequested.1 ≤ levelSchedule.ordinary.calls.secondKernel.delta₀ := by
    simpa only [rhoRequested, internalRho, targetRho] using
      hinternalTarget.trans htargetSecond
  have hstickyHalf : levelSchedule.ordinary.stickyLoss ≤ 1 / 2 := by
    have hnextSigma :=
      (schedule.ordinaryPrefix.level level).nextSourceCeiling_le_sigma
    have houtputNext := levelSchedule.outputLoss_le_next_eighth
    have houtputHalf : levelSchedule.outputLoss ≤ 1 / 2 := by
      nlinarith [schedule.sigma_lt_one]
    exact levelSchedule.ordinary.stickyLoss_le_final.trans <| by
      rw [← levelSchedule.outputLoss_eq]
      exact houtputHalf
  have hinternalSq : internalRho ^ 2 ≤ internalRho := by
    have hinternalPos : 0 < internalRho := by
      simpa only [internalRho] using outer.internal_pos
    have hinternalOne : internalRho ≤ 1 := by
      simpa only [internalRho] using outer.internal_le_one
    nlinarith
  have hinternalSqrt : internalRho ≤ Real.sqrt internalRho :=
    (Real.le_sqrt outer.internal_pos.le outer.internal_pos.le).2 hinternalSq
  have hsqrtOne : Real.sqrt internalRho ≤ 1 :=
    Real.sqrt_le_one.mpr outer.internal_le_one
  let sqrtRequested : WZ2PaperRequestedScale rhoRequested.1 :=
    ⟨Real.sqrt internalRho,
      by simpa only [rhoRequested] using hinternalSqrt, hsqrtOne⟩
  have hsqrtLower :
      Real.rpow internalRho (1 - levelSchedule.ordinary.stickyLoss) ≤
        sqrtRequested.1 := by
    dsimp only [sqrtRequested]
    rw [Real.sqrt_eq_rpow, Real.rpow_eq_pow]
    exact Real.rpow_le_rpow_of_exponent_ge outer.internal_pos
      outer.internal_le_one (by linarith)
  have hsqrtUpper :
      sqrtRequested.1 ≤
        Real.rpow internalRho levelSchedule.ordinary.stickyLoss := by
    dsimp only [sqrtRequested]
    rw [Real.sqrt_eq_rpow, Real.rpow_eq_pow]
    exact Real.rpow_le_rpow_of_exponent_ge outer.internal_pos
      outer.internal_le_one hstickyHalf
  rcases levelSchedule.ordinary.calls.run first sqrtRequested rfl
      hinternalSecond
      (by simpa only [rhoRequested, internalRho] using hsqrtLower)
      (by simpa only [rhoRequested, internalRho] using hsqrtUpper) with
    ⟨twoScale⟩
  rcases PureWZ2Node05V4RichTwoScaleCellPullbackData.nonempty twoScale rfl with
    ⟨pullback⟩
  exact ⟨{
    targetRho := targetRho
    targetRho_eq := rfl
    outer := outer
    rhoRequested := rhoRequested
    rhoRequested_eq := rfl
    inputLossLe := hinputFirst
    sqrtRequested := sqrtRequested
    sqrtRequested_eq := rfl
    twoScale := twoScale
    pullback := pullback
    final_scale_eq := by
      simpa only [rhoRequested, internalRho] using outer.final_scale_eq
  }⟩

/-- Instantiate the common P0 neighborhood budget on the exact internal
two-call witness at one actual hierarchy level.  No runtime envelope-density,
cell-count, or source-volume hypothesis is exposed. -/
theorem actualLevel_heavySlabNeighborhoods
    {sourceDelta inputLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (level : Fin (schedule.mild.levelCount - 1))
    (current : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinputCeiling :
      inputLoss ≤
        (schedule.ordinaryPrefix.level level).level.sourceLossCeiling)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (schedule.ActualHeavySlabNeighborhoodData level current) := by
  rcases schedule.actualLevel_internalTwoCallPullback hsourceDelta hsourceSmall
      level current hinputCeiling with ⟨internal⟩
  let levelSchedule := (schedule.ordinaryPrefix.level level).level
  rcases schedule.actualLevel_neighborhoodThresholds hsourceDelta hsourceSmall
      level with ⟨hdeltaNeighborhood, htargetNeighborhood⟩
  have htargetPos : 0 < internal.targetRho := by
    rw [internal.targetRho_eq]
    exact Real.rpow_pos_of_pos hsourceDelta _
  have hinternalTarget : internal.rhoRequested.1 ≤ internal.targetRho := by
    rw [internal.rhoRequested_eq]
    unfold pureWZ2SourceHorizontalInternalScale
    exact div_le_self htargetPos.le (by norm_num)
  have hinternalSmall : internal.rhoRequested.1 ≤ 1 / 12 := by
    have hgraph : 256 * internal.rhoRequested.1 ≤ 1 := by
      simpa only [internal.rhoRequested_eq] using internal.outer.graph_scale_le_one
    nlinarith
  have hinternalThreshold :
      internal.rhoRequested.1 ≤ levelSchedule.neighborhoodThreshold.rho₀ :=
    hinternalTarget.trans <| by
      simpa only [internal.targetRho_eq] using htargetNeighborhood
  have hinternalPower :
      internal.rhoRequested.1 ≤ Real.rpow sourceDelta schedule.mild.epsilon₂ := by
    rcases schedule.actualLevel_thresholds hsourceDelta hsourceSmall level with
      ⟨_hfloor, _hdensity, _hfirst, _hsecond, _hgraphDelta, _hsecondRho,
        _hdensityRho, _hprojectionRho, _hanalyticRho, _hgeometricRho,
        _hgraphRho, _hdeltaTarget, _hscaleLower, htargetPower⟩
    exact hinternalTarget.trans <| by
      simpa only [internal.targetRho_eq] using htargetPower
  rcases internal.pullback.heavySlabNeighborhoodFamilyOfThreshold hbridge
      levelSchedule.neighborhoodThreshold hinputNonneg hinputCeiling le_rfl
      hdeltaNeighborhood hinternalSmall hinternalThreshold hinternalPower with
    ⟨family⟩
  exact ⟨{ internal := internal, family := family }⟩

/-- Instantiate the family-independent common-bin threshold on every actual
heavy-slab neighborhood, without reselecting its source-popular set or fixed
line. -/
theorem actualLevel_neighborhoodCommonBins
    {sourceDelta inputLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (level : Fin (schedule.mild.levelCount - 1))
    (current : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinputCeiling :
      inputLoss ≤
        (schedule.ordinaryPrefix.level level).level.sourceLossCeiling)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (schedule.ActualNeighborhoodCommonBinData level current) := by
  rcases schedule.actualLevel_heavySlabNeighborhoods hsourceDelta hsourceSmall
      level current hinputNonneg hinputCeiling hbridge with ⟨neighborhoods⟩
  have hgraphOne : 256 * neighborhoods.internal.rhoRequested.1 ≤ 1 := by
    rw [neighborhoods.internal.rhoRequested_eq]
    exact neighborhoods.internal.outer.graph_scale_le_one
  rcases neighborhoods.family.commonBinEnvelopes hgraphOne with ⟨commonBins⟩
  exact ⟨{ neighborhoods := neighborhoods, commonBins := commonBins }⟩

/-- Run the complete paper-order Theorem-5.2 tail, form the exact public-scale
trapezoids, and make the single separated residue selection at one actual
ordinary hierarchy level. -/
theorem actualLevel_saturatedResidue
    {sourceDelta inputLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (level : Fin (schedule.mild.levelCount - 1))
    (current : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinputCeiling :
      inputLoss ≤
        (schedule.ordinaryPrefix.level level).level.sourceLossCeiling)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (schedule.ActualSaturatedResidueData level current hbridge) := by
  rcases schedule.actualLevel_heavySlabNeighborhoods hsourceDelta hsourceSmall
      level current hinputNonneg hinputCeiling hbridge with ⟨neighborhoods⟩
  let levelSchedule := (schedule.ordinaryPrefix.level level).level
  let internal := neighborhoods.internal
  rcases schedule.actualLevel_thresholds hsourceDelta hsourceSmall level with
    ⟨_hfloor, _hdensity, _hfirst, _hsecond, hgraphDelta,
      _htargetSecond, _hdensityRho, htargetProjection, htargetAnalytic,
      htargetGeometric, htargetGraph, _hdeltaTarget, _hscaleLower,
      htargetPower⟩
  have hinternalPos : 0 < internal.rhoRequested.1 := by
    simpa only [internal.rhoRequested_eq] using internal.outer.internal_pos
  have htargetPos : 0 < internal.targetRho := by
    rw [internal.targetRho_eq]
    exact Real.rpow_pos_of_pos hsourceDelta _
  have hinternalTarget : internal.rhoRequested.1 ≤ internal.targetRho := by
    rw [internal.rhoRequested_eq]
    unfold pureWZ2SourceHorizontalInternalScale
    exact div_le_self htargetPos.le (by norm_num)
  have hinternalGeometric :
      internal.rhoRequested.1 ≤ levelSchedule.geometric.rho0 :=
    hinternalTarget.trans <| by
      simpa only [internal.targetRho_eq] using htargetGeometric
  have hinternalGraph :
      internal.rhoRequested.1 ≤ levelSchedule.graphThreshold.rho₀ :=
    hinternalTarget.trans <| by
      simpa only [internal.targetRho_eq] using htargetGraph
  have hinternalProjection :
      internal.rhoRequested.1 ≤ levelSchedule.projection.rho₀ :=
    hinternalTarget.trans <| by
      simpa only [internal.targetRho_eq] using htargetProjection
  have hinternalPower :
      internal.rhoRequested.1 ≤ Real.rpow sourceDelta schedule.mild.epsilon₂ :=
    hinternalTarget.trans <| by
      simpa only [internal.targetRho_eq] using htargetPower
  have hgraphAnalytic :
      256 * internal.rhoRequested.1 ≤ levelSchedule.analytic.rho0 := by
    have hscaled : 256 * internal.rhoRequested.1 ≤ internal.targetRho := by
      rw [internal.rhoRequested_eq]
      unfold pureWZ2SourceHorizontalInternalScale
      nlinarith [htargetPos]
    exact hscaled.trans <| by
      simpa only [internal.targetRho_eq] using htargetAnalytic
  have hCOne :
      (1 : ENNReal) ≤
        160 * Kakeya.realRpowENN sourceDelta (-inputLoss) := by
    have hpower :
        (1 : ENNReal) ≤ Kakeya.realRpowENN sourceDelta (-inputLoss) := by
      rw [Kakeya.realRpowENN, ENNReal.one_le_ofReal]
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hsourceDelta
        current.grain.extremal.delta_le_one (by linarith)
    calc
      (1 : ENNReal) ≤ 160 := by norm_num
      _ = 160 * 1 := by ring
      _ ≤ 160 * Kakeya.realRpowENN sourceDelta (-inputLoss) := by gcongr
  have hfinalEq :
      levelSchedule.outputLoss = levelSchedule.floorSchedule.densityLoss / 8 :=
    levelSchedule.outputLoss_eq.trans levelSchedule.ordinary.finalLoss_eq
  rcases neighborhoods.family.saturatedTail hbridge levelSchedule.projection
      levelSchedule.analytic levelSchedule.graphThreshold
      (by rw [internal.rhoRequested_eq]
          exact internal.outer.graph_scale_le_one)
      (levelSchedule.geometric.heightAbsorb internal.rhoRequested.1
        hinternalPos hinternalGeometric)
      schedule.sigma_pos schedule.sigma_lt_one levelSchedule.normalEta_pos
      (by nlinarith [levelSchedule.normalEta_pos,
          levelSchedule.normalEta_sigma])
      (by rw [internal.rhoRequested_eq]
          exact internal.outer.certificate_scale_le_one)
      (levelSchedule.geometric.planar internal.rhoRequested.1
        hinternalPos hinternalGeometric)
      (levelSchedule.geometric.root internal.rhoRequested.1
        hinternalPos hinternalGeometric)
      (levelSchedule.geometric.localization internal.rhoRequested.1
        hinternalPos hinternalGeometric)
      (by rw [← levelSchedule.ordinary.finalLoss_eq]
          exact levelSchedule.ordinary.finalLoss_pos)
      (by simpa only [← hfinalEq] using levelSchedule.finalLoss_lt_one)
      (by rw [← levelSchedule.ordinary.finalLoss_eq,
          ← levelSchedule.outputLoss_eq]
          exact levelSchedule.finalLoss_half_lt_sigma)
      hinputNonneg hinputCeiling le_rfl le_rfl hgraphDelta hinternalGraph
      hinternalPower hgraphAnalytic hinternalProjection hCOne with ⟨tail⟩
  have hfinalScaleOne :
      pureWZ2SourceHorizontalFinalScale internal.rhoRequested.1 ≤ 1 := by
    rw [internal.rhoRequested_eq]
    exact internal.outer.final_scale_le_one
  have hlengthLower :
      Real.rpow (pureWZ2SourceHorizontalFinalScale internal.rhoRequested.1)
          (1 / 2 + levelSchedule.floorSchedule.densityLoss / 8) ≤
        Real.sqrt internal.rhoRequested.1 := by
    rw [← hfinalEq, internal.rhoRequested_eq, internal.outer.final_scale_eq]
    exact internal.outer.length_lower
  rcases tail.trapezoidFamily hfinalScaleOne hlengthLower with ⟨trapezoids⟩
  rcases trapezoids.selectResidue with ⟨residue⟩
  exact ⟨{
    neighborhoods := neighborhoods
    tail := tail
    trapezoids := trapezoids
    residue := residue
  }⟩

/-- Execute both direct-rich calls and their synchronized pullback at one
actual paper hierarchy scale. -/
theorem actualLevel_twoCallPullback
    {sourceDelta inputLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (level : Fin (schedule.mild.levelCount - 1))
    (current : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent)
    (hinputCeiling :
      inputLoss ≤
        (schedule.ordinaryPrefix.level level).level.sourceLossCeiling) :
    Nonempty (schedule.ActualTwoCallPullbackData level current) := by
  rcases schedule.actualLevel_thresholds hsourceDelta hsourceSmall level with
    ⟨_hfloor, _hdensity, hfirstDelta, _hsourceSecond, _hgraphDelta,
      hrhoSecond, _hdensityRho, _hprojectionRho, _hanalyticRho,
      hgeometricRho, _hgraphRho, hdeltaRho, hscaleLower, hscaleUpper⟩
  let levelSchedule := (schedule.ordinaryPrefix.level level).level
  let rho := wz1Corollary26Scale sourceDelta schedule.mild.levelCount
    ⟨level, by omega⟩
  have hrho : 0 < rho := by
    dsimp only [rho, wz1Corollary26Scale]
    exact Real.rpow_pos_of_pos hsourceDelta _
  have hrhoOne : rho ≤ 1 :=
    hgeometricRho.trans levelSchedule.geometric.rho0_le_one
  let rhoRequested : WZ2PaperRequestedScale sourceDelta :=
    ⟨rho, hdeltaRho, hrhoOne⟩
  have hinputFirst :
      inputLoss ≤
        (levelSchedule.ordinary.calls.firstCallSchedule capability
          ).kernel.sourceLoss :=
    hinputCeiling.trans levelSchedule.sourceLossCeiling_le_firstKernel
  have houtputEpsilon :
      levelSchedule.outputLoss ≤ schedule.mild.epsilon₂ := by
    calc
      levelSchedule.outputLoss ≤
          schedule.mild.epsilon₂ * sigma / 8192 :=
        levelSchedule.outputLoss_le_graphBudget
      _ ≤ schedule.mild.epsilon₂ := by
        have hepsilon := schedule.mild.epsilon₂_pos
        nlinarith [schedule.sigma_lt_one]
  have hfinalEpsilon :
      levelSchedule.ordinary.finalLoss ≤ schedule.mild.epsilon₂ := by
    rw [← levelSchedule.outputLoss_eq]
    exact houtputEpsilon
  have hstickyEpsilon :
      levelSchedule.ordinary.stickyLoss ≤ schedule.mild.epsilon₂ :=
    levelSchedule.ordinary.stickyLoss_le_final.trans hfinalEpsilon
  have hfirstEpsilon :
      levelSchedule.ordinary.calls.firstOutputLoss ≤ schedule.mild.epsilon₂ :=
    levelSchedule.ordinary.calls.calls.firstOutputLoss_lt_secondSource.le.trans <|
      levelSchedule.ordinary.calls.secondKernel.sourceLoss_le_half.trans <|
        (half_le_self
          levelSchedule.ordinary.calls.secondKernel.normalizationLoss_pos.le).trans <|
          levelSchedule.ordinary.calls.secondKernel.normalizationLoss_lt_output.le.trans
            hstickyEpsilon
  have hsourceOne : sourceDelta ≤ 1 := hdeltaRho.trans hrhoOne
  have hfirstLower :
      Real.rpow sourceDelta
          (1 - levelSchedule.ordinary.calls.firstOutputLoss) ≤ rho := by
    calc
      Real.rpow sourceDelta
          (1 - levelSchedule.ordinary.calls.firstOutputLoss) ≤
        Real.rpow sourceDelta (1 - schedule.mild.epsilon₂) := by
          rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
          exact Real.rpow_le_rpow_of_exponent_ge hsourceDelta hsourceOne <| by
            linarith
      _ ≤ rho := hscaleLower
  have hfirstUpper :
      rho ≤ Real.rpow sourceDelta
        levelSchedule.ordinary.calls.firstOutputLoss := by
    calc
      rho ≤ Real.rpow sourceDelta schedule.mild.epsilon₂ := hscaleUpper
      _ ≤ Real.rpow sourceDelta
          levelSchedule.ordinary.calls.firstOutputLoss := by
        rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
        exact Real.rpow_le_rpow_of_exponent_ge hsourceDelta hsourceOne
          hfirstEpsilon
  rcases (levelSchedule.ordinary.calls.firstCallSchedule capability).run
      current hinputFirst hfirstDelta rhoRequested hfirstLower hfirstUpper with
    ⟨first⟩
  have houtputHalf : levelSchedule.outputLoss ≤ 1 / 2 := by
    have hnextSigma :=
      (schedule.ordinaryPrefix.level level).nextSourceCeiling_le_sigma
    have houtputNext := levelSchedule.outputLoss_le_next_eighth
    nlinarith [schedule.sigma_lt_one]
  have hstickyHalf : levelSchedule.ordinary.stickyLoss ≤ 1 / 2 :=
    levelSchedule.ordinary.stickyLoss_le_final.trans <| by
      rw [← levelSchedule.outputLoss_eq]
      exact houtputHalf
  have hrhoSq : rho ^ 2 ≤ rho := by nlinarith
  have hrhoSqrt : rho ≤ Real.sqrt rho :=
    (Real.le_sqrt hrho.le hrho.le).2 hrhoSq
  have hsqrtOne : Real.sqrt rho ≤ 1 := Real.sqrt_le_one.mpr hrhoOne
  let sqrtRequested : WZ2PaperRequestedScale rhoRequested.1 :=
    ⟨Real.sqrt rho, by simpa only [rhoRequested] using hrhoSqrt,
      hsqrtOne⟩
  have hsqrtLower :
      Real.rpow rho (1 - levelSchedule.ordinary.stickyLoss) ≤
        sqrtRequested.1 := by
    dsimp only [sqrtRequested]
    rw [Real.sqrt_eq_rpow, Real.rpow_eq_pow]
    exact Real.rpow_le_rpow_of_exponent_ge hrho hrhoOne <| by linarith
  have hsqrtUpper :
      sqrtRequested.1 ≤
        Real.rpow rho levelSchedule.ordinary.stickyLoss := by
    dsimp only [sqrtRequested]
    rw [Real.sqrt_eq_rpow, Real.rpow_eq_pow]
    exact Real.rpow_le_rpow_of_exponent_ge hrho hrhoOne hstickyHalf
  rcases levelSchedule.ordinary.calls.run first sqrtRequested rfl
      hrhoSecond (by simpa only [rhoRequested] using hsqrtLower)
      (by simpa only [rhoRequested] using hsqrtUpper) with
    ⟨twoScale⟩
  rcases PureWZ2Node05V4RichTwoScaleCellPullbackData.nonempty twoScale rfl with
    ⟨pullback⟩
  exact ⟨{
    rhoRequested := rhoRequested
    rhoRequested_eq := rfl
    inputLossLe := hinputFirst
    sqrtRequested := sqrtRequested
    sqrtRequested_eq := rfl
    twoScale := twoScale
    pullback := pullback
  }⟩

/-- Instantiate the preselected P3 graph powers at an actual ordinary
hierarchy scale, with the same dependent two-call witness used downstream. -/
theorem actualLevel_graphPowers
    {sourceDelta inputLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (level : Fin (schedule.mild.levelCount - 1))
    {current : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale sourceDelta}
    {inputLossLe :
      inputLoss ≤
        ((((schedule.ordinaryPrefix.level level).level.ordinary.calls
          ).firstCallSchedule capability).kernel.sourceLoss)}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    (twoScale : PureWZ2Node05V4RichSecondCallData
      (schedule.ordinaryPrefix.level level).level.ordinary.calls
      current rhoRequested inputLossLe sqrtRequested)
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := wz1Corollary26Scale sourceDelta schedule.mild.levelCount
        ⟨level, by omega⟩) twoScale)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinputCeiling :
      inputLoss ≤
        (schedule.ordinaryPrefix.level level).level.sourceLossCeiling) :
    let rho := wz1Corollary26Scale sourceDelta schedule.mild.levelCount
      ⟨level, by omega⟩
    160 * Kakeya.realRpowENN sourceDelta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rhoRequested.1)
          (-(schedule.ordinaryPrefix.level level).level.normalEta) ∧
      ((32 * Kakeya.realRpowENN sourceDelta (-inputLoss) *
              Kakeya.realRpowENN sourceDelta sigma *
              Kakeya.realRpowENN rho (2 - sigma)) *
            ENNReal.ofReal rho) *
          Kakeya.realRpowENN (4 * rhoRequested.1)
            (3 / 2 + sigma / 2 +
              (schedule.ordinaryPrefix.level level).level.normalEta) ≤
        (Kakeya.realRpowENN rhoRequested.1 3 *
              Kakeya.realRpowENN (sourceDelta / rhoRequested.1)
                (sigma + 2 * twoScale.first.rich.terminalLoss)) *
            Kakeya.realRpowENN rhoRequested.1
              (3 / 2 + sigma / 2 + twoScale.second.terminalLoss) := by
  dsimp only
  rcases schedule.actualLevel_thresholds hsourceDelta hsourceSmall level with
    ⟨_hfloor, _hdensity, _hfirst, _hsecond, hgraphDelta,
      _hsecondRho, _hdensityRho, _hprojectionRho, _hanalyticRho,
      hgeometricRho, hgraphRho, _hdeltaRho, _hscaleLower, hscaleUpper⟩
  let rho := wz1Corollary26Scale sourceDelta schedule.mild.levelCount
    ⟨level, by omega⟩
  have hrho : 0 < rho := by
    dsimp only [rho, wz1Corollary26Scale]
    exact Real.rpow_pos_of_pos hsourceDelta _
  have hfourRho :
      4 * rho ≤ 1 :=
    (schedule.ordinaryPrefix.level level).level.geometric.certificate
      rho hrho hgeometricRho
  have hlocal :=
    (schedule.ordinaryPrefix.level level).level.graphThreshold.local_power
      hinputNonneg hinputCeiling current.grain.extremal.delta_pos
      hgraphDelta hrho hfourRho hscaleUpper
  have hsaturation :=
    (schedule.ordinaryPrefix.level level).level.graphThreshold
      |>.twoCall_saturation_power twoScale pullback hinputNonneg
        hinputCeiling le_rfl le_rfl
        hgraphDelta hgraphRho hscaleUpper
  constructor
  · simpa only [pullback.rhoRequested_eq] using hlocal
  · exact hsaturation

end PureWZ2C2OrdinaryGlobalSchedule

structure PureWZ2C2PostOrdinaryLossSchedule
    (capability : PureWZ2PropStickyCapability)
    (sigma outputLoss targetDelta₀ C Ctotal : ℝ) where
  ordinary : PureWZ2C2OrdinaryGlobalSchedule
    capability sigma outputLoss targetDelta₀ C Ctotal
  slabDensityLoss : ℝ := 5 * ordinary.mild.epsilon₂
  slabDensityLoss_eq : slabDensityLoss = 5 * ordinary.mild.epsilon₂
  rescalingLoss : ℝ := 6 * ordinary.mild.epsilon₂
  rescalingLoss_eq : rescalingLoss = 6 * ordinary.mild.epsilon₂
  jointDensity : PureWZ2Proposition64JointDensitySchedule
    ordinary.mild.levelCount slabDensityLoss rescalingLoss targetDelta₀
  totalLoss : ℝ := ordinary.ordinaryEndpointLoss + rescalingLoss
  totalLoss_eq : totalLoss = ordinary.ordinaryEndpointLoss + rescalingLoss
  totalLoss_le_eight_epsilon₂ :
    totalLoss ≤ 8 * ordinary.mild.epsilon₂
  totalLoss_le_totalMargin :
    totalLoss ≤ Ctotal * ordinary.mild.epsilon₂
  totalLoss_le_outputMargin :
    totalLoss ≤ (1 - C * ordinary.mild.epsilon₂) * outputLoss
  commonDelta₀ : ℝ :=
    min ordinary.commonDelta₀ jointDensity.sourceDelta₀
  commonDelta₀_eq :
    commonDelta₀ = min ordinary.commonDelta₀ jointDensity.sourceDelta₀
  commonDelta₀_pos : 0 < commonDelta₀
  commonDelta₀_le_ordinary : commonDelta₀ ≤ ordinary.commonDelta₀
  commonDelta₀_le_jointDensity :
    commonDelta₀ ≤ jointDensity.sourceDelta₀

/-- Add the paper's `5 epsilon₂` slab density and `6 epsilon₂` mild-rescaling
losses to the ordinary schedule while preserving the final output margin. -/
theorem pureWZ2C2_postOrdinaryLossSchedule
    (capability : PureWZ2PropStickyCapability)
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (houtput : 0 < outputLoss)
    (htarget : 0 < targetDelta₀)
    (hC : 0 < C)
    (hCtotal : 8 ≤ Ctotal) :
    Nonempty (PureWZ2C2PostOrdinaryLossSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal) := by
  rcases pureWZ2C2_ordinaryGlobalSchedule capability critical
      houtput htarget hC (by linarith) with ⟨ordinary⟩
  let slabDensityLoss := 5 * ordinary.mild.epsilon₂
  let rescalingLoss := 6 * ordinary.mild.epsilon₂
  have hslabDensity : 0 < slabDensityLoss := by
    dsimp only [slabDensityLoss]
    exact mul_pos (by norm_num) ordinary.mild.epsilon₂_pos
  have hlossGap : slabDensityLoss < rescalingLoss := by
    dsimp only [slabDensityLoss, rescalingLoss]
    linarith [ordinary.mild.epsilon₂_pos]
  rcases exists_pureWZ2Proposition64JointDensitySchedule
      ordinary.mild.levelCount_ge_two hslabDensity hlossGap htarget with
    ⟨jointDensity⟩
  let totalLoss := ordinary.ordinaryEndpointLoss + rescalingLoss
  have htotalEight :
      totalLoss ≤ 8 * ordinary.mild.epsilon₂ := by
    dsimp only [totalLoss, rescalingLoss]
    linarith [ordinary.ordinaryEndpointLoss_le_two_epsilon₂]
  have htotalMargin :
      totalLoss ≤ Ctotal * ordinary.mild.epsilon₂ :=
    htotalEight.trans <|
      mul_le_mul_of_nonneg_right hCtotal ordinary.mild.epsilon₂_pos.le
  have htotalOutput :
      totalLoss ≤
        (1 - C * ordinary.mild.epsilon₂) * outputLoss :=
    htotalMargin.trans ordinary.mild.total_loss_margin
  let commonDelta₀ :=
    min ordinary.commonDelta₀ jointDensity.sourceDelta₀
  exact ⟨{
    ordinary := ordinary
    slabDensityLoss := slabDensityLoss
    slabDensityLoss_eq := rfl
    rescalingLoss := rescalingLoss
    rescalingLoss_eq := rfl
    jointDensity := jointDensity
    totalLoss := totalLoss
    totalLoss_eq := rfl
    totalLoss_le_eight_epsilon₂ := htotalEight
    totalLoss_le_totalMargin := htotalMargin
    totalLoss_le_outputMargin := htotalOutput
    commonDelta₀ := commonDelta₀
    commonDelta₀_eq := rfl
    commonDelta₀_pos :=
      lt_min ordinary.commonDelta₀_pos jointDensity.sourceDelta₀_pos
    commonDelta₀_le_ordinary := min_le_left _ _
    commonDelta₀_le_jointDensity := min_le_right _ _
  }⟩

/-- The complete family-independent scalar schedule for the frozen Node-5
route. Runtime source, slab, trapezoid, and refinement witnesses are not
stored here. -/
structure PureWZ2C2ClosureSchedule
    (capability : PureWZ2PropStickyCapability)
    (sigma outputLoss targetDelta₀ C Ctotal : ℝ) where
  scalar : PureWZ2C2PostOrdinaryLossSchedule
    capability sigma outputLoss targetDelta₀ C Ctotal

theorem exists_pureWZ2C2ClosureSchedule
    (capability : PureWZ2PropStickyCapability)
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (houtput : 0 < outputLoss)
    (htarget : 0 < targetDelta₀)
    (hC : 0 < C)
    (hCtotal : 8 ≤ Ctotal) :
    Nonempty (PureWZ2C2ClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal) := by
  rcases pureWZ2C2_postOrdinaryLossSchedule capability critical houtput
      htarget hC hCtotal with ⟨scalar⟩
  exact ⟨{ scalar := scalar }⟩

end Kakeya.Assouad

end
