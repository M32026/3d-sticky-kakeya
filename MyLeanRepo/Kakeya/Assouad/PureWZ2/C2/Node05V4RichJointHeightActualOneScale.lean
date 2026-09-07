import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightClosureSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightExactCross

/-!
# Actual-level joint-height one-scale production

This module instantiates the complete joint-height P3 construction at one
actual ordinary hierarchy scale.  The graph-volume lower bound uses the
distinct-label exact cross, while the final density uses the weighted
assigned-source return.  All numerical losses and cutoffs come from the
pre-runtime global schedule.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

namespace PureWZ2C2OrdinaryGlobalSchedule

private theorem jointHeightK_nonempty
    {rho eta : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1) (hetaHalf : eta ≤ 1 / 2) :
    ∃ K : ℕ,
      Kakeya.realRpowENN rho (-1 / 2 + eta) / 2 ≤ K ∧
        (K : ENNReal) ≤ Kakeya.realRpowENN rho (-1 / 2 + eta) := by
  let X : ENNReal := Kakeya.realRpowENN rho (-1 / 2 + eta)
  have hXOne : 1 ≤ X := by
    unfold X Kakeya.realRpowENN
    exact ENNReal.one_le_ofReal.mpr
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hrho hrhoOne (by linarith))
  have hXTop : X ≠ ⊤ := by simp [X, Kakeya.realRpowENN]
  simpa only [X] using
    CommonBinRichSelection.exists_natCast_between_half X hXOne hXTop

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2OrdinaryGlobalSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal)

structure ActualJointHeightKData
    {sourceDelta inputLoss : ℝ}
    (level : Fin (schedule.mild.levelCount - 1))
    (current : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent) where
  internal : schedule.ActualInternalTwoCallPullbackData level current
  K : ℕ
  K_lower :
    Kakeya.realRpowENN internal.rhoRequested.1
        (-1 / 2 + (schedule.ordinaryPrefix.level level).level.normalEta) / 2 ≤ K
  K_capacity :
    (K : ENNReal) *
        PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
          sigma inputLoss sourceDelta internal.rhoRequested.1 ≤
      pureWZ2Node05V4RichJointCommonBinThreshold internal.pullback

theorem actualLevel_jointHeightK
    {sourceDelta inputLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (level : Fin (schedule.mild.levelCount - 1))
    (current : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinputCeiling :
      inputLoss ≤
        (schedule.ordinaryPrefix.level level).level.sourceLossCeiling) :
    Nonempty (schedule.ActualJointHeightKData level current) := by
  rcases schedule.actualLevel_internalTwoCallPullback hsourceDelta hsourceSmall
      level current hinputCeiling with ⟨internal⟩
  let levelSchedule := (schedule.ordinaryPrefix.level level).level
  let rho := internal.rhoRequested.1
  rcases schedule.actualLevel_capacityThresholds hsourceDelta hsourceSmall level
      with ⟨hdeltaCapacity, htargetCapacity⟩
  rcases schedule.actualLevel_thresholds hsourceDelta hsourceSmall level with
    ⟨_hfloor, _hdensity, _hfirst, _hsecond, _hgraphDelta,
      _htargetSecond, _htargetDensity, _htargetProjection, _htargetAnalytic,
      _htargetGeometric, _htargetGraph, _hdeltaTarget, _htargetLower,
      htargetPower⟩
  have hrho : 0 < rho := by
    simpa only [rho, internal.rhoRequested_eq] using internal.outer.internal_pos
  have htargetPos : 0 < internal.targetRho := by
    rw [internal.targetRho_eq]
    exact Real.rpow_pos_of_pos hsourceDelta _
  have hrhoTarget : rho ≤ internal.targetRho := by
    dsimp only [rho]
    rw [internal.rhoRequested_eq]
    unfold pureWZ2SourceHorizontalInternalScale
    exact div_le_self htargetPos.le (by norm_num)
  have hrhoCapacity : rho ≤ levelSchedule.capacityThreshold.rho₀ :=
    hrhoTarget.trans <| by
      simpa only [levelSchedule, internal.targetRho_eq] using htargetCapacity
  have hrhoPower : rho ≤ Real.rpow sourceDelta schedule.mild.epsilon₂ :=
    hrhoTarget.trans <| by
      simpa only [internal.targetRho_eq] using htargetPower
  have hgraphOne : 256 * rho ≤ 1 := by
    simpa only [rho, internal.rhoRequested_eq] using
      internal.outer.graph_scale_le_one
  have hrhoSmall : rho ≤ 1 / 12 := by nlinarith
  have hrhoOne : rho ≤ 1 := by
    dsimp only [rho]
    exact internal.rhoRequested.property.2
  have hetaHalf : levelSchedule.normalEta ≤ 1 / 2 := by
    nlinarith [levelSchedule.normalEta_sigma, schedule.sigma_lt_one]
  rcases jointHeightK_nonempty hrho hrhoOne hetaHalf with
    ⟨K, hKLower, hKUpper⟩
  have hcapacity := internal.pullback.sourcePopular_commonBin_capacity
    levelSchedule.capacityThreshold rfl hinputNonneg hinputCeiling
    hdeltaCapacity hrhoCapacity hgraphOne hrhoPower hrhoSmall
  have hKcapacity :
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss sourceDelta rho ≤
        pureWZ2Node05V4RichJointCommonBinThreshold internal.pullback := by
    calc
      _ ≤ Kakeya.realRpowENN rho (-1 / 2 + levelSchedule.normalEta) *
            PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
              sigma inputLoss sourceDelta rho := by gcongr
      _ ≤ _ := hcapacity
  exact ⟨{
    internal := internal
    K := K
    K_lower := by simpa only [rho, levelSchedule] using hKLower
    K_capacity := by simpa only [rho] using hKcapacity
  }⟩

structure ActualJointHeightPreparedFamilyData
    {sourceDelta inputLoss : ℝ}
    (level : Fin (schedule.mild.levelCount - 1))
    (current : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent)
    (hbridge : PureWZ2PaperADBridgeStatement) where
  kData : schedule.ActualJointHeightKData level current
  prepared : ∀ heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs kData.internal.pullback},
    PureWZ2Node05V4RichJointPreparedData
      (eta := (schedule.ordinaryPrefix.level level).level.normalEta)
      kData.internal.pullback heightIndex
      (pureWZ2Node05V4RichJointOccupiedBinBound
        sigma inputLoss sourceDelta kData.internal.rhoRequested.1)
      (pureWZ2Node05V4RichJointCommonBinThreshold kData.internal.pullback)
      hbridge

theorem actualLevel_jointHeightPreparedFamily
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
    Nonempty (schedule.ActualJointHeightPreparedFamilyData
      level current hbridge) := by
  rcases actualLevel_jointHeightK schedule hsourceDelta hsourceSmall level
      current hinputNonneg hinputCeiling with ⟨kData⟩
  let levelSchedule := (schedule.ordinaryPrefix.level level).level
  let internal := kData.internal
  let rho := internal.rhoRequested.1
  let B₀ := pureWZ2Node05V4RichJointOccupiedBinBound
    sigma inputLoss sourceDelta rho
  let threshold := pureWZ2Node05V4RichJointCommonBinThreshold internal.pullback
  rcases schedule.actualLevel_thresholds hsourceDelta hsourceSmall level with
    ⟨_hfloor, _hdensity, _hfirst, _hsecond, hdeltaGraph,
      _htargetSecond, _htargetDensity, _htargetProjection, _htargetAnalytic,
      htargetGeometric, htargetGraph, _hdeltaTarget, _htargetLower,
      htargetPower⟩
  have hrho : 0 < rho := by
    simpa only [rho, internal.rhoRequested_eq] using internal.outer.internal_pos
  have htargetPos : 0 < internal.targetRho := by
    rw [internal.targetRho_eq]
    exact Real.rpow_pos_of_pos hsourceDelta _
  have hrhoTarget : rho ≤ internal.targetRho := by
    rw [show rho = pureWZ2SourceHorizontalInternalScale internal.targetRho by
      exact internal.rhoRequested_eq]
    unfold pureWZ2SourceHorizontalInternalScale
    exact div_le_self htargetPos.le (by norm_num)
  have hrhoGeometric : rho ≤ levelSchedule.geometric.rho0 :=
    hrhoTarget.trans <| by
      simpa only [levelSchedule, internal.targetRho_eq] using htargetGeometric
  have hrhoGraph : rho ≤ levelSchedule.graphThreshold.rho₀ :=
    hrhoTarget.trans <| by
      simpa only [levelSchedule, internal.targetRho_eq] using htargetGraph
  have hrhoPower : rho ≤ Real.rpow sourceDelta schedule.mild.epsilon₂ :=
    hrhoTarget.trans <| by
      simpa only [internal.targetRho_eq] using htargetPower
  have hgraphOne : 256 * rho ≤ 1 := by
    simpa only [rho, internal.rhoRequested_eq] using
      internal.outer.graph_scale_le_one
  have hheightAbsorb :
      256 * rho + 2 * Real.sqrt rho ≤ 16 * Real.sqrt rho :=
    levelSchedule.geometric.heightAbsorb rho hrho hrhoGeometric
  have hcertificateOne : 4 * internal.rhoRequested.1 ≤ 1 := by
    rw [internal.rhoRequested_eq]
    exact internal.outer.certificate_scale_le_one
  have hPlanarSmall :
      32 * Real.rpow (4 * internal.rhoRequested.1)
          levelSchedule.normalEta ≤ 1 :=
    levelSchedule.geometric.planar internal.rhoRequested.1 hrho hrhoGeometric
  have hrootSmall20 :
      20 * Real.sqrt (4 * internal.rhoRequested.1) ≤ 1 :=
    levelSchedule.geometric.root internal.rhoRequested.1 hrho hrhoGeometric
  have hlocalization :
      Real.rpow (4 * internal.rhoRequested.1)
          (1 - 4 * levelSchedule.normalEta / sigma) ≤
        Real.sqrt (4 * internal.rhoRequested.1) / 14 :=
    levelSchedule.geometric.localization internal.rhoRequested.1
      hrho hrhoGeometric
  have hsourcePower := levelSchedule.graphThreshold.twoCall_saturation_power
    internal.twoScale internal.pullback hinputNonneg hinputCeiling le_rfl le_rfl
    hdeltaGraph hrhoGraph hrhoPower
  have hlocalPower := levelSchedule.graphThreshold.local_power
    hinputNonneg hinputCeiling hsourceDelta hdeltaGraph hrho
      (by nlinarith [hgraphOne]) hrhoPower
  have hetaSigma : 4 * levelSchedule.normalEta < sigma :=
    lt_of_lt_of_le (by nlinarith [levelSchedule.normalEta_pos])
      levelSchedule.normalEta_sigma.le
  have hprepared : ∀ heightIndex, Nonempty
      (PureWZ2Node05V4RichJointPreparedData
        (eta := levelSchedule.normalEta) internal.pullback heightIndex
          B₀ threshold hbridge) := by
    intro heightIndex
    exact internal.pullback.jointHeightPrepared heightIndex B₀ threshold le_rfl
      (fun volumePopular => by
        simpa only [B₀, threshold] using
          internal.pullback.jointCommonBinThreshold_budget
            hgraphOne heightIndex volumePopular)
      hbridge hgraphOne hheightAbsorb schedule.sigma_pos schedule.sigma_lt_one
      levelSchedule.normalEta_pos hetaSigma hcertificateOne hsourcePower
      hlocalPower hPlanarSmall hrootSmall20 hlocalization
  exact ⟨{
    kData := kData
    prepared := fun heightIndex => Classical.choice (hprepared heightIndex)
  }⟩

/-- Produce the complete paper one-scale output at an actual ordinary
hierarchy level.  No graph, density, carrier, cell-mass, or scale-selection
premise remains at the call site. -/
theorem actualLevel_jointHeightOneScale
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
    Nonempty (PureWZ2LocallyLinearOneScaleData
      current.grain
      (schedule.ordinaryPrefix.level level).level.grainLoss
      (wz1Corollary26Scale sourceDelta schedule.mild.levelCount
        ⟨level, by omega⟩)) := by
  let levelSchedule := (schedule.ordinaryPrefix.level level).level
  rcases actualLevel_jointHeightPreparedFamily schedule hsourceDelta hsourceSmall
      level current hinputNonneg hinputCeiling hbridge with ⟨preparedFamily⟩
  let kData := preparedFamily.kData
  let internal := kData.internal
  let rho := internal.rhoRequested.1
  let B₀ := pureWZ2Node05V4RichJointOccupiedBinBound
    sigma inputLoss sourceDelta rho
  let threshold := pureWZ2Node05V4RichJointCommonBinThreshold internal.pullback
  rcases schedule.actualLevel_thresholds hsourceDelta hsourceSmall level with
    ⟨hdeltaFloor, hdeltaDensity, _hfirst, _hsecond, hdeltaGraph,
      _htargetSecond, htargetDensity, htargetProjection, htargetAnalytic,
      htargetGeometric, htargetGraph, _hdeltaTarget, _htargetLower,
      htargetPower⟩
  rcases schedule.actualLevel_capacityThresholds hsourceDelta hsourceSmall level
      with ⟨hdeltaCapacity, htargetCapacity⟩
  have hrho : 0 < rho := by
    simpa only [rho, internal.rhoRequested_eq] using internal.outer.internal_pos
  have htargetPos : 0 < internal.targetRho := by
    rw [internal.targetRho_eq]
    exact Real.rpow_pos_of_pos hsourceDelta _
  have hrhoTarget : rho ≤ internal.targetRho := by
    dsimp only [rho]
    rw [internal.rhoRequested_eq]
    unfold pureWZ2SourceHorizontalInternalScale
    exact div_le_self htargetPos.le (by norm_num)
  have hrhoDensity : rho ≤ levelSchedule.ordinary.densityThreshold.rho₀ :=
    hrhoTarget.trans <| by
      simpa only [levelSchedule, internal.targetRho_eq] using htargetDensity
  have hrhoProjection : rho ≤ levelSchedule.projection.rho₀ :=
    hrhoTarget.trans <| by
      simpa only [levelSchedule, internal.targetRho_eq] using htargetProjection
  have hrhoAnalyticTarget : rho ≤ levelSchedule.analytic.rho0 :=
    hrhoTarget.trans <| by
      simpa only [levelSchedule, internal.targetRho_eq] using htargetAnalytic
  have hrhoGeometric : rho ≤ levelSchedule.geometric.rho0 :=
    hrhoTarget.trans <| by
      simpa only [levelSchedule, internal.targetRho_eq] using htargetGeometric
  have hrhoGraph : rho ≤ levelSchedule.graphThreshold.rho₀ :=
    hrhoTarget.trans <| by
      simpa only [levelSchedule, internal.targetRho_eq] using htargetGraph
  have hrhoCapacity : rho ≤ levelSchedule.capacityThreshold.rho₀ :=
    hrhoTarget.trans <| by
      simpa only [levelSchedule, internal.targetRho_eq] using htargetCapacity
  have hrhoPower : rho ≤ Real.rpow sourceDelta schedule.mild.epsilon₂ :=
    hrhoTarget.trans <| by
      simpa only [internal.targetRho_eq] using htargetPower
  have hgraphOne : 256 * rho ≤ 1 := by
    simpa only [rho, internal.rhoRequested_eq] using
      internal.outer.graph_scale_le_one
  have hrhoSmall : rho ≤ 1 / 12 := by nlinarith
  have hsourcePower := levelSchedule.graphThreshold.twoCall_saturation_power
    internal.twoScale internal.pullback hinputNonneg hinputCeiling le_rfl le_rfl
    hdeltaGraph hrhoGraph hrhoPower
  let K := kData.K
  have hKLower :
      Kakeya.realRpowENN rho (-1 / 2 + levelSchedule.normalEta) / 2 ≤ K := by
    simpa only [rho, levelSchedule, internal] using kData.K_lower
  have hKcapacity :
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss sourceDelta rho ≤ threshold := by
    simpa only [K, rho, threshold, internal] using kData.K_capacity
  let prepared := preparedFamily.prepared
  have hgraphAnalytic : 256 * rho ≤ levelSchedule.analytic.rho0 := by
    have hscaled : 256 * rho ≤ internal.targetRho := by
      rw [show rho = pureWZ2SourceHorizontalInternalScale internal.targetRho by
        exact internal.rhoRequested_eq]
      unfold pureWZ2SourceHorizontalInternalScale
      nlinarith [htargetPos]
    exact hscaled.trans <| by
      simpa only [levelSchedule, internal.targetRho_eq] using htargetAnalytic
  have hCOne :
      (1 : ENNReal) ≤ 160 * Kakeya.realRpowENN sourceDelta (-inputLoss) := by
    have hpower :
        (1 : ENNReal) ≤ Kakeya.realRpowENN sourceDelta (-inputLoss) := by
      rw [Kakeya.realRpowENN, ENNReal.one_le_ofReal]
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hsourceDelta
        current.grain.extremal.delta_le_one (by linarith)
    calc
      (1 : ENNReal) ≤ 160 := by norm_num
      _ = 160 * 1 := by ring
      _ ≤ 160 * Kakeya.realRpowENN sourceDelta (-inputLoss) := by gcongr
  have htheorem52 : ∀ heightIndex, Nonempty
      (PureWZ2Node05V4RichJointTheorem52Data
        (prepared heightIndex) levelSchedule.projection) := by
    intro heightIndex
    let data := prepared heightIndex
    have hbins := data.volumePopular.bins_le_heightBinBound hgraphOne
    have hgraphBase := levelSchedule.capacityThreshold.joint_graph_power
      hrho hrhoCapacity
    have hgraphK :
        (80 * (data.volumePopular.popular.bins : ENNReal) * 512 * 45) *
            Kakeya.realRpowENN data.separated.graphScale
              (1 + sigma / 2 + levelSchedule.analytic.budget.volumeLoss) ≤
          (K : ENNReal) *
            Kakeya.realRpowENN (4 * rho)
              (3 / 2 + sigma / 2 + levelSchedule.normalEta) := by
      calc
        _ = (80 * 512 * 45 : ENNReal) *
              (data.volumePopular.popular.bins : ENNReal) *
              Kakeya.realRpowENN data.separated.graphScale
                (1 + sigma / 2 +
                  levelSchedule.analytic.budget.volumeLoss) := by ring
        _ ≤ (80 * 512 * 45 : ENNReal) *
              pureWZ2Node05V4RichJointHeightBinBound rho *
              Kakeya.realRpowENN (256 * rho)
                (1 + sigma / 2 + levelSchedule.analytic.budget.volumeLoss) := by
          rw [data.graphScale_eq]
          gcongr
        _ ≤ (Kakeya.realRpowENN rho
              (-1 / 2 + levelSchedule.normalEta) / 2) *
              Kakeya.realRpowENN (4 * rho)
              (3 / 2 + sigma / 2 + levelSchedule.normalEta) := hgraphBase
        _ ≤ (K : ENNReal) * Kakeya.realRpowENN (4 * rho)
              (3 / 2 + sigma / 2 + levelSchedule.normalEta) := by gcongr
    have hsaturationActual :
        ((32 * Kakeya.realRpowENN sourceDelta (-inputLoss) *
                Kakeya.realRpowENN sourceDelta sigma *
                Kakeya.realRpowENN rho (2 - sigma)) *
              ENNReal.ofReal rho) *
            Kakeya.realRpowENN (4 * rho)
              (3 / 2 + sigma / 2 + levelSchedule.normalEta) ≤
          internal.pullback.firstPostBalanced.cellMass *
            internal.twoScale.secondBalancedCover.cellMass := by
      have hsourcePower' :
          ((32 * Kakeya.realRpowENN sourceDelta (-inputLoss) *
                  Kakeya.realRpowENN sourceDelta sigma *
                  Kakeya.realRpowENN rho (2 - sigma)) *
                ENNReal.ofReal rho) *
              Kakeya.realRpowENN (4 * rho)
                (3 / 2 + sigma / 2 + levelSchedule.normalEta) ≤
            (Kakeya.realRpowENN rho 3 *
                  Kakeya.realRpowENN (sourceDelta / rho)
                    (sigma + 2 * internal.twoScale.first.rich.terminalLoss)) *
                Kakeya.realRpowENN rho
                  (3 / 2 + sigma / 2 +
                    internal.twoScale.second.terminalLoss) := by
        simpa only [rho, internal.pullback.rhoRequested_eq] using hsourcePower
      apply hsourcePower'.trans
      apply mul_le_mul
      · rw [internal.pullback.firstPost_cellMass_eq]
        simpa only [rho, internal.pullback.rhoRequested_eq] using
          internal.twoScale.first_cellMass_power_lower
      · simpa only [rho, internal.pullback.rhoRequested_eq] using
          internal.twoScale.second_cellMass_rho_power_lower
      · positivity
      · positivity
    have hgraphVolume :
        Kakeya.realRpowENN data.separated.graphScale
            (1 + sigma / 2 + levelSchedule.analytic.budget.volumeLoss) ≤
          volume data.separated.graphShading.union :=
      data.separated.graph_volume_lower_of_jointExactCross K hKcapacity
        levelSchedule.normalEta levelSchedule.analytic.budget.volumeLoss
        hgraphK hsaturationActual
    have hconstant := levelSchedule.graphThreshold.constant_power
      hinputNonneg hinputCeiling hsourceDelta hdeltaGraph hrho hgraphOne hrhoPower
    have hsourceCost := levelSchedule.graphThreshold.source_cost hrho hrhoGraph
    rcases data.finite.theorem52OfThresholds levelSchedule.projection
        levelSchedule.analytic schedule.sigma_pos schedule.sigma_lt_one
        (by simpa only [levelSchedule.outputLoss_eq,
            levelSchedule.ordinary.finalLoss_eq] using
          levelSchedule.outputLoss_pos)
        (by simpa only [levelSchedule.outputLoss_eq,
            levelSchedule.ordinary.finalLoss_eq] using
          levelSchedule.finalLoss_lt_one)
        (by simpa only [levelSchedule.outputLoss_eq,
            levelSchedule.ordinary.finalLoss_eq] using
          levelSchedule.finalLoss_half_lt_sigma)
        levelSchedule.normalEta_pos hCOne
        (by simpa only [data.graphScale_eq] using hconstant)
        hgraphVolume
        (by simpa only [internal.pullback.rhoRequested_eq, data.graphScale_eq]
          using hsourceCost)
        (by simpa only [data.graphScale_eq] using hgraphAnalytic)
        hrhoProjection with ⟨output⟩
    rcases data.finite.exactHeightAssignment output with
      ⟨assignment, hassignment⟩
    rcases data.finite.assignedSourceMass output assignment with ⟨sourceMass⟩
    exact ⟨{
      output := output
      assignment := assignment
      assignment_exact := hassignment
      sourceMass := sourceMass
    }⟩
  let theorem52 := fun heightIndex => Classical.choice (htheorem52 heightIndex)
  have hfamily : Nonempty (PureWZ2Node05V4RichJointBlockFamily
      (eta := levelSchedule.normalEta) internal.pullback B₀ threshold hbridge
        levelSchedule.projection) := by
    apply internal.pullback.jointBlockFamily prepared theorem52
    · intro heightIndex
      calc
        5 * (prepared heightIndex).separated.graphScale =
            pureWZ2SourceHorizontalFinalScale rho := by
          rw [(prepared heightIndex).graphScale_eq]
          unfold pureWZ2SourceHorizontalFinalScale
          ring
        _ = internal.targetRho := by
          simpa only [rho] using internal.final_scale_eq
        _ ≤ 1 := by
          rw [← internal.final_scale_eq]
          rw [internal.rhoRequested_eq]
          exact internal.outer.final_scale_le_one
    · intro heightIndex
      have hfinalEq : levelSchedule.outputLoss =
          levelSchedule.floorSchedule.densityLoss / 8 :=
        levelSchedule.outputLoss_eq.trans
          levelSchedule.ordinary.finalLoss_eq
      rw [← hfinalEq, (prepared heightIndex).graphScale_eq]
      have hscale : 5 * (256 * rho) = internal.targetRho := by
        rw [← internal.final_scale_eq]
        unfold pureWZ2SourceHorizontalFinalScale
        ring
      rw [hscale]
      have hlower :
          Real.rpow internal.targetRho
              (1 / 2 + levelSchedule.outputLoss) ≤
            Real.sqrt rho := by
        simpa only [levelSchedule, rho, internal.rhoRequested_eq] using
          internal.outer.length_lower
      exact hlower.trans (le_add_of_nonneg_right (by positivity))
  rcases hfamily with ⟨family⟩
  rcases family.selectBlockResidue with ⟨residue⟩
  rcases residue.aggregateShading with ⟨aggregated⟩
  rcases residue.geometry aggregated with ⟨geometry⟩
  have hinputDensity : inputLoss ≤ levelSchedule.floorSchedule.densityLoss :=
    hinputCeiling.trans <| levelSchedule.sourceLossCeiling_le_output.trans <| by
      rw [levelSchedule.outputLoss_eq, levelSchedule.ordinary.finalLoss_eq]
      exact div_le_self levelSchedule.floorSchedule.densityLoss_pos.le
        (by norm_num)
  have htraceSource :
      current.ordinaryLoss ≤ levelSchedule.floorSchedule.traceSourceCeiling :=
    current.reentry.sourceLoss_le_half.trans <|
      (div_le_self current.reentry.normalizationLoss_pos.le
        (by norm_num)).trans <|
          hinputCeiling.trans levelSchedule.sourceLossCeiling_le_finalTrace
  have hscaleLower :
      Real.rpow sourceDelta
          (1 - levelSchedule.ordinary.calls.firstOutputLoss) ≤ rho := by
    simpa only [rho, internal.rhoRequested_eq] using internal.outer.sticky_lower
  have hfinalRequested :
      levelSchedule.floorSchedule.densityLoss / 8 ≤
        levelSchedule.grainLoss := by
    calc
      levelSchedule.floorSchedule.densityLoss / 8 =
          levelSchedule.outputLoss :=
        (levelSchedule.outputLoss_eq.trans
          levelSchedule.ordinary.finalLoss_eq).symm
      _ ≤ levelSchedule.grainLoss := levelSchedule.outputLoss_le_grain
  have hinputSource :
      inputLoss ≤ levelSchedule.ordinary.sourceLossCeiling := by
    rw [← levelSchedule.sourceLossCeiling_eq]
    exact hinputCeiling
  have honeScale := aggregated.scheduledOneScale
    (scaleLoss := levelSchedule.ordinary.calls.firstOutputLoss)
    (structuralBudget :=
      levelSchedule.transition.finalStructuralBudget)
    (requestedLoss := levelSchedule.grainLoss) geometry
    levelSchedule.floorSchedule levelSchedule.ordinary.densityThreshold
    levelSchedule.ordinary.finalLoss_eq hfinalRequested
    hinputSource hinputDensity htraceSource
    hdeltaFloor hdeltaDensity (by simpa only [rho] using hrhoDensity)
    (by simpa only [rho, internal.rhoRequested_eq] using
      internal.outer.delta_le_internal)
    hscaleLower hgraphOne hrhoSmall
  have hpublicScale : geometry.scale =
      wz1Corollary26Scale sourceDelta schedule.mild.levelCount
        ⟨level, by omega⟩ := by
    rw [geometry.scale_eq, internal.rhoRequested_eq, internal.targetRho_eq]
    unfold pureWZ2SourceHorizontalInternalScale
    ring
  simpa only [hpublicScale] using honeScale

/-- Consume the actual P3 one-scale output with the preselected transition
scalar receipt.  The resulting next source and refreshed re-entry are the two
projections of one dependent step. -/
theorem actualLevel_jointHeightOutput
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
    Nonempty (PureWZ2ReentrantOneScaleOutput current
      (schedule.ordinaryPrefix.level level).level.transition.transitionLoss
      (wz1Corollary26Scale sourceDelta schedule.mild.levelCount
        ⟨level, by omega⟩)) := by
  let levelSchedule := (schedule.ordinaryPrefix.level level).level
  rcases schedule.actualLevel_jointHeightOneScale hsourceDelta hsourceSmall
      level current hinputNonneg hinputCeiling hbridge with ⟨oneScale⟩
  have hdeltaScalar :
      sourceDelta ≤ levelSchedule.transition.scalarClosure.delta₀ := by
    simpa only [levelSchedule] using
      schedule.actualLevel_transitionScalarThreshold hsourceSmall level
  have hinputScalar :
      inputLoss ≤ levelSchedule.transition.scalarClosure.sourceLossCeiling :=
    hinputCeiling.trans levelSchedule.sourceLossCeiling_le_scalar
  let scalar := levelSchedule.transition.scalarClosure.runtime inputLoss
    current.reentry.normalizationLoss_pos hinputScalar sourceDelta
    hsourceDelta hdeltaScalar current
  have hinputGrain : inputLoss ≤ levelSchedule.grainLoss := by
    exact hinputScalar.trans_eq <| by
      rw [levelSchedule.grainLoss_eq,
        levelSchedule.transition.grainLoss_eq,
        levelSchedule.transition.scalarClosure.sourceLossCeiling_eq]
  have hgrainDensity :
      levelSchedule.grainLoss ≤
        levelSchedule.transition.traceSchedule.densityLoss := by
    rw [levelSchedule.grainLoss_eq, levelSchedule.transition.grainLoss_eq]
    exact scalar.grainLoss_le_density
  have hinputDensityAbsorption :
      Kakeya.realRpowENN sourceDelta
          levelSchedule.transition.scalarClosure.inputEta ≤
        (100 : ENNReal)⁻¹ * current.reentry.geometry.ordinaryDensity *
          Kakeya.realRpowENN sourceDelta levelSchedule.grainLoss := by
    simpa only [levelSchedule.grainLoss_eq,
      levelSchedule.transition.grainLoss_eq] using
        scalar.inputDensityAbsorption
  have htopLevelAbsorption :
      ((Kakeya.realRpowENN sourceDelta
          levelSchedule.transition.scalarClosure.outputEta)⁻¹ * 1) *
          Kakeya.realRpowENN sourceDelta (-levelSchedule.grainLoss) ≤
        Kakeya.realRpowENN sourceDelta
          (-levelSchedule.transition.transitionLoss) := by
    simpa only [levelSchedule.grainLoss_eq,
      levelSchedule.transition.grainLoss_eq] using
        scalar.topLevelAbsorption
  rcases exists_pureWZ2ReentrantOneScaleStep_of_traceSchedule
      oneScale hinputGrain levelSchedule.transition.traceSchedule
      scalar.delta_le_schedule
      levelSchedule.transition.scalarClosure.inputEta
      (Kakeya.realRpowENN sourceDelta
        levelSchedule.transition.scalarClosure.inputEta)
      scalar.densitySeparation hinputDensityAbsorption
      scalar.croppedMassAbsorption
      levelSchedule.transition.scalarClosure.sourceLossCeiling
      scalar.input_loss_le_cwa scalar.cwa_epsilon_pos
      scalar.cwaRestrictionAbsorption scalar.cwaCardinalityAbsorption
      hgrainDensity scalar.densityAbsorption htopLevelAbsorption
      scalar.densityLoss_le_half scalar.outputEta_le_structural with ⟨step⟩
  exact ⟨{
    grainLoss := levelSchedule.grainLoss
    outputEta := levelSchedule.transition.scalarClosure.outputEta
    croppedMassFraction := Kakeya.realRpowENN sourceDelta
      levelSchedule.transition.scalarClosure.inputEta
    step := step
  }⟩

end PureWZ2C2OrdinaryGlobalSchedule

end Kakeya.Assouad

end
