import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSaturatedTheorem52Provenance
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalUniformBudget

/-!
# Family-free analytic bounds for the saturated Node-5 graph

The finite graph is built from a subset of the universal radius-two spatial
grid.  Its two dyadic regularizations therefore have a universal quadratic
logarithmic cost, independently of the auxiliary saturation family.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The height-popularity and y-residue costs of any anchored finite graph are
bounded by the universal quadratic logarithm of its graph scale. -/
theorem PureWZ2AnchoredFiniteGraphData.extraCost_le_quadraticLog
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C prep.windowed.global.cells}
    (data : PureWZ2AnchoredFiniteGraphData prep localBins) :
    (data.graph.residue.extraCost : ℝ) ≤
      920 * (Real.log (1 / rho) + 1) ^ 2 := by
  have hlog := wz1Lemma23BoundedCells_log_bound
    input.rho_pos input.rho_le_one
  have hcellsSubset : prep.windowed.global.cells ⊆
      wz1Lemma23BoundedCells rho input.rho_pos := by
    classical
    exact prep.windowed.global.cells_active.trans (Finset.filter_subset _ _)
  have hcard : prep.windowed.global.cells.card ≤
      (wz1Lemma23BoundedCells rho input.rho_pos).card :=
    Finset.card_le_card hcellsSubset
  have hrawCard : data.rawResidue.cells.card ≤
      (wz1Lemma23BoundedCells rho input.rho_pos).card :=
    (Finset.card_le_card data.rawResidue.cells_subset).trans hcard
  have hrawNonempty : data.rawResidue.cells.Nonempty := by
    rw [data.raw_residue_eq]
    exact data.popularSource.cells_nonempty
  have hboundedNonempty :
      (wz1Lemma23BoundedCells rho input.rho_pos).Nonempty :=
    hrawNonempty.mono (data.rawResidue.cells_subset.trans hcellsSubset)
  have hrawLogNat : Nat.log 2 data.rawResidue.cells.card + 1 ≤
      Nat.log 2 (wz1Lemma23BoundedCells rho input.rho_pos).card + 1 :=
    Nat.add_le_add_right (Nat.log_mono_right hrawCard) 1
  have hheightCard :
      (wz1Lemma23BoundedHeightIndices rho input.rho_pos).card ≤
        (wz1Lemma23BoundedCells rho input.rho_pos).card :=
    Finset.card_image_le
  have hbinsArg :
      2 * (wz1Lemma23BoundedHeightIndices rho input.rho_pos).card ≤
        4 * (wz1Lemma23BoundedCells rho input.rho_pos).card := by
    have hcellsPos : 0 <
        (wz1Lemma23BoundedCells rho input.rho_pos).card :=
      hboundedNonempty.card_pos
    omega
  have hbinsLog :
      Nat.log 2
          (2 * (wz1Lemma23BoundedHeightIndices rho input.rho_pos).card) ≤
        Nat.log 2
          (4 * (wz1Lemma23BoundedCells rho input.rho_pos).card) :=
    Nat.log_mono_right hbinsArg
  have hcellsNe :
      (wz1Lemma23BoundedCells rho input.rho_pos).card ≠ 0 :=
    hboundedNonempty.card_ne_zero
  have hfourEq :
      4 * (wz1Lemma23BoundedCells rho input.rho_pos).card =
        (wz1Lemma23BoundedCells rho input.rho_pos).card * 2 * 2 := by
    ring
  have hbinsNat : data.heightPopular.bins ≤
      Nat.log 2 (wz1Lemma23BoundedCells rho input.rho_pos).card + 3 := by
    rw [data.heightPopular.bins_eq]
    calc
      Nat.log 2
          (2 * (wz1Lemma23BoundedHeightIndices rho input.rho_pos).card) + 1 ≤
        Nat.log 2
          (4 * (wz1Lemma23BoundedCells rho input.rho_pos).card) + 1 := by
          omega
      _ = Nat.log 2
          (wz1Lemma23BoundedCells rho input.rho_pos).card + 3 := by
        rw [hfourEq]
        calc
          Nat.log 2
              ((wz1Lemma23BoundedCells rho input.rho_pos).card * 2 * 2) + 1 =
            Nat.log 2
              ((wz1Lemma23BoundedCells rho input.rho_pos).card * 2) +
                1 + 1 := by
              rw [Nat.log_mul_base (by omega)
                (Nat.mul_ne_zero hcellsNe (by omega))]
          _ = Nat.log 2
              (wz1Lemma23BoundedCells rho input.rho_pos).card +
                1 + 1 + 1 := by
              rw [Nat.log_mul_base (by omega) hcellsNe]
          _ = _ := by omega
  let L : ℝ := Real.log (1 / rho) + 1
  have hLone : 1 ≤ L := by
    dsimp only [L]
    have hlogNonneg : 0 ≤ Real.log (1 / rho) := by
      apply Real.log_nonneg
      exact one_le_one_div input.rho_pos input.rho_le_one
    linarith
  have hrawLogReal :
      (Nat.log 2 data.rawResidue.cells.card + 1 : ℝ) ≤ 20 * L := by
    have hcast :
        (Nat.log 2 data.rawResidue.cells.card + 1 : ℝ) ≤
          (Nat.log 2 (wz1Lemma23BoundedCells rho input.rho_pos).card +
            1 : ℕ) := by
      exact_mod_cast hrawLogNat
    exact hcast.trans (by simpa [L] using hlog)
  have hbinsReal : (data.heightPopular.bins : ℝ) ≤ 23 * L := by
    have hnat : (data.heightPopular.bins : ℝ) ≤
        (Nat.log 2 (wz1Lemma23BoundedCells rho input.rho_pos).card +
          3 : ℕ) := by
      exact_mod_cast hbinsNat
    calc
      (data.heightPopular.bins : ℝ) ≤
          (Nat.log 2 (wz1Lemma23BoundedCells rho input.rho_pos).card +
            3 : ℕ) := hnat
      _ ≤ 20 * L + 2 := by
        norm_num only [Nat.cast_add, Nat.cast_ofNat]
        linarith [hlog]
      _ ≤ 23 * L := by nlinarith
  have hrawExtra : data.rawResidue.extraCost =
      2 * data.heightPopular.bins := by
    rw [data.raw_residue_eq]
    exact data.popularSource.extraCost_eq
  have hextra : data.graph.residue.extraCost =
      2 * data.heightPopular.bins *
        (Nat.log 2 data.rawResidue.cells.card + 1) := by
    rw [data.graph_residue_eq, data.popularResidue.extraCost_eq,
      hrawExtra, data.popularResidue.logarithmicCost_eq]
  rw [hextra]
  push_cast
  nlinarith [mul_le_mul hbinsReal hrawLogReal (by positivity) (by positivity)]

/-- Specialize the pre-runtime source-horizontal logarithmic cutoff to the
saturated finite graph. -/
theorem PureWZ2SourceHorizontalAnalyticThreshold.extra_saturatedFiniteGraph
    {theoremEta sigma inputLoss delta rho stickyLoss eta : ℝ}
    (analytic : PureWZ2SourceHorizontalAnalyticThreshold theoremEta)
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : neighborhood.saturatedGraphScale ≤ 1}
    (data : PureWZ2Node05V4RichSaturatedFiniteGraphData
      (eta := eta) neighborhood hbridge hgraphOne)
    (hrho : 0 < rho) (hrhoSmall : rho ≤ analytic.rho0) :
    (data.finiteGraph.graph.residue.extraCost : ℝ) ≤
      Real.rpow neighborhood.graphScale (-analytic.budget.extraLoss) := by
  exact data.finiteGraph.extraCost_le_quadraticLog.trans
    (analytic.extraScalar rho neighborhood.graphScale hrho hrhoSmall rfl)

/-- Apply the pre-runtime analytic and projection thresholds to the saturated
finite graph.  Only the three power comparisons specific to the V4 source
remain explicit: the graph AD constant, graph volume, and local-certificate
source cost. -/
theorem PureWZ2Node05V4RichSaturatedFiniteGraphData.theorem52OfThresholds
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss finalLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : neighborhood.saturatedGraphScale ≤ 1}
    (data : PureWZ2Node05V4RichSaturatedFiniteGraphData
      (eta := eta) neighborhood hbridge hgraphOne)
    (projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss)
    (analytic : PureWZ2SourceHorizontalAnalyticThreshold projection.theoremEta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtput : 0 < finalLoss) (houtputOne : finalLoss < 1)
    (houtputSigma : finalLoss / 2 < sigma)
    (heta : 0 < eta)
    (hCOne : (1 : ENNReal) ≤
      160 * Kakeya.realRpowENN delta (-inputLoss))
    (hCpower :
      (160 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
        Real.rpow neighborhood.graphScale (-analytic.budget.constantLoss))
    (hgraphVolumePower :
      Kakeya.realRpowENN neighborhood.graphScale
          (1 + sigma / 2 + analytic.budget.volumeLoss) ≤
        Kakeya.realRpowENN rho
            (-1 / 2 + neighborhood.neighborhoodLoss) *
          Kakeya.realRpowENN (4 * rhoRequested.1)
            (3 / 2 + sigma / 2 + eta))
    (hsourceCost :
      Kakeya.realRpowENN rhoRequested.1 (-eta) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale neighborhood.graphScale)
          (-projection.sourceCostLossCeiling))
    (hgraphAnalytic : neighborhood.graphScale ≤ analytic.rho0)
    (hrhoProjection : rho ≤ projection.rho₀) :
    Nonempty (PureWZ2AnchoredTheorem52Output data.finiteGraph projection) := by
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hrhoRequested : 0 < rhoRequested.1 := by
    rw [pullback.rhoRequested_eq]
    exact hrho
  have hrhoAnalytic : rho ≤ analytic.rho0 := by
    apply (show rho ≤ neighborhood.graphScale by
      dsimp only [PureWZ2PreCommonBinGlobalGrainNeighborhoodData.graphScale,
        PureWZ2PreCommonBinGlobalGrainNeighborhoodData.saturatedGraphScale]
      linarith).trans hgraphAnalytic
  have hcertificateToSource :
      Kakeya.realRpowENN (4 * rhoRequested.1) (-eta) ≤
        Kakeya.realRpowENN rhoRequested.1 (-eta) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_nonpos hrhoRequested
      (by nlinarith) (by linarith)
  have hCbound :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        10 * Kakeya.realRpowENN rhoRequested.1 (-eta) :=
    data.local_power.trans <| calc
      Kakeya.realRpowENN (4 * rhoRequested.1) (-eta) ≤
          Kakeya.realRpowENN rhoRequested.1 (-eta) := hcertificateToSource
      _ ≤ 10 * Kakeya.realRpowENN rhoRequested.1 (-eta) := by
        exact le_mul_of_one_le_left (by positivity) (by norm_num)
  apply data.theorem52 projection hsigma hsigmaOne houtput houtputOne
    houtputSigma hCOne analytic.budget.constantLoss
    analytic.budget.volumeLoss analytic.budget.extraLoss
    projection.sourceCostLossCeiling
    hCpower (by
      simpa only [Kakeya.realRpowENN] using
        data.graph_volume_lower analytic.budget.volumeLoss hgraphVolumePower)
  · exact analytic.extra_saturatedFiniteGraph data hrho hrhoAnalytic
  · exact analytic.edge neighborhood.graphScale
      neighborhood.graphScale_pos hgraphAnalytic
  · exact analytic.katzTao neighborhood.graphScale
      neighborhood.graphScale_pos hgraphAnalytic
  · exact hCbound
  · exact hsourceCost
  · exact projection.sourceCostLossCeiling_pos.le
  · exact le_rfl
  · simpa only [PureWZ2PreCommonBinGlobalGrainNeighborhoodData.graphScale,
      PureWZ2PreCommonBinGlobalGrainNeighborhoodData.saturatedGraphScale]
      using projection.graph_small rho hrho hrhoProjection
  · simpa only [PureWZ2PreCommonBinGlobalGrainNeighborhoodData.graphScale,
      PureWZ2PreCommonBinGlobalGrainNeighborhoodData.saturatedGraphScale]
      using projection.constant_small rho hrho hrhoProjection

end Kakeya.Assouad

end
