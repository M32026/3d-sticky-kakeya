import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CommonBinNatFloorSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinHeavyPopularFloor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinSourceHeavyGraphFamily

/-!
# Uniform scalar selection for source-heavy common-bin graphs

This module isolates the two family-free scalar inequalities left after the
geometric common-bin argument.  From them it chooses one natural `K`, defines
the per-slab rich threshold, constructs the source-heavy graph family, and
proves its aggregate graph budget.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Complete uniform common-bin scalar and graph-family receipt. -/
structure PureWZ2SourceHeavyCommonBinScalarData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)
    (B₀ : ENNReal)
    (volumeLoss : ℝ) where
  preBinFamily : PureWZ2SourceHeavyPreBinRhoHeightFamilyData pullback
  X : ENNReal
  X_one : 1 ≤ X
  X_ne_top : X ≠ ⊤
  X_source_lower :
    preBinFamily.popularFloor /
        (4 * B₀ *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho) ≤
      X
  K : ℕ
  K_lower : X / 2 ≤ K
  K_upper : (K : ENNReal) ≤ X
  threshold :
    PureWZ2SourceHeavyStandardSqrtSlabIndex pullback → ENNReal
  threshold_eq : ∀ heightIndex,
    threshold heightIndex =
      (K : ENNReal) *
        PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
          sigma inputLoss delta rho
  graph :
    PureWZ2SourceHeavyStandardSlabCommonBinGraphFamilyData
      pullback threshold K
  graph_preBinFamily_eq : graph.preBinFamily = preBinFamily
  separated_graph_scalar :
    40 * pureWZ2CommonBinPreBinHeightCost rho * (5 : ENNReal) * 512 *
          graph.graphThreshold volumeLoss ≤
      (K : ENNReal) * twoScale.fine.balanced.cellMass
  graphBudget :
    graph.GraphBudget volumeLoss

/-- The two multiplication-only scalar budgets produce the complete
source-heavy common-bin graph family. -/
theorem PureWZ2TwoScaleCellPullbackData.sourceHeavyCommonBinScalarData
    {sigma inputLoss delta rho middleLoss outputLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)
    (preBinFamily : PureWZ2SourceHeavyPreBinRhoHeightFamilyData pullback)
    (B₀ X : ENNReal)
    (hB₀ :
      264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hXOne : 1 ≤ X)
    (hXTop : X ≠ ⊤)
    (hXSourceLower :
      preBinFamily.popularFloor /
          (4 * B₀ *
            PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
              sigma inputLoss delta rho) ≤
        X)
    (hcapacity :
      2 * B₀ *
          (X *
            PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
              sigma inputLoss delta rho) ≤
        preBinFamily.popularFloor)
    (hseparatedGraph :
      40 * pureWZ2CommonBinPreBinHeightCost rho * (5 : ENNReal) * 512 *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss) ≤
        (X / 2) * twoScale.fine.balanced.cellMass) :
    Nonempty
      (PureWZ2SourceHeavyCommonBinScalarData
        pullback B₀ volumeLoss) := by
  rcases CommonBinRichSelection.exists_natCast_between_half
      X hXOne hXTop with
    ⟨K, hKLower, hKUpper⟩
  let cellCap :=
    PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
      sigma inputLoss delta rho
  let threshold :
      PureWZ2SourceHeavyStandardSqrtSlabIndex pullback → ENNReal :=
    fun _ => (K : ENNReal) * cellCap
  have hthresholdBudget : ∀ heightIndex,
      2 * B₀ * threshold heightIndex ≤
        pureWZ2SourceCommonBinPopularThreshold
          (preBinFamily.blockData heightIndex).sourceSet
          (Real.sqrt rho) := by
    intro heightIndex
    calc
      2 * B₀ * threshold heightIndex =
          2 * B₀ * ((K : ENNReal) * cellCap) := by
        rfl
      _ ≤ 2 * B₀ * (X * cellCap) := by
        gcongr
      _ ≤ preBinFamily.popularFloor :=
        hcapacity
      _ ≤
          pureWZ2SourceCommonBinPopularThreshold
            (preBinFamily.blockData heightIndex).sourceSet
            (Real.sqrt rho) :=
        preBinFamily.popularFloor_le heightIndex
          (by
            rw [← twoScale.rhoRequested_eq]
            exact twoScale.rhoRequested.property.2)
  have hK : ∀ heightIndex,
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤
        threshold heightIndex := by
    intro heightIndex
    exact le_rfl
  rcases
      pullback.sourceHeavyStandardSlabCommonBinGraphFamily
        preBinFamily B₀ threshold K hB₀ hthresholdBudget hK
    with
    ⟨graph, hgraphPreBin⟩
  have hseparatedGraphK :
      40 * pureWZ2CommonBinPreBinHeightCost rho * (5 : ENNReal) * 512 *
          graph.graphThreshold volumeLoss ≤
        (K : ENNReal) * twoScale.fine.balanced.cellMass := by
    calc
      40 * pureWZ2CommonBinPreBinHeightCost rho * (5 : ENNReal) * 512 *
            graph.graphThreshold volumeLoss =
          40 * pureWZ2CommonBinPreBinHeightCost rho * (5 : ENNReal) * 512 *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss) := by
        rfl
      _ ≤ (X / 2) * twoScale.fine.balanced.cellMass :=
        hseparatedGraph
      _ ≤ (K : ENNReal) * twoScale.fine.balanced.cellMass := by
        gcongr
  have hgraphK :
      ∀ heightIndex,
        40 * graph.heightCost heightIndex *
            graph.graphThreshold volumeLoss ≤
          (K : ENNReal) * twoScale.fine.balanced.cellMass := by
    intro heightIndex
    have hheightCost :=
      (graph.blockData heightIndex).preBin.logarithmicCost_le_heightCost
        (by
          rw [← twoScale.rhoRequested_eq]
          exact twoScale.rhoRequested.property.2)
    calc
      40 * graph.heightCost heightIndex * graph.graphThreshold volumeLoss ≤
          40 * pureWZ2CommonBinPreBinHeightCost rho *
            graph.graphThreshold volumeLoss := by
        gcongr
        simpa [PureWZ2SourceHeavyStandardSlabCommonBinGraphFamilyData.heightCost]
          using hheightCost
      _ = (40 * pureWZ2CommonBinPreBinHeightCost rho *
          graph.graphThreshold volumeLoss) * 1 := by rw [mul_one]
      _ ≤ (40 * pureWZ2CommonBinPreBinHeightCost rho *
          graph.graphThreshold volumeLoss) * ((5 : ENNReal) * 512) :=
        by
          simpa [mul_comm] using mul_le_mul_right
            (show (1 : ENNReal) ≤ 5 * 512 by norm_num)
            (40 * pureWZ2CommonBinPreBinHeightCost rho *
              graph.graphThreshold volumeLoss)
      _ = 40 * pureWZ2CommonBinPreBinHeightCost rho *
          (5 : ENNReal) * 512 * graph.graphThreshold volumeLoss := by ring
      _ = 40 * pureWZ2CommonBinPreBinHeightCost rho *
          (5 : ENNReal) * 512 *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss) := rfl
      _ ≤ (X / 2) * twoScale.fine.balanced.cellMass := hseparatedGraph
      _ ≤ (K : ENNReal) * twoScale.fine.balanced.cellMass := by gcongr
  exact ⟨{
    preBinFamily := preBinFamily
    X := X
    X_one := hXOne
    X_ne_top := hXTop
    X_source_lower := hXSourceLower
    K := K
    K_lower := hKLower
    K_upper := hKUpper
    threshold := threshold
    threshold_eq := fun _ => rfl
    graph := graph
    graph_preBinFamily_eq := hgraphPreBin
    separated_graph_scalar := hseparatedGraphK
    graphBudget := graph.graphBudget_of_commonBin volumeLoss hgraphK
  }⟩

end Kakeya.Assouad

end
