import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryAllBinReentryTraceSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryAllBinNestedSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseAnalyticThreshold
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseProjectionThreshold

/-!
# Re-entry-trace scheduled all-bin ordinary height-lift producer

The all-bin selector is run before any chosen-bin geometry.  The final
selected-residue density is reduced through the runtime source's exact ordinary
trace and the preselected ordinary critical floor, without a same-extremizer
grain-restoration capability or a global cropped-floor hypothesis.  The analytic
threshold is then specialized at the common graph scale, and the projection
conclusion is obtained from the closed OSW reduction.  Finally, the internal
`Z_popular`/`Z_lin` heights are saturated by genuine `rho` cells and pulled
back with exact relative density.  Thus neither pointwise graph goodness, a
projection callback, nor an external height-provenance certificate is exposed.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- The complete concrete all-bin construction on one literal prepared source.
The selected residue and the final one-scale output are kept together, so a
consumer can retain the exact dependent provenance instead of remembering only
the ambient result type. -/
structure PureWZ2OrdinaryAllBinConcreteOneScaleData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) where
  normalEta : ℝ
  theoremEta : ℝ
  volumeLoss : ℝ
  safe : PureWZ2BalancedSafeBlockFamilyData prepared
  carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe
  companions : PureWZ2OrdinaryAllBinOuterPopularCompanionData carriers
  regional : PureWZ2OrdinaryAllBinNestedRegionalData
    (normalEta := normalEta) (finalLoss := finalLoss)
    (theoremEta := theoremEta) (volumeLoss := volumeLoss)
    carriers companions
  residueData : regional.SelectedBlockResidueData
  oneScaleData : residueData.OneScaleData

/-- The complete concrete nested all-bin construction, with its selected-mass
ledger cancelled at the scheduled density loss before invoking the local
ordinary-trace one-scale assembly.  The exact first-cover `cellMass` is
preserved throughout. -/
theorem PureWZ2SourceCarrierPreparation.toConcreteOneScaleOfScheduledAllBinsReentryTrace
    {sigma inputLoss delta rho middleLoss
      stickyLoss finalLoss normalEta outerLoss structuralBudget
      sourceCostLoss traceSourceLoss : ℝ}
    {logExponent normalizationExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (projection : PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss)
    (analytic : PureWZ2SourceFixedBinCoarseAnalyticThreshold
      projection.theoremEta)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) source.shading normalizationExponent
      traceSourceLoss inputLoss)
    (floorSchedule : PureWZ2ReentryTraceFloorSchedule
      sigma finalLoss structuralBudget)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hfinal : 0 < finalLoss) (hfinalOne : finalLoss < 1)
    (hfinalSigma : finalLoss / 2 < sigma)
    (hnormalEta : 0 < normalEta)
    (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (hlocAbsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1)
    (hmargin : 4 * rho ≤ Real.sqrt rho)
    (hCge : (4 : ENNReal) ≤
      Kakeya.realRpowENN rho (-middleLoss))
    (hlocalConstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss)))
    (hCpower :
      (10 * Kakeya.realRpowENN rho (-middleLoss)).toReal ≤
        Real.rpow (256 * rho) (-analytic.base.budget.constantLoss))
    (houterLoss : 0 < outerLoss)
    (hrho : 0 < rho)
    (hrhoOuterSmall : rho ≤
      Classical.choose
        (pureWZ2_sourceWindowHeightBins_power_schedule
          (extraLoss := outerLoss) houterLoss))
    (hrhoPower : rho ≤ Real.rpow delta stickyLoss)
    (hrhoAnalytic : rho ≤ analytic.rho₀)
    (hsourceCost :
      Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale (256 * rho)) (-sourceCostLoss))
    (hsourceCostLoss : 0 ≤ sourceCostLoss)
    (hsourceCostCeiling :
      sourceCostLoss ≤ projection.sourceCostLossCeiling)
    (hrhoProjection : rho ≤ projection.rho₀)
    (hscaleOne : 5 * (256 * rho) ≤ 1)
    (hlengthLower :
      Real.rpow (5 * (256 * rho)) (1 / 2 + finalLoss) ≤
        twoScale.sqrtRequested.1)
    (hnestedGraphBudget :
      4 * (PureWZ2OrdinaryAllBinNestedRegionalData.SelectedBlockResidueData.nestedBinCost
          rho sigma middleLoss *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + analytic.base.budget.volumeLoss)) *
          pureWZ2BalancedSafeNestedCoarseVolumeCost rho ≤
        volume (wz1PaperGridCube rho (0, 0, 0)))
    (hinputDensity : inputLoss ≤ floorSchedule.densityLoss)
    (htraceSource : traceSourceLoss ≤ floorSchedule.traceSourceCeiling)
    (hdeltaSchedule : delta ≤ floorSchedule.delta₀)
    (hfinalPower :
      2 * PureWZ2OrdinaryAllBinNestedRegionalData.SelectedBlockResidueData.totalCost
          delta rho sigma inputLoss middleLoss outerLoss
            analytic.base.budget.extraLoss *
          Kakeya.realRpowENN delta floorSchedule.densityLoss ≤
        Kakeya.realRpowENN rho
            (stickyLoss + twoScale.coarseLoss) *
          wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta inputLoss *
          twoScale.coarse.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss) :
    Nonempty (PureWZ2OrdinaryAllBinConcreteOneScaleData
      (finalLoss := finalLoss) prepared) := by
  rcases prepared.balancedSafeBlockFamily hmargin with ⟨safe⟩
  rcases safe.ordinaryPaperOrderCarriers with ⟨carriers⟩
  rcases carriers.outerPopularCoarseCompanions with ⟨companions⟩
  rcases companions.prepareNestedRegional hbridge hgraphOne hheightAbsorb with
    ⟨preparedRegional⟩
  have hgraphAnalytic : 256 * rho ≤ analytic.base.rho0 :=
    analytic.graph_le_base rho hrho hrhoAnalytic
  have hCOne : (1 : ENNReal) ≤
      10 * Kakeya.realRpowENN rho (-middleLoss) := by
    calc
      (1 : ENNReal) ≤ 10 * 4 := by norm_num
      _ ≤ 10 * Kakeya.realRpowENN rho (-middleLoss) := by
        exact mul_le_mul_left' hCge 10
  let nestedCost :=
    PureWZ2OrdinaryAllBinNestedRegionalData.SelectedBlockResidueData.nestedBinCost
      rho sigma middleLoss
  have hscaled : ∀ block : {block //
        block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ∀ bin : {bin // bin ∈ (preparedRegional.sourceBins block).line.globalBins},
        2 * ((((preparedRegional.nested block bin).fixedLine.line.globalBins.card :
              ENNReal) *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + analytic.base.budget.volumeLoss))) *
            pureWZ2BalancedSafeNestedCoarseVolumeCost rho ≤
          volume (preparedRegional.sync block bin).parentRestriction.cellRestriction.shading.union := by
    intro block bin
    exact preparedRegional.nested_graph_budget hnestedGraphBudget block bin
  rcases preparedRegional.toNestedRegional
      (constantLoss := analytic.base.budget.constantLoss)
      (extraLoss := analytic.base.budget.extraLoss)
      hscaled hbridge hsigma hsigmaOne
      hnormalEta hnormalEtaSigma hcertificateOne hsourceFloor hlocalPower
      hglobalPower hPlanarSmall hrootSmall20 hlocAbsorb hlocalConstant hCOne
      hCpower
      (fun block bin good nestedBin pipeline => by
        apply analytic.extra rho hrho hrhoAnalytic)
      (fun block bin good nestedBin => by
        simpa [((preparedRegional.nested block bin).preparation
          nestedBin.1).prep.graphScale_eq] using
          analytic.base.edge (256 * rho) (by positivity) hgraphAnalytic)
      (fun block bin good nestedBin => by
        simpa [((preparedRegional.nested block bin).preparation
          nestedBin.1).prep.graphScale_eq] using
          analytic.base.katzTao (256 * rho) (by positivity) hgraphAnalytic)
      (fun block bin good nestedBin pipeline ready => by
        apply projection.alternativeA_sourceFixedBinCoarse ready
          hfinal hfinalOne hsigma hsigmaOne hfinalSigma
          (sourceCostLoss := sourceCostLoss)
        · simpa [ready.ready.deltaGraph_eq,
            ((preparedRegional.nested block bin).preparation
              nestedBin.1).prep.graphScale_eq] using hsourceCost
        · exact hsourceCostLoss
        · exact hsourceCostCeiling
        · exact hrhoProjection)
      hscaleOne hlengthLower with ⟨regional⟩
  rcases regional.selectBlockResidue with ⟨residueData⟩
  let outerCost := Kakeya.realRpowENN (256 * rho) (-outerLoss)
  let parentCost :=
    PureWZ2OrdinaryAllBinNestedRegionalData.SelectedBlockResidueData.parentBinCost rho
  let sourceBinCost :=
    PureWZ2OrdinaryAllBinNestedRegionalData.SelectedBlockResidueData.sourceBinCost
      delta rho sigma inputLoss
  have houterCostPos : 0 < outerCost := by
    dsimp only [outerCost, Kakeya.realRpowENN]
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)
  have houterCostTop : outerCost ≠ ⊤ := by
    simp [outerCost, Kakeya.realRpowENN]
  have houterCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      (2 * (carriers.carrier block.1).outerPopular.popular.bins :
          ENNReal) ≤ outerCost := by
    intro block
    exact carriers.outer_bins_power_bound
      houterLoss hrho hrhoOuterSmall block
  have hparentCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((regional.weightClass block).bins : ENNReal) ≤ parentCost := by
    intro block
    exact PureWZ2OrdinaryAllBinNestedRegionalData.SelectedBlockResidueData.parentBinCost_bound
      (regional := regional) block
  have hsourceBinCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((regional.sourceBins block).line.globalBins.card : ENNReal) ≤
        sourceBinCost := fun block => by
    simpa [sourceBinCost] using
      (PureWZ2OrdinaryAllBinNestedRegionalData.SelectedBlockResidueData.sourceBinCost_bound
        (regional := regional) block)
  have hnestedBinCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ∀ bin : {bin // bin ∈ (regional.sourceBins block).line.globalBins},
        (((regional.family block).good bin).selected.card : ENNReal) ≤
          nestedCost := fun block bin => by
    simpa [nestedCost] using
      (PureWZ2OrdinaryAllBinNestedRegionalData.SelectedBlockResidueData.nestedBinCost_bound
        (regional := regional) block bin)
  let totalCost :=
    PureWZ2OrdinaryAllBinNestedRegionalData.SelectedBlockResidueData.totalCost
      delta rho sigma inputLoss middleLoss outerLoss
        analytic.base.budget.extraLoss
  have hselected := residueData.selected_nested_mass_bound
    (extraLoss := analytic.base.budget.extraLoss)
    outerCost parentCost sourceBinCost nestedCost houterCost hparentCost
    hsourceBinCost hnestedBinCost
    (fun block bin nestedBin => by
      apply analytic.extra rho hrho hrhoAnalytic)
  have htotalCostPos : 0 < totalCost := by
    simpa [totalCost] using
      PureWZ2OrdinaryAllBinNestedRegionalData.SelectedBlockResidueData.totalCost_pos
        (sigma := sigma) (inputLoss := inputLoss) (middleLoss := middleLoss)
        (outerLoss := outerLoss) (extraLoss := analytic.base.budget.extraLoss)
        source.extremal.delta_pos hrho (by nlinarith [hgraphOne])
  have htotalCostTop : totalCost ≠ ⊤ := by
    simpa [totalCost] using
      (PureWZ2OrdinaryAllBinNestedRegionalData.SelectedBlockResidueData.totalCost_ne_top
        (delta := delta) (rho := rho) (sigma := sigma)
        (inputLoss := inputLoss) (middleLoss := middleLoss)
        (outerLoss := outerLoss)
        (extraLoss := analytic.base.budget.extraLoss) hrho)
  have hdense := residueData.dense_of_selected_nested_mass totalCost
    htotalCostPos htotalCostTop
    (by
      simpa only [totalCost,
        PureWZ2OrdinaryAllBinNestedRegionalData.SelectedBlockResidueData.totalCost,
        outerCost, parentCost, sourceBinCost, nestedCost]
        using hselected)
    (by simpa [totalCost, mul_comm, mul_left_comm, mul_assoc] using hfinalPower)
  rcases residueData.toOneScaleDataOfReentryTraceSchedule reentry floorSchedule
      hinputDensity htraceSource hdeltaSchedule hdense with ⟨oneScaleData⟩
  exact ⟨{
    normalEta := normalEta
    theoremEta := projection.theoremEta
    volumeLoss := analytic.base.budget.volumeLoss
    safe := safe
    carriers := carriers
    companions := companions
    regional := regional
    residueData := residueData
    oneScaleData := oneScaleData
  }⟩

/-- Compatibility projection which forgets the complete all-bin provenance. -/
theorem PureWZ2SourceCarrierPreparation.toOneScaleOfScheduledAllBinsReentryTrace
    {sigma inputLoss delta rho middleLoss
      stickyLoss finalLoss normalEta outerLoss structuralBudget
      sourceCostLoss traceSourceLoss : ℝ}
    {logExponent normalizationExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (projection : PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss)
    (analytic : PureWZ2SourceFixedBinCoarseAnalyticThreshold
      projection.theoremEta)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) source.shading normalizationExponent
      traceSourceLoss inputLoss)
    (floorSchedule : PureWZ2ReentryTraceFloorSchedule
      sigma finalLoss structuralBudget)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hfinal : 0 < finalLoss) (hfinalOne : finalLoss < 1)
    (hfinalSigma : finalLoss / 2 < sigma)
    (hnormalEta : 0 < normalEta)
    (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (hlocAbsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1)
    (hmargin : 4 * rho ≤ Real.sqrt rho)
    (hCge : (4 : ENNReal) ≤
      Kakeya.realRpowENN rho (-middleLoss))
    (hlocalConstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss)))
    (hCpower :
      (10 * Kakeya.realRpowENN rho (-middleLoss)).toReal ≤
        Real.rpow (256 * rho) (-analytic.base.budget.constantLoss))
    (houterLoss : 0 < outerLoss)
    (hrho : 0 < rho)
    (hrhoOuterSmall : rho ≤
      Classical.choose
        (pureWZ2_sourceWindowHeightBins_power_schedule
          (extraLoss := outerLoss) houterLoss))
    (hrhoPower : rho ≤ Real.rpow delta stickyLoss)
    (hrhoAnalytic : rho ≤ analytic.rho₀)
    (hsourceCost :
      Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale (256 * rho)) (-sourceCostLoss))
    (hsourceCostLoss : 0 ≤ sourceCostLoss)
    (hsourceCostCeiling :
      sourceCostLoss ≤ projection.sourceCostLossCeiling)
    (hrhoProjection : rho ≤ projection.rho₀)
    (hscaleOne : 5 * (256 * rho) ≤ 1)
    (hlengthLower :
      Real.rpow (5 * (256 * rho)) (1 / 2 + finalLoss) ≤
        twoScale.sqrtRequested.1)
    (hnestedGraphBudget :
      4 * (PureWZ2OrdinaryAllBinNestedRegionalData.SelectedBlockResidueData.nestedBinCost
          rho sigma middleLoss *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + analytic.base.budget.volumeLoss)) *
          pureWZ2BalancedSafeNestedCoarseVolumeCost rho ≤
        volume (wz1PaperGridCube rho (0, 0, 0)))
    (hinputDensity : inputLoss ≤ floorSchedule.densityLoss)
    (htraceSource : traceSourceLoss ≤ floorSchedule.traceSourceCeiling)
    (hdeltaSchedule : delta ≤ floorSchedule.delta₀)
    (hfinalPower :
      2 * PureWZ2OrdinaryAllBinNestedRegionalData.SelectedBlockResidueData.totalCost
          delta rho sigma inputLoss middleLoss outerLoss
            analytic.base.budget.extraLoss *
          Kakeya.realRpowENN delta floorSchedule.densityLoss ≤
        Kakeya.realRpowENN rho
            (stickyLoss + twoScale.coarseLoss) *
          wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta inputLoss *
          twoScale.coarse.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss) :
    Nonempty (PureWZ2LocallyLinearOneScaleData source finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  rcases prepared.toConcreteOneScaleOfScheduledAllBinsReentryTrace
      projection analytic hbridge reentry floorSchedule hsigma hsigmaOne
      hfinal hfinalOne hfinalSigma hnormalEta hnormalEtaSigma
      hcertificateOne hsourceFloor hlocalPower hglobalPower hPlanarSmall
      hrootSmall20 hlocAbsorb hgraphOne hheightAbsorb hmargin hCge
      hlocalConstant hCpower houterLoss hrho hrhoOuterSmall hrhoPower
      hrhoAnalytic hsourceCost hsourceCostLoss hsourceCostCeiling
      hrhoProjection hscaleOne hlengthLower hnestedGraphBudget hinputDensity
      htraceSource hdeltaSchedule hfinalPower with ⟨data⟩
  exact ⟨data.oneScaleData.oneScale⟩

end Kakeya.Assouad

end
