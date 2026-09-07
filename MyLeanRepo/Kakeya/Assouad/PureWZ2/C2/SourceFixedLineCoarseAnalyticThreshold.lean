import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalUniformBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarsePipeline

/-!
# Uniform analytic threshold for fixed-bin coarse pipelines

The edge and Katz--Tao bounds are the existing source-horizontal bounds.
Only the logarithmic `extraCost` estimate is restated for the preparation-
indexed fixed-bin pipeline used by the all-bin selector.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The bounded-grid logarithmic cost is uniform over every fixed-bin coarse
pipeline at the common graph scale `256 * rho`. -/
theorem pureWZ2_sourceFixedBinCoarse_extraCost_schedule
    {extraLoss : ℝ} (hextraLoss : 0 < extraLoss) :
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ rho₀ →
        ∀ sigma inputLoss delta middleLoss stickyLoss normalEta : ℝ,
        ∀ logExponent : ℕ,
        ∀ source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta,
        ∀ twoScale : PureWZ2OneScaleTwoScaleStickyData
            source rho middleLoss stickyLoss logExponent,
        ∀ pullback : PureWZ2TwoScaleCellPullbackData twoScale,
        ∀ prepared : PureWZ2SourceCarrierPreparation pullback,
        ∀ window : PureWZ2SourceCarrierWindow prepared,
        ∀ line : PureWZ2SourceHorizontalFixedBinData window,
        ∀ parents : PureWZ2SourceHorizontalFixedBinParentData line,
        ∀ selection : PureWZ2SourceHorizontalFixedBinYSelection parents,
        ∀ residue : PureWZ2SourceHorizontalFixedBinYResidueData selection,
        ∀ retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue,
        ∀ carrier : PureWZ2SourceFixedBinCoarseCarrierData residue,
        ∀ fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained,
        ∀ original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
          carrier fineWitnesses.coarseWitnesses,
        ∀ prep : PureWZ2SourceFixedBinCoarsePreparationData original,
        ∀ pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
            (normalEta := normalEta) prep,
          (pipeline.preparedGraph.graph.residue.extraCost : ℝ) ≤
            Real.rpow prep.graphScale (-extraLoss) := by
  rcases log_poly_decay_general 2000 (extraLoss / 2) (by norm_num)
      (by positivity) with
    ⟨constantScale₀, hconstantScale₀, hconstantScale₀One, hgraphLog⟩
  rcases log_poly_decay_general 1 (extraLoss / 4) (by norm_num)
      (by positivity) with
    ⟨logScale₀, hlogScale₀, hlogScale₀One, hlogPower⟩
  let graphScale₀ := min constantScale₀ logScale₀
  let rho₀ := graphScale₀ / 256
  refine ⟨rho₀, by positivity, ?_, ?_⟩
  · exact (div_le_self (by positivity) (by norm_num)).trans
      ((min_le_left _ _).trans hconstantScale₀One)
  intro rho hrho hrhoSmall sigma inputLoss delta middleLoss stickyLoss
    normalEta logExponent source twoScale pullback prepared window line parents
    selection residue retained carrier fineWitnesses original prep pipeline
  have hgraphPos : 0 < prep.graphScale := prep.graphScale_pos
  have hgraphSmall : prep.graphScale ≤ graphScale₀ := by
    rw [prep.graphScale_eq]
    calc
      256 * rho ≤ 256 * rho₀ := by gcongr
      _ = graphScale₀ := by unfold rho₀; ring
  have hgraphOne : prep.graphScale ≤ 1 :=
    hgraphSmall.trans ((min_le_left _ _).trans hconstantScale₀One)
  have hlog := wz1Lemma23BoundedCells_log_bound hgraphPos hgraphOne
  have hcellsSubset : prep.windowed.global.cells ⊆
      wz1Lemma23BoundedCells prep.graphScale hgraphPos := by
    classical
    exact prep.windowed.global.cells_active.trans (Finset.filter_subset _ _)
  have hcard : prep.windowed.global.cells.card ≤
      (wz1Lemma23BoundedCells prep.graphScale hgraphPos).card :=
    Finset.card_le_card hcellsSubset
  have hrawCard : pipeline.preparedGraph.rawResidue.cells.card ≤
      (wz1Lemma23BoundedCells prep.graphScale hgraphPos).card :=
    (Finset.card_le_card
      pipeline.preparedGraph.rawResidue.cells_subset).trans hcard
  have hrawNonempty : pipeline.preparedGraph.rawResidue.cells.Nonempty := by
    rw [pipeline.preparedGraph.raw_residue_eq]
    exact pipeline.preparedGraph.popularSource.cells_nonempty
  have hboundedNonempty :
      (wz1Lemma23BoundedCells prep.graphScale hgraphPos).Nonempty :=
    hrawNonempty.mono
      (pipeline.preparedGraph.rawResidue.cells_subset.trans hcellsSubset)
  have hrawLogNat :
      Nat.log 2 pipeline.preparedGraph.rawResidue.cells.card + 1 ≤
        Nat.log 2 (wz1Lemma23BoundedCells prep.graphScale hgraphPos).card + 1 :=
    Nat.add_le_add_right (Nat.log_mono_right hrawCard) 1
  have hheightCard :
      (wz1Lemma23BoundedHeightIndices prep.graphScale hgraphPos).card ≤
        (wz1Lemma23BoundedCells prep.graphScale hgraphPos).card :=
    Finset.card_image_le
  have hbinsArg :
      2 * (wz1Lemma23BoundedHeightIndices prep.graphScale hgraphPos).card ≤
        4 * (wz1Lemma23BoundedCells prep.graphScale hgraphPos).card := by
    have hcellsPos : 0 <
        (wz1Lemma23BoundedCells prep.graphScale hgraphPos).card :=
      hboundedNonempty.card_pos
    omega
  have hbinsLog :
      Nat.log 2
          (2 * (wz1Lemma23BoundedHeightIndices prep.graphScale hgraphPos).card) ≤
        Nat.log 2
          (4 * (wz1Lemma23BoundedCells prep.graphScale hgraphPos).card) :=
    Nat.log_mono_right hbinsArg
  have hcellsNe :
      (wz1Lemma23BoundedCells prep.graphScale hgraphPos).card ≠ 0 :=
    hboundedNonempty.card_ne_zero
  have hfourEq :
      4 * (wz1Lemma23BoundedCells prep.graphScale hgraphPos).card =
        (wz1Lemma23BoundedCells prep.graphScale hgraphPos).card * 2 * 2 := by
    ring
  have hbinsNat : pipeline.preparedGraph.heightPopular.bins ≤
      Nat.log 2 (wz1Lemma23BoundedCells prep.graphScale hgraphPos).card + 3 := by
    rw [pipeline.preparedGraph.heightPopular.bins_eq]
    calc
      Nat.log 2
          (2 * (wz1Lemma23BoundedHeightIndices prep.graphScale hgraphPos).card) + 1 ≤
        Nat.log 2
          (4 * (wz1Lemma23BoundedCells prep.graphScale hgraphPos).card) + 1 := by
          omega
      _ = Nat.log 2
          (wz1Lemma23BoundedCells prep.graphScale hgraphPos).card + 3 := by
        rw [hfourEq]
        calc
          Nat.log 2
              ((wz1Lemma23BoundedCells prep.graphScale hgraphPos).card * 2 * 2) + 1 =
            Nat.log 2
              ((wz1Lemma23BoundedCells prep.graphScale hgraphPos).card * 2) +
                1 + 1 := by
              rw [Nat.log_mul_base (by omega)
                (Nat.mul_ne_zero hcellsNe (by omega))]
          _ = Nat.log 2
              (wz1Lemma23BoundedCells prep.graphScale hgraphPos).card +
                1 + 1 + 1 := by
              rw [Nat.log_mul_base (by omega) hcellsNe]
          _ = _ := by omega
  let L : ℝ := Real.log (1 / prep.graphScale) + 1
  have hLNonneg : 0 ≤ L := by
    dsimp only [L]
    have hlogNonneg : 0 ≤ Real.log (1 / prep.graphScale) := by
      apply Real.log_nonneg
      exact one_le_one_div hgraphPos hgraphOne
    linarith
  have hrawLogReal :
      (Nat.log 2 pipeline.preparedGraph.rawResidue.cells.card + 1 : ℝ) ≤
        20 * L := by
    have hcast :
        (Nat.log 2 pipeline.preparedGraph.rawResidue.cells.card + 1 : ℝ) ≤
          (Nat.log 2 (wz1Lemma23BoundedCells prep.graphScale hgraphPos).card +
            1 : ℕ) := by
      exact_mod_cast hrawLogNat
    exact hcast.trans (by simpa [L] using hlog)
  have hbinsReal : (pipeline.preparedGraph.heightPopular.bins : ℝ) ≤
      23 * L := by
    have hnat : (pipeline.preparedGraph.heightPopular.bins : ℝ) ≤
        (Nat.log 2 (wz1Lemma23BoundedCells prep.graphScale hgraphPos).card +
          3 : ℕ) := by
      exact_mod_cast hbinsNat
    have hone : 1 ≤ L := by
      dsimp only [L]
      have hlogNonneg : 0 ≤ Real.log (1 / prep.graphScale) := by
        apply Real.log_nonneg
        exact one_le_one_div hgraphPos hgraphOne
      linarith
    calc
      (pipeline.preparedGraph.heightPopular.bins : ℝ) ≤
          (Nat.log 2 (wz1Lemma23BoundedCells prep.graphScale hgraphPos).card +
            3 : ℕ) := hnat
      _ ≤ 20 * L + 2 := by
        norm_num only [Nat.cast_add, Nat.cast_ofNat]
        linarith [hlog]
      _ ≤ 23 * L := by nlinarith
  have hcostQuadratic :
      (pipeline.preparedGraph.graph.residue.extraCost : ℝ) ≤ 920 * L ^ 2 := by
    rw [pipeline.preparedGraph.extraCost_eq]
    push_cast
    nlinarith [mul_le_mul hbinsReal hrawLogReal (by positivity) (by positivity)]
  have hLsmall : L ≤ Real.rpow prep.graphScale (-(extraLoss / 4)) := by
    have h := hlogPower prep.graphScale hgraphPos
      (hgraphSmall.trans (min_le_right _ _))
    simpa [L, one_div, Real.rpow_neg hgraphPos.le] using h
  have hcostLinear :
      (pipeline.preparedGraph.graph.residue.extraCost : ℝ) ≤
        920 * Real.rpow prep.graphScale (-(extraLoss / 2)) := by
    calc
      _ ≤ 920 * L ^ 2 := hcostQuadratic
      _ ≤ 920 * (Real.rpow prep.graphScale (-(extraLoss / 4))) ^ 2 := by
        gcongr
      _ = 920 * Real.rpow prep.graphScale (-(extraLoss / 2)) := by
        rw [pow_two]
        congr 1
        calc
          Real.rpow prep.graphScale (-(extraLoss / 4)) *
              Real.rpow prep.graphScale (-(extraLoss / 4)) =
            Real.rpow prep.graphScale
              (-(extraLoss / 4) + -(extraLoss / 4)) :=
            (Real.rpow_add hgraphPos _ _).symm
          _ = Real.rpow prep.graphScale (-(extraLoss / 2)) := by
            congr 1
            ring
  have habsorb := hgraphLog prep.graphScale hgraphPos
    (hgraphSmall.trans (min_le_left _ _))
  have hinverse :
      1 / Real.rpow prep.graphScale extraLoss =
        Real.rpow prep.graphScale (-extraLoss) := by
    rw [one_div]
    exact (Real.rpow_neg hgraphPos.le extraLoss).symm
  have hconstant : 920 ≤
      Real.rpow prep.graphScale (-(extraLoss / 2)) := by
    have hraw := habsorb
    have hLone : 1 ≤ Real.log (1 / prep.graphScale) + 1 := by
      have hlogNonneg : 0 ≤ Real.log (1 / prep.graphScale) := by
        apply Real.log_nonneg
        exact one_le_one_div hgraphPos hgraphOne
      linarith
    have : 2000 ≤ 2000 * (Real.log (1 / prep.graphScale) + 1) := by
      nlinarith
    have h920 : (920 : ℝ) ≤ 2000 := by norm_num
    have hpower :
        2000 * (Real.log (1 / prep.graphScale) + 1) ≤
          Real.rpow prep.graphScale (-(extraLoss / 2)) := by
      simpa [one_div, Real.rpow_neg hgraphPos.le] using hraw
    exact h920.trans (this.trans hpower)
  calc
    (pipeline.preparedGraph.graph.residue.extraCost : ℝ) ≤
        920 * Real.rpow prep.graphScale (-(extraLoss / 2)) := hcostLinear
    _ ≤ Real.rpow prep.graphScale (-(extraLoss / 2)) *
        Real.rpow prep.graphScale (-(extraLoss / 2)) := by gcongr
    _ = Real.rpow prep.graphScale (-extraLoss) := by
      calc
        Real.rpow prep.graphScale (-(extraLoss / 2)) *
            Real.rpow prep.graphScale (-(extraLoss / 2)) =
          Real.rpow prep.graphScale
            (-(extraLoss / 2) + -(extraLoss / 2)) :=
          (Real.rpow_add hgraphPos _ _).symm
        _ = Real.rpow prep.graphScale (-extraLoss) := by
          congr 1
          ring

/-- One pre-runtime threshold supplies all analytic bounds for every
preparation-indexed fixed-bin coarse pipeline. -/
structure PureWZ2SourceFixedBinCoarseAnalyticThreshold
    (theoremEta : ℝ) where
  base : PureWZ2SourceHorizontalAnalyticThreshold theoremEta
  rho₀ : ℝ
  rho₀_pos : 0 < rho₀
  rho₀_le_one : rho₀ ≤ 1
  graph_le_base :
    ∀ rho, 0 < rho → rho ≤ rho₀ → 256 * rho ≤ base.rho0
  extra :
    ∀ rho : ℝ, 0 < rho → rho ≤ rho₀ →
      ∀ sigma inputLoss delta middleLoss stickyLoss normalEta : ℝ,
      ∀ logExponent : ℕ,
      ∀ source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta,
      ∀ twoScale : PureWZ2OneScaleTwoScaleStickyData
          source rho middleLoss stickyLoss logExponent,
      ∀ pullback : PureWZ2TwoScaleCellPullbackData twoScale,
      ∀ prepared : PureWZ2SourceCarrierPreparation pullback,
      ∀ window : PureWZ2SourceCarrierWindow prepared,
      ∀ line : PureWZ2SourceHorizontalFixedBinData window,
      ∀ parents : PureWZ2SourceHorizontalFixedBinParentData line,
      ∀ selection : PureWZ2SourceHorizontalFixedBinYSelection parents,
      ∀ residue : PureWZ2SourceHorizontalFixedBinYResidueData selection,
      ∀ retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue,
      ∀ carrier : PureWZ2SourceFixedBinCoarseCarrierData residue,
      ∀ fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained,
      ∀ original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
        carrier fineWitnesses.coarseWitnesses,
      ∀ prep : PureWZ2SourceFixedBinCoarsePreparationData original,
      ∀ pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
          (normalEta := normalEta) prep,
        (pipeline.preparedGraph.graph.residue.extraCost : ℝ) ≤
          Real.rpow prep.graphScale (-base.budget.extraLoss)

theorem pureWZ2_sourceFixedBinCoarse_analytic_threshold
    {theoremEta : ℝ} (htheoremEta : 0 < theoremEta) :
    Nonempty (PureWZ2SourceFixedBinCoarseAnalyticThreshold theoremEta) := by
  rcases pureWZ2_sourceHorizontal_analytic_threshold htheoremEta with ⟨base⟩
  rcases pureWZ2_sourceFixedBinCoarse_extraCost_schedule
      base.budget.extraLoss_pos with
    ⟨extraRho₀, hextraRho₀, hextraRho₀One, hextra⟩
  let rho₀ := min (base.rho0 / 256) extraRho₀
  exact ⟨{
    base := base
    rho₀ := rho₀
    rho₀_pos := lt_min (div_pos base.rho0_pos (by norm_num)) hextraRho₀
    rho₀_le_one := by
      calc
        rho₀ ≤ base.rho0 / 256 := min_le_left _ _
        _ ≤ base.rho0 := div_le_self base.rho0_pos.le (by norm_num)
        _ ≤ 1 := base.rho0_le_one
    graph_le_base := by
      intro rho hrho hrhoSmall
      have hbound : rho ≤ base.rho0 / 256 :=
        hrhoSmall.trans (min_le_left _ _)
      nlinarith
    extra := by
      intro rho hrho hrhoSmall
      exact hextra rho hrho (hrhoSmall.trans (min_le_right _ _))
  }⟩

end Kakeya.Assouad

end
