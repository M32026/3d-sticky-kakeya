import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineLocalCellFamily
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedPreparedGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23HeightPopularity

/-!
# Genuine prepared Lemma-23 graph on the fixed-line residue

All geometric inputs come from the same Pure paper carrier.  The explicit
smallness assumptions are intended to be discharged once by the one-scale
threshold.
-/

noncomputable section

namespace Kakeya.Assouad

theorem PureWZ2HorizontalFixedLineGraphParentData.preparedGraph
    {sigma inputLoss delta rho middleLoss outputLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading :
      PureWZ2HorizontalFixedLineResidueShadingData residue}
    {prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading}
    (graphParents : PureWZ2HorizontalFixedLineGraphParentData prep)
    (sources : PureWZ2HorizontalFixedLineResidueSourceFamily residueShading)
    (fullGrains :
      PureWZ2HorizontalFixedLineResidueFullGrainFamily
        (eta := eta) sources prep)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (heta : 0 < eta) (heta_sigma : 4 * eta < sigma)
    (hconstantPower :
      10 * Kakeya.realRpowENN
          twoScale.rhoRequested.1 (-middleLoss) ≤
        Kakeya.realRpowENN prep.graphScale (-eta))
    (hPlanarSmall : 32 * Real.rpow prep.graphScale eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt prep.graphScale ≤ 1)
    (habsorb :
      Real.rpow prep.graphScale (1 - 4 * eta / sigma) ≤
        Real.sqrt prep.graphScale / 14) :
    ∃ graph : WZ1Lemma23WindowedPreparedGraph prep.windowed,
      graph.residue.heightFiberCost = 2 ∧
        graph.residue.extraCost ≤
          Nat.log 2 prep.windowed.global.cells.card + 1 := by
  rcases graphParents.localCellFamily sources fullGrains with ⟨family⟩
  have hCtop :
      (10 * Kakeya.realRpowENN
        twoScale.rhoRequested.1 (-middleLoss) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  rcases wz1_lemma23_local_bin_package_generalized
      prep.shadow
      (10 * Kakeya.realRpowENN
        twoScale.rhoRequested.1 (-middleLoss))
      prep.windowed.global.sourceSlope prep.windowed.global.cells
      prep.localGrains prep.base_le_graphScale prep.graphScale_one
      hsigma hsigma_one heta heta_sigma hCtop hconstantPower
      hPlanarSmall hrootSmall20 habsorb family with
    ⟨localBins, _⟩
  rcases wz1_lemma23_y_residue_package
      prep.windowed.global prep.graphScale_one with
    ⟨rawResidue, _hrawCells, _hrawExtra⟩
  have hrawNonempty : rawResidue.cells.Nonempty := by
    apply Finset.card_pos.mp
    have hglobalNonempty : 0 < prep.windowed.global.cells.card := by
      have hvolumePos : 0 < MeasureTheory.volume prep.shadow.union := by
        rw [prep.shadow_union, residueShading.volume_eq]
        have hselectedPos :
            0 < (residue.selected.card : ENNReal) := by
          exact_mod_cast residue.selected_nonempty.card_pos
        exact ENNReal.mul_pos
          hselectedPos.ne'
          twoScale.fine.balanced.cellMass_pos.ne'
      by_contra hzero
      have hcells : prep.windowed.global.cells.card = 0 :=
        Nat.eq_zero_of_not_pos hzero
      have hbound := prep.windowed.global.volume_cell_bound
      rw [hcells] at hbound
      norm_num at hbound
      exact (not_le_of_gt hvolumePos) hbound.le
    have hrawCard := rawResidue.card_loss
    by_contra hzero
    have hrawZero : rawResidue.cells.card = 0 :=
      Nat.eq_zero_of_not_pos hzero
    rw [hrawZero, Nat.mul_zero] at hrawCard
    omega
  rcases rawResidue.regularizeHeights hrawNonempty with ⟨popularResidue⟩
  let graphResidue := popularResidue.residue
  have hheightFiberCost : graphResidue.heightFiberCost = 2 :=
    popularResidue.heightFiberCost_eq
  have hextraCost : graphResidue.extraCost ≤
      Nat.log 2 prep.windowed.global.cells.card + 1 := by
    have hrawCard : rawResidue.cells.card ≤
        prep.windowed.global.cells.card :=
      Finset.card_le_card rawResidue.cells_subset
    have hlog : Nat.log 2 rawResidue.cells.card ≤
        Nat.log 2 prep.windowed.global.cells.card :=
      Nat.log_mono_right hrawCard
    rw [popularResidue.extraCost_eq, _hrawExtra, one_mul,
      popularResidue.logarithmicCost_eq]
    omega
  rcases wz1_lemma23_y_residue_prepared_package
      prep.windowed.global graphResidue localBins with ⟨graphPackage⟩
  have hcoord :
      ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hpaper : point ∈ residueShading.shading.union := by
      rwa [prep.shadow_union] at hpoint
    have hbox := shading_union_subset_axisBox hpaper
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  exact ⟨{
    localBins := localBins
    residue := graphResidue
    graph := graphPackage
    vertex_separation := graphPackage.vertex_separation
    vertex_bounds := graphPackage.vertex_bounds_of_coord
      prep.graphScale_one hcoord
  }, hheightFiberCost, hextraCost⟩

end Kakeya.Assouad
