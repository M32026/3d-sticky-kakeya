import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinAnchoredPreBin
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SecondStageSourceFloor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalRelativeMassBudget

/-!
# Quantitative scalar inputs from an anchored two-scale witness
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

namespace PureWZ2AnchoredSourceRelativeFineSelection

variable
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    (selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine)

theorem selected_count_mul_cube :
    (selected.selectedCells.card : ENNReal) *
        volume (wz1PaperGridCube rhoRequested.1 (0, 0, 0)) =
      volume fine.refined.union := by
  have hrho : 0 < rhoRequested.1 := coarse.coarse_extremal.delta_pos
  have hunion := fine.refined_cubical.union_eq_activeCells hrho
  rw [selected.selectedCells_eq]
  exact (wz1PaperGridCube_volume_biUnion hrho
    (wz1PaperActiveCells fine.refined hrho)).symm.trans
      (congrArg volume hunion.symm)

theorem balanced_volume_cross :
    volume selected.shading.union *
        volume coarse.croppedCoarseShading.union =
      volume fine.refined.union * volume coarse.refined.union := by
  have hsource := selected.volume_eq
  have hfirst := coarse.balanced.fine_union_volume
  have hcoarse :=
    coarse.balanced.toWZ1PaperBalancedCoverData.coarse_union_volume
      coarse.coarse_extremal.delta_pos
  rw [coarse.balanced.toWZ1PaperBalancedCoverData_activeCells] at hcoarse
  rw [hsource, hfirst, hcoarse, ← selected.selected_count_mul_cube]
  ring

theorem volume_relative_lower :
    Kakeya.realRpowENN delta (sigma + coarseLoss) *
        Kakeya.realRpowENN rhoRequested.1 (fineLoss + coarseLoss) ≤
      volume selected.shading.union := by
  let coarseVolume := volume coarse.croppedCoarseShading.union
  have hrho : 0 < rhoRequested.1 := coarse.coarse_extremal.delta_pos
  have hratio :
      Kakeya.realRpowENN rhoRequested.1 (fineLoss + coarseLoss) *
          coarseVolume ≤
        volume fine.refined.union := by
    calc
      _ ≤ Kakeya.realRpowENN rhoRequested.1 (fineLoss + coarseLoss) *
          Kakeya.realRpowENN rhoRequested.1 (sigma - coarseLoss) := by
            gcongr
            exact coarse.coarse_extremal.volume_upper
      _ = Kakeya.realRpowENN rhoRequested.1 (sigma + fineLoss) := by
            rw [← realRpowENN_add hrho]
            congr 1
            ring
      _ ≤ volume fine.refined.union := fine.refined_volume_lower
  have hscaled :
      (Kakeya.realRpowENN delta (sigma + coarseLoss) *
          Kakeya.realRpowENN rhoRequested.1 (fineLoss + coarseLoss)) *
          coarseVolume ≤
        volume selected.shading.union * coarseVolume := by
    calc
      _ = Kakeya.realRpowENN delta (sigma + coarseLoss) *
          (Kakeya.realRpowENN rhoRequested.1
            (fineLoss + coarseLoss) * coarseVolume) := by ring
      _ ≤ volume coarse.refined.union * volume fine.refined.union := by
            gcongr
            exact coarse.refined_volume_lower
      _ = volume selected.shading.union * coarseVolume := by
            rw [selected.balanced_volume_cross]
            ring
  have hcoarsePos : 0 < coarseVolume := by
    have hpowerPos :
        0 < Kakeya.realRpowENN rhoRequested.1 (sigma + coarseLoss) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hrho _)
    exact hpowerPos.trans_le coarse.coarse_volume_lower
  have hcoarseTop : coarseVolume ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp [Kakeya.realRpowENN])
      coarse.coarse_extremal.volume_upper
  exact (ENNReal.mul_le_mul_iff_right hcoarsePos.ne' hcoarseTop).mp <| by
    simpa [coarseVolume, mul_comm, mul_left_comm, mul_assoc] using hscaled

theorem second_source_floor_power :
    sqrtRequested.1 = Real.sqrt rhoRequested.1 →
    Kakeya.realRpowENN rhoRequested.1
        (3 / 2 + sigma / 2 + 3 * fineLoss / 2) ≤
      fine.balanced.cellMass := by
  intro hsqrt
  let scale := rhoRequested.1
  have hscale : 0 < scale := coarse.coarse_extremal.delta_pos
  have hcube :
      volume (wz1PaperGridCube sqrtRequested.1 (0, 0, 0)) =
        Kakeya.realRpowENN scale (3 / 2) := by
    rw [wz1PaperGridCube_volume_exact fine.coarse_extremal.delta_pos]
    rw [show sqrtRequested.1 = Real.sqrt scale by exact hsqrt]
    simp only [Kakeya.realRpowENN, Real.sqrt_eq_rpow]
    apply congrArg ENNReal.ofReal
    calc
      (Real.rpow scale (1 / 2)) ^ 3 =
          Real.rpow scale ((1 / 2 : ℝ) * (3 : ℕ)) :=
        (Real.rpow_mul_natCast hscale.le (1 / 2) 3).symm
      _ = Real.rpow scale (3 / 2) := by congr 1; ring
  have hcoarsePower :
      Kakeya.realRpowENN sqrtRequested.1 (sigma - fineLoss) =
        Kakeya.realRpowENN scale ((sigma - fineLoss) / 2) := by
    rw [show sqrtRequested.1 = Real.sqrt scale by exact hsqrt]
    simp only [Kakeya.realRpowENN, Real.sqrt_eq_rpow]
    apply congrArg ENNReal.ofReal
    calc
      (Real.rpow scale (1 / 2)).rpow (sigma - fineLoss) =
          Real.rpow scale ((1 / 2) * (sigma - fineLoss)) :=
        (Real.rpow_mul hscale.le (1 / 2) (sigma - fineLoss)).symm
      _ = Real.rpow scale ((sigma - fineLoss) / 2) := by
        congr 1
        ring
  let balanced := fine.balanced.toWZ1PaperBalancedCoverData
  let count : ENNReal := balanced.activeCells.card
  have hfine : Kakeya.realRpowENN scale (sigma + fineLoss) ≤
      volume fine.refined.union := fine.refined_volume_lower
  have hcoarse : volume fine.croppedCoarseShading.union ≤
      Kakeya.realRpowENN sqrtRequested.1 (sigma - fineLoss) :=
    fine.coarse_extremal.volume_upper
  have hfineEq := balanced.fine_union_volume
  have hcoarseEq := balanced.coarse_union_volume
    fine.coarse_extremal.delta_pos
  have hscaled :
      count *
          (Kakeya.realRpowENN scale (sigma + fineLoss) *
            volume (wz1PaperGridCube sqrtRequested.1 (0, 0, 0))) ≤
        count *
          (Kakeya.realRpowENN sqrtRequested.1 (sigma - fineLoss) *
            balanced.cellMass) := by
    calc
      _ = Kakeya.realRpowENN scale (sigma + fineLoss) *
          (count * volume
            (wz1PaperGridCube sqrtRequested.1 (0, 0, 0))) := by ring
      _ = Kakeya.realRpowENN scale (sigma + fineLoss) *
          volume fine.croppedCoarseShading.union := by rw [← hcoarseEq]
      _ ≤ volume fine.refined.union *
          Kakeya.realRpowENN sqrtRequested.1 (sigma - fineLoss) := by gcongr
      _ = count *
          (Kakeya.realRpowENN sqrtRequested.1 (sigma - fineLoss) *
            balanced.cellMass) := by rw [hfineEq]; ring
  have hcountZero : count ≠ 0 := by
    have hnonempty : balanced.activeCells.Nonempty := by
      by_contra hempty
      have hzero : volume fine.refined.union = 0 := by
        rw [hfineEq]
        simp [Finset.not_nonempty_iff_eq_empty.mp hempty]
      have hpositive :
          0 < Kakeya.realRpowENN scale (sigma + fineLoss) :=
        ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hscale _)
      rw [hzero] at hfine
      exact (not_le_of_gt hpositive) hfine
    change (balanced.activeCells.card : ENNReal) ≠ 0
    exact_mod_cast Finset.card_ne_zero.mpr hnonempty
  have hcountTop : count ≠ ⊤ := by simp [count]
  have hscaled' :
      (Kakeya.realRpowENN scale (sigma + fineLoss) *
          volume (wz1PaperGridCube sqrtRequested.1 (0, 0, 0))) * count ≤
        (Kakeya.realRpowENN sqrtRequested.1 (sigma - fineLoss) *
          balanced.cellMass) * count := by
    simpa [mul_comm] using hscaled
  have hraw :=
    (ENNReal.mul_le_mul_iff_left hcountZero hcountTop).mp hscaled'
  rw [hcube, hcoarsePower, ← realRpowENN_add hscale] at hraw
  let denominator :=
    Kakeya.realRpowENN scale ((sigma - fineLoss) / 2)
  have hdenomZero : denominator ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hscale _))
  have hdenomTop : denominator ≠ ⊤ := by
    simp [denominator, Kakeya.realRpowENN]
  have htarget :
      Kakeya.realRpowENN scale
            (3 / 2 + sigma / 2 + 3 * fineLoss / 2) * denominator =
        Kakeya.realRpowENN scale (sigma + fineLoss + 3 / 2) := by
    dsimp only [denominator]
    rw [← realRpowENN_add hscale]
    congr 1
    ring
  apply (ENNReal.mul_le_mul_iff_left hdenomZero hdenomTop).mp
  rw [htarget]
  have hcellMass : balanced.cellMass = fine.balanced.cellMass := rfl
  rw [hcellMass] at hraw
  simpa [denominator, scale, add_comm, add_left_comm, add_assoc, mul_comm]
    using hraw

end PureWZ2AnchoredSourceRelativeFineSelection

structure PureWZ2AnchoredCommonBinScalarData
    {sigma inputLoss delta coarseLoss fineLoss volumeLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    (preBin : PureWZ2AnchoredPreBinRhoHeightFamilyData selected)
    (B₀ : ENNReal) where
  X : ENNReal
  X_one : 1 ≤ X
  X_ne_top : X ≠ ⊤
  K : ℕ
  K_lower : X / 2 ≤ K
  K_upper : (K : ENNReal) ≤ X
  capacity :
    2 * B₀ *
        (X * PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
          sigma inputLoss delta rhoRequested.1) ≤
      volume selected.shading.union /
        (20 * pureWZ2CommonBinPreBinHeightCost rhoRequested.1)
  separated_graph_scalar :
    40 * pureWZ2CommonBinPreBinHeightCost rhoRequested.1 * (5 : ENNReal) *
          512 * Kakeya.realRpowENN (256 * rhoRequested.1)
            (1 + sigma / 2 + volumeLoss) ≤
      (K : ENNReal) * fine.balanced.cellMass

theorem pureWZ2_anchoredCommonBinScalarData
    {sigma inputLoss delta coarseLoss fineLoss volumeLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    (preBin : PureWZ2AnchoredPreBinRhoHeightFamilyData selected)
    (B₀ : ENNReal) (hB₀Pos : 0 < B₀) (hB₀Top : B₀ ≠ ⊤)
    (hpopular :
      4 * B₀ *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rhoRequested.1 ≤
        volume selected.shading.union /
          (20 * pureWZ2CommonBinPreBinHeightCost rhoRequested.1))
    (hgraph :
      (8 * B₀ *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rhoRequested.1) *
          (40 * pureWZ2CommonBinPreBinHeightCost rhoRequested.1 *
            (5 : ENNReal) * 512 *
            Kakeya.realRpowENN (256 * rhoRequested.1)
              (1 + sigma / 2 + volumeLoss)) ≤
        (volume selected.shading.union /
          (20 * pureWZ2CommonBinPreBinHeightCost rhoRequested.1)) *
          fine.balanced.cellMass) :
    Nonempty (PureWZ2AnchoredCommonBinScalarData
      (volumeLoss := volumeLoss) preBin B₀) := by
  let cellCap :=
    PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
      sigma inputLoss delta rhoRequested.1
  let denom : ENNReal := 4 * B₀ * cellCap
  let popular := volume selected.shading.union /
    (20 * pureWZ2CommonBinPreBinHeightCost rhoRequested.1)
  let X := popular / denom
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hrho : 0 < rhoRequested.1 :=
    source.extremal.delta_pos.trans_le rhoRequested.property.1
  have hcellCapPos : 0 < cellCap := by
    unfold cellCap
      PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
    exact ENNReal.mul_pos
      (ENNReal.mul_pos
        (ENNReal.mul_pos (by norm_num)
          (ENNReal.ofReal_pos.mpr
            (Real.rpow_pos_of_pos hdelta _)).ne').ne'
        (ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos hdelta _)).ne').ne'
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hrho _)).ne'
  have hcellCapTop : cellCap ≠ ⊤ := by
    unfold cellCap
      PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
      Kakeya.realRpowENN
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hdenomPos : 0 < denom := by
    dsimp only [denom]
    positivity
  have hdenomTop : denom ≠ ⊤ := by
    dsimp only [denom]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hB₀Top) hcellCapTop
  have hpopularTop : popular ≠ ⊤ := by
    dsimp only [popular]
    exact ENNReal.div_ne_top
      (by
        rw [selected.volume_eq]
        exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          coarse.balanced.cellMass_ne_top)
      (by
        exact (ENNReal.mul_pos (by norm_num)
          (pureWZ2CommonBinPreBinHeightCost_pos hrho
            rhoRequested.property.2).ne').ne')
  have hXOne : 1 ≤ X := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hdenomPos.ne') (Or.inl hdenomTop)).2
    simpa [denom, popular] using hpopular
  have hXTop : X ≠ ⊤ := ENNReal.div_ne_top hpopularTop hdenomPos.ne'
  have hXDenom : X * denom = popular :=
    ENNReal.div_mul_cancel hdenomPos.ne' hdenomTop
  rcases CommonBinRichSelection.exists_natCast_between_half X hXOne hXTop with
    ⟨K, hKLower, hKUpper⟩
  have hcapacity : 2 * B₀ * (X * cellCap) ≤ popular := by
    calc
      _ = X * (2 * B₀ * cellCap) := by ring
      _ ≤ X * (4 * B₀ * cellCap) := by gcongr; norm_num
      _ = X * denom := by rfl
      _ = popular := hXDenom
  have htwiceDenomPos : 0 < 2 * denom :=
    ENNReal.mul_pos (by norm_num) hdenomPos.ne'
  have htwiceDenomTop : 2 * denom ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hdenomTop
  have hseparated :
      40 * pureWZ2CommonBinPreBinHeightCost rhoRequested.1 *
            (5 : ENNReal) * 512 *
            Kakeya.realRpowENN (256 * rhoRequested.1)
              (1 + sigma / 2 + volumeLoss) ≤
        (K : ENNReal) * fine.balanced.cellMass := by
    calc
      _ ≤ (X / 2) * fine.balanced.cellMass := by
        apply (ENNReal.mul_le_mul_iff_right
          htwiceDenomPos.ne' htwiceDenomTop).mp
        calc
          (2 * denom) *
              (40 * pureWZ2CommonBinPreBinHeightCost rhoRequested.1 *
                (5 : ENNReal) * 512 *
                Kakeya.realRpowENN (256 * rhoRequested.1)
                  (1 + sigma / 2 + volumeLoss)) =
            (8 * B₀ * cellCap) *
              (40 * pureWZ2CommonBinPreBinHeightCost rhoRequested.1 *
                (5 : ENNReal) * 512 *
                Kakeya.realRpowENN (256 * rhoRequested.1)
                  (1 + sigma / 2 + volumeLoss)) := by
              dsimp only [denom]
              ring
          _ ≤ popular * fine.balanced.cellMass := by
              simpa only [popular, cellCap] using hgraph
          _ = (2 * denom) *
              ((X / 2) * fine.balanced.cellMass) := by
            calc
              popular * fine.balanced.cellMass =
                  (X * denom) * fine.balanced.cellMass := by rw [hXDenom]
              _ = (2 * denom) *
                  ((X / 2) * fine.balanced.cellMass) := by
                have hhalf : X / 2 * 2 = X :=
                  ENNReal.div_mul_cancel (by norm_num) (by norm_num)
                rw [show (2 * denom) *
                      ((X / 2) * fine.balanced.cellMass) =
                    (X / 2 * 2) * denom *
                      fine.balanced.cellMass by ring, hhalf]
      _ ≤ (K : ENNReal) * fine.balanced.cellMass := by gcongr
  exact ⟨{
    X := X
    X_one := hXOne
    X_ne_top := hXTop
    K := K
    K_lower := hKLower
    K_upper := hKUpper
    capacity := by simpa [cellCap, popular] using hcapacity
    separated_graph_scalar := hseparated
  }⟩

end Kakeya.Assouad

end
