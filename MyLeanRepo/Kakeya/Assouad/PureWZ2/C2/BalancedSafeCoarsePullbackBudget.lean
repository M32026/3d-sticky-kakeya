import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.BalancedSafeGraphGoodFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SelectedCoarseRegionSourcePreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalCrossStageBounds

/-!
# Aggregate ordinary graph supply through coarse-region pullback

This is the quantitative form of the order used in WZ Lemma 24: select each
fixed-line region on the first-sticky coarse carrier, then pull that exact
region back through the first balanced cover before running the source-slope
Lemma-23 graph.  The first balanced cell mass is therefore not paid twice.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- The structural lower bound matching the coarse-region pullback order.
The first sticky stage contributes one balanced cell floor and the volume of
its whole retained refinement; the second sticky stage contributes its
refined-volume floor and one balanced cell floor.  These are four distinct
inputs even when two of their power exponents happen to agree. -/
theorem PureWZ2SourceCarrierPreparation.coarse_pullback_graph_supply_lower
    {sigma inputLoss delta rho middleLoss stickyLoss secondEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (hrhoSmall : twoScale.rhoRequested.1 ≤ 1 / 12)
    (hsecondFraction :
      Kakeya.realRpowENN twoScale.rhoRequested.1 secondEta ≤
        wz2PaperPureRefinementFraction
          twoScale.rhoRequested.1 logExponent)
    (hcoarseSigma : twoScale.coarseLoss ≤ sigma) :
    Kakeya.realRpowENN rho
          (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
        Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
        Kakeya.realRpowENN twoScale.rhoRequested.1
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) *
        Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) ≤
      MeasureTheory.volume prepared.shadow.union *
        twoScale.fine.balanced.cellMass *
        MeasureTheory.volume twoScale.coarse.refined.union := by
  let cubeVolume : ENNReal :=
    MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))
  let coarseMass : ENNReal := twoScale.coarse.balanced.cellMass
  let fineMass : ENNReal := twoScale.fine.balanced.cellMass
  let coarsePower : ENNReal :=
    Kakeya.realRpowENN rho (sigma - twoScale.coarseLoss)
  let volumePower : ENNReal := Kakeya.realRpowENN rho
    (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta)
  let firstCellPower : ENNReal :=
    Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss)
  let secondCellPower : ENNReal := Kakeya.realRpowENN
    twoScale.rhoRequested.1
      (3 / 2 + sigma / 2 + 3 * stickyLoss / 2)
  let firstRefinedPower : ENNReal :=
    Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss)
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hcoarsePowerOne : coarsePower ≤ 1 := by
    dsimp only [coarsePower, Kakeya.realRpowENN]
    exact ENNReal.ofReal_le_one.mpr
      (Real.rpow_le_one hrho.le hrhoOne (by linarith))
  have hvolume : volumePower * coarseMass ≤
      MeasureTheory.volume prepared.shadow.union * cubeVolume := by
    simpa [volumePower, coarseMass, cubeVolume] using
      prepared.volume_mul_cube_lower hrhoSmall hsecondFraction
  have hfirstCell : firstCellPower * cubeVolume ≤ coarseMass := by
    calc
      firstCellPower * cubeVolume ≤ coarsePower * coarseMass := by
        simpa [firstCellPower, cubeVolume, coarsePower, coarseMass] using
          twoScale.first_cell_floor_raw
      _ ≤ 1 * coarseMass := by gcongr
      _ = coarseMass := one_mul _
  have hsecondCell : secondCellPower ≤ fineMass := by
    simpa [secondCellPower, fineMass] using
      twoScale.second_source_floor_power
  have hfirstRefined : firstRefinedPower ≤
      MeasureTheory.volume twoScale.coarse.refined.union := by
    simpa [firstRefinedPower] using twoScale.coarse.refined_volume_lower
  have hcubePos : 0 < cubeVolume := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_pos.mpr (pow_pos hrho 3)
  have hcancelZero : coarseMass * cubeVolume ≠ 0 :=
    mul_ne_zero twoScale.coarse.balanced.cellMass_pos.ne' hcubePos.ne'
  have hcancelTop : coarseMass * cubeVolume ≠ ⊤ :=
    ENNReal.mul_ne_top twoScale.coarse.balanced.cellMass_ne_top
      (by
        dsimp only [cubeVolume]
        rw [wz1PaperGridCube_volume_exact hrho]
        exact ENNReal.ofReal_ne_top)
  have hscaled :
      (volumePower * firstCellPower * secondCellPower * firstRefinedPower) *
          (coarseMass * cubeVolume) ≤
        (MeasureTheory.volume prepared.shadow.union * fineMass *
          MeasureTheory.volume twoScale.coarse.refined.union) *
            (coarseMass * cubeVolume) := by
    calc
      (volumePower * firstCellPower * secondCellPower * firstRefinedPower) *
            (coarseMass * cubeVolume) =
          (volumePower * coarseMass) *
            (firstCellPower * cubeVolume) *
              secondCellPower * firstRefinedPower := by ring
      _ ≤ (MeasureTheory.volume prepared.shadow.union * cubeVolume) *
            coarseMass * fineMass *
              MeasureTheory.volume twoScale.coarse.refined.union := by gcongr
      _ = (MeasureTheory.volume prepared.shadow.union * fineMass *
            MeasureTheory.volume twoScale.coarse.refined.union) *
          (coarseMass * cubeVolume) := by ring
  apply (ENNReal.mul_le_mul_iff_right hcancelZero hcancelTop).mp
  simpa [volumePower, firstCellPower, secondCellPower, firstRefinedPower,
    coarseMass, fineMass, mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- Sum the fixed-line Fubini estimates only after transporting every selected
coarse region to the actual original-source graph carrier. -/
theorem PureWZ2BalancedSafeAllBlockFamilyData.aggregate_volume_supply_le_via_coarse_pullback
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {firstPullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation firstPullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (data : PureWZ2BalancedSafeAllBlockFamilyData
      (normalEta := normalEta) safe) :
    MeasureTheory.volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
        MeasureTheory.volume twoScale.coarse.refined.union ≤
      2 * pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        (∑ block : {block // block ∈ safe.blocks},
          MeasureTheory.volume (data.pipeline block).prep.shadow.union) *
        MeasureTheory.volume
          twoScale.coarse.croppedCoarseShading.union := by
  have hlocal : ∀ block : {block // block ∈ safe.blocks},
      (MeasureTheory.volume (safe.blockWindow block).shading.union *
          twoScale.fine.balanced.cellMass) *
          MeasureTheory.volume twoScale.coarse.refined.union ≤
        pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          (MeasureTheory.volume (data.pipeline block).prep.shadow.union *
            MeasureTheory.volume
              twoScale.coarse.croppedCoarseShading.union) := by
    intro block
    let pipeline := data.pipeline block
    rcases pipeline.residue.retainCoarseCarrier with ⟨coarseCarrier⟩
    rcases coarseCarrier.pullbackToSource with ⟨sourcePullback⟩
    have hsupply := coarseCarrier.sourceResidue_volume_supply_le
      sourcePullback pipeline.retained
    rw [data.volumeSupply_eq block, ← pipeline.shadow_union] at hsupply
    exact hsupply
  have hphase := safe.volume_half
  have hsum :
      (∑ block : {block // block ∈ safe.blocks},
        ((MeasureTheory.volume (safe.blockWindow block).shading.union *
            twoScale.fine.balanced.cellMass) *
          MeasureTheory.volume twoScale.coarse.refined.union)) ≤
        ∑ block : {block // block ∈ safe.blocks},
          (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
            (MeasureTheory.volume (data.pipeline block).prep.shadow.union *
              MeasureTheory.volume
                twoScale.coarse.croppedCoarseShading.union)) := by
    exact Finset.sum_le_sum fun block _ => hlocal block
  calc
    MeasureTheory.volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
        MeasureTheory.volume twoScale.coarse.refined.union ≤
      (2 * ∑ block : {block // block ∈ safe.blocks},
          MeasureTheory.volume (safe.blockWindow block).shading.union) *
        twoScale.fine.balanced.cellMass *
          MeasureTheory.volume twoScale.coarse.refined.union := by gcongr
    _ = 2 * ((∑ block : {block // block ∈ safe.blocks},
          MeasureTheory.volume (safe.blockWindow block).shading.union) *
        twoScale.fine.balanced.cellMass *
          MeasureTheory.volume twoScale.coarse.refined.union) := by ac_rfl
    _ = 2 * ∑ block : {block // block ∈ safe.blocks},
        ((MeasureTheory.volume (safe.blockWindow block).shading.union *
            twoScale.fine.balanced.cellMass) *
          MeasureTheory.volume twoScale.coarse.refined.union) := by
      rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ 2 * ∑ block : {block // block ∈ safe.blocks},
        (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          (MeasureTheory.volume (data.pipeline block).prep.shadow.union *
            MeasureTheory.volume
              twoScale.coarse.croppedCoarseShading.union)) := by
      exact mul_le_mul_left' hsum 2
    _ = 2 * pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        (∑ block : {block // block ∈ safe.blocks},
          MeasureTheory.volume (data.pipeline block).prep.shadow.union) *
        MeasureTheory.volume
          twoScale.coarse.croppedCoarseShading.union := by
      rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- The exact pullback supply converts the paper power budget into graph
popularity.  The volume of the first-stage coarse carrier is kept as a common
factor until the final cancellation, so the first balanced cell mass is not
introduced a second time. -/
theorem PureWZ2BalancedSafeAllBlockFamilyData.goodGraphBudget_of_coarse_pullback_power
    {sigma inputLoss delta rho middleLoss stickyLoss secondEta normalEta
      volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {firstPullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation firstPullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (data : PureWZ2BalancedSafeAllBlockFamilyData
      (normalEta := normalEta) safe)
    (hrhoSmall : twoScale.rhoRequested.1 ≤ 1 / 12)
    (hsecondFraction :
      Kakeya.realRpowENN twoScale.rhoRequested.1 secondEta ≤
        wz2PaperPureRefinementFraction
          twoScale.rhoRequested.1 logExponent)
    (hcoarseSigma : twoScale.coarseLoss ≤ sigma)
    (hpower :
      4 * pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          (safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss) *
          MeasureTheory.volume
            twoScale.coarse.croppedCoarseShading.union ≤
        Kakeya.realRpowENN rho
            (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss)) :
    2 * ((safe.blocks.card : ENNReal) *
        Kakeya.realRpowENN (256 * rho)
          (1 + sigma / 2 + volumeLoss)) ≤
      ∑ block : {block // block ∈ safe.blocks},
        MeasureTheory.volume (data.pipeline block).prep.shadow.union := by
  let cost : ENNReal :=
    pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss
  let threshold : ENNReal := Kakeya.realRpowENN (256 * rho)
    (1 + sigma / 2 + volumeLoss)
  let coarseVolume : ENNReal := MeasureTheory.volume
    twoScale.coarse.croppedCoarseShading.union
  let common : ENNReal := 2 * cost * coarseVolume
  have hstruct := prepared.coarse_pullback_graph_supply_lower
    hrhoSmall hsecondFraction hcoarseSigma
  have hall := data.aggregate_volume_supply_le_via_coarse_pullback
  have hscaled :
      common * (2 * ((safe.blocks.card : ENNReal) * threshold)) ≤
        common * ∑ block : {block // block ∈ safe.blocks},
          MeasureTheory.volume (data.pipeline block).prep.shadow.union := by
    calc
      common * (2 * ((safe.blocks.card : ENNReal) * threshold)) =
          4 * cost * (safe.blocks.card : ENNReal) * threshold *
            coarseVolume := by
        simp only [common]
        ring
      _ ≤ Kakeya.realRpowENN rho
            (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) := by
        simpa [cost, threshold, coarseVolume, mul_assoc] using hpower
      _ ≤ MeasureTheory.volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          MeasureTheory.volume twoScale.coarse.refined.union := hstruct
      _ ≤ 2 * cost *
          (∑ block : {block // block ∈ safe.blocks},
            MeasureTheory.volume (data.pipeline block).prep.shadow.union) *
          coarseVolume := by
        simpa [cost, coarseVolume, mul_assoc] using hall
      _ = common * ∑ block : {block // block ∈ safe.blocks},
          MeasureTheory.volume (data.pipeline block).prep.shadow.union := by
        simp only [common]
        ring
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hcostPos : 0 < cost := by
    dsimp only [cost]
    exact pureWZ2SourceHorizontalVolumeCost_pos
      hrho source.extremal.delta_pos
  have hcoarseVolumePos : 0 < coarseVolume := by
    have hpowerPos : 0 < Kakeya.realRpowENN
        twoScale.rhoRequested.1 (sigma + twoScale.coarseLoss) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos
        twoScale.coarseGrains.extremal.delta_pos _)
    exact hpowerPos.trans_le (by
      simpa [coarseVolume] using twoScale.coarse.coarse_volume_lower)
  have hcommonZero : common ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) hcostPos.ne') hcoarseVolumePos.ne'
  have hcostTop : cost ≠ ⊤ := by
    dsimp only [cost]
    exact pureWZ2SourceHorizontalVolumeCost_ne_top
      rho delta sigma inputLoss
  have hcommonTop : common ≠ ⊤ := by
    have hcoarseVolumeTop : coarseVolume ≠ ⊤ := by
      have hupperTop : Kakeya.realRpowENN
          twoScale.rhoRequested.1
            (sigma - twoScale.coarseLoss) ≠ ⊤ := by
        simp [Kakeya.realRpowENN]
      exact ne_top_of_le_ne_top hupperTop
        (by simpa [coarseVolume] using
          twoScale.coarse.coarse_extremal.volume_upper)
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hcostTop)
      hcoarseVolumeTop
  simpa only [threshold] using
    (ENNReal.mul_le_mul_iff_right hcommonZero hcommonTop).mp hscaled

namespace PureWZ2BalancedSafeGraphGoodBlockFamilyData

/-- Continue the exact coarse-pullback aggregate supply through graph-volume
popularity and the per-graph height popularity step. -/
theorem aggregate_height_mass_bound_via_coarse_pullback
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {firstPullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation firstPullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {all : PureWZ2BalancedSafeAllBlockFamilyData
      (normalEta := normalEta) safe}
    (data : PureWZ2BalancedSafeGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (theoremEta := theoremEta) all volumeLoss)
    (hbad :
      2 * ((safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) ≤
        ∑ block : {block // block ∈ safe.blocks},
          MeasureTheory.volume (all.pipeline block).prep.shadow.union) :
    MeasureTheory.volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          MeasureTheory.volume twoScale.coarse.refined.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      4 * pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho data.extraLoss *
        (∑ index : Fin data.outputs.indexCount,
          (data.outputs.rich index).heightLift.shading.mass) *
        MeasureTheory.volume
          twoScale.coarse.croppedCoarseShading.union := by
  let cost : ENNReal :=
    pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss
  let heightCost : ENNReal :=
    PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
      rho data.extraLoss
  let multiplicity : ENNReal := twoScale.coarse.fineMultiplicity
  let floor : ENNReal := pureWZ2SourceHorizontalRichFloor rho finalLoss
  let coarseVolume : ENNReal := MeasureTheory.volume
    twoScale.coarse.croppedCoarseShading.union
  let allGraph := ∑ block : {block // block ∈ safe.blocks},
    MeasureTheory.volume (all.pipeline block).prep.shadow.union
  let goodGraph := ∑ block ∈
      pureWZ2GoodBalancedSafeGraphBlocks all volumeLoss,
    MeasureTheory.volume (all.pipeline block).prep.shadow.union
  have hall : MeasureTheory.volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          MeasureTheory.volume twoScale.coarse.refined.union ≤
        2 * cost * allGraph * coarseVolume := by
    simpa [cost, allGraph, coarseVolume] using
      all.aggregate_volume_supply_le_via_coarse_pullback
  have hgood : allGraph ≤ 2 * goodGraph := by
    simpa [allGraph, goodGraph] using all.goodGraphBlocks_retains_half hbad
  have hgoodIndexed : goodGraph =
      ∑ index : Fin data.outputs.indexCount,
        MeasureTheory.volume (data.outputs.pipeline index).prep.shadow.union := by
    symm
    dsimp only [goodGraph]
    apply Finset.sum_bij (fun index _ => data.safeBlock index)
    · intro index _
      exact data.block_mem index
    · intro first _ second _ heq
      exact data.safeBlock_injective heq
    · intro block hblock
      rcases data.block_surjective block hblock with ⟨index, heq⟩
      exact ⟨index, Finset.mem_univ index, heq⟩
    · intro index _
      rw [data.pipeline_eq index]
  have hlocal :
      (∑ index : Fin data.outputs.indexCount,
          MeasureTheory.volume (data.outputs.pipeline index).prep.shadow.union) *
          multiplicity * floor ≤
        heightCost * ∑ index : Fin data.outputs.indexCount,
          (data.outputs.rich index).heightLift.shading.mass := by
    calc
      _ = ∑ index : Fin data.outputs.indexCount,
          (MeasureTheory.volume
              (data.outputs.pipeline index).prep.shadow.union *
            multiplicity * floor) := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ ∑ index : Fin data.outputs.indexCount,
          heightCost *
            (data.outputs.rich index).heightLift.shading.mass := by
        exact Finset.sum_le_sum fun index _ => by
          simpa [heightCost, multiplicity, floor] using
            data.graph_height_mass_bound_uniform index
      _ = heightCost * ∑ index : Fin data.outputs.indexCount,
          (data.outputs.rich index).heightLift.shading.mass := by
        rw [Finset.mul_sum]
  calc
    MeasureTheory.volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          MeasureTheory.volume twoScale.coarse.refined.union *
          multiplicity * floor ≤
        (2 * cost * allGraph * coarseVolume) *
          multiplicity * floor := by gcongr
    _ ≤ (2 * cost * (2 * goodGraph) * coarseVolume) *
          multiplicity * floor := by gcongr
    _ = 4 * cost * (goodGraph * multiplicity * floor) * coarseVolume := by ring
    _ = 4 * cost *
        ((∑ index : Fin data.outputs.indexCount,
          MeasureTheory.volume (data.outputs.pipeline index).prep.shadow.union) *
            multiplicity * floor) * coarseVolume := by rw [hgoodIndexed]
    _ ≤ 4 * cost *
        (heightCost * ∑ index : Fin data.outputs.indexCount,
          (data.outputs.rich index).heightLift.shading.mass) *
        coarseVolume := by gcongr
    _ = 4 * pureWZ2SourceHorizontalVolumeCost
          rho delta sigma inputLoss *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho data.extraLoss *
        (∑ index : Fin data.outputs.indexCount,
          (data.outputs.rich index).heightLift.shading.mass) *
        MeasureTheory.volume
          twoScale.coarse.croppedCoarseShading.union := by
      simp only [cost, heightCost, coarseVolume]
      ring

/-- Select the final mod-64 residue only after the exact coarse-pullback graph
and per-block height popularity steps. -/
theorem selectResidue_height_mass_bound_via_coarse_pullback
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {firstPullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation firstPullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {all : PureWZ2BalancedSafeAllBlockFamilyData
      (normalEta := normalEta) safe}
    (data : PureWZ2BalancedSafeGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (theoremEta := theoremEta) all volumeLoss)
    (hbad :
      2 * ((safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) ≤
        ∑ block : {block // block ∈ safe.blocks},
          MeasureTheory.volume (all.pipeline block).prep.shadow.union) :
    ∃ residueData : PureWZ2SourceHorizontalBlockResidueData data.outputs,
      MeasureTheory.volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          MeasureTheory.volume twoScale.coarse.refined.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
        256 * pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho data.extraLoss *
          residueData.family.shading.mass *
          MeasureTheory.volume
            twoScale.coarse.croppedCoarseShading.union := by
  rcases data.outputs.selectResidue with ⟨residueData⟩
  refine ⟨residueData,
    (data.aggregate_height_mass_bound_via_coarse_pullback hbad).trans ?_⟩
  calc
    4 * pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho data.extraLoss *
          (∑ index : Fin data.outputs.indexCount,
            (data.outputs.rich index).heightLift.shading.mass) *
          MeasureTheory.volume
            twoScale.coarse.croppedCoarseShading.union ≤
        4 * pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho data.extraLoss *
          (64 * residueData.family.shading.mass) *
          MeasureTheory.volume
            twoScale.coarse.croppedCoarseShading.union := by
      gcongr
      exact residueData.total_mass_le
    _ = 256 * pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho data.extraLoss *
          residueData.family.shading.mass *
          MeasureTheory.volume
            twoScale.coarse.croppedCoarseShading.union := by ring

end PureWZ2BalancedSafeGraphGoodBlockFamilyData

end Kakeya.Assouad

end
