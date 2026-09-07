import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalCrossStageBounds

/-!
# Same-relative-density mass budget for the source-horizontal step

The two balanced covers are used in the order of WZ Lemma 5.5.  The second
refinement supplies the number of retained side-`rho` cells, while the first
refinement supplies their common incidence mass.  Both identities contain
the same physical side-`rho` cube volume, which is cancelled before the
point-multiplicity band is used.  Consequently the final source-height lift
pays no additional balanced-cell-mass factor.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- Exact relative volume retained by the two nested sticky refinements.

This is the ratio form of the two balanced-cover identities.  The final
coarse volume is cancelled, so the estimate pays only the two refinement
losses `stickyLoss + coarseLoss`; it does not replace the ratio by separate
absolute cell-volume floors. -/
theorem PureWZ2SourceCarrierPreparation.pullback_volume_relative_lower
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) :
    Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
        Kakeya.realRpowENN rho (stickyLoss + twoScale.coarseLoss) ≤
      MeasureTheory.volume prepared.shadow.union := by
  let coarseVolume : ENNReal :=
    MeasureTheory.volume twoScale.coarse.croppedCoarseShading.union
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hrhoEq : twoScale.rhoRequested.1 = rho :=
    twoScale.rhoRequested_eq
  have hratio :
      Kakeya.realRpowENN rho (stickyLoss + twoScale.coarseLoss) *
          coarseVolume ≤
        MeasureTheory.volume twoScale.fine.refined.union := by
    calc
      Kakeya.realRpowENN rho (stickyLoss + twoScale.coarseLoss) *
            coarseVolume ≤
          Kakeya.realRpowENN rho (stickyLoss + twoScale.coarseLoss) *
            Kakeya.realRpowENN rho (sigma - twoScale.coarseLoss) := by
        gcongr
        simpa [coarseVolume, hrhoEq] using
          twoScale.coarse.coarse_extremal.volume_upper
      _ = Kakeya.realRpowENN rho (sigma + stickyLoss) := by
        rw [← realRpowENN_add hrho]
        congr 1
        ring
      _ ≤ MeasureTheory.volume twoScale.fine.refined.union := by
        simpa [hrhoEq] using twoScale.fine.refined_volume_lower
  have hscaled :
      (Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          Kakeya.realRpowENN rho (stickyLoss + twoScale.coarseLoss)) *
          coarseVolume ≤
        MeasureTheory.volume prepared.shadow.union * coarseVolume := by
    calc
      _ = Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          (Kakeya.realRpowENN rho
            (stickyLoss + twoScale.coarseLoss) * coarseVolume) := by ring
      _ ≤ MeasureTheory.volume twoScale.coarse.refined.union *
          MeasureTheory.volume twoScale.fine.refined.union := by
        gcongr
        exact twoScale.coarse.refined_volume_lower
      _ = MeasureTheory.volume prepared.shadow.union * coarseVolume := by
        rw [prepared.shadow_union, pullback.balanced_volume_cross]
        ring
  have hcoarsePos : 0 < coarseVolume := by
    have hpowerPos : 0 < Kakeya.realRpowENN rho
        (sigma + twoScale.coarseLoss) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hrho _)
    exact hpowerPos.trans_le (by
      simpa [coarseVolume, hrhoEq] using twoScale.coarse.coarse_volume_lower)
  have hcoarseTop : coarseVolume ≠ ⊤ := by
    have hupper : coarseVolume ≤
        Kakeya.realRpowENN rho (sigma - twoScale.coarseLoss) := by
      simpa [coarseVolume, hrhoEq] using
        twoScale.coarse.coarse_extremal.volume_upper
    exact ne_top_of_le_ne_top (by simp [Kakeya.realRpowENN]) hupper
  apply (ENNReal.mul_le_mul_iff_right hcoarsePos.ne' hcoarseTop).mp
  simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- Exact relative indexed mass retained by the two sticky stages.  This is
the mass analogue of `pullback_volume_relative_lower` and is the paper's
same-relative-density input for the final height-only lift. -/
theorem PureWZ2SourceCarrierPreparation.pullback_mass_relative_lower
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) :
    wz2PaperPureRefinementFraction delta logExponent * source.shading.mass *
        Kakeya.realRpowENN rho (stickyLoss + twoScale.coarseLoss) ≤
      pullback.shading.mass := by
  let coarseVolume : ENNReal :=
    MeasureTheory.volume twoScale.coarse.croppedCoarseShading.union
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hrhoEq : twoScale.rhoRequested.1 = rho :=
    twoScale.rhoRequested_eq
  have hratio :
      Kakeya.realRpowENN rho (stickyLoss + twoScale.coarseLoss) *
          coarseVolume ≤
        MeasureTheory.volume twoScale.fine.refined.union := by
    calc
      Kakeya.realRpowENN rho (stickyLoss + twoScale.coarseLoss) *
            coarseVolume ≤
          Kakeya.realRpowENN rho (stickyLoss + twoScale.coarseLoss) *
            Kakeya.realRpowENN rho (sigma - twoScale.coarseLoss) := by
        gcongr
        simpa [coarseVolume, hrhoEq] using
          twoScale.coarse.coarse_extremal.volume_upper
      _ = Kakeya.realRpowENN rho (sigma + stickyLoss) := by
        rw [← realRpowENN_add hrho]
        congr 1
        ring
      _ ≤ MeasureTheory.volume twoScale.fine.refined.union := by
        simpa [hrhoEq] using twoScale.fine.refined_volume_lower
  have hscaled :
      (wz2PaperPureRefinementFraction delta logExponent *
          source.shading.mass *
          Kakeya.realRpowENN rho
            (stickyLoss + twoScale.coarseLoss)) * coarseVolume ≤
        pullback.shading.mass * coarseVolume := by
    calc
      _ = (wz2PaperPureRefinementFraction delta logExponent *
            source.shading.mass) *
          (Kakeya.realRpowENN rho
            (stickyLoss + twoScale.coarseLoss) * coarseVolume) := by ring
      _ ≤ twoScale.coarse.refined.mass *
          MeasureTheory.volume twoScale.fine.refined.union := by
        gcongr
        exact twoScale.coarse.retained_mass
      _ = pullback.shading.mass * coarseVolume := by
        rw [pullback.balanced_mass_cross]
  have hcoarsePos : 0 < coarseVolume := by
    have hpowerPos : 0 < Kakeya.realRpowENN rho
        (sigma + twoScale.coarseLoss) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hrho _)
    exact hpowerPos.trans_le (by
      simpa [coarseVolume, hrhoEq] using twoScale.coarse.coarse_volume_lower)
  have hcoarseTop : coarseVolume ≠ ⊤ := by
    have hupper : coarseVolume ≤
        Kakeya.realRpowENN rho (sigma - twoScale.coarseLoss) := by
      simpa [coarseVolume, hrhoEq] using
        twoScale.coarse.coarse_extremal.volume_upper
    exact ne_top_of_le_ne_top (by simp [Kakeya.realRpowENN]) hupper
  apply (ENNReal.mul_le_mul_iff_right hcoarsePos.ne' hcoarseTop).mp
  simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- The exact pullback has the first sticky multiplicity band, so its relative
indexed-mass lower bound can be expressed on the geometric carrier volume. -/
theorem PureWZ2SourceCarrierPreparation.relative_mass_via_multiplicity_lower
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) :
    wz2PaperPureRefinementFraction delta logExponent *
          (Kakeya.realRpowENN delta inputLoss *
            (wz1PaperBodyFamily source.family).mass) *
        Kakeya.realRpowENN rho (stickyLoss + twoScale.coarseLoss) ≤
      2 * (MeasureTheory.volume prepared.shadow.union *
        (twoScale.coarse.fineMultiplicity : ENNReal)) := by
  have hsource : Kakeya.realRpowENN delta inputLoss *
        (wz1PaperBodyFamily source.family).mass ≤ source.shading.mass :=
    source.extremal.dense
  have hpullback := prepared.pullback_mass_relative_lower
  have hupper : pullback.shading.mass ≤
      2 * (MeasureTheory.volume prepared.shadow.union *
        (twoScale.coarse.fineMultiplicity : ENNReal)) := by
    rw [pullback.mass_eq, prepared.shadow_union, pullback.volume_eq]
    calc
      (pullback.selectedCells.card : ENNReal) *
            twoScale.coarse.balanced.incidenceMass ≤
          (pullback.selectedCells.card : ENNReal) *
            ((2 * twoScale.coarse.fineMultiplicity : ENNReal) *
              twoScale.coarse.balanced.cellMass) := by
        gcongr
        exact twoScale.coarse.balanced_incidenceMass_band.2
      _ = 2 * (((pullback.selectedCells.card : ENNReal) *
            twoScale.coarse.balanced.cellMass) *
          (twoScale.coarse.fineMultiplicity : ENNReal)) := by ring
  calc
    wz2PaperPureRefinementFraction delta logExponent *
          (Kakeya.realRpowENN delta inputLoss *
            (wz1PaperBodyFamily source.family).mass) *
        Kakeya.realRpowENN rho (stickyLoss + twoScale.coarseLoss) ≤
      wz2PaperPureRefinementFraction delta logExponent *
          source.shading.mass *
        Kakeya.realRpowENN rho (stickyLoss + twoScale.coarseLoss) := by gcongr
    _ ≤ pullback.shading.mass := hpullback
    _ ≤ 2 * (MeasureTheory.volume prepared.shadow.union *
        (twoScale.coarse.fineMultiplicity : ENNReal)) := hupper

/--
The paper's same-relative-density cancellation for the original source
family.  This is the mass counterpart of pulling a subcollection of the
second coarse cover back through the first balanced cover.
-/
theorem PureWZ2SourceCarrierPreparation.relative_mass_structural_lower
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
        (wz2PaperPureRefinementFraction delta logExponent *
          (Kakeya.realRpowENN delta inputLoss *
            (wz1PaperBodyFamily source.family).mass)) ≤
      2 * (MeasureTheory.volume prepared.shadow.union *
        (twoScale.coarse.fineMultiplicity : ENNReal)) := by
  let cubeVolume : ENNReal :=
    MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))
  let selectedCount : ENNReal := pullback.selectedCells.card
  let incidenceMass : ENNReal := twoScale.coarse.balanced.incidenceMass
  let cellMass : ENNReal := twoScale.coarse.balanced.cellMass
  let multiplicity : ENNReal := twoScale.coarse.fineMultiplicity
  let coarsePower : ENNReal :=
    Kakeya.realRpowENN rho (sigma - twoScale.coarseLoss)
  let volumePower : ENNReal := Kakeya.realRpowENN rho
    (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta)
  let bodySupply : ENNReal :=
    wz2PaperPureRefinementFraction delta logExponent *
      (Kakeya.realRpowENN delta inputLoss *
        (wz1PaperBodyFamily source.family).mass)
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
  have hvolumePower : volumePower ≤
      MeasureTheory.volume twoScale.fine.refined.union := by
    simpa [volumePower, twoScale.rhoRequested_eq] using
      twoScale.second_refined_volume_power hrhoSmall hsecondFraction
  have hincidence : bodySupply * cubeVolume ≤
      coarsePower * incidenceMass := by
    simpa [bodySupply, cubeVolume, coarsePower, twoScale.rhoRequested_eq]
      using twoScale.first_incidence_body_floor
  have hcountCube : selectedCount * cubeVolume =
      MeasureTheory.volume twoScale.fine.refined.union := by
    simpa [selectedCount, cubeVolume] using
      pullback.selected_count_mul_coarse_volume
  have hcubePos : 0 < cubeVolume := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_pos.mpr (pow_pos hrho 3)
  have hcubeTop : cubeVolume ≠ ⊤ := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_ne_top
  have hscaled :
      (volumePower * bodySupply) * cubeVolume ≤
        (coarsePower * pullback.shading.mass) * cubeVolume := by
    calc
      (volumePower * bodySupply) * cubeVolume =
          volumePower * (bodySupply * cubeVolume) := by ring
      _ ≤ MeasureTheory.volume twoScale.fine.refined.union *
          (coarsePower * incidenceMass) := by gcongr
      _ = (selectedCount * cubeVolume) *
          (coarsePower * incidenceMass) := by rw [hcountCube]
      _ = (coarsePower * (selectedCount * incidenceMass)) *
          cubeVolume := by ring
      _ = (coarsePower * pullback.shading.mass) * cubeVolume := by
        rw [pullback.mass_eq]
  have hrelative : volumePower * bodySupply ≤
      coarsePower * pullback.shading.mass :=
    (ENNReal.mul_le_mul_iff_right hcubePos.ne' hcubeTop).mp (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
  have hpullbackMass : pullback.shading.mass ≤
      2 * (MeasureTheory.volume prepared.shadow.union * multiplicity) := by
    rw [pullback.mass_eq, prepared.shadow_union, pullback.volume_eq]
    calc
      selectedCount * incidenceMass ≤
          selectedCount * ((2 * multiplicity) * cellMass) := by
        gcongr
        simpa [incidenceMass, multiplicity, cellMass, mul_assoc] using
          twoScale.coarse.balanced_incidenceMass_band.2
      _ = 2 * ((selectedCount * cellMass) * multiplicity) := by ring
  calc
    Kakeya.realRpowENN rho
          (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
        (wz2PaperPureRefinementFraction delta logExponent *
          (Kakeya.realRpowENN delta inputLoss *
            (wz1PaperBodyFamily source.family).mass)) =
        volumePower * bodySupply := rfl
    _ ≤ coarsePower * pullback.shading.mass := hrelative
    _ ≤ 1 * pullback.shading.mass := by gcongr
    _ ≤ 2 * (MeasureTheory.volume prepared.shadow.union *
        (twoScale.coarse.fineMultiplicity : ENNReal)) := by
      simpa [multiplicity] using hpullbackMass

/--
Convert the same-relative-density estimate into the exact weighted supply
needed by the final ordinary height lift.  The numerical hypothesis contains
only powers and explicit finite losses: the source body mass occurs once, in
`relative_mass_structural_lower`, and is not reused as a second independent
structural supply.
-/
theorem PureWZ2SourceCarrierPreparation.final_mass_of_relative_budget
    {sigma inputLoss delta rho middleLoss stickyLoss secondEta finalLoss
      structuralLoss : ℝ}
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
    (hcoarseSigma : twoScale.coarseLoss ≤ sigma)
    (cost : ENNReal)
    (hpower :
      2 * cost * Kakeya.realRpowENN delta structuralLoss ≤
        Kakeya.realRpowENN rho
            (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
          wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta inputLoss *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0)) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss) :
    cost *
          (Kakeya.realRpowENN delta structuralLoss *
            (wz1PaperBodyFamily source.family).mass) ≤
      MeasureTheory.volume prepared.shadow.union *
        twoScale.fine.balanced.cellMass *
        twoScale.coarse.balanced.cellMass *
        (twoScale.coarse.fineMultiplicity : ENNReal) *
        pureWZ2SourceHorizontalRichFloor rho finalLoss := by
  let bodyMass : ENNReal := (wz1PaperBodyFamily source.family).mass
  let volumePower : ENNReal := Kakeya.realRpowENN rho
    (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta)
  let refinement : ENNReal :=
    wz2PaperPureRefinementFraction delta logExponent
  let inputPower : ENNReal := Kakeya.realRpowENN delta inputLoss
  let coarseMass : ENNReal := twoScale.coarse.balanced.cellMass
  let fineMass : ENNReal := twoScale.fine.balanced.cellMass
  let firstCellPower : ENNReal :=
    Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss)
  let secondCellPower : ENNReal := Kakeya.realRpowENN
    twoScale.rhoRequested.1 (3 / 2 + sigma / 2 + 3 * stickyLoss / 2)
  let cubeVolume : ENNReal :=
    MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))
  let multiplicity : ENNReal := twoScale.coarse.fineMultiplicity
  let richFloor : ENNReal :=
    pureWZ2SourceHorizontalRichFloor rho finalLoss
  let target : ENNReal := MeasureTheory.volume prepared.shadow.union *
    fineMass * coarseMass * multiplicity * richFloor
  have hrelative : volumePower * (refinement * (inputPower * bodyMass)) ≤
      2 * (MeasureTheory.volume prepared.shadow.union * multiplicity) := by
    simpa [volumePower, refinement, inputPower, bodyMass, multiplicity] using
      prepared.relative_mass_structural_lower
        hrhoSmall hsecondFraction hcoarseSigma
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hcoarsePowerOne :
      Kakeya.realRpowENN rho (sigma - twoScale.coarseLoss) ≤ 1 := by
    exact ENNReal.ofReal_le_one.mpr
      (Real.rpow_le_one hrho.le hrhoOne (by linarith))
  have hfirstCell : firstCellPower * cubeVolume ≤ coarseMass := by
    calc
      firstCellPower * cubeVolume ≤
          Kakeya.realRpowENN rho (sigma - twoScale.coarseLoss) *
            coarseMass := by
        simpa [firstCellPower, cubeVolume] using
          twoScale.first_cell_floor_raw
      _ ≤ 1 * coarseMass := by gcongr
      _ = coarseMass := one_mul _
  have hsecondCell : secondCellPower ≤ fineMass := by
    simpa [secondCellPower, fineMass] using
      twoScale.second_source_floor_power
  have hscaled :
      (2 : ENNReal) * (cost *
          (Kakeya.realRpowENN delta structuralLoss * bodyMass)) ≤
        (2 : ENNReal) * target := by
    calc
      (2 : ENNReal) * (cost *
          (Kakeya.realRpowENN delta structuralLoss * bodyMass)) =
        (2 * cost * Kakeya.realRpowENN delta structuralLoss) * bodyMass := by
          ring
      _ ≤ (volumePower * refinement * inputPower *
          firstCellPower * cubeVolume * secondCellPower * richFloor) *
          bodyMass := by
        gcongr
      _ = (volumePower * (refinement * (inputPower * bodyMass))) *
          ((firstCellPower * cubeVolume) * secondCellPower * richFloor) := by
        ring
      _ ≤ (2 * (MeasureTheory.volume prepared.shadow.union * multiplicity)) *
          ((firstCellPower * cubeVolume) * secondCellPower * richFloor) := by
        gcongr
      _ ≤ (2 * (MeasureTheory.volume prepared.shadow.union * multiplicity)) *
          (coarseMass * fineMass * richFloor) := by gcongr
      _ = (2 : ENNReal) * target := by
        simp only [target]
        ring
  have htwoZero : (2 : ENNReal) ≠ 0 := by norm_num
  have htwoTop : (2 : ENNReal) ≠ ⊤ := by norm_num
  have hcancel :=
    (ENNReal.mul_le_mul_iff_right htwoZero htwoTop).mp hscaled
  simpa [target, bodyMass, fineMass, coarseMass, multiplicity, richFloor,
    mul_comm, mul_left_comm, mul_assoc] using hcancel

/-- Same-relative-density lower bound in the exact coarse-pullback form.
The first-stage coarse carrier volume is retained as the common factor which
will be cancelled only after the graph and height popularity estimates. -/
theorem PureWZ2SourceCarrierPreparation.final_mass_of_coarse_pullback_relative_budget
    {sigma inputLoss delta rho middleLoss stickyLoss secondEta finalLoss
      structuralLoss : ℝ}
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
    (hcoarseSigma : twoScale.coarseLoss ≤ sigma)
    (cost : ENNReal)
    (hpower :
      2 * cost * Kakeya.realRpowENN delta structuralLoss *
          MeasureTheory.volume
            twoScale.coarse.croppedCoarseShading.union ≤
        Kakeya.realRpowENN rho
            (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
          wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta inputLoss *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss) :
    cost *
          (Kakeya.realRpowENN delta structuralLoss *
            (wz1PaperBodyFamily source.family).mass) *
        MeasureTheory.volume twoScale.coarse.croppedCoarseShading.union ≤
      MeasureTheory.volume prepared.shadow.union *
        twoScale.fine.balanced.cellMass *
        MeasureTheory.volume twoScale.coarse.refined.union *
        (twoScale.coarse.fineMultiplicity : ENNReal) *
        pureWZ2SourceHorizontalRichFloor rho finalLoss := by
  let bodyMass : ENNReal := (wz1PaperBodyFamily source.family).mass
  let volumePower : ENNReal := Kakeya.realRpowENN rho
    (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta)
  let refinement : ENNReal :=
    wz2PaperPureRefinementFraction delta logExponent
  let inputPower : ENNReal := Kakeya.realRpowENN delta inputLoss
  let fineMass : ENNReal := twoScale.fine.balanced.cellMass
  let secondCellPower : ENNReal := Kakeya.realRpowENN
    twoScale.rhoRequested.1
      (3 / 2 + sigma / 2 + 3 * stickyLoss / 2)
  let firstRefinedPower : ENNReal :=
    Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss)
  let multiplicity : ENNReal := twoScale.coarse.fineMultiplicity
  let richFloor : ENNReal := pureWZ2SourceHorizontalRichFloor rho finalLoss
  let coarseVolume : ENNReal := MeasureTheory.volume
    twoScale.coarse.croppedCoarseShading.union
  let target : ENNReal := MeasureTheory.volume prepared.shadow.union *
    fineMass * MeasureTheory.volume twoScale.coarse.refined.union *
      multiplicity * richFloor
  have hrelative : volumePower * (refinement * (inputPower * bodyMass)) ≤
      2 * (MeasureTheory.volume prepared.shadow.union * multiplicity) := by
    simpa [volumePower, refinement, inputPower, bodyMass, multiplicity] using
      prepared.relative_mass_structural_lower
        hrhoSmall hsecondFraction hcoarseSigma
  have hsecondCell : secondCellPower ≤ fineMass := by
    simpa [secondCellPower, fineMass] using
      twoScale.second_source_floor_power
  have hfirstRefined : firstRefinedPower ≤
      MeasureTheory.volume twoScale.coarse.refined.union := by
    simpa [firstRefinedPower] using twoScale.coarse.refined_volume_lower
  have hscaled :
      (2 : ENNReal) *
          (cost * (Kakeya.realRpowENN delta structuralLoss * bodyMass) *
            coarseVolume) ≤
        (2 : ENNReal) * target := by
    calc
      (2 : ENNReal) *
            (cost * (Kakeya.realRpowENN delta structuralLoss * bodyMass) *
              coarseVolume) =
          (2 * cost * Kakeya.realRpowENN delta structuralLoss *
            coarseVolume) * bodyMass := by ring
      _ ≤ (volumePower * refinement * inputPower * secondCellPower *
            firstRefinedPower * richFloor) * bodyMass := by gcongr
      _ = (volumePower * (refinement * (inputPower * bodyMass))) *
          (secondCellPower * firstRefinedPower * richFloor) := by ring
      _ ≤ (2 * (MeasureTheory.volume prepared.shadow.union * multiplicity)) *
          (fineMass * MeasureTheory.volume twoScale.coarse.refined.union *
            richFloor) := by gcongr
      _ = (2 : ENNReal) * target := by
        simp only [target]
        ring
  have htwoZero : (2 : ENNReal) ≠ 0 := by norm_num
  have htwoTop : (2 : ENNReal) ≠ ⊤ := by norm_num
  have hcancel :=
    (ENNReal.mul_le_mul_iff_right htwoZero htwoTop).mp hscaled
  simpa [target, bodyMass, fineMass, multiplicity, richFloor, coarseVolume,
    mul_comm, mul_left_comm, mul_assoc] using hcancel

/--
The graph-volume popularity budget using only the genuine two-stage volume
supply.  Each balanced cell mass is paid once.
-/
theorem PureWZ2SourceCarrierPreparation.graph_cost_of_relative_volume_budget
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
    (hcoarseSigma : twoScale.coarseLoss ≤ sigma)
    (cost : ENNReal)
    (hpower : cost ≤
      Kakeya.realRpowENN rho
          (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
        Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
        Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
        MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0)) *
        Kakeya.realRpowENN twoScale.rhoRequested.1
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2)) :
    cost ≤ MeasureTheory.volume prepared.shadow.union *
      (twoScale.coarse.balanced.cellMass *
        twoScale.fine.balanced.cellMass) := by
  let cubeVolume : ENNReal :=
    MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))
  let coarseMass : ENNReal := twoScale.coarse.balanced.cellMass
  let fineMass : ENNReal := twoScale.fine.balanced.cellMass
  let volumePower : ENNReal := Kakeya.realRpowENN rho
    (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta)
  let firstCellPower : ENNReal :=
    Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss)
  let secondCellPower : ENNReal := Kakeya.realRpowENN
    twoScale.rhoRequested.1 (3 / 2 + sigma / 2 + 3 * stickyLoss / 2)
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hcoarsePowerOne :
      Kakeya.realRpowENN rho (sigma - twoScale.coarseLoss) ≤ 1 := by
    exact ENNReal.ofReal_le_one.mpr
      (Real.rpow_le_one hrho.le hrhoOne (by linarith))
  have hfirstCell : firstCellPower * cubeVolume ≤ coarseMass := by
    calc
      firstCellPower * cubeVolume ≤
          Kakeya.realRpowENN rho (sigma - twoScale.coarseLoss) *
            coarseMass := by
        simpa [firstCellPower, cubeVolume] using
          twoScale.first_cell_floor_raw
      _ ≤ 1 * coarseMass := by gcongr
      _ = coarseMass := one_mul _
  have hsecondCell : secondCellPower ≤ fineMass := by
    simpa [secondCellPower, fineMass] using
      twoScale.second_source_floor_power
  have hvolume : volumePower * coarseMass ≤
      MeasureTheory.volume prepared.shadow.union * cubeVolume := by
    simpa [volumePower, coarseMass, cubeVolume] using
      prepared.volume_mul_cube_lower hrhoSmall hsecondFraction
  have hcubePos : 0 < cubeVolume := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_pos.mpr (pow_pos hrho 3)
  have hcubeTop : cubeVolume ≠ ⊤ := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_ne_top
  have hscaled : cost * cubeVolume ≤
      (MeasureTheory.volume prepared.shadow.union *
        (coarseMass * fineMass)) * cubeVolume := by
    calc
      cost * cubeVolume ≤
          (volumePower * firstCellPower * firstCellPower * cubeVolume *
            secondCellPower) * cubeVolume := by
        gcongr
      _ = (volumePower * (firstCellPower * cubeVolume)) *
          (firstCellPower * cubeVolume) * secondCellPower := by ring
      _ ≤ (volumePower * coarseMass) * coarseMass * fineMass := by gcongr
      _ ≤ (MeasureTheory.volume prepared.shadow.union * cubeVolume) *
          coarseMass * fineMass := by gcongr
      _ = (MeasureTheory.volume prepared.shadow.union *
          (coarseMass * fineMass)) * cubeVolume := by ring
  apply (ENNReal.mul_le_mul_iff_right hcubePos.ne' hcubeTop).mp
  simpa [mul_comm] using hscaled

end Kakeya.Assouad

end
