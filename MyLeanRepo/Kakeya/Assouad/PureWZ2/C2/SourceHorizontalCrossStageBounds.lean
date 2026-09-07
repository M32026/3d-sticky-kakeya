import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalProjectionSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SecondStageSourceFloor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TwoScaleVolume

/-!
# Cross-stage quantitative identities for the source-horizontal carrier

The pullback carrier is selected by the second sticky cover but measured with
the first sticky balanced cell mass.  The identities below deliberately keep
those two roles separate.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- Exact cross-stage volume identity: the pullback volume times one physical
side-`rho` cube equals the second refined volume times the first balanced cell
mass. -/
theorem PureWZ2SourceCarrierPreparation.volume_mul_cube_eq
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) :
    volume prepared.shadow.union *
        volume (wz1PaperGridCube rho (0, 0, 0)) =
      volume twoScale.fine.refined.union *
        twoScale.coarse.balanced.cellMass := by
  rw [prepared.shadow_union, pullback.volume_eq,
    ← pullback.selected_count_mul_coarse_volume]
  ring

/-- Power-form consequence of the exact cross-stage identity. -/
theorem PureWZ2SourceCarrierPreparation.volume_mul_cube_lower
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
          twoScale.rhoRequested.1 logExponent) :
    Kakeya.realRpowENN rho
          (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
        twoScale.coarse.balanced.cellMass ≤
      volume prepared.shadow.union *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  have hsecond := twoScale.second_refined_volume_power
    hrhoSmall hsecondFraction
  have hsecondRho :
      Kakeya.realRpowENN rho
          (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) ≤
        volume twoScale.fine.refined.union := by
    calc
      Kakeya.realRpowENN rho
          (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) =
        Kakeya.realRpowENN twoScale.rhoRequested.1
          (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) := by
        rw [twoScale.rhoRequested_eq]
      _ ≤ volume twoScale.fine.refined.union := hsecond
  rw [prepared.volume_mul_cube_eq]
  gcongr

/-- First-stage source cell floor, with the requested scale rewritten to the
outer parameter `rho`. -/
theorem PureWZ2OneScaleTwoScaleStickyData.first_cell_floor_raw
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent) :
    Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
        volume (wz1PaperGridCube rho (0, 0, 0)) ≤
      Kakeya.realRpowENN rho (sigma - twoScale.coarseLoss) *
        twoScale.coarse.balanced.cellMass := by
  simpa only [twoScale.rhoRequested_eq] using
    twoScale.coarse.source_floor_raw

/-- First-stage incidence floor remains tied to the original source shading,
not the intermediate coarse grain carrier. -/
theorem PureWZ2OneScaleTwoScaleStickyData.first_incidence_floor_raw
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent) :
    (wz2PaperPureRefinementFraction delta logExponent *
          source.shading.mass) *
        volume (wz1PaperGridCube rho (0, 0, 0)) ≤
      Kakeya.realRpowENN rho (sigma - twoScale.coarseLoss) *
        twoScale.coarse.balanced.incidenceMass := by
  simpa only [twoScale.rhoRequested_eq] using
    twoScale.coarse.incidence_floor_raw

/-- Replace original indexed source mass by the paper body mass using the
source extremality density. -/
theorem PureWZ2OneScaleTwoScaleStickyData.first_incidence_body_floor
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent) :
    (wz2PaperPureRefinementFraction delta logExponent *
          (Kakeya.realRpowENN delta inputLoss *
            (wz1PaperBodyFamily source.family).mass)) *
        volume (wz1PaperGridCube rho (0, 0, 0)) ≤
      Kakeya.realRpowENN rho (sigma - twoScale.coarseLoss) *
        twoScale.coarse.balanced.incidenceMass := by
  calc
    (wz2PaperPureRefinementFraction delta logExponent *
          (Kakeya.realRpowENN delta inputLoss *
            (wz1PaperBodyFamily source.family).mass)) *
        volume (wz1PaperGridCube rho (0, 0, 0)) ≤
      (wz2PaperPureRefinementFraction delta logExponent *
          source.shading.mass) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
      gcongr
      exact source.extremal.dense
    _ ≤ Kakeya.realRpowENN rho (sigma - twoScale.coarseLoss) *
        twoScale.coarse.balanced.incidenceMass :=
      twoScale.first_incidence_floor_raw

/--
The first-sticky point multiplicity is bounded by the original paper body
mass after paying one physical side-`delta` tube cross-section.  This uses an
actual point of the retained first refinement and the injective selected
subfamily; no ambient family cardinality is introduced as an assumption.
-/
theorem PureWZ2OneScaleTwoScaleStickyData.first_multiplicity_body_upper
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent)
    (hdeltaSmall : delta ≤ 1 / 12) :
    (twoScale.coarse.fineMultiplicity : ENNReal) *
        Kakeya.realRpowENN delta 2 ≤
      (wz1PaperBodyFamily source.family).mass := by
  classical
  have hrefinedPos :
      0 < volume twoScale.coarse.refined.union := by
    have hpower :
        0 < Kakeya.realRpowENN delta
          (sigma + twoScale.coarseLoss) :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos source.extremal.delta_pos _)
    exact hpower.trans_le twoScale.coarse.refined_volume_lower
  have hrefinedNonempty : twoScale.coarse.refined.union.Nonempty := by
    by_contra hempty
    have hzero : volume twoScale.coarse.refined.union = 0 := by
      rw [Set.not_nonempty_iff_eq_empty.mp hempty]
      simp
    exact (ne_of_gt hrefinedPos) hzero
  rcases hrefinedNonempty with ⟨point, hpoint⟩
  have hmultNat : twoScale.coarse.fineMultiplicity ≤
      twoScale.coarse.selected.family.card := by
    have hlower :=
      (twoScale.coarse.refined_multiplicity_band point hpoint).1
    have hupper : twoScale.coarse.refined.pointMultiplicity point ≤
        twoScale.coarse.selected.family.card := by
      let predicate : Fin twoScale.coarse.selected.family.card → Prop :=
        fun index => point ∈ twoScale.coarse.refined.carrier index
      change (Finset.univ.filter predicate).card ≤ _
      have hsubset : Finset.univ.filter predicate ⊆
          (Finset.univ : Finset
            (Fin twoScale.coarse.selected.family.card)) :=
        Finset.filter_subset predicate Finset.univ
      simpa using Finset.card_le_card hsubset
    exact hlower.trans hupper
  have hselectedNat : twoScale.coarse.selected.family.card ≤
      source.family.card := by
    simpa using
      (Fintype.card_le_of_injective
        twoScale.coarse.selected.embedding
        twoScale.coarse.selected.embedding.injective)
  have hmult : (twoScale.coarse.fineMultiplicity : ENNReal) ≤
      source.family.enncard := by
    change (twoScale.coarse.fineMultiplicity : ENNReal) ≤
      (source.family.card : ENNReal)
    exact_mod_cast hmultNat.trans hselectedNat
  calc
    (twoScale.coarse.fineMultiplicity : ENNReal) *
          Kakeya.realRpowENN delta 2 ≤
        source.family.enncard * Kakeya.realRpowENN delta 2 := by
      gcongr
    _ ≤ (wz1PaperBodyFamily source.family).mass :=
      pureWZ2_paperBody_mass_lower source.extremal.delta_pos
        hdeltaSmall source.line_class

/--
Complete cross-stage supply floor for the source-horizontal absorption.  One
copy of the first balanced cell mass comes from the second-stage pullback
volume.  The other is paired with `fineMultiplicity` through the first-stage
incidence band, so no standalone power lower bound on the multiplicity is
assumed.
-/
theorem PureWZ2SourceCarrierPreparation.weighted_supply_structural_lower
    {sigma inputLoss delta rho middleLoss stickyLoss secondEta finalLoss : ℝ}
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
        (wz2PaperPureRefinementFraction delta logExponent *
          (Kakeya.realRpowENN delta inputLoss *
            (wz1PaperBodyFamily source.family).mass)) *
        volume (wz1PaperGridCube rho (0, 0, 0)) *
        pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      2 * (volume prepared.shadow.union *
        (twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass) *
        (twoScale.coarse.fineMultiplicity : ENNReal) *
        pureWZ2SourceHorizontalRichFloor rho finalLoss) := by
  let cubeVolume := volume (wz1PaperGridCube rho (0, 0, 0))
  let coarseMass := twoScale.coarse.balanced.cellMass
  let fineMass := twoScale.fine.balanced.cellMass
  let multiplicity : ENNReal := twoScale.coarse.fineMultiplicity
  let incidenceMass := twoScale.coarse.balanced.incidenceMass
  let coarsePower := Kakeya.realRpowENN rho
    (sigma - twoScale.coarseLoss)
  let volumePower := Kakeya.realRpowENN rho
    (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta)
  let firstCellPower := Kakeya.realRpowENN delta
    (sigma + twoScale.coarseLoss)
  let secondCellPower := Kakeya.realRpowENN twoScale.rhoRequested.1
    (3 / 2 + sigma / 2 + 3 * stickyLoss / 2)
  let bodySupply := wz2PaperPureRefinementFraction delta logExponent *
    (Kakeya.realRpowENN delta inputLoss *
      (wz1PaperBodyFamily source.family).mass)
  let richFloor := pureWZ2SourceHorizontalRichFloor rho finalLoss
  have hrhoPos : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hcoarsePowerOne : coarsePower ≤ 1 := by
    dsimp only [coarsePower, Kakeya.realRpowENN]
    exact ENNReal.ofReal_le_one.mpr
      (Real.rpow_le_one hrhoPos.le hrhoOne (by linarith))
  have hvolume : volumePower * coarseMass ≤
      volume prepared.shadow.union * cubeVolume := by
    simpa [volumePower, coarseMass, cubeVolume] using
      prepared.volume_mul_cube_lower hrhoSmall hsecondFraction
  have hfirstCell : firstCellPower * cubeVolume ≤
      coarsePower * coarseMass := by
    simpa [firstCellPower, cubeVolume, coarsePower, coarseMass] using
      twoScale.first_cell_floor_raw
  have hsecondCell : secondCellPower ≤ fineMass := by
    simpa [secondCellPower, fineMass] using
      twoScale.second_source_floor_power
  have hincidence : bodySupply * cubeVolume ≤
      coarsePower * incidenceMass := by
    simpa [bodySupply, cubeVolume, coarsePower, incidenceMass] using
      twoScale.first_incidence_body_floor
  have hband : incidenceMass ≤ 2 * multiplicity * coarseMass := by
    simpa [incidenceMass, multiplicity, coarseMass, mul_assoc] using
      twoScale.coarse.balanced_incidenceMass_band.2
  have hcubePos : 0 < cubeVolume := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrhoPos]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hcancelZero : coarseMass * cubeVolume ≠ 0 := by
    exact mul_ne_zero twoScale.coarse.balanced.cellMass_pos.ne' hcubePos.ne'
  have hcancelTop : coarseMass * cubeVolume ≠ ⊤ := by
    exact ENNReal.mul_ne_top twoScale.coarse.balanced.cellMass_ne_top
      (by dsimp only [cubeVolume]
          rw [wz1PaperGridCube_volume_exact hrhoPos]
          exact ENNReal.ofReal_ne_top)
  have hscaled :
      (volumePower * firstCellPower * secondCellPower * bodySupply *
          cubeVolume * richFloor) * (coarseMass * cubeVolume) ≤
        (2 * (volume prepared.shadow.union *
          (coarseMass * fineMass) * multiplicity * richFloor)) *
        (coarseMass * cubeVolume) := by
    calc
    (volumePower * firstCellPower * secondCellPower * bodySupply *
          cubeVolume * richFloor) * (coarseMass * cubeVolume) =
        (volumePower * coarseMass) *
          (firstCellPower * cubeVolume) * secondCellPower *
          (bodySupply * cubeVolume) * richFloor := by ring
    _ ≤ (volume prepared.shadow.union * cubeVolume) *
          (coarsePower * coarseMass) * fineMass *
          (coarsePower * incidenceMass) * richFloor := by gcongr
    _ ≤ (volume prepared.shadow.union * cubeVolume) *
          (coarsePower * coarseMass) * fineMass *
          (coarsePower * (2 * multiplicity * coarseMass)) *
          richFloor := by gcongr
    _ ≤ (volume prepared.shadow.union * cubeVolume) *
          (1 * coarseMass) * fineMass *
          (1 * (2 * multiplicity * coarseMass)) * richFloor := by gcongr
    _ = (2 * (volume prepared.shadow.union *
          (coarseMass * fineMass) * multiplicity * richFloor)) *
        (coarseMass * cubeVolume) := by ring
  apply (ENNReal.mul_le_mul_iff_right hcancelZero hcancelTop).mp
  simpa [volumePower, firstCellPower, secondCellPower, bodySupply,
    cubeVolume, richFloor, coarseMass, fineMass, multiplicity,
    mul_comm] using hscaled

/--
Cancel the common multiplicity and rich-height factors after comparing a
local block cost with the complete structural supply.  This is the form used
to prove that the good source-block set is nonempty.
-/
theorem PureWZ2SourceCarrierPreparation.block_cost_le_of_structural_supply
    {sigma inputLoss delta rho middleLoss stickyLoss secondEta finalLoss : ℝ}
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
    (hcost :
      2 * cost * (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
        Kakeya.realRpowENN rho
            (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) *
          (wz2PaperPureRefinementFraction delta logExponent *
            (Kakeya.realRpowENN delta inputLoss *
              (wz1PaperBodyFamily source.family).mass)) *
          volume (wz1PaperGridCube rho (0, 0, 0)) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss) :
    cost ≤ volume prepared.shadow.union *
      (twoScale.coarse.balanced.cellMass *
        twoScale.fine.balanced.cellMass) := by
  let common : ENNReal :=
    2 * (twoScale.coarse.fineMultiplicity : ENNReal) *
      pureWZ2SourceHorizontalRichFloor rho finalLoss
  have hstruct := prepared.weighted_supply_structural_lower
    hrhoSmall hsecondFraction hcoarseSigma (finalLoss := finalLoss)
  have hscaled : cost * common ≤
      (volume prepared.shadow.union *
        (twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass)) * common := by
    calc
      cost * common =
          2 * cost * (twoScale.coarse.fineMultiplicity : ENNReal) *
            pureWZ2SourceHorizontalRichFloor rho finalLoss := by
        simp only [common]
        ring
      _ ≤ _ := hcost.trans hstruct
      _ = (volume prepared.shadow.union *
            (twoScale.coarse.balanced.cellMass *
              twoScale.fine.balanced.cellMass)) * common := by
        simp only [common]
        ring
  have hrhoPos : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hcommonZero : common ≠ 0 := by
    dsimp only [common, pureWZ2SourceHorizontalRichFloor]
    have hmultiplicity :
        (twoScale.coarse.fineMultiplicity : ENNReal) ≠ 0 := by
      exact_mod_cast twoScale.coarse.fineMultiplicity_pos.ne'
    have hfloor : Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale (256 * rho)) (finalLoss - 1) ≠ 0 := by
      apply ne_of_gt
      apply ENNReal.ofReal_pos.mpr
      apply Real.rpow_pos_of_pos
      unfold wz1Lemma23Theorem22Scale
      positivity
    exact mul_ne_zero (mul_ne_zero (by norm_num) hmultiplicity) hfloor
  have hcommonTop : common ≠ ⊤ := by
    dsimp only [common, pureWZ2SourceHorizontalRichFloor]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (by simp))
      (by simp [Kakeya.realRpowENN])
  have hscaled' : common * cost ≤ common *
      (volume prepared.shadow.union *
        (twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass)) := by
    simpa [mul_comm] using hscaled
  exact (ENNReal.mul_le_mul_iff_right hcommonZero hcommonTop).mp hscaled'

/--
Cancel the absolute factor two after comparing the final source-mass cost
with the complete structural supply.  The multiplicity and rich-height
factors remain on the target side, exactly as required by the weighted
one-scale producer.
-/
theorem PureWZ2SourceCarrierPreparation.final_cost_le_of_structural_supply
    {sigma inputLoss delta rho middleLoss stickyLoss secondEta finalLoss : ℝ}
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
    (hcost :
      2 * cost ≤
        Kakeya.realRpowENN rho
            (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) *
          (wz2PaperPureRefinementFraction delta logExponent *
            (Kakeya.realRpowENN delta inputLoss *
              (wz1PaperBodyFamily source.family).mass)) *
          volume (wz1PaperGridCube rho (0, 0, 0)) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss) :
    cost ≤ volume prepared.shadow.union *
      (twoScale.coarse.balanced.cellMass *
        twoScale.fine.balanced.cellMass) *
      (twoScale.coarse.fineMultiplicity : ENNReal) *
      pureWZ2SourceHorizontalRichFloor rho finalLoss := by
  have hstruct := prepared.weighted_supply_structural_lower
    hrhoSmall hsecondFraction hcoarseSigma (finalLoss := finalLoss)
  have hscaled : 2 * cost ≤
      2 * (volume prepared.shadow.union *
        (twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass) *
        (twoScale.coarse.fineMultiplicity : ENNReal) *
        pureWZ2SourceHorizontalRichFloor rho finalLoss) :=
    hcost.trans hstruct
  let target : ENNReal := volume prepared.shadow.union *
    (twoScale.coarse.balanced.cellMass *
      twoScale.fine.balanced.cellMass) *
    (twoScale.coarse.fineMultiplicity : ENNReal) *
    pureWZ2SourceHorizontalRichFloor rho finalLoss
  have hscaled' : (2 : ENNReal) * cost ≤ (2 : ENNReal) * target := by
    simpa [target] using hscaled
  have htwoZero : (2 : ENNReal) ≠ 0 := by norm_num
  have htwoTop : (2 : ENNReal) ≠ ⊤ := by norm_num
  exact (ENNReal.mul_le_mul_iff_right htwoZero htwoTop).mp hscaled'

end Kakeya.Assouad
