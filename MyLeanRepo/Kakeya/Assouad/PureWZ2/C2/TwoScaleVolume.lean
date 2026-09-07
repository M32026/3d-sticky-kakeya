import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleTwoScaleSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.StickyMultiplicity
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Exact volume retention for the second pure sticky refinement

This module keeps the polylogarithmic factor and every scale power explicit.
No small-scale absorption is performed here.
-/

noncomputable section

namespace Kakeya.Assouad

theorem PureWZ2OneScaleTwoScaleStickyData.second_refined_volume_raw
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent)
    (hrhoSmall : twoScale.rhoRequested.1 ≤ 1 / 12) :
    (wz2PaperPureRefinementFraction
          twoScale.rhoRequested.1 logExponent *
        Kakeya.realRpowENN twoScale.rhoRequested.1 middleLoss *
        Kakeya.realRpowENN twoScale.rhoRequested.1 2) ≤
      (Kakeya.realRpowENN
          (twoScale.rhoRequested.1 / twoScale.sqrtRequested.1)
          (2 - sigma - outputLoss)) *
        MeasureTheory.volume twoScale.fine.refined.union := by
  let scale := twoScale.rhoRequested.1
  let fineScale := twoScale.sqrtRequested.1
  let fraction := wz2PaperPureRefinementFraction scale logExponent
  let cap := Kakeya.realRpowENN (scale / fineScale)
    (2 - sigma - outputLoss)
  let ambientCard := twoScale.coarse.coarse.enncard
  let selectedCard := twoScale.fine.selected.family.enncard
  let targetVolume := MeasureTheory.volume twoScale.fine.refined.union
  have hambientMass :
      Kakeya.realRpowENN scale middleLoss * ambientCard *
          Kakeya.realRpowENN scale 2 ≤
        twoScale.coarseGrains.shading.mass := by
    exact twoScale.coarseGrains.extremal.mass_lower
      hrhoSmall twoScale.coarseGrains.line_class
  have hretained :
      fraction * twoScale.coarseGrains.shading.mass ≤
        twoScale.fine.refined.mass := by
    exact twoScale.fine.retained_mass
  have hmassUpper :
      twoScale.fine.refined.mass ≤
        (cap * selectedCard) * targetVolume := by
    exact twoScale.fine.data.refined_mass_le_fiberSumCap_mul_volume
  have hselectedCard : selectedCard ≤ ambientCard := by
    change
      (twoScale.fine.selected.family.card : ENNReal) ≤
        (twoScale.coarse.coarse.card : ENNReal)
    exact_mod_cast
      (show twoScale.fine.selected.family.card ≤
          twoScale.coarse.coarse.card by
        simpa using Finset.card_le_univ
          (Finset.univ.map twoScale.fine.selected.embedding))
  have hwithCard :
      (fraction * Kakeya.realRpowENN scale middleLoss *
          Kakeya.realRpowENN scale 2) * ambientCard ≤
        (cap * targetVolume) * ambientCard := by
    calc
      (fraction * Kakeya.realRpowENN scale middleLoss *
            Kakeya.realRpowENN scale 2) * ambientCard =
          fraction *
            (Kakeya.realRpowENN scale middleLoss * ambientCard *
              Kakeya.realRpowENN scale 2) := by ring
      _ ≤ fraction * twoScale.coarseGrains.shading.mass := by
        gcongr
      _ ≤ twoScale.fine.refined.mass := hretained
      _ ≤ (cap * selectedCard) * targetVolume := hmassUpper
      _ ≤ (cap * ambientCard) * targetVolume := by
        gcongr
      _ = (cap * targetVolume) * ambientCard := by ring
  have hcardZero : ambientCard ≠ 0 := by
    apply ne_of_gt
    dsimp only [ambientCard, Kakeya.Streamlined.TubeFamily.enncard]
    exact_mod_cast
      (show 0 < twoScale.coarse.coarse.card by
        exact twoScale.coarse.coarse_extremal.nonempty)
  have hcardTop : ambientCard ≠ ⊤ := by
    simp [ambientCard, Kakeya.Streamlined.TubeFamily.enncard]
  have hwithCard' :
      ambientCard *
          (fraction * Kakeya.realRpowENN scale middleLoss *
            Kakeya.realRpowENN scale 2) ≤
        ambientCard * (cap * targetVolume) := by
    simpa [mul_comm] using hwithCard
  exact
    (ENNReal.mul_le_mul_iff_right hcardZero hcardTop).mp hwithCard'

/-- Simplify the exact square-root scale powers in the raw volume bound. -/
theorem PureWZ2OneScaleTwoScaleStickyData.second_refined_volume_power
    {sigma inputLoss delta rho middleLoss outputLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent)
    (hrhoSmall : twoScale.rhoRequested.1 ≤ 1 / 12)
    (hetaAbsorb :
      Kakeya.realRpowENN twoScale.rhoRequested.1 eta ≤
        wz2PaperPureRefinementFraction
          twoScale.rhoRequested.1 logExponent) :
    Kakeya.realRpowENN twoScale.rhoRequested.1
        (1 + sigma / 2 + middleLoss + outputLoss / 2 + eta) ≤
      MeasureTheory.volume twoScale.fine.refined.union := by
  let scale := twoScale.rhoRequested.1
  have hscale : 0 < scale :=
    source.extremal.delta_pos.trans_le twoScale.rhoRequested.property.1
  have hsqrt : twoScale.sqrtRequested.1 = Real.sqrt scale := by
    calc
      twoScale.sqrtRequested.1 = Real.sqrt rho :=
        twoScale.sqrtRequested_eq
      _ = Real.sqrt scale := by
        congr 1
        exact twoScale.rhoRequested_eq.symm
  have hratio : scale / twoScale.sqrtRequested.1 = Real.sqrt scale := by
    rw [hsqrt]
    have hsqrtPos : 0 < Real.sqrt scale := Real.sqrt_pos.mpr hscale
    apply (div_eq_iff hsqrtPos.ne').2
    rw [← pow_two, Real.sq_sqrt hscale.le]
  have hcap :
      Kakeya.realRpowENN
          (scale / twoScale.sqrtRequested.1)
          (2 - sigma - outputLoss) =
        Kakeya.realRpowENN scale
          ((2 - sigma - outputLoss) / 2) := by
    rw [hratio]
    simp only [Kakeya.realRpowENN, Real.sqrt_eq_rpow]
    apply congrArg ENNReal.ofReal
    calc
      (Real.rpow scale (1 / 2)).rpow
          (2 - sigma - outputLoss) =
          Real.rpow scale
            ((1 / 2) * (2 - sigma - outputLoss)) :=
        (Real.rpow_mul hscale.le (1 / 2)
          (2 - sigma - outputLoss)).symm
      _ = Real.rpow scale ((2 - sigma - outputLoss) / 2) := by
        congr 1
        ring
  have hraw := twoScale.second_refined_volume_raw hrhoSmall
  rw [hcap] at hraw
  have hleft :
      Kakeya.realRpowENN scale eta *
          Kakeya.realRpowENN scale middleLoss *
          Kakeya.realRpowENN scale 2 ≤
        wz2PaperPureRefinementFraction scale logExponent *
          Kakeya.realRpowENN scale middleLoss *
          Kakeya.realRpowENN scale 2 := by
    gcongr
  have hcombined :
      Kakeya.realRpowENN scale (eta + middleLoss + 2) ≤
        Kakeya.realRpowENN scale
            ((2 - sigma - outputLoss) / 2) *
          MeasureTheory.volume twoScale.fine.refined.union := by
    rw [realRpowENN_add hscale, realRpowENN_add hscale]
    exact hleft.trans hraw
  let cap := Kakeya.realRpowENN scale
    ((2 - sigma - outputLoss) / 2)
  have hcapZero : cap ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hscale _))
  have hcapTop : cap ≠ ⊤ := by
    simp [cap, Kakeya.realRpowENN]
  have htarget :
      Kakeya.realRpowENN scale
          (1 + sigma / 2 + middleLoss + outputLoss / 2 + eta) *
          cap =
        Kakeya.realRpowENN scale (eta + middleLoss + 2) := by
    dsimp only [cap]
    rw [← realRpowENN_add hscale]
    congr 1
    ring
  have hscaled :
      Kakeya.realRpowENN scale
          (1 + sigma / 2 + middleLoss + outputLoss / 2 + eta) * cap ≤
        MeasureTheory.volume twoScale.fine.refined.union * cap := by
    rw [htarget]
    simpa [cap, mul_comm] using hcombined
  exact (ENNReal.mul_le_mul_iff_left hcapZero hcapTop).mp hscaled

end Kakeya.Assouad
