import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinStandardSlabSourceMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalGoodBlocks

/-!
# Source-heavy standard slab selection

Light unshifted standard slabs are removed before selecting common bins.  The
threshold is one tenth of source mass times `sqrt rho`; the occupied-slab
count bound shows that the retained slabs carry at least half the source.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

def pureWZ2StandardSqrtSlabHeavyThreshold
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale) : ENNReal :=
  (10 : ENNReal)⁻¹ * volume pullback.shading.union *
    ENNReal.ofReal (Real.sqrt rho)

def pureWZ2SourceHeavyStandardSqrtSlabs
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale) :
    Finset {heightIndex // heightIndex ∈
      pullback.standardSqrtSlabIndices} :=
  Finset.univ.filter fun heightIndex =>
    pureWZ2StandardSqrtSlabHeavyThreshold pullback ≤
      volume (pullback.standardSqrtSlabSourceRegion heightIndex.1)

namespace PureWZ2TwoScaleCellPullbackData

variable
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)

theorem standardSqrtSlabHeavyThreshold_ne_top :
    pureWZ2StandardSqrtSlabHeavyThreshold pullback ≠ ⊤ := by
  have hsourceTop : volume pullback.shading.union ≠ ⊤ := by
    rw [pullback.volume_eq]
    exact ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top _)
      twoScale.coarse.balanced.cellMass_ne_top
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by norm_num) hsourceTop)
    ENNReal.ofReal_ne_top

theorem standardSqrtSlabHeavyThreshold_le
    {heightIndex :
      {heightIndex // heightIndex ∈ pullback.standardSqrtSlabIndices}}
    (hheightIndex :
      heightIndex ∈ pureWZ2SourceHeavyStandardSqrtSlabs pullback) :
    pureWZ2StandardSqrtSlabHeavyThreshold pullback ≤
      volume
        (pullback.standardSqrtSlabSourceRegion heightIndex.1) :=
  (Finset.mem_filter.mp hheightIndex).2

/-- The discarded light standard slabs have at most half the exact source
mass, hence the source-heavy slabs retain at least half. -/
theorem sourceHeavyStandardSqrtSlabs_retains_half :
    volume pullback.shading.union ≤
      2 * ∑ heightIndex ∈
          pureWZ2SourceHeavyStandardSqrtSlabs pullback,
        volume
          (pullback.standardSqrtSlabSourceRegion heightIndex.1) := by
  let slabs : Finset {heightIndex // heightIndex ∈
      pullback.standardSqrtSlabIndices} := Finset.univ
  let sourceMass := volume pullback.shading.union
  let root := ENNReal.ofReal (Real.sqrt rho)
  let slabThreshold := pureWZ2StandardSqrtSlabHeavyThreshold pullback
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hrootOne : Real.sqrt rho ≤ 1 :=
    Real.sqrt_le_one.mpr hrhoOne
  have hfive :
      ENNReal.ofReal (2 + 3 * Real.sqrt rho) ≤ 5 := by
    calc
      ENNReal.ofReal (2 + 3 * Real.sqrt rho) ≤
          ENNReal.ofReal 5 := by
        apply ENNReal.ofReal_mono
        linarith
      _ = 5 := by norm_num
  have hcardRoot :
      (slabs.card : ENNReal) * root ≤ 5 := by
    have hcard :=
      pullback.standardSqrtSlabIndices_card_mul_sqrtENN_le
    have hcardEq :
        slabs.card = pullback.standardSqrtSlabIndices.card := by
      simp [slabs]
    simpa [hcardEq, root] using hcard.trans hfive
  have hsmall :
      2 * ((slabs.card : ENNReal) * slabThreshold) ≤
        sourceMass := by
    have hcoefficient :
        (2 : ENNReal) * (10 : ENNReal)⁻¹ * 5 = 1 := by
      rw [show (10 : ENNReal) = 2 * 5 by norm_num]
      rw [ENNReal.mul_inv (by norm_num) (by norm_num)]
      calc
        (2 : ENNReal) * (2⁻¹ * 5⁻¹) * 5 =
            (2 * 2⁻¹) * (5⁻¹ * 5) := by ac_rfl
        _ = 1 := by
          rw [ENNReal.mul_inv_cancel, ENNReal.inv_mul_cancel] <;>
            norm_num
    calc
      2 * ((slabs.card : ENNReal) * slabThreshold) =
          (2 * (10 : ENNReal)⁻¹) *
            ((slabs.card : ENNReal) * root) * sourceMass := by
        simp only [slabThreshold, pureWZ2StandardSqrtSlabHeavyThreshold,
          sourceMass, root]
        ring
      _ ≤ (2 * (10 : ENNReal)⁻¹) * 5 * sourceMass := by
        gcongr
      _ = sourceMass := by rw [hcoefficient, one_mul]
  have htotal :
      (∑ heightIndex ∈ slabs,
        volume
          (pullback.standardSqrtSlabSourceRegion heightIndex.1)) =
        sourceMass := by
    simpa [slabs, sourceMass] using
      pullback.sum_standardSqrtSlabSourceRegion_volume_subtype
  have hhalf :=
    finset_good_weighted_supply_retains_half
      slabs
      (fun heightIndex =>
        volume
          (pullback.standardSqrtSlabSourceRegion heightIndex.1))
      1 slabThreshold
      pullback.standardSqrtSlabHeavyThreshold_ne_top
      (by simpa [htotal] using hsmall)
  simp only [mul_one] at hhalf
  rw [htotal] at hhalf
  simpa [slabs, sourceMass, slabThreshold,
    pureWZ2SourceHeavyStandardSqrtSlabs] using hhalf

/-- Source-heavy standard slabs retain half of the exact indexed source mass,
not merely half of the spatial union volume. -/
theorem sourceHeavyStandardSqrtSlabs_retains_half_mass :
    pullback.shading.mass ≤
      2 * ∑ heightIndex ∈ pureWZ2SourceHeavyStandardSqrtSlabs pullback,
        pullback.standardSqrtSlabSourceWeight heightIndex.1 := by
  let cellMass := twoScale.coarse.balanced.cellMass
  have hcellPos : 0 < cellMass := twoScale.coarse.balanced.cellMass_pos
  have hcellTop : cellMass ≠ ⊤ :=
    twoScale.coarse.balanced.cellMass_ne_top
  apply (ENNReal.mul_le_mul_iff_right hcellPos.ne' hcellTop).mp
  calc
    cellMass * pullback.shading.mass =
        volume pullback.shading.union *
          twoScale.coarse.balanced.incidenceMass := by
      rw [pullback.volume_eq, pullback.mass_eq]
      dsimp only [cellMass]
      ring
    _ ≤ (2 * ∑ heightIndex ∈
          pureWZ2SourceHeavyStandardSqrtSlabs pullback,
        volume (pullback.standardSqrtSlabSourceRegion heightIndex.1)) *
          twoScale.coarse.balanced.incidenceMass := by
      gcongr
      exact pullback.sourceHeavyStandardSqrtSlabs_retains_half
    _ = cellMass *
        (2 * ∑ heightIndex ∈
          pureWZ2SourceHeavyStandardSqrtSlabs pullback,
            pullback.standardSqrtSlabSourceWeight heightIndex.1) := by
      calc
        (2 * ∑ heightIndex ∈
            pureWZ2SourceHeavyStandardSqrtSlabs pullback,
              volume (pullback.standardSqrtSlabSourceRegion heightIndex.1)) *
              twoScale.coarse.balanced.incidenceMass =
            2 * ((∑ heightIndex ∈
              pureWZ2SourceHeavyStandardSqrtSlabs pullback,
                volume (pullback.standardSqrtSlabSourceRegion heightIndex.1)) *
                  twoScale.coarse.balanced.incidenceMass) := by ring
        _ =
            2 * (∑ heightIndex ∈
              pureWZ2SourceHeavyStandardSqrtSlabs pullback,
                volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) *
                  twoScale.coarse.balanced.incidenceMass) := by
          rw [Finset.sum_mul]
        _ = 2 * (∑ heightIndex ∈
              pureWZ2SourceHeavyStandardSqrtSlabs pullback,
                pullback.standardSqrtSlabSourceWeight heightIndex.1 *
                  twoScale.coarse.balanced.cellMass) := by
          apply congrArg (fun value : ENNReal => 2 * value)
          apply Finset.sum_congr rfl
          intro heightIndex _
          exact pullback.standardSqrtSlab_sourceWeight_cross heightIndex.1
        _ = cellMass *
            (2 * ∑ heightIndex ∈
              pureWZ2SourceHeavyStandardSqrtSlabs pullback,
                pullback.standardSqrtSlabSourceWeight heightIndex.1) := by
          rw [← Finset.sum_mul]
          ring

theorem sourceHeavyStandardSqrtSlabs_nonempty :
    (pureWZ2SourceHeavyStandardSqrtSlabs pullback).Nonempty := by
  have hsourcePos : 0 < volume pullback.shading.union := by
    rw [pullback.volume_eq]
    have hselected : pullback.selectedCells.Nonempty := by
      by_contra hnone
      have hcells : pullback.selectedCells = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnone
      have hfinePos :
          0 < volume twoScale.fine.refined.union :=
        (ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos
            twoScale.coarseGrains.extremal.delta_pos _)).trans_le
          twoScale.fine.refined_volume_lower
      rw [← pullback.selected_count_mul_coarse_volume, hcells] at hfinePos
      exact (lt_irrefl (0 : ENNReal)) <| by
        simpa only [Finset.card_empty, Nat.cast_zero, zero_mul] using hfinePos
    exact ENNReal.mul_pos
      (by exact_mod_cast hselected.card_pos.ne')
      twoScale.coarse.balanced.cellMass_pos.ne'
  have hretained :=
    pullback.sourceHeavyStandardSqrtSlabs_retains_half
  by_contra hempty
  have hempty' :
      pureWZ2SourceHeavyStandardSqrtSlabs pullback = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  rw [hempty'] at hretained
  simp only [Finset.sum_empty, mul_zero] at hretained
  exact (not_le_of_gt hsourcePos) hretained

end PureWZ2TwoScaleCellPullbackData

end Kakeya.Assouad

end
