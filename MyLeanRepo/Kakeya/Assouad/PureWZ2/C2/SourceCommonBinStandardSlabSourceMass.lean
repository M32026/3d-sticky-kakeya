import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinStandardSlabMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.BalancedSafeWindow

/-!
# Exact source-mass partition by standard slabs

The occupied unshifted standard slabs are the fibres of the canonical
second-parent height map on the selected rho-cells.  Their source masses
therefore sum exactly to the pulled-back source mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2TwoScaleCellPullbackData

variable
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)

theorem selectedCells_card_eq_sum_standardSqrtSlabRhoCells :
    pullback.selectedCells.card =
      ∑ heightIndex ∈ pullback.standardSqrtSlabIndices,
        (pullback.standardSqrtSlabRhoCells heightIndex).card := by
  have hmaps :
      Set.MapsTo pullback.standardSqrtSlabIndex
        (pullback.selectedCells : Set (ℤ × ℤ × ℤ))
        (pullback.standardSqrtSlabIndices : Set ℤ) := by
    intro cell hcell
    exact Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
  have hcount := Finset.card_eq_sum_card_fiberwise hmaps
  simpa [standardSqrtSlabRhoCells] using hcount

/-- Exact source-volume partition over occupied standard slabs. -/
theorem sum_standardSqrtSlabSourceRegion_volume :
    (∑ heightIndex ∈ pullback.standardSqrtSlabIndices,
      volume (pullback.standardSqrtSlabSourceRegion heightIndex)) =
        volume pullback.shading.union := by
  simp_rw [pullback.standardSqrtSlabSourceRegion_volume]
  rw [← Finset.sum_mul]
  rw [pullback.volume_eq]
  congr 1
  exact_mod_cast
    pullback.selectedCells_card_eq_sum_standardSqrtSlabRhoCells.symm

/-- Subtype-indexed form used by the standard-slab graph family. -/
theorem sum_standardSqrtSlabSourceRegion_volume_subtype :
    (∑ heightIndex :
        {heightIndex // heightIndex ∈ pullback.standardSqrtSlabIndices},
      volume
        (pullback.standardSqrtSlabSourceRegion heightIndex.1)) =
      volume pullback.shading.union := by
  rw [← pullback.sum_standardSqrtSlabSourceRegion_volume]
  rw [Finset.sum_subtype
    pullback.standardSqrtSlabIndices (fun _ => Iff.rfl)]

/-- Indexed original-source mass carried by one standard slab. -/
def standardSqrtSlabSourceWeight (heightIndex : ℤ) : ENNReal :=
  ((pullback.standardSqrtSlabRhoCells heightIndex).card : ENNReal) *
    twoScale.coarse.balanced.incidenceMass

/-- Exact indexed-mass partition over all occupied standard slabs. -/
theorem sum_standardSqrtSlabSourceWeight :
    (∑ heightIndex ∈ pullback.standardSqrtSlabIndices,
      pullback.standardSqrtSlabSourceWeight heightIndex) =
        pullback.shading.mass := by
  simp_rw [standardSqrtSlabSourceWeight]
  rw [← Finset.sum_mul, pullback.mass_eq]
  congr 1
  exact_mod_cast
    pullback.selectedCells_card_eq_sum_standardSqrtSlabRhoCells.symm

/-- Subtype-indexed form of the exact standard-slab mass partition. -/
theorem sum_standardSqrtSlabSourceWeight_subtype :
    (∑ heightIndex :
        {heightIndex // heightIndex ∈ pullback.standardSqrtSlabIndices},
      pullback.standardSqrtSlabSourceWeight heightIndex.1) =
      pullback.shading.mass := by
  rw [← pullback.sum_standardSqrtSlabSourceWeight]
  rw [Finset.sum_subtype
    pullback.standardSqrtSlabIndices (fun _ => Iff.rfl)]

/-- The source-volume and indexed-mass weights on one standard slab use the
same rho-cell count. -/
theorem standardSqrtSlab_sourceWeight_cross (heightIndex : ℤ) :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex) *
        twoScale.coarse.balanced.incidenceMass =
      pullback.standardSqrtSlabSourceWeight heightIndex *
        twoScale.coarse.balanced.cellMass := by
  rw [pullback.standardSqrtSlabSourceRegion_volume]
  unfold standardSqrtSlabSourceWeight
  ring

/-- The genuine second-refined standard-slab regions also sum exactly to the
selected-cell coarse volume. -/
theorem sum_standardSqrtSlabCoarseRegion_volume :
    (∑ heightIndex ∈ pullback.standardSqrtSlabIndices,
      volume (pullback.standardSqrtSlabCoarseRegion heightIndex)) =
        volume twoScale.fine.refined.union := by
  simp_rw [pullback.standardSqrtSlabCoarseRegion_volume]
  rw [← Finset.sum_mul]
  rw [← pullback.selected_count_mul_coarse_volume]
  congr 1
  exact_mod_cast
    pullback.selectedCells_card_eq_sum_standardSqrtSlabRhoCells.symm

/-- Only `O(1 / sqrt rho)` unshifted standard slabs meet the paper crop. -/
theorem standardSqrtSlabIndices_card_mul_sqrt_le :
    (pullback.standardSqrtSlabIndices.card : ℝ) * Real.sqrt rho ≤
      2 + 3 * Real.sqrt rho := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  let root := Real.sqrt rho
  have hroot : 0 < root := Real.sqrt_pos.mpr hrho
  let lower : ℤ := Int.floor ((-1 - root / 2) / root)
  let upper : ℤ := Int.floor ((1 + root / 2) / root)
  have hcenter :
      ∀ cell ∈ pullback.selectedCells,
        |pureWZ2PaperCellCenterHeight root
            (pullback.standardSecondParent cell)| ≤
          1 + root / 2 := by
    intro cell hcell
    have hactive :
        cell ∈ wz1PaperActiveCells twoScale.fine.refined
          twoScale.coarseGrains.extremal.delta_pos := by
      rwa [pullback.selectedCells_eq] at hcell
    rcases
        ((mem_wz1PaperActiveCells twoScale.fine.refined
          twoScale.coarseGrains.extremal.delta_pos cell).mp hactive).2
      with
      ⟨point, hpointFine, hpointCell⟩
    have hbox := shading_union_subset_axisBox hpointFine
    have hpointHeight : |point (2 : Fin 3)| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
    have hpointParent :
        point ∈ wz1PaperGridCube root
          (pullback.standardSecondParent cell) := by
      simpa [root, twoScale.sqrtRequested_eq] using
        pullback.standardSecondParent_cell_subset hcell
          (by simpa only [twoScale.rhoRequested_eq] using hpointCell)
    have hparentBounds := hpointParent
    rw [wz1PaperGridCube_eq_Ico hroot
      (pullback.standardSecondParent cell)] at hparentBounds
    have hcenterDistance :
        |pureWZ2PaperCellCenterHeight root
              (pullback.standardSecondParent cell) -
            point (2 : Fin 3)| ≤
          root / 2 := by
      rw [abs_le]
      constructor
      · calc
          -(root / 2) =
              pureWZ2PaperCellCenterHeight root
                  (pullback.standardSecondParent cell) -
                (((pullback.standardSecondParent cell).2.2 : ℝ) + 1) *
                  root := by
                    dsimp only [pureWZ2PaperCellCenterHeight]
                    ring
          _ ≤
              pureWZ2PaperCellCenterHeight root
                  (pullback.standardSecondParent cell) -
                point (2 : Fin 3) :=
            sub_le_sub_left hparentBounds.2.2.2.2.2.le _
      · calc
          pureWZ2PaperCellCenterHeight root
                (pullback.standardSecondParent cell) -
              point (2 : Fin 3) ≤
            pureWZ2PaperCellCenterHeight root
                (pullback.standardSecondParent cell) -
              ((pullback.standardSecondParent cell).2.2 : ℝ) * root :=
            sub_le_sub_left hparentBounds.2.2.2.2.1 _
          _ = root / 2 := by
            dsimp only [pureWZ2PaperCellCenterHeight]
            ring
    calc
      |pureWZ2PaperCellCenterHeight root
          (pullback.standardSecondParent cell)| ≤
        |pureWZ2PaperCellCenterHeight root
              (pullback.standardSecondParent cell) -
            point (2 : Fin 3)| +
          |point (2 : Fin 3)| := by
            calc
              _ =
                  |(pureWZ2PaperCellCenterHeight root
                        (pullback.standardSecondParent cell) -
                      point (2 : Fin 3)) +
                    point (2 : Fin 3)| := by ring_nf
              _ ≤ _ := abs_add_le _ _
      _ ≤ root / 2 + 1 :=
        add_le_add hcenterDistance hpointHeight
      _ = 1 + root / 2 := by ring
  have hindexFloor :
      ∀ cell : ℤ × ℤ × ℤ,
        Int.floor
            (pureWZ2PaperCellCenterHeight root
                (pullback.standardSecondParent cell) / root) =
          pullback.standardSqrtSlabIndex cell := by
    intro cell
    unfold standardSqrtSlabIndex pureWZ2PaperCellCenterHeight
    rw [mul_div_cancel_right₀ _ hroot.ne']
    rw [Int.floor_eq_iff]
    constructor <;> norm_num
  have hsubset :
      pullback.standardSqrtSlabIndices ⊆ Finset.Icc lower upper := by
    intro heightIndex hheightIndex
    rw [standardSqrtSlabIndices] at hheightIndex
    rcases Finset.mem_image.mp hheightIndex with
      ⟨cell, hcell, rfl⟩
    have hc := abs_le.mp (hcenter cell hcell)
    rw [Finset.mem_Icc, ← hindexFloor cell]
    constructor
    · apply Int.floor_mono
      apply div_le_div_of_nonneg_right _ hroot.le
      linarith [hc.1]
    · apply Int.floor_mono
      exact div_le_div_of_nonneg_right (by linarith [hc.2]) hroot.le
  have hcardNat :
      pullback.standardSqrtSlabIndices.card ≤
        (Finset.Icc lower upper).card :=
    Finset.card_le_card hsubset
  have hlowerUpper : lower ≤ upper + 1 := by
    have hreal :
        ((-1 - root / 2) / root) ≤
          ((1 + root / 2) / root) := by
      apply div_le_div_of_nonneg_right _ hroot.le
      linarith
    have hfloor : lower ≤ upper := Int.floor_mono hreal
    omega
  have hcardInt :
      ((Finset.Icc lower upper).card : ℤ) =
        upper + 1 - lower :=
    Int.card_Icc_of_le lower upper hlowerUpper
  have hcardReal :
      (pullback.standardSqrtSlabIndices.card : ℝ) ≤
        (upper : ℝ) + 1 - lower := by
    have hcast :
        (pullback.standardSqrtSlabIndices.card : ℤ) ≤
          (Finset.Icc lower upper).card := by
      exact_mod_cast hcardNat
    rw [hcardInt] at hcast
    exact_mod_cast hcast
  have hupper :
      (upper : ℝ) ≤ (1 + root / 2) / root :=
    Int.floor_le _
  have hlower :
      ((-1 - root / 2) / root) < (lower : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hquotient :
      (1 + root / 2) / root -
          ((-1 - root / 2) / root) =
        (2 + root) / root := by
    field_simp [hroot.ne']
    ring
  have hcardBound :
      (pullback.standardSqrtSlabIndices.card : ℝ) ≤
        (2 + root) / root + 2 := by
    rw [← hquotient]
    linarith
  have hmul := mul_le_mul_of_nonneg_right hcardBound hroot.le
  have hcancel : (2 + root) / root * root = 2 + root := by
    field_simp [hroot.ne']
  rw [add_mul, hcancel] at hmul
  calc
    (pullback.standardSqrtSlabIndices.card : ℝ) * Real.sqrt rho =
        (pullback.standardSqrtSlabIndices.card : ℝ) * root := by
      rfl
    _ ≤ 2 + root + 2 * root := hmul
    _ = 2 + 3 * Real.sqrt rho := by
      dsimp only [root]
      ring

theorem standardSqrtSlabIndices_card_mul_sqrtENN_le :
    (pullback.standardSqrtSlabIndices.card : ENNReal) *
        ENNReal.ofReal (Real.sqrt rho) ≤
      ENNReal.ofReal (2 + 3 * Real.sqrt rho) := by
  have hreal := pullback.standardSqrtSlabIndices_card_mul_sqrt_le
  have hcast :
      (pullback.standardSqrtSlabIndices.card : ENNReal) =
        ENNReal.ofReal
          (pullback.standardSqrtSlabIndices.card : ℝ) := by
    simp
  rw [hcast, ← ENNReal.ofReal_mul
    (by exact_mod_cast
      (Nat.zero_le pullback.standardSqrtSlabIndices.card))]
  exact ENNReal.ofReal_mono hreal

end PureWZ2TwoScaleCellPullbackData

end Kakeya.Assouad

end
