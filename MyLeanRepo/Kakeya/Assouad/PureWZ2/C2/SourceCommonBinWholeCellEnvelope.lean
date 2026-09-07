import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinStandardSlabPopular
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinRichSpatialCells
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinIntegratedRichMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CommonBinDistinctIncidence
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GridCubeCover

/-!
# Whole-cell envelopes for one fixed common-bin label

This module performs the cell-density cancellation for one fixed common-bin
label inside an unshifted standard side-`sqrt rho` slab.  The source set is
restricted to an arbitrary measurable set of heights.  Its participating
rho-cells are selected from the standard slab itself, and the geometric
envelope is the union of those complete rho-cubes.

No shifted safe window, parent mass, graph budget, or joint-envelope density
is used.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The fixed `u_*` bin strip enlarged by an additive whole-cell margin. -/
def pureWZ2FixedCommonBinWholeCellStrip
    (slope : ℝ → ℝ) (referenceHeight side margin : ℝ)
    (bin : ℤ) : Set Point3 :=
  {point |
    (bin : ℝ) * side - margin ≤
        inner ℝ point (globalGrainDirection (slope referenceHeight)) ∧
      inner ℝ point (globalGrainDirection (slope referenceHeight)) <
        ((bin : ℝ) + 1) * side + margin}

/-- Vertical thickening used by complete rho-cells meeting a height set. -/
def pureWZ2WholeCellHeightThickening
    (rho : ℝ) (heights : Set ℝ) : Set Point3 :=
  {point | ∃ height ∈ heights,
    |point (2 : Fin 3) - height| ≤ rho}

namespace PureWZ2TwoScaleCellPullbackData

variable
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)

/-- The part of one standard source slab carrying one fixed common-bin label
and whose genuine height belongs to `heights`. -/
def standardSqrtSlabFixedBinHeightRegion
    (heightIndex : ℤ) (referenceHeight : ℝ)
    (heights : Set ℝ) (bin : ℤ) : Set Point3 :=
  pureWZ2FixedCommonBinRegion
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      source.globalGrains.slope referenceHeight (Real.sqrt rho) bin ∩
    {point | point (2 : Fin 3) ∈ heights}

/-- Standard-slab selected rho-cells which meet the fixed-bin height
restriction. -/
def standardSqrtSlabFixedBinRhoCells
    (heightIndex : ℤ) (referenceHeight : ℝ)
    (heights : Set ℝ) (bin : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (pullback.standardSqrtSlabRhoCells heightIndex).filter fun cell =>
    (pullback.standardSqrtSlabFixedBinHeightRegion
        heightIndex referenceHeight heights bin ∩
      wz1PaperGridCube rho cell).Nonempty

/-- The complete rho-cell envelope of one standard-slab fixed-bin source
set. -/
def standardSqrtSlabFixedBinWholeCellEnvelope
    (heightIndex : ℤ) (referenceHeight : ℝ)
    (heights : Set ℝ) (bin : ℤ) : Set Point3 :=
  wz2RetainedCellsUnion rho
    (pullback.standardSqrtSlabFixedBinRhoCells
      heightIndex referenceHeight heights bin)

theorem measurableSet_standardSqrtSlabFixedBinHeightRegion
    (heightIndex : ℤ) (referenceHeight : ℝ)
    {heights : Set ℝ} (hheights : MeasurableSet heights)
    (bin : ℤ) :
    MeasurableSet
      (pullback.standardSqrtSlabFixedBinHeightRegion
        heightIndex referenceHeight heights bin) := by
  apply
    (measurableSet_pureWZ2FixedCommonBinRegion
      (pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex)
      source.globalGrains.slope referenceHeight (Real.sqrt rho) bin).inter
  exact hheights.preimage (by fun_prop)

/-- Exact Fubini identity for one fixed label and an arbitrary measurable
height set. -/
theorem standardSqrtSlabFixedBinHeightRegion_volume
    (heightIndex : ℤ) (referenceHeight : ℝ)
    {heights : Set ℝ} (hheights : MeasurableSet heights)
    (bin : ℤ) :
    volume
        (pullback.standardSqrtSlabFixedBinHeightRegion
          heightIndex referenceHeight heights bin) =
      ∫⁻ height in heights,
        pureWZ2FixedCommonBinSliceMass
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          source.globalGrains.slope referenceHeight
          (Real.sqrt rho) height bin := by
  let fixedRegion :=
    pureWZ2FixedCommonBinRegion
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      source.globalGrains.slope referenceHeight (Real.sqrt rho) bin
  let restricted :=
    pullback.standardSqrtSlabFixedBinHeightRegion
      heightIndex referenceHeight heights bin
  have hslice :
      ∀ height : ℝ,
        wz1Lemma23PlanarSlice restricted height =
          if height ∈ heights then
            wz1Lemma23PlanarSlice fixedRegion height
          else ∅ := by
    intro height
    by_cases hheight : height ∈ heights
    · rw [if_pos hheight]
      ext point
      simp only [wz1Lemma23_mem_planarSlice_iff]
      constructor
      · intro hpoint
        exact hpoint.1
      · intro hpoint
        exact ⟨hpoint, by simpa [point3] using hheight⟩
    · rw [if_neg hheight]
      ext point
      simp only [Set.notMem_empty, iff_false]
      rw [wz1Lemma23_mem_planarSlice_iff]
      intro hpoint
      exact hheight (by simpa [point3] using hpoint.2)
  rw [wz1_lemma23_volume_eq_lintegral_planarSlice restricted
    (pullback.measurableSet_standardSqrtSlabFixedBinHeightRegion
      heightIndex referenceHeight hheights bin)]
  rw [← lintegral_indicator hheights]
  apply lintegral_congr
  intro height
  rw [hslice height]
  by_cases hheight : height ∈ heights
  · simp [hheight, fixedRegion, pureWZ2FixedCommonBinSliceMass]
  · simp [hheight]

/-- The fixed-bin height restriction is exactly the disjoint union of its
nonempty standard-slab rho-cell pieces. -/
theorem standardSqrtSlabFixedBinHeightRegion_eq_biUnion
    (heightIndex : ℤ) (referenceHeight : ℝ)
    (heights : Set ℝ) (bin : ℤ) :
    pullback.standardSqrtSlabFixedBinHeightRegion
        heightIndex referenceHeight heights bin =
      ⋃ cell ∈ pullback.standardSqrtSlabFixedBinRhoCells
          heightIndex referenceHeight heights bin,
        pullback.standardSqrtSlabFixedBinHeightRegion
            heightIndex referenceHeight heights bin ∩
          wz1PaperGridCube rho cell := by
  ext point
  constructor
  · intro hpoint
    have hpointSlab :
        point ∈ pullback.standardSqrtSlabSourceRegion heightIndex :=
      hpoint.1.1
    change point ∈
      pullback.shading.union ∩
        wz2RetainedCellsUnion rho
          (pullback.standardSqrtSlabRhoCells heightIndex) at hpointSlab
    rw [wz2RetainedCellsUnion] at hpointSlab
    rcases Set.mem_iUnion₂.mp hpointSlab.2 with
      ⟨cell, hcell, hpointCell⟩
    have hcellSelected :
        cell ∈ pullback.standardSqrtSlabFixedBinRhoCells
          heightIndex referenceHeight heights bin := by
      rw [standardSqrtSlabFixedBinRhoCells, Finset.mem_filter]
      exact ⟨hcell, ⟨point, hpoint, hpointCell⟩⟩
    exact Set.mem_iUnion₂.mpr
      ⟨cell, hcellSelected, hpoint, hpointCell⟩
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨cell, _hcell, hpointPiece⟩
    exact hpointPiece.1

/-- Exact mass decomposition over the participating standard-slab
rho-cells. -/
theorem standardSqrtSlabFixedBinHeightRegion_volume_eq_sum
    (heightIndex : ℤ) (referenceHeight : ℝ)
    {heights : Set ℝ} (hheights : MeasurableSet heights)
    (bin : ℤ) :
    volume
        (pullback.standardSqrtSlabFixedBinHeightRegion
          heightIndex referenceHeight heights bin) =
      ∑ cell ∈ pullback.standardSqrtSlabFixedBinRhoCells
          heightIndex referenceHeight heights bin,
        volume
          (pullback.standardSqrtSlabFixedBinHeightRegion
              heightIndex referenceHeight heights bin ∩
            wz1PaperGridCube rho cell) := by
  calc
    volume
        (pullback.standardSqrtSlabFixedBinHeightRegion
          heightIndex referenceHeight heights bin) =
      volume
        (⋃ cell ∈ pullback.standardSqrtSlabFixedBinRhoCells
            heightIndex referenceHeight heights bin,
          pullback.standardSqrtSlabFixedBinHeightRegion
              heightIndex referenceHeight heights bin ∩
            wz1PaperGridCube rho cell) := by
        exact congrArg volume
          (pullback.standardSqrtSlabFixedBinHeightRegion_eq_biUnion
            heightIndex referenceHeight heights bin)
    _ = ∑ cell ∈ pullback.standardSqrtSlabFixedBinRhoCells
          heightIndex referenceHeight heights bin,
        volume
          (pullback.standardSqrtSlabFixedBinHeightRegion
              heightIndex referenceHeight heights bin ∩
            wz1PaperGridCube rho cell) := by
      apply MeasureTheory.measure_biUnion_finset
      · intro first _ second _ hne
        exact (wz1PaperGridCube_disjoint hne).mono
          Set.inter_subset_right Set.inter_subset_right
      · intro cell _
        exact
          (pullback.measurableSet_standardSqrtSlabFixedBinHeightRegion
            heightIndex referenceHeight hheights bin).inter
            (wz1PaperGridCube_measurable cell)

/-- Each participating fixed-bin piece has at most the balanced source mass
of its ambient selected rho-cell. -/
theorem standardSqrtSlabFixedBinHeightRegion_cell_volume_le
    (heightIndex : ℤ) (referenceHeight : ℝ)
    (heights : Set ℝ) (bin : ℤ)
    {cell : ℤ × ℤ × ℤ}
    (hcell : cell ∈
      pullback.standardSqrtSlabFixedBinRhoCells
        heightIndex referenceHeight heights bin) :
    volume
        (pullback.standardSqrtSlabFixedBinHeightRegion
            heightIndex referenceHeight heights bin ∩
          wz1PaperGridCube rho cell) ≤
      twoScale.coarse.balanced.cellMass := by
  have hcellSlab :
      cell ∈ pullback.standardSqrtSlabRhoCells heightIndex :=
    (Finset.mem_filter.mp hcell).1
  have hsubset :
      pullback.standardSqrtSlabFixedBinHeightRegion
            heightIndex referenceHeight heights bin ∩
          wz1PaperGridCube rho cell ⊆
        pullback.shading.union ∩ wz1PaperGridCube rho cell := by
    rintro point ⟨hpoint, hpointCell⟩
    have hpointSlab :
        point ∈ pullback.standardSqrtSlabSourceRegion heightIndex :=
      hpoint.1.1
    change point ∈
      pullback.shading.union ∩
        wz2RetainedCellsUnion rho
          (pullback.standardSqrtSlabRhoCells heightIndex) at hpointSlab
    exact ⟨hpointSlab.1, hpointCell⟩
  calc
    volume
        (pullback.standardSqrtSlabFixedBinHeightRegion
            heightIndex referenceHeight heights bin ∩
          wz1PaperGridCube rho cell) ≤
      volume (pullback.shading.union ∩ wz1PaperGridCube rho cell) :=
        measure_mono hsubset
    _ = twoScale.coarse.balanced.cellMass :=
      pullback.cell_mass cell
        (pullback.standardSqrtSlabRhoCells_subset heightIndex hcellSlab)

/-- The fixed-bin source mass is bounded by the number of participating
rho-cells times the exact balanced source cell mass. -/
theorem standardSqrtSlabFixedBinHeightRegion_volume_le
    (heightIndex : ℤ) (referenceHeight : ℝ)
    {heights : Set ℝ} (hheights : MeasurableSet heights)
    (bin : ℤ) :
    volume
        (pullback.standardSqrtSlabFixedBinHeightRegion
          heightIndex referenceHeight heights bin) ≤
      ((pullback.standardSqrtSlabFixedBinRhoCells
        heightIndex referenceHeight heights bin).card : ENNReal) *
        twoScale.coarse.balanced.cellMass := by
  rw [pullback.standardSqrtSlabFixedBinHeightRegion_volume_eq_sum
    heightIndex referenceHeight hheights bin]
  calc
    (∑ cell ∈ pullback.standardSqrtSlabFixedBinRhoCells
          heightIndex referenceHeight heights bin,
        volume
          (pullback.standardSqrtSlabFixedBinHeightRegion
              heightIndex referenceHeight heights bin ∩
            wz1PaperGridCube rho cell)) ≤
      ∑ _cell ∈ pullback.standardSqrtSlabFixedBinRhoCells
          heightIndex referenceHeight heights bin,
        twoScale.coarse.balanced.cellMass := by
      apply Finset.sum_le_sum
      intro cell hcell
      exact
        pullback.standardSqrtSlabFixedBinHeightRegion_cell_volume_le
          heightIndex referenceHeight heights bin hcell
    _ =
      ((pullback.standardSqrtSlabFixedBinRhoCells
        heightIndex referenceHeight heights bin).card : ENNReal) *
        twoScale.coarse.balanced.cellMass := by
      simp [Finset.sum_const]

/-- Exact geometric volume of the complete rho-cell envelope. -/
theorem standardSqrtSlabFixedBinWholeCellEnvelope_volume
    (heightIndex : ℤ) (referenceHeight : ℝ)
    (heights : Set ℝ) (bin : ℤ) :
    volume
        (pullback.standardSqrtSlabFixedBinWholeCellEnvelope
          heightIndex referenceHeight heights bin) =
      ((pullback.standardSqrtSlabFixedBinRhoCells
        heightIndex referenceHeight heights bin).card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarse.coarse_extremal.delta_pos
  exact wz1PaperGridCube_volume_biUnion hrho
    (pullback.standardSqrtSlabFixedBinRhoCells
      heightIndex referenceHeight heights bin)

/-- The fixed-bin source set lies in its complete-cell envelope. -/
theorem standardSqrtSlabFixedBinHeightRegion_subset_envelope
    (heightIndex : ℤ) (referenceHeight : ℝ)
    (heights : Set ℝ) (bin : ℤ) :
    pullback.standardSqrtSlabFixedBinHeightRegion
        heightIndex referenceHeight heights bin ⊆
      pullback.standardSqrtSlabFixedBinWholeCellEnvelope
        heightIndex referenceHeight heights bin := by
  intro point hpoint
  rw [pullback.standardSqrtSlabFixedBinHeightRegion_eq_biUnion
    heightIndex referenceHeight heights bin] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with
    ⟨cell, hcell, hpointPiece⟩
  rw [standardSqrtSlabFixedBinWholeCellEnvelope,
    wz2RetainedCellsUnion]
  exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointPiece.2⟩

/-- Whole-cell localization: the complete envelope remains in the fixed
`u_*` strip enlarged by `4*rho`, and in the vertical `rho`-thickening of the
chosen height set. -/
theorem standardSqrtSlabFixedBinWholeCellEnvelope_subset_strip_height
    (heightIndex : ℤ) (referenceHeight : ℝ)
    (heights : Set ℝ) (bin : ℤ) :
    pullback.standardSqrtSlabFixedBinWholeCellEnvelope
        heightIndex referenceHeight heights bin ⊆
      pureWZ2FixedCommonBinWholeCellStrip
          source.globalGrains.slope referenceHeight (Real.sqrt rho)
          (4 * rho) bin ∩
        pureWZ2WholeCellHeightThickening rho heights := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarse.coarse_extremal.delta_pos
  have hroot : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  intro point hpoint
  rw [standardSqrtSlabFixedBinWholeCellEnvelope,
    wz2RetainedCellsUnion] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with
    ⟨cell, hcell, hpointCell⟩
  have hcellMeet :=
    (Finset.mem_filter.mp hcell).2
  rcases hcellMeet with
    ⟨sourcePoint, hsourcePoint, hsourcePointCell⟩
  have hpointBox := hpointCell
  have hsourcePointBox := hsourcePointCell
  rw [wz1PaperGridCube_eq_Ico hrho cell] at hpointBox hsourcePointBox
  have hcoord0 :
      |point 0 - sourcePoint 0| ≤ rho := by
    rw [abs_le]
    constructor <;>
      linarith [hpointBox.1, hpointBox.2.1,
        hsourcePointBox.1, hsourcePointBox.2.1]
  have hcoord1 :
      |point 1 - sourcePoint 1| ≤ rho := by
    rw [abs_le]
    constructor <;>
      linarith [hpointBox.2.2.1, hpointBox.2.2.2.1,
        hsourcePointBox.2.2.1, hsourcePointBox.2.2.2.1]
  have hcoord2 :
      |point 2 - sourcePoint 2| ≤ rho := by
    rw [abs_le]
    constructor <;>
      linarith [hpointBox.2.2.2.2.1, hpointBox.2.2.2.2.2,
        hsourcePointBox.2.2.2.2.1,
        hsourcePointBox.2.2.2.2.2]
  let direction :=
    globalGrainDirection (source.globalGrains.slope referenceHeight)
  have hslope :
      |source.globalGrains.slope referenceHeight| ≤ 3 :=
    source.globalGrains.slope_global_bound referenceHeight
  have hinner :
      |inner ℝ point direction - inner ℝ sourcePoint direction| ≤
        4 * rho := by
    have hformula :
        inner ℝ point direction - inner ℝ sourcePoint direction =
          (point 0 - sourcePoint 0) +
            source.globalGrains.slope referenceHeight *
              (point 1 - sourcePoint 1) := by
      simp [direction, globalGrainDirection, PiLp.inner_apply,
        Fin.sum_univ_succ]
      ring
    rw [hformula]
    calc
      |(point 0 - sourcePoint 0) +
          source.globalGrains.slope referenceHeight *
            (point 1 - sourcePoint 1)| ≤
        |point 0 - sourcePoint 0| +
          |source.globalGrains.slope referenceHeight *
            (point 1 - sourcePoint 1)| := abs_add_le _ _
      _ =
        |point 0 - sourcePoint 0| +
          |source.globalGrains.slope referenceHeight| *
            |point 1 - sourcePoint 1| := by rw [abs_mul]
      _ ≤ rho + 3 * rho := by gcongr
      _ = 4 * rho := by ring
  have hlabel :
      pureWZ2FixedCommonBinLabel source.globalGrains.slope
        referenceHeight (Real.sqrt rho) sourcePoint = bin :=
    hsourcePoint.1.2
  have hlabelBounds :
      (bin : ℝ) * Real.sqrt rho ≤
          inner ℝ sourcePoint direction ∧
        inner ℝ sourcePoint direction <
          ((bin : ℝ) + 1) * Real.sqrt rho := by
    unfold pureWZ2FixedCommonBinLabel at hlabel
    rw [Int.floor_eq_iff] at hlabel
    constructor
    · exact (le_div_iff₀ hroot).mp hlabel.1
    · exact (div_lt_iff₀ hroot).mp hlabel.2
  constructor
  · change
      (bin : ℝ) * Real.sqrt rho - 4 * rho ≤
          inner ℝ point direction ∧
        inner ℝ point direction <
          ((bin : ℝ) + 1) * Real.sqrt rho + 4 * rho
    rw [abs_le] at hinner
    constructor <;> linarith [hlabelBounds.1, hlabelBounds.2]
  · exact
      ⟨sourcePoint (2 : Fin 3), hsourcePoint.2, hcoord2⟩

/-- Cancellation of the common source density.  The hypotheses are exactly
the fixed-label lower bound and the per-rho-cell source/cube cross identity;
positivity and finiteness of `theta` follow from the balanced source cell
mass and the positive rho-cube volume. -/
theorem standardSqrtSlabFixedBinWholeCellEnvelope_cancellation
    (heightIndex : ℤ) (referenceHeight : ℝ)
    {heights : Set ℝ} (hheights : MeasurableSet heights)
    (bin : ℤ) (theta : ENNReal) (K : ℕ)
    (hfixed :
      theta * K * twoScale.fine.balanced.cellMass ≤
        20 * volume
          (pullback.standardSqrtSlabFixedBinHeightRegion
            heightIndex referenceHeight heights bin))
    (hcellCross :
      theta * volume (wz1PaperGridCube rho (0, 0, 0)) =
        twoScale.coarse.balanced.cellMass) :
    K * twoScale.fine.balanced.cellMass ≤
      20 * volume
        (pullback.standardSqrtSlabFixedBinWholeCellEnvelope
          heightIndex referenceHeight heights bin) := by
  let cells :=
    pullback.standardSqrtSlabFixedBinRhoCells
      heightIndex referenceHeight heights bin
  let cubeVolume := volume (wz1PaperGridCube rho (0, 0, 0))
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarse.coarse_extremal.delta_pos
  have hcubePos : 0 < cubeVolume := by
    simpa [cubeVolume] using
      wz1PaperGridCube_volume_pos hrho (0, 0, 0)
  have hthetaPos : 0 < theta := by
    apply pos_of_mul_pos_left
    · rw [hcellCross]
      exact twoScale.coarse.balanced.cellMass_pos
    · exact bot_le
  have hthetaTop : theta ≠ ⊤ := by
    intro htop
    have hproductTop : theta * cubeVolume = ⊤ := by
      simp [htop, hcubePos.ne']
    have hcellTop : twoScale.coarse.balanced.cellMass = ⊤ := by
      rw [← hcellCross]
      exact hproductTop
    exact twoScale.coarse.balanced.cellMass_ne_top hcellTop
  have hwhole :=
    CommonBinDistinctIncidence.whole_cell_volume_lower
      K 5 cells.card twoScale.fine.balanced.cellMass
      (volume
        (pullback.standardSqrtSlabFixedBinHeightRegion
          heightIndex referenceHeight heights bin))
      twoScale.coarse.balanced.cellMass cubeVolume theta
      (by
        norm_num
        exact hfixed)
      (by
        simpa [cells, mul_comm] using
          pullback.standardSqrtSlabFixedBinHeightRegion_volume_le
            heightIndex referenceHeight hheights bin)
      (by simpa [cubeVolume] using hcellCross.symm)
      hthetaPos hthetaTop
  calc
    K * twoScale.fine.balanced.cellMass ≤
        4 * (5 : ENNReal) * ((cells.card : ENNReal) * cubeVolume) :=
      hwhole
    _ = 20 * volume
        (pullback.standardSqrtSlabFixedBinWholeCellEnvelope
          heightIndex referenceHeight heights bin) := by
      rw [pullback.standardSqrtSlabFixedBinWholeCellEnvelope_volume
        heightIndex referenceHeight heights bin]
      dsimp only [cells, cubeVolume]
      ring

end PureWZ2TwoScaleCellPullbackData

end Kakeya.Assouad

end
