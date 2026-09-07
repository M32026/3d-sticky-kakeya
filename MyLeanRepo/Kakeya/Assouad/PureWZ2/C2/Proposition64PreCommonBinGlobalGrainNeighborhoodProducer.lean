import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64PreCommonBinLocalGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSourcePopularHeights
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinStandardSlabHeavySelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinRichSpatialCells
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CommonBinStandardParentWeightedSelection
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume

/-!
# Proposition 6.4 pre-common-bin global-grain neighborhood producer

This is the finite producer for the global-neighborhood step of WZ1
Lemma 5.3 (`locallyLinearLem`).  It first chooses one literal unshifted
side-`sqrt rho` source slab, constructs the paper's source-popular height set
`Z_S`, and then chooses the fixed-line reference height `z₀` from `Z_S`.
The spatial objects counted by
`K` are the distinct side-`sqrt rho` paper-grid cubes meeting that one bin.

Before the mod-`512` selection, one maximum-mass cube is retained in each
coarse `y` layer.  The final residue therefore loses at most `512`; the
bounded number of possible `x` cubes in one `y` layer is paid before this
residue.  Every shading and every witness below is a restriction of the same
`pullback.shading`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

namespace PureWZ2Node05V4RichTwoScaleCellPullbackData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)

/-- The exact final-source shading over a finite family of genuine
side-`sqrt rho` second-cover parents. -/
def preCommonBinParentsFineShading
    (parents : Finset (ℤ × ℤ × ℤ)) :
    WZ1PaperTubeShading current.grain.family where
  carrier index :=
    ⋃ parent ∈ parents,
      (pullback.preCommonBinFinePullbackShading parent).carrier index
  measurable_carrier index :=
    MeasurableSet.biUnion parents.finite_toSet.countable fun parent _ =>
      (pullback.preCommonBinFinePullbackShading parent).measurable_carrier index
  subset_body index := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨parent, _hparent, hpointParent⟩
    exact
      (pullback.preCommonBinFinePullbackShading parent).subset_body
        index hpointParent

theorem preCommonBinParentsFineShading_sub_source
    (parents : Finset (ℤ × ℤ × ℤ)) :
    PureWZ2PaperIsSubshading
      (pullback.preCommonBinParentsFineShading parents)
      current.grain.shading := by
  intro index point hpoint
  rcases Set.mem_iUnion₂.mp hpoint with
    ⟨parent, _hparent, hpointParent⟩
  exact
    pullback.preCommonBinFinePullbackShading_sub_source
      parent index hpointParent

theorem preCommonBinParentsFineShading_union
    (parents : Finset (ℤ × ℤ × ℤ)) :
    (pullback.preCommonBinParentsFineShading parents).union =
      ⋃ parent ∈ parents,
        pullback.preCommonBinFinePullback parent := by
  ext point
  constructor
  · rintro ⟨index, hpoint⟩
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨parent, hparent, hpointParent⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨parent, hparent, ?_⟩
    rw [← pullback.preCommonBinFinePullbackShading_union parent]
    exact ⟨index, hpointParent⟩
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨parent, hparent, hpointParent⟩
    rw [← pullback.preCommonBinFinePullbackShading_union parent] at hpointParent
    rcases hpointParent with ⟨index, hindex⟩
    exact
      ⟨index, Set.mem_iUnion₂.mpr
        ⟨parent, hparent, hindex⟩⟩

/-- Distinct second-cover parents have disjoint exact source pullbacks, so
indexed source mass is exactly additive over a finite parent family. -/
theorem preCommonBinParentsFineShading_mass
    (parents : Finset (ℤ × ℤ × ℤ)) :
    (pullback.preCommonBinParentsFineShading parents).mass =
      ∑ parent ∈ parents,
        (pullback.preCommonBinFinePullbackShading parent).mass := by
  have hcarrier :
      ∀ index : Fin current.grain.family.card,
        volume
            ((pullback.preCommonBinParentsFineShading parents).carrier index) =
          ∑ parent ∈ parents,
            volume
              ((pullback.preCommonBinFinePullbackShading parent).carrier
                index) := by
    intro index
    apply MeasureTheory.measure_biUnion_finset
    · intro first _hfirst second _hsecond hne
      exact
        (wz1PaperGridCube_disjoint
          (scale := sqrtRequested.1) hne).mono
          (fun _point hpoint => by
            apply pullback.preCommonBinFinePullback_subset_parent
            rw [← pullback.preCommonBinFinePullbackShading_union first]
            exact ⟨index, hpoint⟩)
          (fun _point hpoint => by
            apply pullback.preCommonBinFinePullback_subset_parent
            rw [← pullback.preCommonBinFinePullbackShading_union second]
            exact ⟨index, hpoint⟩)
    · intro parent _hparent
      exact
        (pullback.preCommonBinFinePullbackShading parent).measurable_carrier
          index
  calc
    (pullback.preCommonBinParentsFineShading parents).mass =
        ∑ index : Fin current.grain.family.card,
          ∑ parent ∈ parents,
            volume
              ((pullback.preCommonBinFinePullbackShading parent).carrier
                index) := by
      apply Finset.sum_congr rfl
      intro index _hindex
      exact hcarrier index
    _ =
        ∑ parent ∈ parents,
          ∑ index : Fin current.grain.family.card,
            volume
              ((pullback.preCommonBinFinePullbackShading parent).carrier
                index) := by
      rw [Finset.sum_comm]
    _ =
        ∑ parent ∈ parents,
          (pullback.preCommonBinFinePullbackShading parent).mass := by
      rfl

/-- The first terminal point-multiplicity floor integrated on one exact
source pullback, then crossed with the second balanced cell identity. -/
theorem preCommonBinFinePullbackShading_mass_lower_cross
    {parent : WZ2PaperCellIndex}
    (hparent : parent ∈
      twoScale.second.terminal.balanced.activeCells) :
    (((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
          twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
        twoScale.second.terminal.balanced.cellMass) *
          pullback.firstPostBalanced.cellMass ≤
      (pullback.preCommonBinFinePullbackShading parent).mass *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  let localShading :=
    pullback.preCommonBinFinePullbackShading parent
  let floor : ℕ :=
    twoScale.first.fourDegreeReceipts.fineDegreeFloor *
      twoScale.first.fourDegreeReceipts.muFine
  have hlocalFloor :
      ∀ point ∈ localShading.union,
        (floor : ENNReal) ≤
          (localShading.pointMultiplicity point : ENNReal) := by
    intro point hpoint
    rcases hpoint with ⟨ambientIndex, hlocal⟩
    have hregion :
        point ∈ wz2RetainedCellsUnion rho
          (pullback.preCommonBinRhoCells parent) :=
      hlocal.2
    have hpostSource :
        point ∈ pullback.postSourceShading.union :=
      ⟨ambientIndex, hlocal.1⟩
    have hlocalMultiplicity :
        localShading.pointMultiplicity point =
          pullback.postSourceShading.pointMultiplicity point := by
      simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
      congr 1
      apply Finset.filter_congr
      intro index _
      change
        (point ∈ pullback.postSourceShading.carrier index ∩
            wz2RetainedCellsUnion rho
              (pullback.preCommonBinRhoCells parent)) ↔
          point ∈ pullback.postSourceShading.carrier index
      exact and_iff_left hregion
    have hpostFine :
        point ∈ pullback.postFirstFineShading.union := by
      rw [← pullback.zeroExtension.union_eq]
      rw [← pullback.postSourceShading_eq]
      exact hpostSource
    rcases hpostFine with ⟨fineIndex, hpostFineCarrier⟩
    have hretained :
        point ∈ pureWZ2Node05RetainedCellRegion rho
          pullback.selectedCells := by
      rw [pullback.postFirstFineShading_eq] at hpostFineCarrier
      exact hpostFineCarrier.2
    have hpostFineMultiplicity :
        pullback.postFirstFineShading.pointMultiplicity point =
          twoScale.first.refinedFineShading.pointMultiplicity point := by
      simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
      congr 1
      apply Finset.filter_congr
      intro index _
      rw [pullback.postFirstFineShading_eq,
        pureWZ2Node05RestrictToCells_carrier]
      exact and_iff_left hretained
    have hrawPoint :
        point ∈ twoScale.first.refinedFineShading.union :=
      ⟨fineIndex, by
        rw [pullback.postFirstFineShading_eq] at hpostFineCarrier
        exact hpostFineCarrier.1⟩
    have hrawFloor :=
      twoScale.first.fourDegreeReceipts
        |>.fine_pointMultiplicity_floor_on_union hrawPoint
    rw [hlocalMultiplicity, pullback.postSourceShading_eq,
      pullback.zeroExtension.pointMultiplicity_eq,
      hpostFineMultiplicity]
    exact_mod_cast hrawFloor
  have hmass :
      (floor : ENNReal) * volume localShading.union ≤
        localShading.mass :=
    multiplicity_floor_le_mass hlocalFloor
  have hvolumeCross :=
    pullback.preCommonBinFinePullback_mass_cross hparent
  rw [pullback.preCommonBinFinePullbackShading_union] at hmass
  calc
    ((floor : ENNReal) *
          twoScale.second.terminal.balanced.cellMass) *
        pullback.firstPostBalanced.cellMass =
      (floor : ENNReal) *
        (volume (pullback.preCommonBinFinePullback parent) *
          volume (wz1PaperGridCube rho (0, 0, 0))) := by
      rw [hvolumeCross]
      ring
    _ = ((floor : ENNReal) *
          volume (pullback.preCommonBinFinePullback parent)) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by ring
    _ ≤ localShading.mass *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
      gcongr

theorem preCommonBinFinePullbackShading_mass_upper_cross
    {parent : WZ2PaperCellIndex}
    (hparent : parent ∈
      twoScale.second.terminal.balanced.activeCells) :
    (pullback.preCommonBinFinePullbackShading parent).mass *
          volume (wz1PaperGridCube rho (0, 0, 0)) ≤
      (twoScale.first.fourDegreeReceipts.regularity : ENNReal) *
        ((((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
              twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
            twoScale.second.terminal.balanced.cellMass) *
          pullback.firstPostBalanced.cellMass) := by
  let localShading :=
    pullback.preCommonBinFinePullbackShading parent
  let cap : ℕ :=
    (twoScale.first.fourDegreeReceipts.regularity *
      twoScale.first.fourDegreeReceipts.fineDegreeFloor) *
        twoScale.first.fourDegreeReceipts.muFine
  have hlocalCap :
      ∀ point ∈ localShading.union,
        (localShading.pointMultiplicity point : ENNReal) ≤
          (cap : ENNReal) := by
    intro point hpoint
    rcases hpoint with ⟨ambientIndex, hlocal⟩
    have hregion :
        point ∈ wz2RetainedCellsUnion rho
          (pullback.preCommonBinRhoCells parent) :=
      hlocal.2
    have hpostSource :
        point ∈ pullback.postSourceShading.union :=
      ⟨ambientIndex, hlocal.1⟩
    have hlocalMultiplicity :
        localShading.pointMultiplicity point =
          pullback.postSourceShading.pointMultiplicity point := by
      simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
      congr 1
      apply Finset.filter_congr
      intro index _
      change
        (point ∈ pullback.postSourceShading.carrier index ∩
            wz2RetainedCellsUnion rho
              (pullback.preCommonBinRhoCells parent)) ↔
          point ∈ pullback.postSourceShading.carrier index
      exact and_iff_left hregion
    have hpostFine :
        point ∈ pullback.postFirstFineShading.union := by
      rw [← pullback.zeroExtension.union_eq]
      rw [← pullback.postSourceShading_eq]
      exact hpostSource
    rcases hpostFine with ⟨fineIndex, hpostFineCarrier⟩
    have hretained :
        point ∈ pureWZ2Node05RetainedCellRegion rho
          pullback.selectedCells := by
      rw [pullback.postFirstFineShading_eq] at hpostFineCarrier
      exact hpostFineCarrier.2
    have hpostFineMultiplicity :
        pullback.postFirstFineShading.pointMultiplicity point =
          twoScale.first.refinedFineShading.pointMultiplicity point := by
      simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
      congr 1
      apply Finset.filter_congr
      intro index _
      rw [pullback.postFirstFineShading_eq,
        pureWZ2Node05RestrictToCells_carrier]
      exact and_iff_left hretained
    rw [hlocalMultiplicity, pullback.postSourceShading_eq,
      pullback.zeroExtension.pointMultiplicity_eq,
      hpostFineMultiplicity]
    exact_mod_cast
      twoScale.first.fourDegreeReceipts.fine_pointMultiplicity_upper point
  have hmass :
      localShading.mass ≤
        (cap : ENNReal) * volume localShading.union :=
    mass_le_of_pointMultiplicity_le hlocalCap
  have hvolumeCross :=
    pullback.preCommonBinFinePullback_mass_cross hparent
  rw [pullback.preCommonBinFinePullbackShading_union] at hmass
  calc
    localShading.mass *
          volume (wz1PaperGridCube rho (0, 0, 0)) ≤
      ((cap : ENNReal) *
          volume (pullback.preCommonBinFinePullback parent)) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
      gcongr
    _ = (cap : ENNReal) *
        (volume (pullback.preCommonBinFinePullback parent) *
          volume (wz1PaperGridCube rho (0, 0, 0))) := by ring
    _ = (cap : ENNReal) *
        (twoScale.second.terminal.balanced.cellMass *
          pullback.firstPostBalanced.cellMass) := by rw [hvolumeCross]
    _ =
      (twoScale.first.fourDegreeReceipts.regularity : ENNReal) *
        ((((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
              twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
            twoScale.second.terminal.balanced.cellMass) *
          pullback.firstPostBalanced.cellMass) := by
      dsimp only [cap]
      push_cast
      ring

/-- Pure crop geometry: only `O(1 / sqrt rho)` unshifted standard slabs can
meet the post-synchronized source.  No family cardinality enters the
right-hand side. -/
theorem standardSqrtSlabIndices_card_mul_sqrt_le :
    (pullback.standardSqrtSlabIndices.card : ℝ) * Real.sqrt rho ≤
      2 + 3 * Real.sqrt rho := by
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
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
        cell ∈ wz1PaperActiveCells twoScale.secondRefinedFineShading
          twoScale.first.publicSticky.coarse_extremal.delta_pos := by
      rwa [pullback.selectedCells_eq] at hcell
    rcases
        ((mem_wz1PaperActiveCells twoScale.secondRefinedFineShading
          twoScale.first.publicSticky.coarse_extremal.delta_pos cell).mp
          hactive).2 with
      ⟨point, hpointFine, hpointCell⟩
    rcases hpointFine with ⟨fineIndex, hpointFine⟩
    have hpointRaw : point ∈ pullback.rawFirstT6Shading.union := by
      refine ⟨twoScale.secondSticky.selected.embedding fineIndex, ?_⟩
      rw [pullback.rawFirstT6Shading_eq]
      exact twoScale.secondSticky.subshading fineIndex hpointFine
    have hbox := shading_union_subset_axisBox hpointRaw
    have hpointHeight : |point (2 : Fin 3)| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
    have hpointParent :
        point ∈ wz1PaperGridCube root
          (pullback.standardSecondParent cell) := by
      simpa [root, pullback.sqrtRequested_eq] using
        pullback.standardSecondParent_cell_subset hcell
          (by simpa only [pullback.rhoRequested_eq] using hpointCell)
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

theorem standardSqrtSlabIndices_card_mul_sqrtENN_le_five
    (hrhoOne : rho ≤ 1) :
    (pullback.standardSqrtSlabIndices.card : ENNReal) *
        ENNReal.ofReal (Real.sqrt rho) ≤ 5 := by
  have hreal := pullback.standardSqrtSlabIndices_card_mul_sqrt_le
  have hrootOne : Real.sqrt rho ≤ 1 :=
    Real.sqrt_le_one.mpr hrhoOne
  have hcast :
      (pullback.standardSqrtSlabIndices.card : ENNReal) =
        ENNReal.ofReal
          (pullback.standardSqrtSlabIndices.card : ℝ) := by
    simp
  rw [hcast, ← ENNReal.ofReal_mul
    (by exact_mod_cast
      (Nat.zero_le pullback.standardSqrtSlabIndices.card))]
  calc
    ENNReal.ofReal
        ((pullback.standardSqrtSlabIndices.card : ℝ) *
          Real.sqrt rho) ≤
      ENNReal.ofReal (2 + 3 * Real.sqrt rho) :=
        ENNReal.ofReal_mono hreal
    _ ≤ 5 := by
      calc
        ENNReal.ofReal (2 + 3 * Real.sqrt rho) ≤
            ENNReal.ofReal 5 :=
          ENNReal.ofReal_mono (by linarith)
        _ = 5 := by norm_num

end PureWZ2Node05V4RichTwoScaleCellPullbackData

/-- A side-`sqrt rho` spatial cube's contribution to one side-`delta`
global-grain bin.  The two scales are deliberately separate. -/
def pureWZ2PreCommonBinGlobalLineSpatialCellSliceMass
    (E : Set Point3) (slope : ℝ → ℝ)
    (lineHeight lineScale spatialScale : ℝ) (bin : ℤ)
    (parent : ℤ × ℤ × ℤ) : ENNReal :=
  volume
    (wz1Lemma23PlanarSlice
      (pureWZ2FixedCommonBinRegion
          E slope lineHeight lineScale bin ∩
        wz1PaperGridCube spatialScale parent)
      lineHeight)

/-- Once the global bin is fixed at the fine scale `lineScale`, its
intersection with one side-`spatialScale` planar cube is a single strip.  The
resulting area bound is geometric and contains no AD covering-number factor. -/
theorem pureWZ2PreCommonBinGlobalLineSpatialCellSliceMass_le_strip
    {E : Set Point3} (hE : MeasurableSet E)
    (slope : ℝ → ℝ) (lineHeight : ℝ)
    {lineScale spatialScale : ℝ}
    (hlineScale : 0 < lineScale)
    (hspatialScale : 0 < spatialScale)
    (bin : ℤ) (parent : ℤ × ℤ × ℤ) :
    pureWZ2PreCommonBinGlobalLineSpatialCellSliceMass
        E slope lineHeight lineScale spatialScale bin parent ≤
      ENNReal.ofReal (4 * spatialScale * lineScale) := by
  apply paperGridCube_planarSlice_volume_le_of_projection_strip
    (measurableSet_pureWZ2FixedCommonBinRegion
      hE slope lineHeight lineScale bin)
    hspatialScale hlineScale parent
  intro point hpoint
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
  have hlabel := hlift.1.2
  change Int.floor
      (inner ℝ (point3 (point 0) (point 1) lineHeight)
        (globalGrainDirection (slope lineHeight)) / lineScale) = bin at hlabel
  rw [Int.floor_eq_iff] at hlabel
  have hformula :
      inner ℝ (point3 (point 0) (point 1) lineHeight)
          (globalGrainDirection (slope lineHeight)) =
        point 0 + slope lineHeight * point 1 := by
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ, point3]
  rw [hformula] at hlabel
  change |point 0 + slope lineHeight * point 1 -
    (bin : ℝ) * lineScale| ≤ lineScale
  have hlower :
      (bin : ℝ) * lineScale ≤
        point 0 + slope lineHeight * point 1 :=
    (le_div_iff₀ hlineScale).mp (by simpa [mul_comm] using hlabel.1)
  have hupper :
      point 0 + slope lineHeight * point 1 <
        ((bin : ℝ) + 1) * lineScale :=
    (div_lt_iff₀ hlineScale).mp (by simpa using hlabel.2)
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- The actual side-`sqrt rho` spatial cubes carrying positive slice mass in
one side-`delta` global-grain bin. -/
def pureWZ2PreCommonBinGlobalLineSpatialCells
    (E : Set Point3) (slope : ℝ → ℝ)
    (lineHeight lineScale spatialScale : ℝ)
    (hspatialScale : 0 < spatialScale) (bin : ℤ) :
    Finset (ℤ × ℤ × ℤ) :=
  (pureWZ2BoundedPaperGridCells spatialScale hspatialScale).filter
    fun parent =>
      (wz1Lemma23PlanarSlice
        (pureWZ2FixedCommonBinRegion
            E slope lineHeight lineScale bin ∩
          wz1PaperGridCube spatialScale parent)
        lineHeight).Nonempty

private theorem preCommonBin_paperGridIndex_mem_bounded
    {spatialScale : ℝ} (hspatialScale : 0 < spatialScale)
    {point : Point3} (hpoint : ‖point‖ ≤ 2) :
    wz1PaperGridIndex spatialScale point ∈
      pureWZ2BoundedPaperGridCells spatialScale hspatialScale := by
  have hsqrt : Real.sqrt 3 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hparameter :
      0 < spatialScale * Real.sqrt 3 / 2 := by positivity
  have hscale :
      gridSide (spatialScale * Real.sqrt 3 / 2) = spatialScale := by
    rw [gridSide]
    field_simp
  have hindex :
      rhoGridIndex (spatialScale * Real.sqrt 3 / 2) point =
        wz1PaperGridIndex spatialScale point := by
    simp only [rhoGridIndex, wz1PaperGridIndex, hscale]
  change
    wz1PaperGridIndex spatialScale point ∈
      gridIndicesInRadius 2 (spatialScale * Real.sqrt 3 / 2) _
  rw [← hindex]
  exact gridIndex_inRadius (by norm_num) hparameter hpoint

/-- A spatial-cell contribution when the fixed-bin direction is anchored at
`referenceHeight` but the genuine source slice is taken at `sliceHeight`. -/
def pureWZ2PreCommonBinSpatialCellSliceMassAtHeight
    (E : Set Point3) (slope : ℝ → ℝ)
    (referenceHeight sliceHeight lineScale spatialScale : ℝ) (bin : ℤ)
    (parent : WZ2PaperCellIndex) : ENNReal :=
  volume
    (wz1Lemma23PlanarSlice
      (pureWZ2FixedCommonBinRegion
          E slope referenceHeight lineScale bin ∩
        wz1PaperGridCube spatialScale parent)
      sliceHeight)

/-- Side-`spatialScale` cells meeting one fixed bin at a separately supplied
source height. -/
def pureWZ2PreCommonBinSpatialCellsAtHeight
    (E : Set Point3) (slope : ℝ → ℝ)
    (referenceHeight sliceHeight lineScale spatialScale : ℝ)
    (hspatialScale : 0 < spatialScale) (bin : ℤ) :
    Finset WZ2PaperCellIndex :=
  (pureWZ2BoundedPaperGridCells spatialScale hspatialScale).filter
    fun parent =>
      (wz1Lemma23PlanarSlice
        (pureWZ2FixedCommonBinRegion
            E slope referenceHeight lineScale bin ∩
          wz1PaperGridCube spatialScale parent)
        sliceHeight).Nonempty

/-- The strip cap is unchanged when the source slice height differs from the
height anchoring the fixed bin's direction. -/
theorem pureWZ2PreCommonBinSpatialCellSliceMassAtHeight_le_strip
    {E : Set Point3} (hE : MeasurableSet E)
    (slope : ℝ → ℝ) (referenceHeight sliceHeight : ℝ)
    {lineScale spatialScale : ℝ}
    (hlineScale : 0 < lineScale)
    (hspatialScale : 0 < spatialScale)
    (bin : ℤ) (parent : WZ2PaperCellIndex) :
    pureWZ2PreCommonBinSpatialCellSliceMassAtHeight
        E slope referenceHeight sliceHeight lineScale spatialScale bin parent ≤
      ENNReal.ofReal (4 * spatialScale * lineScale) := by
  apply paperGridCube_planarSlice_volume_le_of_projection_strip
    (measurableSet_pureWZ2FixedCommonBinRegion
      hE slope referenceHeight lineScale bin)
    hspatialScale hlineScale parent
  intro point hpoint
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
  have hlabel := hlift.1.2
  change Int.floor
      (inner ℝ (point3 (point 0) (point 1) sliceHeight)
        (globalGrainDirection (slope referenceHeight)) / lineScale) = bin
    at hlabel
  rw [Int.floor_eq_iff] at hlabel
  have hformula :
      inner ℝ (point3 (point 0) (point 1) sliceHeight)
          (globalGrainDirection (slope referenceHeight)) =
        point 0 + slope referenceHeight * point 1 := by
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ, point3]
  rw [hformula] at hlabel
  change |point 0 + slope referenceHeight * point 1 -
    (bin : ℝ) * lineScale| ≤ lineScale
  have hlower :
      (bin : ℝ) * lineScale ≤
        point 0 + slope referenceHeight * point 1 :=
    (le_div_iff₀ hlineScale).mp (by simpa [mul_comm] using hlabel.1)
  have hupper :
      point 0 + slope referenceHeight * point 1 <
        ((bin : ℝ) + 1) * lineScale :=
    (div_lt_iff₀ hlineScale).mp (by simpa using hlabel.2)
  rw [abs_le]
  constructor <;> linarith

/-- Exact fixed-bin slice decomposition with independent reference and source
heights. -/
theorem pureWZ2PreCommonBin_sliceMassAtHeight_eq_sum_spatialCells
    {E : Set Point3} (hE : MeasurableSet E)
    (slope : ℝ → ℝ) (referenceHeight sliceHeight : ℝ)
    {lineScale spatialScale : ℝ}
    (hspatialScale : 0 < spatialScale) (bin : ℤ)
    (hbounded : ∀ point ∈ E, ‖point‖ ≤ 2) :
    pureWZ2FixedCommonBinSliceMass
        E slope referenceHeight lineScale sliceHeight bin =
      ∑ parent ∈
          pureWZ2PreCommonBinSpatialCellsAtHeight
            E slope referenceHeight sliceHeight lineScale spatialScale
              hspatialScale bin,
        pureWZ2PreCommonBinSpatialCellSliceMassAtHeight
          E slope referenceHeight sliceHeight lineScale spatialScale
            bin parent := by
  let parents :=
    pureWZ2PreCommonBinSpatialCellsAtHeight
      E slope referenceHeight sliceHeight lineScale spatialScale
        hspatialScale bin
  let piece : WZ2PaperCellIndex → Set Point2 := fun parent =>
    wz1Lemma23PlanarSlice
      (pureWZ2FixedCommonBinRegion
          E slope referenceHeight lineScale bin ∩
        wz1PaperGridCube spatialScale parent)
      sliceHeight
  have hpartition :
      wz1Lemma23PlanarSlice
          (pureWZ2FixedCommonBinRegion
            E slope referenceHeight lineScale bin)
          sliceHeight =
        ⋃ parent ∈ parents, piece parent := by
    ext point
    constructor
    · intro hpoint
      have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
      let lifted := point3 (point 0) (point 1) sliceHeight
      let parent := wz1PaperGridIndex spatialScale lifted
      have hparentBounded :
          parent ∈
            pureWZ2BoundedPaperGridCells spatialScale hspatialScale := by
        apply preCommonBin_paperGridIndex_mem_bounded hspatialScale
        exact hbounded lifted hlift.1
      have hparentCube :
          lifted ∈ wz1PaperGridCube spatialScale parent :=
        (mem_wz1PaperGridCube spatialScale parent lifted).mpr rfl
      have hlocal : point ∈ piece parent := by
        apply wz1Lemma23_mem_planarSlice_iff.mpr
        exact ⟨hlift, hparentCube⟩
      have hparentActive : parent ∈ parents := by
        change parent ∈
          pureWZ2PreCommonBinSpatialCellsAtHeight
            E slope referenceHeight sliceHeight lineScale spatialScale
              hspatialScale bin
        rw [pureWZ2PreCommonBinSpatialCellsAtHeight, Finset.mem_filter]
        exact ⟨hparentBounded, ⟨point, hlocal⟩⟩
      exact Set.mem_iUnion₂.mpr ⟨parent, hparentActive, hlocal⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨parent, _hparent, hlocal⟩
      exact wz1Lemma23_mem_planarSlice_iff.mpr
        (wz1Lemma23_mem_planarSlice_iff.mp hlocal).1
  have hdisjoint :
      (parents : Set WZ2PaperCellIndex).PairwiseDisjoint piece := by
    intro first _hfirst second _hsecond hne
    change Disjoint (piece first) (piece second)
    rw [Set.disjoint_left]
    intro point hfirst hsecond
    have hfirstLift := wz1Lemma23_mem_planarSlice_iff.mp hfirst
    have hsecondLift := wz1Lemma23_mem_planarSlice_iff.mp hsecond
    exact Set.disjoint_left.mp
      (wz1PaperGridCube_disjoint hne)
      hfirstLift.2 hsecondLift.2
  have hregionMeasurable :
      MeasurableSet
        (pureWZ2FixedCommonBinRegion
          E slope referenceHeight lineScale bin) :=
    measurableSet_pureWZ2FixedCommonBinRegion
      hE slope referenceHeight lineScale bin
  have hmeasurable :
      ∀ parent ∈ parents, MeasurableSet (piece parent) := by
    intro parent _hparent
    have hlift :
        Continuous (fun point : Point2 =>
          point3 (point 0) (point 1) sliceHeight) := by
      unfold point3
      fun_prop
    have heq :
        piece parent =
          (fun point : Point2 =>
            point3 (point 0) (point 1) sliceHeight) ⁻¹'
              (pureWZ2FixedCommonBinRegion
                  E slope referenceHeight lineScale bin ∩
                wz1PaperGridCube spatialScale parent) := by
      ext point
      exact wz1Lemma23_mem_planarSlice_iff
    rw [heq]
    exact
      (hregionMeasurable.inter
        (wz1PaperGridCube_measurable parent)).preimage hlift.measurable
  rw [pureWZ2FixedCommonBinSliceMass, hpartition,
    MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable]
  rfl

/-- Exact decomposition of one `delta` global-grain bin over the distinct
side-`sqrt rho` spatial cubes that it meets. -/
theorem pureWZ2PreCommonBinGlobalLine_sliceMass_eq_sum_spatialCells
    {E : Set Point3} (hE : MeasurableSet E)
    (slope : ℝ → ℝ) (lineHeight : ℝ)
    {lineScale spatialScale : ℝ}
    (hspatialScale : 0 < spatialScale) (bin : ℤ)
    (hbounded : ∀ point ∈ E, ‖point‖ ≤ 2) :
    pureWZ2FixedCommonBinSliceMass
        E slope lineHeight lineScale lineHeight bin =
      ∑ parent ∈
          pureWZ2PreCommonBinGlobalLineSpatialCells
            E slope lineHeight lineScale spatialScale hspatialScale bin,
        pureWZ2PreCommonBinGlobalLineSpatialCellSliceMass
          E slope lineHeight lineScale spatialScale bin parent := by
  let parents :=
    pureWZ2PreCommonBinGlobalLineSpatialCells
      E slope lineHeight lineScale spatialScale hspatialScale bin
  let piece : (ℤ × ℤ × ℤ) → Set Point2 := fun parent =>
    wz1Lemma23PlanarSlice
      (pureWZ2FixedCommonBinRegion
          E slope lineHeight lineScale bin ∩
        wz1PaperGridCube spatialScale parent)
      lineHeight
  have hpartition :
      wz1Lemma23PlanarSlice
          (pureWZ2FixedCommonBinRegion
            E slope lineHeight lineScale bin)
          lineHeight =
        ⋃ parent ∈ parents, piece parent := by
    ext point
    constructor
    · intro hpoint
      have hlift :=
        wz1Lemma23_mem_planarSlice_iff.mp hpoint
      let lifted := point3 (point 0) (point 1) lineHeight
      let parent := wz1PaperGridIndex spatialScale lifted
      have hparentBounded :
          parent ∈
            pureWZ2BoundedPaperGridCells spatialScale hspatialScale := by
        apply preCommonBin_paperGridIndex_mem_bounded hspatialScale
        exact hbounded lifted hlift.1
      have hparentCube :
          lifted ∈ wz1PaperGridCube spatialScale parent :=
        (mem_wz1PaperGridCube spatialScale parent lifted).mpr rfl
      have hlocal : point ∈ piece parent := by
        apply wz1Lemma23_mem_planarSlice_iff.mpr
        exact ⟨hlift, hparentCube⟩
      have hparentActive : parent ∈ parents := by
        change parent ∈
          pureWZ2PreCommonBinGlobalLineSpatialCells
            E slope lineHeight lineScale spatialScale hspatialScale bin
        rw [pureWZ2PreCommonBinGlobalLineSpatialCells, Finset.mem_filter]
        exact ⟨hparentBounded, ⟨point, hlocal⟩⟩
      exact Set.mem_iUnion₂.mpr ⟨parent, hparentActive, hlocal⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨parent, _hparent, hlocal⟩
      exact wz1Lemma23_mem_planarSlice_iff.mpr
        (wz1Lemma23_mem_planarSlice_iff.mp hlocal).1
  have hdisjoint :
      (parents : Set (ℤ × ℤ × ℤ)).PairwiseDisjoint piece := by
    intro first _hfirst second _hsecond hne
    change Disjoint (piece first) (piece second)
    rw [Set.disjoint_left]
    intro point hfirst hsecond
    have hfirstLift := wz1Lemma23_mem_planarSlice_iff.mp hfirst
    have hsecondLift := wz1Lemma23_mem_planarSlice_iff.mp hsecond
    exact Set.disjoint_left.mp
      (wz1PaperGridCube_disjoint hne)
      hfirstLift.2 hsecondLift.2
  have hregionMeasurable :
      MeasurableSet
        (pureWZ2FixedCommonBinRegion
          E slope lineHeight lineScale bin) :=
    measurableSet_pureWZ2FixedCommonBinRegion
      hE slope lineHeight lineScale bin
  have hmeasurable :
      ∀ parent ∈ parents, MeasurableSet (piece parent) := by
    intro parent _hparent
    have hlift :
        Continuous (fun point : Point2 =>
          point3 (point 0) (point 1) lineHeight) := by
      unfold point3
      fun_prop
    have heq :
        piece parent =
          (fun point : Point2 =>
            point3 (point 0) (point 1) lineHeight) ⁻¹'
              (pureWZ2FixedCommonBinRegion
                  E slope lineHeight lineScale bin ∩
                wz1PaperGridCube spatialScale parent) := by
      ext point
      exact wz1Lemma23_mem_planarSlice_iff
    rw [heq]
    exact
      (hregionMeasurable.inter
        (wz1PaperGridCube_measurable parent)).preimage hlift.measurable
  rw [pureWZ2FixedCommonBinSliceMass, hpartition,
    MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable]
  rfl

/-- At a fixed global line and fixed standard height slab, at most thirteen
side-`sqrt rho` cubes can occur over one coarse `y` index. -/
def pureWZ2PreCommonBinGlobalLineYFiberBound : ℕ := 13

/-- The requested number of selected side-`sqrt rho` cubes.  The second term
is the runtime ratio certified by the balanced cell masses and the terminal
multiplicity floor.  It is not a `P0` cutoff; it is discharged later from
the same rich-call receipts. -/
def pureWZ2PreCommonBinRequiredCubeCount
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (neighborhoodLoss : ℝ) : ENNReal :=
  max
    (Kakeya.realRpowENN rho
      (-1 / 2 + neighborhoodLoss))
    ((Kakeya.realRpowENN rho
        (1 + sigma / 2 + neighborhoodLoss) *
          volume (wz1PaperGridCube rho (0, 0, 0))) /
      ((((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
            twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
          twoScale.second.terminal.balanced.cellMass) *
        pullback.firstPostBalanced.cellMass))

/-- The finite geometric cost before the final cube count with an explicit
outer slab-to-slice factor.  The leading `2` is exactly the half-average
threshold used to define the source-popular set `Z_S`. -/
def pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
    (slabFactor : ENNReal) (sigma inputLoss delta rho : ℝ) : ENNReal :=
  2 * slabFactor *
    (132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
      Kakeya.realRpowENN (1 / delta) (1 - sigma)) *
    ENNReal.ofReal (4 * Real.sqrt rho * delta) *
    13 *
    512 *
    Prop62PaperAudit.V4.logarithmicLoss delta ^ 10

/-- Maximal-slab specialization retained for compatibility. -/
def pureWZ2PreCommonBinGlobalNeighborhoodCost
    (sigma inputLoss delta rho : ℝ) : ENNReal :=
  pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
    5 sigma inputLoss delta rho

/-- Source-heavy-slab specialization used by the all-slab Lemma-5.4 route. -/
def pureWZ2PreCommonBinHeavySlabNeighborhoodCost
    (sigma inputLoss delta rho : ℝ) : ENNReal :=
  pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
    10 sigma inputLoss delta rho

/-- A global-grain neighborhood indexed by the exact standard slab supplied
to its producer. -/
structure PureWZ2PreCommonBinGlobalGrainNeighborhoodAtData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (heightIndex : {heightIndex //
      heightIndex ∈ pullback.standardSqrtSlabIndices})
    (neighborhoodLoss : ℝ) where
  neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback
  heightIndex_eq : neighborhood.heightIndex = heightIndex
  neighborhoodLoss_eq : neighborhood.neighborhoodLoss = neighborhoodLoss
  source_slab_volume_upper :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) ≤
      ENNReal.ofReal (Real.sqrt rho) *
        pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
          1 sigma inputLoss delta rho *
        (neighborhood.K : ENNReal)

/-- Pure geometry behind the one-per-`y` selection.  All cubes lie in one
standard height slab and carry a point in one `delta`-neighborhood of the
same global line. -/
theorem pureWZ2PreCommonBinGlobalLine_yFiber_card
    {delta root lineLevel slopeValue : ℝ}
    (hroot : 0 < root)
    (hdeltaRoot : delta ≤ root)
    (hslope : |slopeValue| ≤ 3)
    (parents : Finset (ℤ × ℤ × ℤ))
    (heightIndex : ℤ)
    (hheight :
      ∀ parent ∈ parents, parent.2.2 = heightIndex)
    (witness : (ℤ × ℤ × ℤ) → Point3)
    (hwitnessCube :
      ∀ parent ∈ parents,
        witness parent ∈ wz1PaperGridCube root parent)
    (hwitnessLine :
      ∀ parent ∈ parents,
        |inner ℝ (witness parent)
            (globalGrainDirection slopeValue) - lineLevel| ≤ delta)
    (y : ℤ) :
    (parents.filter fun parent =>
      commonBinStandardParentY parent = y).card ≤
        pureWZ2PreCommonBinGlobalLineYFiberBound := by
  let fiber := parents.filter fun parent =>
    commonBinStandardParentY parent = y
  change fiber.card ≤ pureWZ2PreCommonBinGlobalLineYFiberBound
  by_cases hfiber : fiber = ∅
  · simp [hfiber]
  have hfiberNonempty : fiber.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hfiber
  let first := Classical.choose hfiberNonempty
  have hfirstFiber : first ∈ fiber :=
    Classical.choose_spec hfiberNonempty
  have hfirstParent : first ∈ parents :=
    (Finset.mem_filter.mp hfirstFiber).1
  have hfirstY : first.2.1 = y :=
    (Finset.mem_filter.mp hfirstFiber).2
  have hindexRange :
      ∀ parent ∈ fiber,
        first.1 - 6 ≤ parent.1 ∧ parent.1 ≤ first.1 + 6 := by
    intro parent hparentFiber
    have hparent : parent ∈ parents :=
      (Finset.mem_filter.mp hparentFiber).1
    have hparentY : parent.2.1 = y :=
      (Finset.mem_filter.mp hparentFiber).2
    have hparentCube := hwitnessCube parent hparent
    have hfirstCube := hwitnessCube first hfirstParent
    rw [wz1PaperGridCube_eq_Ico hroot parent] at hparentCube
    rw [wz1PaperGridCube_eq_Ico hroot first] at hfirstCube
    have hyClose :
        |witness parent 1 - witness first 1| ≤ root := by
      rw [hparentY] at hparentCube
      rw [hfirstY] at hfirstCube
      rw [abs_le]
      constructor <;>
        linarith [hparentCube.2.2.1, hparentCube.2.2.2.1,
          hfirstCube.2.2.1, hfirstCube.2.2.2.1]
    have hprojectionClose :
        |inner ℝ (witness parent)
              (globalGrainDirection slopeValue) -
            inner ℝ (witness first)
              (globalGrainDirection slopeValue)| ≤
          2 * delta := by
      have htriangle :=
        abs_sub
          (inner ℝ (witness parent)
              (globalGrainDirection slopeValue) - lineLevel)
          (inner ℝ (witness first)
              (globalGrainDirection slopeValue) - lineLevel)
      have hrearrange :
          (inner ℝ (witness parent)
                (globalGrainDirection slopeValue) - lineLevel) -
              (inner ℝ (witness first)
                (globalGrainDirection slopeValue) - lineLevel) =
            inner ℝ (witness parent)
                (globalGrainDirection slopeValue) -
              inner ℝ (witness first)
                (globalGrainDirection slopeValue) := by
        ring
      rw [hrearrange] at htriangle
      exact htriangle.trans (by
        linarith [hwitnessLine parent hparent,
          hwitnessLine first hfirstParent])
    have hxClose :
        |witness parent 0 - witness first 0| ≤ 5 * root := by
      have hformula :
          inner ℝ (witness parent)
                (globalGrainDirection slopeValue) -
              inner ℝ (witness first)
                (globalGrainDirection slopeValue) =
            (witness parent 0 - witness first 0) +
              slopeValue * (witness parent 1 - witness first 1) := by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
        ring
      rw [hformula] at hprojectionClose
      have hsolve :
          |witness parent 0 - witness first 0| ≤
            |(witness parent 0 - witness first 0) +
                slopeValue * (witness parent 1 - witness first 1)| +
              |slopeValue| *
                |witness parent 1 - witness first 1| := by
        have h := abs_sub
          ((witness parent 0 - witness first 0) +
            slopeValue * (witness parent 1 - witness first 1))
          (slopeValue * (witness parent 1 - witness first 1))
        simpa [abs_mul] using h
      calc
        |witness parent 0 - witness first 0| ≤ _ := hsolve
        _ ≤ 2 * delta + 3 * root := by gcongr
        _ ≤ 5 * root := by linarith
    have hlowerReal :
        ((first.1 - 6 : ℤ) : ℝ) ≤ (parent.1 : ℝ) := by
      have hmul :
          ((first.1 : ℝ) - 5) * root <
            ((parent.1 : ℝ) + 1) * root := by
        calc
          ((first.1 : ℝ) - 5) * root =
              (first.1 : ℝ) * root - 5 * root := by ring
          _ ≤ witness first 0 - 5 * root := by
            linarith [hfirstCube.1]
          _ ≤ witness parent 0 := by
            linarith [abs_le.mp hxClose]
          _ < ((parent.1 : ℝ) + 1) * root :=
            hparentCube.2.1
      have hindices :
          (first.1 : ℝ) - 5 < (parent.1 : ℝ) + 1 :=
        lt_of_mul_lt_mul_right hmul hroot.le
      norm_num
      linarith
    have hupperReal :
        (parent.1 : ℝ) ≤ ((first.1 + 6 : ℤ) : ℝ) := by
      have hmul :
          (parent.1 : ℝ) * root <
            ((first.1 : ℝ) + 6) * root := by
        calc
          (parent.1 : ℝ) * root ≤ witness parent 0 :=
            hparentCube.1
          _ ≤ witness first 0 + 5 * root := by
            linarith [abs_le.mp hxClose]
          _ < ((first.1 : ℝ) + 1) * root + 5 * root := by
            linarith [hfirstCube.2.1]
          _ = ((first.1 : ℝ) + 6) * root := by ring
      have hindices :
          (parent.1 : ℝ) < (first.1 : ℝ) + 6 :=
        lt_of_mul_lt_mul_right hmul hroot.le
      push_cast
      linarith
    exact
      ⟨by exact_mod_cast hlowerReal, by exact_mod_cast hupperReal⟩
  have himageSubset :
      fiber.image (fun parent => parent.1) ⊆
        Finset.Icc (first.1 - 6) (first.1 + 6) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨parent, hparent, rfl⟩
    exact Finset.mem_Icc.mpr (hindexRange parent hparent)
  have hinjective :
      Set.InjOn (fun parent : ℤ × ℤ × ℤ => parent.1) fiber := by
    intro firstParent hfirst secondParent hsecond hx
    have hfirstY' := (Finset.mem_filter.mp hfirst).2
    have hsecondY' := (Finset.mem_filter.mp hsecond).2
    have hfirstParent' := (Finset.mem_filter.mp hfirst).1
    have hsecondParent' := (Finset.mem_filter.mp hsecond).1
    apply Prod.ext
    · exact hx
    · apply Prod.ext
      · exact hfirstY'.trans hsecondY'.symm
      · exact
          (hheight firstParent hfirstParent').trans
            (hheight secondParent hsecondParent').symm
  rw [← Finset.card_image_of_injOn hinjective]
  calc
    (fiber.image fun parent => parent.1).card ≤
        (Finset.Icc (first.1 - 6) (first.1 + 6)).card :=
      Finset.card_le_card himageSubset
    _ = pureWZ2PreCommonBinGlobalLineYFiberBound := by
      simp [pureWZ2PreCommonBinGlobalLineYFiberBound]
      omega

/-- Construct the finite global-grain neighborhood at one fixed occupied
standard slab, used before local grains and before every later
common-bin/four-cycle selection.

The source-to-slab hypothesis is division-free: after the Fubini slice is
selected it yields `sourceVolume ≤ outerSlabFactor * sliceArea`. -/
theorem PureWZ2Node05V4RichTwoScaleCellPullbackData.producePreCommonBinGlobalGrainNeighborhoodAt
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (heightIndex : {heightIndex //
      heightIndex ∈ pullback.standardSqrtSlabIndices})
    (outerSlabFactor : ENNReal)
    (houterSlabFactorPos : 0 < outerSlabFactor)
    (houterSlabFactorTop : outerSlabFactor ≠ ⊤)
    (hsourceSlab :
      volume pullback.shading.union * ENNReal.ofReal (Real.sqrt rho) ≤
        outerSlabFactor *
          volume (pullback.standardSqrtSlabSourceRegion heightIndex.1))
    (hbridge : PureWZ2PaperADBridgeStatement)
    (neighborhoodLoss : ℝ)
    (hbudget :
      pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
          outerSlabFactor sigma inputLoss delta rho *
        pureWZ2PreCommonBinRequiredCubeCount
          pullback neighborhoodLoss ≤
        volume pullback.shading.union) :
    Nonempty
      (PureWZ2PreCommonBinGlobalGrainNeighborhoodAtData
        pullback heightIndex neighborhoodLoss) := by
  let source := current.grain
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hheightIndex :
      heightIndex.1 ∈ pullback.standardSqrtSlabIndices :=
    heightIndex.property
  let root := Real.sqrt rho
  let rootENN := ENNReal.ofReal root
  let sourceVolume := volume pullback.shading.union
  let E :=
    pullback.standardSqrtSlabSourceRegion heightIndex.1
  have hrhoOne : rho ≤ 1 := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.2
  have hdeltaRho : delta ≤ rho := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.1
  have hroot : 0 < root := Real.sqrt_pos.mpr hrho
  have hrootOne : root ≤ 1 := by
    simpa [root] using Real.sqrt_le_one.mpr hrhoOne
  have hrhoRoot : rho ≤ root := by
    dsimp only [root]
    nlinarith [Real.sq_sqrt hrho.le, Real.sqrt_nonneg rho]
  have hdeltaRoot : delta ≤ root := hdeltaRho.trans hrhoRoot
  have hrootENN : 0 < rootENN :=
    ENNReal.ofReal_pos.mpr hroot
  have hrootENNTop : rootENN ≠ ⊤ := ENNReal.ofReal_ne_top
  have hEMeasurable : MeasurableSet E := by
    simpa [E] using
      pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex.1
  have hETop : volume E ≠ ⊤ := by
    simpa [E] using
      pullback.standardSqrtSlabSourceRegion_volume_ne_top heightIndex.1
  have hEPos : 0 < volume E := by
    simpa [E] using
      pullback.standardSqrtSlabSourceRegion_volume_pos hheightIndex
  let slabLeft := (heightIndex.1 : ℝ) * root
  let slabRight := slabLeft + root
  rcases pullback.sourcePopularHeightData heightIndex with
    ⟨popularData⟩
  let lineHeight := popularData.referenceHeight
  have hlineHeightPopular :
      lineHeight ∈ pullback.sourcePopularHeights heightIndex.1 := by
    simpa [lineHeight, popularData.popularHeights_eq] using
      popularData.referenceHeight_mem
  have hlineHeightSlab : lineHeight ∈ Set.Ico slabLeft slabRight := by
    simpa [slabLeft, slabRight, root, sourcePopularHeights,
      sourcePopularSlabLeft] using hlineHeightPopular.1
  let sliceArea :=
    volume (wz1Lemma23PlanarSlice E lineHeight)
  have hsliceLower :
      volume E / (2 * rootENN) ≤ sliceArea := by
    have hthreshold := hlineHeightPopular.2
    rw [pureWZ2SourceCommonBinPopularThreshold_eq] at hthreshold
    simpa [E, rootENN, root, sliceArea,
      pureWZ2SourceCommonBinSliceMass] using hthreshold
  have hELeSlice :
      volume E ≤ sliceArea * (2 * rootENN) := by
    exact
      (ENNReal.div_le_iff_le_mul
        (Or.inl (ENNReal.mul_pos (by norm_num) hrootENN.ne').ne')
        (Or.inl (ENNReal.mul_ne_top (by norm_num) hrootENNTop))).mp
        hsliceLower
  have hsourceSlice :
      sourceVolume ≤ 2 * outerSlabFactor * sliceArea := by
    apply (ENNReal.mul_le_mul_iff_right hrootENN.ne' hrootENNTop).mp
    calc
      rootENN * sourceVolume ≤ outerSlabFactor * volume E := by
        simpa only [sourceVolume, rootENN, E, mul_comm] using hsourceSlab
      _ ≤ outerSlabFactor * (sliceArea * (2 * rootENN)) := by gcongr
      _ = rootENN * (2 * outerSlabFactor * sliceArea) := by ring
  have hslicePos : 0 < sliceArea := by
    have hquotientPos : 0 < volume E / (2 * rootENN) :=
      ENNReal.div_pos hEPos.ne'
        (ENNReal.mul_ne_top (by norm_num) hrootENNTop)
    exact hquotientPos.trans_le hsliceLower
  have hsliceNonempty :
      (wz1Lemma23PlanarSlice E lineHeight).Nonempty := by
    by_contra hempty
    have hempty' :
        wz1Lemma23PlanarSlice E lineHeight = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hempty
    change 0 < volume (wz1Lemma23PlanarSlice E lineHeight) at hslicePos
    rw [hempty'] at hslicePos
    have hnot : ¬ (0 < volume (∅ : Set Point2)) := by simp
    exact hnot hslicePos
  have hlineHeightRange :
      lineHeight ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa [lineHeight] using popularData.referenceHeight_mem_paperRange
  have hlineHeightContract :
      lineHeight ∈
        Set.Ico
          ((heightIndex.1 : ℝ) * Real.sqrt rho)
          ((heightIndex.1 : ℝ) * Real.sqrt rho +
            Real.sqrt rho) := by
    simpa [slabLeft, slabRight, root] using hlineHeightSlab
  let slice : Set Point3 := horizontalSlice E lineHeight
  have hsliceY :
      ∀ point ∈ slice, |point (1 : Fin 3)| ≤ 1 := by
    intro point hpoint
    change point ∈ horizontalSlice E lineHeight at hpoint
    have hsource :
        point ∈ source.shading.union :=
      pullback.subshading.union_subset
        (pullback.standardSqrtSlabSourceRegion_subset_source
          heightIndex.1 (by
            simpa [E] using hpoint.1))
    have hbox := shading_union_subset_axisBox hsource
    simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
  have hsliceAD :
      IsADSet1
        (scalarProjection
          (globalGrainDirection
            (source.globalGrains.slope lineHeight))
          slice)
        delta (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss)) := by
    let restrictedGlobal :=
      source.globalGrains.toPureWZ2LipschitzGlobalGrainData.restrict
        pullback.subshading le_rfl
        (by simp [Kakeya.realRpowENN] :
          Kakeya.realRpowENN delta (-inputLoss) ≠ ⊤)
    let globalPaper :=
      PureWZ2BoundedLipschitzGlobalGrainData.ofSlopeBound
        restrictedGlobal (by
          intro z hz
          exact source.globalGrains.slope_bound z hz)
    let shadow :=
      pureWZ2ActiveCellShading pullback.shading
        source.extremal.delta_pos
    have hfullAD :=
      globalPaper.activeCellShadow_exactAD
        source.extremal.delta_pos pullback.whole_cells hbridge
        globalPaper.slope_bound lineHeight hlineHeightRange
    have hslope :
        globalPaper.slope = source.globalGrains.slope := rfl
    rw [hslope] at hfullAD
    have hshadowUnion :
        shadow.union = pullback.shading.union :=
      pureWZ2ActiveCellShading_union pullback.shading
        source.extremal.delta_pos pullback.whole_cells
    rw [show
      horizontalSlice shadow.union lineHeight =
        horizontalSlice pullback.shading.union lineHeight by
          rw [hshadowUnion]] at hfullAD
    apply hfullAD.mono
    rintro value ⟨point, hpoint, rfl⟩
    refine ⟨point, ⟨?_, hpoint.2⟩, rfl⟩
    exact hpoint.1.1
  let bins :=
    pureWZ2OccupiedCommonBins slice source.globalGrains.slope
      lineHeight delta
  have hlabelMem :
      ∀ point ∈ slice,
        pureWZ2FixedCommonBinLabel source.globalGrains.slope
            lineHeight delta point ∈ bins := by
    intro point hpoint
    simpa [bins] using
      pureWZ2_fixed_common_bin_mem
        slice source.globalGrains.slope
        source.globalGrains.slope_lipschitz
        lineHeight lineHeight hlineHeightRange hlineHeightRange
        (by simpa using source.extremal.delta_pos.le)
        hsliceY hsliceAD source.extremal.delta_le_one hpoint
  have hbinsNonempty : bins.Nonempty := by
    rcases hsliceNonempty with ⟨point, hpoint⟩
    let lifted := point3 (point 0) (point 1) lineHeight
    have hlift : lifted ∈ slice := by
      exact ⟨wz1Lemma23_mem_planarSlice_iff.mp hpoint, by
        simp [lifted, point3]⟩
    exact ⟨_, hlabelMem lifted hlift⟩
  have hbinsBound :
      (bins.card : ENNReal) ≤
        132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
          Kakeya.realRpowENN (1 / delta) (1 - sigma) := by
    simpa [bins] using
      pureWZ2_fixed_common_bin_occupied_bound
        slice source.globalGrains.slope
        source.globalGrains.slope_lipschitz
        lineHeight lineHeight hlineHeightRange hlineHeightRange
        (by simpa using source.extremal.delta_pos.le)
        hsliceY hsliceAD source.extremal.delta_le_one
  let binMass : ℤ → ENNReal := fun bin =>
    pureWZ2FixedCommonBinSliceMass E source.globalGrains.slope
      lineHeight delta lineHeight bin
  have hsliceMassSum :
      sliceArea = ∑ bin ∈ bins, binMass bin := by
    simpa [sliceArea, slice, binMass] using
      pureWZ2_fixed_common_bin_sliceMass_sum
        hEMeasurable source.globalGrains.slope
        lineHeight delta lineHeight bins hlabelMem
  rcases Finset.exists_max_image bins binMass hbinsNonempty with
    ⟨lineBin, hlineBin, hlineBinMax⟩
  have hsliceBin :
      sliceArea ≤ (bins.card : ENNReal) * binMass lineBin := by
    rw [hsliceMassSum]
    calc
      (∑ bin ∈ bins, binMass bin) ≤
          ∑ _bin ∈ bins, binMass lineBin :=
        Finset.sum_le_sum fun bin hbin => hlineBinMax bin hbin
      _ = (bins.card : ENNReal) * binMass lineBin := by
        simp [Finset.sum_const]
  let parents :=
    pureWZ2PreCommonBinGlobalLineSpatialCells
      E source.globalGrains.slope lineHeight delta root hroot lineBin
  have hENorm :
      ∀ point ∈ E, ‖point‖ ≤ 2 := by
    intro point hpoint
    exact norm_le_two_of_mem_paperShading
      (pullback.subshading.union_subset
        (pullback.standardSqrtSlabSourceRegion_subset_source
          heightIndex.1 (by simpa [E] using hpoint)))
  have hbinMassDecomposition :
      binMass lineBin =
        ∑ parent ∈ parents,
          pureWZ2PreCommonBinGlobalLineSpatialCellSliceMass
            E source.globalGrains.slope lineHeight delta root
            lineBin parent := by
    simpa [binMass, parents] using
      pureWZ2PreCommonBinGlobalLine_sliceMass_eq_sum_spatialCells
        hEMeasurable source.globalGrains.slope lineHeight hroot lineBin hENorm
  let cellCap := ENNReal.ofReal (4 * root * delta)
  have hcellUpper :
      ∀ parent ∈ parents,
        pureWZ2PreCommonBinGlobalLineSpatialCellSliceMass
            E source.globalGrains.slope lineHeight delta root
            lineBin parent ≤ cellCap := by
    intro parent _hparent
    simpa [cellCap, root] using
      pureWZ2PreCommonBinGlobalLineSpatialCellSliceMass_le_strip
        hEMeasurable source.globalGrains.slope lineHeight
        source.extremal.delta_pos hroot lineBin parent
  have hbinParents :
      binMass lineBin ≤ (parents.card : ENNReal) * cellCap := by
    rw [hbinMassDecomposition]
    calc
      (∑ parent ∈ parents,
          pureWZ2PreCommonBinGlobalLineSpatialCellSliceMass
            E source.globalGrains.slope lineHeight delta root
            lineBin parent) ≤
          ∑ _parent ∈ parents, cellCap :=
        Finset.sum_le_sum fun parent hparent => hcellUpper parent hparent
      _ = (parents.card : ENNReal) * cellCap := by
        simp [Finset.sum_const]
  have hparentsNonempty : parents.Nonempty := by
    have hlineBinData := hlineBin
    change lineBin ∈
      pureWZ2OccupiedCommonBins slice source.globalGrains.slope
        lineHeight delta at hlineBinData
    rw [pureWZ2OccupiedCommonBins, Finset.mem_filter] at hlineBinData
    rcases hlineBinData.2 with ⟨point, hpointSlice, hpointLabel⟩
    change point ∈ horizontalSlice E lineHeight at hpointSlice
    let parent := wz1PaperGridIndex root point
    have hparentBounded :
        parent ∈ pureWZ2BoundedPaperGridCells root hroot := by
      apply preCommonBin_paperGridIndex_mem_bounded
      exact hENorm point hpointSlice.1
    have hpointCube :
        point ∈ wz1PaperGridCube root parent :=
      (mem_wz1PaperGridCube root parent point).mpr rfl
    have hpointPlanar :
        WithLp.toLp 2 ![point 0, point 1] ∈
          wz1Lemma23PlanarSlice
            (pureWZ2FixedCommonBinRegion
                E source.globalGrains.slope lineHeight delta lineBin ∩
              wz1PaperGridCube root parent)
            lineHeight := by
      apply wz1Lemma23_mem_planarSlice_iff.mpr
      have hheight : point (2 : Fin 3) = lineHeight := hpointSlice.2
      have hliftEq :
          point3
              ((WithLp.toLp 2 ![point 0, point 1] : Point2) 0)
              ((WithLp.toLp 2 ![point 0, point 1] : Point2) 1)
              lineHeight =
            point := by
        ext coordinate
        fin_cases coordinate <;> simp [point3, hheight]
      rw [hliftEq]
      exact ⟨⟨hpointSlice.1, hpointLabel⟩, hpointCube⟩
    refine ⟨parent, ?_⟩
    change parent ∈
      pureWZ2PreCommonBinGlobalLineSpatialCells
        E source.globalGrains.slope lineHeight delta root hroot lineBin
    rw [pureWZ2PreCommonBinGlobalLineSpatialCells, Finset.mem_filter]
    exact ⟨hparentBounded, ⟨_, hpointPlanar⟩⟩
  let rawWitness : (ℤ × ℤ × ℤ) → Point3 := fun parent =>
    if hparent : parent ∈ parents then
      let planar :=
        Classical.choose
          ((Finset.mem_filter.mp hparent).2)
      point3 (planar 0) (planar 1) lineHeight
    else
      0
  have hrawWitness :
      ∀ parent (hparent : parent ∈ parents),
        rawWitness parent ∈
            pureWZ2FixedCommonBinRegion
              E source.globalGrains.slope lineHeight delta lineBin ∩
              wz1PaperGridCube root parent ∧
          rawWitness parent (2 : Fin 3) = lineHeight := by
    intro parent hparent
    let planar :=
      Classical.choose ((Finset.mem_filter.mp hparent).2)
    have hplanar :
        planar ∈
          wz1Lemma23PlanarSlice
            (pureWZ2FixedCommonBinRegion
                E source.globalGrains.slope lineHeight delta lineBin ∩
              wz1PaperGridCube root parent)
            lineHeight :=
      Classical.choose_spec ((Finset.mem_filter.mp hparent).2)
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hplanar
    have hwitnessEq :
        rawWitness parent =
          point3 (planar 0) (planar 1) lineHeight := by
      dsimp only [rawWitness]
      rw [dif_pos hparent]
    rw [hwitnessEq]
    exact ⟨hlift, by simp [point3]⟩
  have hparentsSubset :
      parents ⊆
        pullback.standardSqrtSlabParents heightIndex.1 := by
    intro parent hparent
    have hw := (hrawWitness parent hparent).1
    have hregion := hw.1
    rw [pureWZ2FixedCommonBinRegion] at hregion
    have hpointE := hregion.1
    change rawWitness parent ∈ pullback.shading.union ∩
      wz2RetainedCellsUnion rho
        (pullback.standardSqrtSlabRhoCells heightIndex.1) at hpointE
    rw [wz2RetainedCellsUnion] at hpointE
    rcases Set.mem_iUnion₂.mp hpointE.2 with
      ⟨rhoCell, hrhoCell, hpointRhoCell⟩
    have hpointCanonical :
        rawWitness parent ∈
          wz1PaperGridCube sqrtRequested.1
            (pullback.standardSecondParent rhoCell) :=
      pullback.standardSqrtSlabRhoCell_subset_parent
        hrhoCell hpointRhoCell
    have hpointParent :
        rawWitness parent ∈
          wz1PaperGridCube sqrtRequested.1 parent := by
      simpa [root, pullback.sqrtRequested_eq] using hw.2
    have hparentEq :
        parent = pullback.standardSecondParent rhoCell := by
      exact
        ((mem_wz1PaperGridCube sqrtRequested.1 parent
          (rawWitness parent)).mp hpointParent).symm.trans
        ((mem_wz1PaperGridCube sqrtRequested.1
          (pullback.standardSecondParent rhoCell)
          (rawWitness parent)).mp hpointCanonical)
    rw [hparentEq]
    exact Finset.mem_image.mpr ⟨rhoCell, hrhoCell, rfl⟩
  have hparentHeight :
      ∀ parent ∈ parents, parent.2.2 = heightIndex.1 := by
    intro parent hparent
    exact pullback.standardSqrtSlabParent_height
      (hparentsSubset hparent)
  let lineLevel : ℝ := (lineBin : ℝ) * delta
  have hrawWitnessLine :
      ∀ parent ∈ parents,
        |inner ℝ (rawWitness parent)
            (globalGrainDirection
              (source.globalGrains.slope lineHeight)) -
          lineLevel| ≤ delta := by
    intro parent hparent
    have hregion := (hrawWitness parent hparent).1.1
    rw [pureWZ2FixedCommonBinRegion] at hregion
    have hlabel := hregion.2
    change
      Int.floor
          (inner ℝ (rawWitness parent)
            (globalGrainDirection
              (source.globalGrains.slope lineHeight)) / delta) =
        lineBin at hlabel
    rw [Int.floor_eq_iff] at hlabel
    have hscaledLower :
        (lineBin : ℝ) * delta ≤
          inner ℝ (rawWitness parent)
            (globalGrainDirection
              (source.globalGrains.slope lineHeight)) := by
      exact
        (le_div_iff₀ source.extremal.delta_pos).mp
          (by simpa [mul_comm] using hlabel.1)
    have hscaledUpper :
        inner ℝ (rawWitness parent)
            (globalGrainDirection
              (source.globalGrains.slope lineHeight)) ≤
          (lineBin : ℝ) * delta + delta := by
      have hlt :
          inner ℝ (rawWitness parent)
              (globalGrainDirection
                (source.globalGrains.slope lineHeight)) <
            ((lineBin : ℝ) + 1) * delta :=
        (div_lt_iff₀ source.extremal.delta_pos).mp
          (by simpa using hlabel.2)
      linarith
    rw [abs_le]
    dsimp only [lineLevel]
    constructor <;> linarith
  have hparentYFiber :
      ∀ y : ℤ,
        (parents.filter fun parent =>
          commonBinStandardParentY parent = y).card ≤
            pureWZ2PreCommonBinGlobalLineYFiberBound := by
    intro y
    exact pureWZ2PreCommonBinGlobalLine_yFiber_card
      hroot hdeltaRoot
      (source.globalGrains.slope_bound
        lineHeight hlineHeightRange)
      parents heightIndex.1 hparentHeight rawWitness
      (fun parent hparent => (hrawWitness parent hparent).1.2)
      hrawWitnessLine y
  let parentWeight : (ℤ × ℤ × ℤ) → ENNReal := fun parent =>
    (pullback.preCommonBinFinePullbackShading parent).mass
  let selection :
      CommonBinStandardParentWeightedSelectionData
        pureWZ2PreCommonBinGlobalLineYFiberBound parents parentWeight :=
    Classical.choice
      (commonBin_selectStandardParentWeighted
        pureWZ2PreCommonBinGlobalLineYFiberBound parents parentWeight
        hparentsNonempty hparentYFiber)
  let cubeVolume :=
    volume (wz1PaperGridCube rho (0, 0, 0))
  let balanceMass :=
    (((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
          twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
      twoScale.second.terminal.balanced.cellMass) *
        pullback.firstPostBalanced.cellMass
  have hcubeVolumePos : 0 < cubeVolume := by
    dsimp only [cubeVolume]
    exact wz1PaperGridCube_volume_pos hrho (0, 0, 0)
  have hcubeVolumeTop : cubeVolume ≠ ⊤ := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_ne_top
  have hbalancePosEarly : 0 < balanceMass := by
    dsimp only [balanceMass]
    have hfloorNat :
        0 < twoScale.first.fourDegreeReceipts.fineDegreeFloor *
          twoScale.first.fourDegreeReceipts.muFine :=
      Nat.mul_pos
        twoScale.first.fourDegreeReceipts.fineDegreeFloor_pos
        twoScale.first.fourDegreeReceipts.muFine_pos
    have hfloor :
        ((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
          twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) ≠ 0 := by
      exact_mod_cast hfloorNat.ne'
    exact ENNReal.mul_pos
      (ENNReal.mul_pos hfloor
        twoScale.second.terminal.balanced.cellMass_pos.ne').ne'
      pullback.firstPostBalanced.cellMass_pos.ne'
  have hbalanceTopEarly : balanceMass ≠ ⊤ := by
    dsimp only [balanceMass]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.natCast_ne_top _)
        twoScale.second.terminal.balanced.cellMass_ne_top)
      pullback.firstPostBalanced.cellMass_ne_top
  have hweightLower :
      ∀ parent ∈ parents,
        balanceMass ≤ parentWeight parent * cubeVolume := by
    intro parent hparent
    simpa [parentWeight, cubeVolume, balanceMass] using
      pullback.preCommonBinFinePullbackShading_mass_lower_cross
        (pullback.standardSqrtSlabParents_subset_active
          heightIndex.1 (hparentsSubset hparent))
  have hweightUpper :
      ∀ parent ∈ parents,
        parentWeight parent * cubeVolume ≤
          (twoScale.first.fourDegreeReceipts.regularity : ENNReal) *
            balanceMass := by
    intro parent hparent
    simpa [parentWeight, cubeVolume, balanceMass] using
      pullback.preCommonBinFinePullbackShading_mass_upper_cross
        (pullback.standardSqrtSlabParents_subset_active
          heightIndex.1 (hparentsSubset hparent))
  have hweightFamilyLower :
      ∀ (family : Finset (ℤ × ℤ × ℤ)),
        family ⊆ parents →
        (family.card : ENNReal) * balanceMass ≤
          (∑ parent ∈ family, parentWeight parent) * cubeVolume := by
    intro family hfamily
    rw [Finset.sum_mul]
    calc
      (family.card : ENNReal) * balanceMass =
          ∑ _parent ∈ family, balanceMass := by
        simp [Finset.sum_const]
      _ ≤ ∑ parent ∈ family, parentWeight parent * cubeVolume := by
        exact Finset.sum_le_sum fun parent hparent =>
          hweightLower parent (hfamily hparent)
  have hweightFamilyUpper :
      ∀ (family : Finset (ℤ × ℤ × ℤ)),
        family ⊆ parents →
        (∑ parent ∈ family, parentWeight parent) * cubeVolume ≤
          (family.card : ENNReal) *
            ((twoScale.first.fourDegreeReceipts.regularity : ENNReal) *
              balanceMass) := by
    intro family hfamily
    rw [Finset.sum_mul]
    calc
      (∑ parent ∈ family, parentWeight parent * cubeVolume) ≤
          ∑ _parent ∈ family,
            (twoScale.first.fourDegreeReceipts.regularity : ENNReal) *
              balanceMass := by
        exact Finset.sum_le_sum fun parent hparent =>
          hweightUpper parent (hfamily hparent)
      _ = (family.card : ENNReal) *
          ((twoScale.first.fourDegreeReceipts.regularity : ENNReal) *
            balanceMass) := by
        simp [Finset.sum_const]
  have hparentsCount :
      (parents.card : ENNReal) ≤
        pureWZ2PreCommonBinGlobalLineYFiberBound * 512 *
          twoScale.first.fourDegreeReceipts.regularity *
          (selection.selected.card : ENNReal) := by
    apply
      (ENNReal.mul_le_mul_iff_right
        hbalancePosEarly.ne' hbalanceTopEarly).mp
    have hweighted := selection.final_weight_le
    have hscaled :
        (∑ parent ∈ parents, parentWeight parent) * cubeVolume ≤
          (pureWZ2PreCommonBinGlobalLineYFiberBound * 512 *
            ∑ parent ∈ selection.selected, parentWeight parent) *
            cubeVolume := by
      calc
        (∑ parent ∈ parents, parentWeight parent) * cubeVolume =
            cubeVolume * ∑ parent ∈ parents, parentWeight parent := by
          rw [mul_comm]
        _ ≤ cubeVolume *
            (pureWZ2PreCommonBinGlobalLineYFiberBound * 512 *
              ∑ parent ∈ selection.selected, parentWeight parent) :=
          mul_le_mul_right hweighted cubeVolume
        _ = (pureWZ2PreCommonBinGlobalLineYFiberBound * 512 *
              ∑ parent ∈ selection.selected, parentWeight parent) *
            cubeVolume := by rw [mul_comm]
    have hcountScaled :
        (parents.card : ENNReal) * balanceMass ≤
          (pureWZ2PreCommonBinGlobalLineYFiberBound * 512 *
            twoScale.first.fourDegreeReceipts.regularity *
            (selection.selected.card : ENNReal)) * balanceMass := by
      calc
        (parents.card : ENNReal) * balanceMass ≤
            (∑ parent ∈ parents, parentWeight parent) * cubeVolume :=
          hweightFamilyLower parents (fun _ h => h)
        _ ≤
            (pureWZ2PreCommonBinGlobalLineYFiberBound * 512 *
              ∑ parent ∈ selection.selected, parentWeight parent) *
              cubeVolume :=
          hscaled
        _ ≤
            (pureWZ2PreCommonBinGlobalLineYFiberBound * 512 *
              twoScale.first.fourDegreeReceipts.regularity *
              (selection.selected.card : ENNReal)) * balanceMass := by
          calc
            (pureWZ2PreCommonBinGlobalLineYFiberBound * 512 *
                ∑ parent ∈ selection.selected, parentWeight parent) *
                cubeVolume =
              (pureWZ2PreCommonBinGlobalLineYFiberBound * 512) *
                ((∑ parent ∈ selection.selected, parentWeight parent) *
                  cubeVolume) := by ac_rfl
            _ ≤ (pureWZ2PreCommonBinGlobalLineYFiberBound * 512) *
                ((selection.selected.card : ENNReal) *
                  ((twoScale.first.fourDegreeReceipts.regularity : ENNReal) *
                    balanceMass)) := by
              exact mul_le_mul_right
                (hweightFamilyUpper selection.selected
                  selection.selected_subset)
                (pureWZ2PreCommonBinGlobalLineYFiberBound * 512)
            _ = _ := by ac_rfl
    rw [mul_comm balanceMass,
      mul_comm balanceMass
        (pureWZ2PreCommonBinGlobalLineYFiberBound * 512 *
          twoScale.first.fourDegreeReceipts.regularity *
          (selection.selected.card : ENNReal))]
    exact hcountScaled
  let binCap : ENNReal :=
    132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
      Kakeya.realRpowENN (1 / delta) (1 - sigma)
  have hregularityBound :
      (twoScale.first.fourDegreeReceipts.regularity : ENNReal) ≤
        Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 :=
    twoScale.first.rich.terminal_regularity_bound
  have hsourceUpper :
      sourceVolume ≤
        pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
            outerSlabFactor sigma inputLoss delta rho *
          (selection.selected.card : ENNReal) := by
    calc
      sourceVolume ≤ 2 * outerSlabFactor * sliceArea := hsourceSlice
      _ ≤ 2 * outerSlabFactor *
          ((bins.card : ENNReal) * binMass lineBin) := by
        gcongr
      _ ≤ 2 * outerSlabFactor * (binCap * binMass lineBin) := by
        gcongr
      _ ≤ 2 * outerSlabFactor *
          (binCap * ((parents.card : ENNReal) * cellCap)) := by
        gcongr
      _ ≤ 2 * outerSlabFactor *
          (binCap *
            ((pureWZ2PreCommonBinGlobalLineYFiberBound * 512 *
              twoScale.first.fourDegreeReceipts.regularity *
              (selection.selected.card : ENNReal)) * cellCap)) := by
        gcongr
      _ ≤ 2 * outerSlabFactor *
          (binCap *
            ((13 * 512 *
              Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 *
              (selection.selected.card : ENNReal)) * cellCap)) := by
        gcongr
        · norm_num [pureWZ2PreCommonBinGlobalLineYFiberBound]
      _ =
          pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
              outerSlabFactor sigma inputLoss delta rho *
            (selection.selected.card : ENNReal) := by
        simp only [pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor,
          binCap, cellCap]
        ring
  have hsourceSlabUpper :
      volume E ≤ rootENN *
        pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
          1 sigma inputLoss delta rho *
        (selection.selected.card : ENNReal) := by
    calc
      volume E ≤ sliceArea * (2 * rootENN) := hELeSlice
      _ ≤ ((bins.card : ENNReal) * binMass lineBin) *
          (2 * rootENN) := by
        gcongr
      _ ≤ (binCap * binMass lineBin) * (2 * rootENN) := by
        gcongr
      _ ≤ (binCap * ((parents.card : ENNReal) * cellCap)) *
          (2 * rootENN) := by
        gcongr
      _ ≤ (binCap *
          ((pureWZ2PreCommonBinGlobalLineYFiberBound * 512 *
            twoScale.first.fourDegreeReceipts.regularity *
            (selection.selected.card : ENNReal)) * cellCap)) *
          (2 * rootENN) := by
        gcongr
      _ ≤ (binCap *
          ((13 * 512 * Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 *
            (selection.selected.card : ENNReal)) * cellCap)) *
          (2 * rootENN) := by
        gcongr
        norm_num [pureWZ2PreCommonBinGlobalLineYFiberBound]
      _ = rootENN *
          pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
            1 sigma inputLoss delta rho *
          (selection.selected.card : ENNReal) := by
        simp only [pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor,
          binCap, cellCap]
        ring
  have hbinCapPos : 0 < binCap := by
    dsimp only [binCap]
    have hfirstPower :
        0 < Kakeya.realRpowENN delta (-inputLoss) :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos source.extremal.delta_pos _)
    have hinverse : 0 < 1 / delta :=
      one_div_pos.mpr source.extremal.delta_pos
    have hsecondPower :
        0 < Kakeya.realRpowENN (1 / delta) (1 - sigma) :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hinverse _)
    positivity
  have hcellCapPos : 0 < cellCap := by
    dsimp only [cellCap]
    exact ENNReal.ofReal_pos.mpr
      (mul_pos (mul_pos (by norm_num) hroot) source.extremal.delta_pos)
  have hcostPos :
      0 <
        pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
          outerSlabFactor sigma inputLoss delta rho := by
    have hregularityPos :
        (0 : ENNReal) <
          twoScale.first.fourDegreeReceipts.regularity := by
      exact_mod_cast
        twoScale.first.fourDegreeReceipts.regularity_pos
    have hlogPowerPos :
        0 < Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 :=
      hregularityPos.trans_le hregularityBound
    unfold pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
    exact ENNReal.mul_pos
      (ENNReal.mul_pos
        (ENNReal.mul_pos
          (ENNReal.mul_pos
            (ENNReal.mul_pos
              (ENNReal.mul_pos (by norm_num) houterSlabFactorPos.ne').ne'
                hbinCapPos.ne').ne'
              hcellCapPos.ne').ne'
          (by norm_num)).ne'
        (by norm_num)).ne'
      hlogPowerPos.ne'
  have hcostTop :
      pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
          outerSlabFactor sigma inputLoss delta rho ≠ ⊤ := by
    have hbinCapTop : binCap ≠ ⊤ := by
      dsimp only [binCap, Kakeya.realRpowENN]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (by norm_num)
          (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top))
        ENNReal.ofReal_ne_top
    have hcellCapTop : cellCap ≠ ⊤ := by
      dsimp only [cellCap]
      exact ENNReal.ofReal_ne_top
    unfold pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top
              (ENNReal.mul_ne_top (by norm_num) houterSlabFactorTop)
                hbinCapTop)
              hcellCapTop)
          (by norm_num))
        (by norm_num))
      (by
        simp [Prop62PaperAudit.V4.logarithmicLoss,
          pureWZ2Prop62DirectionLevelCount])
  have hrequiredCard :
      pureWZ2PreCommonBinRequiredCubeCount
          pullback neighborhoodLoss ≤
        (selection.selected.card : ENNReal) := by
    apply
      (ENNReal.mul_le_mul_iff_left hcostPos.ne' hcostTop).mp
    rw [mul_comm
        (pureWZ2PreCommonBinRequiredCubeCount
          pullback neighborhoodLoss),
      mul_comm (selection.selected.card : ENNReal)]
    exact hbudget.trans hsourceUpper
  let centerY : (ℤ × ℤ × ℤ) → ℝ := fun parent =>
    (((parent.2.1 : ℝ) + 1 / 2) *
      sqrtRequested.1)
  have hcenterYInjective :
      Set.InjOn centerY selection.selected := by
    intro first hfirst second hsecond heq
    apply selection.selected_y_injective hfirst hsecond
    have hrootRequested :
        0 < sqrtRequested.1 :=
      twoScale.fine.coarse_extremal.delta_pos
    have hcast :
        (first.2.1 : ℝ) = (second.2.1 : ℝ) := by
      have hcancel :
          ((first.2.1 : ℝ) + 1 / 2) =
            ((second.2.1 : ℝ) + 1 / 2) :=
        mul_right_cancel₀ hrootRequested.ne' heq
      linarith
    exact_mod_cast hcast
  let sample : Finset ℝ :=
    selection.selected.image centerY
  have hsampleNonempty : sample.Nonempty :=
    selection.selected_nonempty.image centerY
  let defaultParent :=
    Classical.choose selection.selected_nonempty
  let cube : ℝ → (ℤ × ℤ × ℤ) := fun y =>
    if hy : y ∈ sample then
      Classical.choose (Finset.mem_image.mp hy)
    else
      defaultParent
  have hcubeData :
      ∀ y (hy : y ∈ sample),
        cube y ∈ selection.selected ∧ centerY (cube y) = y := by
    intro y hy
    dsimp only [cube]
    rw [dif_pos hy]
    exact Classical.choose_spec (Finset.mem_image.mp hy)
  have hcubeSurjective :
      ∀ parent ∈ selection.selected,
        ∃ y ∈ sample, cube y = parent := by
    intro parent hparent
    let y := centerY parent
    have hy : y ∈ sample :=
      Finset.mem_image.mpr ⟨parent, hparent, rfl⟩
    refine ⟨y, hy, ?_⟩
    apply hcenterYInjective (hcubeData y hy).1 hparent
    exact (hcubeData y hy).2
  have hcubeInjective : Set.InjOn cube sample := by
    intro first hfirst second hsecond heq
    rw [← (hcubeData first hfirst).2,
      ← (hcubeData second hsecond).2, heq]
  have hsampleCard :
      sample.card = selection.selected.card := by
    exact Finset.card_image_of_injOn hcenterYInjective
  have hcubeParents :
      ∀ y ∈ sample, cube y ∈ parents := by
    intro y hy
    exact selection.selected_subset (hcubeData y hy).1
  have hcubeStandard :
      ∀ y ∈ sample,
        cube y ∈
          pullback.standardSqrtSlabParents heightIndex.1 := by
    intro y hy
    exact hparentsSubset (hcubeParents y hy)
  let witness : ℝ → Point3 := fun y => rawWitness (cube y)
  have hwitnessPullback :
      ∀ y ∈ sample,
        witness y ∈
          pullback.preCommonBinFinePullback (cube y) := by
    intro y hy
    have hraw := (hrawWitness (cube y) (hcubeParents y hy)).1
    have hregion := hraw.1
    have hpointPullback : witness y ∈ pullback.shading.union := by
      exact hregion.1.1
    rw [pullback.preCommonBinFinePullback_eq_parent]
    exact
      ⟨hpointPullback, by
        simpa [witness, root, pullback.sqrtRequested_eq] using hraw.2⟩
  have hwitnessHeight :
      ∀ y ∈ sample, witness y (2 : Fin 3) = lineHeight := by
    intro y hy
    exact (hrawWitness (cube y) (hcubeParents y hy)).2
  have hwitnessLine :
      ∀ y ∈ sample,
        |inner ℝ (witness y)
            (globalGrainDirection
              (source.globalGrains.slope lineHeight)) -
          lineLevel| ≤ delta := by
    intro y hy
    exact hrawWitnessLine (cube y) (hcubeParents y hy)
  have hpullbackLocalized :
      ∀ y ∈ sample,
        ∀ point ∈ pullback.preCommonBinFinePullback (cube y),
          |inner ℝ point
              (globalGrainDirection
                (source.globalGrains.slope lineHeight)) -
            lineLevel| ≤
          14 * sqrtRequested.1 := by
    intro y hy point hpoint
    have hpointCube :
        point ∈ wz1PaperGridCube root (cube y) := by
      simpa [root, pullback.sqrtRequested_eq] using
        pullback.preCommonBinFinePullback_subset_parent hpoint
    have hwitnessCube :
        witness y ∈ wz1PaperGridCube root (cube y) := by
      have hraw := (hrawWitness (cube y) (hcubeParents y hy)).1.2
      simpa [witness] using hraw
    rw [wz1PaperGridCube_eq_Ico hroot] at hpointCube hwitnessCube
    have hx :
        |point 0 - witness y 0| ≤ root := by
      rw [abs_le]
      constructor <;>
        linarith [hpointCube.1, hpointCube.2.1,
          hwitnessCube.1, hwitnessCube.2.1]
    have hyCoord :
        |point 1 - witness y 1| ≤ root := by
      rw [abs_le]
      constructor <;>
        linarith [hpointCube.2.2.1, hpointCube.2.2.2.1,
          hwitnessCube.2.2.1, hwitnessCube.2.2.2.1]
    have hslope :=
      source.globalGrains.slope_bound lineHeight hlineHeightRange
    have hprojection :
        |inner ℝ point
              (globalGrainDirection
                (source.globalGrains.slope lineHeight)) -
            inner ℝ (witness y)
              (globalGrainDirection
                (source.globalGrains.slope lineHeight))| ≤
          4 * root := by
      have hformula :
          inner ℝ point
                (globalGrainDirection
                  (source.globalGrains.slope lineHeight)) -
              inner ℝ (witness y)
                (globalGrainDirection
                  (source.globalGrains.slope lineHeight)) =
            (point 0 - witness y 0) +
              source.globalGrains.slope lineHeight *
                (point 1 - witness y 1) := by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
        ring
      rw [hformula]
      calc
        |(point 0 - witness y 0) +
            source.globalGrains.slope lineHeight *
              (point 1 - witness y 1)| ≤
            |point 0 - witness y 0| +
              |source.globalGrains.slope lineHeight| *
                |point 1 - witness y 1| := by
          simpa [abs_mul] using
            abs_add_le (point 0 - witness y 0)
              (source.globalGrains.slope lineHeight *
                (point 1 - witness y 1))
        _ ≤ root + 3 * root := by gcongr
        _ = 4 * root := by ring
    have htriangle :=
      abs_add_le
        (inner ℝ point
            (globalGrainDirection
              (source.globalGrains.slope lineHeight)) -
          inner ℝ (witness y)
            (globalGrainDirection
              (source.globalGrains.slope lineHeight)))
        (inner ℝ (witness y)
            (globalGrainDirection
              (source.globalGrains.slope lineHeight)) -
          lineLevel)
    have hrearrange :
        (inner ℝ point
              (globalGrainDirection
                (source.globalGrains.slope lineHeight)) -
            inner ℝ (witness y)
              (globalGrainDirection
                (source.globalGrains.slope lineHeight))) +
          (inner ℝ (witness y)
              (globalGrainDirection
                (source.globalGrains.slope lineHeight)) -
            lineLevel) =
          inner ℝ point
              (globalGrainDirection
                (source.globalGrains.slope lineHeight)) -
            lineLevel := by
      ring
    rw [hrearrange] at htriangle
    calc
      |inner ℝ point
            (globalGrainDirection
              (source.globalGrains.slope lineHeight)) -
          lineLevel| ≤
        |inner ℝ point
              (globalGrainDirection
                (source.globalGrains.slope lineHeight)) -
            inner ℝ (witness y)
              (globalGrainDirection
                (source.globalGrains.slope lineHeight))| +
          |inner ℝ (witness y)
              (globalGrainDirection
                (source.globalGrains.slope lineHeight)) -
            lineLevel| := htriangle
      _ ≤ 4 * root + delta :=
        add_le_add hprojection (hwitnessLine y hy)
      _ ≤ 14 * sqrtRequested.1 := by
        rw [pullback.sqrtRequested_eq]
        dsimp only [root]
        linarith
  have hsampleCenter :
      ∀ y ∈ sample,
        y =
          (((cube y).2.1 : ℝ) + 1 / 2) *
            sqrtRequested.1 := by
    intro y hy
    exact (hcubeData y hy).2.symm
  have hsampleSeparated :
      ∀ y₁ ∈ sample, ∀ y₂ ∈ sample, y₁ ≠ y₂ →
        500 * sqrtRequested.1 ≤ |y₁ - y₂| := by
    intro y₁ hy₁ y₂ hy₂ hne
    have hcubeNe : cube y₁ ≠ cube y₂ := by
      intro heq
      exact hne (hcubeInjective hy₁ hy₂ heq)
    have hindexSep :=
      selection.selected_y_separated
        (cube y₁) (hcubeData y₁ hy₁).1
        (cube y₂) (hcubeData y₂ hy₂).1 hcubeNe
    have hindexSepReal :
        (512 : ℝ) ≤
          |((cube y₁).2.1 : ℝ) - ((cube y₂).2.1 : ℝ)| := by
      exact_mod_cast hindexSep
    rw [hsampleCenter y₁ hy₁, hsampleCenter y₂ hy₂]
    have hrootRequested :
        0 < sqrtRequested.1 :=
      twoScale.fine.coarse_extremal.delta_pos
    rw [show
      ((((cube y₁).2.1 : ℝ) + 1 / 2) *
          sqrtRequested.1 -
        (((cube y₂).2.1 : ℝ) + 1 / 2) *
          sqrtRequested.1) =
        (((cube y₁).2.1 : ℝ) - ((cube y₂).2.1 : ℝ)) *
          sqrtRequested.1 by ring,
      abs_mul, abs_of_pos hrootRequested]
    nlinarith
  have hresidueBounds :
      0 ≤ (selection.residue : ℤ) ∧
        (selection.residue : ℤ) < 512 := by
    constructor
    · exact Int.natCast_nonneg _
    · exact_mod_cast selection.residue.isLt
  have hresidueQuotient :
      ∀ y ∈ sample, ∃ quotient : ℤ,
        (cube y).2.1 =
          (selection.residue : ℤ) + 512 * quotient := by
    intro y hy
    let value := (cube y).2.1
    refine ⟨value / 512, ?_⟩
    have hres :=
      selection.residue_eq (cube y) (hcubeData y hy).1
    have hres' :
        (cube y).2.1 % (512 : ℤ) =
          (selection.residue : ℤ) := by
      simpa [commonBinStandardParentY] using hres
    have hdecomp := Int.ediv_mul_add_emod value 512
    dsimp only [value] at hdecomp ⊢
    rw [hres'] at hdecomp
    calc
      (cube y).2.1 =
          (cube y).2.1 / 512 * 512 +
            (selection.residue : ℤ) := hdecomp.symm
      _ = (selection.residue : ℤ) +
          512 * ((cube y).2.1 / 512) := by ring
  let beforeResidue :=
    pullback.preCommonBinParentsFineShading selection.onePerY
  let aggregate :=
    pullback.preCommonBinParentsFineShading selection.selected
  have hcubeAtCenter :
      ∀ parent ∈ selection.selected,
        cube (centerY parent) = parent := by
    intro parent hparent
    have hy : centerY parent ∈ sample :=
      Finset.mem_image.mpr ⟨parent, hparent, rfl⟩
    apply hcenterYInjective (hcubeData (centerY parent) hy).1 hparent
    exact (hcubeData (centerY parent) hy).2
  have haggregateUnion :
      aggregate.union =
        ⋃ y ∈ sample,
          pullback.preCommonBinFinePullback (cube y) := by
    rw [pullback.preCommonBinParentsFineShading_union]
    ext point
    constructor
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨parent, hparent, hpointParent⟩
      rcases hcubeSurjective parent hparent with
        ⟨y, hy, hcube⟩
      exact Set.mem_iUnion₂.mpr
        ⟨y, hy, by simpa [hcube] using hpointParent⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨y, hy, hpointCube⟩
      exact Set.mem_iUnion₂.mpr
        ⟨cube y, (hcubeData y hy).1, hpointCube⟩
  have hsampleMass :
      (∑ parent ∈ selection.selected,
          (pullback.preCommonBinFinePullbackShading parent).mass) =
        ∑ y ∈ sample,
          (pullback.preCommonBinFinePullbackShading (cube y)).mass := by
    rw [show sample = selection.selected.image centerY by rfl,
      Finset.sum_image hcenterYInjective]
    apply Finset.sum_congr rfl
    intro parent hparent
    rw [hcubeAtCenter parent hparent]
  have haggregateMass :
      aggregate.mass =
        ∑ y ∈ sample,
          (pullback.preCommonBinFinePullbackShading (cube y)).mass := by
    rw [pullback.preCommonBinParentsFineShading_mass]
    exact hsampleMass
  have hfamilyMassLower :
      ∀ (family : Finset (ℤ × ℤ × ℤ)),
        family ⊆ parents →
        (family.card : ENNReal) * balanceMass ≤
          (pullback.preCommonBinParentsFineShading family).mass *
            cubeVolume := by
    intro family hfamily
    rw [pullback.preCommonBinParentsFineShading_mass]
    simpa [parentWeight] using hweightFamilyLower family hfamily
  have haggregateLower :
      (selection.selected.card : ENNReal) * balanceMass ≤
        aggregate.mass * cubeVolume := by
    exact hfamilyMassLower selection.selected selection.selected_subset
  have hbeforeLe :
      beforeResidue.mass ≤ 512 * aggregate.mass := by
    rw [pullback.preCommonBinParentsFineShading_mass,
      pullback.preCommonBinParentsFineShading_mass]
    simpa [parentWeight] using selection.onePerY_weight_le
  have hresidueMass :
      (512 : ENNReal)⁻¹ * beforeResidue.mass ≤ aggregate.mass := by
    calc
      (512 : ENNReal)⁻¹ * beforeResidue.mass ≤
          (512 : ENNReal)⁻¹ * (512 * aggregate.mass) := by
        simpa [mul_comm] using
          mul_le_mul_right hbeforeLe (512 : ENNReal)⁻¹
      _ = aggregate.mass := by
        calc
          (512 : ENNReal)⁻¹ * (512 * aggregate.mass) =
              ((512 : ENNReal)⁻¹ * 512) * aggregate.mass := by
            rw [mul_assoc]
          _ = aggregate.mass := by
            rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
              one_mul]
  let targetK :=
    Kakeya.realRpowENN rho
      (-1 / 2 + neighborhoodLoss)
  let targetMass :=
    Kakeya.realRpowENN rho
      (1 + sigma / 2 + neighborhoodLoss)
  have htargetKRequired :
      targetK ≤
        pureWZ2PreCommonBinRequiredCubeCount
          pullback neighborhoodLoss :=
    le_max_left _ _
  have hpaperK :
      targetK ≤ (sample.card : ENNReal) := by
    calc
      targetK ≤
          pureWZ2PreCommonBinRequiredCubeCount
            pullback neighborhoodLoss :=
        htargetKRequired
      _ ≤ (selection.selected.card : ENNReal) := hrequiredCard
      _ = (sample.card : ENNReal) := by
        exact_mod_cast hsampleCard.symm
  have hbalancePos : 0 < balanceMass := by
    exact hbalancePosEarly
  have hbalanceTop : balanceMass ≠ ⊤ := by
    exact hbalanceTopEarly
  have hmassFractionRequired :
      (targetMass * cubeVolume) / balanceMass ≤
        pureWZ2PreCommonBinRequiredCubeCount
          pullback neighborhoodLoss := by
    exact le_max_right _ _
  have htargetScaled :
      targetMass * cubeVolume ≤
        pureWZ2PreCommonBinRequiredCubeCount
            pullback neighborhoodLoss *
          balanceMass := by
    exact
      (ENNReal.div_le_iff_le_mul
        (Or.inl hbalancePos.ne') (Or.inl hbalanceTop)).mp
        hmassFractionRequired
  have hpaperMass :
      targetMass ≤ aggregate.mass := by
    apply
      (ENNReal.mul_le_mul_iff_right
        hcubeVolumePos.ne' hcubeVolumeTop).mp
    have hscaled :
        targetMass * cubeVolume ≤ aggregate.mass * cubeVolume := by
      calc
        targetMass * cubeVolume ≤
            pureWZ2PreCommonBinRequiredCubeCount
                pullback neighborhoodLoss *
              balanceMass :=
          htargetScaled
        _ ≤ (selection.selected.card : ENNReal) * balanceMass := by
          calc
            pureWZ2PreCommonBinRequiredCubeCount
                  pullback neighborhoodLoss * balanceMass =
                balanceMass *
                  pureWZ2PreCommonBinRequiredCubeCount
                    pullback neighborhoodLoss := by rw [mul_comm]
            _ ≤ balanceMass * (selection.selected.card : ENNReal) :=
              mul_le_mul_right hrequiredCard balanceMass
            _ = (selection.selected.card : ENNReal) * balanceMass := by
              rw [mul_comm]
        _ ≤ aggregate.mass * cubeVolume :=
          haggregateLower
    rw [mul_comm cubeVolume targetMass,
      mul_comm cubeVolume aggregate.mass]
    exact hscaled
  let neighborhoodData :
      PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback := {
    heightIndex := heightIndex
    lineHeight := lineHeight
    lineHeight_mem := hlineHeightRange
    lineHeight_mem_slab := hlineHeightContract
    sourcePopularHeights := popularData.popularHeights
    sourcePopularHeights_eq := by
      simpa using popularData.popularHeights_eq
    sourcePopularHeights_measurable :=
      popularData.popularHeights_measurable
    sourcePopularHalfMass := by
      simpa using popularData.popularHalfMass
    sourcePopularRegion := popularData.popularRegion
    sourcePopularRegion_eq := by
      simpa using popularData.popularRegion_eq
    sourcePopularRegion_measurable :=
      popularData.popularRegion_measurable
    sourcePopularRegion_half_volume := by
      simpa using popularData.popularRegion_half_volume
    lineHeight_mem_popular := by
      simpa [lineHeight] using popularData.referenceHeight_mem
    lineLevel := lineLevel
    sample := sample
    sample_nonempty := hsampleNonempty
    cube := cube
    cube_mem := hcubeStandard
    cube_injective := hcubeInjective
    K := sample.card
    K_eq := rfl
    residueClass := (selection.residue : ℤ)
    residueClass_bounds := hresidueBounds
    cube_y_bounded_residue := hresidueQuotient
    sample_eq_cube_center_y := hsampleCenter
    cube_separated := hsampleSeparated
    witness := witness
    witness_mem_pullback := hwitnessPullback
    witness_height := hwitnessHeight
    witness_near_global_grain := hwitnessLine
    pullback_global_line_localized := hpullbackLocalized
    aggregateFineShading := aggregate
    aggregate_sub_source :=
      pullback.preCommonBinParentsFineShading_sub_source
        selection.selected
    aggregate_union_eq := haggregateUnion
    aggregate_mass_eq := haggregateMass
    boundedResidueMassLoss := 512
    boundedResidueMassLoss_eq := rfl
    neighborhoodFineShadingBeforeResidue := beforeResidue
    neighborhoodFineShadingBeforeResidue_sub_source :=
      pullback.preCommonBinParentsFineShading_sub_source
        selection.onePerY
    bounded_residue_mass_retention := hresidueMass
    neighborhoodLoss := neighborhoodLoss
    paper_K_lower := by simpa [targetK] using hpaperK
    paper_total_mass_lower := by simpa [targetMass] using hpaperMass
  }
  exact ⟨{
    neighborhood := neighborhoodData
    heightIndex_eq := rfl
    neighborhoodLoss_eq := rfl
    source_slab_volume_upper := by
      rw [show neighborhoodData.K = sample.card by rfl, hsampleCard]
      simpa only [E, rootENN, root] using hsourceSlabUpper }⟩

/-- Compatibility entrance which selects a maximal occupied slab.  The actual
single-slab construction is `producePreCommonBinGlobalGrainNeighborhoodAt`. -/
theorem PureWZ2Node05V4RichTwoScaleCellPullbackData.producePreCommonBinGlobalGrainNeighborhood
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (neighborhoodLoss : ℝ)
    (hbudget :
      pureWZ2PreCommonBinGlobalNeighborhoodCost
          sigma inputLoss delta rho *
        pureWZ2PreCommonBinRequiredCubeCount
          pullback neighborhoodLoss ≤
        volume pullback.shading.union) :
    Nonempty
      (PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback) := by
  have hselected : pullback.selectedCells.Nonempty := by
    rcases twoScale.second.terminal.packetCells_nonempty with
      ⟨edge, hedge⟩
    rw [twoScale.second.terminal.packetCells_eq] at hedge
    have hactive :=
      (Finset.mem_product.mp (Finset.mem_filter.mp hedge).1).2
    rw [pullback.selectedCells_eq]
    exact ⟨edge.2, hactive⟩
  have hslabIndices : pullback.standardSqrtSlabIndices.Nonempty :=
    hselected.image pullback.standardSqrtSlabIndex
  let slabs : Finset
      {heightIndex // heightIndex ∈ pullback.standardSqrtSlabIndices} :=
    Finset.univ
  have hslabs : slabs.Nonempty := by
    rcases hslabIndices with ⟨heightIndex, hheightIndex⟩
    exact ⟨⟨heightIndex, hheightIndex⟩, Finset.mem_univ _⟩
  have hmaxExists :=
    Finset.exists_max_image slabs
      (fun heightIndex =>
        volume (pullback.standardSqrtSlabSourceRegion heightIndex.1))
      hslabs
  let heightIndex := Classical.choose hmaxExists
  have hheightIndexSpec := Classical.choose_spec hmaxExists
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hrhoOne : rho ≤ 1 := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.2
  let rootENN := ENNReal.ofReal (Real.sqrt rho)
  have hsourceE :
      volume pullback.shading.union ≤
        (pullback.standardSqrtSlabIndices.card : ENNReal) *
          volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) := by
    have hsumMax :
        (∑ slab ∈ slabs,
          volume (pullback.standardSqrtSlabSourceRegion slab.1)) ≤
          (slabs.card : ENNReal) *
            volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) := by
      simpa [nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul slabs
          (fun slab =>
            volume (pullback.standardSqrtSlabSourceRegion slab.1))
          (volume (pullback.standardSqrtSlabSourceRegion heightIndex.1))
          (fun slab hslab => hheightIndexSpec.2 slab hslab))
    rw [show volume pullback.shading.union =
        ∑ slab : {heightIndex //
            heightIndex ∈ pullback.standardSqrtSlabIndices},
          volume (pullback.standardSqrtSlabSourceRegion slab.1) by
      exact pullback.sum_standardSqrtSlabSourceRegion_volume_subtype.symm]
    simpa only [slabs, Finset.sum_filter, Finset.mem_univ, if_true,
      Finset.card_univ, Fintype.card_coe] using hsumMax
  have hcountRoot :
      (pullback.standardSqrtSlabIndices.card : ENNReal) * rootENN ≤ 5 := by
    simpa only [rootENN] using
      pullback.standardSqrtSlabIndices_card_mul_sqrtENN_le_five hrhoOne
  have hsourceSlab :
      volume pullback.shading.union * ENNReal.ofReal (Real.sqrt rho) ≤
        5 * volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) := by
    calc
      volume pullback.shading.union * ENNReal.ofReal (Real.sqrt rho) ≤
          ((pullback.standardSqrtSlabIndices.card : ENNReal) *
            volume (pullback.standardSqrtSlabSourceRegion heightIndex.1)) *
              rootENN := by
        simpa only [rootENN, mul_comm] using mul_le_mul_right hsourceE rootENN
      _ = ((pullback.standardSqrtSlabIndices.card : ENNReal) * rootENN) *
          volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) := by ring
      _ ≤ 5 * volume
          (pullback.standardSqrtSlabSourceRegion heightIndex.1) := by gcongr
  rcases pullback.producePreCommonBinGlobalGrainNeighborhoodAt
    heightIndex 5 (by norm_num) (by norm_num) hsourceSlab hbridge
      neighborhoodLoss (by
        simpa only [pureWZ2PreCommonBinGlobalNeighborhoodCost,
          pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor] using hbudget)
    with ⟨indexed⟩
  exact ⟨indexed.neighborhood⟩

end Kakeya.Assouad

end
