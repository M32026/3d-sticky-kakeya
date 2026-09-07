import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseCarrier
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains

/-!
# Original-source grains after a selected coarse-region pullback

The ordinary Lemma-24 argument first selects a geometric region on the
first-sticky coarse carrier and only then pulls that region back through the
first balanced cover.  This module prepares the resulting original-family
shading for Lemma 23.  In particular, both the global slope and the local
plane map are restrictions of the original source data; no coarse slope is
substituted for the source slope.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The original-source local and global grain data on a pulled-back coarse
region. -/
structure PureWZ2SelectedCoarseRegionSourcePreparation
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {selected : WZ1PaperTubeShading twoScale.coarse.coarse}
    (pullback : PureWZ2SelectedCoarseRegionSourcePullbackData selected) where
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily pullback.shading source.extremal.delta_pos) :=
    pureWZ2ActiveCellShading pullback.shading source.extremal.delta_pos
  shadow_union : shadow.union = pullback.shading.union
  localPaper : PureWZ2LocalGrainData pullback.shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  globalPaper : PureWZ2LipschitzGlobalGrainData pullback.shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  globalPaper_slope_eq : globalPaper.slope = source.globalGrains.slope
  localGrains : WZ1LocalGrainData shadow sigma
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  planeMap_eq_on_paper :
    ∀ point : {point : Point3 // point ∈ pullback.shading.union},
      localGrains.planeMap point = localPaper.planeMap point
  planeMap_vertical_bound :
    ∀ point ∈ shadow.union,
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  exactAD_delta :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice shadow.union z))
        delta (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss))
  exactAD_rho :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice shadow.union z))
        rho (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss))

/-- Restrict the original source grain fields to the exact same-density
pullback of a genuine coarse cubical region. -/
theorem PureWZ2SelectedCoarseRegionSourcePullbackData.prepareSourceCarrier
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {selected : WZ1PaperTubeShading twoScale.coarse.coarse}
    (pullback : PureWZ2SelectedCoarseRegionSourcePullbackData selected)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2SelectedCoarseRegionSourcePreparation pullback) := by
  let C := Kakeya.realRpowENN delta (-inputLoss)
  have hCtop : C ≠ ⊤ := by simp [C, Kakeya.realRpowENN]
  let localPaper := source.localGrains.restrictWithConstant
    pullback.subshading le_rfl hCtop
  let globalPaper := source.globalGrains.restrict
    pullback.subshading le_rfl hCtop
  let shadow := pureWZ2ActiveCellShading
    pullback.shading source.extremal.delta_pos
  have hunion : shadow.union = pullback.shading.union :=
    pureWZ2ActiveCellShading_union pullback.shading
      source.extremal.delta_pos pullback.whole_cells
  let localGrains := localPaper.toActiveCellShadow
    source.extremal.delta_pos pullback.whole_cells hbridge
  have hplane :
      ∀ point : {point : Point3 // point ∈ pullback.shading.union},
        localGrains.planeMap point = localPaper.planeMap point := by
    intro point
    exact (Classical.choose_spec localPaper.exists_ambient_extension).2 point
  have hverticalPaper :
      ∀ point : {point : Point3 // point ∈ pullback.shading.union},
        |localPaper.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact source.planeMap_vertical_bound
      ⟨point, pullback.subshading.union_subset point.property⟩
  have hvertical :
      ∀ point ∈ shadow.union,
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 :=
    localPaper.toActiveCellShadow_vertical_bound
      source.extremal.delta_pos pullback.whole_cells hbridge hverticalPaper
  have hdeltaRho : delta ≤ rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1
  have hrho : 0 < rho := source.extremal.delta_pos.trans_le hdeltaRho
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hexactDelta :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice shadow.union z))
          delta (1 - sigma) (10 * C) := by
    intro z hz
    have h := globalPaper.activeCellShadow_exactAD
      source.extremal.delta_pos pullback.whole_cells hbridge
      globalPaper.slope_bound z hz
    rwa [show globalPaper.slope = source.globalGrains.slope by rfl] at h
  have hexactRho :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice shadow.union z))
          rho (1 - sigma) (10 * C) := by
    intro z hz
    exact (hexactDelta z hz).coarsen_scale hrho hdeltaRho hrhoOne
  exact ⟨{
    shadow := shadow
    shadow_union := hunion
    localPaper := localPaper
    globalPaper := globalPaper
    globalPaper_slope_eq := rfl
    localGrains := localGrains
    planeMap_eq_on_paper := hplane
    planeMap_vertical_bound := hvertical
    exactAD_delta := by simpa [C] using hexactDelta
    exactAD_rho := by simpa [C] using hexactRho
  }⟩

/-- The fixed-line coarse carrier can be pulled back and immediately prepared
with the original source slope and plane map. -/
theorem PureWZ2SourceFixedLineCoarseCarrierData.pullbackAndPrepareSourceCarrier
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (data : PureWZ2SourceFixedLineCoarseCarrierData residue)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    ∃ sourcePullback :
        PureWZ2SelectedCoarseRegionSourcePullbackData data.shading,
      Nonempty
        (PureWZ2SelectedCoarseRegionSourcePreparation sourcePullback) := by
  rcases data.pullbackToSource with ⟨sourcePullback⟩
  exact ⟨sourcePullback, sourcePullback.prepareSourceCarrier hbridge⟩

/-- The source residue previously used by the finite Lemma-23 graph occupies
exactly the pullback of the coarse region selected from the same fixed line.
This identifies only the spatial unions; it does not identify tube families
or global slopes. -/
theorem PureWZ2SelectedCoarseRegionSourcePullbackData.union_eq_sourceResidue
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {firstPullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation firstPullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {coarseCarrier : PureWZ2SourceFixedLineCoarseCarrierData residue}
    (sourcePullback :
      PureWZ2SelectedCoarseRegionSourcePullbackData coarseCarrier.shading)
    (retained : PureWZ2SourceHorizontalResidueShadingData residue) :
    sourcePullback.shading.union = retained.shading.union := by
  have hfineUnion :
      twoScale.fine.refined.union =
        ⋃ cell ∈ firstPullback.selectedCells,
          wz1PaperGridCube rho cell := by
    have hraw := twoScale.fine.refined_cubical.union_eq_activeCells
      twoScale.coarseGrains.extremal.delta_pos
    rw [firstPullback.selectedCells_eq]
    simpa only [twoScale.rhoRequested_eq] using hraw
  have hregion : retained.selectedRegion = coarseCarrier.shading.union := by
    rw [retained.selectedRegion_eq, coarseCarrier.union_eq,
      coarseCarrier.selectedRegion_eq]
    ext point
    constructor
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨cell, hcell, hpointCell⟩
      have hcellData := Finset.mem_filter.mp (by
        rw [retained.selectedCells_eq] at hcell
        exact hcell)
      refine ⟨?_, Set.mem_iUnion₂.mpr
        ⟨retained.cellParent cell, hcellData.2,
          retained.cell_parent cell hcellData.1 hpointCell⟩⟩
      rw [hfineUnion]
      exact Set.mem_iUnion₂.mpr ⟨cell, hcellData.1, hpointCell⟩
    · rintro ⟨hpointFine, hpointParent⟩
      rw [hfineUnion] at hpointFine
      rcases Set.mem_iUnion₂.mp hpointFine with
        ⟨cell, hcell, hpointCell⟩
      rcases Set.mem_iUnion₂.mp hpointParent with
        ⟨parent, hparent, hpointParent⟩
      have hpointCanonicalParent := retained.cell_parent cell hcell hpointCell
      have hparentEq : retained.cellParent cell = parent :=
        ((mem_wz1PaperGridCube twoScale.sqrtRequested.1
          (retained.cellParent cell) point).mp hpointCanonicalParent).symm.trans
          ((mem_wz1PaperGridCube twoScale.sqrtRequested.1 parent point).mp
            hpointParent)
      exact Set.mem_iUnion₂.mpr ⟨cell, by
        rw [retained.selectedCells_eq]
        exact Finset.mem_filter.mpr ⟨hcell, by rwa [hparentEq]⟩, hpointCell⟩
  ext point
  constructor
  · intro hpoint
    rw [sourcePullback.union_eq] at hpoint
    have hcoarse : point ∈ coarseCarrier.shading.union := by
      rw [← sourcePullback.selectedRegion_eq_coarse]
      exact hpoint.2
    have hfine : point ∈ twoScale.fine.refined.union := by
      rw [coarseCarrier.union_eq] at hcoarse
      exact hcoarse.1
    rw [retained.union_eq]
    refine ⟨?_, ?_⟩
    · rw [firstPullback.union_eq]
      have hambient :
          point ∈ firstPullback.zeroExtension.ambientShading.union := by
        rw [firstPullback.zeroExtension.union_eq]
        rw [sourcePullback.zeroExtension.union_eq] at hpoint
        exact hpoint.1
      have hfirstRegion : point ∈ firstPullback.selectedRegion := by
        rw [firstPullback.selectedRegion_eq, ← hfineUnion]
        exact hfine
      exact ⟨hambient, hfirstRegion⟩
    · rwa [hregion]
  · intro hpoint
    rw [retained.union_eq] at hpoint
    have hfirst := hpoint.1
    rw [firstPullback.union_eq] at hfirst
    rw [sourcePullback.union_eq]
    refine ⟨?_, ?_⟩
    · rw [sourcePullback.zeroExtension.union_eq]
      rw [firstPullback.zeroExtension.union_eq] at hfirst
      exact hfirst.1
    rw [sourcePullback.selectedRegion_eq_coarse, ← hregion]
    exact hpoint.2

/-- The two descriptions of the original-source pullback agree tube by tube.
This is the indexed form needed to transfer the exact mass identity, not an
identification of either source family with the coarse family. -/
theorem PureWZ2SelectedCoarseRegionSourcePullbackData.carrier_eq_sourceResidue
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {firstPullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation firstPullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {coarseCarrier : PureWZ2SourceFixedLineCoarseCarrierData residue}
    (sourcePullback :
      PureWZ2SelectedCoarseRegionSourcePullbackData coarseCarrier.shading)
    (retained : PureWZ2SourceHorizontalResidueShadingData residue)
    (index : Fin source.family.card) :
    sourcePullback.shading.carrier index = retained.shading.carrier index := by
  have hambient :
      sourcePullback.zeroExtension.ambientShading.carrier index =
        firstPullback.zeroExtension.ambientShading.carrier index := by
    ext point
    constructor
    · intro hpoint
      rcases sourcePullback.zeroExtension.carrier_support index point hpoint with
        ⟨selectedIndex, heq, hselected⟩
      rw [← heq, firstPullback.zeroExtension.carrier_embedding]
      exact hselected
    · intro hpoint
      rcases firstPullback.zeroExtension.carrier_support index point hpoint with
        ⟨selectedIndex, heq, hselected⟩
      rw [← heq, sourcePullback.zeroExtension.carrier_embedding]
      exact hselected
  have hregion : retained.selectedRegion = coarseCarrier.shading.union := by
    rw [retained.selectedRegion_eq, coarseCarrier.union_eq,
      coarseCarrier.selectedRegion_eq]
    ext point
    constructor
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨cell, hcell, hpointCell⟩
      have hcellData := Finset.mem_filter.mp (by
        rw [retained.selectedCells_eq] at hcell
        exact hcell)
      refine ⟨?_, Set.mem_iUnion₂.mpr
        ⟨retained.cellParent cell, hcellData.2,
          retained.cell_parent cell hcellData.1 hpointCell⟩⟩
      have hfineUnion := twoScale.fine.refined_cubical.union_eq_activeCells
        twoScale.coarseGrains.extremal.delta_pos
      rw [firstPullback.selectedCells_eq] at hcellData
      rw [hfineUnion]
      simpa only [twoScale.rhoRequested_eq] using
        Set.mem_iUnion₂.mpr ⟨cell, hcellData.1, by
          simpa only [twoScale.rhoRequested_eq] using hpointCell⟩
    · rintro ⟨hpointFine, hpointParent⟩
      have hfineUnion := twoScale.fine.refined_cubical.union_eq_activeCells
        twoScale.coarseGrains.extremal.delta_pos
      rw [hfineUnion] at hpointFine
      rcases Set.mem_iUnion₂.mp hpointFine with
        ⟨cell, hcell, hpointCell⟩
      have hcellFirst : cell ∈ firstPullback.selectedCells := by
        rw [firstPullback.selectedCells_eq]
        simpa only [twoScale.rhoRequested_eq] using hcell
      rcases Set.mem_iUnion₂.mp hpointParent with
        ⟨parent, hparent, hpointParent⟩
      have hpointCellRho : point ∈ wz1PaperGridCube rho cell := by
        simpa only [twoScale.rhoRequested_eq] using hpointCell
      have hpointCanonicalParent :=
        retained.cell_parent cell hcellFirst hpointCellRho
      have hparentEq : retained.cellParent cell = parent :=
        ((mem_wz1PaperGridCube twoScale.sqrtRequested.1
          (retained.cellParent cell) point).mp hpointCanonicalParent).symm.trans
          ((mem_wz1PaperGridCube twoScale.sqrtRequested.1 parent point).mp
            hpointParent)
      exact Set.mem_iUnion₂.mpr ⟨cell, by
        rw [retained.selectedCells_eq]
        exact Finset.mem_filter.mpr ⟨hcellFirst, by rwa [hparentEq]⟩,
          hpointCellRho⟩
  have hregionSubset : retained.selectedRegion ⊆ firstPullback.selectedRegion := by
    intro point hpoint
    rw [retained.selectedRegion_eq] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
    have hcellFirst : cell ∈ firstPullback.selectedCells :=
      retained.selectedCells_subset hcell
    rw [firstPullback.selectedRegion_eq]
    exact Set.mem_iUnion₂.mpr ⟨cell, hcellFirst, hpointCell⟩
  rw [sourcePullback.carrier_eq, retained.carrier_eq,
    firstPullback.carrier_eq, hambient, sourcePullback.selectedRegion_eq_coarse,
    ← hregion]
  ext point
  constructor
  · rintro ⟨hambientPoint, hretainedRegion⟩
    exact ⟨⟨hambientPoint, hregionSubset hretainedRegion⟩, hretainedRegion⟩
  · rintro ⟨⟨hambientPoint, _hfirstRegion⟩, hretainedRegion⟩
    exact ⟨hambientPoint, hretainedRegion⟩

/-- Exact relative-volume identity for the source shading used by the
same-carrier Lemma-23 graph. -/
theorem PureWZ2SelectedCoarseRegionSourcePullbackData.sourceResidue_volume_cross
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {firstPullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation firstPullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {coarseCarrier : PureWZ2SourceFixedLineCoarseCarrierData residue}
    (sourcePullback :
      PureWZ2SelectedCoarseRegionSourcePullbackData coarseCarrier.shading)
    (retained : PureWZ2SourceHorizontalResidueShadingData residue) :
    MeasureTheory.volume retained.shading.union *
        MeasureTheory.volume twoScale.coarse.croppedCoarseShading.union =
      MeasureTheory.volume coarseCarrier.shading.union *
        MeasureTheory.volume twoScale.coarse.refined.union := by
  rw [← sourcePullback.union_eq_sourceResidue retained]
  simpa [sourcePullback.selectedRegion_eq_coarse] using
    sourcePullback.volume_cross

/-- Indexed-mass form of the same relative-density identity. -/
theorem PureWZ2SelectedCoarseRegionSourcePullbackData.sourceResidue_mass_cross
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {firstPullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation firstPullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {coarseCarrier : PureWZ2SourceFixedLineCoarseCarrierData residue}
    (sourcePullback :
      PureWZ2SelectedCoarseRegionSourcePullbackData coarseCarrier.shading)
    (retained : PureWZ2SourceHorizontalResidueShadingData residue) :
    retained.shading.mass *
        MeasureTheory.volume twoScale.coarse.croppedCoarseShading.union =
      MeasureTheory.volume coarseCarrier.shading.union *
        twoScale.coarse.refined.mass := by
  have hmass : sourcePullback.shading.mass = retained.shading.mass := by
    change
      (∑ index : Fin source.family.card,
          MeasureTheory.volume (sourcePullback.shading.carrier index)) =
        ∑ index : Fin source.family.card,
          MeasureTheory.volume (retained.shading.carrier index)
    apply Finset.sum_congr rfl
    intro index _
    rw [sourcePullback.carrier_eq_sourceResidue retained index]
  rw [← hmass]
  simpa [sourcePullback.selectedRegion_eq_coarse] using
    sourcePullback.mass_cross

/-- The fixed-line Fubini supply on the coarse region and the exact
same-relative-density pullback combine without a second first-stage cell-mass
factor. -/
theorem PureWZ2SourceFixedLineCoarseCarrierData.sourceResidue_volume_supply_le
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {firstPullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation firstPullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (coarseCarrier : PureWZ2SourceFixedLineCoarseCarrierData residue)
    (sourcePullback :
      PureWZ2SelectedCoarseRegionSourcePullbackData coarseCarrier.shading)
    (retained : PureWZ2SourceHorizontalResidueShadingData residue) :
    (window.volumeSupply * twoScale.fine.balanced.cellMass) *
        MeasureTheory.volume twoScale.coarse.refined.union ≤
      pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        (MeasureTheory.volume retained.shading.union *
          MeasureTheory.volume
            twoScale.coarse.croppedCoarseShading.union) := by
  calc
    (window.volumeSupply * twoScale.fine.balanced.cellMass) *
          MeasureTheory.volume twoScale.coarse.refined.union ≤
        (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          MeasureTheory.volume coarseCarrier.shading.union) *
            MeasureTheory.volume twoScale.coarse.refined.union := by
      exact mul_le_mul_right' coarseCarrier.volume_supply_le _
    _ = pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          (MeasureTheory.volume coarseCarrier.shading.union *
            MeasureTheory.volume twoScale.coarse.refined.union) := by ring
    _ = pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          (MeasureTheory.volume retained.shading.union *
            MeasureTheory.volume
              twoScale.coarse.croppedCoarseShading.union) := by
      rw [sourcePullback.sourceResidue_volume_cross retained]

end Kakeya.Assouad

end
