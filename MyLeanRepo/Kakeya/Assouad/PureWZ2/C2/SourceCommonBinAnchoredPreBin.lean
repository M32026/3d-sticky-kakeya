import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantAnchoredPostOwner
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CommonBinRhoHeightUniformization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CommonBinRhoHeightLogCost

/-!
# Anchored pre-bin height regularization

All retained cells and source restrictions in this file are derived from one
`PureWZ2AnchoredSourceRelativeFineSelection`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

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

private theorem exists_standardSecondParent
    {cell : ℤ × ℤ × ℤ} (hcell : cell ∈ selected.selectedCells) :
    ∃ parent ∈ fine.balanced.activeCells,
      wz1PaperGridCube rhoRequested.1 cell ⊆
        wz1PaperGridCube sqrtRequested.1 parent := by
  have hactive :
      cell ∈ wz1PaperActiveCells fine.refined
        coarse.coarse_extremal.delta_pos := by
    simpa only [selected.selectedCells_eq] using hcell
  rw [mem_wz1PaperActiveCells] at hactive
  rcases hactive.2 with ⟨point, ⟨index, hpoint⟩, hpointCell⟩
  rcases fine.balanced.fine_cell_nested index point hpoint with
    ⟨parent, hparent, hnested⟩
  have hindex :
      wz1PaperGridIndex rhoRequested.1 point = cell :=
    (mem_wz1PaperGridCube rhoRequested.1 cell point).mp hpointCell
  refine ⟨parent, hparent, ?_⟩
  rwa [hindex] at hnested

noncomputable def standardSecondParent
    (cell : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  if hcell : cell ∈ selected.selectedCells then
    Classical.choose (selected.exists_standardSecondParent hcell)
  else (0, 0, 0)

theorem standardSecondParent_active
    {cell : ℤ × ℤ × ℤ} (hcell : cell ∈ selected.selectedCells) :
    selected.standardSecondParent cell ∈ fine.balanced.activeCells := by
  rw [standardSecondParent, dif_pos hcell]
  exact (Classical.choose_spec
    (selected.exists_standardSecondParent hcell)).1

theorem standardSecondParent_cell_subset
    {cell : ℤ × ℤ × ℤ} (hcell : cell ∈ selected.selectedCells) :
    wz1PaperGridCube rhoRequested.1 cell ⊆
      wz1PaperGridCube sqrtRequested.1
        (selected.standardSecondParent cell) := by
  rw [standardSecondParent, dif_pos hcell]
  exact (Classical.choose_spec
    (selected.exists_standardSecondParent hcell)).2

def standardSqrtSlabIndex (cell : ℤ × ℤ × ℤ) : ℤ :=
  (selected.standardSecondParent cell).2.2

def standardSqrtSlabIndices : Finset ℤ :=
  selected.selectedCells.image selected.standardSqrtSlabIndex

def standardSqrtSlabRhoCells (heightIndex : ℤ) :
    Finset (ℤ × ℤ × ℤ) :=
  selected.selectedCells.filter fun cell =>
    selected.standardSqrtSlabIndex cell = heightIndex

theorem standardSqrtSlabRhoCells_subset (heightIndex : ℤ) :
    selected.standardSqrtSlabRhoCells heightIndex ⊆
      selected.selectedCells :=
  Finset.filter_subset _ _

theorem standardSqrtSlabRhoCells_nonempty
    {heightIndex : ℤ}
    (hheight : heightIndex ∈ selected.standardSqrtSlabIndices) :
    (selected.standardSqrtSlabRhoCells heightIndex).Nonempty := by
  rcases Finset.mem_image.mp hheight with ⟨cell, hcell, hindex⟩
  exact ⟨cell, Finset.mem_filter.mpr ⟨hcell, hindex⟩⟩

end PureWZ2AnchoredSourceRelativeFineSelection

structure PureWZ2AnchoredSelectedCellSourcePullback
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
    (cells : Finset (ℤ × ℤ × ℤ)) where
  cells_subset : cells ⊆ selected.selectedCells
  region : Set Point3 :=
    ⋃ cell ∈ cells, wz1PaperGridCube rhoRequested.1 cell
  region_eq :
    region = ⋃ cell ∈ cells, wz1PaperGridCube rhoRequested.1 cell
  shading : WZ1PaperTubeShading source.family
  carrier_eq : ∀ index,
    shading.carrier index = selected.zeroExtension.ambientShading.carrier index ∩ region
  subshading : PureWZ2PaperIsSubshading shading source.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  union_eq :
    shading.union = selected.zeroExtension.ambientShading.union ∩ region
  volume_eq :
    volume shading.union =
      (cells.card : ENNReal) * coarse.balanced.cellMass
  mass_eq :
    shading.mass =
      (cells.card : ENNReal) * coarse.balanced.incidenceMass

theorem PureWZ2AnchoredSourceRelativeFineSelection.restrictCells
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
    (cells : Finset (ℤ × ℤ × ℤ))
    (hcells : cells ⊆ selected.selectedCells) :
    Nonempty (PureWZ2AnchoredSelectedCellSourcePullback selected cells) := by
  let region : Set Point3 :=
    ⋃ cell ∈ cells, wz1PaperGridCube rhoRequested.1 cell
  have hregion : MeasurableSet region :=
    MeasurableSet.biUnion cells.finite_toSet.countable
      (fun cell _ => wz1PaperGridCube_measurable cell)
  let shading : WZ1PaperTubeShading source.family :=
    { carrier := fun index =>
        selected.zeroExtension.ambientShading.carrier index ∩ region
      measurable_carrier := fun index =>
        (selected.zeroExtension.ambientShading.measurable_carrier index).inter
          hregion
      subset_body := fun index =>
        Set.inter_subset_left.trans
          (selected.zeroExtension.ambientShading.subset_body index) }
  have hunion :
      shading.union =
        selected.zeroExtension.ambientShading.union ∩ region := by
    ext point
    constructor
    · rintro ⟨index, hsource, hregionPoint⟩
      exact ⟨⟨index, hsource⟩, hregionPoint⟩
    · rintro ⟨⟨index, hsource⟩, hregionPoint⟩
      exact ⟨index, hsource, hregionPoint⟩
  have hsub : PureWZ2PaperIsSubshading shading source.shading := by
    intro index point hpoint
    rcases selected.zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, heq, hselected⟩
    subst index
    exact coarse.subshading selectedIndex hselected
  have hwhole : WZ1PaperIsCubicalShading shading := by
    intro index point hpoint other hother
    have hambient :=
      selected.zeroExtension.cubical coarse.refined_cubical
        index point hpoint.1
    rcases selected.zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, _heq, hselected⟩
    rcases coarse.balanced.fine_cell_nested
        selectedIndex point hselected with
      ⟨coarseCell, _hcoarseCell, hnested⟩
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨cell, hcell, hpointCell⟩
    have hpointNested := hnested
      ((mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) point).mpr rfl)
    have hcellEq : coarseCell = cell :=
      ((mem_wz1PaperGridCube rhoRequested.1 coarseCell point).mp
        hpointNested).symm.trans
      ((mem_wz1PaperGridCube rhoRequested.1 cell point).mp hpointCell)
    exact ⟨hambient hother, Set.mem_iUnion₂.mpr
      ⟨cell, hcell, by rw [← hcellEq]; exact hnested hother⟩⟩
  have hvolume :
      volume shading.union =
        (cells.card : ENNReal) * coarse.balanced.cellMass := by
    rw [hunion]
    have hdisjoint :
        (cells : Set (ℤ × ℤ × ℤ)).PairwiseDisjoint
          (fun cell =>
            selected.zeroExtension.ambientShading.union ∩
              wz1PaperGridCube rhoRequested.1 cell) := by
      intro first _ second _ hne
      exact (wz1PaperGridCube_disjoint hne).mono
        Set.inter_subset_right Set.inter_subset_right
    rw [show selected.zeroExtension.ambientShading.union ∩ region =
        ⋃ cell ∈ cells,
          selected.zeroExtension.ambientShading.union ∩
            wz1PaperGridCube rhoRequested.1 cell by
      ext point
      simp only [region, Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
      aesop]
    have hmeasure := measure_biUnion_finset (μ := volume) hdisjoint (by
      intro cell _
      exact selected.zeroExtension.ambientShading.union_measurable.inter
        (wz1PaperGridCube_measurable cell))
    rw [hmeasure]
    calc
      ∑ cell ∈ cells,
          volume (selected.zeroExtension.ambientShading.union ∩
            wz1PaperGridCube rhoRequested.1 cell) =
          ∑ _cell ∈ cells, coarse.balanced.cellMass := by
        apply Finset.sum_congr rfl
        intro cell hcell
        rw [← selected.cell_mass cell (hcells hcell)]
        congr 1
        ext point
        rw [selected.union_eq]
        constructor
        · rintro ⟨hsource, hpointCell⟩
          refine ⟨⟨hsource, ?_⟩, hpointCell⟩
          rw [selected.selectedRegion_eq]
          exact Set.mem_iUnion₂.mpr
            ⟨cell, hcells hcell, hpointCell⟩
        · rintro ⟨⟨hsource, _⟩, hpointCell⟩
          exact ⟨hsource, hpointCell⟩
      _ = _ := by simp
  have hmass :
      shading.mass =
        (cells.card : ENNReal) * coarse.balanced.incidenceMass := by
    have hcarrier :
        ∀ sourceIndex : Fin source.family.card,
          shading.carrier sourceIndex =
            ⋃ cell ∈ cells,
              shading.carrier sourceIndex ∩
                wz1PaperGridCube rhoRequested.1 cell := by
      intro sourceIndex
      ext point
      constructor
      · intro hpoint
        change point ∈
          selected.zeroExtension.ambientShading.carrier sourceIndex ∩
            region at hpoint
        rcases Set.mem_iUnion₂.mp hpoint.2 with
          ⟨cell, hcell, hpointCell⟩
        exact Set.mem_iUnion₂.mpr
          ⟨cell, hcell, hpoint, hpointCell⟩
      · rintro hpoint
        rcases Set.mem_iUnion₂.mp hpoint with
          ⟨_cell, _hcell, hsource, _hpointCell⟩
        exact hsource
    have hcarrierVolume :
        ∀ sourceIndex : Fin source.family.card,
          volume (shading.carrier sourceIndex) =
            ∑ cell ∈ cells,
              volume (shading.carrier sourceIndex ∩
                wz1PaperGridCube rhoRequested.1 cell) := by
      intro sourceIndex
      calc
        volume (shading.carrier sourceIndex) =
            volume (⋃ cell ∈ cells,
              shading.carrier sourceIndex ∩
                wz1PaperGridCube rhoRequested.1 cell) :=
          congrArg volume (hcarrier sourceIndex)
        _ = _ := by
          apply measure_biUnion_finset
          · intro first _ second _ hne
            exact (wz1PaperGridCube_disjoint hne).mono
              Set.inter_subset_right Set.inter_subset_right
          · intro cell _
            exact (shading.measurable_carrier sourceIndex).inter
              (wz1PaperGridCube_measurable cell)
    calc
      shading.mass =
          ∑ sourceIndex : Fin source.family.card,
            ∑ cell ∈ cells,
              volume (shading.carrier sourceIndex ∩
                wz1PaperGridCube rhoRequested.1 cell) := by
        apply Finset.sum_congr rfl
        intro sourceIndex _
        exact hcarrierVolume sourceIndex
      _ = ∑ cell ∈ cells,
          ∑ sourceIndex : Fin source.family.card,
            volume (shading.carrier sourceIndex ∩
              wz1PaperGridCube rhoRequested.1 cell) := by
        rw [Finset.sum_comm]
      _ = ∑ _cell ∈ cells, coarse.balanced.incidenceMass := by
        apply Finset.sum_congr rfl
        intro cell hcell
        have hambient := selected.cell_incidence_mass cell (hcells hcell)
        rw [← hambient]
        apply Finset.sum_congr rfl
        intro sourceIndex _
        congr 1
        ext point
        constructor
        · rintro ⟨hsource, hpointCell⟩
          change point ∈
            selected.zeroExtension.ambientShading.carrier sourceIndex ∩
              region at hsource
          rw [selected.carrier_eq]
          refine ⟨⟨hsource.1, ?_⟩, hpointCell⟩
          rw [selected.selectedRegion_eq]
          exact Set.mem_iUnion₂.mpr
            ⟨cell, hcells hcell, hpointCell⟩
        · rintro ⟨hsource, hpointCell⟩
          rw [selected.carrier_eq] at hsource
          exact ⟨⟨hsource.1, Set.mem_iUnion₂.mpr
            ⟨cell, hcell, hpointCell⟩⟩, hpointCell⟩
      _ = _ := by simp
  exact ⟨{
    cells_subset := hcells
    region := region
    region_eq := rfl
    shading := shading
    carrier_eq := fun _ => rfl
    subshading := hsub
    whole_cells := hwhole
    union_eq := hunion
    volume_eq := hvolume
    mass_eq := hmass
  }⟩

structure PureWZ2AnchoredPreBinRhoHeightRegularizedData
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
    (heightIndex : {heightIndex // heightIndex ∈
      selected.standardSqrtSlabIndices}) where
  sqrtRequested_eq :
    sqrtRequested.1 = Real.sqrt rhoRequested.1
  uniform :
    CommonBinRhoHeightUniformData
      (selected.standardSqrtSlabRhoCells heightIndex.1)
  cells : Finset (ℤ × ℤ × ℤ) := uniform.cells
  cells_eq : cells = uniform.cells
  cells_subset_standard :
    cells ⊆ selected.standardSqrtSlabRhoCells heightIndex.1
  cells_subset_selected : cells ⊆ selected.selectedCells
  cells_nonempty : cells.Nonempty
  sourcePullback :
    PureWZ2AnchoredSelectedCellSourcePullback selected cells
  source_volume :
    volume sourcePullback.shading.union =
      (cells.card : ENNReal) * coarse.balanced.cellMass
  source_mass :
    sourcePullback.shading.mass =
      (cells.card : ENNReal) * coarse.balanced.incidenceMass
  logarithmicCost : ℕ := uniform.logarithmicCost
  logarithmicCost_eq :
    logarithmicCost =
      Nat.log 2 (selected.standardSqrtSlabRhoCells heightIndex.1).card + 1
  card_retention :
    (selected.standardSqrtSlabRhoCells heightIndex.1).card ≤
      logarithmicCost * cells.card

theorem PureWZ2AnchoredSourceRelativeFineSelection.preBinRhoHeightRegularization
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
    (heightIndex : {heightIndex // heightIndex ∈
      selected.standardSqrtSlabIndices})
    (hsqrt : sqrtRequested.1 = Real.sqrt rhoRequested.1) :
    Nonempty
      (PureWZ2AnchoredPreBinRhoHeightRegularizedData selected heightIndex) := by
  let slabCells := selected.standardSqrtSlabRhoCells heightIndex.1
  rcases commonBin_rhoHeightUniformization slabCells
      (selected.standardSqrtSlabRhoCells_nonempty heightIndex.2) with
    ⟨uniform⟩
  have hcellsSelected : uniform.cells ⊆ selected.selectedCells :=
    uniform.cells_subset.trans
      (selected.standardSqrtSlabRhoCells_subset heightIndex.1)
  rcases selected.restrictCells uniform.cells hcellsSelected with
    ⟨sourcePullback⟩
  exact ⟨{
    sqrtRequested_eq := hsqrt
    uniform := uniform
    cells := uniform.cells
    cells_eq := rfl
    cells_subset_standard := uniform.cells_subset
    cells_subset_selected := hcellsSelected
    cells_nonempty := uniform.cells_nonempty
    sourcePullback := sourcePullback
    source_volume := sourcePullback.volume_eq
    source_mass := sourcePullback.mass_eq
    logarithmicCost := uniform.logarithmicCost
    logarithmicCost_eq := by
      simpa only [slabCells] using uniform.logarithmicCost_eq
    card_retention := by
      simpa only [slabCells] using uniform.card_retention
  }⟩

structure PureWZ2AnchoredPreBinRhoHeightFamilyData
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
    (selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine) where
  sqrtRequested_eq :
    sqrtRequested.1 = Real.sqrt rhoRequested.1
  blockData : ∀ heightIndex :
      {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices},
    PureWZ2AnchoredPreBinRhoHeightRegularizedData selected heightIndex

theorem PureWZ2AnchoredSourceRelativeFineSelection.preBinRhoHeightFamily
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
    (hsqrt : sqrtRequested.1 = Real.sqrt rhoRequested.1) :
    Nonempty (PureWZ2AnchoredPreBinRhoHeightFamilyData selected) := by
  exact ⟨{
    sqrtRequested_eq := hsqrt
    blockData := fun heightIndex =>
      Classical.choice
        (selected.preBinRhoHeightRegularization heightIndex hsqrt)
  }⟩

structure PureWZ2HierarchyReentrantAnchoredPreBinInput
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho grainLoss
      outputEta selectedLoss sourceLoss seedLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    {firstOverlay : PureWZ2HierarchyReentrantFirstOverlayReceipt
      (current := current) kernelOutput}
    {anchored :
      PureWZ2HierarchyReentrantCurrentCoarseAnchoredReceipt firstOverlay}
    {selectedNormalizationExponent secondSeedLogExponent firstLogExponent : ℕ}
    {selection : PureWZ2Node05AnchoredSynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (sourceLoss := sourceLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      firstOverlay.ambient anchored.toAnchoredCoarseSource}
    {sqrtRequested : WZ2PaperRequestedScale kernelOutput.requested.1}
    {stage : PureWZ2Node05AnchoredSynchronizedTwoCallStage
      (seedLoss := seedLoss)
      (outputLoss := lossSchedule.ownerSchedule.stickyLoss)
      (firstLogExponent := firstLogExponent)
      (secondSeedLogExponent := secondSeedLogExponent)
      firstOverlay.ambient anchored.toAnchoredCoarseSource selection
      sqrtRequested}
    {receipt : PureWZ2HierarchyReentrantAnchoredTwoScaleReceipt
      (grainLoss := grainLoss) anchored selection sqrtRequested stage}
    (entry : PureWZ2HierarchyReentrantAnchoredPostOwnerInput receipt) where
  family :
    PureWZ2AnchoredPreBinRhoHeightFamilyData receipt.sourceRelative

theorem PureWZ2HierarchyReentrantAnchoredPostOwnerInput.preBin_nonempty
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho grainLoss
      outputEta selectedLoss sourceLoss seedLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    {firstOverlay : PureWZ2HierarchyReentrantFirstOverlayReceipt
      (current := current) kernelOutput}
    {anchored :
      PureWZ2HierarchyReentrantCurrentCoarseAnchoredReceipt firstOverlay}
    {selectedNormalizationExponent secondSeedLogExponent firstLogExponent : ℕ}
    {selection : PureWZ2Node05AnchoredSynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (sourceLoss := sourceLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      firstOverlay.ambient anchored.toAnchoredCoarseSource}
    {sqrtRequested : WZ2PaperRequestedScale kernelOutput.requested.1}
    {stage : PureWZ2Node05AnchoredSynchronizedTwoCallStage
      (seedLoss := seedLoss)
      (outputLoss := lossSchedule.ownerSchedule.stickyLoss)
      (firstLogExponent := firstLogExponent)
      (secondSeedLogExponent := secondSeedLogExponent)
      firstOverlay.ambient anchored.toAnchoredCoarseSource selection
      sqrtRequested}
    {receipt : PureWZ2HierarchyReentrantAnchoredTwoScaleReceipt
      (grainLoss := grainLoss) anchored selection sqrtRequested stage}
    (entry : PureWZ2HierarchyReentrantAnchoredPostOwnerInput receipt) :
    Nonempty (PureWZ2HierarchyReentrantAnchoredPreBinInput entry) := by
  rcases receipt.sourceRelative.preBinRhoHeightFamily
      receipt.sqrtRequested_eq with ⟨family⟩
  exact ⟨{ family := family }⟩

end Kakeya.Assouad

end
