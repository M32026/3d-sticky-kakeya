import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6FixedScaleOutput
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSubfamilyZeroExtensionStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition5SpatialCover
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment

/-!
# Restrict the Node-6 fixed-scale output to selected coarse cells

The restricted shading is indexed by the original ambient family: first extend
the selected fine shading by zero, then intersect every ambient carrier with
the union of the chosen balanced coarse cells.  Its indexed weight is the
actual sum of the restricted carrier masses over ambient sources; no uniform
incidence-mass assertion is made.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Zero extension preserves point multiplicity.  This local copy keeps the
minimal fixed-scale path independent of the historical sticky adapter. -/
theorem WZ2PaperSubfamilyZeroExtensionData.node6_pointMultiplicity_eq
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {selected : Kakeya.Streamlined.TubeSubfamily family}
    {refined : WZ1PaperTubeShading selected.family}
    (zero : WZ2PaperSubfamilyZeroExtensionData selected refined)
    (point : Point3) :
    zero.ambientShading.pointMultiplicity point =
      refined.pointMultiplicity point := by
  classical
  let selectedAt : Finset (Fin selected.family.card) :=
    Finset.univ.filter fun index => point ∈ refined.carrier index
  let ambientAt : Finset (Fin family.card) :=
    Finset.univ.filter fun index =>
      point ∈ zero.ambientShading.carrier index
  have himage : selectedAt.image selected.embedding = ambientAt := by
    ext ambient
    constructor
    · intro hambient
      rcases Finset.mem_image.mp hambient with ⟨index, hindex, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [zero.carrier_embedding index]
        exact (Finset.mem_filter.mp hindex).2⟩
    · intro hambient
      have hpoint := (Finset.mem_filter.mp hambient).2
      rcases zero.carrier_support ambient point hpoint with
        ⟨index, heq, hrefined⟩
      exact Finset.mem_image.mpr ⟨index,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrefined⟩, heq⟩
  change ambientAt.card = selectedAt.card
  rw [← himage, Finset.card_image_of_injective _
    selected.embedding.injective]

structure PureWZ2Node6FixedCellRestrictionData
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (zeroExtension :
      WZ2PaperSubfamilyZeroExtensionData data.selected data.refined)
    (selectedCells : Finset (ℤ × ℤ × ℤ)) where
  selectedCells_subset : selectedCells ⊆ data.balanced.activeCells
  selectedRegion : Set Point3
  selectedRegion_eq : selectedRegion =
    ⋃ cell ∈ selectedCells, wz1PaperGridCube rho.1 cell
  selectedRegion_measurable : MeasurableSet selectedRegion
  shading : WZ1PaperTubeShading source
  carrier_eq : ∀ index, shading.carrier index =
    zeroExtension.ambientShading.carrier index ∩ selectedRegion
  subshading_zero : ∀ index, shading.carrier index ⊆
    zeroExtension.ambientShading.carrier index
  subshading : ∀ index, shading.carrier index ⊆
    sourceShading.carrier index
  cubical : WZ1PaperIsCubicalShading shading
  union_eq : shading.union =
    zeroExtension.ambientShading.union ∩ selectedRegion
  indexedWeight : (ℤ × ℤ × ℤ) → ENNReal
  indexedWeight_eq : ∀ cell, indexedWeight cell =
    ∑ index : Fin source.card,
      volume (shading.carrier index ∩ wz1PaperGridCube rho.1 cell)
  cell_spatial_mass : ∀ cell ∈ selectedCells,
    volume (shading.union ∩ wz1PaperGridCube rho.1 cell) =
      data.balanced.cellMass
  mass_eq_sum_indexedWeight : shading.mass =
    ∑ cell ∈ selectedCells, indexedWeight cell
  union_volume_eq : volume shading.union =
    (selectedCells.card : ENNReal) * data.balanced.cellMass

/-- The actual ambient-source mass meeting one coarse cell. -/
def ambientIndexedCellWeight
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (zeroExtension :
      WZ2PaperSubfamilyZeroExtensionData data.selected data.refined)
    (cell : ℤ × ℤ × ℤ) : ENNReal :=
  ∑ ambient : Fin source.card,
    volume (zeroExtension.ambientShading.carrier ambient ∩
      wz1PaperGridCube rho.1 cell)

/-- Zero extension merely reindexes the selected fine sources, so its honest
ambient weight in any coarse cell is the fixed-scale indexed mass. -/
theorem PureWZ2Node6FixedScaleOutput.ambientIndexedCellWeight_eq_cellIndexedMass
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (zeroExtension :
      WZ2PaperSubfamilyZeroExtensionData data.selected data.refined)
    (cell : ℤ × ℤ × ℤ) :
    ambientIndexedCellWeight data zeroExtension cell =
      data.cellIndexedMass cell := by
  rw [data.cellIndexedMass_eq]
  let supported : Finset (Fin source.card) :=
    Finset.univ.map data.selected.embedding
  calc
    ambientIndexedCellWeight data zeroExtension cell =
        ∑ ambient : Fin source.card,
          volume (zeroExtension.ambientShading.carrier ambient ∩
            wz1PaperGridCube rho.1 cell) := rfl
    _ = ∑ ambient ∈ supported,
          volume (zeroExtension.ambientShading.carrier ambient ∩
            wz1PaperGridCube rho.1 cell) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro ambient _ hnot
      have hempty : zeroExtension.ambientShading.carrier ambient = ∅ := by
        apply Set.not_nonempty_iff_eq_empty.mp
        rintro ⟨point, hpoint⟩
        rcases zeroExtension.carrier_support ambient point hpoint with
          ⟨selectedIndex, heq, _⟩
        exact hnot (Finset.mem_map.mpr
          ⟨selectedIndex, Finset.mem_univ _, heq⟩)
      rw [hempty]
      simp
    _ = ∑ selectedIndex : Fin data.selected.family.card,
          volume (data.refined.carrier selectedIndex ∩
            wz1PaperGridCube rho.1 cell) := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro selectedIndex _
      rw [zeroExtension.carrier_embedding selectedIndex]

namespace PureWZ2Node6FixedCellRestrictionData

/-- On a selected cell, restriction does not change the ambient mass inside
that cell. -/
theorem indexedWeight_eq_ambientIndexedCellWeight
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent}
    {zeroExtension :
      WZ2PaperSubfamilyZeroExtensionData data.selected data.refined}
    {selectedCells : Finset (ℤ × ℤ × ℤ)}
    (restricted : PureWZ2Node6FixedCellRestrictionData
      data zeroExtension selectedCells)
    {cell : ℤ × ℤ × ℤ}
    (hcell : cell ∈ selectedCells) :
    restricted.indexedWeight cell =
      ambientIndexedCellWeight data zeroExtension cell := by
  rw [restricted.indexedWeight_eq]
  apply Finset.sum_congr rfl
  intro ambient _
  congr 1
  rw [restricted.carrier_eq]
  ext point
  constructor
  · rintro ⟨⟨hsource, _⟩, hpointCell⟩
    exact ⟨hsource, hpointCell⟩
  · rintro ⟨hsource, hpointCell⟩
    refine ⟨⟨hsource, ?_⟩, hpointCell⟩
    rw [restricted.selectedRegion_eq]
    exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCell⟩

/-- The restricted shading mass is the sum of the honest ambient-source
weights of the selected cells. -/
theorem shading_mass_eq_sum_ambientIndexedCellWeight
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent}
    {zeroExtension :
      WZ2PaperSubfamilyZeroExtensionData data.selected data.refined}
    {selectedCells : Finset (ℤ × ℤ × ℤ)}
    (restricted : PureWZ2Node6FixedCellRestrictionData
      data zeroExtension selectedCells) :
    restricted.shading.mass =
      ∑ cell ∈ selectedCells,
        ambientIndexedCellWeight data zeroExtension cell := by
  rw [restricted.mass_eq_sum_indexedWeight]
  apply Finset.sum_congr rfl
  intro cell hcell
  exact restricted.indexedWeight_eq_ambientIndexedCellWeight hcell

/-- Restricting to every active balanced cell leaves the zero-extended
ambient shading unchanged. -/
theorem shading_eq_ambientShading
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent}
    {zeroExtension :
      WZ2PaperSubfamilyZeroExtensionData data.selected data.refined}
    (restricted : PureWZ2Node6FixedCellRestrictionData
      data zeroExtension data.balanced.activeCells) :
    restricted.shading = zeroExtension.ambientShading := by
  have hcarrier : restricted.shading.carrier =
      zeroExtension.ambientShading.carrier := by
    funext ambient
    ext point
    rw [restricted.carrier_eq]
    constructor
    · exact fun hpoint => hpoint.1
    · intro hpoint
      refine ⟨hpoint, ?_⟩
      rcases zeroExtension.carrier_support ambient point hpoint with
        ⟨selectedIndex, _heq, hrefined⟩
      rcases data.fine_cell_nested selectedIndex point hrefined with
        ⟨coarseCell, hcoarseCell, hnested⟩
      rw [restricted.selectedRegion_eq]
      exact Set.mem_iUnion₂.mpr ⟨coarseCell, hcoarseCell,
        hnested ((mem_wz1PaperGridCube delta
          (wz1PaperGridIndex delta point) point).mpr rfl)⟩
  have shading_ext :
      ∀ first second : WZ1PaperTubeShading source,
        first.carrier = second.carrier → first = second := by
    intro first second h
    cases first
    cases second
    cases h
    rfl
  exact shading_ext restricted.shading zeroExtension.ambientShading hcarrier

/-- The mass of the full zero extension is the sum of its honest ambient
weights over all active balanced coarse cells. -/
theorem ambientShading_mass_eq_sum_ambientIndexedCellWeight
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent}
    {zeroExtension :
      WZ2PaperSubfamilyZeroExtensionData data.selected data.refined}
    (restricted : PureWZ2Node6FixedCellRestrictionData
      data zeroExtension data.balanced.activeCells) :
    zeroExtension.ambientShading.mass =
      ∑ cell ∈ data.balanced.activeCells,
        ambientIndexedCellWeight data zeroExtension cell := by
  rw [← restricted.shading_eq_ambientShading]
  exact restricted.shading_mass_eq_sum_ambientIndexedCellWeight

/-- A restriction to selected coarse cells is covered by eight radius-scale
balls per selected cell. -/
theorem cell_cover
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent}
    {zeroExtension :
      WZ2PaperSubfamilyZeroExtensionData data.selected data.refined}
    {selectedCells : Finset (ℤ × ℤ × ℤ)}
    (restricted : PureWZ2Node6FixedCellRestrictionData
      data zeroExtension selectedCells) :
    CanCoverByBalls restricted.shading.union rho.1
      (8 * (selectedCells.card : ENNReal)) := by
  have hrho : 0 < rho.1 := data.delta_pos.trans_le rho.2.1
  have hcellCover : ∀ cell ∈ selectedCells,
      ∃ centers : Finset Point3, centers.card ≤ 8 ∧
        ∀ point ∈ wz1PaperGridCube rho.1 cell,
          ∃ center ∈ centers, point ∈ Metric.closedBall center rho.1 := by
    intro cell _
    exact spatialCover_eightBalls hrho
      (Set.nonempty_iff_ne_empty.mpr (by
        intro hempty
        have hpositive := wz1PaperGridCube_volume_pos hrho cell
        rw [hempty] at hpositive
        simp at hpositive))
      (by
        intro first hfirst second hsecond
        exact (wz1_paper_grid_cube_diameter_lt_two_rho
          hrho hfirst hsecond).le)
  choose centers hcentersCard hcentersCover using hcellCover
  let allCenters := selectedCells.biUnion fun cell =>
    if h : cell ∈ selectedCells then centers cell h else ∅
  have hallCard : allCenters.card ≤ 8 * selectedCells.card := by
    calc
      allCenters.card ≤ ∑ cell ∈ selectedCells,
          (if h : cell ∈ selectedCells then centers cell h else ∅).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _cell ∈ selectedCells, 8 := by
        apply Finset.sum_le_sum
        intro cell hcell
        simp only [hcell, dite_true]
        exact hcentersCard cell hcell
      _ = 8 * selectedCells.card := by
        simp [Finset.sum_const, Nat.mul_comm]
  refine ⟨allCenters, by exact_mod_cast hallCard, ?_⟩
  intro point hpoint
  rw [restricted.union_eq, restricted.selectedRegion_eq] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint.2 with
    ⟨cell, hcell, hpointCell⟩
  rcases hcentersCover cell hcell point hpointCell with
    ⟨center, hcenter, hball⟩
  exact ⟨center, Finset.mem_biUnion.mpr ⟨cell, hcell, by
    simpa [hcell] using hcenter⟩, hball⟩

/-- A whole-cell restriction to one height layer lies in one slab. -/
theorem in_height_slab
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent}
    {zeroExtension :
      WZ2PaperSubfamilyZeroExtensionData data.selected data.refined}
    {selectedCells : Finset (ℤ × ℤ × ℤ)}
    (restricted : PureWZ2Node6FixedCellRestrictionData
      data zeroExtension selectedCells)
    (height : ℤ)
    (hheight : ∀ cell ∈ selectedCells, cell.2.2 = height) :
    ∀ index, restricted.shading.carrier index ⊆
      horizontalSlab ((height : ℝ) * rho.1)
        (((height : ℝ) + 1) * rho.1) := by
  have hrho : 0 < rho.1 := data.delta_pos.trans_le rho.2.1
  intro index point hpoint
  rw [restricted.carrier_eq] at hpoint
  rw [restricted.selectedRegion_eq] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint.2 with
    ⟨cell, hcell, hpointCell⟩
  rw [wz1PaperGridCube_eq_Ico hrho] at hpointCell
  rcases hpointCell with
    ⟨_hxLo, _hxHi, _hyLo, _hyHi, hzLo, hzHi⟩
  change (height : ℝ) * rho.1 ≤ point 2 ∧
    point 2 ≤ ((height : ℝ) + 1) * rho.1
  simpa [hheight cell hcell] using And.intro hzLo hzHi.le

end PureWZ2Node6FixedCellRestrictionData

namespace PureWZ2Node6FixedScaleOutput

/-- Restrict a fixed-scale Node-6 shading to any selected balanced coarse
cells, retaining an honest ambient-source mass ledger. -/
theorem restrictCellsWithZero
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (zeroExtension :
      WZ2PaperSubfamilyZeroExtensionData data.selected data.refined)
    (selectedCells : Finset (ℤ × ℤ × ℤ))
    (hselected : selectedCells ⊆ data.balanced.activeCells) :
    Nonempty (PureWZ2Node6FixedCellRestrictionData
      data zeroExtension selectedCells) := by
  let selectedRegion : Set Point3 :=
    ⋃ cell ∈ selectedCells, wz1PaperGridCube rho.1 cell
  have hregionMeasurable : MeasurableSet selectedRegion :=
    MeasurableSet.biUnion selectedCells.finite_toSet.countable
      (fun cell _ => wz1PaperGridCube_measurable cell)
  let shading : WZ1PaperTubeShading source :=
    { carrier := fun index =>
        zeroExtension.ambientShading.carrier index ∩ selectedRegion
      measurable_carrier := fun index =>
        (zeroExtension.ambientShading.measurable_carrier index).inter
          hregionMeasurable
      subset_body := fun index =>
        Set.inter_subset_left.trans
          (zeroExtension.ambientShading.subset_body index) }
  have hunion : shading.union =
      zeroExtension.ambientShading.union ∩ selectedRegion := by
    ext point
    constructor
    · rintro ⟨index, hsource, hregion⟩
      exact ⟨⟨index, hsource⟩, hregion⟩
    · rintro ⟨⟨index, hsource⟩, hregion⟩
      exact ⟨index, hsource, hregion⟩
  have hsub : ∀ index, shading.carrier index ⊆
      sourceShading.carrier index := by
    intro index point hpoint
    rcases zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, heq, hrefined⟩
    rw [← heq]
    exact data.subshading selectedIndex hrefined
  have hcubical : WZ1PaperIsCubicalShading shading := by
    intro index point hpoint
    have hambient :
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          zeroExtension.ambientShading.carrier index :=
      zeroExtension.cubical data.refined_cubical index point hpoint.1
    rcases zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, _heq, hrefined⟩
    rcases data.fine_cell_nested selectedIndex point hrefined with
      ⟨coarseCell, hcoarse, hnested⟩
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨selectedCell, hselectedCell, hpointSelected⟩
    have hpointCoarse : point ∈ wz1PaperGridCube rho.1 coarseCell :=
      hnested ((mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) point).mpr rfl)
    have hcellEq : coarseCell = selectedCell :=
      ((mem_wz1PaperGridCube rho.1 coarseCell point).mp hpointCoarse).symm.trans
        ((mem_wz1PaperGridCube rho.1 selectedCell point).mp hpointSelected)
    intro other hother
    refine ⟨hambient hother, ?_⟩
    exact Set.mem_iUnion₂.mpr ⟨selectedCell, hselectedCell, by
      rw [← hcellEq]
      exact hnested hother⟩
  have hcellSpatial : ∀ cell ∈ selectedCells,
      volume (shading.union ∩ wz1PaperGridCube rho.1 cell) =
        data.balanced.cellMass := by
    intro cell hcell
    rw [hunion, zeroExtension.union_eq]
    have hset :
        (data.refined.union ∩ selectedRegion) ∩
            wz1PaperGridCube rho.1 cell =
          data.refined.union ∩ wz1PaperGridCube rho.1 cell := by
      ext point
      constructor
      · rintro ⟨⟨hrefined, _⟩, hpointCell⟩
        exact ⟨hrefined, hpointCell⟩
      · rintro ⟨hrefined, hpointCell⟩
        exact ⟨⟨hrefined, Set.mem_iUnion₂.mpr
          ⟨cell, hcell, hpointCell⟩⟩, hpointCell⟩
    rw [hset]
    exact data.balanced.fine_cell_mass cell (hselected hcell)
  let indexedWeight : (ℤ × ℤ × ℤ) → ENNReal := fun cell =>
    ∑ index : Fin source.card,
      volume (shading.carrier index ∩ wz1PaperGridCube rho.1 cell)
  have hmass : shading.mass =
      ∑ cell ∈ selectedCells, indexedWeight cell := by
    have hpartition : ∀ index : Fin source.card,
        shading.carrier index = ⋃ cell ∈ selectedCells,
          shading.carrier index ∩ wz1PaperGridCube rho.1 cell := by
      intro index
      ext point
      constructor
      · intro hpoint
        rcases Set.mem_iUnion₂.mp hpoint.2 with
          ⟨cell, hcell, hpointCell⟩
        exact Set.mem_iUnion₂.mpr
          ⟨cell, hcell, hpoint, hpointCell⟩
      · intro hpoint
        rcases Set.mem_iUnion₂.mp hpoint with
          ⟨_cell, _hcell, hsource, _⟩
        exact hsource
    have hcarrierVolume : ∀ index : Fin source.card,
        volume (shading.carrier index) = ∑ cell ∈ selectedCells,
          volume (shading.carrier index ∩
            wz1PaperGridCube rho.1 cell) := by
      intro index
      calc
        volume (shading.carrier index) =
            volume (⋃ cell ∈ selectedCells,
              shading.carrier index ∩ wz1PaperGridCube rho.1 cell) :=
          congrArg volume (hpartition index)
        _ = ∑ cell ∈ selectedCells,
            volume (shading.carrier index ∩
              wz1PaperGridCube rho.1 cell) := by
          apply MeasureTheory.measure_biUnion_finset
          · intro first _ second _ hne
            exact (wz1PaperGridCube_disjoint hne).mono
              Set.inter_subset_right Set.inter_subset_right
          · intro cell _
            exact (shading.measurable_carrier index).inter
              (wz1PaperGridCube_measurable cell)
    calc
      shading.mass = ∑ index : Fin source.card,
          ∑ cell ∈ selectedCells,
            volume (shading.carrier index ∩
              wz1PaperGridCube rho.1 cell) := by
        apply Finset.sum_congr rfl
        intro index _
        exact hcarrierVolume index
      _ = ∑ cell ∈ selectedCells,
          ∑ index : Fin source.card,
            volume (shading.carrier index ∩
              wz1PaperGridCube rho.1 cell) := by
        rw [Finset.sum_comm]
      _ = ∑ cell ∈ selectedCells, indexedWeight cell := rfl
  have hunionVolume : volume shading.union =
      (selectedCells.card : ENNReal) * data.balanced.cellMass := by
    have hpartition : shading.union = ⋃ cell ∈ selectedCells,
        shading.union ∩ wz1PaperGridCube rho.1 cell := by
      ext point
      constructor
      · intro hpoint
        rw [hunion] at hpoint
        rcases Set.mem_iUnion₂.mp hpoint.2 with
          ⟨cell, hcell, hpointCell⟩
        exact Set.mem_iUnion₂.mpr
          ⟨cell, hcell, by rw [hunion]; exact hpoint, hpointCell⟩
      · intro hpoint
        rcases Set.mem_iUnion₂.mp hpoint with
          ⟨_cell, _hcell, hsource, _⟩
        exact hsource
    calc
      volume shading.union = volume (⋃ cell ∈ selectedCells,
          shading.union ∩ wz1PaperGridCube rho.1 cell) :=
        congrArg volume hpartition
      _ = ∑ cell ∈ selectedCells,
          volume (shading.union ∩ wz1PaperGridCube rho.1 cell) := by
        apply MeasureTheory.measure_biUnion_finset
        · intro first _ second _ hne
          exact (wz1PaperGridCube_disjoint hne).mono
            Set.inter_subset_right Set.inter_subset_right
        · intro cell _
          exact (measurableSet_shading_union shading).inter
            (wz1PaperGridCube_measurable cell)
      _ = ∑ _cell ∈ selectedCells, data.balanced.cellMass := by
        apply Finset.sum_congr rfl
        exact hcellSpatial
      _ = (selectedCells.card : ENNReal) *
          data.balanced.cellMass := by
        simp [Finset.sum_const]
  exact ⟨{
    selectedCells_subset := hselected
    selectedRegion := selectedRegion
    selectedRegion_eq := rfl
    selectedRegion_measurable := hregionMeasurable
    shading := shading
    carrier_eq := fun _ => rfl
    subshading_zero := fun _ => Set.inter_subset_left
    subshading := hsub
    cubical := hcubical
    union_eq := hunion
    indexedWeight := indexedWeight
    indexedWeight_eq := fun _ => rfl
    cell_spatial_mass := hcellSpatial
    mass_eq_sum_indexedWeight := hmass
    union_volume_eq := hunionVolume
  }⟩

/-- The full refined mass is the sum of its actual indexed masses over all
active balanced coarse cells. -/
theorem refined_mass_eq_sum_cellIndexedMass
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (zeroExtension :
      WZ2PaperSubfamilyZeroExtensionData data.selected data.refined) :
    data.refined.mass =
      ∑ cell ∈ data.balanced.activeCells, data.cellIndexedMass cell := by
  rcases data.restrictCellsWithZero zeroExtension
      data.balanced.activeCells (fun _ hcell => hcell) with
    ⟨restricted⟩
  calc
    data.refined.mass = zeroExtension.ambientShading.mass :=
      zeroExtension.mass_eq.symm
    _ = ∑ cell ∈ data.balanced.activeCells,
          ambientIndexedCellWeight data zeroExtension cell :=
      restricted.ambientShading_mass_eq_sum_ambientIndexedCellWeight
    _ = ∑ cell ∈ data.balanced.activeCells,
          data.cellIndexedMass cell := by
      apply Finset.sum_congr rfl
      intro cell _
      exact data.ambientIndexedCellWeight_eq_cellIndexedMass
        zeroExtension cell

end PureWZ2Node6FixedScaleOutput

end Kakeya.Assouad

end
