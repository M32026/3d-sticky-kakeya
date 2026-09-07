import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalRichTrapezoid

/-!
# Height-only lift from the auxiliary rich graph to the source family

The Alternative-A graph is used only to select rich heights.  The output
shading below returns to the original `delta` family: it keeps every complete
source `delta`-cell whose whole height span is covered by the rich-height
intervals.  No fixed-line, y-residue, or coarse spatial carrier is retained
in the definition of the final shading.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2SourceAlternativeAHeightLift
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss theoremEta : ℝ}
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
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graphParents : PureWZ2SourceHorizontalGraphParentData prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2SourceAlternativeARichCells
      (graphParents := graphParents) rich}
    {richShading : PureWZ2SourceAlternativeARichShading richCells}
    (richTrapezoid :
      PureWZ2SourceAlternativeARichTrapezoid richShading) where
  heightCells : Finset (ℤ × ℤ × ℤ) :=
    (wz1PaperActiveCells source.shading source.extremal.delta_pos).filter
      fun cell => ∀ point ∈ wz1PaperGridCube delta cell,
        point 2 ∈ richTrapezoid.trapezoid.core ∧
          ∃ heightIndex ∈ rich.heightIndices,
            |point 2 - wz1Lemma23SnappedBaseHeight
              prep.graphScale heightIndex| ≤ prep.graphScale
  heightCells_eq : heightCells =
    (wz1PaperActiveCells source.shading source.extremal.delta_pos).filter
      fun cell => ∀ point ∈ wz1PaperGridCube delta cell,
        point 2 ∈ richTrapezoid.trapezoid.core ∧
          ∃ heightIndex ∈ rich.heightIndices,
            |point 2 - wz1Lemma23SnappedBaseHeight
              prep.graphScale heightIndex| ≤ prep.graphScale
  region : Set Point3 :=
    ⋃ cell ∈ heightCells, wz1PaperGridCube delta cell
  region_eq : region =
    ⋃ cell ∈ heightCells, wz1PaperGridCube delta cell
  region_measurable : MeasurableSet region
  shading : WZ1PaperTubeShading source.family
  carrier_eq : ∀ index, shading.carrier index =
    source.shading.carrier index ∩ region
  subshading : PureWZ2PaperIsSubshading shading source.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  rich_subshading :
    PureWZ2PaperIsSubshading richShading.shading shading
  volume_lower :
    MeasureTheory.volume richShading.shading.union ≤
      MeasureTheory.volume shading.union
  mass_lower : richShading.shading.mass ≤ shading.mass
  active_height_coverage :
    ∀ z, horizontalSlice shading.union z ≠ ∅ →
      z ∈ richTrapezoid.trapezoid.core
  slope_approximation :
    ∀ z, horizontalSlice shading.union z ≠ ∅ →
      |source.globalGrains.slope z -
        richTrapezoid.trapezoid.affine z| ≤ richTrapezoid.scale

theorem PureWZ2SourceAlternativeARichTrapezoid.toHeightLift
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss theoremEta : ℝ}
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
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graphParents : PureWZ2SourceHorizontalGraphParentData prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2SourceAlternativeARichCells
      (graphParents := graphParents) rich}
    {richShading : PureWZ2SourceAlternativeARichShading richCells}
    (richTrapezoid :
      PureWZ2SourceAlternativeARichTrapezoid richShading) :
    Nonempty (PureWZ2SourceAlternativeAHeightLift richTrapezoid) := by
  let heightCells :=
    (wz1PaperActiveCells source.shading source.extremal.delta_pos).filter
      fun cell => ∀ point ∈ wz1PaperGridCube delta cell,
        point 2 ∈ richTrapezoid.trapezoid.core ∧
          ∃ heightIndex ∈ rich.heightIndices,
            |point 2 - wz1Lemma23SnappedBaseHeight
              prep.graphScale heightIndex| ≤ prep.graphScale
  let region : Set Point3 :=
    ⋃ cell ∈ heightCells, wz1PaperGridCube delta cell
  have hregionMeasurable : MeasurableSet region :=
    MeasurableSet.biUnion heightCells.finite_toSet.countable
      (fun cell _ => wz1PaperGridCube_measurable cell)
  let shading : WZ1PaperTubeShading source.family :=
    { carrier := fun index => source.shading.carrier index ∩ region
      measurable_carrier := fun index =>
        (source.shading.measurable_carrier index).inter hregionMeasurable
      subset_body := fun index => Set.inter_subset_left.trans
        (source.shading.subset_body index) }
  have hsub : PureWZ2PaperIsSubshading shading source.shading := by
    intro index point hpoint
    exact hpoint.1
  have hwhole : WZ1PaperIsCubicalShading shading := by
    intro index point hpoint other hother
    have hsourceOther := source.cubical index point hpoint.1 hother
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨selectedCell, hselectedCell, hpointSelected⟩
    have hselectedIndex :
        wz1PaperGridIndex delta point = selectedCell :=
      (mem_wz1PaperGridCube delta selectedCell point).mp hpointSelected
    have hotherSelected :
        other ∈ wz1PaperGridCube delta selectedCell := by
      apply (mem_wz1PaperGridCube delta selectedCell other).mpr
      exact ((mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) other).mp hother).trans hselectedIndex
    exact ⟨hsourceOther, Set.mem_iUnion₂.mpr
      ⟨selectedCell, hselectedCell, hotherSelected⟩⟩
  have hrichSub :
      PureWZ2PaperIsSubshading richShading.shading shading := by
    intro index point hpoint
    have hsource : point ∈ source.shading.carrier index :=
      richShading.subshading index hpoint
    have hsourceUnion : point ∈ source.shading.union := ⟨index, hsource⟩
    rw [source.cubical.union_eq_activeCells source.extremal.delta_pos] at hsourceUnion
    rcases Set.mem_iUnion₂.mp hsourceUnion with
      ⟨cell, hcellActive, hpointCell⟩
    have hcellHeight : ∀ other ∈ wz1PaperGridCube delta cell,
        other 2 ∈ richTrapezoid.trapezoid.core ∧
          ∃ heightIndex ∈ rich.heightIndices,
            |other 2 - wz1Lemma23SnappedBaseHeight
              prep.graphScale heightIndex| ≤ prep.graphScale := by
      intro other hotherCell
      have hcellEq : cell = wz1PaperGridIndex delta point := by
        exact ((mem_wz1PaperGridCube delta cell point).mp hpointCell).symm
      have hotherSourceCell :
          other ∈ wz1PaperGridCube delta
            (wz1PaperGridIndex delta point) := by
        rwa [← hcellEq]
      have hotherRich : other ∈ richShading.shading.carrier index :=
        richShading.whole_cells index point hpoint hotherSourceCell
      have hslice : horizontalSlice richShading.shading.union (other 2) ≠ ∅ := by
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨other, ⟨⟨index, hotherRich⟩, rfl⟩⟩
      exact ⟨richTrapezoid.active_height_coverage (other 2) hslice,
        richTrapezoid.rich_height_coverage (other 2) hslice⟩
    have hcellSelected : cell ∈ heightCells := by
      exact Finset.mem_filter.mpr ⟨hcellActive, hcellHeight⟩
    exact ⟨hsource, Set.mem_iUnion₂.mpr
      ⟨cell, hcellSelected, hpointCell⟩⟩
  have hvolume :
      MeasureTheory.volume richShading.shading.union ≤
        MeasureTheory.volume shading.union :=
    measure_mono hrichSub.union_subset
  have hmass : richShading.shading.mass ≤ shading.mass := by
    apply Finset.sum_le_sum
    intro index _
    exact measure_mono (hrichSub index)
  have hselectedPoint : ∀ point ∈ shading.union,
      point 2 ∈ richTrapezoid.trapezoid.core ∧
        ∃ heightIndex ∈ rich.heightIndices,
          |point 2 - wz1Lemma23SnappedBaseHeight
            prep.graphScale heightIndex| ≤ prep.graphScale := by
    intro point hpoint
    rcases hpoint with ⟨index, _hsource, hregion⟩
    rcases Set.mem_iUnion₂.mp hregion with
      ⟨cell, hcell, hpointCell⟩
    have hcondition := (Finset.mem_filter.mp hcell).2
    exact hcondition point hpointCell
  have hcoverage :
      ∀ z, horizontalSlice shading.union z ≠ ∅ →
        z ∈ richTrapezoid.trapezoid.core := by
    intro z hslice
    rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint, hheight⟩
    have hselected := hselectedPoint point hpoint
    rw [hheight] at hselected
    exact hselected.1
  have hslope :
      ∀ z, horizontalSlice shading.union z ≠ ∅ →
        |source.globalGrains.slope z -
          richTrapezoid.trapezoid.affine z| ≤ richTrapezoid.scale := by
    intro z hslice
    rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint, hheight⟩
    have hselected := (hselectedPoint point hpoint).2
    rw [hheight] at hselected
    rcases hselected with ⟨heightIndex, hheightIndex, hclose⟩
    have hsourcePoint : point ∈ source.shading.union :=
      hsub.union_subset hpoint
    have hbox := shading_union_subset_axisBox hsourcePoint
    have hz : z ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [← hheight]
      have habs : |point 2| ≤ 1 := by
        convert hbox.2.2 using 1 <;> norm_num
      exact abs_le.mp habs
    exact richTrapezoid.rich_height_approximation
      heightIndex hheightIndex z hz hclose
  exact ⟨{
    heightCells := heightCells
    heightCells_eq := rfl
    region := region
    region_eq := rfl
    region_measurable := hregionMeasurable
    shading := shading
    carrier_eq := by intro index; rfl
    subshading := hsub
    whole_cells := hwhole
    rich_subshading := hrichSub
    volume_lower := hvolume
    mass_lower := hmass
    active_height_coverage := hcoverage
    slope_approximation := hslope
  }⟩

end Kakeya.Assouad
