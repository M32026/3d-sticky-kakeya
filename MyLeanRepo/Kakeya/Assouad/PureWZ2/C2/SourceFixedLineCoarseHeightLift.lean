import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseRichTrapezoid

/-!
# Height-only source lift from a fixed-bin coarse rich graph

The chosen global bin and its genuine first-sticky coarse carrier are used
only to produce the rich height indices and the affine trapezoid.  The final
shading returns to the original `delta` family and retains complete source
cells selected solely by those heights.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2SourceFixedBinCoarseHeightLift
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
      (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData
      graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedBinCoarseReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2SourceFixedBinCoarseRichCells
      (graphParents := graphParents) rich}
    {richShading : PureWZ2SourceFixedBinCoarseRichShading richCells}
    (richTrapezoid :
      PureWZ2SourceFixedBinCoarseRichTrapezoid richShading) where
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
  active_height_coverage :
    ∀ z, horizontalSlice shading.union z ≠ ∅ →
      z ∈ richTrapezoid.trapezoid.core
  slope_approximation :
    ∀ z, horizontalSlice shading.union z ≠ ∅ →
      |source.globalGrains.slope z -
        richTrapezoid.trapezoid.affine z| ≤ richTrapezoid.scale

abbrev PureWZ2SourceFixedLineCoarseHeightLift
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData
      carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedLineCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedLineCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalNormalFirstCertificate
      (eta := eta) carriers.fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedLineCoarsePreparedGraphData
      graphParents normalFirst}
    {sharp : PureWZ2SourceFixedLineCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedLineCoarseReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceFixedLineCoarseAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2SourceFixedLineCoarseRichCells
      (graphParents := graphParents) rich}
    {richShading : PureWZ2SourceFixedLineCoarseRichShading richCells}
    (richTrapezoid :
      PureWZ2SourceFixedLineCoarseRichTrapezoid richShading) : Type :=
  PureWZ2SourceFixedBinCoarseHeightLift richTrapezoid

theorem PureWZ2SourceFixedBinCoarseRichTrapezoid.toHeightLiftFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
      (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData
      graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedBinCoarseReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2SourceFixedBinCoarseRichCells
      (graphParents := graphParents) rich}
    {richShading : PureWZ2SourceFixedBinCoarseRichShading richCells}
    (richTrapezoid :
      PureWZ2SourceFixedBinCoarseRichTrapezoid richShading) :
    Nonempty (PureWZ2SourceFixedBinCoarseHeightLift richTrapezoid) := by
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
  have hselectedPoint : ∀ point ∈ shading.union,
      point 2 ∈ richTrapezoid.trapezoid.core ∧
        ∃ heightIndex ∈ rich.heightIndices,
          |point 2 - wz1Lemma23SnappedBaseHeight
            prep.graphScale heightIndex| ≤ prep.graphScale := by
    intro point hpoint
    rcases hpoint with ⟨_index, _hsource, hregion⟩
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
    active_height_coverage := hcoverage
    slope_approximation := hslope
  }⟩

/-- The exact pullback of the coarse `Z_lin` region is contained tube by tube
in the larger source height lift.  This keeps the old exact-pullback route as
a certified lower subshading of the paper-faithful height-only route. -/
theorem PureWZ2SourceFixedBinCoarseHeightLift.sourcePullback_subshading
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
      (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData
      graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedBinCoarseReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2SourceFixedBinCoarseRichCells
      (graphParents := graphParents) rich}
    {richShading : PureWZ2SourceFixedBinCoarseRichShading richCells}
    {richTrapezoid : PureWZ2SourceFixedBinCoarseRichTrapezoid richShading}
    (heightLift : PureWZ2SourceFixedBinCoarseHeightLift richTrapezoid)
    (sourcePullback : PureWZ2SelectedCoarseRegionSourcePullbackData
      richShading.shading) :
    PureWZ2PaperIsSubshading sourcePullback.shading heightLift.shading := by
  intro index point hpoint
  have hsource : point ∈ source.shading.carrier index :=
    sourcePullback.subshading index hpoint
  have hpullUnion : point ∈ sourcePullback.shading.union := ⟨index, hpoint⟩
  have hsourceUnion : point ∈ source.shading.union := ⟨index, hsource⟩
  rw [source.cubical.union_eq_activeCells source.extremal.delta_pos]
    at hsourceUnion
  rcases Set.mem_iUnion₂.mp hsourceUnion with
    ⟨cell, hcell, hpointCell⟩
  have hcondition : ∀ other ∈ wz1PaperGridCube delta cell,
      other 2 ∈ richTrapezoid.trapezoid.core ∧
        ∃ heightIndex ∈ rich.heightIndices,
          |other 2 - wz1Lemma23SnappedBaseHeight
            prep.graphScale heightIndex| ≤ prep.graphScale := by
    intro other hother
    have hcellEq : cell = wz1PaperGridIndex delta point :=
      (mem_wz1PaperGridCube delta cell point).mp hpointCell |>.symm
    have hotherCanonical : other ∈
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) := by
      rwa [← hcellEq]
    have hotherPullback : other ∈ sourcePullback.shading.carrier index :=
      sourcePullback.whole_cells index point hpoint hotherCanonical
    have hotherUnion : other ∈ sourcePullback.shading.union :=
      ⟨index, hotherPullback⟩
    have hotherCoarse : other ∈ richShading.shading.union := by
      rw [sourcePullback.union_eq] at hotherUnion
      rw [sourcePullback.selectedRegion_eq_coarse] at hotherUnion
      exact hotherUnion.2
    have hslice : horizontalSlice richShading.shading.union (other 2) ≠ ∅ := by
      apply Set.nonempty_iff_ne_empty.mp
      exact ⟨other, hotherCoarse, rfl⟩
    exact ⟨richTrapezoid.active_height_coverage (other 2) hslice,
      richTrapezoid.rich_height_coverage (other 2) hslice⟩
  have hheightCell : cell ∈ heightLift.heightCells := by
    rw [heightLift.heightCells_eq]
    exact Finset.mem_filter.mpr ⟨hcell, hcondition⟩
  rw [heightLift.carrier_eq]
  refine ⟨hsource, ?_⟩
  rw [heightLift.region_eq]
  exact Set.mem_iUnion₂.mpr ⟨cell, hheightCell, hpointCell⟩

theorem PureWZ2SourceFixedBinCoarseHeightLift.sourcePullback_mass_le
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
      (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData
      graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedBinCoarseReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2SourceFixedBinCoarseRichCells
      (graphParents := graphParents) rich}
    {richShading : PureWZ2SourceFixedBinCoarseRichShading richCells}
    {richTrapezoid : PureWZ2SourceFixedBinCoarseRichTrapezoid richShading}
    (heightLift : PureWZ2SourceFixedBinCoarseHeightLift richTrapezoid)
    (sourcePullback : PureWZ2SelectedCoarseRegionSourcePullbackData
      richShading.shading) :
    sourcePullback.shading.mass ≤ heightLift.shading.mass := by
  apply Finset.sum_le_sum
  intro index _
  exact measure_mono (heightLift.sourcePullback_subshading sourcePullback index)

theorem PureWZ2SourceFixedLineCoarseRichTrapezoid.toHeightLift
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData
      carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedLineCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedLineCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalNormalFirstCertificate
      (eta := eta) carriers.fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedLineCoarsePreparedGraphData
      graphParents normalFirst}
    {sharp : PureWZ2SourceFixedLineCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedLineCoarseReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceFixedLineCoarseAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2SourceFixedLineCoarseRichCells
      (graphParents := graphParents) rich}
    {richShading : PureWZ2SourceFixedLineCoarseRichShading richCells}
    (richTrapezoid :
      PureWZ2SourceFixedLineCoarseRichTrapezoid richShading) :
    Nonempty (PureWZ2SourceFixedLineCoarseHeightLift richTrapezoid) :=
  PureWZ2SourceFixedBinCoarseRichTrapezoid.toHeightLiftFixedBin richTrapezoid

end Kakeya.Assouad

end
