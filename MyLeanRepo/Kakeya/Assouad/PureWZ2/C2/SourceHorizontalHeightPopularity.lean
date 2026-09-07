import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalResidueShading
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SlicePopularity
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization.WeightBinning

/-!
# Source-volume popularity across graph-height layers

This is the missing `Z_popular` step in WZ Lemma 23.  The weights are the
actual three-dimensional union volumes in the half-open graph-height slabs,
not graph-cell cardinalities.  One dyadic band retains a logarithmic share of
the ambient volume and makes all surviving layer volumes comparable.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2SourceHorizontalFixedBinHeightPopularShadow
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue)
    (ambient : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily retained.shading source.extremal.delta_pos))
    (graphScale : ℝ) where
  graphScale_pos : 0 < graphScale
  ambient_union_subset : ambient.union ⊆ retained.shading.union
  bins : ℕ
  bins_eq : bins =
    Nat.log 2
      (2 * (wz1Lemma23BoundedHeightIndices
        graphScale graphScale_pos).card) + 1
  heightIndices : Finset ℤ
  heightIndices_subset :
    heightIndices ⊆
      wz1Lemma23BoundedHeightIndices graphScale graphScale_pos
  heightIndices_nonempty : heightIndices.Nonempty
  layerMass : ENNReal
  layerMass_pos : 0 < layerMass
  layerMass_ne_top : layerMass ≠ ⊤
  layer_volume_band :
    ∀ heightIndex ∈ heightIndices,
      layerMass ≤ volume (ambient.union ∩
          wz1Lemma23HeightSlab graphScale heightIndex) ∧
        volume (ambient.union ∩
          wz1Lemma23HeightSlab graphScale heightIndex) ≤
            2 * layerMass
  heightRegion : Set Point3 :=
    ⋃ heightIndex ∈ heightIndices,
      wz1Lemma23HeightSlab graphScale heightIndex
  heightRegion_eq : heightRegion =
    ⋃ heightIndex ∈ heightIndices,
      wz1Lemma23HeightSlab graphScale heightIndex
  heightRegion_measurable : MeasurableSet heightRegion
  shading : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily retained.shading source.extremal.delta_pos)
  carrier_eq : ∀ index, shading.carrier index =
    ambient.carrier index ∩ heightRegion
  subshading : IsSubshading shading ambient
  union_eq : shading.union = ambient.union ∩ heightRegion
  volume_eq_sum : volume shading.union =
    ∑ heightIndex ∈ heightIndices,
      volume (ambient.union ∩
        wz1Lemma23HeightSlab graphScale heightIndex)
  retained_volume :
    volume ambient.union / 2 ≤ bins * volume shading.union

theorem PureWZ2SourceHorizontalFixedBinResidueShadingData.heightPopularShadowFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue)
    (ambient : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily retained.shading source.extremal.delta_pos))
    (hambient : ambient.union ⊆ retained.shading.union)
    (hvolumePos : 0 < volume ambient.union)
    (graphScale : ℝ) (hgraphScale : 0 < graphScale) :
    Nonempty (PureWZ2SourceHorizontalFixedBinHeightPopularShadow
      retained ambient graphScale) := by
  let allHeights :=
    wz1Lemma23BoundedHeightIndices graphScale hgraphScale
  let indexType := {heightIndex : ℤ // heightIndex ∈ allHeights}
  let weight : indexType → ENNReal := fun heightIndex =>
    volume (ambient.union ∩
      wz1Lemma23HeightSlab graphScale heightIndex.1)
  let total := volume ambient.union
  have hball : ambient.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hretained : point ∈ retained.shading.union := hambient hpoint
    have hsource := retained.subshading.union_subset hretained
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hpartition : ambient.union =
      ⋃ heightIndex ∈ allHeights,
        ambient.union ∩
          wz1Lemma23HeightSlab graphScale heightIndex := by
    apply Set.Subset.antisymm
    · intro point hpoint
      have hslab := wz1Lemma23_shading_covered_by_heightSlabs_two
        ambient hgraphScale hball hpoint
      rcases Set.mem_iUnion₂.mp hslab with
        ⟨heightIndex, hheightIndex, hpointSlab⟩
      exact Set.mem_iUnion₂.mpr
        ⟨heightIndex, hheightIndex, hpoint, hpointSlab⟩
    · intro point hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨_heightIndex, _hheightIndex, hpointAmbient, _hpointSlab⟩
      exact hpointAmbient
  have hdisjoint : (allHeights : Set ℤ).PairwiseDisjoint
      (fun heightIndex => ambient.union ∩
        wz1Lemma23HeightSlab graphScale heightIndex) := by
    intro first _hfirst second _hsecond hne
    exact (wz1Lemma23_heightSlab_disjoint hgraphScale hne).mono
      Set.inter_subset_right Set.inter_subset_right
  have hmeas : ∀ heightIndex ∈ allHeights, MeasurableSet
      (ambient.union ∩
        wz1Lemma23HeightSlab graphScale heightIndex) := by
    intro heightIndex _
    exact (measurableSet_shading_union ambient).inter
      (by
        change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
          wz1Lemma23HeightInterval graphScale heightIndex)
        exact measurableSet_Ico.preimage
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  have htotal : total = ∑ heightIndex : indexType, weight heightIndex := by
    change volume ambient.union =
      ∑ heightIndex : indexType, volume (ambient.union ∩
        wz1Lemma23HeightSlab graphScale heightIndex.1)
    calc
      volume ambient.union = volume (⋃ heightIndex ∈ allHeights,
          ambient.union ∩
            wz1Lemma23HeightSlab graphScale heightIndex) :=
        congrArg volume hpartition
      _ = ∑ heightIndex ∈ allHeights, volume (ambient.union ∩
            wz1Lemma23HeightSlab graphScale heightIndex) :=
        MeasureTheory.measure_biUnion_finset hdisjoint hmeas
      _ = ∑ heightIndex : indexType, volume (ambient.union ∩
            wz1Lemma23HeightSlab graphScale heightIndex.1) := by
        simpa [indexType] using (Finset.sum_attach allHeights
          (fun heightIndex : ℤ => volume (ambient.union ∩
            wz1Lemma23HeightSlab graphScale heightIndex))).symm
  have htotalTop : total ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      Metric.isBounded_closedBall.measure_lt_top.ne
      (measure_mono hball)
  have htotalPos : 0 < total := by simpa [total] using hvolumePos
  rcases ennreal_dyadic_bin weight total htotal htotalTop htotalPos with
    ⟨bins, selected, hbins, hselected, hretained, _haverage,
      layerMass, hlayerMass, hband⟩
  let heightIndices := selected.image Subtype.val
  have hheightInjective : Set.InjOn (Subtype.val : indexType → ℤ) selected :=
    fun _ _ _ _ h => Subtype.ext h
  have hheightSubset : heightIndices ⊆ allHeights := by
    intro heightIndex hheightIndex
    rcases Finset.mem_image.mp hheightIndex with ⟨index, _hindex, rfl⟩
    exact index.property
  let heightRegion : Set Point3 :=
    ⋃ heightIndex ∈ heightIndices,
      wz1Lemma23HeightSlab graphScale heightIndex
  have hheightRegionMeasurable : MeasurableSet heightRegion :=
    MeasurableSet.biUnion heightIndices.finite_toSet.countable
      (fun heightIndex _ => by
        change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
          wz1Lemma23HeightInterval graphScale heightIndex)
        exact measurableSet_Ico.preimage
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  let shading : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily retained.shading source.extremal.delta_pos) :=
    { carrier := fun index => ambient.carrier index ∩ heightRegion
      measurable_carrier := fun index =>
        (ambient.measurable_carrier index).inter hheightRegionMeasurable
      subset_body := fun index => Set.inter_subset_left.trans
        (ambient.subset_body index) }
  have hunion : shading.union = ambient.union ∩ heightRegion := by
    ext point
    constructor
    · rintro ⟨index, hpointAmbient, hpointRegion⟩
      exact ⟨⟨index, hpointAmbient⟩, hpointRegion⟩
    · rintro ⟨⟨index, hpointAmbient⟩, hpointRegion⟩
      exact ⟨index, hpointAmbient, hpointRegion⟩
  have hvolume : volume shading.union =
      ∑ heightIndex ∈ heightIndices,
        volume (ambient.union ∩
          wz1Lemma23HeightSlab graphScale heightIndex) := by
    rw [hunion]
    have hregionUnion : ambient.union ∩ heightRegion =
        ⋃ heightIndex ∈ heightIndices,
          ambient.union ∩
            wz1Lemma23HeightSlab graphScale heightIndex := by
      ext point
      constructor
      · rintro ⟨hpointAmbient, hpointRegion⟩
        rcases Set.mem_iUnion₂.mp hpointRegion with
          ⟨heightIndex, hheightIndex, hpointSlab⟩
        exact Set.mem_iUnion₂.mpr
          ⟨heightIndex, hheightIndex, hpointAmbient, hpointSlab⟩
      · intro hpoint
        rcases Set.mem_iUnion₂.mp hpoint with
          ⟨heightIndex, hheightIndex, hpointAmbient, hpointSlab⟩
        exact ⟨hpointAmbient, Set.mem_iUnion₂.mpr
          ⟨heightIndex, hheightIndex, hpointSlab⟩⟩
    rw [hregionUnion]
    have hdisjointSelected : (heightIndices : Set ℤ).PairwiseDisjoint
        (fun heightIndex => ambient.union ∩
          wz1Lemma23HeightSlab graphScale heightIndex) := by
      intro first hfirst second hsecond hne
      exact hdisjoint
        (hheightSubset hfirst) (hheightSubset hsecond) hne
    exact MeasureTheory.measure_biUnion_finset
      hdisjointSelected
      (fun heightIndex hheightIndex =>
        hmeas heightIndex (hheightSubset hheightIndex))
  have hselectedSum :
      (∑ index ∈ selected, weight index) =
        ∑ heightIndex ∈ heightIndices,
          volume (ambient.union ∩
            wz1Lemma23HeightSlab graphScale heightIndex) := by
    rw [Finset.sum_image hheightInjective]
  have hlayerTop : layerMass ≠ ⊤ := by
    rcases hselected with ⟨index, hindex⟩
    have hweightTop : weight index ≠ ⊤ :=
      ne_top_of_le_ne_top htotalTop (by
        rw [htotal]
        exact Finset.single_le_sum (fun _ _ => bot_le)
          (Finset.mem_univ index))
    exact ne_top_of_le_ne_top hweightTop (hband index hindex).1
  refine ⟨{
    graphScale_pos := hgraphScale
    ambient_union_subset := hambient
    bins := bins
    bins_eq := by simpa [indexType, Fintype.card_subtype, allHeights] using hbins
    heightIndices := heightIndices
    heightIndices_subset := hheightSubset
    heightIndices_nonempty := hselected.image _
    layerMass := layerMass
    layerMass_pos := hlayerMass
    layerMass_ne_top := hlayerTop
    layer_volume_band := by
      intro heightIndex hheightIndex
      rcases Finset.mem_image.mp hheightIndex with ⟨index, hindex, rfl⟩
      exact hband index hindex
    heightRegion := heightRegion
    heightRegion_eq := rfl
    heightRegion_measurable := hheightRegionMeasurable
    shading := shading
    carrier_eq := by intro index; rfl
    subshading := fun _ => Set.inter_subset_left
    union_eq := hunion
    volume_eq_sum := hvolume
    retained_volume := by
      rw [hvolume, ← hselectedSum]
      simpa [mul_comm] using hretained
  }⟩

/-- Backwards-compatible popular-height data on the maximal global bin. -/
abbrev PureWZ2SourceHorizontalHeightPopularShadow
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (retained : PureWZ2SourceHorizontalResidueShadingData residue)
    (ambient : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily retained.shading source.extremal.delta_pos))
    (graphScale : ℝ) :=
  PureWZ2SourceHorizontalFixedBinHeightPopularShadow retained ambient graphScale

/-- Compatibility wrapper for the former maximal-bin height-popularity API. -/
theorem PureWZ2SourceHorizontalResidueShadingData.heightPopularShadow
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (retained : PureWZ2SourceHorizontalResidueShadingData residue)
    (ambient : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily retained.shading source.extremal.delta_pos))
    (hambient : ambient.union ⊆ retained.shading.union)
    (hvolumePos : 0 < volume ambient.union)
    (graphScale : ℝ) (hgraphScale : 0 < graphScale) :
    Nonempty (PureWZ2SourceHorizontalHeightPopularShadow retained ambient graphScale) :=
  PureWZ2SourceHorizontalFixedBinResidueShadingData.heightPopularShadowFixedBin
    retained ambient hambient hvolumePos graphScale hgraphScale

end Kakeya.Assouad
