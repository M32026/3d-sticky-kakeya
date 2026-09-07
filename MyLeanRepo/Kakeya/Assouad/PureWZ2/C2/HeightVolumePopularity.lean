import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SlicePopularity
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization.WeightBinning
import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement

/-!
# Union-volume popularity before auxiliary spatial selection

This is the carrier-independent popularity step used in WZ Lemma 24.  It is
deliberately applied before selecting a fixed line, a parent residue, or a
finite graph.  The weights are genuine three-dimensional union volumes in
the graph-height slabs.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- A dyadically popular collection of height slabs for an arbitrary finite
ordinary shading.  No graph-cell cardinality enters the retained weight. -/
structure PureWZ2HeightVolumePopularData
    {family : Kakeya.Streamlined.BodyFamily}
    (ambient : Kakeya.Streamlined.Shading family)
    (graphScale : ℝ) where
  graphScale_pos : 0 < graphScale
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
          wz1Lemma23HeightSlab graphScale heightIndex) ≤ 2 * layerMass
  heightRegion : Set Point3 :=
    ⋃ heightIndex ∈ heightIndices,
      wz1Lemma23HeightSlab graphScale heightIndex
  heightRegion_eq : heightRegion =
    ⋃ heightIndex ∈ heightIndices,
      wz1Lemma23HeightSlab graphScale heightIndex
  heightRegion_measurable : MeasurableSet heightRegion
  shading : Kakeya.Streamlined.Shading family
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

/-- Select a union-volume-popular height band on an arbitrary bounded,
positive finite shading. -/
theorem pureWZ2_heightVolumePopularity
    {family : Kakeya.Streamlined.BodyFamily}
    (ambient : Kakeya.Streamlined.Shading family)
    (graphScale : ℝ) (hgraphScale : 0 < graphScale)
    (hball : ambient.union ⊆ Metric.closedBall (0 : Point3) 2)
    (hvolumePos : 0 < volume ambient.union)
    (hvolumeTop : volume ambient.union ≠ ⊤) :
    Nonempty (PureWZ2HeightVolumePopularData ambient graphScale) := by
  let allHeights :=
    wz1Lemma23BoundedHeightIndices graphScale hgraphScale
  let indexType := {heightIndex : ℤ // heightIndex ∈ allHeights}
  let weight : indexType → ENNReal := fun heightIndex =>
    volume (ambient.union ∩
      wz1Lemma23HeightSlab graphScale heightIndex.1)
  let total := volume ambient.union
  have hpartition : ambient.union =
      ⋃ heightIndex ∈ allHeights,
        ambient.union ∩
          wz1Lemma23HeightSlab graphScale heightIndex := by
    apply Set.Subset.antisymm
    · intro point hpoint
      have hnorm : ‖point‖ ≤ 2 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hball hpoint
      rcases wz1Lemma23_radiusTwo_mem_boundedHeightSlab hgraphScale hnorm with
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
    intro first _ second _ hne
    exact (wz1Lemma23_heightSlab_disjoint hgraphScale hne).mono
      Set.inter_subset_right Set.inter_subset_right
  have hmeas : ∀ heightIndex ∈ allHeights, MeasurableSet
      (ambient.union ∩
        wz1Lemma23HeightSlab graphScale heightIndex) := by
    intro heightIndex _
    exact (measurableSet_shading_union ambient).inter (by
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
  rcases ennreal_dyadic_bin weight total htotal hvolumeTop hvolumePos with
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
  have hregionMeas : MeasurableSet heightRegion :=
    MeasurableSet.biUnion heightIndices.finite_toSet.countable
      (fun heightIndex _ => by
        change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
          wz1Lemma23HeightInterval graphScale heightIndex)
        exact measurableSet_Ico.preimage
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  let shading : Kakeya.Streamlined.Shading family :=
    { carrier := fun index => ambient.carrier index ∩ heightRegion
      measurable_carrier := fun index =>
        (ambient.measurable_carrier index).inter hregionMeas
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
      simp [heightRegion]
    rw [hregionUnion]
    exact MeasureTheory.measure_biUnion_finset
      (fun first hfirst second hsecond hne =>
        hdisjoint (hheightSubset hfirst) (hheightSubset hsecond) hne)
      (fun heightIndex hheight => hmeas heightIndex (hheightSubset hheight))
  have hselectedSum :
      (∑ index ∈ selected, weight index) =
        ∑ heightIndex ∈ heightIndices,
          volume (ambient.union ∩
            wz1Lemma23HeightSlab graphScale heightIndex) := by
    rw [Finset.sum_image hheightInjective]
  have hlayerTop : layerMass ≠ ⊤ := by
    rcases hselected with ⟨index, hindex⟩
    have hweightTop : weight index ≠ ⊤ :=
      ne_top_of_le_ne_top hvolumeTop (by
        dsimp only [weight]
        exact measure_mono Set.inter_subset_left)
    exact ne_top_of_le_ne_top hweightTop (hband index hindex).1
  exact ⟨{
    graphScale_pos := hgraphScale
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
    heightRegion_measurable := hregionMeas
    shading := shading
    carrier_eq := fun _ => rfl
    subshading := fun _ => Set.inter_subset_left
    union_eq := hunion
    volume_eq_sum := hvolume
    retained_volume := by
      rw [hvolume, ← hselectedSum]
      simpa [mul_comm] using hretained
  }⟩

end Kakeya.Assouad
