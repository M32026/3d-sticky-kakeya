import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSliceCoordinateSlab

/-!
# Finite height partition for common slices

The cropped paper region lies in `z ∈ [-1,1]`.  Partition it by the exact
half-open slabs `[k Delta, (k+1) Delta)`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

def commonSliceHeightIndices (Delta : ℝ) : Finset ℤ :=
  Finset.Icc (Int.floor (-1 / Delta)) (Int.floor (1 / Delta))

lemma commonSlice_mem_heightSlab_iff
    {Delta : ℝ} (hDelta : 0 < Delta)
    (index : ℤ) (point : Point3) :
    point ∈ commonSliceHeightSlab Delta index ↔
      Int.floor (point (2 : Fin 3) / Delta) = index := by
  simp only [commonSliceHeightSlab, Set.mem_setOf_eq, Set.mem_Ico]
  rw [Int.floor_eq_iff]
  constructor
  · rintro ⟨hlower, hupper⟩
    constructor
    · exact (le_div_iff₀ hDelta).2 (by simpa [mul_comm] using hlower)
    · exact (div_lt_iff₀ hDelta).2 (by simpa [mul_comm] using hupper)
  · rintro ⟨hlower, hupper⟩
    constructor
    · exact (le_div_iff₀ hDelta).1 hlower |>.trans_eq (by ring)
    · exact (div_lt_iff₀ hDelta).1 hupper |>.trans_eq (by ring)

lemma commonSlice_heightSlab_disjoint
    {Delta : ℝ} (hDelta : 0 < Delta)
    {first second : ℤ} (hne : first ≠ second) :
    Disjoint (commonSliceHeightSlab Delta first)
      (commonSliceHeightSlab Delta second) := by
  rw [Set.disjoint_left]
  intro point hfirst hsecond
  have h1 := (commonSlice_mem_heightSlab_iff hDelta first point).mp hfirst
  have h2 := (commonSlice_mem_heightSlab_iff hDelta second point).mp hsecond
  exact hne (h1.symm.trans h2)

lemma commonSlice_height_index_mem
    {Delta : ℝ} (hDelta : 0 < Delta)
    {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    Int.floor (z / Delta) ∈ commonSliceHeightIndices Delta := by
  rw [commonSliceHeightIndices, Finset.mem_Icc]
  constructor
  · exact Int.floor_mono (by
      apply (div_le_div_iff_of_pos_right hDelta).2
      exact hz.1)
  · exact Int.floor_mono (by
      apply (div_le_div_iff_of_pos_right hDelta).2
      exact hz.2)

lemma commonSlice_axisBox_covered
    {Delta : ℝ} (hDelta : 0 < Delta) :
    Kakeya.Streamlined.axisBox 2 2 2 ⊆
      ⋃ index ∈ commonSliceHeightIndices Delta,
        commonSliceHeightSlab Delta index := by
  intro point hpoint
  have hz : point (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 := by
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hpoint
    exact abs_le.mp (by simpa using hpoint.2.2)
  let index := Int.floor (point (2 : Fin 3) / Delta)
  exact Set.mem_iUnion₂.mpr ⟨index, commonSlice_height_index_mem hDelta hz,
    (commonSlice_mem_heightSlab_iff hDelta index point).2 rfl⟩

lemma commonSlice_shading_covered
    {delta Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (hDelta : 0 < Delta) :
    shading.union ⊆
      ⋃ index ∈ commonSliceHeightIndices Delta,
        commonSliceHeightSlab Delta index := by
  rintro point ⟨tube, hpoint⟩
  have hbody := shading.subset_body tube hpoint
  exact commonSlice_axisBox_covered hDelta hbody.2

/-- The finite common-slice slab masses sum exactly to the full indexed
shaded mass. -/
theorem commonSlice_height_slab_mass_sum
    {delta Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (hDelta : 0 < Delta) :
    (∑ index ∈ commonSliceHeightIndices Delta,
        commonSliceSlabMass shading (commonSliceHeightSlab Delta index)) =
      shading.mass := by
  simp_rw [commonSliceSlabMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tube _
  have hpairwise : Set.PairwiseDisjoint
      (↑(commonSliceHeightIndices Delta))
      (fun index => shading.carrier tube ∩ commonSliceHeightSlab Delta index) := by
    intro first hfirst second hsecond hne
    exact (commonSlice_heightSlab_disjoint hDelta hne).mono
      Set.inter_subset_right Set.inter_subset_right
  have hmeasurable : ∀ index ∈ commonSliceHeightIndices Delta,
      MeasurableSet (shading.carrier tube ∩
        commonSliceHeightSlab Delta index) := by
    intro index _
    exact (shading.measurable_carrier tube).inter <| by
      change MeasurableSet
        ((fun point : Point3 => point (2 : Fin 3)) ⁻¹'
          Set.Ico ((index : ℝ) * Delta) (((index : ℝ) + 1) * Delta))
      exact measurableSet_Ico.preimage
        (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.measurable
  have hunion :
      ⋃ index ∈ commonSliceHeightIndices Delta,
        shading.carrier tube ∩ commonSliceHeightSlab Delta index =
      shading.carrier tube := by
    apply Set.Subset.antisymm
    · rintro point hpoint
      rcases Set.mem_iUnion₂.mp hpoint with ⟨index, _, hpoint⟩
      exact hpoint.1
    · intro point hpoint
      have hcover := commonSlice_shading_covered shading hDelta
        ⟨tube, hpoint⟩
      rcases Set.mem_iUnion₂.mp hcover with ⟨index, hindex, hslab⟩
      exact Set.mem_iUnion₂.mpr ⟨index, hindex, hpoint, hslab⟩
  rw [← MeasureTheory.measure_biUnion_finset hpairwise hmeasurable, hunion]

end Kakeya.Assouad.PureWZ2

end
