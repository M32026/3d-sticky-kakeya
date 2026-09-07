import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSliceAxialCoordinateSlab
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSliceSelection

/-!
# Finite partition in the frozen rescaled longitudinal coordinate

The third coordinate of the literal rescaling is bounded on every cropped
paper shading.  We therefore reuse the finite index interval from the
horizontal common-slice partition, but its slabs are preimages under the
frozen rescaling coordinate.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

lemma paperAxisZeroPoint_norm_le_one
    {rho : ℝ} {tube : Kakeya.DeltaTube rho}
    (hline : WZ1PaperTubeInLineClass tube) :
    ‖wz1TubeAxisZeroPoint tube‖ ≤ 1 := by
  have hzeroTwo : wz1TubeAxisZeroPoint tube (2 : Fin 3) = 0 :=
    wz1TubeAxisZeroPoint_coord_two tube hline.vertical
  have hnormSq : ‖wz1TubeAxisZeroPoint tube‖ ^ 2 =
      (wz1TubeAxisZeroPoint tube 0) ^ 2 +
      (wz1TubeAxisZeroPoint tube 1) ^ 2 +
      (wz1TubeAxisZeroPoint tube 2) ^ 2 := by
    have h := EuclideanSpace.real_norm_sq_eq
      (wz1TubeAxisZeroPoint tube)
    simpa [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] using h
  have hfirst : (wz1TubeAxisZeroPoint tube 0) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    exact hline.2.1
  have hsecond : (wz1TubeAxisZeroPoint tube 1) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    exact hline.2.2
  have hnormNonnegative : 0 ≤ ‖wz1TubeAxisZeroPoint tube‖ := norm_nonneg _
  apply (sq_le_sq₀ hnormNonnegative (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [hnormSq, hzeroTwo]
  norm_num at hfirst hsecond ⊢
  linarith

lemma paperShadingPoint_norm_le_three
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {point : Point3} (hpoint : point ∈ shading.union) : ‖point‖ ≤ 3 := by
  rcases hpoint with ⟨tube, htube⟩
  have hbox := (shading.subset_body tube htube).2
  have hcoordinates : |point 0| ≤ 1 ∧ |point 1| ≤ 1 ∧ |point 2| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hbox
  have hnormSq : ‖point‖ ^ 2 =
      point 0 ^ 2 + point 1 ^ 2 + point 2 ^ 2 := by
    have h := EuclideanSpace.real_norm_sq_eq point
    simpa [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] using h
  have hzero : point 0 ^ 2 ≤ 1 := by
    have habs : |point 0| ≤ |(1 : ℝ)| := by simpa using hcoordinates.1
    simpa using (sq_le_sq.mpr habs)
  have hone : point 1 ^ 2 ≤ 1 := by
    have habs : |point 1| ≤ |(1 : ℝ)| := by simpa using hcoordinates.2.1
    simpa using (sq_le_sq.mpr habs)
  have htwo : point 2 ^ 2 ≤ 1 := by
    have habs : |point 2| ≤ |(1 : ℝ)| := by simpa using hcoordinates.2.2
    simpa using (sq_le_sq.mpr habs)
  apply (sq_le_sq₀ (norm_nonneg point) (by norm_num : (0 : ℝ) ≤ 3)).mp
  rw [hnormSq]
  nlinarith

/-- Cropping places the third coordinate of the frozen literal image in the
fixed interval `[-1,1]`. -/
lemma proposition63AxialCoordinate_mem_Icc
    {delta rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (hanchorLine : WZ1PaperTubeInLineClass anchor)
    {point : Point3} (hpoint : point ∈ shading.union) :
    proposition63AxialCoordinate anchor hrho point ∈ Set.Icc (-1 : ℝ) 1 := by
  have hpointNorm : ‖point‖ ≤ 3 := paperShadingPoint_norm_le_three hpoint
  have hzeroNorm : ‖wz1TubeAxisZeroPoint anchor‖ ≤ 1 :=
    paperAxisZeroPoint_norm_le_one hanchorLine
  have hinner : |inner ℝ
      (point - wz1TubeAxisZeroPoint anchor)
      (wz1PaperDirection anchor)| ≤ 4 := by
    calc
      |inner ℝ (point - wz1TubeAxisZeroPoint anchor)
          (wz1PaperDirection anchor)| ≤
          ‖point - wz1TubeAxisZeroPoint anchor‖ *
            ‖wz1PaperDirection anchor‖ := abs_real_inner_le_norm _ _
      _ = ‖point - wz1TubeAxisZeroPoint anchor‖ := by
        rw [wz1PaperDirection_norm anchor, mul_one]
      _ ≤ ‖point‖ + ‖wz1TubeAxisZeroPoint anchor‖ := norm_sub_le _ _
      _ ≤ 3 + 1 := add_le_add hpointNorm hzeroNorm
      _ = 4 := by norm_num
  rw [proposition63AxialCoordinate_eq]
  change -1 ≤ (1 / 100 : ℝ) * inner ℝ
      (point - wz1TubeAxisZeroPoint anchor)
      (wz1PaperDirection anchor) ∧
    (1 / 100 : ℝ) * inner ℝ
      (point - wz1TubeAxisZeroPoint anchor)
      (wz1PaperDirection anchor) ≤ 1
  have hinnerBounds := (abs_le.mp hinner)
  constructor <;> nlinarith [hinnerBounds.1, hinnerBounds.2]

lemma proposition63_mem_axialSlab_iff
    {rho Delta : ℝ} (hDelta : 0 < Delta)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (index : ℤ) (point : Point3) :
    point ∈ proposition63AxialSlab anchor hrho Delta index ↔
      Int.floor (proposition63AxialCoordinate anchor hrho point / Delta) =
        index := by
  simp only [proposition63AxialSlab, Set.mem_setOf_eq, Set.mem_Ico]
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

lemma proposition63_axial_index_mem
    {rho Delta : ℝ} (hDelta : 0 < Delta)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    {point : Point3}
    (hpoint : proposition63AxialCoordinate anchor hrho point ∈
      Set.Icc (-1 : ℝ) 1) :
    Int.floor (proposition63AxialCoordinate anchor hrho point / Delta) ∈
      commonSliceHeightIndices Delta :=
  commonSlice_height_index_mem hDelta hpoint

lemma proposition63_axialSlab_disjoint
    {rho Delta : ℝ} (hDelta : 0 < Delta)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    {first second : ℤ} (hne : first ≠ second) :
    Disjoint (proposition63AxialSlab anchor hrho Delta first)
      (proposition63AxialSlab anchor hrho Delta second) := by
  rw [Set.disjoint_left]
  intro point hfirst hsecond
  have h1 := (proposition63_mem_axialSlab_iff hDelta anchor hrho first point).1
    hfirst
  have h2 := (proposition63_mem_axialSlab_iff hDelta anchor hrho second point).1
    hsecond
  exact hne (h1.symm.trans h2)

/-- Exact finite partition of an arbitrary cropped source shading by the
frozen rescaled longitudinal coordinate. -/
theorem proposition63_axial_slab_mass_sum
    {delta rho Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (hanchorLine : WZ1PaperTubeInLineClass anchor)
    (hDelta : 0 < Delta) :
    (∑ index ∈ commonSliceHeightIndices Delta,
      commonSliceSlabMass shading
        (proposition63AxialSlab anchor hrho Delta index)) = shading.mass := by
  simp_rw [commonSliceSlabMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tube _
  have hpairwise : Set.PairwiseDisjoint
      (↑(commonSliceHeightIndices Delta))
      (fun index => shading.carrier tube ∩
        proposition63AxialSlab anchor hrho Delta index) := by
    intro first _ second _ hne
    exact (proposition63_axialSlab_disjoint hDelta anchor hrho hne).mono
      Set.inter_subset_right Set.inter_subset_right
  have hmeasurable : ∀ index ∈ commonSliceHeightIndices Delta,
      MeasurableSet (shading.carrier tube ∩
        proposition63AxialSlab anchor hrho Delta index) := by
    intro index _
    exact (shading.measurable_carrier tube).inter
      (proposition63AxialSlab_measurable anchor hrho index)
  have hunion :
      ⋃ index ∈ commonSliceHeightIndices Delta,
        shading.carrier tube ∩
          proposition63AxialSlab anchor hrho Delta index =
      shading.carrier tube := by
    apply Set.Subset.antisymm
    · rintro point hpoint
      rcases Set.mem_iUnion₂.mp hpoint with ⟨index, _, hpoint⟩
      exact hpoint.1
    · intro point hpoint
      have hcoordinate := proposition63AxialCoordinate_mem_Icc
        shading anchor hrho hanchorLine ⟨tube, hpoint⟩
      let index := Int.floor
        (proposition63AxialCoordinate anchor hrho point / Delta)
      exact Set.mem_iUnion₂.mpr ⟨index,
        proposition63_axial_index_mem hDelta anchor hrho hcoordinate,
        hpoint, (proposition63_mem_axialSlab_iff
          hDelta anchor hrho index point).2 rfl⟩
  rw [← MeasureTheory.measure_biUnion_finset hpairwise hmeasurable, hunion]

end Kakeya.Assouad.PureWZ2

end
