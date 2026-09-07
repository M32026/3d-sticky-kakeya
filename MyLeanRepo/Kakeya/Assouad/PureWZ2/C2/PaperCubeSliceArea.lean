import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GoodHeights
import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Section6CoverAdapter
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers

/-!
# Horizontal slice area of a literal paper cube
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

private def pureWZ2Point2EquivPi : Point2 ≃ᵐ (Fin 2 → ℝ) :=
  { toFun := WithLp.ofLp
    invFun := WithLp.toLp 2
    left_inv := WithLp.toLp_ofLp (2 : ENNReal)
    right_inv := WithLp.ofLp_toLp (2 : ENNReal)
    measurable_toFun :=
      (PiLp.continuous_ofLp
        (p := 2) (β := fun _ : Fin 2 => ℝ)).measurable
    measurable_invFun :=
      (PiLp.continuous_toLp
        (p := 2) (β := fun _ : Fin 2 => ℝ)).measurable }

private lemma pureWZ2Point2EquivPi_measurePreserving :
    MeasurePreserving pureWZ2Point2EquivPi volume volume :=
  PiLp.volume_preserving_ofLp (Fin 2)

/-- A horizontal slice of a side-`scale` paper cube has area at most `scale²`. -/
theorem wz1PaperGridCube_planarSlice_volume_le
    {scale : ℝ} (hscale : 0 < scale)
    (cell : ℤ × ℤ × ℤ) (height : ℝ) :
    volume
        (wz1Lemma23PlanarSlice
          (wz1PaperGridCube scale cell) height) ≤
      ENNReal.ofReal (scale ^ 2) := by
  let lowerX : ℝ := (cell.1 : ℝ) * scale
  let upperX : ℝ := ((cell.1 : ℝ) + 1) * scale
  let lowerY : ℝ := (cell.2.1 : ℝ) * scale
  let upperY : ℝ := ((cell.2.1 : ℝ) + 1) * scale
  let rectangle : Set Point2 :=
    {point | point 0 ∈ Set.Ico lowerX upperX ∧
      point 1 ∈ Set.Ico lowerY upperY}
  have hsliceSubset :
      wz1Lemma23PlanarSlice
          (wz1PaperGridCube scale cell) height ⊆
        rectangle := by
    intro point hpoint
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    rw [wz1PaperGridCube_eq_Ico hscale cell] at hlift
    change
      (cell.1 : ℝ) * scale ≤ (point3 (point 0) (point 1) height) 0 ∧
      (point3 (point 0) (point 1) height) 0 <
          ((cell.1 : ℝ) + 1) * scale ∧
      (cell.2.1 : ℝ) * scale ≤ (point3 (point 0) (point 1) height) 1 ∧
      (point3 (point 0) (point 1) height) 1 <
          ((cell.2.1 : ℝ) + 1) * scale ∧
      (cell.2.2 : ℝ) * scale ≤ (point3 (point 0) (point 1) height) 2 ∧
      (point3 (point 0) (point 1) height) 2 <
          ((cell.2.2 : ℝ) + 1) * scale at hlift
    change point 0 ∈ Set.Ico lowerX upperX ∧
      point 1 ∈ Set.Ico lowerY upperY
    have hx0 : (point3 (point 0) (point 1) height) 0 = point 0 := by
      simp [point3, PiLp.single_apply]
    have hx1 : (point3 (point 0) (point 1) height) 1 = point 1 := by
      simp [point3, PiLp.single_apply]
    refine ⟨?_, ?_⟩
    · change lowerX ≤ point 0 ∧ point 0 < upperX
      rw [← hx0]
      exact ⟨hlift.1, hlift.2.1⟩
    · change lowerY ≤ point 1 ∧ point 1 < upperY
      rw [← hx1]
      exact ⟨hlift.2.2.1, hlift.2.2.2.1⟩
  have hrectangleVolume :
      volume rectangle = ENNReal.ofReal (scale ^ 2) := by
    let coordinateSet : Fin 2 → Set ℝ :=
      ![Set.Ico lowerX upperX, Set.Ico lowerY upperY]
    let coordinateRectangle : Set (Fin 2 → ℝ) :=
      Set.univ.pi coordinateSet
    have hcoordinate :
        pureWZ2Point2EquivPi '' rectangle = coordinateRectangle := by
      ext point
      simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · rintro ⟨source, hsource, rfl⟩
        intro coordinate
        fin_cases coordinate
        · simpa [coordinateSet, pureWZ2Point2EquivPi] using hsource.1
        · simpa [coordinateSet, pureWZ2Point2EquivPi] using hsource.2
      · intro hpoint
        let source : Point2 := WithLp.toLp 2 point
        refine ⟨source, ?_, by simp [source, pureWZ2Point2EquivPi]⟩
        constructor
        · simpa [coordinateSet] using hpoint 0
        · simpa [coordinateSet] using hpoint 1
    have hmeasurePreserving :
        MeasurePreserving pureWZ2Point2EquivPi volume volume :=
      pureWZ2Point2EquivPi_measurePreserving
    calc
      volume rectangle = volume coordinateRectangle := by
        rw [← hcoordinate]
        have hpre :
            pureWZ2Point2EquivPi ⁻¹'
                (pureWZ2Point2EquivPi '' rectangle) = rectangle :=
          Set.preimage_image_eq rectangle pureWZ2Point2EquivPi.injective
        have himageMeas :
            MeasurableSet (pureWZ2Point2EquivPi '' rectangle) :=
          pureWZ2Point2EquivPi.measurableSet_image.mpr (by
            exact (measurableSet_Ico.preimage (by fun_prop)).inter
              (measurableSet_Ico.preimage (by fun_prop)))
        have hmeasure :=
          hmeasurePreserving.measure_preimage_emb
            pureWZ2Point2EquivPi.measurableEmbedding
            (pureWZ2Point2EquivPi '' rectangle)
        rw [hpre] at hmeasure
        exact hmeasure
      _ = ∏ coordinate : Fin 2, volume (coordinateSet coordinate) :=
        MeasureTheory.volume_pi_pi coordinateSet
      _ = ENNReal.ofReal scale * ENNReal.ofReal scale := by
        rw [Fin.prod_univ_two]
        simp only [coordinateSet, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Real.volume_Ico]
        have hx : upperX - lowerX = scale := by
          dsimp [upperX, lowerX]
          ring
        have hy : upperY - lowerY = scale := by
          dsimp [upperY, lowerY]
          ring
        rw [hx, hy]
      _ = ENNReal.ofReal (scale ^ 2) := by
        rw [← ENNReal.ofReal_mul hscale.le]
        ring
  rw [← hrectangleVolume]
  exact measure_mono hsliceSubset

/-- At a height inside its half-open vertical interval, the horizontal slice
of a side-`scale` paper cube has exactly area `scale^2`. -/
theorem wz1PaperGridCube_planarSlice_volume_exact
    {scale : ℝ} (hscale : 0 < scale)
    (cell : ℤ × ℤ × ℤ) (height : ℝ)
    (hheight : height ∈
      Set.Ico ((cell.2.2 : ℝ) * scale)
        (((cell.2.2 : ℝ) + 1) * scale)) :
    volume
        (wz1Lemma23PlanarSlice
          (wz1PaperGridCube scale cell) height) =
      ENNReal.ofReal (scale ^ 2) := by
  let lowerX : ℝ := (cell.1 : ℝ) * scale
  let upperX : ℝ := ((cell.1 : ℝ) + 1) * scale
  let lowerY : ℝ := (cell.2.1 : ℝ) * scale
  let upperY : ℝ := ((cell.2.1 : ℝ) + 1) * scale
  let rectangle : Set Point2 :=
    {point | point 0 ∈ Set.Ico lowerX upperX ∧
      point 1 ∈ Set.Ico lowerY upperY}
  have hsliceEq :
      wz1Lemma23PlanarSlice
          (wz1PaperGridCube scale cell) height = rectangle := by
    ext point
    rw [wz1Lemma23_mem_planarSlice_iff, wz1PaperGridCube_eq_Ico hscale cell]
    have hx0 : (point3 (point 0) (point 1) height) 0 = point 0 := by
      simp [point3]
    have hx1 : (point3 (point 0) (point 1) height) 1 = point 1 := by
      simp [point3]
    have hx2 : (point3 (point 0) (point 1) height) 2 = height := by
      simp [point3]
    simp only [rectangle, Set.mem_setOf_eq, Set.mem_Ico]
    rw [hx0, hx1, hx2]
    dsimp only [lowerX, upperX, lowerY, upperY]
    constructor
    · rintro ⟨h0l, h0u, h1l, h1u, _h2l, _h2u⟩
      exact ⟨⟨h0l, h0u⟩, h1l, h1u⟩
    · rintro ⟨⟨h0l, h0u⟩, h1l, h1u⟩
      exact ⟨h0l, h0u, h1l, h1u, hheight.1, hheight.2⟩
  have hrectangleVolume :
      volume rectangle = ENNReal.ofReal (scale ^ 2) := by
    let coordinateSet : Fin 2 → Set ℝ :=
      ![Set.Ico lowerX upperX, Set.Ico lowerY upperY]
    let coordinateRectangle : Set (Fin 2 → ℝ) :=
      Set.univ.pi coordinateSet
    have hcoordinate :
        pureWZ2Point2EquivPi '' rectangle = coordinateRectangle := by
      ext point
      simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · rintro ⟨source, hsource, rfl⟩
        intro coordinate
        fin_cases coordinate
        · simpa [coordinateSet, pureWZ2Point2EquivPi] using hsource.1
        · simpa [coordinateSet, pureWZ2Point2EquivPi] using hsource.2
      · intro hpoint
        let source : Point2 := WithLp.toLp 2 point
        refine ⟨source, ?_, by simp [source, pureWZ2Point2EquivPi]⟩
        constructor
        · simpa [coordinateSet] using hpoint 0
        · simpa [coordinateSet] using hpoint 1
    have hmeasurePreserving :
        MeasurePreserving pureWZ2Point2EquivPi volume volume :=
      pureWZ2Point2EquivPi_measurePreserving
    calc
      volume rectangle = volume coordinateRectangle := by
        rw [← hcoordinate]
        have hpre :
            pureWZ2Point2EquivPi ⁻¹'
                (pureWZ2Point2EquivPi '' rectangle) = rectangle :=
          Set.preimage_image_eq rectangle pureWZ2Point2EquivPi.injective
        have himageMeas :
            MeasurableSet (pureWZ2Point2EquivPi '' rectangle) :=
          pureWZ2Point2EquivPi.measurableSet_image.mpr (by
            exact (measurableSet_Ico.preimage (by fun_prop)).inter
              (measurableSet_Ico.preimage (by fun_prop)))
        have hmeasure :=
          hmeasurePreserving.measure_preimage_emb
            pureWZ2Point2EquivPi.measurableEmbedding
            (pureWZ2Point2EquivPi '' rectangle)
        rw [hpre] at hmeasure
        exact hmeasure
      _ = ∏ coordinate : Fin 2, volume (coordinateSet coordinate) :=
        MeasureTheory.volume_pi_pi coordinateSet
      _ = ENNReal.ofReal scale * ENNReal.ofReal scale := by
        rw [Fin.prod_univ_two]
        simp only [coordinateSet, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Real.volume_Ico]
        have hx : upperX - lowerX = scale := by
          dsimp [upperX, lowerX]
          ring
        have hy : upperY - lowerY = scale := by
          dsimp [upperY, lowerY]
          ring
        rw [hx, hy]
      _ = ENNReal.ofReal (scale ^ 2) := by
        rw [← ENNReal.ofReal_mul hscale.le]
        ring
  rw [hsliceEq]
  exact hrectangleVolume

/-- A finite family of distinct paper cubes with one common vertical index has
exact horizontal slice area `#cells * scale^2` at every height in that layer. -/
theorem wz1PaperGridCubes_planarSlice_volume_exact_of_height
    {scale : ℝ} (hscale : 0 < scale)
    (cells : Finset (ℤ × ℤ × ℤ)) (heightIndex : ℤ)
    (hcells : ∀ cell ∈ cells, cell.2.2 = heightIndex)
    (height : ℝ)
    (hheight : height ∈
      Set.Ico ((heightIndex : ℝ) * scale)
        (((heightIndex : ℝ) + 1) * scale)) :
    volume
        (wz1Lemma23PlanarSlice
          (⋃ cell ∈ cells, wz1PaperGridCube scale cell) height) =
      (cells.card : ENNReal) * ENNReal.ofReal (scale ^ 2) := by
  have hsliceUnion :
      wz1Lemma23PlanarSlice
          (⋃ cell ∈ cells, wz1PaperGridCube scale cell) height =
        ⋃ cell ∈ cells,
          wz1Lemma23PlanarSlice
            (wz1PaperGridCube scale cell) height := by
    ext point
    simp only [wz1Lemma23_mem_planarSlice_iff, Set.mem_iUnion]
  rw [hsliceUnion]
  rw [MeasureTheory.measure_biUnion_finset]
  · calc
      (∑ cell ∈ cells,
          volume (wz1Lemma23PlanarSlice
            (wz1PaperGridCube scale cell) height)) =
          ∑ _cell ∈ cells, ENNReal.ofReal (scale ^ 2) := by
            apply Finset.sum_congr rfl
            intro cell hcell
            apply wz1PaperGridCube_planarSlice_volume_exact hscale
            simpa only [hcells cell hcell] using hheight
      _ = (cells.card : ENNReal) * ENNReal.ofReal (scale ^ 2) := by
        simp [Finset.sum_const]
  · intro first _hfirst second _hsecond hne
    apply Set.disjoint_left.mpr
    intro point hfirstSlice hsecondSlice
    have hfirst3 := wz1Lemma23_mem_planarSlice_iff.mp hfirstSlice
    have hsecond3 := wz1Lemma23_mem_planarSlice_iff.mp hsecondSlice
    exact Set.disjoint_left.mp (wz1PaperGridCube_disjoint hne)
      hfirst3 hsecond3
  · intro cell _hcell
    have hmap : Continuous (fun point : Point2 =>
        point3 (point 0) (point 1) height) := by
      unfold point3
      fun_prop
    have hpreimage :
        wz1Lemma23PlanarSlice (wz1PaperGridCube scale cell) height =
          (fun point : Point2 => point3 (point 0) (point 1) height) ⁻¹'
            wz1PaperGridCube scale cell := by
      ext point
      rw [wz1Lemma23_mem_planarSlice_iff]
      rfl
    rw [hpreimage]
    exact (wz1PaperGridCube_measurable cell).preimage hmap.measurable

/-- A finite union of side-`scale` paper cubes has slice area at most `#cells * scale²`. -/
theorem wz1PaperGridCubes_planarSlice_volume_le
    {scale : ℝ} (hscale : 0 < scale)
    (cells : Finset (ℤ × ℤ × ℤ)) (height : ℝ) :
    volume
        (wz1Lemma23PlanarSlice
          (⋃ cell ∈ cells, wz1PaperGridCube scale cell) height) ≤
      (cells.card : ENNReal) * ENNReal.ofReal (scale ^ 2) := by
  have hsliceUnion :
      wz1Lemma23PlanarSlice
          (⋃ cell ∈ cells, wz1PaperGridCube scale cell) height =
        ⋃ cell ∈ cells,
          wz1Lemma23PlanarSlice
            (wz1PaperGridCube scale cell) height := by
    ext point
    simp only [wz1Lemma23_mem_planarSlice_iff, Set.mem_iUnion]
  rw [hsliceUnion]
  calc
    volume
        (⋃ cell ∈ cells,
          wz1Lemma23PlanarSlice
            (wz1PaperGridCube scale cell) height)
        ≤ ∑ cell ∈ cells,
            volume
              (wz1Lemma23PlanarSlice
                (wz1PaperGridCube scale cell) height) :=
      measure_biUnion_finset_le cells _
    _ ≤ ∑ _cell ∈ cells, ENNReal.ofReal (scale ^ 2) := by
      exact Finset.sum_le_sum fun cell _ =>
        wz1PaperGridCube_planarSlice_volume_le hscale cell height
    _ = (cells.card : ENNReal) * ENNReal.ofReal (scale ^ 2) := by
      simp [Finset.sum_const]

/-- A slice-area lower bound forces a corresponding number of paper cubes. -/
theorem card_lower_of_paperGridCubes_planarSlice_volume
    {scale areaLower : ℝ} (hscale : 0 < scale)
    (hareaLower : 0 ≤ areaLower)
    (cells : Finset (ℤ × ℤ × ℤ)) (height : ℝ)
    (hlower :
      ENNReal.ofReal areaLower ≤
        volume
          (wz1Lemma23PlanarSlice
            (⋃ cell ∈ cells, wz1PaperGridCube scale cell) height)) :
    areaLower / scale ^ 2 ≤ (cells.card : ℝ) := by
  have hupper :=
    wz1PaperGridCubes_planarSlice_volume_le hscale cells height
  have hmain :
      ENNReal.ofReal areaLower ≤
        (cells.card : ENNReal) * ENNReal.ofReal (scale ^ 2) :=
    hlower.trans hupper
  have hfinite :
      (cells.card : ENNReal) * ENNReal.ofReal (scale ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have hreal :=
    (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfinite).mpr hmain
  rw [ENNReal.toReal_ofReal hareaLower, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal (sq_nonneg scale)] at hreal
  exact (div_le_iff₀ (sq_pos_of_pos hscale)).2 (by
    simpa [mul_comm] using hreal)

/-- Restricting a balanced fine union to selected active cells preserves exact cell mass. -/
theorem PureWZ2BalancedCoverData.selected_cells_volume
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily scale}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (selected : Finset (ℤ × ℤ × ℤ))
    (hselected : selected ⊆ balanced.activeCells) :
    volume
        (fineShading.union ∩
          ⋃ cell ∈ selected, wz1PaperGridCube scale cell) =
      (selected.card : ENNReal) * balanced.cellMass := by
  have hpartition :
      fineShading.union ∩
          ⋃ cell ∈ selected, wz1PaperGridCube scale cell =
        ⋃ cell ∈ selected,
          fineShading.union ∩ wz1PaperGridCube scale cell := by
    ext point
    constructor
    · rintro ⟨hpoint, hselectedUnion⟩
      rcases Set.mem_iUnion₂.mp hselectedUnion with
        ⟨cell, hcell, hpointCell⟩
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpoint, hpointCell⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨cell, hcell, hpointFine, hpointCell⟩
      exact ⟨hpointFine, Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCell⟩⟩
  rw [hpartition]
  have hDisjoint :
      (selected : Set (ℤ × ℤ × ℤ)).PairwiseDisjoint
        (fun cell => fineShading.union ∩ wz1PaperGridCube scale cell) := by
    intro first _ second _ hne
    exact (wz1PaperGridCube_disjoint hne).mono
      Set.inter_subset_right Set.inter_subset_right
  have hMeasurable :
      ∀ cell ∈ selected,
        MeasurableSet
          (fineShading.union ∩ wz1PaperGridCube scale cell) := by
    intro cell _
    exact (measurableSet_shading_union fineShading).inter
      (wz1PaperGridCube_measurable cell)
  rw [MeasureTheory.measure_biUnion_finset hDisjoint hMeasurable]
  calc
    (∑ cell ∈ selected,
        volume (fineShading.union ∩ wz1PaperGridCube scale cell)) =
        ∑ _cell ∈ selected, balanced.cellMass := by
      apply Finset.sum_congr rfl
      intro cell hcell
      exact balanced.fine_cell_mass cell (hselected hcell)
    _ = (selected.card : ENNReal) * balanced.cellMass := by
      simp [Finset.sum_const]

/-- The selected-cell identity through the Node 5-private receipt. -/
theorem PureWZ2Node5BalancedCoverData.selected_cells_volume
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily scale}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {base : PureWZ2BalancedCoverData cover fineShading coarseShading}
    (balanced : PureWZ2Node5BalancedCoverData base)
    (selected : Finset (ℤ × ℤ × ℤ))
    (hselected : selected ⊆ balanced.activeCells) :
    volume
        (fineShading.union ∩
          ⋃ cell ∈ selected, wz1PaperGridCube scale cell) =
      (selected.card : ENNReal) * balanced.cellMass :=
  base.selected_cells_volume selected hselected

end Kakeya.Assouad
