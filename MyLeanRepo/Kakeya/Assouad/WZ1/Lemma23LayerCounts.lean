import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LipschitzGraphFrostman
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedGlobalPackage

/-!
# Occupied y-layer and height-layer counts for WZ1 Lemma 23

After the actual y-residue selection, distinct occupied y-layers are
`sqrt rho` apart and all active cell centers lie in a fixed bounded interval.
The paper height-window condition similarly places all occupied snapped
heights in one interval of length `sqrt rho`, while the fine z-grid spacing is
`rho / sqrt 3`.
-/

namespace Kakeya.Assouad

noncomputable section

/-- The real snapped y-values occupied by one actual cell family. -/
def wz1Lemma23SnappedYValues
    (rho : ℝ) (cells : Finset (ℤ × ℤ × ℤ)) : Finset ℝ :=
  (wz1Lemma23SnappedYLayers cells).image
    (wz1Lemma23SnappedYValue rho)

/-- The real snapped height values occupied by one actual cell family. -/
def wz1Lemma23SnappedHeightValues
    (rho : ℝ) (cells : Finset (ℤ × ℤ × ℤ)) : Finset ℝ :=
  (wz1Lemma23SnappedHeights cells).image
    (wz1Lemma23SnappedBaseHeight rho)

lemma wz1Lemma23SnappedYValue_injective
    {rho : ℝ} (hrho : 0 < rho) :
    Function.Injective (wz1Lemma23SnappedYValue rho) := by
  intro first second h
  have hside : 0 < gridSide (rho / 2) := by
    simp [gridSide]
    positivity
  have hreal :
      ((first : ℝ) + 1 / 2) * gridSide (rho / 2) =
        ((second : ℝ) + 1 / 2) * gridSide (rho / 2) := by
    simpa [wz1Lemma23SnappedYValue,
      wz1Lemma23CellCenter, point3] using h
  have hsum :
      (first : ℝ) + 1 / 2 =
        (second : ℝ) + 1 / 2 :=
    mul_right_cancel₀ hside.ne' hreal
  have hcast : (first : ℝ) = (second : ℝ) := by
    linarith
  exact_mod_cast hcast

private lemma wz1Lemma23SnappedBaseHeight_injective
    {rho : ℝ} (hrho : 0 < rho) :
    Function.Injective (wz1Lemma23SnappedBaseHeight rho) := by
  intro first second h
  have hside : 0 < gridSide (rho / 2) := by
    simp [gridSide]
    positivity
  have hsum :
      (first : ℝ) + 1 / 2 =
        (second : ℝ) + 1 / 2 :=
    mul_right_cancel₀ hside.ne'
      (by simpa [wz1Lemma23SnappedBaseHeight] using h)
  have hcast : (first : ℝ) = (second : ℝ) := by
    linarith
  exact_mod_cast hcast

/-- The real y-value image has the same cardinality as the y-layer set. -/
lemma wz1Lemma23_snappedYValues_card
    {rho : ℝ} (hrho : 0 < rho)
    (cells : Finset (ℤ × ℤ × ℤ)) :
    (wz1Lemma23SnappedYValues rho cells).card =
      (wz1Lemma23SnappedYLayers cells).card := by
  exact Finset.card_image_of_injective
    _ (wz1Lemma23SnappedYValue_injective hrho)

/-- The real height-value image has the same cardinality as the height set. -/
lemma wz1Lemma23_snappedHeightValues_card
    {rho : ℝ} (hrho : 0 < rho)
    (cells : Finset (ℤ × ℤ × ℤ)) :
    (wz1Lemma23SnappedHeightValues rho cells).card =
      (wz1Lemma23SnappedHeights cells).card := by
  exact Finset.card_image_of_injective
    _ (wz1Lemma23SnappedBaseHeight_injective hrho)

/--
Selected actual y-layers have cardinality at most `4 / sqrt rho`.
-/
theorem wz1Lemma23_y_layer_count_of_coord
    {delta rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hcoord : ∀ point ∈ Y.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1)
    {cells : Finset (ℤ × ℤ × ℤ)}
    (hactive :
      cells ⊆ wz1Lemma23ActiveCells Y rho hrho)
    (hySeparated :
      ∀ first ∈ cells, ∀ second ∈ cells,
        first.2.1 = second.2.1 ∨
          Real.sqrt rho ≤
            |(wz1Lemma23CellCenter rho first) 1 -
              (wz1Lemma23CellCenter rho second) 1|) :
    ((wz1Lemma23SnappedYLayers cells).card : ℝ) ≤
      4 / Real.sqrt rho := by
  let values := wz1Lemma23SnappedYValues rho cells
  by_cases hvalues : values = ∅
  · have hlayers : wz1Lemma23SnappedYLayers cells = ∅ := by
      by_contra hne
      rcases Finset.nonempty_iff_ne_empty.mpr hne with
        ⟨y, hy⟩
      have : wz1Lemma23SnappedYValue rho y ∈ values :=
        Finset.mem_image.mpr ⟨y, hy, rfl⟩
      rw [hvalues] at this
      simpa using this
    simp [hlayers]
    positivity
  · have hnonempty : values.Nonempty := by
      simpa [Finset.nonempty_iff_ne_empty] using hvalues
    have hrange :
        ∀ value ∈ values, (-3 / 2 : ℝ) ≤ value ∧ value ≤ 3 / 2 := by
      intro value hvalue
      rcases Finset.mem_image.mp hvalue with
        ⟨y, hy, rfl⟩
      rcases Finset.mem_image.mp hy with
        ⟨idx, hidx, rfl⟩
      have hcoord :=
        wz1Lemma23_active_cell_center_coord_bound_of_coord
          hrho hrho_one hcoord (hactive hidx) 1
      have hvalue :
          wz1Lemma23SnappedYValue rho idx.2.1 =
            (wz1Lemma23SnappedPoint rho idx) (1 : Fin 3) := by
        simp [wz1Lemma23SnappedYValue,
          wz1Lemma23SnappedPoint,
          wz1Lemma23CellCenter, point3]
      rw [hvalue]
      have hbounds := abs_le.mp hcoord
      constructor <;> linarith
    have hsep :
        ∀ first ∈ values, ∀ second ∈ values,
          first ≠ second →
            Real.sqrt rho ≤ |first - second| := by
      intro first hfirst second hsecond hne
      rcases Finset.mem_image.mp hfirst with
        ⟨firstY, hfirstY, rfl⟩
      rcases Finset.mem_image.mp hsecond with
        ⟨secondY, hsecondY, rfl⟩
      rcases Finset.mem_image.mp hfirstY with
        ⟨firstIdx, hfirstIdx, hfirstIndex⟩
      rcases Finset.mem_image.mp hsecondY with
        ⟨secondIdx, hsecondIdx, hsecondIndex⟩
      have hyNe : firstIdx.2.1 ≠ secondIdx.2.1 := by
        intro hy
        apply hne
        have hindex : firstY = secondY := by
          rw [← hfirstIndex, ← hsecondIndex, hy]
        exact congr_arg
          (wz1Lemma23SnappedYValue rho) hindex
      rcases
          hySeparated firstIdx hfirstIdx
            secondIdx hsecondIdx with hsame | hseparated
      · exact False.elim (hyNe hsame)
      · have hfirstValue :
            wz1Lemma23SnappedYValue rho firstY =
              (wz1Lemma23CellCenter rho firstIdx) 1 := by
          simp [wz1Lemma23SnappedYValue,
            wz1Lemma23CellCenter, point3, ← hfirstIndex]
        have hsecondValue :
            wz1Lemma23SnappedYValue rho secondY =
              (wz1Lemma23CellCenter rho secondIdx) 1 := by
          simp [wz1Lemma23SnappedYValue,
            wz1Lemma23CellCenter, point3, ← hsecondIndex]
        rw [hfirstValue, hsecondValue]
        exact hseparated
    have hcount :=
      lemma23_separated_real_finset_card_le
        (Real.sqrt_pos.mpr hrho) hnonempty hrange hsep
    rw [wz1Lemma23_snappedYValues_card hrho cells] at hcount
    have hsqrtPos : 0 < Real.sqrt rho :=
      Real.sqrt_pos.mpr hrho
    have hone : 1 ≤ 1 / Real.sqrt rho := by
      exact one_le_one_div hsqrtPos
        (Real.sqrt_le_one.mpr hrho_one)
    calc
      ((wz1Lemma23SnappedYLayers cells).card : ℝ)
          ≤ ((3 / 2 : ℝ) - (-3 / 2 : ℝ)) /
              Real.sqrt rho + 1 := hcount
      _ = 3 / Real.sqrt rho + 1 := by ring
      _ ≤ 3 / Real.sqrt rho + 1 / Real.sqrt rho := by
        gcongr
      _ = 4 / Real.sqrt rho := by ring

/-- Historical unit-ball wrapper. -/
theorem wz1Lemma23_y_layer_count
    {delta rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    {cells : Finset (ℤ × ℤ × ℤ)}
    (hactive : cells ⊆ wz1Lemma23ActiveCells Y rho hrho)
    (hySeparated :
      ∀ first ∈ cells, ∀ second ∈ cells,
        first.2.1 = second.2.1 ∨
          Real.sqrt rho ≤
            |(wz1Lemma23CellCenter rho first) 1 -
              (wz1Lemma23CellCenter rho second) 1|) :
    ((wz1Lemma23SnappedYLayers cells).card : ℝ) ≤
      4 / Real.sqrt rho := by
  apply wz1Lemma23_y_layer_count_of_coord
    hrho hrho_one _ hactive hySeparated
  intro point hpoint coordinate
  have hnorm : ‖point‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hball hpoint
  exact (PiLp.norm_apply_le point coordinate).trans hnorm

/--
Actual snapped heights in one paper window have cardinality at most
`3 / sqrt rho`.
-/
theorem wz1Lemma23_height_layer_count
    {rho : ℝ} (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    {cells : Finset (ℤ × ℤ × ℤ)}
    (hwindow : WZ1Lemma23SingleHeightWindow rho cells) :
    ((wz1Lemma23SnappedHeights cells).card : ℝ) ≤
      3 / Real.sqrt rho := by
  let values := wz1Lemma23SnappedHeightValues rho cells
  by_cases hvalues : values = ∅
  · have hlayers : wz1Lemma23SnappedHeights cells = ∅ := by
      by_contra hne
      rcases Finset.nonempty_iff_ne_empty.mpr hne with
        ⟨z, hz⟩
      have : wz1Lemma23SnappedBaseHeight rho z ∈ values :=
        Finset.mem_image.mpr ⟨z, hz, rfl⟩
      rw [hvalues] at this
      simpa using this
    simp [hlayers]
    positivity
  · rcases hwindow with ⟨left, hwindow⟩
    have hnonempty : values.Nonempty := by
      simpa [Finset.nonempty_iff_ne_empty] using hvalues
    have hrange :
        ∀ value ∈ values,
          left ≤ value ∧ value ≤ left + Real.sqrt rho := by
      intro value hvalue
      rcases Finset.mem_image.mp hvalue with
        ⟨heightIndex, hheightIndex, rfl⟩
      rcases Finset.mem_image.mp hheightIndex with
        ⟨idx, hidx, hidxHeight⟩
      have hidxWindow := hwindow idx hidx
      simpa [wz1Lemma23SnappedBaseHeight,
        wz1Lemma23SnappedPoint,
        wz1Lemma23CellCenter, point3, hidxHeight] using
          hidxWindow
    have hsep :
        ∀ first ∈ values, ∀ second ∈ values,
          first ≠ second →
            rho / Real.sqrt 3 ≤ |first - second| := by
      intro first hfirst second hsecond hne
      rcases Finset.mem_image.mp hfirst with
        ⟨firstIndex, hfirstIndex, rfl⟩
      rcases Finset.mem_image.mp hsecond with
        ⟨secondIndex, hsecondIndex, rfl⟩
      have hindexNe : firstIndex ≠ secondIndex := by
        intro h
        exact hne (congr_arg
          (wz1Lemma23SnappedBaseHeight rho) h)
      have hdiff :
          firstIndex - secondIndex ≠ 0 :=
        sub_ne_zero.mpr hindexNe
      have hint :
          (1 : ℝ) ≤ |((firstIndex - secondIndex : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hdiff
      have hside : 0 < gridSide (rho / 2) := by
        simp [gridSide]
        positivity
      have hformula :
          wz1Lemma23SnappedBaseHeight rho firstIndex -
              wz1Lemma23SnappedBaseHeight rho secondIndex =
            ((firstIndex - secondIndex : ℤ) : ℝ) *
              gridSide (rho / 2) := by
        simp [wz1Lemma23SnappedBaseHeight]
        ring
      rw [hformula, abs_mul, abs_of_pos hside]
      have hgrid :
          gridSide (rho / 2) = rho / Real.sqrt 3 := by
        simp [gridSide]
        ring
      rw [hgrid]
      nlinarith
    have hcount :=
      lemma23_separated_real_finset_card_le
        (by positivity : 0 < rho / Real.sqrt 3)
        hnonempty hrange hsep
    rw [wz1Lemma23_snappedHeightValues_card hrho cells] at hcount
    have hsqrtPos : 0 < Real.sqrt rho :=
      Real.sqrt_pos.mpr hrho
    have hsqrt3 : 0 < Real.sqrt 3 :=
      Real.sqrt_pos.mpr (by norm_num)
    have hratio :
        Real.sqrt rho / (rho / Real.sqrt 3) =
          Real.sqrt 3 / Real.sqrt rho := by
      field_simp [hsqrtPos.ne', hsqrt3.ne']
      nlinarith [Real.sq_sqrt hrho.le]
    have hsqrt3LeTwo : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sqrt_nonneg 3,
        Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have hone : 1 ≤ 1 / Real.sqrt rho := by
      exact one_le_one_div hsqrtPos
        (Real.sqrt_le_one.mpr hrho_one)
    calc
      ((wz1Lemma23SnappedHeights cells).card : ℝ)
          ≤ ((left + Real.sqrt rho) - left) /
              (rho / Real.sqrt 3) + 1 := hcount
      _ = Real.sqrt 3 / Real.sqrt rho + 1 := by
        rw [show (left + Real.sqrt rho) - left =
          Real.sqrt rho by ring, hratio]
      _ ≤ 2 / Real.sqrt rho + 1 := by
        gcongr
      _ ≤ 2 / Real.sqrt rho + 1 / Real.sqrt rho := by
        gcongr
      _ = 3 / Real.sqrt rho := by ring

end

end Kakeya.Assouad
