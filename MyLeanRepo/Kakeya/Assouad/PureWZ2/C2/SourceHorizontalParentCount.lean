import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalParents
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineParentCount
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedTripartiteFiber
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LipschitzGraphFrostman

/-!
# Counting fixed-line cells inside one second-stage parent
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Number of original side-`delta` y-layers which can meet one
side-`sqrt rho` parent. -/
def pureWZ2SourceFixedLineParentYBound (delta rho : ℝ) : ℕ :=
  Nat.ceil
      ((Real.sqrt rho + delta) /
        (delta / Real.sqrt 3)) + 1

/-- Number of fixed-height, fixed-global-`delta`-bin source cells which can
map to one side-`sqrt rho` parent. -/
def pureWZ2SourceFixedLineParentFiberBound (delta rho : ℝ) : ℕ :=
  2 * pureWZ2SourceFixedLineParentYBound delta rho

theorem PureWZ2SourceHorizontalFixedBinParentData.fiber_card
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    (parents : PureWZ2SourceHorizontalFixedBinParentData line)
    (parent : ℤ × ℤ × ℤ) :
    (line.heavyCells.filter fun cell => parents.parentCell cell = parent).card ≤
      pureWZ2SourceFixedLineParentFiberBound delta rho := by
  let scale := delta
  let sqrtScale := twoScale.sqrtRequested.1
  have hscale : 0 < scale := source.extremal.delta_pos
  have hscaleOne : scale ≤ 1 := source.extremal.delta_le_one
  have hsqrtScale : 0 < sqrtScale := by
    rw [show sqrtScale = Real.sqrt rho from twoScale.sqrtRequested_eq]
    exact Real.sqrt_pos.2 line.rho_pos
  let fiber := line.heavyCells.filter fun cell => parents.parentCell cell = parent
  let yIndex : (ℤ × ℤ × ℤ) → ℤ := fun cell => cell.2.1
  let ys := fiber.image yIndex
  have hfiberByY : fiber.card ≤ 2 * ys.card := by
    apply Finset.card_le_mul_card_image fiber 2
    intro y hy
    let yFiber := fiber.filter fun cell => yIndex cell = y
    have hsubsetX :
        yFiber.image (fun cell => cell.1) ⊆
          Classical.choose
            (wz1Lemma23_global_bin_x_bound
              scale hscale window.windowed.global.extendedSlope y
              (Int.floor
                (line.lineHeight / gridSide (scale / 2)))
              line.lineBin) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨cell, hcell, rfl⟩
      have hcellFiber := (Finset.mem_filter.mp hcell).1
      have hyCell := (Finset.mem_filter.mp hcell).2
      have hheavy := (Finset.mem_filter.mp hcellFiber).1
      have hslice := line.heavyCells_subset hheavy
      have hslice' :
          cell ∈ wz1Lemma23ExactSliceCells window.shading scale hscale
            line.lineHeight := by
        simpa [line.sliceCells_eq] using hslice
      have hz :
          cell.2.2 = Int.floor (line.lineHeight / gridSide (scale / 2)) :=
        wz1Lemma23ExactSliceCells_height window.shading hscale
          line.lineHeight hslice'
      have hbin :
          wz1Lemma23SnappedGlobalBin scale
              window.windowed.global.extendedSlope cell = line.lineBin := by
        have hlabel :
            Int.floor
              (wz1Lemma23GlobalCoordinate
                  window.windowed.global.extendedSlope
                  (wz1Lemma23CellCenter scale cell) / scale) =
              line.lineBin := by
          have hdef := congrArg (fun s => cell ∈ s) line.heavyCells_eq
          rw [hdef] at hheavy
          exact (Finset.mem_filter.mp hheavy).2
        simpa [wz1Lemma23SnappedGlobalBin,
          wz1Lemma23SnappedPoint] using hlabel
      have hmem :=
        (Classical.choose_spec
          (wz1Lemma23_global_bin_x_bound
            scale hscale window.windowed.global.extendedSlope y
            (Int.floor (line.lineHeight / gridSide (scale / 2)))
            line.lineBin)).1 cell.1
      apply hmem.mpr
      have htuple :
          (cell.1, y, Int.floor (line.lineHeight / gridSide (scale / 2))) =
            cell := by
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact hyCell.symm
          · exact hz.symm
      rw [htuple]
      exact hbin
    have hxCard :
        (yFiber.image (fun cell => cell.1)).card ≤ 2 := by
      exact (Finset.card_le_card hsubsetX).trans
        (Classical.choose_spec
          (wz1Lemma23_global_bin_x_bound
            scale hscale window.windowed.global.extendedSlope y
            (Int.floor (line.lineHeight / gridSide (scale / 2)))
            line.lineBin)).2
    have hinjective : Set.InjOn (fun cell : ℤ × ℤ × ℤ => cell.1) yFiber := by
      intro first hfirst second hsecond heq
      have hyFirst := (Finset.mem_filter.mp hfirst).2
      have hySecond := (Finset.mem_filter.mp hsecond).2
      have hfirstFiber := (Finset.mem_filter.mp hfirst).1
      have hsecondFiber := (Finset.mem_filter.mp hsecond).1
      have hfirstHeavy := (Finset.mem_filter.mp hfirstFiber).1
      have hsecondHeavy := (Finset.mem_filter.mp hsecondFiber).1
      have hzFirst := wz1Lemma23ExactSliceCells_height window.shading hscale
        line.lineHeight (by
          have := line.heavyCells_subset hfirstHeavy
          simpa [line.sliceCells_eq] using this)
      have hzSecond := wz1Lemma23ExactSliceCells_height window.shading hscale
        line.lineHeight (by
          have := line.heavyCells_subset hsecondHeavy
          simpa [line.sliceCells_eq] using this)
      apply Prod.ext
      · exact heq
      · apply Prod.ext
        · exact hyFirst.trans hySecond.symm
        · exact hzFirst.trans hzSecond.symm
    rw [← Finset.card_image_of_injOn hinjective]
    exact hxCard
  have hysReal :
      (ys.card : ℝ) ≤
        (sqrtScale + scale) / (scale / Real.sqrt 3) + 1 := by
    by_cases hysEmpty : ys = ∅
    · simp [hysEmpty]
      positivity
    · have hysNonempty : ys.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hysEmpty
      let yValue : ℤ → ℝ := fun y =>
        ((y : ℝ) + 1 / 2) * gridSide (scale / 2)
      let values := ys.image yValue
      have hvalueInjective : Function.Injective yValue := by
        intro first second heq
        have hside : 0 < gridSide (scale / 2) := by
          simp [gridSide]
          positivity
        have hcast : (first : ℝ) = (second : ℝ) := by
          dsimp only [yValue] at heq
          have := mul_right_cancel₀ hside.ne' heq
          linarith
        exact_mod_cast hcast
      have hvaluesNonempty : values.Nonempty := hysNonempty.image yValue
      have hvaluesCard : values.card = ys.card :=
        Finset.card_image_of_injective ys hvalueInjective
      have hrange :
          ∀ value ∈ values,
            (parent.2.1 : ℝ) * sqrtScale - scale / 2 ≤ value ∧
              value ≤ ((parent.2.1 : ℝ) + 1) * sqrtScale + scale / 2 := by
        intro value hvalue
        rcases Finset.mem_image.mp hvalue with ⟨y, hy, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨cell, hcell, hyCell⟩
        have hcellFiber := (Finset.mem_filter.mp hcell).1
        have hparent := (Finset.mem_filter.mp hcell).2
        have hheavy := hcellFiber
        have hrepParent := parents.representative_mem_parent cell hheavy
        rw [hparent] at hrepParent
        rw [wz1PaperGridCube_eq_Ico
          twoScale.fine.coarse_extremal.delta_pos parent] at hrepParent
        have hrepIndex := line.representative_index cell hheavy
        have hclose :=
          ((wz1_lemma23_snapped_cell_geometry scale hscale hscaleOne).2.1
            cell (line.representative cell) hrepIndex).1 (1 : Fin 3)
        have hsnapY :
            (wz1Lemma23CellCenter scale cell) 1 = yValue y := by
          rw [← hyCell]
          simp [yIndex, yValue, wz1Lemma23CellCenter, point3]
        rw [hsnapY] at hclose
        exact ⟨by
          have := hrepParent.2.2.1
          linarith [abs_le.mp hclose], by
          have := hrepParent.2.2.2.1
          linarith [abs_le.mp hclose]⟩
      have hsep :
          ∀ first ∈ values, ∀ second ∈ values, first ≠ second →
            scale / Real.sqrt 3 ≤ |first - second| := by
        intro first hfirst second hsecond hne
        rcases Finset.mem_image.mp hfirst with ⟨firstY, _, rfl⟩
        rcases Finset.mem_image.mp hsecond with ⟨secondY, _, rfl⟩
        have hyNe : firstY ≠ secondY := by
          intro h
          exact hne (congrArg yValue h)
        have hint : (1 : ℝ) ≤ |((firstY - secondY : ℤ) : ℝ)| := by
          rw [← Int.cast_abs]
          exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hyNe)
        have hside : gridSide (scale / 2) = scale / Real.sqrt 3 := by
          simp [gridSide]
          ring
        dsimp only [yValue]
        rw [show
          (((firstY : ℝ) + 1 / 2) * gridSide (scale / 2) -
              ((secondY : ℝ) + 1 / 2) * gridSide (scale / 2)) =
            ((firstY - secondY : ℤ) : ℝ) * gridSide (scale / 2) by
              push_cast; ring]
        rw [abs_mul, hside, abs_of_pos (by positivity : 0 < scale / Real.sqrt 3)]
        exact le_mul_of_one_le_left (by positivity) hint
      have hcount := lemma23_separated_real_finset_card_le
        (by positivity : 0 < scale / Real.sqrt 3)
        hvaluesNonempty hrange hsep
      rw [hvaluesCard] at hcount
      convert hcount using 1 <;> ring
  have hysNat : ys.card ≤ pureWZ2SourceFixedLineParentYBound scale rho := by
    have hceil :
        (sqrtScale + scale) / (scale / Real.sqrt 3) + 1 ≤
          (pureWZ2SourceFixedLineParentYBound scale rho : ℝ) := by
      rw [show sqrtScale = Real.sqrt rho from twoScale.sqrtRequested_eq]
      dsimp only [pureWZ2SourceFixedLineParentYBound]
      have hbase :
          (Real.sqrt rho + scale) / (scale / Real.sqrt 3) ≤
            (Nat.ceil ((Real.sqrt rho + scale) /
              (scale / Real.sqrt 3)) : ℝ) :=
        Nat.le_ceil _
      have hadd := add_le_add_right hbase (1 : ℝ)
      simpa [add_comm] using hadd
    exact_mod_cast hysReal.trans hceil
  exact hfiberByY.trans (by
    dsimp only [pureWZ2SourceFixedLineParentFiberBound]
    exact Nat.mul_le_mul_left 2 hysNat)

/-- All heavy fixed-line cells are covered by the actual parent image. -/
theorem PureWZ2SourceHorizontalFixedBinParentData.heavy_card
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    (parents : PureWZ2SourceHorizontalFixedBinParentData line) :
    line.heavyCells.card ≤
      pureWZ2SourceFixedLineParentFiberBound delta rho *
        parents.parents.card := by
  rw [parents.parents_eq]
  exact Finset.card_le_mul_card_image line.heavyCells
    (pureWZ2SourceFixedLineParentFiberBound delta rho)
    (fun parent _ => parents.fiber_card parent)

/-- Compatibility name for the maximal-bin parent interface. -/
theorem PureWZ2SourceHorizontalParentData.fiber_card
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    (parents : PureWZ2SourceHorizontalParentData line)
    (parent : ℤ × ℤ × ℤ) :
    (line.heavyCells.filter fun cell => parents.parentCell cell = parent).card ≤
      pureWZ2SourceFixedLineParentFiberBound delta rho :=
  PureWZ2SourceHorizontalFixedBinParentData.fiber_card parents parent

/-- Compatibility name for the maximal-bin parent interface. -/
theorem PureWZ2SourceHorizontalParentData.heavy_card
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    (parents : PureWZ2SourceHorizontalParentData line) :
    line.heavyCells.card ≤
      pureWZ2SourceFixedLineParentFiberBound delta rho *
        parents.parents.card :=
  PureWZ2SourceHorizontalFixedBinParentData.heavy_card parents

end Kakeya.Assouad
