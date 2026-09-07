import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.FixedLineCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineParentCount
import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers

/-!
# Carrier-generic fixed-line parent-y packing

The packing argument bounding the number of side-`root` paper cubes over one
parent y-index uses only the fixed-line geometry and a representative in each
parent.  In particular, it is independent of whether the fixed line was
selected before or after a height-popularity restriction.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- At most 45 side-`root` parents met by one fixed line occur over one parent
y-index.  The theorem is deliberately carrier-generic. -/
theorem pureWZ2_fixedLine_parent_y_fiber_card
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) shading C}
    {slope : ℝ → ℝ}
    (line : PureWZ2HorizontalFixedBinCore windowed slope)
    (root : ℝ) (hroot : 0 < root) (hrhoRoot : rho ≤ root)
    (hslope : |slope line.lineHeight| ≤ 3)
    (parents : Finset (ℤ × ℤ × ℤ))
    (parentCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ))
    (parent_hit : ∀ parent ∈ parents,
      ∃ cell ∈ line.heavyCells, parentCell cell = parent)
    (representative_mem_parent :
      ∀ cell ∈ line.heavyCells,
        line.representative cell ∈
          wz1PaperGridCube root (parentCell cell))
    (y : ℤ) :
    (parents.filter fun parent => parent.2.1 = y).card ≤ 45 := by
  let fiber := parents.filter fun parent => parent.2.1 = y
  change fiber.card ≤ 45
  by_cases hfiber : fiber = ∅
  · rw [hfiber]
    simp
  have hfiberNonempty : fiber.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hfiber
  let first := Classical.choose hfiberNonempty
  have hfirstFiber : first ∈ fiber := Classical.choose_spec hfiberNonempty
  have hfirstParent : first ∈ parents :=
    (Finset.mem_filter.mp hfirstFiber).1
  have hfirstY : first.2.1 = y :=
    (Finset.mem_filter.mp hfirstFiber).2
  let cellFor (parent : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
    if hparent : parent ∈ parents then
      Classical.choose (parent_hit parent hparent)
    else (0, 0, 0)
  have hcellForMem :
      ∀ parent (hparent : parent ∈ parents),
        cellFor parent ∈ line.heavyCells := by
    intro parent hparent
    simp only [cellFor, dif_pos hparent]
    exact (Classical.choose_spec (parent_hit parent hparent)).1
  have hcellForParent :
      ∀ parent (hparent : parent ∈ parents),
        parentCell (cellFor parent) = parent := by
    intro parent hparent
    simp only [cellFor, dif_pos hparent]
    exact (Classical.choose_spec (parent_hit parent hparent)).2
  let representative (parent : ℤ × ℤ × ℤ) : Point3 :=
    line.representative (cellFor parent)
  have hrepresentativeMem :
      ∀ parent (hparent : parent ∈ parents),
        representative parent ∈ wz1PaperGridCube root parent := by
    intro parent hparent
    have hmem := representative_mem_parent
      (cellFor parent) (hcellForMem parent hparent)
    rwa [hcellForParent parent hparent] at hmem
  have hnear :
      ∀ parent (hparent : parent ∈ parents),
        |inner ℝ (representative parent)
              (globalGrainDirection (slope line.lineHeight)) -
            line.lineLevel| ≤ 9 * rho := by
    intro parent hparent
    exact line.heavy_representative_near_line
      (cellFor parent) (hcellForMem parent hparent)
  have hindexRange :
      ∀ parent ∈ fiber,
        first.1 - 22 ≤ parent.1 ∧ parent.1 ≤ first.1 + 22 := by
    intro parent hparentFiber
    have hparent : parent ∈ parents :=
      (Finset.mem_filter.mp hparentFiber).1
    have hparentY : parent.2.1 = y :=
      (Finset.mem_filter.mp hparentFiber).2
    have hparentMem := hrepresentativeMem parent hparent
    have hfirstMem := hrepresentativeMem first hfirstParent
    rw [wz1PaperGridCube_eq_Ico hroot parent] at hparentMem
    rw [wz1PaperGridCube_eq_Ico hroot first] at hfirstMem
    have hyClose :
        |representative parent 1 - representative first 1| ≤ root := by
      apply le_of_lt
      rw [abs_lt]
      have hparentLower := hparentMem.2.2.1
      have hparentUpper := hparentMem.2.2.2.1
      have hfirstLower := hfirstMem.2.2.1
      have hfirstUpper := hfirstMem.2.2.2.1
      rw [hparentY] at hparentLower hparentUpper
      rw [hfirstY] at hfirstLower hfirstUpper
      constructor <;> linarith
    have hcoordClose :
        |inner ℝ (representative parent)
              (globalGrainDirection (slope line.lineHeight)) -
            inner ℝ (representative first)
              (globalGrainDirection (slope line.lineHeight))| ≤
          18 * rho := by
      have htriangle := abs_sub
        (inner ℝ (representative parent)
          (globalGrainDirection (slope line.lineHeight)) - line.lineLevel)
        (inner ℝ (representative first)
          (globalGrainDirection (slope line.lineHeight)) - line.lineLevel)
      have hrewrite :
          (inner ℝ (representative parent)
              (globalGrainDirection (slope line.lineHeight)) - line.lineLevel) -
          (inner ℝ (representative first)
              (globalGrainDirection (slope line.lineHeight)) - line.lineLevel) =
          inner ℝ (representative parent)
              (globalGrainDirection (slope line.lineHeight)) -
            inner ℝ (representative first)
              (globalGrainDirection (slope line.lineHeight)) := by
        ring
      rw [hrewrite] at htriangle
      exact htriangle.trans (by
        have hp := hnear parent hparent
        have hf := hnear first hfirstParent
        linarith)
    have hxClose :
        |representative parent 0 - representative first 0| ≤ 21 * root := by
      have hformula :
          inner ℝ (representative parent)
                (globalGrainDirection (slope line.lineHeight)) -
              inner ℝ (representative first)
                (globalGrainDirection (slope line.lineHeight)) =
            (representative parent 0 - representative first 0) +
              slope line.lineHeight *
                (representative parent 1 - representative first 1) := by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
        ring
      rw [hformula] at hcoordClose
      have hsolve :
          |representative parent 0 - representative first 0| ≤
            |(representative parent 0 - representative first 0) +
                slope line.lineHeight *
                  (representative parent 1 - representative first 1)| +
              |slope line.lineHeight| *
                |representative parent 1 - representative first 1| := by
        have h := abs_sub
          ((representative parent 0 - representative first 0) +
            slope line.lineHeight *
              (representative parent 1 - representative first 1))
          (slope line.lineHeight *
            (representative parent 1 - representative first 1))
        simpa [abs_mul] using h
      calc
        |representative parent 0 - representative first 0| ≤ _ := hsolve
        _ ≤ 18 * rho + 3 * root := by gcongr
        _ ≤ 21 * root := by nlinarith
    have hparentLowerReal :
        (first.1 : ℝ) - 22 ≤ (parent.1 : ℝ) := by
      have hfirstLower := hfirstMem.1
      have hx := (abs_le.mp hxClose).1
      have hmul :
          ((first.1 : ℝ) - 21) * root <
            ((parent.1 : ℝ) + 1) * root := by
        calc
          ((first.1 : ℝ) - 21) * root
              = (first.1 : ℝ) * root - 21 * root := by ring
          _ ≤ representative first 0 - 21 * root := by linarith
          _ ≤ representative parent 0 := by linarith
          _ < ((parent.1 : ℝ) + 1) * root := hparentMem.2.1
      have hindex :
          (first.1 : ℝ) - 21 < (parent.1 : ℝ) + 1 :=
        lt_of_mul_lt_mul_right hmul hroot.le
      linarith
    have hparentUpperReal :
        (parent.1 : ℝ) ≤ (first.1 : ℝ) + 22 := by
      have hparentLower := hparentMem.1
      have hfirstUpper := hfirstMem.2.1
      have hx := (abs_le.mp hxClose).2
      have hmul :
          (parent.1 : ℝ) * root <
            ((first.1 : ℝ) + 22) * root := by
        calc
          (parent.1 : ℝ) * root ≤ representative parent 0 := hparentLower
          _ ≤ representative first 0 + 21 * root := by linarith
          _ < ((first.1 : ℝ) + 1) * root + 21 * root := by linarith
          _ = ((first.1 : ℝ) + 22) * root := by ring
      exact (lt_of_mul_lt_mul_right hmul hroot.le).le
    exact ⟨by exact_mod_cast hparentLowerReal,
      by exact_mod_cast hparentUpperReal⟩
  have himageSubset :
      fiber.image (fun parent => parent.1) ⊆
        Finset.Icc (first.1 - 22) (first.1 + 22) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨parent, hparent, rfl⟩
    exact Finset.mem_Icc.mpr (hindexRange parent hparent)
  have hparentHeight :
      ∀ parent ∈ parents, parent.2.2 = first.2.2 := by
    intro parent hparent
    have hparentIndex :
        wz1PaperGridIndex root (representative parent) = parent :=
      (mem_wz1PaperGridCube root parent _).mp
        (hrepresentativeMem parent hparent)
    have hfirstIndex :
        wz1PaperGridIndex root (representative first) = first :=
      (mem_wz1PaperGridCube root first _).mp
        (hrepresentativeMem first hfirstParent)
    have hparentRepHeight :
        representative parent (2 : Fin 3) = line.lineHeight :=
      line.representative_height (cellFor parent) (hcellForMem parent hparent)
    have hfirstRepHeight :
        representative first (2 : Fin 3) = line.lineHeight :=
      line.representative_height (cellFor first) (hcellForMem first hfirstParent)
    have hz := congrArg (fun idx : ℤ × ℤ × ℤ => idx.2.2) hparentIndex
    have hzFirst := congrArg (fun idx : ℤ × ℤ × ℤ => idx.2.2) hfirstIndex
    simp [wz1PaperGridIndex, gridIndex, hparentRepHeight, hfirstRepHeight]
      at hz hzFirst
    exact hz.symm.trans hzFirst
  have hinjective : Set.InjOn (fun parent : ℤ × ℤ × ℤ => parent.1) fiber := by
    intro firstParent hfirst secondParent hsecond heq
    have hfirstY' := (Finset.mem_filter.mp hfirst).2
    have hsecondY' := (Finset.mem_filter.mp hsecond).2
    have hfirstParent' := (Finset.mem_filter.mp hfirst).1
    have hsecondParent' := (Finset.mem_filter.mp hsecond).1
    have hfirstZ := hparentHeight firstParent hfirstParent'
    have hsecondZ := hparentHeight secondParent hsecondParent'
    apply Prod.ext
    · exact heq
    · apply Prod.ext
      · exact hfirstY'.trans hsecondY'.symm
      · exact hfirstZ.trans hsecondZ.symm
  rw [← Finset.card_image_of_injOn hinjective]
  have hintervalCard :
      (Finset.Icc (first.1 - 22) (first.1 + 22)).card = 45 := by
    simp
    omega
  exact (Finset.card_le_card himageSubset).trans_eq hintervalCard

/-- At one fixed height and one fixed global bin, the number of exact
`rho`-cells assigned to one side-`root` parent is bounded by the standard
terminal fibre count.  The statement is independent of the carrier used to
select the fixed line. -/
theorem pureWZ2_fixedLine_parent_fiber_card
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) shading C}
    {slope : ℝ → ℝ}
    (line : PureWZ2HorizontalFixedBinCore windowed slope)
    (root : ℝ) (hroot : 0 < root)
    (hrootEq : root = Real.sqrt rho)
    (parentCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ))
    (representative_mem_parent :
      ∀ cell ∈ line.heavyCells, line.representative cell ∈
        wz1PaperGridCube root (parentCell cell))
    (parent : ℤ × ℤ × ℤ) :
    (line.heavyCells.filter fun cell => parentCell cell = parent).card ≤
      pureWZ2FixedLineParentFiberBound rho := by
  have hrho : 0 < rho := line.rho_pos
  let fiber := line.heavyCells.filter fun cell => parentCell cell = parent
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
              rho line.rho_pos windowed.global.extendedSlope y
              (Int.floor (line.lineHeight / gridSide (rho / 2)))
              line.lineBin) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨cell, hcell, rfl⟩
      have hcellFiber := (Finset.mem_filter.mp hcell).1
      have hyCell := (Finset.mem_filter.mp hcell).2
      have hheavy := (Finset.mem_filter.mp hcellFiber).1
      have hslice := line.heavyCells_subset hheavy
      have hslice' : cell ∈ wz1Lemma23ExactSliceCells shading rho
          line.rho_pos line.lineHeight := by
        simpa [line.sliceCells_eq] using hslice
      have hz : cell.2.2 =
          Int.floor (line.lineHeight / gridSide (rho / 2)) :=
        wz1Lemma23ExactSliceCells_height shading line.rho_pos
          line.lineHeight hslice'
      have hbin : wz1Lemma23SnappedGlobalBin rho
          windowed.global.extendedSlope cell = line.lineBin := by
        have hlabel : Int.floor
            (wz1Lemma23GlobalCoordinate windowed.global.extendedSlope
              (wz1Lemma23CellCenter rho cell) / rho) = line.lineBin := by
          have hdef := congrArg (fun s => cell ∈ s) line.heavyCells_eq
          rw [hdef] at hheavy
          exact (Finset.mem_filter.mp hheavy).2
        simpa [wz1Lemma23SnappedGlobalBin, wz1Lemma23SnappedPoint] using hlabel
      have hmem := (Classical.choose_spec
        (wz1Lemma23_global_bin_x_bound rho line.rho_pos
          windowed.global.extendedSlope y
          (Int.floor (line.lineHeight / gridSide (rho / 2)))
          line.lineBin)).1 cell.1
      apply hmem.mpr
      have htuple :
          (cell.1, y, Int.floor (line.lineHeight / gridSide (rho / 2))) =
            cell := by
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact hyCell.symm
          · exact hz.symm
      rw [htuple]
      exact hbin
    have hxCard : (yFiber.image (fun cell => cell.1)).card ≤ 2 := by
      exact (Finset.card_le_card hsubsetX).trans
        (Classical.choose_spec
          (wz1Lemma23_global_bin_x_bound rho line.rho_pos
            windowed.global.extendedSlope y
            (Int.floor (line.lineHeight / gridSide (rho / 2)))
            line.lineBin)).2
    have hinjective : Set.InjOn (fun cell : ℤ × ℤ × ℤ => cell.1) yFiber := by
      intro first hfirst second hsecond heq
      have hyFirst := (Finset.mem_filter.mp hfirst).2
      have hySecond := (Finset.mem_filter.mp hsecond).2
      have hfirstFiber := (Finset.mem_filter.mp hfirst).1
      have hsecondFiber := (Finset.mem_filter.mp hsecond).1
      have hfirstHeavy := (Finset.mem_filter.mp hfirstFiber).1
      have hsecondHeavy := (Finset.mem_filter.mp hsecondFiber).1
      have hzFirst := wz1Lemma23ExactSliceCells_height shading line.rho_pos
        line.lineHeight (by
          have := line.heavyCells_subset hfirstHeavy
          simpa [line.sliceCells_eq] using this)
      have hzSecond := wz1Lemma23ExactSliceCells_height shading line.rho_pos
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
  have hysReal : (ys.card : ℝ) ≤
      (root + rho) / (rho / Real.sqrt 3) + 1 := by
    by_cases hysEmpty : ys = ∅
    · simp [hysEmpty]
      exact add_nonneg (div_nonneg (by positivity) (by positivity)) zero_le_one
    · have hysNonempty : ys.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hysEmpty
      let yValue : ℤ → ℝ := fun y =>
        ((y : ℝ) + 1 / 2) * gridSide (rho / 2)
      let values := ys.image yValue
      have hvalueInjective : Function.Injective yValue := by
        intro first second heq
        have hside : 0 < gridSide (rho / 2) := by
          unfold gridSide
          exact div_pos (by linarith) (Real.sqrt_pos.mpr (by norm_num))
        have hcast : (first : ℝ) = (second : ℝ) := by
          dsimp only [yValue] at heq
          have := mul_right_cancel₀ hside.ne' heq
          linarith
        exact_mod_cast hcast
      have hvaluesNonempty : values.Nonempty := hysNonempty.image yValue
      have hvaluesCard : values.card = ys.card :=
        Finset.card_image_of_injective ys hvalueInjective
      have hrange : ∀ value ∈ values,
          (parent.2.1 : ℝ) * root - rho / 2 ≤ value ∧
            value ≤ ((parent.2.1 : ℝ) + 1) * root + rho / 2 := by
        intro value hvalue
        rcases Finset.mem_image.mp hvalue with ⟨y, hy, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨cell, hcell, hyCell⟩
        have hcellFiber := (Finset.mem_filter.mp hcell).1
        have hparent := (Finset.mem_filter.mp hcell).2
        have hheavy := hcellFiber
        have hrepParent := representative_mem_parent cell hheavy
        rw [hparent] at hrepParent
        rw [wz1PaperGridCube_eq_Ico hroot parent] at hrepParent
        have hrepIndex := line.representative_index cell hheavy
        have hclose :=
          ((wz1_lemma23_snapped_cell_geometry rho line.rho_pos
            line.rho_le_one).2.1 cell (line.representative cell)
            hrepIndex).1 (1 : Fin 3)
        have hsnapY : (wz1Lemma23CellCenter rho cell) 1 = yValue y := by
          rw [← hyCell]
          simp [yIndex, yValue, wz1Lemma23CellCenter, point3]
        rw [hsnapY] at hclose
        exact ⟨by
          have := hrepParent.2.2.1
          linarith [abs_le.mp hclose], by
          have := hrepParent.2.2.2.1
          linarith [abs_le.mp hclose]⟩
      have hsep : ∀ first ∈ values, ∀ second ∈ values, first ≠ second →
          rho / Real.sqrt 3 ≤ |first - second| := by
        intro first hfirst second hsecond hne
        rcases Finset.mem_image.mp hfirst with ⟨firstY, _, rfl⟩
        rcases Finset.mem_image.mp hsecond with ⟨secondY, _, rfl⟩
        have hyNe : firstY ≠ secondY := by
          intro h
          exact hne (congrArg yValue h)
        have hint : (1 : ℝ) ≤ |((firstY - secondY : ℤ) : ℝ)| := by
          rw [← Int.cast_abs]
          exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hyNe)
        have hside : gridSide (rho / 2) = rho / Real.sqrt 3 := by
          simp [gridSide]
          ring
        dsimp only [yValue]
        rw [show
          (((firstY : ℝ) + 1 / 2) * gridSide (rho / 2) -
              ((secondY : ℝ) + 1 / 2) * gridSide (rho / 2)) =
            ((firstY - secondY : ℤ) : ℝ) * gridSide (rho / 2) by
              push_cast
              ring]
        rw [abs_mul, hside,
          abs_of_pos (div_pos hrho (Real.sqrt_pos.mpr (by norm_num)))]
        exact le_mul_of_one_le_left
          (div_nonneg hrho.le (Real.sqrt_nonneg 3)) hint
      have hcount := lemma23_separated_real_finset_card_le
        (div_pos hrho (Real.sqrt_pos.mpr (by norm_num)))
        hvaluesNonempty hrange hsep
      rw [hvaluesCard] at hcount
      convert hcount using 1
      all_goals ring
  have hysNat : ys.card ≤ pureWZ2FixedLineParentYBound rho := by
    have hceil :
        (root + rho) / (rho / Real.sqrt 3) + 1 ≤
          (pureWZ2FixedLineParentYBound rho : ℝ) := by
      dsimp only [pureWZ2FixedLineParentYBound]
      rw [hrootEq]
      have hbase :
          (Real.sqrt rho + rho) / (rho / Real.sqrt 3) ≤
            (Nat.ceil ((Real.sqrt rho + rho) /
              (rho / Real.sqrt 3)) : ℝ) := Nat.le_ceil _
      have hadd := add_le_add_right hbase (1 : ℝ)
      simpa [add_comm] using hadd
    exact_mod_cast hysReal.trans hceil
  exact hfiberByY.trans (by
    dsimp only [pureWZ2FixedLineParentFiberBound]
    exact Nat.mul_le_mul_left 2 hysNat)

end Kakeya.Assouad

end
