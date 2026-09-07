import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineParentCount
import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers

/-!
# Fixed-line parent count at one coarse y-index

All selected parents have one common coarse height.  At a fixed coarse
`y`-index, their genuine exact-slice representatives lie in a bounded interval
of `x`-indices because they are all within `9 * rho` of the same horizontal
global-grain line.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- At most 45 actual parents occur over one side-`sqrt rho` y-layer. -/
theorem PureWZ2HorizontalFixedLineParentData.parent_y_fiber_card
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    (parents : PureWZ2HorizontalFixedLineParentData line)
    (y : ℤ) :
    (parents.parents.filter fun parent => parent.2.1 = y).card ≤ 45 := by
  let scale := twoScale.rhoRequested.1
  let root := twoScale.sqrtRequested.1
  let fiber := parents.parents.filter fun parent => parent.2.1 = y
  change fiber.card ≤ 45
  by_cases hfiber : fiber = ∅
  · rw [hfiber]
    simp
  have hfiberNonempty : fiber.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hfiber
  let first := Classical.choose hfiberNonempty
  have hfirstFiber : first ∈ fiber := Classical.choose_spec hfiberNonempty
  have hfirstParent : first ∈ parents.parents :=
    (Finset.mem_filter.mp hfirstFiber).1
  have hfirstY : first.2.1 = y :=
    (Finset.mem_filter.mp hfirstFiber).2
  have hscale : 0 < scale := twoScale.coarseGrains.extremal.delta_pos
  have hscaleOne : scale ≤ 1 := twoScale.rhoRequested.property.2
  have hroot : 0 < root := twoScale.fine.coarse_extremal.delta_pos
  have hscaleRoot : scale ≤ root := by
    have hsqrt : root = Real.sqrt scale := by
      calc
        root = Real.sqrt rho := twoScale.sqrtRequested_eq
        _ = Real.sqrt scale := by
          congr 1
          exact twoScale.rhoRequested_eq.symm
    rw [hsqrt]
    nlinarith [Real.sqrt_nonneg scale, Real.sq_sqrt hscale.le, hscaleOne]
  let cellFor (parent : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
    if hparent : parent ∈ parents.parents then
      Classical.choose (parents.parent_hit parent hparent)
    else (0, 0, 0)
  have hcellForMem :
      ∀ parent (hparent : parent ∈ parents.parents),
        cellFor parent ∈ line.heavyCells := by
    intro parent hparent
    simp only [cellFor, dif_pos hparent]
    exact (Classical.choose_spec (parents.parent_hit parent hparent)).1
  have hcellForParent :
      ∀ parent (hparent : parent ∈ parents.parents),
        parents.parentCell (cellFor parent) = parent := by
    intro parent hparent
    simp only [cellFor, dif_pos hparent]
    exact (Classical.choose_spec (parents.parent_hit parent hparent)).2
  let representative (parent : ℤ × ℤ × ℤ) : Point3 :=
    line.representative (cellFor parent)
  have hrepresentativeMem :
      ∀ parent (hparent : parent ∈ parents.parents),
        representative parent ∈ wz1PaperGridCube root parent := by
    intro parent hparent
    have hmem := parents.representative_mem_parent
      (cellFor parent) (hcellForMem parent hparent)
    rwa [hcellForParent parent hparent] at hmem
  have hnear :
      ∀ parent (hparent : parent ∈ parents.parents),
        |inner ℝ (representative parent)
              (globalGrainDirection
                (twoScale.coarseGrains.globalGrains.slope line.lineHeight)) -
            line.lineLevel| ≤ 9 * scale := by
    intro parent hparent
    exact line.heavy_representative_near_line
      (cellFor parent) (hcellForMem parent hparent)
  have hindexRange :
      ∀ parent ∈ fiber,
        first.1 - 22 ≤ parent.1 ∧ parent.1 ≤ first.1 + 22 := by
    intro parent hparentFiber
    have hparent : parent ∈ parents.parents :=
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
      have hwidth :
          (((y : ℝ) + 1) * root) - (y : ℝ) * root = root := by ring
      constructor
      · linarith
      · linarith
    have hcoordClose :
        |inner ℝ (representative parent)
              (globalGrainDirection
                (twoScale.coarseGrains.globalGrains.slope line.lineHeight)) -
            inner ℝ (representative first)
              (globalGrainDirection
                (twoScale.coarseGrains.globalGrains.slope line.lineHeight))| ≤
          18 * scale := by
      have htriangle := abs_sub
        (inner ℝ (representative parent)
          (globalGrainDirection
            (twoScale.coarseGrains.globalGrains.slope line.lineHeight)) -
          line.lineLevel)
        (inner ℝ (representative first)
          (globalGrainDirection
            (twoScale.coarseGrains.globalGrains.slope line.lineHeight)) -
          line.lineLevel)
      have hrewrite :
          (inner ℝ (representative parent)
              (globalGrainDirection
                (twoScale.coarseGrains.globalGrains.slope line.lineHeight)) -
            line.lineLevel) -
          (inner ℝ (representative first)
              (globalGrainDirection
                (twoScale.coarseGrains.globalGrains.slope line.lineHeight)) -
            line.lineLevel) =
          inner ℝ (representative parent)
              (globalGrainDirection
                (twoScale.coarseGrains.globalGrains.slope line.lineHeight)) -
            inner ℝ (representative first)
              (globalGrainDirection
                (twoScale.coarseGrains.globalGrains.slope line.lineHeight)) := by
        ring
      rw [hrewrite] at htriangle
      exact htriangle.trans (by
        have hp := hnear parent hparent
        have hf := hnear first hfirstParent
        linarith)
    have hslope :
        |twoScale.coarseGrains.globalGrains.slope line.lineHeight| ≤ 3 :=
      twoScale.coarseGrains_slope_bound
        line.lineHeight line.lineHeight_mem
    have hxClose :
        |representative parent 0 - representative first 0| ≤ 21 * root := by
      have hformula :
          inner ℝ (representative parent)
                (globalGrainDirection
                  (twoScale.coarseGrains.globalGrains.slope line.lineHeight)) -
              inner ℝ (representative first)
                (globalGrainDirection
                  (twoScale.coarseGrains.globalGrains.slope line.lineHeight)) =
            (representative parent 0 - representative first 0) +
              twoScale.coarseGrains.globalGrains.slope line.lineHeight *
                (representative parent 1 - representative first 1) := by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
        ring
      rw [hformula] at hcoordClose
      have hsolve :
          |representative parent 0 - representative first 0| ≤
            |(representative parent 0 - representative first 0) +
                twoScale.coarseGrains.globalGrains.slope line.lineHeight *
                  (representative parent 1 - representative first 1)| +
              |twoScale.coarseGrains.globalGrains.slope line.lineHeight| *
                |representative parent 1 - representative first 1| := by
        have h := abs_sub
          ((representative parent 0 - representative first 0) +
            twoScale.coarseGrains.globalGrains.slope line.lineHeight *
              (representative parent 1 - representative first 1))
          (twoScale.coarseGrains.globalGrains.slope line.lineHeight *
            (representative parent 1 - representative first 1))
        simpa [abs_mul] using h
      calc
        |representative parent 0 - representative first 0|
            ≤ _ := hsolve
        _ ≤ 18 * scale + 3 * root := by gcongr
        _ ≤ 21 * root := by nlinarith
    have hparentLowerReal :
        (first.1 : ℝ) - 22 ≤ (parent.1 : ℝ) := by
      have hfirstLower := hfirstMem.1
      have hfirstUpper := hfirstMem.2.1
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
          (parent.1 : ℝ) * root
              ≤ representative parent 0 := hparentLower
          _ ≤ representative first 0 + 21 * root := by linarith
          _ < ((first.1 : ℝ) + 1) * root + 21 * root := by linarith
          _ = ((first.1 : ℝ) + 22) * root := by ring
      exact (lt_of_mul_lt_mul_right hmul hroot.le).le
    exact ⟨by exact_mod_cast hparentLowerReal, by exact_mod_cast hparentUpperReal⟩
  have himageSubset :
      fiber.image (fun parent => parent.1) ⊆
        Finset.Icc (first.1 - 22) (first.1 + 22) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨parent, hparent, rfl⟩
    exact Finset.mem_Icc.mpr (hindexRange parent hparent)
  have hparentHeight :
      ∀ parent ∈ parents.parents, parent.2.2 = first.2.2 := by
    intro parent hparent
    have hparentIndex :
        wz1PaperGridIndex root (representative parent) = parent :=
      (mem_wz1PaperGridCube root parent _).mp
        (hrepresentativeMem parent hparent)
    have hfirstIndex :
        wz1PaperGridIndex root (representative first) = first :=
      (mem_wz1PaperGridCube root first _).mp
        (hrepresentativeMem first hfirstParent)
    have hparentRepHeight : representative parent (2 : Fin 3) = line.lineHeight :=
      line.representative_height (cellFor parent) (hcellForMem parent hparent)
    have hfirstRepHeight : representative first (2 : Fin 3) = line.lineHeight :=
      line.representative_height (cellFor first) (hcellForMem first hfirstParent)
    have hz := congrArg (fun idx : ℤ × ℤ × ℤ => idx.2.2) hparentIndex
    have hzFirst := congrArg (fun idx : ℤ × ℤ × ℤ => idx.2.2) hfirstIndex
    simp [wz1PaperGridIndex, gridIndex, hparentRepHeight, hfirstRepHeight] at hz hzFirst
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

end Kakeya.Assouad
