import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleParents
import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23YLayerSelection

/-!
# A separated residue of actual terminal parents

The fixed horizontal line meets only boundedly many side-`sqrt delta` parents
over one parent y-index.  We retain one genuine parent per y-index and then
one residue modulo 512.  No parent is chosen after a height-popularity
restriction and no full parent shading is reintroduced here.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- At most 45 terminal parents occur over one side-`sqrt delta` y-layer. -/
theorem PureWZ2TerminalFixedBinParentData.parent_y_fiber_card
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    (parents : PureWZ2TerminalFixedBinParentData line)
    (y : ℤ) :
    (parents.parents.filter fun parent => parent.2.1 = y).card ≤ 45 := by
  let scale := delta
  let root := terminal.sqrtRequested.1
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
  have hscale : 0 < scale := source.extremal.delta_pos
  have hscaleOne : scale ≤ 1 := source.extremal.delta_le_one
  have hroot : 0 < root := terminal.sticky.coarse_extremal.delta_pos
  have hscaleRoot : scale ≤ root := by
    have hsqrt : root = Real.sqrt scale := by
      exact terminal.sqrtRequested_eq
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
                (source.globalGrains.slope line.lineHeight)) -
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
      constructor <;> linarith
    have hcoordClose :
        |inner ℝ (representative parent)
              (globalGrainDirection
                (source.globalGrains.slope line.lineHeight)) -
            inner ℝ (representative first)
              (globalGrainDirection
                (source.globalGrains.slope line.lineHeight))| ≤
          18 * scale := by
      have htriangle := abs_sub
        (inner ℝ (representative parent)
          (globalGrainDirection
            (source.globalGrains.slope line.lineHeight)) - line.lineLevel)
        (inner ℝ (representative first)
          (globalGrainDirection
            (source.globalGrains.slope line.lineHeight)) - line.lineLevel)
      have hrewrite :
          (inner ℝ (representative parent)
              (globalGrainDirection
                (source.globalGrains.slope line.lineHeight)) -
            line.lineLevel) -
          (inner ℝ (representative first)
              (globalGrainDirection
                (source.globalGrains.slope line.lineHeight)) -
            line.lineLevel) =
          inner ℝ (representative parent)
              (globalGrainDirection
                (source.globalGrains.slope line.lineHeight)) -
            inner ℝ (representative first)
              (globalGrainDirection
                (source.globalGrains.slope line.lineHeight)) := by
        ring
      rw [hrewrite] at htriangle
      exact htriangle.trans (by
        have hp := hnear parent hparent
        have hf := hnear first hfirstParent
        linarith)
    have hslope : |source.globalGrains.slope line.lineHeight| ≤ 3 :=
      source.globalGrains.slope_bound line.lineHeight line.lineHeight_mem
    have hxClose :
        |representative parent 0 - representative first 0| ≤ 21 * root := by
      have hformula :
          inner ℝ (representative parent)
                (globalGrainDirection
                  (source.globalGrains.slope line.lineHeight)) -
              inner ℝ (representative first)
                (globalGrainDirection
                  (source.globalGrains.slope line.lineHeight)) =
            (representative parent 0 - representative first 0) +
              source.globalGrains.slope line.lineHeight *
                (representative parent 1 - representative first 1) := by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
        ring
      rw [hformula] at hcoordClose
      have hsolve :
          |representative parent 0 - representative first 0| ≤
            |(representative parent 0 - representative first 0) +
                source.globalGrains.slope line.lineHeight *
                  (representative parent 1 - representative first 1)| +
              |source.globalGrains.slope line.lineHeight| *
                |representative parent 1 - representative first 1| := by
        have h := abs_sub
          ((representative parent 0 - representative first 0) +
            source.globalGrains.slope line.lineHeight *
              (representative parent 1 - representative first 1))
          (source.globalGrains.slope line.lineHeight *
            (representative parent 1 - representative first 1))
        simpa [abs_mul] using h
      calc
        |representative parent 0 - representative first 0| ≤ _ := hsolve
        _ ≤ 18 * scale + 3 * root := by gcongr
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

/-- One genuine fixed-line parent for every occupied terminal y-layer. -/
structure PureWZ2TerminalBinParentYSelection
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    (parents : PureWZ2TerminalFixedBinParentData line) where
  yLayers : Finset ℤ
  yLayers_eq : yLayers = parents.parents.image fun parent => parent.2.1
  parentFor : ℤ → ℤ × ℤ × ℤ
  parentFor_mem : ∀ y ∈ yLayers, parentFor y ∈ parents.parents
  parentFor_y : ∀ y ∈ yLayers, (parentFor y).2.1 = y
  selected : Finset (ℤ × ℤ × ℤ)
  selected_eq : selected = yLayers.image parentFor
  selected_subset : selected ⊆ parents.parents
  selected_nonempty : selected.Nonempty
  selected_y_injective :
    Set.InjOn (fun parent : ℤ × ℤ × ℤ => parent.2.1) selected
  selected_card : selected.card = yLayers.card
  parent_card : parents.parents.card ≤ 45 * selected.card
  selected_hit :
    ∀ parent ∈ selected, ∃ cell ∈ line.heavyCells,
      parents.parentCell cell = parent

/-- Backwards-compatible y-selection package on the largest global bin. -/
abbrev PureWZ2TerminalParentYSelection
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    (parents : PureWZ2TerminalFixedLineParentData line) :=
  PureWZ2TerminalBinParentYSelection parents

theorem PureWZ2TerminalFixedBinParentData.selectOnePerYBin
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    (parents : PureWZ2TerminalFixedBinParentData line) :
    Nonempty (PureWZ2TerminalBinParentYSelection parents) := by
  let yLayers := parents.parents.image fun parent => parent.2.1
  have hyLayersNonempty : yLayers.Nonempty :=
    parents.parents_nonempty.image fun parent => parent.2.1
  let defaultParent := Classical.choose parents.parents_nonempty
  let parentFor : ℤ → ℤ × ℤ × ℤ := fun y =>
    if hy : y ∈ yLayers then
      Classical.choose (Finset.mem_image.mp hy)
    else defaultParent
  have hparentForMem :
      ∀ y ∈ yLayers, parentFor y ∈ parents.parents := by
    intro y hy
    simp only [parentFor, dif_pos hy]
    exact (Classical.choose_spec (Finset.mem_image.mp hy)).1
  have hparentForY : ∀ y ∈ yLayers, (parentFor y).2.1 = y := by
    intro y hy
    simp only [parentFor, dif_pos hy]
    exact (Classical.choose_spec (Finset.mem_image.mp hy)).2
  let selected := yLayers.image parentFor
  have hselectedSubset : selected ⊆ parents.parents := by
    intro parent hparent
    rcases Finset.mem_image.mp hparent with ⟨y, hy, rfl⟩
    exact hparentForMem y hy
  have hparentForInjective : Set.InjOn parentFor yLayers := by
    intro first hfirst second hsecond heq
    have := congrArg (fun parent : ℤ × ℤ × ℤ => parent.2.1) heq
    simpa [hparentForY first hfirst, hparentForY second hsecond] using this
  have hselectedCard : selected.card = yLayers.card :=
    Finset.card_image_of_injOn hparentForInjective
  have hselectedYInjective :
      Set.InjOn (fun parent : ℤ × ℤ × ℤ => parent.2.1) selected := by
    intro first hfirst second hsecond heq
    rcases Finset.mem_image.mp hfirst with ⟨firstY, hfirstY, hfirstEq⟩
    rcases Finset.mem_image.mp hsecond with ⟨secondY, hsecondY, hsecondEq⟩
    subst first
    subst second
    have hyEq : firstY = secondY := by
      simpa [hparentForY firstY hfirstY, hparentForY secondY hsecondY]
        using heq
    rw [hyEq]
  have hparentCard : parents.parents.card ≤ 45 * selected.card := by
    have hraw := Finset.card_le_mul_card_image parents.parents 45
      (fun y _ => parents.parent_y_fiber_card y)
    simpa [yLayers, selected, hselectedCard] using hraw
  exact ⟨{
    yLayers := yLayers
    yLayers_eq := rfl
    parentFor := parentFor
    parentFor_mem := hparentForMem
    parentFor_y := hparentForY
    selected := selected
    selected_eq := rfl
    selected_subset := hselectedSubset
    selected_nonempty := hyLayersNonempty.image parentFor
    selected_y_injective := hselectedYInjective
    selected_card := hselectedCard
    parent_card := hparentCard
    selected_hit := by
      intro parent hparent
      exact parents.parent_hit parent (hselectedSubset hparent)
  }⟩

/-- Compatibility wrapper for the former largest-bin terminal chain. -/
theorem PureWZ2TerminalFixedLineParentData.selectOnePerY
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    (parents : PureWZ2TerminalFixedLineParentData line) :
    Nonempty (PureWZ2TerminalParentYSelection parents) :=
  parents.selectOnePerYBin

/-- A mod-512 separated residue of the selected terminal parent y-layers. -/
structure PureWZ2TerminalBinParentYResidueData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    (selection : PureWZ2TerminalBinParentYSelection parents) where
  residue : Fin 512
  selected : Finset (ℤ × ℤ × ℤ)
  selected_eq : selected = selection.selected.filter fun parent =>
    (parent.2.1 % (512 : ℤ)).toNat = residue
  selected_subset : selected ⊆ selection.selected
  selected_nonempty : selected.Nonempty
  card_fraction : selection.selected.card ≤ 512 * selected.card
  residue_eq :
    ∀ parent ∈ selected, parent.2.1 % (512 : ℤ) = (residue : ℤ)
  y_separated :
    ∀ first ∈ selected, ∀ second ∈ selected,
      first.2.1 = second.2.1 ∨
        (512 : ℤ) ≤ |first.2.1 - second.2.1|

/-- Backwards-compatible residue package on the largest global bin. -/
abbrev PureWZ2TerminalParentYResidueData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    (selection : PureWZ2TerminalParentYSelection parents) :=
  PureWZ2TerminalBinParentYResidueData selection

theorem PureWZ2TerminalBinParentYSelection.selectResidueBin
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    (selection : PureWZ2TerminalBinParentYSelection parents) :
    Nonempty (PureWZ2TerminalBinParentYResidueData selection) := by
  let label : (ℤ × ℤ × ℤ) → Fin 512 := fun parent =>
    ⟨(parent.2.1 % (512 : ℤ)).toNat, by
      have hnonneg : 0 ≤ parent.2.1 % (512 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      have hlt : parent.2.1 % (512 : ℤ) < (512 : ℤ) :=
        Int.emod_lt_of_pos _ (by norm_num)
      omega⟩
  rcases wz1Lemma23_weighted_pigeonhole
      (n := 512) (by norm_num) selection.selected (fun _ => 1) label with
    ⟨residue, hcardRaw⟩
  let selected := selection.selected.filter fun parent => label parent = residue
  have hcard : selection.selected.card ≤ 512 * selected.card := by
    simpa [selected, Finset.sum_const] using hcardRaw
  have hselectedNonempty : selected.Nonempty := by
    by_contra hempty
    have hselectedEmpty : selected = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hselectedCard : selected.card = 0 := by simp [hselectedEmpty]
    have hallCard : selection.selected.card = 0 := by
      apply Nat.le_zero.mp
      simpa [hselectedCard] using hcard
    exact (Finset.card_ne_zero.mpr selection.selected_nonempty) hallCard
  have hresidue :
      ∀ parent ∈ selected, parent.2.1 % (512 : ℤ) = (residue : ℤ) := by
    intro parent hparent
    have hlabel := (Finset.mem_filter.mp hparent).2
    have hnonneg : 0 ≤ parent.2.1 % (512 : ℤ) :=
      Int.emod_nonneg _ (by norm_num)
    have hcast : ((label parent : ℕ) : ℤ) = parent.2.1 % (512 : ℤ) := by
      simp [label, Int.toNat_of_nonneg hnonneg]
    have hcastEq := congrArg (fun value : Fin 512 => (value : ℤ)) hlabel
    rwa [hcast] at hcastEq
  have hseparated :
      ∀ first ∈ selected, ∀ second ∈ selected,
        first.2.1 = second.2.1 ∨
          (512 : ℤ) ≤ |first.2.1 - second.2.1| := by
    intro first hfirst second hsecond
    by_cases heq : first.2.1 = second.2.1
    · exact Or.inl heq
    · right
      have hmod : (first.2.1 - second.2.1) % (512 : ℤ) = 0 := by
        rw [Int.sub_emod, hresidue first hfirst, hresidue second hsecond]
        simp
      have hdiv : (512 : ℤ) ∣ first.2.1 - second.2.1 := by
        rwa [Int.dvd_iff_emod_eq_zero]
      exact Int.le_abs_of_dvd (sub_ne_zero.mpr heq) hdiv
  exact ⟨{
    residue := residue
    selected := selected
    selected_eq := by
      apply Finset.ext
      intro parent
      simp only [selected, Finset.mem_filter]
      constructor
      · intro h
        exact ⟨h.1, by
          have hnonneg : 0 ≤ parent.2.1 % (512 : ℤ) :=
            Int.emod_nonneg _ (by norm_num)
          have hcast := congrArg (fun value : Fin 512 => (value : ℕ)) h.2
          simpa [label, Int.toNat_of_nonneg hnonneg] using hcast⟩
      · intro h
        refine ⟨h.1, ?_⟩
        apply Fin.ext
        simpa [label] using h.2
    selected_subset := Finset.filter_subset _ _
    selected_nonempty := hselectedNonempty
    card_fraction := hcard
    residue_eq := hresidue
    y_separated := hseparated
  }⟩

/-- Compatibility wrapper for the former largest-bin terminal chain. -/
theorem PureWZ2TerminalParentYSelection.selectResidue
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    (selection : PureWZ2TerminalParentYSelection parents) :
    Nonempty (PureWZ2TerminalParentYResidueData selection) :=
  selection.selectResidueBin

end Kakeya.Assouad
