import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineParentYCount

/-!
# One actual fixed-line parent per coarse y-layer
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2HorizontalFixedLineYSelection
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    (parents : PureWZ2HorizontalFixedLineParentData line) where
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
    ∀ parent ∈ selected,
      ∃ cell ∈ line.heavyCells, parents.parentCell cell = parent

theorem PureWZ2HorizontalFixedLineParentData.selectOnePerY
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    (parents : PureWZ2HorizontalFixedLineParentData line) :
    Nonempty (PureWZ2HorizontalFixedLineYSelection parents) := by
  let yLayers := parents.parents.image fun parent => parent.2.1
  have hyLayersNonempty : yLayers.Nonempty :=
    parents.parents_nonempty.image fun parent => parent.2.1
  let defaultParent := Classical.choose parents.parents_nonempty
  have hdefaultParent : defaultParent ∈ parents.parents :=
    Classical.choose_spec parents.parents_nonempty
  let parentFor : ℤ → ℤ × ℤ × ℤ := fun y =>
    if hy : y ∈ yLayers then
      Classical.choose (Finset.mem_image.mp hy)
    else defaultParent
  have hparentForMem :
      ∀ y ∈ yLayers, parentFor y ∈ parents.parents := by
    intro y hy
    simp only [parentFor, dif_pos hy]
    exact (Classical.choose_spec (Finset.mem_image.mp hy)).1
  have hparentForY :
      ∀ y ∈ yLayers, (parentFor y).2.1 = y := by
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
      simpa [hparentForY firstY hfirstY, hparentForY secondY hsecondY] using heq
    rw [hyEq]
  have hparentCard : parents.parents.card ≤ 45 * selected.card := by
    have hraw := Finset.card_le_mul_card_image parents.parents 45
      (fun y _ => parents.parent_y_fiber_card y)
    simpa [yLayers, selected, hselectedCard] using hraw
  exact
    ⟨{ yLayers := yLayers
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
         exact parents.parent_hit parent (hselectedSubset hparent) }⟩

end Kakeya.Assouad
