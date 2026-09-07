import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.FixedLineParentYFiber
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalBlockResidue
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularParents

/-!
# Weighted parent selection on the outer-popular terminal carrier

Every weight in this file is the genuine volume of the outer-popular carrier
inside one official side-`sqrt delta` sticky parent.  We first retain a
maximum-weight parent over every occupied parent y-index and then retain a
maximum-weight residue modulo 512.  No assertion is made that the fixed-line
visible parents cover the whole outer-popular carrier.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Actual outer-popular mass inside one official terminal parent cube. -/
def pureWZ2TerminalPopularParentWeight
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    (carrier : PureWZ2TerminalPopularSourceCarrierData heightData)
    (parent : ℤ × ℤ × ℤ) : ENNReal :=
  volume (carrier.shading.union ∩
    wz1PaperGridCube terminal.sqrtRequested.1 parent)

/-- Exact finite additivity of the genuine outer-popular parent weights. -/
theorem pureWZ2TerminalPopularParentWeight_sum_eq
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    (carrier : PureWZ2TerminalPopularSourceCarrierData heightData)
    (selected : Finset (ℤ × ℤ × ℤ)) :
    (∑ parent ∈ selected,
        pureWZ2TerminalPopularParentWeight carrier parent) =
      volume (carrier.shading.union ∩
        ⋃ parent ∈ selected,
          wz1PaperGridCube terminal.sqrtRequested.1 parent) := by
  let piece : (ℤ × ℤ × ℤ) → Set Point3 := fun parent =>
    carrier.shading.union ∩
      wz1PaperGridCube terminal.sqrtRequested.1 parent
  have hdisjoint :
      (selected : Set (ℤ × ℤ × ℤ)).PairwiseDisjoint piece := by
    intro first _ second _ hne
    exact (wz1PaperGridCube_disjoint hne).mono
      Set.inter_subset_right Set.inter_subset_right
  have hmeas : ∀ parent ∈ selected, MeasurableSet (piece parent) := by
    intro parent _
    exact carrier.shading.union_measurable.inter
      (wz1PaperGridCube_measurable parent)
  have hunion :
      (⋃ parent ∈ selected, piece parent) =
        carrier.shading.union ∩
          ⋃ parent ∈ selected,
            wz1PaperGridCube terminal.sqrtRequested.1 parent := by
    ext point
    simp [piece]
  rw [← hunion, MeasureTheory.measure_biUnion_finset hdisjoint hmeas]
  rfl

/-- The old 45-parent packing argument depends only on fixed-line geometry,
so it remains valid after source-volume height popularity. -/
theorem PureWZ2TerminalPopularFixedBinParentData.parent_y_fiber_card
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {popularPrepared : PureWZ2TerminalPopularPreparedWindowData carrier}
    {line : PureWZ2HorizontalFixedBinCore
      popularPrepared.windowed source.globalGrains.slope}
    (parents : PureWZ2TerminalPopularFixedBinParentData line)
    (y : ℤ) :
    (parents.parents.filter fun parent => parent.2.1 = y).card ≤ 45 := by
  have hdeltaRoot : delta ≤ terminal.sqrtRequested.1 := by
    rw [terminal.sqrtRequested_eq]
    nlinarith [Real.sqrt_nonneg delta,
      Real.sq_sqrt source.extremal.delta_pos.le,
      source.extremal.delta_le_one]
  exact pureWZ2_fixedLine_parent_y_fiber_card
    line terminal.sqrtRequested.1
    terminal.sticky.coarse_extremal.delta_pos hdeltaRoot
    (source.globalGrains.slope_bound line.lineHeight line.lineHeight_mem)
    parents.parents parents.parentCell parents.parent_hit
    parents.representative_mem_parent y

/-- Carrier-independent maximum-weight one-per-y and mod-512 selection. -/
structure PureWZ2FiniteWeightedParentYResidueData
    (parents : Finset (ℤ × ℤ × ℤ))
    (weight : (ℤ × ℤ × ℤ) → ENNReal) where
  yLayers : Finset ℤ
  yLayers_eq : yLayers = parents.image fun parent => parent.2.1
  parentFor : ℤ → ℤ × ℤ × ℤ
  parentFor_mem : ∀ y ∈ yLayers, parentFor y ∈ parents
  parentFor_y : ∀ y ∈ yLayers, (parentFor y).2.1 = y
  parentFor_max : ∀ y ∈ yLayers, ∀ parent ∈ parents,
    parent.2.1 = y →
      weight parent ≤ weight (parentFor y)
  onePerY : Finset (ℤ × ℤ × ℤ)
  onePerY_eq : onePerY = yLayers.image parentFor
  onePerY_subset : onePerY ⊆ parents
  onePerY_nonempty : onePerY.Nonempty
  onePerY_y_injective :
    Set.InjOn (fun parent : ℤ × ℤ × ℤ => parent.2.1) onePerY
  onePerY_weight_retention :
    (∑ parent ∈ parents, weight parent) ≤
      45 * ∑ parent ∈ onePerY, weight parent
  residue : Fin 512
  selected : Finset (ℤ × ℤ × ℤ)
  selected_eq : selected = onePerY.filter fun parent =>
    (parent.2.1 % (512 : ℤ)).toNat = residue
  selected_subset : selected ⊆ onePerY
  selected_nonempty : selected.Nonempty
  residue_weight_retention :
    (∑ parent ∈ onePerY, weight parent) ≤
      512 * ∑ parent ∈ selected, weight parent
  residue_eq :
    ∀ parent ∈ selected, parent.2.1 % (512 : ℤ) = (residue : ℤ)
  y_injective :
    Set.InjOn (fun parent : ℤ × ℤ × ℤ => parent.2.1) selected
  y_separated :
    ∀ first ∈ selected, ∀ second ∈ selected, first ≠ second →
      (512 : ℤ) ≤ |first.2.1 - second.2.1|

theorem pureWZ2_selectFiniteWeightedParentYResidue
    (parents : Finset (ℤ × ℤ × ℤ))
    (weight : (ℤ × ℤ × ℤ) → ENNReal)
    (parents_nonempty : parents.Nonempty)
    (fiber_card : ∀ y : ℤ,
      (parents.filter fun parent => parent.2.1 = y).card ≤ 45) :
    Nonempty (PureWZ2FiniteWeightedParentYResidueData parents weight) := by
  let yLayers := parents.image fun parent => parent.2.1
  have hyLayersNonempty : yLayers.Nonempty :=
    parents_nonempty.image fun parent => parent.2.1
  let defaultParent := Classical.choose parents_nonempty
  let fiber (y : ℤ) := parents.filter fun parent => parent.2.1 = y
  have hfiberNonempty : ∀ y ∈ yLayers, (fiber y).Nonempty := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨parent, hparent, hparentY⟩
    exact ⟨parent, Finset.mem_filter.mpr ⟨hparent, hparentY⟩⟩
  let parentFor : ℤ → ℤ × ℤ × ℤ := fun y =>
    if hy : y ∈ yLayers then
      Classical.choose
        (Finset.exists_max_image (fiber y) weight (hfiberNonempty y hy))
    else defaultParent
  have hparentForFiber : ∀ y (hy : y ∈ yLayers),
      parentFor y ∈ fiber y := by
    intro y hy
    simp only [parentFor, dif_pos hy]
    exact (Classical.choose_spec
      (Finset.exists_max_image (fiber y) weight
        (hfiberNonempty y hy))).1
  have hparentForMem : ∀ y ∈ yLayers, parentFor y ∈ parents := by
    intro y hy
    exact (Finset.mem_filter.mp (hparentForFiber y hy)).1
  have hparentForY : ∀ y ∈ yLayers, (parentFor y).2.1 = y := by
    intro y hy
    exact (Finset.mem_filter.mp (hparentForFiber y hy)).2
  have hparentForMax : ∀ y (hy : y ∈ yLayers), ∀ parent ∈ parents,
      parent.2.1 = y → weight parent ≤ weight (parentFor y) := by
    intro y hy parent hparent hparentY
    simp only [parentFor, dif_pos hy]
    exact (Classical.choose_spec
      (Finset.exists_max_image (fiber y) weight
        (hfiberNonempty y hy))).2 parent
          (Finset.mem_filter.mpr ⟨hparent, hparentY⟩)
  let onePerY := yLayers.image parentFor
  have honePerYSubset : onePerY ⊆ parents := by
    intro parent hparent
    rcases Finset.mem_image.mp hparent with ⟨y, hy, rfl⟩
    exact hparentForMem y hy
  have hparentForInjective : Set.InjOn parentFor yLayers := by
    intro first hfirst second hsecond heq
    have := congrArg (fun parent : ℤ × ℤ × ℤ => parent.2.1) heq
    simpa [hparentForY first hfirst, hparentForY second hsecond] using this
  have honePerYInjective :
      Set.InjOn (fun parent : ℤ × ℤ × ℤ => parent.2.1) onePerY := by
    intro first hfirst second hsecond heq
    rcases Finset.mem_image.mp hfirst with ⟨firstY, hfirstY, rfl⟩
    rcases Finset.mem_image.mp hsecond with ⟨secondY, hsecondY, rfl⟩
    have hyEq : firstY = secondY := by
      simpa [hparentForY firstY hfirstY, hparentForY secondY hsecondY]
        using heq
    rw [hyEq]
  have hallByY :
      (∑ y ∈ yLayers, ∑ parent ∈ fiber y, weight parent) =
        ∑ parent ∈ parents, weight parent := by
    exact Finset.sum_fiberwise_of_maps_to
      (fun parent hparent => Finset.mem_image.mpr
        ⟨parent, hparent, rfl⟩) weight
  have hfiberWeight : ∀ y ∈ yLayers,
      (∑ parent ∈ fiber y, weight parent) ≤
        45 * weight (parentFor y) := by
    intro y hy
    calc
      (∑ parent ∈ fiber y, weight parent) ≤
          ((fiber y).card : ENNReal) * weight (parentFor y) := by
        simpa [nsmul_eq_mul] using
          (Finset.sum_le_card_nsmul (fiber y) weight
            (weight (parentFor y)) (fun parent hparent =>
              hparentForMax y hy parent
                (Finset.mem_filter.mp hparent).1
                (Finset.mem_filter.mp hparent).2))
      _ ≤ 45 * weight (parentFor y) := by
        gcongr
        exact_mod_cast fiber_card y
  have honePerYSum :
      (∑ parent ∈ onePerY, weight parent) =
        ∑ y ∈ yLayers, weight (parentFor y) := by
    exact Finset.sum_image hparentForInjective
  have honePerYRetention :
      (∑ parent ∈ parents, weight parent) ≤
        45 * ∑ parent ∈ onePerY, weight parent := by
    rw [← hallByY]
    calc
      (∑ y ∈ yLayers, ∑ parent ∈ fiber y, weight parent) ≤
          ∑ y ∈ yLayers, 45 * weight (parentFor y) := by
        exact Finset.sum_le_sum fun y hy => hfiberWeight y hy
      _ = 45 * ∑ y ∈ yLayers, weight (parentFor y) := by
        rw [Finset.mul_sum]
      _ = 45 * ∑ parent ∈ onePerY, weight parent := by
        rw [honePerYSum]
  let color : (ℤ × ℤ × ℤ) → Fin 512 := fun parent =>
    ⟨(parent.2.1 % (512 : ℤ)).toNat, by
      have hnonneg : 0 ≤ parent.2.1 % (512 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      have hlt : parent.2.1 % (512 : ℤ) < (512 : ℤ) :=
        Int.emod_lt_of_pos _ (by norm_num)
      omega⟩
  rcases finset_ennreal_weighted_pigeonhole
      (n := 512) (by norm_num) onePerY weight color with
    ⟨rawResidue, hrawRetention⟩
  let rawSelected := onePerY.filter fun parent => color parent = rawResidue
  have hresidueExists : ∃ residue : Fin 512,
      let selected := onePerY.filter fun parent => color parent = residue
      selected.Nonempty ∧
        (∑ parent ∈ onePerY, weight parent) ≤
          512 * ∑ parent ∈ selected, weight parent := by
    by_cases hrawNonempty : rawSelected.Nonempty
    · exact ⟨rawResidue, hrawNonempty, by
        simpa [rawSelected] using hrawRetention⟩
    · have hrawEmpty : rawSelected = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hrawNonempty
      have htotalZero : ∑ parent ∈ onePerY, weight parent = 0 := by
        have hle : (∑ parent ∈ onePerY, weight parent) ≤ 0 := by
          simpa [rawSelected, hrawEmpty] using hrawRetention
        exact le_zero_iff.mp hle
      let first := Classical.choose (hyLayersNonempty.image parentFor)
      have hfirst : first ∈ onePerY :=
        Classical.choose_spec (hyLayersNonempty.image parentFor)
      refine ⟨color first, ?_, ?_⟩
      · exact ⟨first, Finset.mem_filter.mpr ⟨hfirst, rfl⟩⟩
      · rw [htotalZero]
        exact bot_le
  rcases hresidueExists with ⟨residue, hselectedNonempty, hresidueRetention⟩
  let selected := onePerY.filter fun parent => color parent = residue
  have hresidue : ∀ parent ∈ selected,
      parent.2.1 % (512 : ℤ) = (residue : ℤ) := by
    intro parent hparent
    have hlabel := (Finset.mem_filter.mp hparent).2
    have hnonneg : 0 ≤ parent.2.1 % (512 : ℤ) :=
      Int.emod_nonneg _ (by norm_num)
    have hcast : ((color parent : ℕ) : ℤ) =
        parent.2.1 % (512 : ℤ) := by
      simp [color, Int.toNat_of_nonneg hnonneg]
    have hcastEq := congrArg (fun value : Fin 512 => (value : ℤ)) hlabel
    rwa [hcast] at hcastEq
  have hselectedYInjective :
      Set.InjOn (fun parent : ℤ × ℤ × ℤ => parent.2.1) selected :=
    honePerYInjective.mono (Finset.filter_subset _ _)
  have hseparated : ∀ first ∈ selected, ∀ second ∈ selected,
      first ≠ second → (512 : ℤ) ≤ |first.2.1 - second.2.1| := by
    intro first hfirst second hsecond hne
    have hyNe : first.2.1 ≠ second.2.1 := fun hy =>
      hne (hselectedYInjective hfirst hsecond hy)
    have hmod : (first.2.1 - second.2.1) % (512 : ℤ) = 0 := by
      rw [Int.sub_emod, hresidue first hfirst, hresidue second hsecond]
      simp
    have hdiv : (512 : ℤ) ∣ first.2.1 - second.2.1 := by
      rwa [Int.dvd_iff_emod_eq_zero]
    exact Int.le_abs_of_dvd (sub_ne_zero.mpr hyNe) hdiv
  exact ⟨{
    yLayers := yLayers
    yLayers_eq := rfl
    parentFor := parentFor
    parentFor_mem := hparentForMem
    parentFor_y := hparentForY
    parentFor_max := hparentForMax
    onePerY := onePerY
    onePerY_eq := rfl
    onePerY_subset := honePerYSubset
    onePerY_nonempty := hyLayersNonempty.image parentFor
    onePerY_y_injective := honePerYInjective
    onePerY_weight_retention := honePerYRetention
    residue := residue
    selected := selected
    selected_eq := by
      apply Finset.ext
      intro parent
      simp only [selected, Finset.mem_filter]
      constructor
      · rintro ⟨hparent, hcolor⟩
        exact ⟨hparent, by
          have hcast := congrArg (fun value : Fin 512 => (value : ℕ)) hcolor
          simpa [color] using hcast⟩
      · rintro ⟨hparent, hvalue⟩
        refine ⟨hparent, Fin.ext ?_⟩
        simpa [color] using hvalue
    selected_subset := Finset.filter_subset _ _
    selected_nonempty := hselectedNonempty
    residue_weight_retention := hresidueRetention
    residue_eq := hresidue
    y_injective := hselectedYInjective
    y_separated := hseparated
  }⟩

/-- One maximum actual outer-popular parent weight over every occupied
parent y-index, followed by one maximum-weight mod-512 residue. -/
structure PureWZ2TerminalPopularWeightedParentSelectionData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {popularPrepared : PureWZ2TerminalPopularPreparedWindowData carrier}
    {line : PureWZ2HorizontalFixedBinCore
      popularPrepared.windowed source.globalGrains.slope}
    (parents : PureWZ2TerminalPopularFixedBinParentData line)
    extends PureWZ2FiniteWeightedParentYResidueData parents.parents
      (pureWZ2TerminalPopularParentWeight carrier) where
  visible_weight_eq :
    (∑ parent ∈ parents.parents,
        pureWZ2TerminalPopularParentWeight carrier parent) =
      volume (carrier.shading.union ∩
        ⋃ parent ∈ parents.parents,
          wz1PaperGridCube terminal.sqrtRequested.1 parent)
  selected_weight_eq :
    (∑ parent ∈ selected,
        pureWZ2TerminalPopularParentWeight carrier parent) =
      volume (carrier.shading.union ∩
        ⋃ parent ∈ selected,
          wz1PaperGridCube terminal.sqrtRequested.1 parent)

theorem PureWZ2TerminalPopularFixedBinParentData.selectWeightedParents
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {popularPrepared : PureWZ2TerminalPopularPreparedWindowData carrier}
    {line : PureWZ2HorizontalFixedBinCore
      popularPrepared.windowed source.globalGrains.slope}
    (parents : PureWZ2TerminalPopularFixedBinParentData line) :
    Nonempty (PureWZ2TerminalPopularWeightedParentSelectionData parents) := by
  rcases pureWZ2_selectFiniteWeightedParentYResidue parents.parents
      (pureWZ2TerminalPopularParentWeight carrier) parents.parents_nonempty
      parents.parent_y_fiber_card with ⟨selection⟩
  exact ⟨{
    toPureWZ2FiniteWeightedParentYResidueData := selection
    visible_weight_eq :=
      pureWZ2TerminalPopularParentWeight_sum_eq carrier parents.parents
    selected_weight_eq :=
      pureWZ2TerminalPopularParentWeight_sum_eq carrier selection.selected
  }⟩

end Kakeya.Assouad

end
