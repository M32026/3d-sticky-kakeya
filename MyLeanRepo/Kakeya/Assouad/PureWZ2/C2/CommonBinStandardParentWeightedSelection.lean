import Mathlib.Tactic

/-!
# Construction-independent weighted parent-y selection

This file contains only finite combinatorics.  From a nonempty finite family
of integer-grid parents, with at most `D` parents in each fixed-`y` fiber, it
first selects a maximum-weight parent in every occupied fiber.  It then
selects a nonempty maximum-weight residue class modulo `512`.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

attribute [local instance] Classical.propDecidable

/-- The integer-grid parent type used by the common-bin route. -/
abbrev CommonBinStandardParent := ℤ × ℤ × ℤ

/-- The parent coordinate on which the finite selection is performed. -/
def commonBinStandardParentY (parent : CommonBinStandardParent) : ℤ :=
  parent.2.1

/-- The residue modulo `512` of a standard parent's `y` coordinate. -/
def commonBinStandardParentYResidue
    (parent : CommonBinStandardParent) : Fin 512 :=
  ⟨(commonBinStandardParentY parent % (512 : ℤ)).toNat, by
    have hnonneg :
        0 ≤ commonBinStandardParentY parent % (512 : ℤ) :=
      Int.emod_nonneg _ (by norm_num)
    have hlt :
        commonBinStandardParentY parent % (512 : ℤ) < (512 : ℤ) :=
      Int.emod_lt_of_pos _ (by norm_num)
    omega⟩

/-- ENNReal weighted pigeonhole over a finite family. -/
theorem commonBin_ennreal_weighted_pigeonhole
    {α : Type*} [DecidableEq α]
    {n : ℕ} (hn : 0 < n)
    (indices : Finset α)
    (weight : α → ENNReal)
    (color : α → Fin n) :
    ∃ target : Fin n,
      (∀ other : Fin n,
        (∑ index ∈ indices.filter (fun index => color index = other),
            weight index) ≤
          ∑ index ∈ indices.filter (fun index => color index = target),
            weight index) ∧
      (∑ index ∈ indices, weight index) ≤
        (n : ENNReal) *
          ∑ index ∈ indices.filter (fun index => color index = target),
            weight index := by
  let fiberWeight : Fin n → ENNReal := fun target =>
    ∑ index ∈ indices.filter (fun index => color index = target),
      weight index
  have hcolors : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨0, hn⟩
  rcases Finset.exists_max_image Finset.univ fiberWeight hcolors with
    ⟨target, _htarget, hmax⟩
  have htotal :
      (∑ target : Fin n, fiberWeight target) =
        ∑ index ∈ indices, weight index := by
    simpa [fiberWeight] using
      Finset.sum_fiberwise indices color weight
  refine ⟨target, ?_, ?_⟩
  · intro other
    exact hmax other (Finset.mem_univ other)
  · rw [← htotal]
    calc
      (∑ other : Fin n, fiberWeight other) ≤
          ∑ _other : Fin n, fiberWeight target := by
        exact Finset.sum_le_sum fun other _ =>
          hmax other (Finset.mem_univ other)
      _ = (n : ENNReal) * fiberWeight target := by
        simp [Finset.sum_const]
      _ = (n : ENNReal) *
            ∑ index ∈ indices.filter (fun index => color index = target),
              weight index := rfl

/-- One maximum-weight parent in every occupied `y` fiber. -/
structure CommonBinStandardParentYSelectionData
    (D : ℕ)
    (parents : Finset CommonBinStandardParent)
    (weight : CommonBinStandardParent → ENNReal) where
  yLayers : Finset ℤ
  yLayers_eq :
    yLayers = parents.image commonBinStandardParentY
  parentFor : ℤ → CommonBinStandardParent
  parentFor_mem :
    ∀ y ∈ yLayers, parentFor y ∈ parents
  parentFor_y :
    ∀ y ∈ yLayers, commonBinStandardParentY (parentFor y) = y
  parentFor_max :
    ∀ y ∈ yLayers, ∀ parent ∈ parents,
      commonBinStandardParentY parent = y →
        weight parent ≤ weight (parentFor y)
  onePerY : Finset CommonBinStandardParent
  onePerY_eq :
    onePerY = yLayers.image parentFor
  onePerY_subset :
    onePerY ⊆ parents
  onePerY_nonempty :
    onePerY.Nonempty
  onePerY_y_injective :
    Set.InjOn commonBinStandardParentY onePerY
  total_weight_le :
    (∑ parent ∈ parents, weight parent) ≤
      (D : ENNReal) * ∑ parent ∈ onePerY, weight parent

/-- Select one maximum-weight representative from every occupied `y` fiber. -/
theorem commonBin_selectStandardParentY
    (D : ℕ)
    (parents : Finset CommonBinStandardParent)
    (weight : CommonBinStandardParent → ENNReal)
    (parents_nonempty : parents.Nonempty)
    (fiber_card :
      ∀ y : ℤ,
        (parents.filter fun parent =>
          commonBinStandardParentY parent = y).card ≤ D) :
    Nonempty (CommonBinStandardParentYSelectionData D parents weight) := by
  let yLayers := parents.image commonBinStandardParentY
  have hyLayersNonempty : yLayers.Nonempty :=
    parents_nonempty.image commonBinStandardParentY
  let defaultParent := Classical.choose parents_nonempty
  let fiber (y : ℤ) :=
    parents.filter fun parent => commonBinStandardParentY parent = y
  have hfiberNonempty :
      ∀ y ∈ yLayers, (fiber y).Nonempty := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨parent, hparent, hparentY⟩
    exact
      ⟨parent, Finset.mem_filter.mpr
        ⟨hparent, hparentY⟩⟩
  let parentFor : ℤ → CommonBinStandardParent := fun y =>
    if hy : y ∈ yLayers then
      Classical.choose
        (Finset.exists_max_image
          (fiber y) weight (hfiberNonempty y hy))
    else
      defaultParent
  have hparentForFiber :
      ∀ y (hy : y ∈ yLayers), parentFor y ∈ fiber y := by
    intro y hy
    simp only [parentFor, dif_pos hy]
    exact
      (Classical.choose_spec
        (Finset.exists_max_image
          (fiber y) weight (hfiberNonempty y hy))).1
  have hparentForMem :
      ∀ y ∈ yLayers, parentFor y ∈ parents := by
    intro y hy
    exact (Finset.mem_filter.mp (hparentForFiber y hy)).1
  have hparentForY :
      ∀ y ∈ yLayers, commonBinStandardParentY (parentFor y) = y := by
    intro y hy
    exact (Finset.mem_filter.mp (hparentForFiber y hy)).2
  have hparentForMax :
      ∀ y (hy : y ∈ yLayers), ∀ parent ∈ parents,
        commonBinStandardParentY parent = y →
          weight parent ≤ weight (parentFor y) := by
    intro y hy parent hparent hparentY
    simp only [parentFor, dif_pos hy]
    exact
      (Classical.choose_spec
        (Finset.exists_max_image
          (fiber y) weight (hfiberNonempty y hy))).2 parent
            (Finset.mem_filter.mpr ⟨hparent, hparentY⟩)
  let onePerY := yLayers.image parentFor
  have honePerYSubset : onePerY ⊆ parents := by
    intro parent hparent
    rcases Finset.mem_image.mp hparent with ⟨y, hy, rfl⟩
    exact hparentForMem y hy
  have hparentForInjective : Set.InjOn parentFor yLayers := by
    intro first hfirst second hsecond heq
    have hY := congrArg commonBinStandardParentY heq
    simpa [hparentForY first hfirst, hparentForY second hsecond] using hY
  have honePerYInjective :
      Set.InjOn commonBinStandardParentY onePerY := by
    intro first hfirst second hsecond heq
    rcases Finset.mem_image.mp hfirst with
      ⟨firstY, hfirstY, rfl⟩
    rcases Finset.mem_image.mp hsecond with
      ⟨secondY, hsecondY, rfl⟩
    have hyEq : firstY = secondY := by
      simpa [hparentForY firstY hfirstY,
        hparentForY secondY hsecondY] using heq
    rw [hyEq]
  have hallByY :
      (∑ y ∈ yLayers, ∑ parent ∈ fiber y, weight parent) =
        ∑ parent ∈ parents, weight parent := by
    exact
      Finset.sum_fiberwise_of_maps_to
        (fun parent hparent =>
          Finset.mem_image.mpr ⟨parent, hparent, rfl⟩)
        weight
  have hfiberWeight :
      ∀ y ∈ yLayers,
        (∑ parent ∈ fiber y, weight parent) ≤
          (D : ENNReal) * weight (parentFor y) := by
    intro y hy
    calc
      (∑ parent ∈ fiber y, weight parent) ≤
          ((fiber y).card : ENNReal) * weight (parentFor y) := by
        simpa [nsmul_eq_mul] using
          (Finset.sum_le_card_nsmul
            (fiber y) weight (weight (parentFor y))
            (fun parent hparent =>
              hparentForMax y hy parent
                (Finset.mem_filter.mp hparent).1
                (Finset.mem_filter.mp hparent).2))
      _ ≤ (D : ENNReal) * weight (parentFor y) := by
        gcongr
        exact_mod_cast fiber_card y
  have honePerYSum :
      (∑ parent ∈ onePerY, weight parent) =
        ∑ y ∈ yLayers, weight (parentFor y) :=
    Finset.sum_image hparentForInjective
  have htotalWeight :
      (∑ parent ∈ parents, weight parent) ≤
        (D : ENNReal) * ∑ parent ∈ onePerY, weight parent := by
    rw [← hallByY]
    calc
      (∑ y ∈ yLayers, ∑ parent ∈ fiber y, weight parent) ≤
          ∑ y ∈ yLayers,
            (D : ENNReal) * weight (parentFor y) := by
        exact Finset.sum_le_sum fun y hy => hfiberWeight y hy
      _ = (D : ENNReal) *
          ∑ y ∈ yLayers, weight (parentFor y) := by
        rw [Finset.mul_sum]
      _ = (D : ENNReal) *
          ∑ parent ∈ onePerY, weight parent := by
        rw [honePerYSum]
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
    total_weight_le := htotalWeight
  }⟩

/-- The one-per-`y` maximum selection followed by a nonempty residue
selection modulo `512`. -/
structure CommonBinStandardParentWeightedSelectionData
    (D : ℕ)
    (parents : Finset CommonBinStandardParent)
    (weight : CommonBinStandardParent → ENNReal)
    extends CommonBinStandardParentYSelectionData D parents weight where
  residue : Fin 512
  selected : Finset CommonBinStandardParent
  selected_eq :
    selected = onePerY.filter fun parent =>
      commonBinStandardParentYResidue parent = residue
  selected_subset_onePerY :
    selected ⊆ onePerY
  selected_subset :
    selected ⊆ parents
  selected_nonempty :
    selected.Nonempty
  residue_eq :
    ∀ parent ∈ selected,
      commonBinStandardParentY parent % (512 : ℤ) = (residue : ℤ)
  selected_y_injective :
    Set.InjOn commonBinStandardParentY selected
  selected_y_separated :
    ∀ first ∈ selected, ∀ second ∈ selected, first ≠ second →
      (512 : ℤ) ≤
        |commonBinStandardParentY first -
          commonBinStandardParentY second|
  onePerY_weight_le :
    (∑ parent ∈ onePerY, weight parent) ≤
      512 * ∑ parent ∈ selected, weight parent
  residue_max :
    ∀ other : Fin 512,
      (∑ parent ∈ onePerY.filter (fun parent =>
          commonBinStandardParentYResidue parent = other),
          weight parent) ≤
        ∑ parent ∈ selected, weight parent
  final_weight_le :
    (∑ parent ∈ parents, weight parent) ≤
      (D : ENNReal) * 512 *
        ∑ parent ∈ selected, weight parent

/-- Retain a nonempty maximum-weight residue modulo `512` from an existing
one-per-`y` maximum selection.  Nonemptiness does not require positive
weights: in the zero-total case, an occupied residue is chosen explicitly. -/
theorem CommonBinStandardParentYSelectionData.selectWeightedResidue
    {D : ℕ}
    {parents : Finset CommonBinStandardParent}
    {weight : CommonBinStandardParent → ENNReal}
    (data : CommonBinStandardParentYSelectionData D parents weight) :
    Nonempty
      (CommonBinStandardParentWeightedSelectionData D parents weight) := by
  rcases commonBin_ennreal_weighted_pigeonhole
      (n := 512) (by norm_num) data.onePerY weight
      commonBinStandardParentYResidue with
    ⟨rawResidue, hrawMax, hrawWeight⟩
  let rawSelected :=
    data.onePerY.filter fun parent =>
      commonBinStandardParentYResidue parent = rawResidue
  have hresidueExists :
      ∃ residue : Fin 512,
        let selected :=
          data.onePerY.filter fun parent =>
            commonBinStandardParentYResidue parent = residue
        selected.Nonempty ∧
          (∀ other : Fin 512,
            (∑ parent ∈ data.onePerY.filter (fun parent =>
                commonBinStandardParentYResidue parent = other),
                weight parent) ≤
              ∑ parent ∈ selected, weight parent) ∧
          (∑ parent ∈ data.onePerY, weight parent) ≤
            512 * ∑ parent ∈ selected, weight parent := by
    by_cases hrawNonempty : rawSelected.Nonempty
    · exact
        ⟨rawResidue, hrawNonempty, hrawMax, by
          simpa [rawSelected] using hrawWeight⟩
    · have hrawEmpty : rawSelected = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hrawNonempty
      have htotalZero :
          (∑ parent ∈ data.onePerY, weight parent) = 0 := by
        have hle :
            (∑ parent ∈ data.onePerY, weight parent) ≤ 0 := by
          simpa [rawSelected, hrawEmpty] using hrawWeight
        exact le_zero_iff.mp hle
      have hfiberZero :
          ∀ other : Fin 512,
            (∑ parent ∈ data.onePerY.filter (fun parent =>
                commonBinStandardParentYResidue parent = other),
                weight parent) = 0 := by
        intro other
        apply le_zero_iff.mp
        calc
          (∑ parent ∈ data.onePerY.filter (fun parent =>
              commonBinStandardParentYResidue parent = other),
              weight parent) ≤
              ∑ parent ∈ data.onePerY.filter (fun parent =>
                commonBinStandardParentYResidue parent = rawResidue),
                weight parent :=
            hrawMax other
          _ = 0 := by simp [rawSelected, hrawEmpty]
      let first := Classical.choose data.onePerY_nonempty
      have hfirst : first ∈ data.onePerY :=
        Classical.choose_spec data.onePerY_nonempty
      refine
        ⟨commonBinStandardParentYResidue first, ?_, ?_, ?_⟩
      · exact
          ⟨first, Finset.mem_filter.mpr ⟨hfirst, rfl⟩⟩
      · intro other
        rw [hfiberZero other,
          hfiberZero (commonBinStandardParentYResidue first)]
      · rw [htotalZero]
        exact bot_le
  rcases hresidueExists with
    ⟨residue, hselectedNonempty, hresidueMax, hresidueWeight⟩
  let selected :=
    data.onePerY.filter fun parent =>
      commonBinStandardParentYResidue parent = residue
  have hresidue :
      ∀ parent ∈ selected,
        commonBinStandardParentY parent % (512 : ℤ) =
          (residue : ℤ) := by
    intro parent hparent
    have hlabel := (Finset.mem_filter.mp hparent).2
    have hnonneg :
        0 ≤ commonBinStandardParentY parent % (512 : ℤ) :=
      Int.emod_nonneg _ (by norm_num)
    have hcast :
        ((commonBinStandardParentYResidue parent : ℕ) : ℤ) =
          commonBinStandardParentY parent % (512 : ℤ) := by
      simp [commonBinStandardParentYResidue,
        Int.toNat_of_nonneg hnonneg]
    have hcastEq :=
      congrArg (fun value : Fin 512 => (value : ℤ)) hlabel
    rwa [hcast] at hcastEq
  have hselectedYInjective :
      Set.InjOn commonBinStandardParentY selected :=
    data.onePerY_y_injective.mono (Finset.filter_subset _ _)
  have hseparated :
      ∀ first ∈ selected, ∀ second ∈ selected, first ≠ second →
        (512 : ℤ) ≤
          |commonBinStandardParentY first -
            commonBinStandardParentY second| := by
    intro first hfirst second hsecond hne
    have hyNe :
        commonBinStandardParentY first ≠
          commonBinStandardParentY second := fun hy =>
      hne (hselectedYInjective hfirst hsecond hy)
    have hmod :
        (commonBinStandardParentY first -
          commonBinStandardParentY second) % (512 : ℤ) = 0 := by
      rw [Int.sub_emod, hresidue first hfirst,
        hresidue second hsecond]
      simp
    have hdiv :
        (512 : ℤ) ∣
          commonBinStandardParentY first -
            commonBinStandardParentY second := by
      rwa [Int.dvd_iff_emod_eq_zero]
    exact Int.le_abs_of_dvd (sub_ne_zero.mpr hyNe) hdiv
  have hfinalWeight :
      (∑ parent ∈ parents, weight parent) ≤
        (D : ENNReal) * 512 *
          ∑ parent ∈ selected, weight parent := by
    calc
      (∑ parent ∈ parents, weight parent) ≤
          (D : ENNReal) *
            ∑ parent ∈ data.onePerY, weight parent :=
        data.total_weight_le
      _ ≤ (D : ENNReal) *
          (512 * ∑ parent ∈ selected, weight parent) := by
        gcongr
      _ = (D : ENNReal) * 512 *
          ∑ parent ∈ selected, weight parent := by
        ring
  exact ⟨{
    toCommonBinStandardParentYSelectionData := data
    residue := residue
    selected := selected
    selected_eq := rfl
    selected_subset_onePerY := Finset.filter_subset _ _
    selected_subset :=
      (Finset.filter_subset _ _).trans data.onePerY_subset
    selected_nonempty := hselectedNonempty
    residue_eq := hresidue
    selected_y_injective := hselectedYInjective
    selected_y_separated := hseparated
    onePerY_weight_le := hresidueWeight
    residue_max := hresidueMax
    final_weight_le := hfinalWeight
  }⟩

/-- One-shot constructor for the common-bin standard parent weighted
selection. -/
theorem commonBin_selectStandardParentWeighted
    (D : ℕ)
    (parents : Finset CommonBinStandardParent)
    (weight : CommonBinStandardParent → ENNReal)
    (parents_nonempty : parents.Nonempty)
    (fiber_card :
      ∀ y : ℤ,
        (parents.filter fun parent =>
          commonBinStandardParentY parent = y).card ≤ D) :
    Nonempty
      (CommonBinStandardParentWeightedSelectionData D parents weight) := by
  rcases
      commonBin_selectStandardParentY
        D parents weight parents_nonempty fiber_card with
    ⟨selection⟩
  exact selection.selectWeightedResidue

end Kakeya.Assouad

end
