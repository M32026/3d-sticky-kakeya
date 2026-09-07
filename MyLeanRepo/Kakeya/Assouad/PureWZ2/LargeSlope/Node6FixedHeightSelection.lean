import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6FixedCellRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6ScaleData
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LipschitzGraphFrostman

/-!
# Whole-cell height selection for the Node-6 fixed-scale output

This module performs the finite selection at TeX lines 1968--1970 directly
from the Node-6-private indexed cell-mass band.  It does not pass through the
historical sticky cell restriction or Section-6 cover adapter.

First choose a largest occupied coarse height layer.  The paper box gives at
most `4 / rho` occupied layers.  The global indexed-mass budget and the upper
side of the cell-mass band therefore supply enough cells in that layer.  A
cardinality-budgeted subset is then restricted by `restrictCellsWithZero`;
the lower side of the same band supplies the actual selected shading mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Occupied third-coordinate indices of the fixed-scale active cells. -/
def pureWZ2Node6FixedCellHeights
    (cells : Finset WZ2PaperCellIndex) : Finset ℤ :=
  cells.image fun cell => cell.2.2

/-- A largest fiber of a finite map carries the average cardinality. -/
private theorem node6_fixed_exists_max_fiber_with_product_bound
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (cells : Finset α) (label : α → β)
    (hcells : cells.Nonempty) :
    ∃ value ∈ cells.image label,
      cells.card ≤ (cells.image label).card *
        (cells.filter fun cell => label cell = value).card ∧
      (cells.filter fun cell => label cell = value).Nonempty := by
  let values := cells.image label
  let fiber (value : β) := cells.filter fun cell => label cell = value
  have hvalues : values.Nonempty := hcells.image label
  rcases Finset.exists_max_image values (fun value => (fiber value).card)
      hvalues with ⟨value, hvalue, hmax⟩
  have hmaps : Set.MapsTo label (cells : Set α) (values : Set β) :=
    fun cell hcell => Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
  have hsum : cells.card = ∑ other ∈ values, (fiber other).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hbound : cells.card ≤ values.card * (fiber value).card := by
    calc
      cells.card = ∑ other ∈ values, (fiber other).card := hsum
      _ ≤ ∑ _other ∈ values, (fiber value).card := by
        exact Finset.sum_le_sum fun other hother => hmax other hother
      _ = values.card * (fiber value).card := by
        simp [Finset.sum_const]
  have hfiber : (fiber value).Nonempty := by
    rcases Finset.mem_image.mp hvalue with ⟨cell, hcell, hlabel⟩
    exact ⟨cell, Finset.mem_filter.mpr ⟨hcell, hlabel⟩⟩
  exact ⟨value, hvalue, hbound, hfiber⟩

/-- Select enough equal-weight cells to reach `target`, while respecting an
`ENNReal` cardinality budget.  This is the small finite lemma needed here; it
is kept local so this module does not depend on the historical selector. -/
private theorem node6_fixed_exists_subset_card_mass_within_budget
    {α : Type*} [DecidableEq α]
    (cells : Finset α) (weight target budget : ENNReal)
    (hweightZero : weight ≠ 0) (hweightTop : weight ≠ ⊤)
    (htargetTop : target ≠ ⊤)
    (havailable : target ≤ (cells.card : ENNReal) * weight)
    (hbudget : target / weight + 1 ≤ budget) :
    ∃ selected ⊆ cells,
      target ≤ (selected.card : ENNReal) * weight ∧
      (selected.card : ENNReal) ≤ budget := by
  let quotient : ENNReal := target / weight
  have hquotientTop : quotient ≠ ⊤ :=
    ENNReal.div_ne_top htargetTop hweightZero
  let count : ℕ := Nat.ceil quotient.toReal
  have hquotientCells : quotient ≤ (cells.card : ENNReal) :=
    (ENNReal.div_le_iff hweightZero hweightTop).2 havailable
  have hquotientCellsReal : quotient.toReal ≤ (cells.card : ℝ) := by
    exact (ENNReal.toReal_le_toReal hquotientTop (by simp)).2
      hquotientCells
  have hcountCells : count ≤ cells.card :=
    Nat.ceil_le.mpr hquotientCellsReal
  rcases Finset.exists_subset_card_eq hcountCells with
    ⟨selected, hselected, hselectedCard⟩
  have hquotientCount : quotient ≤ (count : ENNReal) := by
    rw [← ENNReal.ofReal_toReal hquotientTop]
    simpa using ENNReal.ofReal_mono (Nat.le_ceil quotient.toReal)
  have htargetCount : target ≤ (count : ENNReal) * weight :=
    (ENNReal.div_le_iff hweightZero hweightTop).1 hquotientCount
  have hcountBudget : (count : ENNReal) ≤ budget := by
    have hceil : (count : ℝ) < quotient.toReal + 1 :=
      Nat.ceil_lt_add_one ENNReal.toReal_nonneg
    have hcountQuotient : (count : ENNReal) ≤ quotient + 1 := by
      have hcast : (count : ENNReal) = ENNReal.ofReal (count : ℝ) := by
        simp
      have hadd : ENNReal.ofReal (quotient.toReal + 1) = quotient + 1 := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num)]
        simp [ENNReal.ofReal_toReal hquotientTop]
      rw [hcast, ← hadd]
      exact ENNReal.ofReal_mono hceil.le
    exact hcountQuotient.trans hbudget
  refine ⟨selected, hselected, ?_, ?_⟩
  · rw [hselectedCard]
    exact htargetCount
  · rw [hselectedCard]
    exact hcountBudget

/-- The ambient zero-extension weight in a coarse cell is exactly the
Node-6-private indexed mass of that cell. -/
private theorem node6_fixed_ambientIndexedCellWeight_eq
    {delta sigma fixedLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := fixedLoss)
      sourceShading rho logExponent)
    (zeroExtension :
      WZ2PaperSubfamilyZeroExtensionData data.selected data.refined)
    (cell : WZ2PaperCellIndex) :
    ambientIndexedCellWeight data zeroExtension cell =
      data.cellIndexedMass cell := by
  classical
  let image : Finset (Fin source.card) :=
    Finset.image data.selected.embedding Finset.univ
  have hzero : ∀ ambient : Fin source.card, ambient ∉ image →
      zeroExtension.ambientShading.carrier ambient = ∅ := by
    intro ambient hambient
    ext point
    constructor
    · intro hpoint
      rcases zeroExtension.carrier_support ambient point hpoint with
        ⟨index, hindex, _⟩
      exact (hambient (Finset.mem_image.mpr
        ⟨index, Finset.mem_univ _, hindex⟩)).elim
    · simp
  rw [ambientIndexedCellWeight, data.cellIndexedMass_eq]
  calc
    ∑ ambient : Fin source.card,
          volume (zeroExtension.ambientShading.carrier ambient ∩
            wz1PaperGridCube rho.1 cell) =
        ∑ ambient ∈ image,
          volume (zeroExtension.ambientShading.carrier ambient ∩
            wz1PaperGridCube rho.1 cell) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro ambient _ hambient
      rw [hzero ambient hambient]
      simp
    _ = ∑ index : Fin data.selected.family.card,
          volume (zeroExtension.ambientShading.carrier
              (data.selected.embedding index) ∩
            wz1PaperGridCube rho.1 cell) := by
      rw [Finset.sum_image]
      intro first _ second _ heq
      exact data.selected.embedding.injective heq
    _ = ∑ index : Fin data.selected.family.card,
          volume (data.refined.carrier index ∩
            wz1PaperGridCube rho.1 cell) := by
      apply Finset.sum_congr rfl
      intro index _
      rw [zeroExtension.carrier_embedding]

/-- A full active-cell restriction gives the exact global indexed-mass
decomposition required by the height pigeonhole. -/
private theorem node6_fixed_refined_mass_eq_sum_cellIndexedMass
    {delta sigma fixedLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := fixedLoss)
      sourceShading rho logExponent)
    (zeroExtension :
      WZ2PaperSubfamilyZeroExtensionData data.selected data.refined) :
    data.refined.mass =
      ∑ cell ∈ data.balanced.activeCells, data.cellIndexedMass cell := by
  rcases data.restrictCellsWithZero zeroExtension
      data.balanced.activeCells (fun _ h => h) with ⟨restricted⟩
  calc
    data.refined.mass = zeroExtension.ambientShading.mass :=
      zeroExtension.mass_eq.symm
    _ = ∑ cell ∈ data.balanced.activeCells,
          ambientIndexedCellWeight data zeroExtension cell :=
      restricted.ambientShading_mass_eq_sum_ambientIndexedCellWeight
    _ = ∑ cell ∈ data.balanced.activeCells,
          data.cellIndexedMass cell := by
      apply Finset.sum_congr rfl
      intro cell _
      exact node6_fixed_ambientIndexedCellWeight_eq data zeroExtension cell

/-- A whole coarse grid cell inside the paper box has both vertical
endpoints in `[-1,1]`. -/
private theorem node6_fixed_gridCube_height_endpoints
    {scale : ℝ} (hscale : 0 < scale)
    (cell : WZ2PaperCellIndex)
    (hbox : wz1PaperGridCube scale cell ⊆
      Kakeya.Streamlined.axisBox 2 2 2) :
    -1 ≤ (cell.2.2 : ℝ) * scale ∧
      ((cell.2.2 : ℝ) + 1) * scale ≤ 1 := by
  let left : ℝ := (cell.2.2 : ℝ) * scale
  let right : ℝ := ((cell.2.2 : ℝ) + 1) * scale
  have hinterval : Set.Ico left right ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro z hz
    let point : Point3 := point3
      (((cell.1 : ℝ) + 1 / 2) * scale)
      (((cell.2.1 : ℝ) + 1 / 2) * scale) z
    have hpoint0 : point 0 = ((cell.1 : ℝ) + 1 / 2) * scale := by
      simp [point, point3]
    have hpoint1 : point 1 = ((cell.2.1 : ℝ) + 1 / 2) * scale := by
      simp [point, point3]
    have hpoint2 : point 2 = z := by
      simp [point, point3]
    have hpoint : point ∈ wz1PaperGridCube scale cell := by
      rw [wz1PaperGridCube_eq_Ico hscale]
      change
        (cell.1 : ℝ) * scale ≤ point 0 ∧
        point 0 < ((cell.1 : ℝ) + 1) * scale ∧
        (cell.2.1 : ℝ) * scale ≤ point 1 ∧
        point 1 < ((cell.2.1 : ℝ) + 1) * scale ∧
        (cell.2.2 : ℝ) * scale ≤ point 2 ∧
        point 2 < ((cell.2.2 : ℝ) + 1) * scale
      rw [hpoint0, hpoint1, hpoint2]
      exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
        hz.1, hz.2⟩
    have hzbox : |z| ≤ 1 := by
      have hpbox := hbox hpoint
      simpa [Kakeya.Streamlined.axisBox, hpoint0, hpoint1, hpoint2] using
        hpbox.2.2
    exact abs_le.mp hzbox
  have hleft : -1 ≤ left :=
    (hinterval ⟨le_rfl, by dsimp only [left, right]; linarith⟩).1
  have hright : right ≤ 1 := by
    have hone : (1 : ℝ) ∈ upperBounds (Set.Ico left right) :=
      fun z hz => (hinterval hz).2
    rw [upperBounds_Ico (by dsimp only [left, right]; linarith)] at hone
    exact hone
  exact ⟨hleft, hright⟩

/-- Active coarse cells in the paper box occupy at most `4 / scale` height
layers. -/
private theorem node6_fixed_cellHeights_card_mul_scale_le_four
    {scale : ℝ} (hscale : 0 < scale) (hscaleOne : scale ≤ 1)
    (cells : Finset WZ2PaperCellIndex)
    (hbox : ∀ cell ∈ cells, wz1PaperGridCube scale cell ⊆
      Kakeya.Streamlined.axisBox 2 2 2) :
    ((pureWZ2Node6FixedCellHeights cells).card : ENNReal) *
        ENNReal.ofReal scale ≤ 4 := by
  by_cases hempty : cells = ∅
  · simp [hempty, pureWZ2Node6FixedCellHeights]
  let values : Finset ℝ :=
    (pureWZ2Node6FixedCellHeights cells).image fun height : ℤ =>
      ((height : ℝ) + 1 / 2) * scale
  have hvalues : values.Nonempty := by
    have hcells : cells.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    exact (hcells.image fun cell => cell.2.2).image _
  have hrange : ∀ value ∈ values, (-1 : ℝ) ≤ value ∧ value ≤ 1 := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with ⟨height, hheight, rfl⟩
    rcases Finset.mem_image.mp hheight with ⟨cell, hcell, rfl⟩
    have hend := node6_fixed_gridCube_height_endpoints
      hscale cell (hbox cell hcell)
    constructor <;> nlinarith
  have hsep : ∀ first ∈ values, ∀ second ∈ values, first ≠ second →
      scale ≤ |first - second| := by
    intro first hfirst second hsecond hne
    rcases Finset.mem_image.mp hfirst with ⟨firstIndex, _, rfl⟩
    rcases Finset.mem_image.mp hsecond with ⟨secondIndex, _, rfl⟩
    have hindexNe : firstIndex ≠ secondIndex := by
      intro heq
      exact hne (by rw [heq])
    have hint : (1 : ℝ) ≤ |((firstIndex - secondIndex : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hindexNe)
    have hcast : ((firstIndex - secondIndex : ℤ) : ℝ) =
        (firstIndex : ℝ) - (secondIndex : ℝ) := by norm_cast
    have hformula :
        ((firstIndex : ℝ) + 1 / 2) * scale -
            ((secondIndex : ℝ) + 1 / 2) * scale =
          ((firstIndex - secondIndex : ℤ) : ℝ) * scale := by
      rw [hcast]
      ring
    rw [hformula, abs_mul, abs_of_pos hscale]
    nlinarith
  have hcount := lemma23_separated_real_finset_card_le
    hscale hvalues hrange hsep
  have hvaluesCard : values.card =
      (pureWZ2Node6FixedCellHeights cells).card := by
    apply Finset.card_image_of_injective
    intro first second heq
    have hcast : (first : ℝ) = (second : ℝ) := by nlinarith
    exact_mod_cast hcast
  rw [hvaluesCard] at hcount
  have hreal : ((pureWZ2Node6FixedCellHeights cells).card : ℝ) *
      scale ≤ 3 := by
    have htwo : (1 : ℝ) - (-1 : ℝ) = 2 := by norm_num
    rw [htwo] at hcount
    calc
      ((pureWZ2Node6FixedCellHeights cells).card : ℝ) * scale ≤
          (2 / scale + 1) * scale := by gcongr
      _ = 2 + scale := by field_simp [hscale.ne']
      _ ≤ 3 := by linarith
  rw [← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact (ENNReal.ofReal_mono hreal).trans (by norm_num)

/-- Provenance for the budgeted subset of the largest occupied Node-6
height layer. -/
structure PureWZ2Node6FixedHeightSelectionProvenance
    {delta sigma fixedLoss slabLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := fixedLoss)
      sourceShading rho logExponent)
    (zeroExtension :
      WZ2PaperSubfamilyZeroExtensionData data.selected data.refined)
    (targetMass coverBudget : ENNReal) where
  height : ℤ
  height_mem :
    height ∈ pureWZ2Node6FixedCellHeights data.balanced.activeCells
  layer : Finset WZ2PaperCellIndex
  layer_eq : layer = data.balanced.activeCells.filter fun cell =>
    cell.2.2 = height
  selectedCells : Finset WZ2PaperCellIndex
  selectedCells_subset_layer : selectedCells ⊆ layer
  selectedCells_nonempty : selectedCells.Nonempty
  selectedCells_mass :
    targetMass ≤ (selectedCells.card : ENNReal) *
      data.cellIndexedMassBase
  selectedCells_budget :
    (selectedCells.card : ENNReal) ≤ coverBudget / 8
  restricted : PureWZ2Node6FixedCellRestrictionData
    data zeroExtension selectedCells
  scaleData : PureWZ2Section6ScaleData
    zeroExtension.ambientShading sigma slabLoss rho
  slabShading_eq : scaleData.slabShading = restricted.shading
  slabLeft_eq : scaleData.slabLeft = (height : ℝ) * rho.1
  slabRight_eq : scaleData.slabRight = ((height : ℝ) + 1) * rho.1

namespace PureWZ2Node6FixedScaleOutput

/-- Select a budgeted subset of the largest occupied height layer and package
it as the stable Section-6 scale data. -/
theorem section6ScaleProvenance_of_global_indexed_mass_budget
    {delta sigma fixedLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := fixedLoss)
      sourceShading rho logExponent)
    (zeroExtension :
      WZ2PaperSubfamilyZeroExtensionData data.selected data.refined)
    (slabLoss : ℝ)
    (fixedLossLeSlab : fixedLoss ≤ slabLoss)
    (targetMass coverBudget : ENNReal)
    (targetMass_eq : targetMass =
      ENNReal.ofReal (Real.pi / 4) *
        Kakeya.realRpowENN delta (slabLoss + 2) *
        source.enncard * ENNReal.ofReal rho.1)
    (coverBudget_eq : coverBudget =
      Kakeya.realRpowENN delta (-slabLoss) *
        Kakeya.realRpowENN rho.1 (-2 + sigma))
    (globalMassBudget :
      4 * data.cellIndexedMassRatio * targetMass ≤
        ENNReal.ofReal rho.1 * data.refined.mass)
    (selectionBudget :
      targetMass / data.cellIndexedMassBase + 1 ≤
        coverBudget / 8) :
    Nonempty (PureWZ2Node6FixedHeightSelectionProvenance
      (slabLoss := slabLoss) data zeroExtension targetMass coverBudget) := by
  have hrho : 0 < rho.1 := data.delta_pos.trans_le rho.2.1
  have hrhoOne : rho.1 ≤ 1 := rho.2.2
  have hsourceNonempty : source.Nonempty := by
    have hcard : data.selected.family.card ≤ source.card := by
      simpa using Fintype.card_le_of_injective
        data.selected.embedding data.selected.embedding.injective
    exact data.selected_nonempty.trans_le hcard
  have htargetPos : 0 < targetMass := by
    rw [targetMass_eq]
    have hpi : 0 < ENNReal.ofReal (Real.pi / 4) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    have hrpow : 0 < Kakeya.realRpowENN delta (slabLoss + 2) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos data.delta_pos _)
    have hfamily : 0 < source.enncard := by
      change (0 : ENNReal) < (source.card : ENNReal)
      exact_mod_cast hsourceNonempty
    have hrhoENN : 0 < ENNReal.ofReal rho.1 :=
      ENNReal.ofReal_pos.mpr hrho
    positivity
  have htargetTop : targetMass ≠ ⊤ := by
    rw [targetMass_eq]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
          simp [Kakeya.realRpowENN]))
        (by simp [Kakeya.Streamlined.TubeFamily.enncard]))
      ENNReal.ofReal_ne_top
  have hglobalMass :=
    node6_fixed_refined_mass_eq_sum_cellIndexedMass data zeroExtension
  have hactiveNonempty : data.balanced.activeCells.Nonempty := by
    by_contra hempty
    have hcells : data.balanced.activeCells = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hrefinedZero : data.refined.mass = 0 := by
      rw [hglobalMass, hcells]
      simp
    have hleftPos :
        0 < 4 * data.cellIndexedMassRatio * targetMass := by
      exact bot_lt_iff_ne_bot.mpr <|
        mul_ne_zero
          (mul_ne_zero (by norm_num) data.cellIndexedMassRatio_pos.ne')
          htargetPos.ne'
    have hle : 4 * data.cellIndexedMassRatio * targetMass ≤ 0 := by
      simpa [hrefinedZero] using globalMassBudget
    exact (not_le_of_gt hleftPos) hle
  rcases node6_fixed_exists_max_fiber_with_product_bound
      data.balanced.activeCells (fun cell => cell.2.2) hactiveNonempty with
    ⟨height, hheight, hheavy, hlayerNonempty⟩
  let layer := data.balanced.activeCells.filter fun cell =>
    cell.2.2 = height
  let heightCount := pureWZ2Node6FixedCellHeights data.balanced.activeCells
  have hcoarseCellBox : ∀ cell ∈ data.balanced.activeCells,
      wz1PaperGridCube rho.1 cell ⊆
        Kakeya.Streamlined.axisBox 2 2 2 := by
    intro cell hcell point hpoint
    have hpointCoarse : point ∈ data.croppedCoarseShading.union := by
      rw [data.balanced.coarse_union_eq]
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpoint⟩
    rcases hpointCoarse with ⟨index, hcarrier⟩
    exact (data.croppedCoarseShading.subset_body index hcarrier).2
  have hheightScale : (heightCount.card : ENNReal) *
      ENNReal.ofReal rho.1 ≤ 4 := by
    exact node6_fixed_cellHeights_card_mul_scale_le_four
      hrho hrhoOne data.balanced.activeCells hcoarseCellBox
  have hheavyENN : (data.balanced.activeCells.card : ENNReal) ≤
      (heightCount.card : ENNReal) * (layer.card : ENNReal) := by
    exact_mod_cast hheavy
  have hrhoActive : ENNReal.ofReal rho.1 *
      (data.balanced.activeCells.card : ENNReal) ≤
      4 * (layer.card : ENNReal) := by
    calc
      ENNReal.ofReal rho.1 *
            (data.balanced.activeCells.card : ENNReal) ≤
          ENNReal.ofReal rho.1 *
            ((heightCount.card : ENNReal) * (layer.card : ENNReal)) := by
        gcongr
      _ = ((heightCount.card : ENNReal) * ENNReal.ofReal rho.1) *
          (layer.card : ENNReal) := by ring
      _ ≤ 4 * (layer.card : ENNReal) := by gcongr
  have hrefinedUpper : data.refined.mass ≤
      (data.balanced.activeCells.card : ENNReal) *
        (data.cellIndexedMassRatio * data.cellIndexedMassBase) := by
    rw [hglobalMass]
    calc
      ∑ cell ∈ data.balanced.activeCells, data.cellIndexedMass cell ≤
          ∑ _cell ∈ data.balanced.activeCells,
            data.cellIndexedMassRatio * data.cellIndexedMassBase := by
        apply Finset.sum_le_sum
        intro cell hcell
        exact (data.cellIndexedMass_band cell hcell).2
      _ = (data.balanced.activeCells.card : ENNReal) *
          (data.cellIndexedMassRatio * data.cellIndexedMassBase) := by
        simp [Finset.sum_const]
  have hsupplyScaled :
      4 * data.cellIndexedMassRatio * targetMass ≤
        (4 * data.cellIndexedMassRatio) *
          ((layer.card : ENNReal) * data.cellIndexedMassBase) := by
    calc
      4 * data.cellIndexedMassRatio * targetMass ≤
          ENNReal.ofReal rho.1 * data.refined.mass := globalMassBudget
      _ ≤ ENNReal.ofReal rho.1 *
          ((data.balanced.activeCells.card : ENNReal) *
            (data.cellIndexedMassRatio * data.cellIndexedMassBase)) := by
        gcongr
      _ = (ENNReal.ofReal rho.1 *
            (data.balanced.activeCells.card : ENNReal)) *
          (data.cellIndexedMassRatio * data.cellIndexedMassBase) := by ring
      _ ≤ (4 * (layer.card : ENNReal)) *
          (data.cellIndexedMassRatio * data.cellIndexedMassBase) := by
        gcongr
      _ = (4 * data.cellIndexedMassRatio) *
          ((layer.card : ENNReal) * data.cellIndexedMassBase) := by ring
  have hfactorZero : (4 * data.cellIndexedMassRatio : ENNReal) ≠ 0 := by
    exact mul_ne_zero (by norm_num) data.cellIndexedMassRatio_pos.ne'
  have hfactorTop : (4 * data.cellIndexedMassRatio : ENNReal) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) data.cellIndexedMassRatio_ne_top
  have hsupply : targetMass ≤
      (layer.card : ENNReal) * data.cellIndexedMassBase := by
    apply (ENNReal.mul_le_mul_iff_left hfactorZero hfactorTop).mp
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsupplyScaled
  rcases node6_fixed_exists_subset_card_mass_within_budget
      layer data.cellIndexedMassBase targetMass (coverBudget / 8)
      data.cellIndexedMassBase_pos.ne' data.cellIndexedMassBase_ne_top
      htargetTop hsupply selectionBudget with
    ⟨selectedCells, hselectedLayer, hselectedMass, hselectedBudget⟩
  have hselectedActive : selectedCells ⊆ data.balanced.activeCells :=
    hselectedLayer.trans (Finset.filter_subset _ _)
  have hselectedHeight : ∀ cell ∈ selectedCells, cell.2.2 = height := by
    intro cell hcell
    exact (Finset.mem_filter.mp (hselectedLayer hcell)).2
  have hselectedNonempty : selectedCells.Nonempty := by
    by_contra hempty
    have hcells : selectedCells = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hle : targetMass ≤ 0 := by
      simpa [hcells] using hselectedMass
    exact (not_le_of_gt htargetPos) hle
  rcases data.restrictCellsWithZero zeroExtension selectedCells
      hselectedActive with ⟨restricted⟩
  have hmass : targetMass ≤ restricted.shading.mass := by
    rw [restricted.shading_mass_eq_sum_ambientIndexedCellWeight]
    calc
      targetMass ≤ (selectedCells.card : ENNReal) *
          data.cellIndexedMassBase := hselectedMass
      _ = ∑ _cell ∈ selectedCells, data.cellIndexedMassBase := by
        simp [Finset.sum_const]
      _ ≤ ∑ cell ∈ selectedCells,
          ambientIndexedCellWeight data zeroExtension cell := by
        apply Finset.sum_le_sum
        intro cell hcell
        rw [node6_fixed_ambientIndexedCellWeight_eq data zeroExtension cell]
        exact (data.cellIndexedMass_band cell (hselectedActive hcell)).1
  rcases hselectedNonempty with ⟨cell, hcell⟩
  have hendpoints := node6_fixed_gridCube_height_endpoints
    hrho cell (hcoarseCellBox cell (hselectedActive hcell))
  have hcellHeight := hselectedHeight cell hcell
  let left : ℝ := (height : ℝ) * rho.1
  let right : ℝ := ((height : ℝ) + 1) * rho.1
  have hleft : -1 ≤ left := by
    simpa [left, hcellHeight] using hendpoints.1
  have hright : right ≤ 1 := by
    simpa [right, hcellHeight] using hendpoints.2
  have hordered : left < right := by
    dsimp only [left, right]
    linarith
  have hwidth : right - left = rho.1 := by
    dsimp only [left, right]
    ring
  have hslabIn : ∀ index, restricted.shading.carrier index ⊆
      horizontalSlab left right := by
    simpa [left, right] using
      restricted.in_height_slab height hselectedHeight
  have hcoverCard : 8 * (selectedCells.card : ENNReal) ≤ coverBudget := by
    have he : (8 : ENNReal) ≠ 0 := by norm_num
    have ht : (8 : ENNReal) ≠ ⊤ := by norm_num
    have hraw := (ENNReal.le_div_iff_mul_le (Or.inl he) (Or.inl ht)).1
      hselectedBudget
    simpa [mul_comm] using hraw
  have hcoverRaw := restricted.cell_cover
  have hcover : CanCoverByBalls restricted.shading.union rho.1 coverBudget := by
    rcases hcoverRaw with ⟨centers, hcentersCard, hcenters⟩
    exact ⟨centers, hcentersCard.trans hcoverCard, hcenters⟩
  have hpoint : ∀ point,
      (restricted.shading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho.1)
            (2 - sigma - slabLoss) * source.enncard := by
    intro point
    have hnat : restricted.shading.pointMultiplicity point ≤
        zeroExtension.ambientShading.pointMultiplicity point := by
      apply Finset.card_le_card
      intro index hindex
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        restricted.subshading_zero index (Finset.mem_filter.mp hindex).2⟩
    have hselectedCard : data.selected.family.enncard ≤ source.enncard := by
      change (data.selected.family.card : ENNReal) ≤ (source.card : ENNReal)
      have hcard : data.selected.family.card ≤ source.card := by
        simpa using Fintype.card_le_of_injective
          data.selected.embedding data.selected.embedding.injective
      exact_mod_cast hcard
    calc
      (restricted.shading.pointMultiplicity point : ENNReal) ≤
          (zeroExtension.ambientShading.pointMultiplicity point : ENNReal) := by
        exact_mod_cast hnat
      _ = (data.refined.pointMultiplicity point : ENNReal) := by
        rw [zeroExtension.node6_pointMultiplicity_eq]
      _ ≤ Kakeya.realRpowENN (delta / rho.1)
            (2 - sigma - fixedLoss) * data.selected.family.enncard :=
        data.fine_pointMultiplicity_upper point
      _ ≤ Kakeya.realRpowENN (delta / rho.1)
            (2 - sigma - slabLoss) * source.enncard := by
        gcongr
        exact pure_wz2_rpowENN_antitone
          (div_pos data.delta_pos hrho)
          ((div_le_one hrho).mpr rho.2.1) (by linarith)
  let scaleData : PureWZ2Section6ScaleData
      zeroExtension.ambientShading sigma slabLoss rho :=
    { slabLeft := left
      slabRight := right
      slabLeft_mem := hleft
      slab_ordered := hordered
      slabRight_mem := hright
      slab_width := hwidth
      slabShading := restricted.shading
      slab_subshading := restricted.subshading_zero
      slab_cubical := restricted.cubical
      slab_in_slab := hslabIn
      slab_mass := by rw [← targetMass_eq]; exact hmass
      slab_cover := by rw [← coverBudget_eq]; exact hcover
      slab_pointMultiplicity_upper := hpoint }
  exact ⟨{
    height := height
    height_mem := hheight
    layer := layer
    layer_eq := rfl
    selectedCells := selectedCells
    selectedCells_subset_layer := hselectedLayer
    selectedCells_nonempty := ⟨cell, hcell⟩
    selectedCells_mass := hselectedMass
    selectedCells_budget := hselectedBudget
    restricted := restricted
    scaleData := scaleData
    slabShading_eq := rfl
    slabLeft_eq := rfl
    slabRight_eq := rfl
  }⟩

/-- Projection of the fixed-height selector to the stable Section-6 input. -/
theorem section6ScaleData_of_global_indexed_mass_budget
    {delta sigma fixedLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := fixedLoss)
      sourceShading rho logExponent)
    (zeroExtension :
      WZ2PaperSubfamilyZeroExtensionData data.selected data.refined)
    (slabLoss : ℝ)
    (fixedLossLeSlab : fixedLoss ≤ slabLoss)
    (targetMass coverBudget : ENNReal)
    (targetMass_eq : targetMass =
      ENNReal.ofReal (Real.pi / 4) *
        Kakeya.realRpowENN delta (slabLoss + 2) *
        source.enncard * ENNReal.ofReal rho.1)
    (coverBudget_eq : coverBudget =
      Kakeya.realRpowENN delta (-slabLoss) *
        Kakeya.realRpowENN rho.1 (-2 + sigma))
    (globalMassBudget :
      4 * data.cellIndexedMassRatio * targetMass ≤
        ENNReal.ofReal rho.1 * data.refined.mass)
    (selectionBudget :
      targetMass / data.cellIndexedMassBase + 1 ≤
        coverBudget / 8) :
    Nonempty (PureWZ2Section6ScaleData
      zeroExtension.ambientShading sigma slabLoss rho) := by
  rcases data.section6ScaleProvenance_of_global_indexed_mass_budget
      zeroExtension slabLoss fixedLossLeSlab targetMass coverBudget
      targetMass_eq coverBudget_eq globalMassBudget selectionBudget with
    ⟨provenance⟩
  exact ⟨provenance.scaleData⟩

end PureWZ2Node6FixedScaleOutput

end Kakeya.Assouad

end
