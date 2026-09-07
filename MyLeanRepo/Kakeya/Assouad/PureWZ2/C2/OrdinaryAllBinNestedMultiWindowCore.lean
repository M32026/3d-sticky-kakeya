import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryAllBinNestedSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleStatements

/-!
# Multi-window output of the nested ordinary regional construction

After choosing one nested rich output in each regularized source block and a
mass-heavy block residue, the final shading is their finite union on the
original source family.  The selected source bin and nested coarse bin remain
part of each output's dependent provenance.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2OrdinaryAllBinNestedRegionalData
namespace SelectedBlockResidueData

variable
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta finalLoss
      theoremEta volumeLoss outerLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {companions : PureWZ2OrdinaryAllBinOuterPopularCompanionData carriers}
    {regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions}

/-- Source-independent envelope for the parent-fibre dyadic regularization. -/
def parentBinCost (rho : ℝ) : ENNReal :=
  2 * ENNReal.ofReal
    (wz2PaperBoundaryLogCoefficient * (1 + Real.log (Real.sqrt rho)⁻¹))

/-- Source-global-bin count at the original `delta` resolution. -/
def sourceBinCost (delta rho sigma inputLoss : ℝ) : ENNReal :=
  132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
    Kakeya.realRpowENN (1 / delta) (1 - sigma)

/-- Nested genuine-coarse global-bin count at resolution `rho`. -/
def nestedBinCost (rho sigma middleLoss : ℝ) : ENNReal :=
  132 * (10 * Kakeya.realRpowENN rho (-middleLoss)) *
    Kakeya.realRpowENN (1 / rho) (1 - sigma)

/-- Complete runtime-independent cost of the nested regional output. -/
def totalCost (delta rho sigma inputLoss middleLoss outerLoss extraLoss : ℝ) :
    ENNReal :=
  4096 * Kakeya.realRpowENN (256 * rho) (-outerLoss) *
    parentBinCost rho *
    pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
    pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho *
    PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost rho extraLoss *
    sourceBinCost delta rho sigma inputLoss *
    nestedBinCost rho sigma middleLoss

theorem parentBinCost_bound
    (block : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}) :
    ((regional.weightClass block).bins : ENNReal) ≤ parentBinCost rho := by
  simpa [parentBinCost, twoScale.sqrtRequested_eq] using
    PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData.bins_le_logEnvelope
      (regional.weightClass block)

theorem sourceBinCost_bound
    (block : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}) :
    ((regional.sourceBins block).line.globalBins.card : ENNReal) ≤
      sourceBinCost delta rho sigma inputLoss := by
  exact (regional.sourceBins block).line.global_bin_count

theorem nestedBinCost_bound
    (block : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe})
    (bin : {bin // bin ∈ (regional.sourceBins block).line.globalBins}) :
    (((regional.family block).good bin).selected.card : ENNReal) ≤
      nestedBinCost rho sigma middleLoss := by
  have hselectedNat : ((regional.family block).good bin).selected.card ≤
      ((regional.family block).nested bin).fixedLine.line.globalBins.card := by
    simpa using Finset.card_le_univ ((regional.family block).good bin).selected
  calc
    (((regional.family block).good bin).selected.card : ENNReal) ≤
        ((((regional.family block).nested bin).fixedLine.line.globalBins.card :
          ℕ) : ENNReal) := by
      exact_mod_cast hselectedNat
    _ ≤ nestedBinCost rho sigma middleLoss := by
      simpa [nestedBinCost, twoScale.rhoRequested_eq] using
        ((regional.family block).nested bin).fixedLine.line.global_bin_count

theorem sourceBinCost_pos
    (hdelta : 0 < delta) : 0 < sourceBinCost delta rho sigma inputLoss := by
  have hinputPower : 0 < Kakeya.realRpowENN delta (-inputLoss) := by
    unfold Kakeya.realRpowENN
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)
  have hinversePower :
      0 < Kakeya.realRpowENN (1 / delta) (1 - sigma) := by
    unfold Kakeya.realRpowENN
    exact ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos (one_div_pos.mpr hdelta) _)
  have hten : 0 < (10 : ENNReal) * Kakeya.realRpowENN delta (-inputLoss) :=
    ENNReal.mul_pos (by norm_num) hinputPower.ne'
  have hprefix :
      0 < (132 : ENNReal) *
        (10 * Kakeya.realRpowENN delta (-inputLoss)) :=
    ENNReal.mul_pos (by norm_num) hten.ne'
  unfold sourceBinCost
  exact ENNReal.mul_pos hprefix.ne' hinversePower.ne'

theorem sourceBinCost_ne_top :
    sourceBinCost delta rho sigma inputLoss ≠ ⊤ := by
  unfold sourceBinCost
  repeat' apply ENNReal.mul_ne_top
  all_goals simp [Kakeya.realRpowENN]

theorem nestedBinCost_pos
    (hrho : 0 < rho) : 0 < nestedBinCost rho sigma middleLoss := by
  have hmiddlePower : 0 < Kakeya.realRpowENN rho (-middleLoss) := by
    unfold Kakeya.realRpowENN
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hrho _)
  have hinversePower :
      0 < Kakeya.realRpowENN (1 / rho) (1 - sigma) := by
    unfold Kakeya.realRpowENN
    exact ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos (one_div_pos.mpr hrho) _)
  have hten : 0 < (10 : ENNReal) * Kakeya.realRpowENN rho (-middleLoss) :=
    ENNReal.mul_pos (by norm_num) hmiddlePower.ne'
  have hprefix :
      0 < (132 : ENNReal) *
        (10 * Kakeya.realRpowENN rho (-middleLoss)) :=
    ENNReal.mul_pos (by norm_num) hten.ne'
  unfold nestedBinCost
  exact ENNReal.mul_pos hprefix.ne' hinversePower.ne'

theorem nestedBinCost_ne_top :
    nestedBinCost rho sigma middleLoss ≠ ⊤ := by
  unfold nestedBinCost
  repeat' apply ENNReal.mul_ne_top
  all_goals simp [Kakeya.realRpowENN]

theorem parentBinCost_pos (hrho : 0 < rho) (hrhoOne : rho ≤ 1) :
    0 < parentBinCost rho := by
  have hcoefficient : 0 < wz2PaperBoundaryLogCoefficient := by
    unfold wz2PaperBoundaryLogCoefficient
    exact lt_of_lt_of_le
      (div_pos (by norm_num) (Real.log_pos (by norm_num)))
      (le_max_right _ _)
  have hrootPos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  have hrootOne : Real.sqrt rho ≤ 1 := Real.sqrt_le_one.mpr hrhoOne
  have hinvOne : 1 ≤ (Real.sqrt rho)⁻¹ :=
    (one_le_inv₀ hrootPos).mpr hrootOne
  have hlogNonneg : 0 ≤ Real.log (Real.sqrt rho)⁻¹ :=
    Real.log_nonneg hinvOne
  unfold parentBinCost
  exact ENNReal.mul_pos (by norm_num)
    (ENNReal.ofReal_pos.mpr (mul_pos hcoefficient (by linarith))).ne'

theorem parentBinCost_ne_top : parentBinCost rho ≠ ⊤ := by
  unfold parentBinCost
  exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top

theorem totalCost_pos
    (hdelta : 0 < delta) (hrho : 0 < rho) (hrhoOne : rho ≤ 1) :
    0 < totalCost delta rho sigma inputLoss middleLoss outerLoss extraLoss := by
  have hparent : 0 < parentBinCost rho := parentBinCost_pos hrho hrhoOne
  have hsourceBins : 0 < sourceBinCost delta rho sigma inputLoss :=
    sourceBinCost_pos hdelta
  have hnestedBins : 0 < nestedBinCost rho sigma middleLoss :=
    nestedBinCost_pos hrho
  have hsourceCost : 0 < pureWZ2BalancedSafeSourceBinVolumeCost rho delta := by
    have hfiberNat : 0 < pureWZ2SourceFixedLineParentFiberBound delta rho := by
      unfold pureWZ2SourceFixedLineParentFiberBound
        pureWZ2SourceFixedLineParentYBound
      omega
    have hfiber :
        0 < (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) := by
      exact_mod_cast hfiberNat
    have hraw : 0 < pureWZ2BalancedSafeSourceBinRawVolumeCost rho delta := by
      have hwidth : 0 < ENNReal.ofReal (Real.sqrt rho + 2 * rho) :=
        ENNReal.ofReal_pos.mpr (by
          have := Real.sqrt_pos.mpr hrho
          linarith)
      have hdeltaArea : 0 < ENNReal.ofReal delta ^ 2 :=
        by
          simpa [pow_two] using ENNReal.mul_pos
            (ENNReal.ofReal_pos.mpr hdelta).ne'
            (ENNReal.ofReal_pos.mpr hdelta).ne'
      have hpi : 0 < ENNReal.ofReal Real.pi :=
        ENNReal.ofReal_pos.mpr Real.pi_pos
      have harea :
          0 < ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi :=
        ENNReal.mul_pos hdeltaArea.ne' hpi.ne'
      have hgeometry : 0 < ENNReal.ofReal (Real.sqrt rho + 2 * rho) *
          (ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi) :=
        ENNReal.mul_pos hwidth.ne' harea.ne'
      have hfibred : 0 < ENNReal.ofReal (Real.sqrt rho + 2 * rho) *
            (ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi) *
          (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) :=
        ENNReal.mul_pos hgeometry.ne' hfiber.ne'
      unfold pureWZ2BalancedSafeSourceBinRawVolumeCost
      exact ENNReal.mul_pos hfibred.ne' (by norm_num)
    unfold pureWZ2BalancedSafeSourceBinVolumeCost
    apply ENNReal.div_pos
    · exact hraw.ne'
    · rw [wz1PaperGridCube_volume_exact hrho]
      exact ENNReal.ofReal_ne_top
  have hnestedCost : 0 <
      pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho := by
    have hwidth : 0 < ENNReal.ofReal (Real.sqrt rho + 2 * rho) :=
      ENNReal.ofReal_pos.mpr (by
        have := Real.sqrt_pos.mpr hrho
        linarith)
    have hrhoArea : 0 < ENNReal.ofReal rho ^ 2 :=
      by
        simpa [pow_two] using ENNReal.mul_pos
          (ENNReal.ofReal_pos.mpr hrho).ne'
          (ENNReal.ofReal_pos.mpr hrho).ne'
    have hpi : 0 < ENNReal.ofReal Real.pi :=
      ENNReal.ofReal_pos.mpr Real.pi_pos
    have harea : 0 < ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi :=
      ENNReal.mul_pos hrhoArea.ne' hpi.ne'
    have hprefactor :
        0 < (125 : ENNReal) * ENNReal.ofReal (Real.sqrt rho + 2 * rho) :=
      ENNReal.mul_pos (by norm_num) hwidth.ne'
    unfold pureWZ2BalancedSafeNestedCoarseRawVolumeCost
    exact ENNReal.mul_pos hprefactor.ne' harea.ne'
  have hheightCost : 0 <
      PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
        rho extraLoss := by
    unfold PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
      PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap
    exact ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr
        (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by positivity) _))).ne'
      (ENNReal.ofReal_pos.mpr (div_pos (by norm_num) (Real.sqrt_pos.mpr (by
        positivity)))).ne'
  have houter : 0 < Kakeya.realRpowENN (256 * rho) (-outerLoss) := by
    unfold Kakeya.realRpowENN
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)
  have h1 : 0 < (4096 : ENNReal) *
      Kakeya.realRpowENN (256 * rho) (-outerLoss) :=
    ENNReal.mul_pos (by norm_num) houter.ne'
  have h2 : 0 < 4096 * Kakeya.realRpowENN (256 * rho) (-outerLoss) *
      parentBinCost rho := ENNReal.mul_pos h1.ne' hparent.ne'
  have h3 : 0 < 4096 * Kakeya.realRpowENN (256 * rho) (-outerLoss) *
      parentBinCost rho * pureWZ2BalancedSafeSourceBinVolumeCost rho delta :=
    ENNReal.mul_pos h2.ne' hsourceCost.ne'
  have h4 : 0 < 4096 * Kakeya.realRpowENN (256 * rho) (-outerLoss) *
        parentBinCost rho * pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
      pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho :=
    ENNReal.mul_pos h3.ne' hnestedCost.ne'
  have h5 : 0 < 4096 * Kakeya.realRpowENN (256 * rho) (-outerLoss) *
          parentBinCost rho * pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
        pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho *
      PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
        rho extraLoss := ENNReal.mul_pos h4.ne' hheightCost.ne'
  have h6 : 0 < 4096 * Kakeya.realRpowENN (256 * rho) (-outerLoss) *
            parentBinCost rho * pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
          pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss * sourceBinCost delta rho sigma inputLoss :=
    ENNReal.mul_pos h5.ne' hsourceBins.ne'
  unfold totalCost
  exact ENNReal.mul_pos h6.ne' hnestedBins.ne'

theorem totalCost_ne_top (hrho : 0 < rho) :
    totalCost delta rho sigma inputLoss middleLoss outerLoss extraLoss ≠ ⊤ := by
  have hcubeZero : volume (wz1PaperGridCube rho (0, 0, 0)) ≠ 0 :=
    (wz1PaperGridCube_volume_pos hrho (0, 0, 0)).ne'
  have hwidthTop : ENNReal.ofReal (Real.sqrt rho + 2 * rho) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hdeltaAreaTop : ENNReal.ofReal delta ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hrhoAreaTop : ENNReal.ofReal rho ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hpiTop : ENNReal.ofReal Real.pi ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsourceAreaTop :
      ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi ≠ ⊤ :=
    ENNReal.mul_ne_top hdeltaAreaTop hpiTop
  have hsourceGeometryTop : ENNReal.ofReal (Real.sqrt rho + 2 * rho) *
      (ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi) ≠ ⊤ :=
    ENNReal.mul_ne_top hwidthTop hsourceAreaTop
  have hsourceFiberTop : ENNReal.ofReal (Real.sqrt rho + 2 * rho) *
        (ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi) *
      (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top hsourceGeometryTop (ENNReal.natCast_ne_top _)
  have hsourceRawTop : pureWZ2BalancedSafeSourceBinRawVolumeCost rho delta ≠ ⊤ := by
    unfold pureWZ2BalancedSafeSourceBinRawVolumeCost
    exact ENNReal.mul_ne_top hsourceFiberTop (by norm_num)
  have hsourceCostTop :
      pureWZ2BalancedSafeSourceBinVolumeCost rho delta ≠ ⊤ := by
    unfold pureWZ2BalancedSafeSourceBinVolumeCost
    exact ENNReal.div_ne_top hsourceRawTop hcubeZero
  have hnestedCostTop :
      pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho ≠ ⊤ := by
    have hprefixTop :
        (125 : ENNReal) * ENNReal.ofReal (Real.sqrt rho + 2 * rho) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) hwidthTop
    have hareaTop : ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi ≠ ⊤ :=
      ENNReal.mul_ne_top hrhoAreaTop hpiTop
    unfold pureWZ2BalancedSafeNestedCoarseRawVolumeCost
    exact ENNReal.mul_ne_top hprefixTop hareaTop
  have hheightTop :
      PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
        rho extraLoss ≠ ⊤ := by
    unfold PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
      PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have houterTop : Kakeya.realRpowENN (256 * rho) (-outerLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have h1 : (4096 : ENNReal) *
      Kakeya.realRpowENN (256 * rho) (-outerLoss) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) houterTop
  have h2 : 4096 * Kakeya.realRpowENN (256 * rho) (-outerLoss) *
      parentBinCost rho ≠ ⊤ := ENNReal.mul_ne_top h1 parentBinCost_ne_top
  have h3 : 4096 * Kakeya.realRpowENN (256 * rho) (-outerLoss) *
      parentBinCost rho * pureWZ2BalancedSafeSourceBinVolumeCost rho delta ≠ ⊤ :=
    ENNReal.mul_ne_top h2 hsourceCostTop
  have h4 : 4096 * Kakeya.realRpowENN (256 * rho) (-outerLoss) *
        parentBinCost rho * pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
      pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho ≠ ⊤ :=
    ENNReal.mul_ne_top h3 hnestedCostTop
  have h5 : 4096 * Kakeya.realRpowENN (256 * rho) (-outerLoss) *
          parentBinCost rho * pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
        pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho *
      PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
        rho extraLoss ≠ ⊤ := ENNReal.mul_ne_top h4 hheightTop
  have h6 : 4096 * Kakeya.realRpowENN (256 * rho) (-outerLoss) *
            parentBinCost rho * pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
          pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss * sourceBinCost delta rho sigma inputLoss ≠ ⊤ :=
    ENNReal.mul_ne_top h5 sourceBinCost_ne_top
  unfold totalCost
  exact ENNReal.mul_ne_top h6 nestedBinCost_ne_top

/-- Finite union of the selected original-family nested height lifts. -/
def shading (residueData : regional.SelectedBlockResidueData) :
    WZ1PaperTubeShading source.family where
  carrier sourceIndex := ⋃ index : Fin residueData.retained.card,
    (regional.selectedShading
      (residueData.selectedIndex index)).carrier sourceIndex
  measurable_carrier sourceIndex := MeasurableSet.iUnion fun index =>
    (regional.selectedShading
      (residueData.selectedIndex index)).measurable_carrier
        sourceIndex
  subset_body sourceIndex := by
    intro point hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨index, hindex⟩
    exact (regional.selectedShading
      (residueData.selectedIndex index)).subset_body
        sourceIndex hindex

@[simp] theorem mem_shading_carrier_iff
    (residueData : regional.SelectedBlockResidueData)
    (sourceIndex : Fin source.family.card) (point : Point3) :
    point ∈ residueData.shading.carrier sourceIndex ↔
      ∃ index : Fin residueData.retained.card,
        point ∈ (regional.selectedShading
          (residueData.selectedIndex index)).carrier
            sourceIndex := by
  simp [shading]

theorem subshading (residueData : regional.SelectedBlockResidueData) :
    PureWZ2PaperIsSubshading residueData.shading source.shading := by
  intro sourceIndex point hpoint
  rcases (residueData.mem_shading_carrier_iff sourceIndex point).mp hpoint with
    ⟨index, hindex⟩
  exact (regional.selectedRich
    (residueData.selectedIndex index)).heightLift.subshading sourceIndex hindex

theorem cubical (residueData : regional.SelectedBlockResidueData) :
    WZ1PaperIsCubicalShading residueData.shading := by
  intro sourceIndex point hpoint other hother
  rcases (residueData.mem_shading_carrier_iff sourceIndex point).mp hpoint with
    ⟨index, hindex⟩
  exact (residueData.mem_shading_carrier_iff sourceIndex other).mpr
    ⟨index, (regional.selectedRich
      (residueData.selectedIndex index)).heightLift.whole_cells
        sourceIndex point hindex hother⟩

theorem mem_shading_union_iff
    (residueData : regional.SelectedBlockResidueData) (point : Point3) :
    point ∈ residueData.shading.union ↔
      ∃ index : Fin residueData.retained.card,
        point ∈ (regional.selectedShading
          (residueData.selectedIndex index)).union := by
  constructor
  · rintro ⟨sourceIndex, hpoint⟩
    rcases (residueData.mem_shading_carrier_iff
      sourceIndex point).mp hpoint with ⟨index, hindex⟩
    exact ⟨index, sourceIndex, hindex⟩
  · rintro ⟨index, sourceIndex, hpoint⟩
    exact ⟨sourceIndex,
      (residueData.mem_shading_carrier_iff sourceIndex point).mpr
        ⟨index, hpoint⟩⟩

theorem heightLift_union_pairwise_disjoint
    (residueData : regional.SelectedBlockResidueData) :
    Pairwise fun first second : Fin residueData.retained.card =>
      Disjoint
        (regional.selectedShading
          (residueData.selectedIndex first)).union
        (regional.selectedShading
          (residueData.selectedIndex second)).union := by
  intro first second hne
  rw [Set.disjoint_left]
  intro point hfirst hsecond
  let z := point (2 : Fin 3)
  have hfirstSlice : horizontalSlice
      (regional.selectedShading
        (residueData.selectedIndex first)).union z ≠ ∅ := by
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨point, hfirst, rfl⟩
  have hsecondSlice : horizontalSlice
      (regional.selectedShading
        (residueData.selectedIndex second)).union z ≠ ∅ := by
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨point, hsecond, rfl⟩
  have hfirstCore := (regional.selectedRich
    (residueData.selectedIndex first)).heightLift.active_height_coverage
      z hfirstSlice
  have hsecondCore := (regional.selectedRich
    (residueData.selectedIndex second)).heightLift.active_height_coverage
      z hsecondSlice
  have hsep := residueData.separated_cores regional first second hne
    z hfirstCore z hsecondCore
  have hscalePos : 0 < pureWZ2SourceHorizontalFinalScale rho := by
    have hrho : 0 < rho :=
      (regional.sourceBins
        (residueData.selectedIndex first)).line.rho_pos
    unfold pureWZ2SourceHorizontalFinalScale
    positivity
  exact (not_le_of_gt (Real.sqrt_pos.mpr hscalePos)) (by simpa using hsep)

theorem heightLift_carrier_pairwise_disjoint
    (residueData : regional.SelectedBlockResidueData)
    (sourceIndex : Fin source.family.card) :
    Pairwise fun first second : Fin residueData.retained.card =>
      Disjoint
        ((regional.selectedShading
          (residueData.selectedIndex first)).carrier
            sourceIndex)
        ((regional.selectedShading
          (residueData.selectedIndex second)).carrier
            sourceIndex) := by
  intro first second hne
  exact (residueData.heightLift_union_pairwise_disjoint hne).mono
    (fun point (hpoint : point ∈ (regional.selectedShading
        (residueData.selectedIndex first)).carrier
          sourceIndex) =>
      show point ∈ (regional.selectedShading
        (residueData.selectedIndex first)).union from
        ⟨sourceIndex, hpoint⟩)
    (fun point (hpoint : point ∈ (regional.selectedShading
        (residueData.selectedIndex second)).carrier
          sourceIndex) =>
      show point ∈ (regional.selectedShading
        (residueData.selectedIndex second)).union from
        ⟨sourceIndex, hpoint⟩)

theorem shading_mass_eq_sum
    (residueData : regional.SelectedBlockResidueData) :
    residueData.shading.mass =
      ∑ index : Fin residueData.retained.card,
        regional.selectedMass (residueData.selectedIndex index) := by
  calc
    residueData.shading.mass =
        ∑ sourceIndex : Fin source.family.card,
          volume (⋃ index : Fin residueData.retained.card,
            (regional.selectedShading
              (residueData.selectedIndex index)).carrier
                sourceIndex) := rfl
    _ = ∑ sourceIndex : Fin source.family.card,
          ∑ index : Fin residueData.retained.card,
            volume ((regional.selectedShading
              (residueData.selectedIndex index)).carrier
                sourceIndex) := by
      apply Finset.sum_congr rfl
      intro sourceIndex _
      rw [MeasureTheory.measure_iUnion
        (residueData.heightLift_carrier_pairwise_disjoint sourceIndex)
        (fun index => (regional.selectedShading
          (residueData.selectedIndex index)).measurable_carrier
            sourceIndex)]
      simp [tsum_fintype]
    _ = ∑ index : Fin residueData.retained.card,
          ∑ sourceIndex : Fin source.family.card,
            volume ((regional.selectedShading
              (residueData.selectedIndex index)).carrier
                sourceIndex) := by
      rw [Finset.sum_comm]
    _ = ∑ index : Fin residueData.retained.card,
        regional.selectedMass (residueData.selectedIndex index) := rfl

theorem total_mass_le_shading_mass
    (residueData : regional.SelectedBlockResidueData) :
    (∑ block : {block //
        block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      regional.selectedMass block) ≤ 64 * residueData.shading.mass := by
  rw [residueData.shading_mass_eq_sum]
  exact residueData.total_mass_le

/-- Pay the two finite maximum selections and the mod-64 residue after the
aggregate genuine-coarse regional estimate.  The first-cover `cellMass` stays
on the left; it is not replaced by geometric cube volume. -/
theorem selected_nested_mass_bound
    (residueData : regional.SelectedBlockResidueData)
    (outerCost parentCost sourceBinCost nestedBinCost : ENNReal)
    (houterCost : ∀ block : {block //
        block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      (2 * (carriers.carrier block.1).outerPopular.popular.bins : ENNReal) ≤
        outerCost)
    (hparentCost : ∀ block : {block //
        block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((regional.weightClass block).bins : ENNReal) ≤ parentCost)
    (hsourceBinCost : ∀ block : {block //
        block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((regional.sourceBins block).line.globalBins.card : ENNReal) ≤
        sourceBinCost)
    (hnestedBinCost : ∀ block : {block //
        block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ∀ bin : {bin // bin ∈ (regional.sourceBins block).line.globalBins},
        (((regional.family block).good bin).selected.card : ENNReal) ≤
          nestedBinCost)
    {extraLoss : ℝ}
    (hextraPower : ∀ block : {block //
        block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ∀ bin : {bin // bin ∈ (regional.sourceBins block).line.globalBins},
      ∀ nestedBin : {nestedBin //
          nestedBin ∈ ((regional.family block).good bin).selected},
        ((((regional.family block).rich bin).pipeline
          nestedBin).preparedGraph.graph.residue.extraCost : ℝ) ≤
          Real.rpow (((regional.family block).nested bin).preparation
            nestedBin.1).prep.graphScale (-extraLoss)) :
    volume prepared.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          twoScale.coarse.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      4096 * outerCost * parentCost *
        pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
        pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss * sourceBinCost * nestedBinCost *
        residueData.shading.mass := by
  let geometricCost : ENNReal := 64 * outerCost * parentCost *
    pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
    pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho *
    PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
      rho extraLoss
  have haggregate := regional.aggregate_heightLift_mass_bound
    outerCost parentCost houterCost hparentCost hextraPower
  have hblocks :
      (∑ block : {block //
          block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
        ∑ bin : {bin // bin ∈ (regional.sourceBins block).line.globalBins},
          ∑ nestedBin : {nestedBin //
              nestedBin ∈ ((regional.family block).good bin).selected},
            (((regional.family block).rich bin).rich
              nestedBin).heightLift.shading.mass) ≤
        sourceBinCost * nestedBinCost *
          ∑ block : {block //
            block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
              regional.selectedMass block := by
    calc
      _ ≤ ∑ block : {block //
          block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
        sourceBinCost * nestedBinCost * regional.selectedMass block := by
          apply Finset.sum_le_sum
          intro block _
          calc
            _ ≤ ((regional.sourceBins block).line.globalBins.card : ENNReal) *
                (((regional.family block).good
                  (regional.selectedSourceBin block)).selected.card : ENNReal) *
                regional.selectedMass block := by
              simpa [PureWZ2OrdinaryAllBinNestedRegionalData.selectedMass,
                PureWZ2OrdinaryAllBinNestedRegionalData.selectedRich] using
                regional.block_mass_le_selected block
            _ ≤ sourceBinCost * nestedBinCost *
                regional.selectedMass block := by
              gcongr
              · exact hsourceBinCost block
              · exact hnestedBinCost block (regional.selectedSourceBin block)
      _ = sourceBinCost * nestedBinCost *
          ∑ block : {block //
            block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
              regional.selectedMass block := by
        rw [Finset.mul_sum]
  calc
    _ ≤ geometricCost *
        ∑ block : {block //
          block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
            ∑ bin : {bin //
                bin ∈ (regional.sourceBins block).line.globalBins},
              ∑ nestedBin : {nestedBin //
                  nestedBin ∈ ((regional.family block).good bin).selected},
                (((regional.family block).rich bin).rich
                  nestedBin).heightLift.shading.mass := by
      simpa [geometricCost] using haggregate
    _ ≤ geometricCost *
        (sourceBinCost * nestedBinCost *
          ∑ block : {block //
            block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
              regional.selectedMass block) := by gcongr
    _ ≤ geometricCost *
        (sourceBinCost * nestedBinCost * (64 * residueData.shading.mass)) := by
      gcongr
      exact residueData.total_mass_le_shading_mass
    _ = _ := by
      dsimp only [geometricCost]
      ring

def trapezoids (residueData : regional.SelectedBlockResidueData) :
    Finset WZ1VerticalTrapezoid :=
  Finset.univ.image fun index =>
    regional.selectedTrapezoid (residueData.selectedIndex index)

theorem trapezoids_nonempty
    (residueData : regional.SelectedBlockResidueData) :
    residueData.trapezoids.Nonempty := by
  let first : Fin residueData.retained.card :=
    ⟨0, Finset.card_pos.mpr residueData.retained_nonempty⟩
  exact ⟨regional.selectedTrapezoid (residueData.selectedIndex first),
    Finset.mem_image.mpr ⟨first, Finset.mem_univ _, rfl⟩⟩

theorem rich_scale_eq
    (residueData : regional.SelectedBlockResidueData)
    (index : Fin residueData.retained.card) :
    (regional.selectedRich
      (residueData.selectedIndex index)).richTrapezoid.scale =
        pureWZ2SourceHorizontalFinalScale rho := by
  rw [(regional.selectedRich
    (residueData.selectedIndex index)).richTrapezoid.scale_eq]
  rw [((regional.family (residueData.selectedIndex index)).nested
    (regional.selectedSourceBin (residueData.selectedIndex index))).preparation
      (regional.selectedNestedBin (residueData.selectedIndex index)
        (regional.selectedSourceBin
          (residueData.selectedIndex index))).1 |>.prep.graphScale_eq]
  simp [pureWZ2SourceHorizontalFinalScale]
  ring

theorem dense_of_total_mass
    (residueData : regional.SelectedBlockResidueData)
    {structuralLoss : ℝ}
    (hdense : 64 * (Kakeya.realRpowENN delta structuralLoss *
        (wz1PaperBodyFamily source.family).mass) ≤
      ∑ block : {block //
          block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
        regional.selectedMass block) :
    residueData.shading.IsLambdaDense
      (Kakeya.realRpowENN delta structuralLoss) := by
  unfold Kakeya.Streamlined.Shading.IsLambdaDense
  apply (ENNReal.mul_le_mul_iff_left
    (show (64 : ENNReal) ≠ 0 by norm_num)
    (show (64 : ENNReal) ≠ ⊤ by norm_num)).mp
  simpa [mul_comm] using
    hdense.trans residueData.total_mass_le_shading_mass

/-- Cancel a concrete selected-mass estimate against the first-sticky relative
mass lower bound.  The exact first-cover `cellMass` appears on both sides of
the calculation and is never identified with physical cube volume. -/
theorem dense_of_selected_nested_mass
    (residueData : regional.SelectedBlockResidueData)
    (cost : ENNReal) (hcostPos : 0 < cost) (hcostTop : cost ≠ ⊤)
    {structuralLoss : ℝ}
    (hselected :
      volume prepared.shadow.union *
            (twoScale.coarse.fineMultiplicity : ENNReal) *
            twoScale.coarse.balanced.cellMass *
            pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
        cost * residueData.shading.mass)
    (hpower :
      2 * cost * Kakeya.realRpowENN delta structuralLoss ≤
        wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta inputLoss *
          Kakeya.realRpowENN rho
            (stickyLoss + twoScale.coarseLoss) *
          twoScale.coarse.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss) :
    residueData.shading.IsLambdaDense
      (Kakeya.realRpowENN delta structuralLoss) := by
  let target := Kakeya.realRpowENN delta structuralLoss *
    (wz1PaperBodyFamily source.family).mass
  have hrelative := prepared.relative_mass_via_multiplicity_lower
  have hscaledTwo : (2 : ENNReal) * (cost * target) ≤
      2 * (cost * residueData.shading.mass) := by
    calc
      (2 : ENNReal) * (cost * target) =
          (2 * cost * Kakeya.realRpowENN delta structuralLoss) *
            (wz1PaperBodyFamily source.family).mass := by
        simp only [target]
        ring
      _ ≤ (wz2PaperPureRefinementFraction delta logExponent *
            Kakeya.realRpowENN delta inputLoss *
            Kakeya.realRpowENN rho
              (stickyLoss + twoScale.coarseLoss) *
            twoScale.coarse.balanced.cellMass *
            pureWZ2SourceHorizontalRichFloor rho finalLoss) *
          (wz1PaperBodyFamily source.family).mass := by
        exact mul_le_mul_right' hpower (wz1PaperBodyFamily source.family).mass
      _ = (wz2PaperPureRefinementFraction delta logExponent *
            (Kakeya.realRpowENN delta inputLoss *
              (wz1PaperBodyFamily source.family).mass) *
            Kakeya.realRpowENN rho
              (stickyLoss + twoScale.coarseLoss)) *
          twoScale.coarse.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss := by ring
      _ ≤ (2 * (volume prepared.shadow.union *
            (twoScale.coarse.fineMultiplicity : ENNReal))) *
          twoScale.coarse.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss := by
        exact mul_le_mul_right' (mul_le_mul_right' (by
          simpa [mul_assoc] using hrelative)
            twoScale.coarse.balanced.cellMass)
          (pureWZ2SourceHorizontalRichFloor rho finalLoss)
      _ = 2 * (volume prepared.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          twoScale.coarse.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss) := by ring
      _ ≤ 2 * (cost * residueData.shading.mass) := by
        exact mul_le_mul_left' hselected 2
  have hscaled : cost * target ≤ cost * residueData.shading.mass :=
    (ENNReal.mul_le_mul_iff_right
      (show (2 : ENNReal) ≠ 0 by norm_num)
      (show (2 : ENNReal) ≠ ⊤ by norm_num)).mp (by
        simpa [mul_comm] using hscaledTwo)
  have hdense : target ≤ residueData.shading.mass :=
    (ENNReal.mul_le_mul_iff_left hcostPos.ne' hcostTop).mp (by
      simpa [mul_comm] using hscaled)
  simpa [Kakeya.Streamlined.Shading.IsLambdaDense, target] using hdense



end SelectedBlockResidueData
end PureWZ2OrdinaryAllBinNestedRegionalData

end Kakeya.Assouad

end
