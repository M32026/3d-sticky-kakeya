import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightAggregateMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalAnalyticSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63CrossDegreeAbsorption

/-!
# Family-independent scalar envelope for joint-height block costs

The source-volume popularity bin count is logarithmic, while the number of
selected graph-height layers in one side-`sqrt rho` slab is
`O(rho^{-1/2})`.  Their product is the exact runtime block cost consumed by
the aggregate density absorption.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2Node05V4RichSourceVolumePopularHeightData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    (data :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex)

theorem bins_real_le_log
    (hgraphOne : 256 * rho ≤ 1) :
    (data.popular.bins : ℝ) ≤
      23 * (Real.log (1 / (256 * rho)) + 1) := by
  have hgraph : 0 < 256 * rho := data.popular.graphScale_pos
  have hheightCard :
      (wz1Lemma23BoundedHeightIndices (256 * rho) hgraph).card ≤
        (wz1Lemma23BoundedCells (256 * rho) hgraph).card :=
    Finset.card_image_le
  have hheightNonempty :
      (wz1Lemma23BoundedHeightIndices (256 * rho) hgraph).Nonempty :=
    data.popular.heightIndices_nonempty.mono data.popular.heightIndices_subset
  have hcellsNonempty :
      (wz1Lemma23BoundedCells (256 * rho) hgraph).Nonempty := by
    simpa [wz1Lemma23BoundedHeightIndices] using hheightNonempty
  have hbinsArg :
      2 * (wz1Lemma23BoundedHeightIndices (256 * rho) hgraph).card ≤
        4 * (wz1Lemma23BoundedCells (256 * rho) hgraph).card := by
    have hcellsPos :
        0 < (wz1Lemma23BoundedCells (256 * rho) hgraph).card :=
      hcellsNonempty.card_pos
    omega
  have hbinsLog :
      Nat.log 2
          (2 * (wz1Lemma23BoundedHeightIndices
            (256 * rho) hgraph).card) ≤
        Nat.log 2
          (4 * (wz1Lemma23BoundedCells (256 * rho) hgraph).card) :=
    Nat.log_mono_right hbinsArg
  have hcellsNe :
      (wz1Lemma23BoundedCells (256 * rho) hgraph).card ≠ 0 :=
    hcellsNonempty.card_ne_zero
  have hfourEq :
      4 * (wz1Lemma23BoundedCells (256 * rho) hgraph).card =
        (wz1Lemma23BoundedCells (256 * rho) hgraph).card * 2 * 2 := by ring
  have hbinsNat : data.popular.bins ≤
      Nat.log 2 (wz1Lemma23BoundedCells (256 * rho) hgraph).card + 3 := by
    rw [data.popular.bins_eq]
    calc
      Nat.log 2
          (2 * (wz1Lemma23BoundedHeightIndices
            (256 * rho) hgraph).card) + 1 ≤
        Nat.log 2
          (4 * (wz1Lemma23BoundedCells (256 * rho) hgraph).card) + 1 := by
            omega
      _ = Nat.log 2
          (wz1Lemma23BoundedCells (256 * rho) hgraph).card + 3 := by
        rw [hfourEq]
        calc
          Nat.log 2
                ((wz1Lemma23BoundedCells
                  (256 * rho) hgraph).card * 2 * 2) + 1 =
              Nat.log 2
                ((wz1Lemma23BoundedCells
                  (256 * rho) hgraph).card * 2) + 1 + 1 := by
            rw [Nat.log_mul_base (by omega)
              (Nat.mul_ne_zero hcellsNe (by omega))]
          _ = Nat.log 2
                (wz1Lemma23BoundedCells
                  (256 * rho) hgraph).card + 1 + 1 + 1 := by
            rw [Nat.log_mul_base (by omega) hcellsNe]
          _ = _ := by omega
  let L := Real.log (1 / (256 * rho)) + 1
  have hlog := wz1Lemma23BoundedCells_log_bound hgraph hgraphOne
  have hLone : 1 ≤ L := by
    dsimp only [L]
    have hlogNonneg : 0 ≤ Real.log (1 / (256 * rho)) := by
      apply Real.log_nonneg
      exact one_le_one_div hgraph hgraphOne
    linarith
  have hnat : (data.popular.bins : ℝ) ≤
      (Nat.log 2 (wz1Lemma23BoundedCells
        (256 * rho) hgraph).card + 3 : ℕ) := by
    exact_mod_cast hbinsNat
  calc
    (data.popular.bins : ℝ) ≤
        (Nat.log 2 (wz1Lemma23BoundedCells
          (256 * rho) hgraph).card + 3 : ℕ) := hnat
    _ ≤ 20 * L + 2 := by
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      linarith [hlog]
    _ ≤ 23 * L := by nlinarith

end PureWZ2Node05V4RichSourceVolumePopularHeightData

/-- The common occupied-bin bound used by the integrated source-popular
construction.  It depends only on the current source and scale, not on a
heavy slab or on any subsequently selected height family. -/
noncomputable def pureWZ2Node05V4RichJointOccupiedBinBound
    (sigma inputLoss delta rho : ℝ) : ENNReal :=
  264 * Kakeya.realRpowENN delta (-inputLoss) *
    Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma)

/-- A family-independent upper bound for the dyadic height-volume bin count
inside every source-heavy slab. -/
noncomputable def pureWZ2Node05V4RichJointHeightBinBound
    (rho : ℝ) : ENNReal :=
  23 * ENNReal.ofReal (Real.log (1 / (256 * rho)) + 1)

/-- The positive common-bin mass threshold selected before any heavy-slab
source-popular witness.  The factor `160 = 2 * 2 * 2 * 10 * 2` pays the
common-bin discard, the two source-popularity halvings, the heavy-slab
average, and the final slice normalization. -/
noncomputable def pureWZ2Node05V4RichJointCommonBinThreshold
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale) : ENNReal :=
  volume pullback.shading.union /
    (160 *
      pureWZ2Node05V4RichJointOccupiedBinBound sigma inputLoss delta rho *
      pureWZ2Node05V4RichJointHeightBinBound rho)

namespace PureWZ2Node05V4RichTwoScaleCellPullbackData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)

theorem jointOccupiedBinBound_pos
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    0 < pureWZ2Node05V4RichJointOccupiedBinBound
      sigma inputLoss delta rho := by
  unfold pureWZ2Node05V4RichJointOccupiedBinBound Kakeya.realRpowENN
  exact ENNReal.mul_pos
    (ENNReal.mul_pos (by norm_num)
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)).ne').ne'
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos (one_div_pos.mpr (Real.sqrt_pos.mpr hrho)) _)).ne'

theorem jointOccupiedBinBound_ne_top :
    pureWZ2Node05V4RichJointOccupiedBinBound
      sigma inputLoss delta rho ≠ ⊤ := by
  unfold pureWZ2Node05V4RichJointOccupiedBinBound Kakeya.realRpowENN
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top

theorem jointHeightBinBound_pos
    (hrho : 0 < rho) (hgraphOne : 256 * rho ≤ 1) :
    0 < pureWZ2Node05V4RichJointHeightBinBound rho := by
  have hgraph : 0 < 256 * rho := by positivity
  have hlogNonneg : 0 ≤ Real.log (1 / (256 * rho)) := by
    apply Real.log_nonneg
    exact one_le_one_div hgraph hgraphOne
  unfold pureWZ2Node05V4RichJointHeightBinBound
  exact ENNReal.mul_pos (by norm_num)
    (ENNReal.ofReal_pos.mpr (by linarith)).ne'

theorem jointHeightBinBound_ne_top :
    pureWZ2Node05V4RichJointHeightBinBound rho ≠ ⊤ := by
  unfold pureWZ2Node05V4RichJointHeightBinBound
  exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top

theorem jointCommonBinThreshold_pos (_hgraphOne : 256 * rho ≤ 1) :
    0 < pureWZ2Node05V4RichJointCommonBinThreshold pullback := by
  have hdelta : 0 < delta := current.grain.extremal.delta_pos
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hselected : pullback.selectedCells.Nonempty := by
    rcases twoScale.second.terminal.packetCells_nonempty with ⟨edge, hedge⟩
    rw [twoScale.second.terminal.packetCells_eq] at hedge
    have hactive := (Finset.mem_product.mp (Finset.mem_filter.mp hedge).1).2
    rw [pullback.selectedCells_eq]
    exact ⟨edge.2, hactive⟩
  have hvolumePos : 0 < volume pullback.shading.union := by
    rw [pullback.volume_eq]
    exact ENNReal.mul_pos
      (by exact_mod_cast hselected.card_pos.ne')
      pullback.firstPostBalanced.cellMass_pos.ne'
  have hdenomTop :
      160 * pureWZ2Node05V4RichJointOccupiedBinBound
          sigma inputLoss delta rho *
        pureWZ2Node05V4RichJointHeightBinBound rho ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) jointOccupiedBinBound_ne_top)
      jointHeightBinBound_ne_top
  unfold pureWZ2Node05V4RichJointCommonBinThreshold
  exact ENNReal.div_pos hvolumePos.ne' hdenomTop

theorem jointCommonBinThreshold_ne_top (hgraphOne : 256 * rho ≤ 1) :
    pureWZ2Node05V4RichJointCommonBinThreshold pullback ≠ ⊤ := by
  have hdelta : 0 < delta := current.grain.extremal.delta_pos
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hvolumeTop : volume pullback.shading.union ≠ ⊤ := by
    rw [pullback.volume_eq]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      pullback.firstPostBalanced.cellMass_ne_top
  have hdenomPos :
      0 < 160 * pureWZ2Node05V4RichJointOccupiedBinBound
          sigma inputLoss delta rho *
        pureWZ2Node05V4RichJointHeightBinBound rho :=
    ENNReal.mul_pos
      (ENNReal.mul_pos (by norm_num)
        (jointOccupiedBinBound_pos hdelta hrho).ne').ne'
      (jointHeightBinBound_pos hrho hgraphOne).ne'
  unfold pureWZ2Node05V4RichJointCommonBinThreshold
  exact ENNReal.div_ne_top hvolumeTop hdenomPos.ne'

/-- The common threshold is valid for every source-volume-popular witness in
every heavy slab.  This is the family-independent gate missing from the
integrated `Z_S` route: all dependence is on the prior two-call pullback. -/
theorem jointCommonBinThreshold_budget
    (hgraphOne : 256 * rho ≤ 1)
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback})
    (volumePopular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex) :
    2 * pureWZ2Node05V4RichJointOccupiedBinBound
          sigma inputLoss delta rho *
        pureWZ2Node05V4RichJointCommonBinThreshold pullback ≤
      pureWZ2SourceCommonBinPopularThreshold
        volumePopular.jointSourceSet (Real.sqrt rho) := by
  let B₀ := pureWZ2Node05V4RichJointOccupiedBinBound
    sigma inputLoss delta rho
  let heightCost := pureWZ2Node05V4RichJointHeightBinBound rho
  let threshold := pureWZ2Node05V4RichJointCommonBinThreshold pullback
  let root := ENNReal.ofReal (Real.sqrt rho)
  let sourceVolume := volume pullback.shading.union
  let jointVolume := volume volumePopular.jointSourceSet
  let denom := 160 * B₀ * heightCost
  have hdelta : 0 < delta := current.grain.extremal.delta_pos
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hrootPos : 0 < root := by
    dsimp only [root]
    apply ENNReal.ofReal_pos.mpr
    exact Real.sqrt_pos.mpr hrho
  have hrootTop : root ≠ ⊤ := ENNReal.ofReal_ne_top
  have hB₀Pos : 0 < B₀ := by
    exact jointOccupiedBinBound_pos hdelta hrho
  have hB₀Top : B₀ ≠ ⊤ := by
    exact jointOccupiedBinBound_ne_top
  have hheightPos : 0 < heightCost := by
    exact jointHeightBinBound_pos hrho hgraphOne
  have hheightTop : heightCost ≠ ⊤ := by
    exact jointHeightBinBound_ne_top
  have hdenomPos : 0 < denom := by
    dsimp only [denom]
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (by norm_num) hB₀Pos.ne').ne' hheightPos.ne'
  have hdenomTop : denom ≠ ⊤ := by
    dsimp only [denom]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hB₀Top) hheightTop
  have hsourceTop : sourceVolume ≠ ⊤ := by
    dsimp only [sourceVolume]
    rw [pullback.volume_eq]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      pullback.firstPostBalanced.cellMass_ne_top
  have hthresholdEq : threshold = sourceVolume / denom := rfl
  have hcancel : threshold * denom = sourceVolume := by
    rw [hthresholdEq]
    exact ENNReal.div_mul_cancel hdenomPos.ne' hdenomTop
  have hbins : (volumePopular.popular.bins : ENNReal) ≤ heightCost := by
    have hreal := volumePopular.bins_real_le_log hgraphOne
    have hofReal := ENNReal.ofReal_mono hreal
    dsimp only [heightCost, pureWZ2Node05V4RichJointHeightBinBound]
    calc
      (volumePopular.popular.bins : ENNReal) =
          ENNReal.ofReal (volumePopular.popular.bins : ℝ) := by simp
      _ ≤ ENNReal.ofReal
          (23 * (Real.log (1 / (256 * rho)) + 1)) := hofReal
      _ = 23 * ENNReal.ofReal
          (Real.log (1 / (256 * rho)) + 1) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
  have hheavy :
      (10 : ENNReal)⁻¹ * sourceVolume * root ≤
        volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) := by
    simpa only [sourceVolume, root, pureWZ2Node05V4RichHeavySlabThreshold]
      using (Finset.mem_filter.mp heightIndex.2).2
  have hretained :
      volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) / 2 / 2 ≤
        (volumePopular.popular.bins : ENNReal) * jointVolume := by
    calc
      volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) / 2 / 2 ≤
          volume volumePopular.continuous.popularRegion / 2 := by
        gcongr
        exact volumePopular.continuous.popularRegion_half_volume
      _ = volume volumePopular.sourcePopularShading.union / 2 := by
        rw [volumePopular.sourcePopularShading_union]
      _ ≤ (volumePopular.popular.bins : ENNReal) *
          volume volumePopular.popular.shading.union :=
        volumePopular.popular.retained_volume
      _ = (volumePopular.popular.bins : ENNReal) * jointVolume := by
        rfl
  have hsourceToJoint :
      sourceVolume * root / 40 ≤ heightCost * jointVolume := by
    have hforty : (40 : ENNReal)⁻¹ =
        (10 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ := by
      rw [show (40 : ENNReal) = 10 * 2 * 2 by norm_num]
      rw [ENNReal.mul_inv (by norm_num) (by norm_num)]
      rw [ENNReal.mul_inv (by norm_num) (by norm_num)]
    calc
      sourceVolume * root / 40 =
          ((10 : ENNReal)⁻¹ * sourceVolume * root) / 2 / 2 := by
        rw [div_eq_mul_inv, hforty]
        simp only [div_eq_mul_inv]
        ring
      _ ≤ volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) / 2 / 2 := by
        gcongr
      _ ≤ (volumePopular.popular.bins : ENNReal) * jointVolume := hretained
      _ ≤ heightCost * jointVolume := by gcongr
  rw [pureWZ2SourceCommonBinPopularThreshold_eq]
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.mul_pos (by norm_num) hrootPos.ne').ne')
    (Or.inl (ENNReal.mul_ne_top (by norm_num) hrootTop))).2
  apply (ENNReal.mul_le_mul_iff_left hheightPos.ne' hheightTop).mp
  have hforty : (40 : ENNReal)⁻¹ =
      (10 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ := by
    rw [show (40 : ENNReal) = 10 * 2 * 2 by norm_num]
    rw [ENNReal.mul_inv (by norm_num) (by norm_num)]
    rw [ENNReal.mul_inv (by norm_num) (by norm_num)]
  have hcoef : (160 : ENNReal) * (40 : ENNReal)⁻¹ = 4 := by
    rw [show (160 : ENNReal) = 4 * 40 by norm_num, mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
  calc
    (2 * B₀ * threshold * (2 * root)) * heightCost =
        sourceVolume * root / 40 := by
      rw [div_eq_mul_inv]
      calc
        _ = B₀ * threshold * root * heightCost * 4 := by ring
        _ = B₀ * threshold * root * heightCost *
            (160 * (40 : ENNReal)⁻¹) := by rw [hcoef]
        _ = threshold * denom * (root * (40 : ENNReal)⁻¹) := by
          dsimp only [denom]
          ring
        _ = sourceVolume * (root * (40 : ENNReal)⁻¹) := by rw [hcancel]
        _ = sourceVolume * root * (40 : ENNReal)⁻¹ := by ring
    _ ≤ heightCost * jointVolume := hsourceToJoint
    _ = jointVolume * heightCost := by ring

end PureWZ2Node05V4RichTwoScaleCellPullbackData

/-- Uniform runtime envelope for the per-block popularity cost. -/
noncomputable def pureWZ2Node05V4RichJointBlockCost (rho : ℝ) : ENNReal :=
  2208 * ENNReal.ofReal (Real.log (1 / (256 * rho)) + 1) *
    Kakeya.realRpowENN rho (-(1 / 2 : ℝ))

noncomputable def pureWZ2Node05V4RichJointGain
    (rho finalLoss : ℝ) : ENNReal :=
  Kakeya.realRpowENN
    (wz1Lemma23Theorem22Scale (256 * rho)) (finalLoss - 1)

theorem pureWZ2Node05V4RichJointBlockCost_pos
    {rho : ℝ} (hrho : 0 < rho) (hgraphOne : 256 * rho ≤ 1) :
    0 < pureWZ2Node05V4RichJointBlockCost rho := by
  have hgraph : 0 < 256 * rho := by positivity
  have hlogNonneg : 0 ≤ Real.log (1 / (256 * rho)) := by
    apply Real.log_nonneg
    exact one_le_one_div hgraph hgraphOne
  unfold pureWZ2Node05V4RichJointBlockCost
  exact ENNReal.mul_pos
    (ENNReal.mul_pos (by norm_num)
      (ENNReal.ofReal_pos.mpr (by linarith)).ne').ne'
    (by
      simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hrho])

theorem pureWZ2Node05V4RichJointBlockCost_ne_top (rho : ℝ) :
    pureWZ2Node05V4RichJointBlockCost rho ≠ ⊤ := by
  unfold pureWZ2Node05V4RichJointBlockCost
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
    (by simp [Kakeya.realRpowENN])

theorem PureWZ2Node05V4RichJointTheorem52Data.gain_eq
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta finalLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {B₀ threshold : ENNReal}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {prepared : PureWZ2Node05V4RichJointPreparedData
      (eta := eta) pullback heightIndex B₀ threshold hbridge}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (data : PureWZ2Node05V4RichJointTheorem52Data prepared projection) :
    pureWZ2Node05V4RichJointGain rho finalLoss =
      Kakeya.realRpowENN data.output.ready.ready.deltaGraph
        (finalLoss - 1) := by
  unfold pureWZ2Node05V4RichJointGain
  rw [data.output.ready.ready.deltaGraph_eq, prepared.graphScale_eq]

theorem PureWZ2Node05V4RichSourceVolumePopularHeightData.blockCost_le
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    (data :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex)
    (hgraphOne : 256 * rho ≤ 1) :
    24 * (data.popular.bins : ENNReal) *
        (data.popular.heightIndices.card : ENNReal) ≤
      pureWZ2Node05V4RichJointBlockCost rho := by
  let L := Real.log (1 / (256 * rho)) + 1
  have hLNonneg : 0 ≤ L := by
    dsimp only [L]
    have hgraph : 0 < 256 * rho := data.popular.graphScale_pos
    have hlogNonneg : 0 ≤ Real.log (1 / (256 * rho)) := by
      apply Real.log_nonneg
      exact one_le_one_div hgraph hgraphOne
    linarith
  have hbinsReal := data.bins_real_le_log hgraphOne
  have hbins :
      (data.popular.bins : ENNReal) ≤
        23 * ENNReal.ofReal L := by
    calc
      (data.popular.bins : ENNReal) =
          ENNReal.ofReal (data.popular.bins : ℝ) := by simp
      _ ≤ ENNReal.ofReal (23 * L) := by
        apply ENNReal.ofReal_mono
        simpa [L] using hbinsReal
      _ = 23 * ENNReal.ofReal L := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
  have hheight := data.heightIndices_card_le_four_sqrt_inv
  unfold pureWZ2Node05V4RichJointBlockCost
  calc
    24 * (data.popular.bins : ENNReal) *
          (data.popular.heightIndices.card : ENNReal) ≤
        24 * (23 * ENNReal.ofReal L) *
          (4 * Kakeya.realRpowENN rho (-(1 / 2 : ℝ))) := by
      gcongr
    _ = 2208 * ENNReal.ofReal L *
        Kakeya.realRpowENN rho (-(1 / 2 : ℝ)) := by ring

theorem PureWZ2Node05V4RichSourceVolumePopularHeightData.bins_le_heightBinBound
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    (data :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex)
    (hgraphOne : 256 * rho ≤ 1) :
    (data.popular.bins : ENNReal) ≤
      pureWZ2Node05V4RichJointHeightBinBound rho := by
  have hreal := data.bins_real_le_log hgraphOne
  unfold pureWZ2Node05V4RichJointHeightBinBound
  calc
    (data.popular.bins : ENNReal) =
        ENNReal.ofReal (data.popular.bins : ℝ) := by simp
    _ ≤ ENNReal.ofReal
        (23 * (Real.log (1 / (256 * rho)) + 1)) :=
      ENNReal.ofReal_mono hreal
    _ = 23 * ENNReal.ofReal
        (Real.log (1 / (256 * rho)) + 1) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num

theorem pureWZ2Node05V4RichJointBlockCost_le_six_window
    {rho : ℝ} (hrho : 0 < rho) :
    pureWZ2Node05V4RichJointBlockCost rho ≤
      6 * pureWZ2OrdinaryPaperOrderWindowHeightCost rho := by
  have hlog :
      Real.log (1 / (256 * rho)) + 1 ≤ Real.log rho⁻¹ + 1 := by
    have hleft : 0 < 1 / (256 * rho) := by positivity
    have hquotient : 1 / (256 * rho) ≤ rho⁻¹ := by
      rw [one_div]
      exact inv_anti₀ hrho (by nlinarith)
    linarith [Real.log_le_log hleft hquotient]
  have hofReal := ENNReal.ofReal_mono hlog
  unfold pureWZ2Node05V4RichJointBlockCost
    pureWZ2OrdinaryPaperOrderWindowHeightCost
  calc
    2208 * ENNReal.ofReal (Real.log (1 / (256 * rho)) + 1) *
          Kakeya.realRpowENN rho (-(1 / 2 : ℝ)) ≤
        2208 * ENNReal.ofReal (Real.log rho⁻¹ + 1) *
          Kakeya.realRpowENN rho (-(1 / 2 : ℝ)) := by
      gcongr
    _ = 6 * (368 * ENNReal.ofReal (Real.log rho⁻¹ + 1) *
          Kakeya.realRpowENN rho (-(1 / 2 : ℝ))) := by ring

/-- The uniform block cost is paid by the genuine rich-height gain after one
preselected positive `rho^finalLoss` factor. -/
theorem pureWZ2Node05V4RichJointBlockCost_richGain_schedule
    {finalLoss : ℝ} (hfinal : 0 < finalLoss) (hfinalOne : finalLoss ≤ 1) :
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ rho₀ →
        pureWZ2Node05V4RichJointBlockCost rho *
            Kakeya.realRpowENN rho finalLoss ≤
          pureWZ2Node05V4RichJointGain rho finalLoss := by
  rcases pureWZ2OrdinaryPaperOrderWindowHeightCost_richFloor_schedule
      hfinal hfinalOne with
    ⟨rho₀, hrho₀, hrho₀One, habsorb⟩
  refine ⟨rho₀, hrho₀, hrho₀One, ?_⟩
  intro rho hrho hrhoSmall
  calc
    pureWZ2Node05V4RichJointBlockCost rho *
          Kakeya.realRpowENN rho finalLoss ≤
        (6 * pureWZ2OrdinaryPaperOrderWindowHeightCost rho) *
          Kakeya.realRpowENN rho finalLoss := by
      gcongr
      exact pureWZ2Node05V4RichJointBlockCost_le_six_window hrho
    _ ≤ (512 * pureWZ2OrdinaryPaperOrderWindowHeightCost rho) *
          Kakeya.realRpowENN rho finalLoss := by
      gcongr
      norm_num
    _ ≤ pureWZ2SourceHorizontalRichFloor rho finalLoss :=
      habsorb rho hrho hrhoSmall
    _ = pureWZ2Node05V4RichJointGain rho finalLoss := rfl

/-- Algebraic core of the P0 aggregate-density absorption.  Each premise is
family-independent or supplied by a pre-runtime threshold; the conclusion is
exactly the `habsorb` consumed by the assembled P3 one-scale output. -/
theorem pureWZ2Node05V4RichJoint_aggregateDensity_absorb_of_powers
    {delta rho inputLoss sourceLossCeiling densityLoss finalLoss
      scaleLoss regularityLoss refinementLoss : ℝ}
    {regularity : ENNReal}
    (hdelta : 0 < delta)
    (hregularity :
      128 * regularity ^ 4 ≤
        Kakeya.realRpowENN delta (-regularityLoss))
    (hgap :
      Kakeya.realRpowENN delta (densityLoss - regularityLoss) ≤
        Kakeya.realRpowENN delta
          (sourceLossCeiling + 2 * refinementLoss +
            (1 - scaleLoss) * finalLoss))
    (hsource :
      Kakeya.realRpowENN delta sourceLossCeiling ≤
        Kakeya.realRpowENN delta inputLoss)
    (hrefinementDelta :
      Kakeya.realRpowENN delta refinementLoss ≤
        wz2PaperPureRefinementFraction delta 61)
    (hrefinementRho :
      Kakeya.realRpowENN delta refinementLoss ≤
        wz2PaperPureRefinementFraction rho 61)
    (hscale :
      Kakeya.realRpowENN delta ((1 - scaleLoss) * finalLoss) ≤
        Kakeya.realRpowENN rho finalLoss)
    (hblockGain :
      pureWZ2Node05V4RichJointBlockCost rho *
          Kakeya.realRpowENN rho finalLoss ≤
        pureWZ2Node05V4RichJointGain rho finalLoss) :
    (128 * regularity ^ 4 *
        pureWZ2Node05V4RichJointBlockCost rho) *
          Kakeya.realRpowENN delta densityLoss ≤
      (wz2PaperPureRefinementFraction delta 61 *
        wz2PaperPureRefinementFraction rho 61 *
        Kakeya.realRpowENN delta inputLoss) *
          pureWZ2Node05V4RichJointGain rho finalLoss := by
  have hregularityDensity :
      128 * regularity ^ 4 *
          Kakeya.realRpowENN delta densityLoss ≤
        Kakeya.realRpowENN delta (densityLoss - regularityLoss) := by
    calc
      128 * regularity ^ 4 *
            Kakeya.realRpowENN delta densityLoss ≤
          Kakeya.realRpowENN delta (-regularityLoss) *
            Kakeya.realRpowENN delta densityLoss := by
        gcongr
      _ = Kakeya.realRpowENN delta
          (densityLoss - regularityLoss) := by
        rw [← realRpowENN_add hdelta]
        congr 1
        ring
  have htargetPower :
      Kakeya.realRpowENN delta
          (sourceLossCeiling + 2 * refinementLoss +
            (1 - scaleLoss) * finalLoss) ≤
        (wz2PaperPureRefinementFraction delta 61 *
          wz2PaperPureRefinementFraction rho 61 *
          Kakeya.realRpowENN delta inputLoss) *
            Kakeya.realRpowENN rho finalLoss := by
    rw [show sourceLossCeiling + 2 * refinementLoss +
        (1 - scaleLoss) * finalLoss =
      sourceLossCeiling + refinementLoss + refinementLoss +
        ((1 - scaleLoss) * finalLoss) by ring]
    rw [realRpowENN_add hdelta, realRpowENN_add hdelta,
      realRpowENN_add hdelta]
    calc
      Kakeya.realRpowENN delta sourceLossCeiling *
            Kakeya.realRpowENN delta refinementLoss *
            Kakeya.realRpowENN delta refinementLoss *
            Kakeya.realRpowENN delta ((1 - scaleLoss) * finalLoss) ≤
          Kakeya.realRpowENN delta inputLoss *
            wz2PaperPureRefinementFraction delta 61 *
            wz2PaperPureRefinementFraction rho 61 *
            Kakeya.realRpowENN rho finalLoss := by
        gcongr
      _ = (wz2PaperPureRefinementFraction delta 61 *
            wz2PaperPureRefinementFraction rho 61 *
            Kakeya.realRpowENN delta inputLoss) *
          Kakeya.realRpowENN rho finalLoss := by ring
  calc
    (128 * regularity ^ 4 *
          pureWZ2Node05V4RichJointBlockCost rho) *
        Kakeya.realRpowENN delta densityLoss =
      (128 * regularity ^ 4 *
        Kakeya.realRpowENN delta densityLoss) *
          pureWZ2Node05V4RichJointBlockCost rho := by ring
    _ ≤ Kakeya.realRpowENN delta (densityLoss - regularityLoss) *
          pureWZ2Node05V4RichJointBlockCost rho := by
      gcongr
    _ ≤ Kakeya.realRpowENN delta
          (sourceLossCeiling + 2 * refinementLoss +
            (1 - scaleLoss) * finalLoss) *
          pureWZ2Node05V4RichJointBlockCost rho := by
      gcongr
    _ ≤ ((wz2PaperPureRefinementFraction delta 61 *
            wz2PaperPureRefinementFraction rho 61 *
            Kakeya.realRpowENN delta inputLoss) *
          Kakeya.realRpowENN rho finalLoss) *
          pureWZ2Node05V4RichJointBlockCost rho := by
      gcongr
    _ = (wz2PaperPureRefinementFraction delta 61 *
          wz2PaperPureRefinementFraction rho 61 *
          Kakeya.realRpowENN delta inputLoss) *
        (pureWZ2Node05V4RichJointBlockCost rho *
          Kakeya.realRpowENN rho finalLoss) := by ring
    _ ≤ (wz2PaperPureRefinementFraction delta 61 *
          wz2PaperPureRefinementFraction rho 61 *
          Kakeya.realRpowENN delta inputLoss) *
        pureWZ2Node05V4RichJointGain rho finalLoss := by
      gcongr

structure PureWZ2Node05V4RichJointDensityThreshold
    (sourceLossCeiling densityLoss finalLoss scaleLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  rho₀ : ℝ
  rho₀_pos : 0 < rho₀
  rho₀_le_one : rho₀ ≤ 1
  absorb :
    ∀ {inputLoss delta rho : ℝ} {regularity : ℕ},
      inputLoss ≤ sourceLossCeiling →
      0 < delta → delta ≤ delta₀ →
      0 < rho → rho ≤ rho₀ →
      delta ≤ rho →
      Real.rpow delta (1 - scaleLoss) ≤ rho →
      (regularity : ENNReal) ≤
        Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 →
      (128 * (regularity : ENNReal) ^ 4 *
          pureWZ2Node05V4RichJointBlockCost rho) *
          Kakeya.realRpowENN delta densityLoss ≤
        (wz2PaperPureRefinementFraction delta 61 *
          wz2PaperPureRefinementFraction rho 61 *
          Kakeya.realRpowENN delta inputLoss) *
          pureWZ2Node05V4RichJointGain rho finalLoss

/-- Choose the one common cutoff which discharges the complete aggregate
`habsorb` before any runtime family or scale is known. -/
theorem pureWZ2Node05V4RichJoint_density_threshold
    {sourceLossCeiling densityLoss finalLoss scaleLoss : ℝ}
    (hfinal : 0 < finalLoss)
    (hfinalOne : finalLoss ≤ 1)
    (hgap :
      sourceLossCeiling + (1 - scaleLoss) * finalLoss < densityLoss) :
    Nonempty (PureWZ2Node05V4RichJointDensityThreshold
      sourceLossCeiling densityLoss finalLoss scaleLoss) := by
  let gap :=
    densityLoss -
      (sourceLossCeiling + (1 - scaleLoss) * finalLoss)
  have hgapPos : 0 < gap := by
    dsimp only [gap]
    linarith
  let refinementLoss := gap / 8
  let regularityLoss := gap / 4
  have hrefinementLoss : 0 < refinementLoss := by
    dsimp only [refinementLoss]
    positivity
  have hregularityLoss : 0 < regularityLoss := by
    dsimp only [regularityLoss]
    positivity
  have hexponentGap :
      sourceLossCeiling + 2 * refinementLoss +
          (1 - scaleLoss) * finalLoss ≤
        densityLoss - regularityLoss := by
    dsimp only [refinementLoss, regularityLoss, gap]
    linarith
  rcases pureWZ2Node05V4RichJointBlockCost_richGain_schedule
      hfinal hfinalOne with
    ⟨blockRho₀, hblockRho₀, hblockRho₀One, hblock⟩
  rcases pureWZ2_refinementFraction_power_schedule
      61 hrefinementLoss with
    ⟨refinementRho₀, hrefinementRho₀, hrefinementRho₀One, hrefinement⟩
  let regularityCoefficient : ENNReal := 128 * 2 ^ (40 : ℕ)
  have hregularityCoefficientTop : regularityCoefficient ≠ ⊤ := by
    dsimp only [regularityCoefficient]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top (by norm_num))
  rcases exists_delta_log_absorbed_ennreal
      regularityCoefficient hregularityCoefficientTop
      hregularityLoss (show 0 < (40 : ℕ) by norm_num) with
    ⟨regularityDelta₀, hregularityDelta₀, hregularityDelta₀One,
      hregularityAbsorb⟩
  let delta₀ := min regularityDelta₀ refinementRho₀
  let rho₀ := min blockRho₀ refinementRho₀
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min hregularityDelta₀ hrefinementRho₀
    delta₀_le_one := (min_le_left _ _).trans hregularityDelta₀One
    rho₀ := rho₀
    rho₀_pos := lt_min hblockRho₀ hrefinementRho₀
    rho₀_le_one := (min_le_left _ _).trans hblockRho₀One
    absorb := ?_
  }⟩
  intro inputLoss delta rho regularity hinput hdelta hdeltaSmall
    hrho hrhoSmall hdeltaRho hscaleLower hregularityBound
  have hdeltaOne : delta ≤ 1 :=
    hdeltaSmall.trans ((min_le_left _ _).trans hregularityDelta₀One)
  have hrhoOne : rho ≤ 1 :=
    hrhoSmall.trans ((min_le_left _ _).trans hblockRho₀One)
  have hdeltaRegularity : delta ≤ regularityDelta₀ :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaRefinement : delta ≤ refinementRho₀ :=
    hdeltaSmall.trans (min_le_right _ _)
  have hrhoBlock : rho ≤ blockRho₀ :=
    hrhoSmall.trans (min_le_left _ _)
  have hrhoRefinement : rho ≤ refinementRho₀ :=
    hrhoSmall.trans (min_le_right _ _)
  have hlogarithmic :
      Prop62PaperAudit.V4.logarithmicLoss delta ≤
        2 * ENNReal.ofReal (1 + Real.log delta⁻¹) := by
    simpa only [Prop62PaperAudit.V4.logarithmicLoss,
      show ENNReal.ofReal
      (2 * (1 + Real.log delta⁻¹)) =
        2 * ENNReal.ofReal (1 + Real.log delta⁻¹) by
          rw [ENNReal.ofReal_mul (by norm_num)]
          norm_num] using
      PureWZ2.proposition63_logarithmicLoss_le_two_logEnvelope
        hdelta hdeltaOne
  have hregularityPower :
      128 * (regularity : ENNReal) ^ 4 ≤
        Kakeya.realRpowENN delta (-regularityLoss) := by
    have hpow :
        (regularity : ENNReal) ^ 4 ≤
          (2 * ENNReal.ofReal (1 + Real.log delta⁻¹)) ^ 40 := by
      calc
        (regularity : ENNReal) ^ 4 ≤
            (Prop62PaperAudit.V4.logarithmicLoss delta ^ 10) ^ 4 := by
          gcongr
        _ = Prop62PaperAudit.V4.logarithmicLoss delta ^ 40 := by
          rw [← pow_mul]
        _ ≤ (2 * ENNReal.ofReal
              (1 + Real.log delta⁻¹)) ^ 40 := by
          gcongr
    calc
      128 * (regularity : ENNReal) ^ 4 ≤
          128 * (2 * ENNReal.ofReal
            (1 + Real.log delta⁻¹)) ^ 40 := by gcongr
      _ = regularityCoefficient *
          ENNReal.ofReal (1 + Real.log delta⁻¹) ^ 40 := by
        dsimp only [regularityCoefficient]
        rw [mul_pow]
        ring
      _ ≤ Kakeya.realRpowENN delta (-regularityLoss) :=
        hregularityAbsorb delta hdelta hdeltaRegularity
  have hgapPower :
      Kakeya.realRpowENN delta (densityLoss - regularityLoss) ≤
        Kakeya.realRpowENN delta
          (sourceLossCeiling + 2 * refinementLoss +
            (1 - scaleLoss) * finalLoss) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge
      hdelta hdeltaOne hexponentGap
  have hsourcePower :
      Kakeya.realRpowENN delta sourceLossCeiling ≤
        Kakeya.realRpowENN delta inputLoss := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne hinput
  have hrefinementDelta :
      Kakeya.realRpowENN delta refinementLoss ≤
        wz2PaperPureRefinementFraction delta 61 :=
    hrefinement delta hdelta hdeltaRefinement
  have hrefinementRho :
      Kakeya.realRpowENN delta refinementLoss ≤
        wz2PaperPureRefinementFraction rho 61 := by
    calc
      Kakeya.realRpowENN delta refinementLoss ≤
          Kakeya.realRpowENN rho refinementLoss := by
        apply ENNReal.ofReal_mono
        exact Real.rpow_le_rpow hdelta.le hdeltaRho hrefinementLoss.le
      _ ≤ wz2PaperPureRefinementFraction rho 61 :=
        hrefinement rho hrho hrhoRefinement
  have hscalePower :
      Kakeya.realRpowENN delta ((1 - scaleLoss) * finalLoss) ≤
        Kakeya.realRpowENN rho finalLoss := by
    apply ENNReal.ofReal_mono
    calc
      Real.rpow delta ((1 - scaleLoss) * finalLoss) =
          Real.rpow (Real.rpow delta (1 - scaleLoss)) finalLoss := by
        exact Real.rpow_mul hdelta.le (1 - scaleLoss) finalLoss
      _ ≤ Real.rpow rho finalLoss :=
        Real.rpow_le_rpow (Real.rpow_nonneg hdelta.le _) hscaleLower hfinal.le
  exact pureWZ2Node05V4RichJoint_aggregateDensity_absorb_of_powers
    hdelta hregularityPower hgapPower hsourcePower hrefinementDelta
    hrefinementRho hscalePower (hblock rho hrho hrhoBlock)

structure PureWZ2Node05V4RichJointLossBudget
    {sigma floorLoss structuralBudget : ℝ}
    (floorSchedule : PureWZ2ReentryTraceFloorSchedule
      sigma floorLoss structuralBudget)
    (scaleLoss : ℝ) where
  sourceLossCeiling : ℝ := floorSchedule.densityLoss / 8
  sourceLossCeiling_eq :
    sourceLossCeiling = floorSchedule.densityLoss / 8
  sourceLossCeiling_pos : 0 < sourceLossCeiling
  finalLoss : ℝ := floorSchedule.densityLoss / 8
  finalLoss_eq : finalLoss = floorSchedule.densityLoss / 8
  finalLoss_pos : 0 < finalLoss
  finalLoss_le_one : finalLoss ≤ 1
  density_gap :
    sourceLossCeiling + (1 - scaleLoss) * finalLoss <
      floorSchedule.densityLoss
  densityThreshold : PureWZ2Node05V4RichJointDensityThreshold
    sourceLossCeiling floorSchedule.densityLoss finalLoss scaleLoss

/-- Concrete loss split showing that the complete aggregate-density gap is
compatible with the existing re-entry floor budget. -/
theorem PureWZ2ReentryTraceFloorSchedule.jointLossBudget
    {sigma floorLoss structuralBudget scaleLoss : ℝ}
    (floorSchedule : PureWZ2ReentryTraceFloorSchedule
      sigma floorLoss structuralBudget)
    (hfloorOne : floorLoss ≤ 1)
    (hscaleNonneg : 0 ≤ scaleLoss) :
    Nonempty (PureWZ2Node05V4RichJointLossBudget
      floorSchedule scaleLoss) := by
  let sourceLossCeiling := floorSchedule.densityLoss / 8
  let finalLoss := floorSchedule.densityLoss / 8
  have hsourcePos : 0 < sourceLossCeiling := by
    dsimp only [sourceLossCeiling]
    exact div_pos floorSchedule.densityLoss_pos (by norm_num)
  have hfinalPos : 0 < finalLoss := by
    dsimp only [finalLoss]
    exact div_pos floorSchedule.densityLoss_pos (by norm_num)
  have hfinalOne : finalLoss ≤ 1 := by
    dsimp only [finalLoss]
    have hdensityOne :
        floorSchedule.densityLoss ≤ 1 :=
      floorSchedule.densityLoss_le_floor.trans hfloorOne
    linarith
  have hgap :
      sourceLossCeiling + (1 - scaleLoss) * finalLoss <
        floorSchedule.densityLoss := by
    rw [show sourceLossCeiling = floorSchedule.densityLoss / 8 by rfl,
      show finalLoss = floorSchedule.densityLoss / 8 by rfl]
    have hdensityPos := floorSchedule.densityLoss_pos
    nlinarith
  rcases pureWZ2Node05V4RichJoint_density_threshold
      hfinalPos hfinalOne hgap with ⟨densityThreshold⟩
  exact ⟨{
    sourceLossCeiling := sourceLossCeiling
    sourceLossCeiling_eq := rfl
    sourceLossCeiling_pos := hsourcePos
    finalLoss := finalLoss
    finalLoss_eq := rfl
    finalLoss_pos := hfinalPos
    finalLoss_le_one := hfinalOne
    density_gap := hgap
    densityThreshold := densityThreshold
  }⟩

end Kakeya.Assouad

end
