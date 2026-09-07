import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TerminalMassRetention
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGridCubeVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperActiveCellLogBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CanonicalMassBudget
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Proposition 6.2: pre-balancing reference parent-degree floor

This module proves the finite counting inequality behind
`WZ2_prop62.tex`, equation `prop62-prebalance-packet-density`.

The input shading is still the shading on the complete metric family, before
packet-cell exactification and the final balancing sample.  Its aggregate
density, followed by the three paper-ordered weighted dyadic selections,
forces the common reference parent-degree scale `K` to be large.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62PacketCellInput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput cover shading)
    (multiplicity : input.FineMultiplicityClassData)
    (parentClass : input.ParentClassData multiplicity)
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        coarse ambientConstant scaleWindow}
    (treeCleanup :
      input.ParentTreeCleanupData
        multiplicity parentClass schedule)
    (exactification :
      input.PacketCellExactificationData
        multiplicity parentClass treeCleanup)
    (parentDegree :
      input.ReferenceParentDegreeData
        multiplicity parentClass treeCleanup exactification)

/-- The three weighted dyadic losses before the reference-parent tree core. -/
def prebalanceParentDegreeLoss : ENNReal :=
  (32 : ENNReal) *
    multiplicity.binCount *
    parentClass.weightBinCount *
    parentClass.fiberBinCount

/-- The finite dyadic loss before balancing when `muFine` is not cancelled. -/
def prebalancePacketDensityLoss : ENNReal :=
  (16 : ENNReal) *
    multiplicity.binCount *
    parentClass.weightBinCount *
    parentClass.fiberBinCount

def prebalanceLogCoefficient : ℝ :=
  max
    pureWZ2Prop62OrdinaryCardLogConstant
    (wz2PaperBoundaryLogCoefficient + 1)

def prebalanceTailCoefficient (depthBound : ℕ) : ℝ :=
  40 *
    (8 * (depthBound + 2) * 8 ^ 4) ^ 3 *
    prebalanceLogCoefficient ^ 13

theorem one_le_prebalanceLogCoefficient :
    (1 : ℝ) ≤ prebalanceLogCoefficient := by
  have boundaryOne :
      (1 : ℝ) ≤ wz2PaperBoundaryLogCoefficient + 1 := by
    have boundaryNonnegative :
        (0 : ℝ) ≤ wz2PaperBoundaryLogCoefficient := by
      unfold wz2PaperBoundaryLogCoefficient
      exact (by positivity : (0 : ℝ) ≤
        max (5 * Real.log 163 / Real.log 2 + 2) (5 / Real.log 2))
    linarith
  exact boundaryOne.trans (le_max_right _ _)

theorem prebalanceTailCoefficient_pos
    (depthBound : ℕ) :
    0 < prebalanceTailCoefficient depthBound := by
  unfold prebalanceTailCoefficient
  have coefficientPositive :
      (0 : ℝ) < prebalanceLogCoefficient :=
    zero_lt_one.trans_le one_le_prebalanceLogCoefficient
  positivity

structure PrebalanceSmallData
    (delta : ℝ)
    (depthBound : ℕ)
    (densityExponent lossExponent : ℝ) : Prop where
  delta_lt_one : delta < 1
  loss_bound :
    (128 : ENNReal) *
        (ENNReal.ofReal
          (prebalanceLogCoefficient *
            (1 + Real.log delta⁻¹))) ^ 3 ≤
      Kakeya.realRpowENN delta (-lossExponent)
  tail_bound :
    prebalanceTailCoefficient depthBound *
        (1 + Real.log delta⁻¹) ^ 13 ≤
      Real.rpow delta
        (-((1 - (densityExponent + lossExponent)) / 2))

theorem exists_prebalanceSmallThreshold
    (depthBound : ℕ)
    (densityExponent lossExponent : ℝ)
    (lossExponentPos : 0 < lossExponent)
    (exponentGap : densityExponent + lossExponent < 1) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₀ →
          PrebalanceSmallData
            delta depthBound densityExponent lossExponent := by
  rcases
      exists_delta_C_pow_log_absorbed_ennreal
        128 (by norm_num)
        prebalanceLogCoefficient
        (zero_le_one.trans one_le_prebalanceLogCoefficient)
        lossExponentPos (n := 3) (by norm_num)
    with ⟨lossThreshold, lossThresholdPos, lossThresholdLeOne,
      lossBound⟩
  let gap : ℝ := 1 - (densityExponent + lossExponent)
  have gapHalfPos : 0 < gap / 2 := by
    dsimp only [gap]
    linarith
  rcases
      exists_delta_log_absorbed
        (prebalanceTailCoefficient depthBound)
        (prebalanceTailCoefficient_pos depthBound)
        gapHalfPos (n := 13) (by norm_num)
    with ⟨tailThreshold, tailThresholdPos, tailThresholdLeOne,
      tailBound⟩
  let delta₀ := min (min lossThreshold tailThreshold) (1 / 2 : ℝ)
  have delta₀Pos : 0 < delta₀ := by
    dsimp only [delta₀]
    exact lt_min (lt_min lossThresholdPos tailThresholdPos) (by norm_num)
  have delta₀LeOne : delta₀ ≤ 1 := by
    exact (min_le_right _ _).trans (by norm_num)
  refine ⟨delta₀, delta₀Pos, delta₀LeOne, ?_⟩
  intro delta deltaPos deltaLe
  have deltaLeLoss : delta ≤ lossThreshold :=
    deltaLe.trans <| (min_le_left _ _).trans (min_le_left _ _)
  have deltaLeTail : delta ≤ tailThreshold :=
    deltaLe.trans <| (min_le_left _ _).trans (min_le_right _ _)
  have deltaLtOne : delta < 1 :=
    deltaLe.trans_lt <| (min_le_right _ _).trans_lt (by norm_num)
  exact
    {
      delta_lt_one := deltaLtOne
      loss_bound := lossBound delta deltaPos deltaLeLoss
      tail_bound := by
        simpa only [prebalanceTailCoefficient, gap] using
          tailBound delta deltaPos deltaLeTail
    }

noncomputable def prebalanceSmallThreshold
    (depthBound : ℕ)
    (densityExponent lossExponent : ℝ)
    (lossExponentPos : 0 < lossExponent)
    (exponentGap : densityExponent + lossExponent < 1) : ℝ :=
  Classical.choose <|
    exists_prebalanceSmallThreshold
      depthBound densityExponent lossExponent
        lossExponentPos exponentGap

theorem prebalanceSmallThreshold_pos
    (depthBound : ℕ)
    (densityExponent lossExponent : ℝ)
    (lossExponentPos : 0 < lossExponent)
    (exponentGap : densityExponent + lossExponent < 1) :
    0 <
      prebalanceSmallThreshold
        depthBound densityExponent lossExponent
          lossExponentPos exponentGap :=
  (Classical.choose_spec <|
    exists_prebalanceSmallThreshold
      depthBound densityExponent lossExponent
        lossExponentPos exponentGap).1

theorem prebalanceSmallThreshold_le_one
    (depthBound : ℕ)
    (densityExponent lossExponent : ℝ)
    (lossExponentPos : 0 < lossExponent)
    (exponentGap : densityExponent + lossExponent < 1) :
    prebalanceSmallThreshold
        depthBound densityExponent lossExponent
          lossExponentPos exponentGap ≤
      1 :=
  (Classical.choose_spec <|
    exists_prebalanceSmallThreshold
      depthBound densityExponent lossExponent
        lossExponentPos exponentGap).2.1

theorem prebalanceSmallData_of_smallDelta
    (depthBound : ℕ)
    (densityExponent lossExponent : ℝ)
    (lossExponentPos : 0 < lossExponent)
    (exponentGap : densityExponent + lossExponent < 1)
    (deltaPos : 0 < delta)
    (deltaLe :
      delta ≤
        prebalanceSmallThreshold
          depthBound densityExponent lossExponent
            lossExponentPos exponentGap) :
    PrebalanceSmallData
      delta depthBound densityExponent lossExponent :=
  (Classical.choose_spec <|
    exists_prebalanceSmallThreshold
      depthBound densityExponent lossExponent
        lossExponentPos exponentGap).2.2
    delta deltaPos deltaLe

theorem natLog_product_add_one_le
    (first second : ℕ)
    (firstPos : 0 < first)
    (secondPos : 0 < second) :
    Nat.log 2 (first * second) + 1 ≤
      (Nat.log 2 (2 * first) + 1) +
        (Nat.log 2 (2 * second) + 1) := by
  have firstLt :
      2 * first <
        2 ^ (Nat.log 2 (2 * first) + 1) := by
    simpa using
      Nat.lt_pow_succ_log_self
        (by norm_num : 1 < 2) (2 * first)
  have secondLt :
      2 * second <
        2 ^ (Nat.log 2 (2 * second) + 1) := by
    simpa using
      Nat.lt_pow_succ_log_self
        (by norm_num : 1 < 2) (2 * second)
  have productLt :
      first * second <
        2 ^
          ((Nat.log 2 (2 * first) + 1) +
            (Nat.log 2 (2 * second) + 1)) := by
    calc
      first * second < (2 * first) * (2 * second) := by
        nlinarith
      _ <
          2 ^ (Nat.log 2 (2 * first) + 1) *
            2 ^ (Nat.log 2 (2 * second) + 1) := by
        nlinarith
      _ =
          2 ^
            ((Nat.log 2 (2 * first) + 1) +
              (Nat.log 2 (2 * second) + 1)) := by
        exact
          (pow_add 2
            (Nat.log 2 (2 * first) + 1)
            (Nat.log 2 (2 * second) + 1)).symm
  have logLt :
      Nat.log 2 (first * second) <
        (Nat.log 2 (2 * first) + 1) +
          (Nat.log 2 (2 * second) + 1) := by
    exact
      (Nat.log_lt_iff_lt_pow
        (by norm_num : 1 < 2)
        (Nat.mul_ne_zero firstPos.ne' secondPos.ne')).mpr productLt
  omega

theorem positiveMultiplicityCount_le_fine_mul_cells :
    (∑ pair ∈ input.positivePairs,
        input.packetCellMultiplicity pair) ≤
      fine.card * input.fineCells.card := by
  rw [input.positiveMultiplicityCount_eq_sourceCellCount]
  calc
    (∑ source : Fin fine.card,
        (input.sourceCellsForSource source).card) ≤
        ∑ _source : Fin fine.card, input.fineCells.card := by
      exact Finset.sum_le_sum fun source _ =>
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = fine.card * input.fineCells.card := by
      simp [Finset.sum_const, nsmul_eq_mul]

theorem multiplicityBinCount_le_fineCellLogs :
    multiplicity.binCount ≤
      (Nat.log 2 (2 * fine.card) + 1) +
        (Nat.log 2 (2 * input.fineCells.card) + 1) := by
  have fineCardPos : 0 < fine.card := by
    rcases input.fineCells_nonempty with ⟨cell, cellMem⟩
    have cellActive :
        cell ∈ wz1PaperActiveCells shading input.delta_pos := by
      rw [← input.fineCells_eq]
      exact cellMem
    rcases
        ((mem_wz1PaperActiveCells
          shading input.delta_pos cell).mp cellActive).2
      with ⟨point, ⟨source, _pointMem⟩, _pointCell⟩
    change 0 < (wz1PaperBodyFamily fine).card
    exact Nat.zero_lt_of_lt source.isLt
  have fineCellsPos : 0 < input.fineCells.card :=
    input.fineCells_nonempty.card_pos
  rw [multiplicity.binCount_eq]
  have logLe :
      Nat.log 2
          (∑ pair ∈ input.positivePairs,
            input.packetCellMultiplicity pair) ≤
        Nat.log 2 (fine.card * input.fineCells.card) :=
    Nat.log_mono_right
      (input.positiveMultiplicityCount_le_fine_mul_cells)
  exact
    (Nat.add_le_add_right logLe 1).trans <|
      natLog_product_add_one_le
        fine.card input.fineCells.card fineCardPos fineCellsPos

theorem weightBinCount_le_multiplicityBinCount :
    parentClass.weightBinCount ≤ multiplicity.binCount := by
  rw [parentClass.weightBinCount_eq, multiplicity.binCount_eq]
  apply Nat.add_le_add_right
  apply Nat.log_mono_right
  rw [input.sum_parentIncidenceWeight multiplicity]
  exact Finset.sum_le_sum_of_subset multiplicity.selectedPairs_subset

theorem fiberBinCount_le_fineLog :
    parentClass.fiberBinCount ≤
      Nat.log 2 (2 * fine.card) + 1 := by
  rw [parentClass.fiberBinCount_eq]
  apply Nat.add_le_add_right
  apply Nat.log_mono_right
  omega

theorem fineLog_le_prebalanceLog
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4) :
    (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
      prebalanceLogCoefficient *
        (1 + Real.log delta⁻¹) := by
  have rawCard :
      fine.card ≤
        (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by
    have raw :=
      wz2PaperOrdinary_local_six_grid_card_bound
        deltaPos (show (0 : ℝ) ≤ 5 by norm_num)
        fineDistinct Finset.univ (0 : Point3) <| by
          intro source _
          simpa [dist_zero_right] using
            PureWZ2Prop62AncestryMetricPreliminaryOutput.fine_midpoint_norm_le_five
              (fine := fine) fineBoundedBase source
    have firstArgument :
        5 / (delta / 64) = 320 / delta := by
      field_simp [deltaPos.ne']
      norm_num
    have secondArgument :
        1 / (delta / 64) ≤ 320 / delta := by
      have identity : 1 / (delta / 64) = 64 / delta := by
        field_simp [deltaPos.ne']
      rw [identity]
      exact div_le_div_of_nonneg_right (by norm_num) deltaPos.le
    have firstCeil :
        Nat.ceil (5 / (delta / 64)) =
          Nat.ceil (320 / delta) := by
      rw [firstArgument]
    have secondCeil :
        Nat.ceil (1 / (delta / 64)) ≤
          Nat.ceil (320 / delta) :=
      Nat.ceil_mono secondArgument
    simpa only [Finset.card_univ, Fintype.card_fin] using
      raw.trans <| by
        rw [firstCeil]
        calc
          (2 * Nat.ceil (320 / delta) + 1) ^ 3 *
              (2 * Nat.ceil (1 / (delta / 64)) + 1) ^ 3 ≤
            (2 * Nat.ceil (320 / delta) + 1) ^ 3 *
              (2 * Nat.ceil (320 / delta) + 1) ^ 3 := by
            gcongr
          _ = (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by ring
  have raw :=
    pureWZ2Prop62_ordinary_card_log_bound
      deltaPos deltaLeOne
      fineNonempty rawCard
  have logNonnegative : 0 ≤ Real.log delta⁻¹ := by
    apply Real.log_nonneg
    exact
      (one_le_inv₀ deltaPos).mpr
        deltaLeOne
  exact raw.trans <| by
    apply mul_le_mul_of_nonneg_right
    exact le_max_left _ _
    linarith

theorem fineCellLog_le_prebalanceLog :
    delta ≤ 1 →
    (Nat.log 2 (2 * input.fineCells.card) + 1 : ℝ) ≤
      prebalanceLogCoefficient *
        (1 + Real.log delta⁻¹) := by
  intro deltaLeOne
  rw [input.fineCells_eq]
  have raw :=
    wz2_paper_active_cell_log_bound
      input.delta_pos deltaLeOne shading
  have fineCellsPos :
      0 <
        (wz1PaperActiveCells shading input.delta_pos).card := by
    rw [← input.fineCells_eq]
    exact input.fineCells_nonempty.card_pos
  have doubledLog :
      Nat.log 2
          (2 * (wz1PaperActiveCells shading input.delta_pos).card) + 1 =
        Nat.log 2
            (wz1PaperActiveCells shading input.delta_pos).card + 2 := by
    rw [Nat.mul_comm, Nat.log_mul_base (by norm_num) fineCellsPos.ne']
  have logNonnegative : 0 ≤ Real.log delta⁻¹ := by
    apply Real.log_nonneg
    exact
      (one_le_inv₀ input.delta_pos).mpr
        deltaLeOne
  have doubledRaw :
      (Nat.log 2
          (2 * (wz1PaperActiveCells shading input.delta_pos).card) + 1 :
            ℝ) ≤
        (wz2PaperBoundaryLogCoefficient + 1) *
          (1 + Real.log delta⁻¹) := by
    have doubledLogReal :
        (Nat.log 2
            (2 * (wz1PaperActiveCells shading input.delta_pos).card) + 1 :
              ℝ) =
          (Nat.log 2
              (wz1PaperActiveCells shading input.delta_pos).card + 2 :
                ℝ) := by
      exact_mod_cast doubledLog
    rw [doubledLogReal]
    have raw' :
        (Nat.log 2
            (wz1PaperActiveCells shading input.delta_pos).card + 1 : ℝ) ≤
          wz2PaperBoundaryLogCoefficient *
            (1 + Real.log delta⁻¹) := by
      exact raw.trans <| by
        have leftLe :
            5 / Real.log 2 ≤ wz2PaperBoundaryLogCoefficient :=
          le_max_right _ _
        have rightLe :
            5 * Real.log 163 / Real.log 2 + 2 ≤
              wz2PaperBoundaryLogCoefficient :=
          le_max_left _ _
        rw [show Real.log (1 / delta) = Real.log delta⁻¹ by
          congr 1
          field_simp [input.delta_pos.ne']]
        nlinarith
    calc
      (Nat.log 2
          (wz1PaperActiveCells shading input.delta_pos).card + 2 : ℝ) =
          (Nat.log 2
            (wz1PaperActiveCells shading input.delta_pos).card + 1 : ℝ) +
            1 := by ring
      _ ≤
          wz2PaperBoundaryLogCoefficient *
              (1 + Real.log delta⁻¹) + 1 := by
        gcongr
      _ ≤
          (wz2PaperBoundaryLogCoefficient + 1) *
            (1 + Real.log delta⁻¹) := by
        nlinarith
  exact doubledRaw.trans <| by
    apply mul_le_mul_of_nonneg_right
    exact le_max_right _ _
    linarith

theorem coarse_card_le_fine_card
    (section6 : PureWZ2Section6Cover fine coarse) :
    coarse.card ≤ fine.card := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_surjective
      section6.toWZ1PaperTubeCover.parent
      section6.toWZ1PaperTubeCover.parent_surjective

theorem coarseLog_le_prebalanceLog
    (section6 : PureWZ2Section6Cover fine coarse)
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4) :
    (Nat.log 2 (2 * coarse.card) + 1 : ℝ) ≤
      prebalanceLogCoefficient *
        (1 + Real.log delta⁻¹) := by
  have doubledCard :
      2 * coarse.card ≤ 2 * fine.card := by
    exact Nat.mul_le_mul_left 2 (coarse_card_le_fine_card section6)
  have logLe :
      Nat.log 2 (2 * coarse.card) + 1 ≤
        Nat.log 2 (2 * fine.card) + 1 :=
    Nat.add_le_add_right (Nat.log_mono_right doubledCard) 1
  have logLeReal :
      (Nat.log 2 (2 * coarse.card) + 1 : ℝ) ≤
        (Nat.log 2 (2 * fine.card) + 1 : ℝ) := by
    exact_mod_cast logLe
  exact logLeReal.trans <|
    fineLog_le_prebalanceLog
      deltaPos deltaLeOne fineNonempty fineDistinct fineBoundedBase

theorem realLog_card_lt_dyadicLog
    (cardinality : ℕ)
    (cardinalityPos : 0 < cardinality) :
    Real.log (cardinality : ℝ) <
      (Nat.log 2 (2 * cardinality) + 1 : ℝ) := by
  have cardinalityLt :
      cardinality <
        2 ^ (Nat.log 2 (2 * cardinality) + 1) := by
    calc
      cardinality < 2 * cardinality := by omega
      _ <
          2 ^ (Nat.log 2 (2 * cardinality) + 1) := by
        simpa using
          Nat.lt_pow_succ_log_self
            (by norm_num : 1 < 2) (2 * cardinality)
  have logarithmLt :
      Real.log (cardinality : ℝ) <
        Real.log
          ((2 : ℝ) ^
            (Nat.log 2 (2 * cardinality) + 1)) := by
    apply Real.log_lt_log
    · exact_mod_cast cardinalityPos
    · exact_mod_cast cardinalityLt
  have logTwoLtOne : Real.log 2 < 1 := by
    have raw :=
      Real.log_lt_sub_one_of_pos
        (show (0 : ℝ) < 2 by norm_num)
        (show (2 : ℝ) ≠ 1 by norm_num)
    norm_num at raw ⊢
    exact raw
  calc
    Real.log (cardinality : ℝ) <
        Real.log
          ((2 : ℝ) ^
            (Nat.log 2 (2 * cardinality) + 1)) :=
      logarithmLt
    _ =
        (Nat.log 2 (2 * cardinality) + 1 : ℝ) *
          Real.log 2 := by
      rw [Real.log_pow]
      norm_num
    _ ≤ (Nat.log 2 (2 * cardinality) + 1 : ℝ) := by
      have exponentNonnegative :
          (0 : ℝ) ≤
            (Nat.log 2 (2 * cardinality) + 1 : ℕ) := by
        positivity
      nlinarith

theorem coarseRealLog_lt_prebalanceLog
    (section6 : PureWZ2Section6Cover fine coarse)
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4) :
    Real.log (coarse.card : ℝ) <
      prebalanceLogCoefficient *
        (1 + Real.log delta⁻¹) := by
  have coarsePos : 0 < coarse.card := by
    let source : Fin fine.card := ⟨0, fineNonempty⟩
    rcases section6.covers source with ⟨parent, _⟩
    exact Nat.zero_lt_of_lt parent.isLt
  exact
    (realLog_card_lt_dyadicLog coarse.card coarsePos).trans_le <|
      coarseLog_le_prebalanceLog
        section6 deltaPos deltaLeOne fineNonempty
          fineDistinct fineBoundedBase

theorem allEdges_card_le_coarse_mul_cells :
    exactification.incidence.allEdges.card ≤
      coarse.card * input.fineCells.card := by
  calc
    exactification.incidence.allEdges.card =
        exactification.incidence.edgePool.card := by
      simp [
        PureWZ2Prop62FourDegreeIncidenceData.allEdges,
        Fintype.card_coe
      ]
    _ =
        (input.referencePairs
          multiplicity parentClass treeCleanup).card := by
      rw [exactification.incidence_edgePool_eq]
    _ ≤ multiplicity.selectedPairs.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ input.positivePairs.card :=
      Finset.card_le_card multiplicity.selectedPairs_subset
    _ ≤ (Finset.univ ×ˢ input.fineCells).card := by
      exact
        Finset.card_le_card
          (Finset.filter_subset _ _)
    _ = coarse.card * input.fineCells.card := by
      simp [Finset.card_product]

theorem allEdgesLog_le_prebalanceLog
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4) :
    (Nat.log 2 exactification.incidence.allEdges.card + 1 : ℝ) ≤
      2 * prebalanceLogCoefficient *
        (1 + Real.log delta⁻¹) := by
  have coarseCardPos : 0 < coarse.card := by
    let source : Fin fine.card := ⟨0, fineNonempty⟩
    rcases cover.covers source with ⟨parent, _⟩
    exact Nat.zero_lt_of_lt parent.isLt
  have fineCellsPos : 0 < input.fineCells.card :=
    input.fineCells_nonempty.card_pos
  have logLe :
      Nat.log 2 exactification.incidence.allEdges.card + 1 ≤
        Nat.log 2 (coarse.card * input.fineCells.card) + 1 :=
    Nat.add_le_add_right
      (Nat.log_mono_right
        (input.allEdges_card_le_coarse_mul_cells
          multiplicity parentClass treeCleanup exactification)) 1
  have productLog :
      Nat.log 2 (coarse.card * input.fineCells.card) + 1 ≤
        (Nat.log 2 (2 * coarse.card) + 1) +
          (Nat.log 2 (2 * input.fineCells.card) + 1) :=
    natLog_product_add_one_le
      coarse.card input.fineCells.card coarseCardPos fineCellsPos
  have coarseLog :=
    coarseLog_le_prebalanceLog cover
      deltaPos deltaLeOne fineNonempty fineDistinct fineBoundedBase
  have cellLog :=
    input.fineCellLog_le_prebalanceLog deltaLeOne
  calc
    (Nat.log 2 exactification.incidence.allEdges.card + 1 : ℝ) ≤
        (Nat.log 2 (2 * coarse.card) + 1 : ℝ) +
          (Nat.log 2 (2 * input.fineCells.card) + 1 : ℝ) := by
      exact_mod_cast logLe.trans productLog
    _ ≤
        prebalanceLogCoefficient * (1 + Real.log delta⁻¹) +
          prebalanceLogCoefficient * (1 + Real.log delta⁻¹) := by
      exact add_le_add coarseLog cellLog
    _ =
        2 * prebalanceLogCoefficient *
          (1 + Real.log delta⁻¹) := by ring

theorem commonBinCount_le_four_allEdgesLog
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges} :
    input.commonBinCount
        multiplicity parentClass treeCleanup exactification bins ≤
      4 * (Nat.log 2 exactification.incidence.allEdges.card + 1) := by
  have fineBin :
      bins.fineCellBin.binCount =
        Nat.log 2 exactification.incidence.allEdges.card + 1 :=
    bins.fineCellBin.binCount_eq
  have parentCoarseCard :
      bins.fineCellBin.selectedEdges.card ≤
        exactification.incidence.allEdges.card :=
    Finset.card_le_card bins.fineCellBin.selectedEdges_subset
  have parentCoarseBin :
      bins.parentCoarseBin.binCount ≤
        Nat.log 2 exactification.incidence.allEdges.card + 1 := by
    rw [bins.parentCoarseBin.binCount_eq]
    exact
      Nat.add_le_add_right
        (Nat.log_mono_right parentCoarseCard) 1
  have coarseCellCard :
      bins.parentCoarseBin.selectedEdges.card ≤
        exactification.incidence.allEdges.card :=
    Finset.card_le_card <|
      bins.parentCoarseBin.selectedEdges_subset.trans
        bins.fineCellBin.selectedEdges_subset
  have coarseCellBin :
      bins.coarseCellBin.binCount ≤
        Nat.log 2 exactification.incidence.allEdges.card + 1 := by
    rw [bins.coarseCellBin.binCount_eq]
    exact
      Nat.add_le_add_right
        (Nat.log_mono_right coarseCellCard) 1
  unfold PureWZ2Prop62PacketCellInput.commonBinCount
  rw [fineBin]
  have edgeLogPos :
      0 < Nat.log 2 exactification.incidence.allEdges.card + 1 := by
    omega
  omega

theorem canonicalPeelingA0_le_logFourth
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}
    (depthBound : ℕ)
    (depthLe : schedule.levelCount ≤ depthBound) :
    (input.canonicalPeelingA0
        multiplicity parentClass treeCleanup exactification bins : ℝ) ≤
      (8 * (depthBound + 2) * 4 ^ 4 : ℝ) *
        (Nat.log 2 exactification.incidence.allEdges.card + 1 : ℝ) ^ 4 := by
  let edgeLog := Nat.log 2 exactification.incidence.allEdges.card + 1
  have commonBin :
      input.commonBinCount
          multiplicity parentClass treeCleanup exactification bins ≤
        4 * edgeLog := by
    simpa only [edgeLog] using
      input.commonBinCount_le_four_allEdgesLog
        multiplicity parentClass treeCleanup exactification
  have naturalBound :
      input.canonicalPeelingA0
          multiplicity parentClass treeCleanup exactification bins ≤
        8 * (depthBound + 2) * (4 * edgeLog) ^ 4 := by
    unfold PureWZ2Prop62PacketCellInput.canonicalPeelingA0
    gcongr
  have realBound :
      (input.canonicalPeelingA0
          multiplicity parentClass treeCleanup exactification bins : ℝ) ≤
        (8 * (depthBound + 2) * (4 * edgeLog) ^ 4 : ℕ) := by
    exact_mod_cast naturalBound
  calc
    (input.canonicalPeelingA0
        multiplicity parentClass treeCleanup exactification bins : ℝ) ≤
        (8 * (depthBound + 2) * (4 * edgeLog) ^ 4 : ℕ) :=
      realBound
    _ =
        (8 * (depthBound + 2) * 4 ^ 4 : ℝ) *
          (edgeLog : ℝ) ^ 4 := by
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
        Nat.cast_pow]
      ring
    _ =
        (8 * (depthBound + 2) * 4 ^ 4 : ℝ) *
          (Nat.log 2 exactification.incidence.allEdges.card + 1 : ℝ) ^ 4 := by
      simp only [edgeLog, Nat.cast_add, Nat.cast_one]

theorem canonicalPeelingA0_le_prebalanceLogFourth
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}
    (depthBound : ℕ)
    (depthLe : schedule.levelCount ≤ depthBound)
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4) :
    (input.canonicalPeelingA0
        multiplicity parentClass treeCleanup exactification bins : ℝ) ≤
      (8 * (depthBound + 2) * 8 ^ 4 : ℝ) *
        (prebalanceLogCoefficient *
          (1 + Real.log delta⁻¹)) ^ 4 := by
  calc
    (input.canonicalPeelingA0
        multiplicity parentClass treeCleanup exactification bins : ℝ) ≤
        (8 * (depthBound + 2) * 4 ^ 4 : ℝ) *
          (Nat.log 2 exactification.incidence.allEdges.card + 1 : ℝ) ^ 4 :=
      input.canonicalPeelingA0_le_logFourth
        multiplicity parentClass treeCleanup exactification
          depthBound depthLe
    _ ≤
        (8 * (depthBound + 2) * 4 ^ 4 : ℝ) *
          (2 * prebalanceLogCoefficient *
            (1 + Real.log delta⁻¹)) ^ 4 := by
      gcongr
      exact
        input.allEdgesLog_le_prebalanceLog
          multiplicity parentClass treeCleanup exactification
            deltaPos deltaLeOne fineNonempty fineDistinct fineBoundedBase
    _ =
        (8 * (depthBound + 2) * 8 ^ 4 : ℝ) *
          (prebalanceLogCoefficient *
            (1 + Real.log delta⁻¹)) ^ 4 := by
      ring

theorem prebalanceParentDegreeLoss_le_logCube
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4) :
    input.prebalanceParentDegreeLoss multiplicity parentClass ≤
      (128 : ENNReal) *
        (ENNReal.ofReal
          (prebalanceLogCoefficient *
            (1 + Real.log delta⁻¹))) ^ 3 := by
  let envelope : ℝ :=
    prebalanceLogCoefficient * (1 + Real.log delta⁻¹)
  let envelopeENN : ENNReal := ENNReal.ofReal envelope
  have fineLogReal :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤ envelope := by
    simpa only [envelope] using
      fineLog_le_prebalanceLog
        deltaPos deltaLeOne fineNonempty fineDistinct fineBoundedBase
  have cellLogReal :
      (Nat.log 2 (2 * input.fineCells.card) + 1 : ℝ) ≤ envelope := by
    simpa only [envelope] using
      input.fineCellLog_le_prebalanceLog deltaLeOne
  have fineLogENN :
      (Nat.log 2 (2 * fine.card) + 1 : ENNReal) ≤ envelopeENN := by
    have converted := ENNReal.ofReal_mono fineLogReal
    rw [ENNReal.ofReal_add (by positivity)] at converted <;> norm_num
    simpa only [
      envelopeENN, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one
    ] using converted
  have cellLogENN :
      (Nat.log 2 (2 * input.fineCells.card) + 1 : ENNReal) ≤
        envelopeENN := by
    have converted := ENNReal.ofReal_mono cellLogReal
    rw [ENNReal.ofReal_add (by positivity)] at converted <;> norm_num
    simpa only [
      envelopeENN, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one
    ] using converted
  have multiplicityLogENN :
      (multiplicity.binCount : ENNReal) ≤ 2 * envelopeENN := by
    calc
      (multiplicity.binCount : ENNReal) ≤
          (Nat.log 2 (2 * fine.card) + 1 : ENNReal) +
            (Nat.log 2 (2 * input.fineCells.card) + 1 : ENNReal) := by
        exact_mod_cast
          input.multiplicityBinCount_le_fineCellLogs multiplicity
      _ ≤ envelopeENN + envelopeENN := add_le_add fineLogENN cellLogENN
      _ = 2 * envelopeENN := by ring
  have weightLogENN :
      (parentClass.weightBinCount : ENNReal) ≤
        2 * envelopeENN := by
    have weightLe :
        (parentClass.weightBinCount : ENNReal) ≤
          (multiplicity.binCount : ENNReal) := by
      exact_mod_cast
        input.weightBinCount_le_multiplicityBinCount
          multiplicity parentClass
    exact weightLe.trans multiplicityLogENN
  have fiberLogENN :
      (parentClass.fiberBinCount : ENNReal) ≤ envelopeENN := by
    have fiberLe :
        (parentClass.fiberBinCount : ENNReal) ≤
          (Nat.log 2 (2 * fine.card) + 1 : ENNReal) := by
      exact_mod_cast
        input.fiberBinCount_le_fineLog multiplicity parentClass
    exact fiberLe.trans fineLogENN
  unfold prebalanceParentDegreeLoss
  calc
    (32 : ENNReal) *
          multiplicity.binCount *
          parentClass.weightBinCount *
          parentClass.fiberBinCount ≤
        32 * (2 * envelopeENN) * (2 * envelopeENN) * envelopeENN := by
      gcongr
    _ = 128 * envelopeENN ^ 3 := by ring
    _ = _ := rfl

theorem prebalancePacketDensityLoss_le_logCube
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4) :
    input.prebalancePacketDensityLoss multiplicity parentClass ≤
      (64 : ENNReal) *
        (ENNReal.ofReal
          (prebalanceLogCoefficient *
            (1 + Real.log delta⁻¹))) ^ 3 := by
  let envelope : ENNReal :=
    ENNReal.ofReal
      (prebalanceLogCoefficient * (1 + Real.log delta⁻¹))
  have parentLoss :
      input.prebalanceParentDegreeLoss multiplicity parentClass ≤
        128 * envelope ^ 3 := by
    simpa only [envelope] using
      input.prebalanceParentDegreeLoss_le_logCube
        multiplicity parentClass deltaPos deltaLeOne fineNonempty
          fineDistinct fineBoundedBase
  have packetTwice :
      2 * input.prebalancePacketDensityLoss multiplicity parentClass =
        input.prebalanceParentDegreeLoss multiplicity parentClass := by
    simp [prebalancePacketDensityLoss, prebalanceParentDegreeLoss]
    ring
  have packetBound :
      input.prebalancePacketDensityLoss multiplicity parentClass * 2 ≤
        (64 * envelope ^ 3) * 2 := by
    calc
      input.prebalancePacketDensityLoss multiplicity parentClass * 2 =
          input.prebalanceParentDegreeLoss multiplicity parentClass := by
        simpa only [mul_comm] using packetTwice
      _ ≤ 128 * envelope ^ 3 := parentLoss
      _ = (64 * envelope ^ 3) * 2 := by ring
  have twoPos : (0 : ENNReal) < 2 := by norm_num
  have twoTop : (2 : ENNReal) ≠ ⊤ := by norm_num
  exact
    (ENNReal.mul_le_mul_iff_left twoPos.ne' twoTop).mp packetBound

theorem prebalanceDyadicProduct_le_logCube
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4) :
    (multiplicity.binCount : ENNReal) *
        parentClass.weightBinCount *
        parentClass.fiberBinCount ≤
      4 *
        (ENNReal.ofReal
          (prebalanceLogCoefficient *
            (1 + Real.log delta⁻¹))) ^ 3 := by
  let product : ENNReal :=
    (multiplicity.binCount : ENNReal) *
      parentClass.weightBinCount *
      parentClass.fiberBinCount
  let envelope : ENNReal :=
    ENNReal.ofReal
      (prebalanceLogCoefficient * (1 + Real.log delta⁻¹))
  have packetBound :
      input.prebalancePacketDensityLoss multiplicity parentClass ≤
        64 * envelope ^ 3 := by
    simpa only [envelope] using
      input.prebalancePacketDensityLoss_le_logCube
        multiplicity parentClass deltaPos deltaLeOne fineNonempty
          fineDistinct fineBoundedBase
  have scaled : product * 16 ≤ (4 * envelope ^ 3) * 16 := by
    calc
      product * 16 =
          input.prebalancePacketDensityLoss multiplicity parentClass := by
        simp [product, prebalancePacketDensityLoss]
        ring
      _ ≤ 64 * envelope ^ 3 := packetBound
      _ = (4 * envelope ^ 3) * 16 := by ring
  have sixteenPos : (0 : ENNReal) < 16 := by norm_num
  have sixteenTop : (16 : ENNReal) ≠ ⊤ := by norm_num
  exact
    (ENNReal.mul_le_mul_iff_left
      sixteenPos.ne' sixteenTop).mp scaled

theorem canonicalPeelingA0_le_prebalanceLogFourthENN
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}
    (depthBound : ℕ)
    (depthLe : schedule.levelCount ≤ depthBound)
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4) :
    (input.canonicalPeelingA0
        multiplicity parentClass treeCleanup exactification bins : ENNReal) ≤
      ENNReal.ofReal (8 * (depthBound + 2) * 8 ^ 4 : ℝ) *
        (ENNReal.ofReal
          (prebalanceLogCoefficient *
            (1 + Real.log delta⁻¹))) ^ 4 := by
  have realBound :=
    input.canonicalPeelingA0_le_prebalanceLogFourth
      multiplicity parentClass treeCleanup exactification
        (bins := bins)
        depthBound depthLe deltaPos deltaLeOne fineNonempty
        fineDistinct fineBoundedBase
  have converted := ENNReal.ofReal_mono realBound
  have coefficientNonnegative :
      (0 : ℝ) ≤ 8 * (depthBound + 2) * 8 ^ 4 := by
    positivity
  have envelopeNonnegative :
      0 ≤
        prebalanceLogCoefficient *
          (1 + Real.log delta⁻¹) := by
    have logNonnegative : 0 ≤ Real.log delta⁻¹ := by
      apply Real.log_nonneg
      exact (one_le_inv₀ deltaPos).mpr deltaLeOne
    exact mul_nonneg
      (zero_le_one.trans one_le_prebalanceLogCoefficient)
      (by linarith)
  rw [ENNReal.ofReal_mul coefficientNonnegative,
    ENNReal.ofReal_pow envelopeNonnegative] at converted
  simpa only [ENNReal.ofReal_natCast] using converted

theorem threeDegreeBinProduct_le_prebalanceLogCube
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4) :
    (bins.fineCellBin.binCount : ENNReal) *
        bins.parentCoarseBin.binCount *
        bins.coarseCellBin.binCount ≤
      8 *
        (ENNReal.ofReal
          (prebalanceLogCoefficient *
            (1 + Real.log delta⁻¹))) ^ 3 := by
  let edgeLog := Nat.log 2 exactification.incidence.allEdges.card + 1
  let envelope : ENNReal :=
    ENNReal.ofReal
      (prebalanceLogCoefficient * (1 + Real.log delta⁻¹))
  have edgeLogReal :
      (edgeLog : ℝ) ≤
        2 * prebalanceLogCoefficient * (1 + Real.log delta⁻¹) := by
    simpa only [edgeLog, Nat.cast_add, Nat.cast_one] using
      input.allEdgesLog_le_prebalanceLog
        multiplicity parentClass treeCleanup exactification
          deltaPos deltaLeOne fineNonempty fineDistinct fineBoundedBase
  have edgeLogENN : (edgeLog : ENNReal) ≤ 2 * envelope := by
    have converted := ENNReal.ofReal_mono edgeLogReal
    rw [show
      ENNReal.ofReal
          (2 * prebalanceLogCoefficient *
            (1 + Real.log delta⁻¹)) =
        2 * envelope by
          dsimp only [envelope]
          rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring] at converted
    simpa only [ENNReal.ofReal_natCast] using converted
  have fineBin :
      bins.fineCellBin.binCount ≤ edgeLog := by
    rw [bins.fineCellBin.binCount_eq]
  have parentCoarseBin :
      bins.parentCoarseBin.binCount ≤ edgeLog := by
    rw [bins.parentCoarseBin.binCount_eq]
    apply Nat.add_le_add_right
    apply Nat.log_mono_right
    exact Finset.card_le_card bins.fineCellBin.selectedEdges_subset
  have coarseCellBin :
      bins.coarseCellBin.binCount ≤ edgeLog := by
    rw [bins.coarseCellBin.binCount_eq]
    apply Nat.add_le_add_right
    apply Nat.log_mono_right
    exact Finset.card_le_card <|
      bins.parentCoarseBin.selectedEdges_subset.trans
        bins.fineCellBin.selectedEdges_subset
  have fineBinENN :
      (bins.fineCellBin.binCount : ENNReal) ≤ edgeLog := by
    exact_mod_cast fineBin
  have parentCoarseBinENN :
      (bins.parentCoarseBin.binCount : ENNReal) ≤ edgeLog := by
    exact_mod_cast parentCoarseBin
  have coarseCellBinENN :
      (bins.coarseCellBin.binCount : ENNReal) ≤ edgeLog := by
    exact_mod_cast coarseCellBin
  have edgeCube :
      (edgeLog : ENNReal) ^ 3 ≤ (2 * envelope) ^ 3 := by
    gcongr
  calc
    (bins.fineCellBin.binCount : ENNReal) *
          bins.parentCoarseBin.binCount *
          bins.coarseCellBin.binCount ≤
        (edgeLog : ENNReal) * edgeLog * edgeLog := by
      gcongr
    _ = (edgeLog : ENNReal) ^ 3 := by ring
    _ ≤ (2 * envelope) ^ 3 := edgeCube
    _ = 8 * envelope ^ 3 := by ring
    _ = _ := rfl

theorem muFine_le_parentFiberCard
    {parent : Fin coarse.card}
    (parentMem : parent ∈ treeCleanup.referenceParents) :
    multiplicity.muFine ≤ input.parentFiberCard parent := by
  rcases
      treeCleanup.reference_parent_has_selected_pair
        input multiplicity parentClass schedule parentMem
    with ⟨pair, pairMem⟩
  have pairSelected :
      pair ∈ multiplicity.selectedPairs :=
    (Finset.mem_filter.mp pairMem).1
  have pairParent : pair.1 = parent :=
    (Finset.mem_filter.mp pairMem).2
  have packetSubset :
      input.packetCellSources pair.1 pair.2 ⊆
        wz2PaperFullFiberIndices fine coarse pair.1 := by
    intro source sourceMem
    exact
      (input.mem_packetCellSources_iff
        pair.1 pair.2 source).mp sourceMem |>.2.1
  calc
    multiplicity.muFine ≤ input.packetCellMultiplicity pair :=
      (multiplicity.multiplicity_band pair pairSelected).1
    _ =
        (input.packetCellSources pair.1 pair.2).card := rfl
    _ ≤
        (wz2PaperFullFiberIndices fine coarse pair.1).card :=
      Finset.card_le_card packetSubset
    _ = input.parentFiberCard parent := by
      rw [parentFiberCard, pairParent]

theorem selectedParents_card_mul_fiberFloor_le_fine_card :
    parentClass.selectedParents.card * parentClass.fiberFloor ≤
      fine.card := by
  let parentMap := cover.toWZ1PaperTubeCover.parent
  have fiberEq :
      ∀ parent : Fin coarse.card,
        wz2PaperFullFiberIndices fine coarse parent =
          (Finset.univ : Finset (Fin fine.card)).filter
            (fun source => parentMap source = parent) := by
    intro parent
    ext source
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro sourceMem
      exact
        (cover.toWZ1PaperTubeCover.parent_unique
          source parent
          ((mem_wz2PaperFullFiberIndices_iff
            parent source).mp sourceMem)).symm
    · intro sourceParent
      rw [← sourceParent]
      exact
        (mem_wz2PaperFullFiberIndices_iff
          (parentMap source) source).mpr
          (cover.toWZ1PaperTubeCover.parent_covers source)
  have fiberSum :
      (∑ parent ∈ parentClass.selectedParents,
          input.parentFiberCard parent) =
        ((Finset.univ : Finset (Fin fine.card)).filter
          (fun source =>
            parentMap source ∈ parentClass.selectedParents)).card := by
    have raw :=
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin fine.card))
        parentClass.selectedParents parentMap
    calc
      (∑ parent ∈ parentClass.selectedParents,
          input.parentFiberCard parent) =
          ∑ parent ∈ parentClass.selectedParents,
            ((Finset.univ : Finset (Fin fine.card)).filter
              (fun source => parentMap source = parent)).card := by
        apply Finset.sum_congr rfl
        intro parent _
        rw [parentFiberCard, fiberEq]
      _ = _ := raw
  calc
    parentClass.selectedParents.card * parentClass.fiberFloor =
        ∑ _parent ∈ parentClass.selectedParents,
          parentClass.fiberFloor := by
      simp
    _ ≤
        ∑ parent ∈ parentClass.selectedParents,
          input.parentFiberCard parent := by
      exact Finset.sum_le_sum fun parent parentMem =>
        (parentClass.fiber_card_band parent parentMem).1
    _ =
        ((Finset.univ : Finset (Fin fine.card)).filter
          (fun source =>
            parentMap source ∈ parentClass.selectedParents)).card :=
      fiberSum
    _ ≤ fine.card := by
      simpa using
        Finset.card_le_card
          (Finset.filter_subset
            (fun source : Fin fine.card =>
              parentMap source ∈ parentClass.selectedParents)
            Finset.univ)

theorem sourceShading_mass_le_selectedParentWeight :
    shading.mass ≤
      ((multiplicity.binCount : ENNReal) *
        parentClass.weightBinCount *
        parentClass.fiberBinCount) *
        (∑ parent ∈ parentClass.selectedParents,
          (input.parentIncidenceWeight multiplicity parent : ENNReal)) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  let positiveCount : ENNReal :=
    ∑ pair ∈ input.positivePairs,
      (input.packetCellMultiplicity pair : ENNReal)
  let selectedCount : ENNReal :=
    ∑ pair ∈ multiplicity.selectedPairs,
      (input.packetCellMultiplicity pair : ENNReal)
  let weightClassCount : ENNReal :=
    ∑ parent ∈ parentClass.weightClass,
      (input.parentIncidenceWeight multiplicity parent : ENNReal)
  let selectedParentCount : ENNReal :=
    ∑ parent ∈ parentClass.selectedParents,
      (input.parentIncidenceWeight multiplicity parent : ENNReal)
  have positiveCountEq :
      positiveCount =
        ((∑ pair ∈ input.positivePairs,
          input.packetCellMultiplicity pair : ℕ) : ENNReal) := by
    dsimp only [positiveCount]
    rw [Nat.cast_sum]
  have classRetention :
      positiveCount ≤
        (multiplicity.binCount : ENNReal) * selectedCount := by
    dsimp only [positiveCount, selectedCount]
    exact_mod_cast multiplicity.class_retention
  have selectedCountEq :
      selectedCount =
        ∑ parent ∈ input.multiplicityParents multiplicity,
          (input.parentIncidenceWeight multiplicity parent : ENNReal) := by
    dsimp only [selectedCount]
    exact_mod_cast
      (input.sum_parentIncidenceWeight multiplicity).symm
  have weightRetention :
      selectedCount ≤
        (parentClass.weightBinCount : ENNReal) *
          weightClassCount := by
    rw [selectedCountEq]
    dsimp only [weightClassCount]
    exact_mod_cast parentClass.weight_retention
  have fiberRetention :
      weightClassCount ≤
        (parentClass.fiberBinCount : ENNReal) *
          selectedParentCount :=
    parentClass.fiber_weight_retention
  rw [input.sourceShading_mass_eq]
  rw [← positiveCountEq]
  calc
    positiveCount *
          volume (wz1PaperGridCube delta (0, 0, 0)) ≤
        ((multiplicity.binCount : ENNReal) * selectedCount) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := by
      gcongr
    _ ≤
        ((multiplicity.binCount : ENNReal) *
          ((parentClass.weightBinCount : ENNReal) *
            weightClassCount)) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := by
      gcongr
    _ ≤
        ((multiplicity.binCount : ENNReal) *
          ((parentClass.weightBinCount : ENNReal) *
            ((parentClass.fiberBinCount : ENNReal) *
              selectedParentCount))) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := by
      gcongr
    _ = _ := by
      dsimp only [selectedParentCount]
      ring

theorem sourceShading_mass_le_weightFloor :
    shading.mass ≤
      ((multiplicity.binCount : ENNReal) *
        parentClass.weightBinCount *
        parentClass.fiberBinCount) *
        ((parentClass.selectedParents.card : ENNReal) *
          (2 * parentClass.weightFloor : ℕ)) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  calc
    shading.mass ≤
        ((multiplicity.binCount : ENNReal) *
          parentClass.weightBinCount *
          parentClass.fiberBinCount) *
          (∑ parent ∈ parentClass.selectedParents,
            (input.parentIncidenceWeight multiplicity parent : ENNReal)) *
          volume (wz1PaperGridCube delta (0, 0, 0)) :=
      input.sourceShading_mass_le_selectedParentWeight
        multiplicity parentClass
    _ ≤
        ((multiplicity.binCount : ENNReal) *
          parentClass.weightBinCount *
          parentClass.fiberBinCount) *
          (∑ _parent ∈ parentClass.selectedParents,
            (2 * parentClass.weightFloor : ℕ)) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := by
      gcongr
      calc
        (∑ parent ∈ parentClass.selectedParents,
            (input.parentIncidenceWeight multiplicity parent : ENNReal)) ≤
            ∑ _parent ∈ parentClass.selectedParents,
              ((2 * parentClass.weightFloor : ℕ) : ENNReal) := by
          exact Finset.sum_le_sum fun parent parentMem => by
            exact_mod_cast
              (parentClass.weight_band parent
                (parentClass.selectedParents_subset parentMem)).2.le
        _ =
            ((∑ _parent ∈ parentClass.selectedParents,
              (2 * parentClass.weightFloor : ℕ)) : ℕ) := by
          rw [Nat.cast_sum]
    _ = _ := by
      simp [Finset.sum_const, nsmul_eq_mul]

/--
The exact finite-loss form of the paper's pre-balancing packet-density
estimate. Unlike `prebalance_parent_degree_density`, this keeps both
`muFine` and the selected complete-fiber floor visible:

`density * N_f * delta^2 ≤ loss * muFine * K * |q|`.
-/
theorem prebalance_parent_packet_density
    (densityConstant : ENNReal)
    (density :
      densityConstant * fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass) :
    densityConstant * (parentClass.fiberFloor : ENNReal) *
          Kakeya.realRpowENN delta 2 ≤
      input.prebalancePacketDensityLoss
          multiplicity parentClass *
        (multiplicity.muFine : ENNReal) *
        (parentDegree.K : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  let selectedCard : ENNReal :=
    parentClass.selectedParents.card
  let fiberFloor : ENNReal :=
    parentClass.fiberFloor
  let dyadicLoss : ENNReal :=
    (multiplicity.binCount : ENNReal) *
      parentClass.weightBinCount *
      parentClass.fiberBinCount
  have selectedCardPosNat :
      0 < parentClass.selectedParents.card :=
    parentClass.selectedParents_nonempty.card_pos
  have selectedCardPos : 0 < selectedCard := by
    simpa only [selectedCard] using
      (show
        (0 : ENNReal) <
          (parentClass.selectedParents.card : ENNReal) by
        exact_mod_cast selectedCardPosNat)
  have selectedCardTop : selectedCard ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have selectedFiberCount :
      selectedCard * fiberFloor ≤ fine.enncard := by
    simpa only [selectedCard, fiberFloor,
      Kakeya.Streamlined.TubeFamily.enncard, Nat.cast_mul] using
        (show
          ((parentClass.selectedParents.card *
            parentClass.fiberFloor : ℕ) : ENNReal) ≤
              (fine.card : ENNReal) by
          exact_mod_cast
            input.selectedParents_card_mul_fiberFloor_le_fine_card
              multiplicity parentClass)
  have densityToWeight :
      densityConstant * (selectedCard * fiberFloor) *
            Kakeya.realRpowENN delta 2 ≤
        dyadicLoss *
          (selectedCard * (2 * parentClass.weightFloor : ℕ)) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := by
    calc
      densityConstant * (selectedCard * fiberFloor) *
            Kakeya.realRpowENN delta 2 ≤
          densityConstant * fine.enncard *
            Kakeya.realRpowENN delta 2 := by
        gcongr
      _ ≤ shading.mass := density
      _ ≤
          dyadicLoss *
            (selectedCard * (2 * parentClass.weightFloor : ℕ)) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
        simpa only [dyadicLoss, selectedCard] using
          input.sourceShading_mass_le_weightFloor
            multiplicity parentClass
  have cancelledSelected :
      densityConstant * fiberFloor *
            Kakeya.realRpowENN delta 2 ≤
        dyadicLoss *
          (2 * parentClass.weightFloor : ℕ) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := by
    apply
      (ENNReal.mul_le_mul_iff_left
        selectedCardPos.ne' selectedCardTop).mp
    simpa [selectedCard, fiberFloor, mul_assoc, mul_left_comm,
      mul_comm] using densityToWeight
  rcases treeCleanup.referenceParents_nonempty with
    ⟨parent, parentMem⟩
  have weightFloorLe :
      parentClass.weightFloor ≤
        input.parentIncidenceWeight multiplicity parent :=
    (treeCleanup.reference_weight_band parent parentMem).1
  have weightUpper :
      input.parentIncidenceWeight multiplicity parent <
        2 * multiplicity.muFine *
          input.referenceParentDegree
            multiplicity parentClass treeCleanup parent :=
    input.weight_lt_two_muFine_mul_referenceParentDegree
      multiplicity parentClass treeCleanup parentMem
  have degreeUpper :
      input.referenceParentDegree
          multiplicity parentClass treeCleanup parent <
        4 * parentDegree.K :=
    (parentDegree.degree_band parent parentMem).2
  have weightFloorUpper :
      parentClass.weightFloor ≤
        8 * multiplicity.muFine * parentDegree.K := by
    calc
      parentClass.weightFloor ≤
          input.parentIncidenceWeight multiplicity parent :=
        weightFloorLe
      _ ≤
          2 * multiplicity.muFine *
            input.referenceParentDegree
              multiplicity parentClass treeCleanup parent :=
        weightUpper.le
      _ ≤
          2 * multiplicity.muFine * (4 * parentDegree.K) := by
        gcongr
      _ = 8 * multiplicity.muFine * parentDegree.K := by
        ring
  calc
    densityConstant * (parentClass.fiberFloor : ENNReal) *
          Kakeya.realRpowENN delta 2 ≤
        dyadicLoss *
          (2 * parentClass.weightFloor : ℕ) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := by
      simpa only [fiberFloor] using cancelledSelected
    _ ≤
        dyadicLoss *
          (2 * (8 * multiplicity.muFine * parentDegree.K) : ℕ) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := by
      gcongr
    _ =
        input.prebalancePacketDensityLoss multiplicity parentClass *
          (multiplicity.muFine : ENNReal) *
          (parentDegree.K : ENNReal) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := by
      simp [prebalancePacketDensityLoss, dyadicLoss]
      ring

theorem prebalancePacketDensityLoss_pos :
    0 <
      input.prebalancePacketDensityLoss
        multiplicity parentClass := by
  have multiplicityBinPos : 0 < multiplicity.binCount := by
    rw [multiplicity.binCount_eq]
    omega
  have weightBinPos : 0 < parentClass.weightBinCount := by
    rw [parentClass.weightBinCount_eq]
    omega
  have fiberBinPos : 0 < parentClass.fiberBinCount := by
    rw [parentClass.fiberBinCount_eq]
    omega
  unfold prebalancePacketDensityLoss
  positivity

theorem prebalancePacketDensityLoss_ne_top :
    input.prebalancePacketDensityLoss
        multiplicity parentClass ≠ ⊤ := by
  unfold prebalancePacketDensityLoss
  exact
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num)
          (ENNReal.natCast_ne_top multiplicity.binCount))
        (ENNReal.natCast_ne_top parentClass.weightBinCount))
      (ENNReal.natCast_ne_top parentClass.fiberBinCount)

/--
The exact finite-loss form of the paper's pre-balancing lower bound for `K`.
-/
theorem prebalance_parent_degree_density
    (densityConstant : ENNReal)
    (density :
      densityConstant * fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass) :
    densityConstant * Kakeya.realRpowENN delta 2 ≤
      input.prebalanceParentDegreeLoss
          multiplicity parentClass *
        (parentDegree.K : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  let selectedCard : ENNReal :=
    parentClass.selectedParents.card
  let fiberFloor : ENNReal :=
    parentClass.fiberFloor
  let dyadicLoss : ENNReal :=
    (multiplicity.binCount : ENNReal) *
      parentClass.weightBinCount *
      parentClass.fiberBinCount
  have selectedCardPosNat :
      0 < parentClass.selectedParents.card :=
    parentClass.selectedParents_nonempty.card_pos
  have selectedCardPos : 0 < selectedCard := by
    simpa only [selectedCard] using
      (show
        (0 : ENNReal) <
          (parentClass.selectedParents.card : ENNReal) by
        exact_mod_cast selectedCardPosNat)
  have selectedCardTop : selectedCard ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have fiberFloorPos : 0 < fiberFloor := by
    simpa only [fiberFloor] using
      (show
        (0 : ENNReal) < (parentClass.fiberFloor : ENNReal) by
        exact_mod_cast parentClass.fiberFloor_pos)
  have fiberFloorTop : fiberFloor ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have selectedFiberCount :
      selectedCard * fiberFloor ≤ fine.enncard := by
    simpa only [selectedCard, fiberFloor,
      Kakeya.Streamlined.TubeFamily.enncard, Nat.cast_mul] using
        (show
          ((parentClass.selectedParents.card *
            parentClass.fiberFloor : ℕ) : ENNReal) ≤
              (fine.card : ENNReal) by
          exact_mod_cast
            input.selectedParents_card_mul_fiberFloor_le_fine_card
              multiplicity parentClass)
  have densityToWeight :
      densityConstant * (selectedCard * fiberFloor) *
            Kakeya.realRpowENN delta 2 ≤
        dyadicLoss *
          (selectedCard * (2 * parentClass.weightFloor : ℕ)) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := by
    calc
      densityConstant * (selectedCard * fiberFloor) *
            Kakeya.realRpowENN delta 2 ≤
          densityConstant * fine.enncard *
            Kakeya.realRpowENN delta 2 := by
        gcongr
      _ ≤ shading.mass := density
      _ ≤
          dyadicLoss *
            (selectedCard * (2 * parentClass.weightFloor : ℕ)) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
        simpa only [dyadicLoss, selectedCard] using
          input.sourceShading_mass_le_weightFloor
            multiplicity parentClass
  have cancelledSelected :
      densityConstant * fiberFloor *
            Kakeya.realRpowENN delta 2 ≤
        dyadicLoss *
          (2 * parentClass.weightFloor : ℕ) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := by
    apply
      (ENNReal.mul_le_mul_iff_left
        selectedCardPos.ne' selectedCardTop).mp
    simpa [selectedCard, fiberFloor, mul_assoc, mul_left_comm,
      mul_comm] using densityToWeight
  rcases treeCleanup.referenceParents_nonempty with
    ⟨parent, parentMem⟩
  have weightFloorLe :
      parentClass.weightFloor ≤
        input.parentIncidenceWeight multiplicity parent :=
    (treeCleanup.reference_weight_band parent parentMem).1
  have weightUpper :
      input.parentIncidenceWeight multiplicity parent <
        2 * multiplicity.muFine *
          input.referenceParentDegree
            multiplicity parentClass treeCleanup parent :=
    input.weight_lt_two_muFine_mul_referenceParentDegree
      multiplicity parentClass treeCleanup parentMem
  have degreeUpper :
      input.referenceParentDegree
          multiplicity parentClass treeCleanup parent <
        4 * parentDegree.K :=
    (parentDegree.degree_band parent parentMem).2
  have muFineUpper :
      multiplicity.muFine < 2 * parentClass.fiberFloor :=
    (input.muFine_le_parentFiberCard
      multiplicity parentClass treeCleanup parentMem).trans_lt
      (treeCleanup.reference_fiber_card_band parent parentMem).2
  have weightFloorUpper :
      parentClass.weightFloor ≤
        16 * parentClass.fiberFloor * parentDegree.K := by
    calc
      parentClass.weightFloor ≤
          input.parentIncidenceWeight multiplicity parent :=
        weightFloorLe
      _ ≤
          2 * multiplicity.muFine *
            input.referenceParentDegree
              multiplicity parentClass treeCleanup parent :=
        weightUpper.le
      _ ≤
          2 * (2 * parentClass.fiberFloor) *
            (4 * parentDegree.K) := by
        gcongr <;> omega
      _ = 16 * parentClass.fiberFloor * parentDegree.K := by
        ring
  have densityWithFiber :
      densityConstant * fiberFloor *
            Kakeya.realRpowENN delta 2 ≤
        (32 * dyadicLoss) *
          fiberFloor *
          (parentDegree.K : ENNReal) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := by
    calc
      densityConstant * fiberFloor *
            Kakeya.realRpowENN delta 2 ≤
          dyadicLoss *
            (2 * parentClass.weightFloor : ℕ) *
            volume (wz1PaperGridCube delta (0, 0, 0)) :=
        cancelledSelected
      _ ≤
          dyadicLoss *
            (2 * (16 * parentClass.fiberFloor * parentDegree.K) : ℕ) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
        gcongr
      _ =
          (32 * dyadicLoss) *
            fiberFloor *
            (parentDegree.K : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        ring
  apply
    (ENNReal.mul_le_mul_iff_left
      fiberFloorPos.ne' fiberFloorTop).mp
  simpa [prebalanceParentDegreeLoss, dyadicLoss, fiberFloor,
    mul_assoc, mul_left_comm, mul_comm] using densityWithFiber

/--
Power-form consequence of `prebalance_parent_degree_density`.

If the three dyadic losses cost at most `delta ^ (-lossExponent)`, an input
density `delta ^ densityExponent` forces

`delta ^ (densityExponent + lossExponent - 1) ≤ K`.
-/
theorem referenceParentDegree_power_floor
    (densityExponent lossExponent : ℝ)
    (density :
      Kakeya.realRpowENN delta densityExponent *
          fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass)
    (lossBound :
      input.prebalanceParentDegreeLoss
          multiplicity parentClass ≤
        Kakeya.realRpowENN delta (-lossExponent)) :
    Kakeya.realRpowENN delta
        (densityExponent + lossExponent - 1) ≤
      (parentDegree.K : ENNReal) := by
  have exactDensity :=
    input.prebalance_parent_degree_density
      multiplicity parentClass treeCleanup exactification
        parentDegree
        (Kakeya.realRpowENN delta densityExponent)
        density
  have cubeVolume :
      volume (wz1PaperGridCube delta (0, 0, 0)) =
        Kakeya.realRpowENN delta 3 := by
    rw [wz1PaperGridCube_volume_exact input.delta_pos]
    simp [Kakeya.realRpowENN, Real.rpow_natCast]
  rw [cubeVolume] at exactDensity
  have boundedDensity :
      Kakeya.realRpowENN delta densityExponent *
            Kakeya.realRpowENN delta 2 ≤
        Kakeya.realRpowENN delta (-lossExponent) *
          (parentDegree.K : ENNReal) *
          Kakeya.realRpowENN delta 3 := by
    exact exactDensity.trans <| by
      gcongr
  let cancellationFactor : ENNReal :=
    Kakeya.realRpowENN delta (3 - lossExponent)
  have cancellationFactorPos : 0 < cancellationFactor := by
    simp [
      cancellationFactor, Kakeya.realRpowENN,
      Real.rpow_pos_of_pos input.delta_pos
    ]
  have cancellationFactorTop : cancellationFactor ≠ ⊤ := by
    simp [cancellationFactor, Kakeya.realRpowENN]
  apply
    (ENNReal.mul_le_mul_iff_left
      cancellationFactorPos.ne' cancellationFactorTop).mp
  calc
    Kakeya.realRpowENN delta
          (densityExponent + lossExponent - 1) *
        cancellationFactor =
      Kakeya.realRpowENN delta densityExponent *
        Kakeya.realRpowENN delta 2 := by
        dsimp only [cancellationFactor]
        rw [← realRpowENN_add input.delta_pos,
          ← realRpowENN_add input.delta_pos]
        congr 1
        ring
    _ ≤
        Kakeya.realRpowENN delta (-lossExponent) *
          (parentDegree.K : ENNReal) *
          Kakeya.realRpowENN delta 3 :=
      boundedDensity
    _ =
        (parentDegree.K : ENNReal) *
          (Kakeya.realRpowENN delta (-lossExponent) *
            Kakeya.realRpowENN delta 3) := by
      ring
    _ =
        (parentDegree.K : ENNReal) *
          Kakeya.realRpowENN delta (-lossExponent + 3) := by
      rw [← realRpowENN_add input.delta_pos]
    _ =
        (parentDegree.K : ENNReal) *
          cancellationFactor := by
      dsimp only [cancellationFactor]
      congr 1
      congr 1
      ring

theorem canonical_scaled_referenceDegree_lt_of_absorptions
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup exactification parentDegree bins
          (input.canonicalPeelingA0
            multiplicity parentClass treeCleanup exactification bins))
    (depthBound : ℕ)
    (densityExponent lossExponent : ℝ)
    (deltaLtOne : delta < 1)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4)
    (depthLe : schedule.levelCount ≤ depthBound)
    (exponentGap : densityExponent + lossExponent < 1)
    (density :
      Kakeya.realRpowENN delta densityExponent *
          fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass)
    (lossBound :
      (128 : ENNReal) *
          (ENNReal.ofReal
            (prebalanceLogCoefficient *
              (1 + Real.log delta⁻¹))) ^ 3 ≤
        Kakeya.realRpowENN delta (-lossExponent))
    (tailBound :
      prebalanceTailCoefficient depthBound *
          (1 + Real.log delta⁻¹) ^ 13 ≤
        Real.rpow delta
          (-((1 - (densityExponent + lossExponent)) / 2))) :
    (40 : ℝ) *
          (input.canonicalPeelingA0
            multiplicity parentClass treeCleanup exactification bins : ℝ) ^ 3 *
          Real.log (coarse.card : ℝ) <
      (parentDegree.K : ℝ) := by
  let A0 :=
    input.canonicalPeelingA0
      multiplicity parentClass treeCleanup exactification bins
  let logEnvelope : ℝ :=
    prebalanceLogCoefficient * (1 + Real.log delta⁻¹)
  let depthCoefficient : ℝ :=
    8 * (depthBound + 2) * 8 ^ 4
  let gap : ℝ := 1 - (densityExponent + lossExponent)
  have deltaLeOne : delta ≤ 1 := deltaLtOne.le
  have preLoss :
      input.prebalanceParentDegreeLoss multiplicity parentClass ≤
        Kakeya.realRpowENN delta (-lossExponent) :=
    (input.prebalanceParentDegreeLoss_le_logCube
      multiplicity parentClass
      input.delta_pos deltaLeOne fineNonempty fineDistinct
        fineBoundedBase).trans lossBound
  have degreeFloorENN :
      Kakeya.realRpowENN delta
          (densityExponent + lossExponent - 1) ≤
        (parentDegree.K : ENNReal) :=
    input.referenceParentDegree_power_floor
      multiplicity parentClass treeCleanup exactification parentDegree
      densityExponent lossExponent density preLoss
  have degreeFloorReal :
      Real.rpow delta
          (densityExponent + lossExponent - 1) ≤
        (parentDegree.K : ℝ) := by
    have converted :=
      (ENNReal.toReal_le_toReal
        (by simp [Kakeya.realRpowENN])
        (ENNReal.natCast_ne_top parentDegree.K)).mpr degreeFloorENN
    simpa [Kakeya.realRpowENN,
      ENNReal.toReal_ofReal (Real.rpow_nonneg input.delta_pos.le _)] using
      converted
  have A0Bound :
      (A0 : ℝ) ≤ depthCoefficient * logEnvelope ^ 4 := by
    simpa only [A0, depthCoefficient, logEnvelope] using
      input.canonicalPeelingA0_le_prebalanceLogFourth
        multiplicity parentClass treeCleanup exactification
          depthBound depthLe input.delta_pos deltaLeOne
          fineNonempty fineDistinct fineBoundedBase
  have coarseLog :
      Real.log (coarse.card : ℝ) < logEnvelope := by
    simpa only [logEnvelope] using
      coarseRealLog_lt_prebalanceLog
        cover input.delta_pos deltaLeOne fineNonempty
          fineDistinct fineBoundedBase
  have A0PosReal : (0 : ℝ) < A0 := by
    exact_mod_cast
      input.canonicalPeelingA0_pos
        multiplicity parentClass treeCleanup exactification bins
  have logEnvelopePos : 0 < logEnvelope := by
    have logNonnegative : 0 ≤ Real.log delta⁻¹ := by
      apply Real.log_nonneg
      exact (one_le_inv₀ input.delta_pos).mpr deltaLeOne
    have coefficientPositive :
        (0 : ℝ) < prebalanceLogCoefficient :=
      zero_lt_one.trans_le one_le_prebalanceLogCoefficient
    dsimp only [logEnvelope]
    positivity
  have scaledUpper :
      (40 : ℝ) * (A0 : ℝ) ^ 3 *
          Real.log (coarse.card : ℝ) <
        (40 * depthCoefficient ^ 3 *
          prebalanceLogCoefficient ^ 13) *
          (1 + Real.log delta⁻¹) ^ 13 := by
    calc
      (40 : ℝ) * (A0 : ℝ) ^ 3 *
            Real.log (coarse.card : ℝ) <
          40 * (A0 : ℝ) ^ 3 * logEnvelope := by
        gcongr
      _ ≤
          40 * (depthCoefficient * logEnvelope ^ 4) ^ 3 *
            logEnvelope := by
        gcongr
      _ =
          (40 * depthCoefficient ^ 3 *
            prebalanceLogCoefficient ^ 13) *
            (1 + Real.log delta⁻¹) ^ 13 := by
        dsimp only [logEnvelope]
        ring
  have gapPos : 0 < gap := by
    dsimp only [gap]
    linarith [exponentGap]
  have strictPower :
      Real.rpow delta (-(gap / 2)) <
        Real.rpow delta (-gap) := by
    exact
      Real.rpow_lt_rpow_of_exponent_gt
        input.delta_pos deltaLtOne (by linarith)
  have exponentEq :
      densityExponent + lossExponent - 1 = -gap := by
    dsimp only [gap]
    ring
  calc
    (40 : ℝ) * (A0 : ℝ) ^ 3 *
          Real.log (coarse.card : ℝ) <
        (40 * depthCoefficient ^ 3 *
          prebalanceLogCoefficient ^ 13) *
          (1 + Real.log delta⁻¹) ^ 13 :=
      scaledUpper
    _ ≤
        Real.rpow delta (-((1 - (densityExponent + lossExponent)) / 2)) :=
      by
        simpa only [prebalanceTailCoefficient] using tailBound
    _ = Real.rpow delta (-(gap / 2)) := by
      rfl
    _ < Real.rpow delta (-gap) := strictPower
    _ = Real.rpow delta
          (densityExponent + lossExponent - 1) := by
      rw [exponentEq]
    _ ≤ (parentDegree.K : ℝ) := degreeFloorReal

/--
The common logarithmic coefficient used by the caller-supplied fine-cardinality
route.  The extra `1` pays for passing from the active-cell logarithm to its
doubled-cardinality form.
-/
def fineLogEnvelopeCoefficient (logCoefficient : ℝ) : ℝ :=
  logCoefficient + 1

theorem fineLogEnvelopeCoefficient_one_le
    {logCoefficient : ℝ}
    (logCoefficientOne : 1 ≤ logCoefficient) :
    1 ≤ fineLogEnvelopeCoefficient logCoefficient := by
  unfold fineLogEnvelopeCoefficient
  linarith

theorem fineLog_le_fineLogEnvelope
    {logCoefficient : ℝ}
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹)) :
    (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
      fineLogEnvelopeCoefficient logCoefficient *
        (1 + Real.log delta⁻¹) := by
  have logNonnegative : 0 ≤ Real.log delta⁻¹ := by
    apply Real.log_nonneg
    exact (one_le_inv₀ deltaPos).mpr deltaLeOne
  exact fineLogBound.trans <| by
    apply mul_le_mul_of_nonneg_right
    · unfold fineLogEnvelopeCoefficient
      linarith
    · linarith

theorem fineCellLog_le_fineLogEnvelope
    {logCoefficient : ℝ}
    (deltaLeOne : delta ≤ 1)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient) :
    (Nat.log 2 (2 * input.fineCells.card) + 1 : ℝ) ≤
      fineLogEnvelopeCoefficient logCoefficient *
        (1 + Real.log delta⁻¹) := by
  rw [input.fineCells_eq]
  have raw :=
    wz2_paper_active_cell_log_bound
      input.delta_pos deltaLeOne shading
  have fineCellsPos :
      0 <
        (wz1PaperActiveCells shading input.delta_pos).card := by
    rw [← input.fineCells_eq]
    exact input.fineCells_nonempty.card_pos
  have doubledLog :
      Nat.log 2
          (2 * (wz1PaperActiveCells shading input.delta_pos).card) + 1 =
        Nat.log 2
            (wz1PaperActiveCells shading input.delta_pos).card + 2 := by
    rw [Nat.mul_comm, Nat.log_mul_base (by norm_num) fineCellsPos.ne']
  have logNonnegative : 0 ≤ Real.log delta⁻¹ := by
    apply Real.log_nonneg
    exact (one_le_inv₀ input.delta_pos).mpr deltaLeOne
  have doubledRaw :
      (Nat.log 2
          (2 * (wz1PaperActiveCells shading input.delta_pos).card) + 1 :
            ℝ) ≤
        (wz2PaperBoundaryLogCoefficient + 1) *
          (1 + Real.log delta⁻¹) := by
    have doubledLogReal :
        (Nat.log 2
            (2 * (wz1PaperActiveCells shading input.delta_pos).card) + 1 :
              ℝ) =
          (Nat.log 2
              (wz1PaperActiveCells shading input.delta_pos).card + 2 :
                ℝ) := by
      exact_mod_cast doubledLog
    rw [doubledLogReal]
    have raw' :
        (Nat.log 2
            (wz1PaperActiveCells shading input.delta_pos).card + 1 : ℝ) ≤
          wz2PaperBoundaryLogCoefficient *
            (1 + Real.log delta⁻¹) := by
      exact raw.trans <| by
        have leftLe :
            5 / Real.log 2 ≤ wz2PaperBoundaryLogCoefficient :=
          le_max_right _ _
        have rightLe :
            5 * Real.log 163 / Real.log 2 + 2 ≤
              wz2PaperBoundaryLogCoefficient :=
          le_max_left _ _
        rw [show Real.log (1 / delta) = Real.log delta⁻¹ by
          congr 1
          field_simp [input.delta_pos.ne']]
        nlinarith
    calc
      (Nat.log 2
          (wz1PaperActiveCells shading input.delta_pos).card + 2 : ℝ) =
          (Nat.log 2
            (wz1PaperActiveCells shading input.delta_pos).card + 1 : ℝ) +
            1 := by ring
      _ ≤
          wz2PaperBoundaryLogCoefficient *
              (1 + Real.log delta⁻¹) + 1 := by
        gcongr
      _ ≤
          (wz2PaperBoundaryLogCoefficient + 1) *
            (1 + Real.log delta⁻¹) := by
        nlinarith
  exact doubledRaw.trans <| by
    apply mul_le_mul_of_nonneg_right
    · unfold fineLogEnvelopeCoefficient
      linarith
    · linarith

theorem coarseLog_le_fineLogEnvelope
    {logCoefficient : ℝ}
    (section6 : PureWZ2Section6Cover fine coarse)
    (deltaPos : 0 < delta)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹))
    (deltaLeOne : delta ≤ 1) :
    (Nat.log 2 (2 * coarse.card) + 1 : ℝ) ≤
      fineLogEnvelopeCoefficient logCoefficient *
        (1 + Real.log delta⁻¹) := by
  have doubledCard :
      2 * coarse.card ≤ 2 * fine.card :=
    Nat.mul_le_mul_left 2 <| coarse_card_le_fine_card section6
  have logLe :
      Nat.log 2 (2 * coarse.card) + 1 ≤
        Nat.log 2 (2 * fine.card) + 1 :=
    Nat.add_le_add_right (Nat.log_mono_right doubledCard) 1
  have logLeReal :
      (Nat.log 2 (2 * coarse.card) + 1 : ℝ) ≤
        (Nat.log 2 (2 * fine.card) + 1 : ℝ) := by
    exact_mod_cast logLe
  exact logLeReal.trans <|
    fineLog_le_fineLogEnvelope deltaPos deltaLeOne fineLogBound

theorem allEdgesLog_le_fineLogEnvelope
    {logCoefficient : ℝ}
    (deltaLeOne : delta ≤ 1)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹)) :
    (Nat.log 2 exactification.incidence.allEdges.card + 1 : ℝ) ≤
      2 * fineLogEnvelopeCoefficient logCoefficient *
        (1 + Real.log delta⁻¹) := by
  have coarseCardPos : 0 < coarse.card := by
    let source : Fin fine.card := ⟨0, by
      rcases input.fineCells_nonempty with ⟨cell, cellMem⟩
      have cellActive :
          cell ∈ wz1PaperActiveCells shading input.delta_pos := by
        rw [← input.fineCells_eq]
        exact cellMem
      rcases
          ((mem_wz1PaperActiveCells
            shading input.delta_pos cell).mp cellActive).2
        with ⟨point, ⟨source, _pointMem⟩, _pointCell⟩
      exact Nat.zero_lt_of_lt source.isLt⟩
    rcases cover.covers source with ⟨parent, _⟩
    exact Nat.zero_lt_of_lt parent.isLt
  have fineCellsPos : 0 < input.fineCells.card :=
    input.fineCells_nonempty.card_pos
  have logLe :
      Nat.log 2 exactification.incidence.allEdges.card + 1 ≤
        Nat.log 2 (coarse.card * input.fineCells.card) + 1 :=
    Nat.add_le_add_right
      (Nat.log_mono_right
        (input.allEdges_card_le_coarse_mul_cells
          multiplicity parentClass treeCleanup exactification)) 1
  have productLog :
      Nat.log 2 (coarse.card * input.fineCells.card) + 1 ≤
        (Nat.log 2 (2 * coarse.card) + 1) +
          (Nat.log 2 (2 * input.fineCells.card) + 1) :=
    natLog_product_add_one_le
      coarse.card input.fineCells.card coarseCardPos fineCellsPos
  have coarseLog :=
    coarseLog_le_fineLogEnvelope
      cover input.delta_pos fineLogBound deltaLeOne
  have cellLog :=
    input.fineCellLog_le_fineLogEnvelope
      deltaLeOne boundaryCoefficientLe
  calc
    (Nat.log 2 exactification.incidence.allEdges.card + 1 : ℝ) ≤
        (Nat.log 2 (2 * coarse.card) + 1 : ℝ) +
          (Nat.log 2 (2 * input.fineCells.card) + 1 : ℝ) := by
      exact_mod_cast logLe.trans productLog
    _ ≤
        fineLogEnvelopeCoefficient logCoefficient *
            (1 + Real.log delta⁻¹) +
          fineLogEnvelopeCoefficient logCoefficient *
            (1 + Real.log delta⁻¹) :=
      add_le_add coarseLog cellLog
    _ =
        2 * fineLogEnvelopeCoefficient logCoefficient *
          (1 + Real.log delta⁻¹) := by ring

theorem prebalanceParentDegreeLoss_le_logCube_of_fineLog
    {logCoefficient : ℝ}
    (deltaLeOne : delta ≤ 1)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹)) :
    input.prebalanceParentDegreeLoss multiplicity parentClass ≤
      (128 : ENNReal) *
        (ENNReal.ofReal
          (fineLogEnvelopeCoefficient logCoefficient *
            (1 + Real.log delta⁻¹))) ^ 3 := by
  let envelope : ℝ :=
    fineLogEnvelopeCoefficient logCoefficient *
      (1 + Real.log delta⁻¹)
  let envelopeENN : ENNReal := ENNReal.ofReal envelope
  have fineLogReal :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤ envelope := by
    simpa only [envelope] using
      fineLog_le_fineLogEnvelope
        input.delta_pos deltaLeOne fineLogBound
  have cellLogReal :
      (Nat.log 2 (2 * input.fineCells.card) + 1 : ℝ) ≤ envelope := by
    simpa only [envelope] using
      input.fineCellLog_le_fineLogEnvelope
        deltaLeOne boundaryCoefficientLe
  have fineLogENN :
      (Nat.log 2 (2 * fine.card) + 1 : ENNReal) ≤ envelopeENN := by
    have converted := ENNReal.ofReal_mono fineLogReal
    rw [ENNReal.ofReal_add (by positivity)] at converted <;> norm_num
    simpa only [
      envelopeENN, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one
    ] using converted
  have cellLogENN :
      (Nat.log 2 (2 * input.fineCells.card) + 1 : ENNReal) ≤
        envelopeENN := by
    have converted := ENNReal.ofReal_mono cellLogReal
    rw [ENNReal.ofReal_add (by positivity)] at converted <;> norm_num
    simpa only [
      envelopeENN, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one
    ] using converted
  have multiplicityLogENN :
      (multiplicity.binCount : ENNReal) ≤ 2 * envelopeENN := by
    calc
      (multiplicity.binCount : ENNReal) ≤
          (Nat.log 2 (2 * fine.card) + 1 : ENNReal) +
            (Nat.log 2 (2 * input.fineCells.card) + 1 : ENNReal) := by
        exact_mod_cast
          input.multiplicityBinCount_le_fineCellLogs multiplicity
      _ ≤ envelopeENN + envelopeENN := add_le_add fineLogENN cellLogENN
      _ = 2 * envelopeENN := by ring
  have weightLogENN :
      (parentClass.weightBinCount : ENNReal) ≤ 2 * envelopeENN := by
    have weightLe :
        (parentClass.weightBinCount : ENNReal) ≤
          (multiplicity.binCount : ENNReal) := by
      exact_mod_cast
        input.weightBinCount_le_multiplicityBinCount
          multiplicity parentClass
    exact weightLe.trans multiplicityLogENN
  have fiberLogENN :
      (parentClass.fiberBinCount : ENNReal) ≤ envelopeENN := by
    have fiberLe :
        (parentClass.fiberBinCount : ENNReal) ≤
          (Nat.log 2 (2 * fine.card) + 1 : ENNReal) := by
      exact_mod_cast
        input.fiberBinCount_le_fineLog multiplicity parentClass
    exact fiberLe.trans fineLogENN
  unfold prebalanceParentDegreeLoss
  calc
    (32 : ENNReal) *
          multiplicity.binCount *
          parentClass.weightBinCount *
          parentClass.fiberBinCount ≤
        32 * (2 * envelopeENN) * (2 * envelopeENN) * envelopeENN := by
      gcongr
    _ = 128 * envelopeENN ^ 3 := by ring
    _ = _ := rfl

theorem prebalancePacketDensityLoss_le_logCube_of_fineLog
    {logCoefficient : ℝ}
    (deltaLeOne : delta ≤ 1)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹)) :
    input.prebalancePacketDensityLoss multiplicity parentClass ≤
      (64 : ENNReal) *
        (ENNReal.ofReal
          (fineLogEnvelopeCoefficient logCoefficient *
            (1 + Real.log delta⁻¹))) ^ 3 := by
  let envelope : ENNReal :=
    ENNReal.ofReal
      (fineLogEnvelopeCoefficient logCoefficient *
        (1 + Real.log delta⁻¹))
  have parentLoss :
      input.prebalanceParentDegreeLoss multiplicity parentClass ≤
        128 * envelope ^ 3 := by
    simpa only [envelope] using
      input.prebalanceParentDegreeLoss_le_logCube_of_fineLog
        multiplicity parentClass deltaLeOne boundaryCoefficientLe fineLogBound
  have packetTwice :
      2 * input.prebalancePacketDensityLoss multiplicity parentClass =
        input.prebalanceParentDegreeLoss multiplicity parentClass := by
    simp [prebalancePacketDensityLoss, prebalanceParentDegreeLoss]
    ring
  have packetBound :
      input.prebalancePacketDensityLoss multiplicity parentClass * 2 ≤
        (64 * envelope ^ 3) * 2 := by
    calc
      input.prebalancePacketDensityLoss multiplicity parentClass * 2 =
          input.prebalanceParentDegreeLoss multiplicity parentClass := by
        simpa only [mul_comm] using packetTwice
      _ ≤ 128 * envelope ^ 3 := parentLoss
      _ = (64 * envelope ^ 3) * 2 := by ring
  exact
    (ENNReal.mul_le_mul_iff_left
      (by norm_num : (0 : ENNReal) < 2).ne' (by norm_num)).mp packetBound

theorem prebalanceDyadicProduct_le_logCube_of_fineLog
    {logCoefficient : ℝ}
    (deltaLeOne : delta ≤ 1)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹)) :
    (multiplicity.binCount : ENNReal) *
        parentClass.weightBinCount *
        parentClass.fiberBinCount ≤
      4 *
        (ENNReal.ofReal
          (fineLogEnvelopeCoefficient logCoefficient *
            (1 + Real.log delta⁻¹))) ^ 3 := by
  let product : ENNReal :=
    (multiplicity.binCount : ENNReal) *
      parentClass.weightBinCount *
      parentClass.fiberBinCount
  let envelope : ENNReal :=
    ENNReal.ofReal
      (fineLogEnvelopeCoefficient logCoefficient *
        (1 + Real.log delta⁻¹))
  have packetBound :
      input.prebalancePacketDensityLoss multiplicity parentClass ≤
        64 * envelope ^ 3 := by
    simpa only [envelope] using
      input.prebalancePacketDensityLoss_le_logCube_of_fineLog
        multiplicity parentClass deltaLeOne boundaryCoefficientLe fineLogBound
  have scaled : product * 16 ≤ (4 * envelope ^ 3) * 16 := by
    calc
      product * 16 =
          input.prebalancePacketDensityLoss multiplicity parentClass := by
        simp [product, prebalancePacketDensityLoss]
        ring
      _ ≤ 64 * envelope ^ 3 := packetBound
      _ = (4 * envelope ^ 3) * 16 := by ring
  exact
    (ENNReal.mul_le_mul_iff_left
      (by norm_num : (0 : ENNReal) < 16).ne' (by norm_num)).mp scaled

theorem canonicalPeelingA0_le_logFourthENN_of_fineLog
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}
    {logCoefficient : ℝ}
    (depthBound : ℕ)
    (depthLe : schedule.levelCount ≤ depthBound)
    (deltaLeOne : delta ≤ 1)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹)) :
    (input.canonicalPeelingA0
        multiplicity parentClass treeCleanup exactification bins : ENNReal) ≤
      ENNReal.ofReal (8 * (depthBound + 2) * 8 ^ 4 : ℝ) *
        (ENNReal.ofReal
          (fineLogEnvelopeCoefficient logCoefficient *
            (1 + Real.log delta⁻¹))) ^ 4 := by
  have edgeLog :=
    input.allEdgesLog_le_fineLogEnvelope
      multiplicity parentClass treeCleanup exactification
        deltaLeOne boundaryCoefficientLe fineLogBound
  have realBound :=
    input.canonicalPeelingA0_le_logFourth
      multiplicity parentClass treeCleanup exactification
        (bins := bins) depthBound depthLe
  have bound :
      (input.canonicalPeelingA0
          multiplicity parentClass treeCleanup exactification bins : ℝ) ≤
        (8 * (depthBound + 2) * 8 ^ 4 : ℝ) *
          (fineLogEnvelopeCoefficient logCoefficient *
            (1 + Real.log delta⁻¹)) ^ 4 := by
    calc
      (input.canonicalPeelingA0
          multiplicity parentClass treeCleanup exactification bins : ℝ) ≤
        (8 * (depthBound + 2) * 4 ^ 4 : ℝ) *
          (Nat.log 2 exactification.incidence.allEdges.card + 1 : ℝ) ^ 4 :=
        realBound
      _ ≤
        (8 * (depthBound + 2) * 4 ^ 4 : ℝ) *
          (2 * fineLogEnvelopeCoefficient logCoefficient *
            (1 + Real.log delta⁻¹)) ^ 4 := by
        gcongr
      _ =
        (8 * (depthBound + 2) * 8 ^ 4 : ℝ) *
          (fineLogEnvelopeCoefficient logCoefficient *
            (1 + Real.log delta⁻¹)) ^ 4 := by ring
  have converted := ENNReal.ofReal_mono bound
  have coefficientNonnegative :
      (0 : ℝ) ≤ 8 * (depthBound + 2) * 8 ^ 4 := by positivity
  have envelopeNonnegative :
      0 ≤
        fineLogEnvelopeCoefficient logCoefficient *
          (1 + Real.log delta⁻¹) := by
    have logNonnegative : 0 ≤ Real.log delta⁻¹ := by
      apply Real.log_nonneg
      exact (one_le_inv₀ input.delta_pos).mpr deltaLeOne
    have coefficientNonnegative :
        0 ≤ fineLogEnvelopeCoefficient logCoefficient := by
      unfold fineLogEnvelopeCoefficient
      have boundaryNonnegative :
          0 ≤ wz2PaperBoundaryLogCoefficient := by
        unfold wz2PaperBoundaryLogCoefficient
        positivity
      linarith [boundaryCoefficientLe, boundaryNonnegative]
    positivity
  rw [ENNReal.ofReal_mul coefficientNonnegative,
    ENNReal.ofReal_pow envelopeNonnegative] at converted
  simpa only [ENNReal.ofReal_natCast] using converted

theorem threeDegreeBinProduct_le_logCube_of_fineLog
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}
    {logCoefficient : ℝ}
    (deltaLeOne : delta ≤ 1)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹)) :
    (bins.fineCellBin.binCount : ENNReal) *
        bins.parentCoarseBin.binCount *
        bins.coarseCellBin.binCount ≤
      8 *
        (ENNReal.ofReal
          (fineLogEnvelopeCoefficient logCoefficient *
            (1 + Real.log delta⁻¹))) ^ 3 := by
  let edgeLog := Nat.log 2 exactification.incidence.allEdges.card + 1
  let envelope : ENNReal :=
    ENNReal.ofReal
      (fineLogEnvelopeCoefficient logCoefficient *
        (1 + Real.log delta⁻¹))
  have edgeLogReal :
      (edgeLog : ℝ) ≤
        2 * fineLogEnvelopeCoefficient logCoefficient *
          (1 + Real.log delta⁻¹) := by
    simpa only [edgeLog, Nat.cast_add, Nat.cast_one] using
      input.allEdgesLog_le_fineLogEnvelope
        multiplicity parentClass treeCleanup exactification
          deltaLeOne boundaryCoefficientLe fineLogBound
  have edgeLogENN : (edgeLog : ENNReal) ≤ 2 * envelope := by
    have converted := ENNReal.ofReal_mono edgeLogReal
    rw [show
      ENNReal.ofReal
          (2 * fineLogEnvelopeCoefficient logCoefficient *
            (1 + Real.log delta⁻¹)) =
        2 * envelope by
          dsimp only [envelope]
          rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring] at converted
    simpa only [ENNReal.ofReal_natCast] using converted
  have fineBin :
      bins.fineCellBin.binCount ≤ edgeLog := by
    rw [bins.fineCellBin.binCount_eq]
  have parentCoarseBin :
      bins.parentCoarseBin.binCount ≤ edgeLog := by
    rw [bins.parentCoarseBin.binCount_eq]
    apply Nat.add_le_add_right
    apply Nat.log_mono_right
    exact Finset.card_le_card bins.fineCellBin.selectedEdges_subset
  have coarseCellBin :
      bins.coarseCellBin.binCount ≤ edgeLog := by
    rw [bins.coarseCellBin.binCount_eq]
    apply Nat.add_le_add_right
    apply Nat.log_mono_right
    exact Finset.card_le_card <|
      bins.parentCoarseBin.selectedEdges_subset.trans
        bins.fineCellBin.selectedEdges_subset
  have fineBinENN :
      (bins.fineCellBin.binCount : ENNReal) ≤ edgeLog := by
    exact_mod_cast fineBin
  have parentCoarseBinENN :
      (bins.parentCoarseBin.binCount : ENNReal) ≤ edgeLog := by
    exact_mod_cast parentCoarseBin
  have coarseCellBinENN :
      (bins.coarseCellBin.binCount : ENNReal) ≤ edgeLog := by
    exact_mod_cast coarseCellBin
  calc
    (bins.fineCellBin.binCount : ENNReal) *
          bins.parentCoarseBin.binCount *
          bins.coarseCellBin.binCount ≤
        (edgeLog : ENNReal) * edgeLog * edgeLog := by
      gcongr
    _ = (edgeLog : ENNReal) ^ 3 := by ring
    _ ≤ (2 * envelope) ^ 3 := by gcongr
    _ = 8 * envelope ^ 3 := by ring
    _ = _ := rfl

def prebalanceTailCoefficientOfFineLog
    (depthBound : ℕ) (logCoefficient : ℝ) : ℝ :=
  40 *
    (8 * (depthBound + 2) * 8 ^ 4) ^ 3 *
    (fineLogEnvelopeCoefficient logCoefficient) ^ 13

theorem prebalanceTailCoefficientOfFineLog_pos
    (depthBound : ℕ)
    {logCoefficient : ℝ}
    (logCoefficientOne : 1 ≤ logCoefficient) :
    0 < prebalanceTailCoefficientOfFineLog
      depthBound logCoefficient := by
  unfold prebalanceTailCoefficientOfFineLog
  have coefficientPos :
      0 < fineLogEnvelopeCoefficient logCoefficient :=
    zero_lt_one.trans_le <|
      fineLogEnvelopeCoefficient_one_le logCoefficientOne
  positivity

structure PrebalanceSmallDataOfFineLog
    (delta : ℝ)
    (depthBound : ℕ)
    (densityExponent lossExponent logCoefficient : ℝ) : Prop where
  delta_lt_one : delta < 1
  loss_bound :
    (128 : ENNReal) *
        (ENNReal.ofReal
          (fineLogEnvelopeCoefficient logCoefficient *
            (1 + Real.log delta⁻¹))) ^ 3 ≤
      Kakeya.realRpowENN delta (-lossExponent)
  tail_bound :
    prebalanceTailCoefficientOfFineLog depthBound logCoefficient *
        (1 + Real.log delta⁻¹) ^ 13 ≤
      Real.rpow delta
        (-((1 - (densityExponent + lossExponent)) / 2))

theorem exists_prebalanceSmallThresholdOfFineLog
    (depthBound : ℕ)
    (densityExponent lossExponent logCoefficient : ℝ)
    (lossExponentPos : 0 < lossExponent)
    (exponentGap : densityExponent + lossExponent < 1)
    (logCoefficientOne : 1 ≤ logCoefficient) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₀ →
          PrebalanceSmallDataOfFineLog
            delta depthBound densityExponent lossExponent
              logCoefficient := by
  have envelopeOne :
      (1 : ℝ) ≤ fineLogEnvelopeCoefficient logCoefficient :=
    fineLogEnvelopeCoefficient_one_le logCoefficientOne
  rcases
      exists_delta_C_pow_log_absorbed_ennreal
        128 (by norm_num)
        (fineLogEnvelopeCoefficient logCoefficient)
        (zero_le_one.trans envelopeOne)
        lossExponentPos (n := 3) (by norm_num)
    with ⟨lossThreshold, lossThresholdPos, lossThresholdLeOne,
      lossBound⟩
  let gap : ℝ := 1 - (densityExponent + lossExponent)
  have gapHalfPos : 0 < gap / 2 := by
    dsimp only [gap]
    linarith
  rcases
      exists_delta_log_absorbed
        (prebalanceTailCoefficientOfFineLog depthBound logCoefficient)
        (prebalanceTailCoefficientOfFineLog_pos
          depthBound logCoefficientOne)
        gapHalfPos (n := 13) (by norm_num)
    with ⟨tailThreshold, tailThresholdPos, tailThresholdLeOne,
      tailBound⟩
  let delta₀ := min (min lossThreshold tailThreshold) (1 / 2 : ℝ)
  refine
    ⟨delta₀, lt_min (lt_min lossThresholdPos tailThresholdPos) (by norm_num),
      (min_le_right _ _).trans (by norm_num), ?_⟩
  intro delta deltaPos deltaLe
  exact
    {
      delta_lt_one :=
        deltaLe.trans_lt <| (min_le_right _ _).trans_lt (by norm_num)
      loss_bound :=
        lossBound delta deltaPos <|
          deltaLe.trans <| (min_le_left _ _).trans (min_le_left _ _)
      tail_bound := by
        simpa only [gap] using
          tailBound delta deltaPos <|
            deltaLe.trans <| (min_le_left _ _).trans (min_le_right _ _)
    }

noncomputable def prebalanceSmallThresholdOfFineLog
    (depthBound : ℕ)
    (densityExponent lossExponent logCoefficient : ℝ)
    (lossExponentPos : 0 < lossExponent)
    (exponentGap : densityExponent + lossExponent < 1)
    (logCoefficientOne : 1 ≤ logCoefficient) : ℝ :=
  Classical.choose <|
    exists_prebalanceSmallThresholdOfFineLog
      depthBound densityExponent lossExponent logCoefficient
        lossExponentPos exponentGap logCoefficientOne

theorem prebalanceSmallDataOfFineLog_of_smallDelta
    (depthBound : ℕ)
    (densityExponent lossExponent logCoefficient : ℝ)
    (lossExponentPos : 0 < lossExponent)
    (exponentGap : densityExponent + lossExponent < 1)
    (logCoefficientOne : 1 ≤ logCoefficient)
    (deltaPos : 0 < delta)
    (deltaLe :
      delta ≤
        prebalanceSmallThresholdOfFineLog
          depthBound densityExponent lossExponent logCoefficient
            lossExponentPos exponentGap logCoefficientOne) :
    PrebalanceSmallDataOfFineLog
      delta depthBound densityExponent lossExponent logCoefficient :=
  (Classical.choose_spec <|
    exists_prebalanceSmallThresholdOfFineLog
      depthBound densityExponent lossExponent logCoefficient
        lossExponentPos exponentGap logCoefficientOne).2.2
    delta deltaPos deltaLe

theorem canonical_scaled_referenceDegree_lt_of_fineLog
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup exactification parentDegree bins
          (input.canonicalPeelingA0
            multiplicity parentClass treeCleanup exactification bins))
    (depthBound : ℕ)
    (densityExponent lossExponent logCoefficient : ℝ)
    (small :
      PrebalanceSmallDataOfFineLog
        delta depthBound densityExponent lossExponent logCoefficient)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹))
    (depthLe : schedule.levelCount ≤ depthBound)
    (exponentGap : densityExponent + lossExponent < 1)
    (density :
      Kakeya.realRpowENN delta densityExponent *
          fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass) :
    (40 : ℝ) *
          (input.canonicalPeelingA0
            multiplicity parentClass treeCleanup exactification bins : ℝ) ^ 3 *
          Real.log (coarse.card : ℝ) <
      (parentDegree.K : ℝ) := by
  let A0 :=
    input.canonicalPeelingA0
      multiplicity parentClass treeCleanup exactification bins
  let logEnvelope : ℝ :=
    fineLogEnvelopeCoefficient logCoefficient *
      (1 + Real.log delta⁻¹)
  let depthCoefficient : ℝ :=
    8 * (depthBound + 2) * 8 ^ 4
  let gap : ℝ := 1 - (densityExponent + lossExponent)
  have deltaLeOne : delta ≤ 1 := small.delta_lt_one.le
  have preLoss :
      input.prebalanceParentDegreeLoss multiplicity parentClass ≤
        Kakeya.realRpowENN delta (-lossExponent) :=
    (input.prebalanceParentDegreeLoss_le_logCube_of_fineLog
      multiplicity parentClass deltaLeOne boundaryCoefficientLe
        fineLogBound).trans small.loss_bound
  have degreeFloorENN :
      Kakeya.realRpowENN delta
          (densityExponent + lossExponent - 1) ≤
        (parentDegree.K : ENNReal) :=
    input.referenceParentDegree_power_floor
      multiplicity parentClass treeCleanup exactification parentDegree
      densityExponent lossExponent density preLoss
  have degreeFloorReal :
      Real.rpow delta
          (densityExponent + lossExponent - 1) ≤
        (parentDegree.K : ℝ) := by
    have converted :=
      (ENNReal.toReal_le_toReal
        (by simp [Kakeya.realRpowENN])
        (ENNReal.natCast_ne_top parentDegree.K)).mpr degreeFloorENN
    simpa [Kakeya.realRpowENN,
      ENNReal.toReal_ofReal (Real.rpow_nonneg input.delta_pos.le _)] using
      converted
  have A0Bound :
      (A0 : ℝ) ≤ depthCoefficient * logEnvelope ^ 4 := by
    have raw :=
      input.canonicalPeelingA0_le_logFourth
        multiplicity parentClass treeCleanup exactification
          (bins := bins) depthBound depthLe
    have edgeLog :=
      input.allEdgesLog_le_fineLogEnvelope
        multiplicity parentClass treeCleanup exactification
          deltaLeOne boundaryCoefficientLe fineLogBound
    calc
      (A0 : ℝ) ≤
          (8 * (depthBound + 2) * 4 ^ 4 : ℝ) *
            (Nat.log 2 exactification.incidence.allEdges.card + 1 : ℝ) ^ 4 :=
        raw
      _ ≤
          (8 * (depthBound + 2) * 4 ^ 4 : ℝ) *
            (2 * logEnvelope) ^ 4 := by
        gcongr
        dsimp only [logEnvelope]
        nlinarith [edgeLog]
      _ = depthCoefficient * logEnvelope ^ 4 := by
        dsimp only [depthCoefficient]
        ring
  have coarseLog :
      Real.log (coarse.card : ℝ) < logEnvelope := by
    have coarsePos : 0 < coarse.card := by
      let source : Fin fine.card := ⟨0, by
        rcases input.fineCells_nonempty with ⟨cell, cellMem⟩
        have cellActive :
            cell ∈ wz1PaperActiveCells shading input.delta_pos := by
          rw [← input.fineCells_eq]
          exact cellMem
        rcases
            ((mem_wz1PaperActiveCells
              shading input.delta_pos cell).mp cellActive).2
          with ⟨point, ⟨source, _pointMem⟩, _pointCell⟩
        exact Nat.zero_lt_of_lt source.isLt⟩
      rcases cover.covers source with ⟨parent, _⟩
      exact Nat.zero_lt_of_lt parent.isLt
    exact
      (realLog_card_lt_dyadicLog coarse.card coarsePos).trans_le <| by
        simpa only [logEnvelope] using
          coarseLog_le_fineLogEnvelope
            cover input.delta_pos fineLogBound deltaLeOne
  have A0PosReal : (0 : ℝ) < A0 := by
    exact_mod_cast
      input.canonicalPeelingA0_pos
        multiplicity parentClass treeCleanup exactification bins
  have logEnvelopePos : 0 < logEnvelope := by
    have logNonnegative : 0 ≤ Real.log delta⁻¹ := by
      apply Real.log_nonneg
      exact (one_le_inv₀ input.delta_pos).mpr deltaLeOne
    have coefficientPos :
        0 < fineLogEnvelopeCoefficient logCoefficient := by
      unfold fineLogEnvelopeCoefficient
      have boundaryNonnegative :
          0 ≤ wz2PaperBoundaryLogCoefficient := by
        unfold wz2PaperBoundaryLogCoefficient
        positivity
      linarith [boundaryCoefficientLe, boundaryNonnegative]
    dsimp only [logEnvelope]
    positivity
  have scaledUpper :
      (40 : ℝ) * (A0 : ℝ) ^ 3 *
          Real.log (coarse.card : ℝ) <
        (40 * depthCoefficient ^ 3 *
          (fineLogEnvelopeCoefficient logCoefficient) ^ 13) *
          (1 + Real.log delta⁻¹) ^ 13 := by
    calc
      (40 : ℝ) * (A0 : ℝ) ^ 3 *
            Real.log (coarse.card : ℝ) <
          40 * (A0 : ℝ) ^ 3 * logEnvelope := by
        gcongr
      _ ≤
          40 * (depthCoefficient * logEnvelope ^ 4) ^ 3 *
            logEnvelope := by
        gcongr
      _ =
          (40 * depthCoefficient ^ 3 *
            (fineLogEnvelopeCoefficient logCoefficient) ^ 13) *
            (1 + Real.log delta⁻¹) ^ 13 := by
        dsimp only [logEnvelope]
        ring
  have gapPos : 0 < gap := by
    dsimp only [gap]
    linarith [exponentGap]
  have strictPower :
      Real.rpow delta (-(gap / 2)) <
        Real.rpow delta (-gap) :=
    Real.rpow_lt_rpow_of_exponent_gt
      input.delta_pos small.delta_lt_one (by linarith)
  have exponentEq :
      densityExponent + lossExponent - 1 = -gap := by
    dsimp only [gap]
    ring
  calc
    (40 : ℝ) * (A0 : ℝ) ^ 3 *
          Real.log (coarse.card : ℝ) <
        (40 * depthCoefficient ^ 3 *
          (fineLogEnvelopeCoefficient logCoefficient) ^ 13) *
          (1 + Real.log delta⁻¹) ^ 13 :=
      scaledUpper
    _ ≤
        Real.rpow delta
          (-((1 - (densityExponent + lossExponent)) / 2)) := by
      simpa only [prebalanceTailCoefficientOfFineLog] using small.tail_bound
    _ = Real.rpow delta (-(gap / 2)) := by rfl
    _ < Real.rpow delta (-gap) := strictPower
    _ = Real.rpow delta
          (densityExponent + lossExponent - 1) := by rw [exponentEq]
    _ ≤ (parentDegree.K : ℝ) := degreeFloorReal

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
