import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9PreliminaryM8Schedule

/-!
# Family-free cutoffs for the preliminary M7/M8 iteration

The preliminary plane map is one-Lipschitz.  Consequently every four-call
coefficient in the first grain-structure iteration is fixed before the
runtime family is chosen.  This file collects the remaining finite root,
query, pair, and terminal thresholds without referring to a shading.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- One coordinate's root and paper-four-call thresholds at coefficient one. -/
structure Proposition63M9PreliminaryCoordinateCutoffData
    {sigma producerLoss localLoss nextSourceLoss : ℝ}
    (preliminary : Proposition63M9PreliminaryM8ScheduleData
      sigma producerLoss localLoss)
    (losses : Proposition63M9PreliminaryRootLossData
      preliminary nextSourceLoss)
    (index : ℕ)
    (hindex : index < preliminary.schedule.centralTemplate.count) where
  rootCutoff : ℝ
  rootCutoff_pos : 0 < rootCutoff
  rootCutoff_le_one : rootCutoff ≤ 1
  root_density : ∀ {delta : ℝ}, 0 < delta → delta ≤ rootCutoff →
    Kakeya.realRpowENN delta
        (Proposition63FourCallInnerBackwardLossSchedule.rootDensityLoss
          (preliminary.schedule.outer.oneQuery index hindex).backward) ≤
      Kakeya.realRpowENN delta
        (preliminary.schedule.outer.oneQuery index hindex).rootSourceLoss / 2
  paper : Proposition63FourCallPaperGlobalCutoffData
    (inputLoss :=
      (preliminary.schedule.outer.oneQuery index hindex).rootSourceLoss)
    (preliminary.schedule.outer.oneQuery index hindex).backward 1
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_root : delta₀ ≤ rootCutoff
  delta₀_le_grid : delta₀ ≤
    (preliminary.schedule.outer.oneQuery index hindex).gridSchedule.delta₀
  delta₀_le_paperFine : delta₀ ≤ paper.deltaCommon.delta₀
  query_amplified : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    let queryLoss := preliminary.schedule.outer.loss (index + 1)
    let discreteLoss :=
      (preliminary.schedule.outer.oneQuery index hindex).gridSchedule.discreteLoss
    (64 * (lipschitzExtensionConstant Point3 : ℝ)) *
        Real.rpow delta (queryLoss * discreteLoss / 2) ≤ 1
  query_quarter : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    Real.rpow delta (preliminary.schedule.outer.loss (index + 1)) ≤ 1 / 4
  pair_scale : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    2 * Real.rpow delta
        (preliminary.schedule.outer.loss (index + 1) / 2) ≤
      min paper.rhoCommon.delta₀ (1 / 144)
  first_output_gap : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    ∀ pairIndex (hpair : pairIndex <
      (finiteIntervalOrderedPairs
        (preliminary.schedule.outer.oneQuery index hindex).gridSchedule.gridN).length),
      Real.rpow delta
        ((preliminary.schedule.outer.oneQuery index hindex).gridSchedule.discreteLoss -
          ((preliminary.schedule.outer.oneQuery index hindex).backward.seed
            pairIndex hpair).schedule.firstOutputLoss) ≤ 1 / 2

/-- Select all family-free cutoffs for one preliminary M7 coordinate. -/
theorem proposition63_m9_preliminary_coordinate_cutoff
    {sigma producerLoss localLoss nextSourceLoss : ℝ}
    (preliminary : Proposition63M9PreliminaryM8ScheduleData
      sigma producerLoss localLoss)
    (losses : Proposition63M9PreliminaryRootLossData
      preliminary nextSourceLoss)
    (index : ℕ)
    (hindex : index < preliminary.schedule.centralTemplate.count) :
    Nonempty (Proposition63M9PreliminaryCoordinateCutoffData
      preliminary losses index hindex) := by
  let oneQuery := preliminary.schedule.outer.oneQuery index hindex
  have sourceDensityGap : oneQuery.rootSourceLoss <
      oneQuery.backward.rootDensityLoss := by
    dsimp only [oneQuery, Proposition63Lemma411ScheduleData.rootSourceLoss,
      Proposition63FourCallInnerBackwardLossSchedule.rootDensityLoss,
      Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss]
    linarith [oneQuery.backward.rootBudget_pos]
  rcases proposition63_four_call_paper_global_cutoff oneQuery.backward 1
      sourceDensityGap with ⟨paper⟩
  have rootGap : 0 < oneQuery.backward.rootDensityLoss -
      oneQuery.rootSourceLoss := by
    dsimp only [oneQuery, Proposition63Lemma411ScheduleData.rootSourceLoss,
      Proposition63FourCallInnerBackwardLossSchedule.rootDensityLoss,
      Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss]
    linarith [oneQuery.backward.rootBudget_pos]
  rcases exists_delta_realRpowENN_bound (2 : ENNReal) (by norm_num) rootGap with
    ⟨rootCutoff, rootCutoffPos, rootCutoffOne, rootBound⟩
  let amplifiedConstant : ℝ :=
    64 * (lipschitzExtensionConstant Point3 : ℝ)
  have amplifiedConstantPos : 0 < amplifiedConstant := by
    dsimp only [amplifiedConstant]
    exact mul_pos (by norm_num) (by
      simp [lipschitzExtensionConstant])
  have queryExponentPos : 0 <
      preliminary.schedule.outer.loss (index + 1) *
        oneQuery.gridSchedule.discreteLoss / 2 := by
    exact div_pos (mul_pos
      (preliminary.schedule.outer.loss_pos (index + 1) (by omega))
      oneQuery.gridSchedule.discrete_loss_pos) (by norm_num)
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := 1 / amplifiedConstant)
      (s := preliminary.schedule.outer.loss (index + 1) *
        oneQuery.gridSchedule.discreteLoss / 2)
      (one_div_pos.mpr amplifiedConstantPos) queryExponentPos with
    ⟨queryAmplifiedCutoff, queryAmplifiedPos, queryAmplifiedOne,
      queryAmplifiedBound⟩
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := (1 / 4 : ℝ))
      (s := preliminary.schedule.outer.loss (index + 1)) (by norm_num)
      (preliminary.schedule.outer.loss_pos (index + 1) (by omega)) with
    ⟨queryQuarterCutoff, queryQuarterPos, queryQuarterOne, queryQuarterBound⟩
  let pairTarget : ℝ := min paper.rhoCommon.delta₀ (1 / 144) / 2
  have pairTargetPos : 0 < pairTarget := by
    dsimp only [pairTarget]
    exact div_pos (lt_min paper.rhoCommon.delta₀_pos (by norm_num))
      (by norm_num)
  rcases pure_wz2_exists_delta₀_rpow_le (threshold := pairTarget)
      (s := preliminary.schedule.outer.loss (index + 1) / 2) pairTargetPos
      (half_pos (preliminary.schedule.outer.loss_pos (index + 1) (by omega)))
    with ⟨pairScaleCutoff, pairScalePos, pairScaleOne, pairScaleBound⟩
  let PairIndex := Fin
    (finiteIntervalOrderedPairs oneQuery.gridSchedule.gridN).length
  have pairExponentPos : ∀ pair : PairIndex, 0 <
      oneQuery.gridSchedule.discreteLoss -
        (oneQuery.backward.seed pair.val pair.isLt).schedule.firstOutputLoss := by
    intro pair
    rw [sub_pos]
    let seed := oneQuery.backward.seed pair.val pair.isLt
    change seed.schedule.firstOutputLoss < oneQuery.gridSchedule.discreteLoss
    calc
      seed.schedule.firstOutputLoss < seed.schedule.second.sourceLoss :=
        seed.schedule.firstOutputLoss_lt_secondSource
      _ ≤ seed.schedule.second.normalizationLoss / 2 :=
        seed.schedule.second.sourceLoss_le_half
      _ < seed.schedule.second.normalizationLoss :=
        half_lt_self seed.schedule.second.normalizationLoss_pos
      _ < seed.schedule.secondOutputLoss :=
        seed.schedule.second.normalizationLoss_lt_output
      _ ≤ oneQuery.gridSchedule.discreteLoss :=
        seed.secondOutputLoss_le_discrete
  let pairGapCutoff : PairIndex → ℝ := fun pair => Classical.choose <|
    pure_wz2_exists_delta₀_rpow_le (threshold := (1 / 2 : ℝ))
      (by norm_num) (pairExponentPos pair)
  have pairGapPos : ∀ pair, 0 < pairGapCutoff pair := by
    intro pair
    exact (Classical.choose_spec <| pure_wz2_exists_delta₀_rpow_le
      (threshold := (1 / 2 : ℝ))
      (by norm_num) (pairExponentPos pair)).1
  rcases proposition63_finite_positive_cutoff
      (finiteIntervalOrderedPairs oneQuery.gridSchedule.gridN).length
      (fun pairIndex hpair => pairGapCutoff ⟨pairIndex, hpair⟩)
      (fun pairIndex hpair => pairGapPos ⟨pairIndex, hpair⟩) with
    ⟨pairGapCommon⟩
  let delta₀ := min rootCutoff <| min oneQuery.gridSchedule.delta₀ <|
    min paper.deltaCommon.delta₀ <| min queryAmplifiedCutoff <|
      min queryQuarterCutoff <| min pairScaleCutoff pairGapCommon.delta₀
  refine ⟨{
    rootCutoff := rootCutoff
    rootCutoff_pos := rootCutoffPos
    rootCutoff_le_one := rootCutoffOne
    root_density := by
      intro delta deltaPos deltaLe
      apply (ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).2
      calc
        Kakeya.realRpowENN delta oneQuery.backward.rootDensityLoss * 2 =
            2 * Kakeya.realRpowENN delta
              oneQuery.backward.rootDensityLoss := by ring
        _ ≤ Kakeya.realRpowENN delta
              (-(oneQuery.backward.rootDensityLoss - oneQuery.rootSourceLoss)) *
            Kakeya.realRpowENN delta oneQuery.backward.rootDensityLoss := by
          gcongr
          exact rootBound delta deltaPos
            (deltaLe.trans <| by simp [delta₀])
        _ = Kakeya.realRpowENN delta oneQuery.rootSourceLoss := by
          rw [← realRpowENN_add deltaPos]
          congr 1
          ring
    paper := paper
    delta₀ := delta₀
    delta₀_pos := lt_min rootCutoffPos <| lt_min oneQuery.gridSchedule.delta₀_pos <|
      lt_min paper.deltaCommon.delta₀_pos <| lt_min queryAmplifiedPos <|
        lt_min queryQuarterPos <| lt_min pairScalePos pairGapCommon.delta₀_pos
    delta₀_le_one := (min_le_left _ _).trans rootCutoffOne
    delta₀_le_root := min_le_left _ _
    delta₀_le_grid := (min_le_right _ _).trans (min_le_left _ _)
    delta₀_le_paperFine := (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
    query_amplified := by
      intro delta deltaPos deltaLe
      dsimp only [amplifiedConstant] at queryAmplifiedBound ⊢
      have bound := queryAmplifiedBound delta deltaPos <|
        deltaLe.trans <| by simp [delta₀]
      rw [le_div_iff₀ amplifiedConstantPos] at bound
      simpa [oneQuery, mul_comm] using bound
    query_quarter := by
      intro delta deltaPos deltaLe
      exact queryQuarterBound delta deltaPos <| deltaLe.trans <| by
        simp [delta₀]
    pair_scale := by
      intro delta deltaPos deltaLe
      have bound := pairScaleBound delta deltaPos <| deltaLe.trans <| by
        simp [delta₀]
      dsimp only [pairTarget] at bound ⊢
      linarith
    first_output_gap := by
      intro delta deltaPos deltaLe pairIndex hpair
      let pair : PairIndex := ⟨pairIndex, hpair⟩
      have spec := Classical.choose_spec <| pure_wz2_exists_delta₀_rpow_le
        (threshold := (1 / 2 : ℝ))
        (by norm_num) (pairExponentPos pair)
      have deltaCommon : delta ≤ pairGapCommon.delta₀ :=
        deltaLe.trans <| by simp [delta₀]
      have deltaPair : delta ≤ pairGapCutoff pair :=
        deltaCommon.trans (pairGapCommon.le_threshold pairIndex hpair)
      simpa only [pair] using spec.2.2 delta deltaPos deltaPair
  }⟩

/-- The finite common cutoff for every coordinate of the preliminary
grain-structure iteration. -/
structure Proposition63M9PreliminaryOuterCutoffData
    {sigma producerLoss localLoss nextSourceLoss : ℝ}
    (preliminary : Proposition63M9PreliminaryM8ScheduleData
      sigma producerLoss localLoss)
    (losses : Proposition63M9PreliminaryRootLossData
      preliminary nextSourceLoss) where
  coordinate : ∀ index
    (hindex : index < preliminary.schedule.centralTemplate.count),
      Proposition63M9PreliminaryCoordinateCutoffData
        preliminary losses index hindex
  common : Proposition63FinitePositiveCutoff
    preliminary.schedule.centralTemplate.count
    (fun index hindex => (coordinate index hindex).delta₀)
  gridDensityCutoff : ℝ
  gridDensityCutoff_pos : 0 < gridDensityCutoff
  delta₀ : ℝ
  delta₀_eq : delta₀ = min preliminary.delta₀
    (min losses.currentAbsorption.delta₀
      (min gridDensityCutoff common.delta₀))
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_terminal : delta₀ ≤ preliminary.delta₀
  delta₀_le_currentReentry : delta₀ ≤ losses.currentAbsorption.delta₀
  grid_density : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    Kakeya.realRpowENN delta preliminary.gridLoss ≤
      Kakeya.realRpowENN delta losses.reentryLoss / 2
  delta₀_le_coordinate : ∀ index
    (hindex : index < preliminary.schedule.centralTemplate.count),
      delta₀ ≤ (coordinate index hindex).delta₀

/-- Aggregate all preliminary M7 coordinate cutoffs before the runtime scale
and family are selected. -/
theorem proposition63_m9_preliminary_outer_cutoff
    {sigma producerLoss localLoss nextSourceLoss : ℝ}
    (preliminary : Proposition63M9PreliminaryM8ScheduleData
      sigma producerLoss localLoss)
    (losses : Proposition63M9PreliminaryRootLossData
      preliminary nextSourceLoss) :
    Nonempty (Proposition63M9PreliminaryOuterCutoffData
      preliminary losses) := by
  let coordinate : ∀ index
      (hindex : index < preliminary.schedule.centralTemplate.count),
      Proposition63M9PreliminaryCoordinateCutoffData
        preliminary losses index hindex :=
    fun index hindex => Classical.choice <|
      proposition63_m9_preliminary_coordinate_cutoff
        preliminary losses index hindex
  rcases proposition63_finite_positive_cutoff
      preliminary.schedule.centralTemplate.count
      (fun index hindex => (coordinate index hindex).delta₀)
      (fun index hindex => (coordinate index hindex).delta₀_pos) with
    ⟨common⟩
  have gridGap : 0 < preliminary.gridLoss - losses.reentryLoss := by
    linarith [losses.reentry_lt_grid]
  rcases exists_delta_realRpowENN_bound (2 : ENNReal) (by norm_num) gridGap with
    ⟨gridDensityCutoff, gridDensityCutoffPos, _gridDensityCutoffOne,
      gridDensityBound⟩
  let delta₀ := min preliminary.delta₀ <|
    min losses.currentAbsorption.delta₀ <|
      min gridDensityCutoff common.delta₀
  exact ⟨{
    coordinate := coordinate
    common := common
    gridDensityCutoff := gridDensityCutoff
    gridDensityCutoff_pos := gridDensityCutoffPos
    delta₀ := delta₀
    delta₀_eq := rfl
    delta₀_pos := lt_min preliminary.delta₀_pos <|
      lt_min losses.currentAbsorption.delta₀_pos <|
        lt_min gridDensityCutoffPos common.delta₀_pos
    delta₀_le_one := (min_le_left _ _).trans preliminary.delta₀_le_one
    delta₀_le_terminal := min_le_left _ _
    delta₀_le_currentReentry := (min_le_right _ _).trans (min_le_left _ _)
    grid_density := by
      intro runtimeDelta runtimeDeltaPos runtimeDeltaLe
      apply (ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).2
      calc
        Kakeya.realRpowENN runtimeDelta preliminary.gridLoss * 2 =
            2 * Kakeya.realRpowENN runtimeDelta preliminary.gridLoss := by ring
        _ ≤ Kakeya.realRpowENN runtimeDelta
              (-(preliminary.gridLoss - losses.reentryLoss)) *
            Kakeya.realRpowENN runtimeDelta preliminary.gridLoss := by
          gcongr
          exact gridDensityBound runtimeDelta runtimeDeltaPos
            (runtimeDeltaLe.trans <| by simp [delta₀])
        _ = Kakeya.realRpowENN runtimeDelta losses.reentryLoss := by
          rw [← realRpowENN_add runtimeDeltaPos]
          congr 1
          ring
    delta₀_le_coordinate := by
      intro index hindex
      exact (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (common.le_threshold index hindex)
  }⟩

/-- Materialize the complete preliminary outer binding on one canonical
ambient re-entry.  No current shading occurs in this construction. -/
noncomputable def Proposition63M9PreliminaryOuterCutoffData.outerBindingInputs
    {sigma producerLoss localLoss nextSourceLoss delta ambientSourceLoss
      ambientNormalizationLoss : ℝ}
    {preliminary : Proposition63M9PreliminaryM8ScheduleData
      sigma producerLoss localLoss}
    {losses : Proposition63M9PreliminaryRootLossData
      preliminary nextSourceLoss}
    (cutoff : Proposition63M9PreliminaryOuterCutoffData preliminary losses)
    {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {normalizationExponent : ℕ}
    (ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) ambientShading normalizationExponent
        ambientSourceLoss ambientNormalizationLoss)
    (ambientSource_le : ambientSourceLoss ≤ losses.reentryLoss)
    (ambientNormalization_le :
      ambientNormalizationLoss ≤ losses.reentryNormalizationLoss)
    (deltaPos : 0 < delta) (deltaLe : delta ≤ cutoff.delta₀) (K : ℝ) :
    Proposition63Lemma411OuterBindingInputs (incidence := delta)
      (preliminary.schedule.centralTemplate.rebase delta deltaPos
        (deltaLe.trans cutoff.delta₀_le_one))
      preliminary.schedule.outer
      ambientReentry K 1 preliminary.gridLoss_le_mid := by
  let central := preliminary.schedule.centralTemplate.rebase delta deltaPos
    (deltaLe.trans cutoff.delta₀_le_one)
  let outer := preliminary.schedule.outer
  let rootBinding : ∀ outerIndex
      (houter : outerIndex < central.count),
      Proposition63Lemma411OuterRootBindingData
        (outer.oneQuery outerIndex houter) ambientReentry := by
    intro outerIndex houter
    have houterTemplate :
        outerIndex < preliminary.schedule.centralTemplate.count := by
      simpa only [central, Proposition63Lemma412CentralGridData.rebase_count]
        using houter
    let coordinate := cutoff.coordinate outerIndex houterTemplate
    refine {
      ambient_source_le := ?_
      ambient_normalization_le := ?_
      density_absorb := ?_
    }
    · simpa only [outer] using
        ambientSource_le.trans
          (losses.reentry_le_rootSource outerIndex houterTemplate)
    · simpa only [outer] using
        ambientNormalization_le.trans
          (losses.reentryNormalization_le_rootNormalization
            outerIndex houterTemplate)
    · simpa only [outer, coordinate] using
        coordinate.root_density deltaPos
          ((deltaLe.trans <| cutoff.delta₀_le_coordinate
            outerIndex houterTemplate).trans coordinate.delta₀_le_root)
  refine {
    rootBinding := rootBinding
    delta_le_grid := ?_
    smallness := ?_
  }
  · intro outerIndex houter
    exact deltaLe.trans (cutoff.delta₀_le_coordinate outerIndex houter)
      |>.trans (cutoff.coordinate outerIndex houter).delta₀_le_grid
  · intro outerIndex houter
    have houterTemplate :
        outerIndex < preliminary.schedule.centralTemplate.count := by
      simpa only [central, Proposition63Lemma412CentralGridData.rebase_count]
        using houter
    let oneQuery := outer.oneQuery outerIndex houter
    let root := (rootBinding outerIndex houter).root
    let lossLeMid : outer.loss (outerIndex + 1) ≤
        preliminary.midLoss :=
      (outer.loss_le_terminal (outerIndex + 1) (by omega)).trans
        preliminary.gridLoss_le_mid
    let window := central.query_window
      root.normalization.final_extremal.delta_pos
      root.normalization.final_extremal.delta_le_one houter lossLeMid
    let query := central.query outerIndex houter
    let coordinate := cutoff.coordinate outerIndex houterTemplate
    have deltaCoordinate : delta ≤ coordinate.delta₀ :=
      deltaLe.trans (cutoff.delta₀_le_coordinate outerIndex houterTemplate)
    let grid := oneQuery.runtimeGrid query
      root.normalization.final_extremal.delta_pos
      (deltaCoordinate.trans coordinate.delta₀_le_grid) window.1 window.2
    have coefficientOne : 1 ≤
        (((4 : NNReal) * (lipschitzExtensionConstant Point3 * (1 : NNReal))) : ℝ) := by
      have extensionOne : 1 ≤ (lipschitzExtensionConstant Point3 : ℝ) := by
        simp [lipschitzExtensionConstant]
      push_cast
      norm_num
      linarith
    have queryPower : Real.rpow query.1
          (oneQuery.gridSchedule.discreteLoss / 2) ≤
        Real.rpow delta
          (outer.loss (outerIndex + 1) *
            oneQuery.gridSchedule.discreteLoss / 2) := by
      calc
        Real.rpow query.1 (oneQuery.gridSchedule.discreteLoss / 2) ≤
            Real.rpow
              (Real.rpow delta (outer.loss (outerIndex + 1)))
              (oneQuery.gridSchedule.discreteLoss / 2) :=
          Real.rpow_le_rpow (deltaPos.trans_le query.2.1).le window.2
            (div_nonneg oneQuery.gridSchedule.discrete_loss_pos.le
              (by norm_num))
        _ = Real.rpow delta
            (outer.loss (outerIndex + 1) *
              oneQuery.gridSchedule.discreteLoss / 2) := by
          rw [show outer.loss (outerIndex + 1) *
                oneQuery.gridSchedule.discreteLoss / 2 =
              outer.loss (outerIndex + 1) *
                (oneQuery.gridSchedule.discreteLoss / 2) by ring]
          exact (Real.rpow_mul deltaPos.le _ _).symm
    have amplified := coordinate.query_amplified deltaPos deltaCoordinate
    have querySmall : 2 * Real.rpow query.1
        (oneQuery.gridSchedule.discreteLoss / 2) ≤ 1 := by
      have extensionOne : 1 ≤ (lipschitzExtensionConstant Point3 : ℝ) := by
        simp [lipschitzExtensionConstant]
      have coefficientBound :
          (2 : ℝ) ≤ 64 * (lipschitzExtensionConstant Point3 : ℝ) := by
        linarith
      calc
        2 * Real.rpow query.1 (oneQuery.gridSchedule.discreteLoss / 2) ≤
            2 * Real.rpow delta
              (outer.loss (outerIndex + 1) *
                oneQuery.gridSchedule.discreteLoss / 2) := by gcongr
        _ ≤ (64 * (lipschitzExtensionConstant Point3 : ℝ)) *
            Real.rpow delta
              (outer.loss (outerIndex + 1) *
                oneQuery.gridSchedule.discreteLoss / 2) :=
          mul_le_mul_of_nonneg_right coefficientBound
            (Real.rpow_nonneg deltaPos.le _)
        _ ≤ 1 := amplified
    have queryQuarter : query.1 ≤ 1 / 4 :=
      window.2.trans (coordinate.query_quarter deltaPos deltaCoordinate)
    have sqrtQuerySmall : 2 * Real.sqrt query.1 ≤ 1 := by
      have sqrtLe : Real.sqrt query.1 ≤ Real.sqrt (1 / 4 : ℝ) :=
        Real.sqrt_le_sqrt queryQuarter
      norm_num at sqrtLe ⊢
      linarith
    have amplifiedQuerySmall : Real.rpow query.1
        (oneQuery.gridSchedule.discreteLoss / 2) ≤
      1 / (16 * (((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * (1 : NNReal))) : ℝ)) := by
      have denominatorPos : 0 < 64 *
          (lipschitzExtensionConstant Point3 : ℝ) :=
        mul_pos (by norm_num) (by simp [lipschitzExtensionConstant])
      rw [show (16 * (((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * (1 : NNReal))) : ℝ)) =
          64 * (lipschitzExtensionConstant Point3 : ℝ) by
        push_cast
        ring]
      rw [le_div_iff₀ denominatorPos]
      calc
        Real.rpow query.1 (oneQuery.gridSchedule.discreteLoss / 2) *
              (64 * (lipschitzExtensionConstant Point3 : ℝ)) ≤
        Real.rpow delta
                (outer.loss (outerIndex + 1) *
                  oneQuery.gridSchedule.discreteLoss / 2) *
              (64 * (lipschitzExtensionConstant Point3 : ℝ)) :=
          mul_le_mul_of_nonneg_right queryPower denominatorPos.le
        _ = (64 * (lipschitzExtensionConstant Point3 : ℝ)) *
            Real.rpow delta
              (outer.loss (outerIndex + 1) *
                oneQuery.gridSchedule.discreteLoss / 2) := by ring
        _ ≤ 1 := by simpa [oneQuery, outer] using amplified
    let scalar : Proposition63Lemma411ScalarSmallnessData
        (incidence := delta) oneQuery.backward root grid 1 := {
      delta_lt_one := (deltaLe.trans cutoff.delta₀_le_terminal).trans_lt <|
        preliminary.scale_small.trans_lt (by norm_num)
      sigma_pos := oneQuery.sigma_pos
      sigma_lt_one := oneQuery.sigma_lt_one
      discrete_loss_pos := oneQuery.gridSchedule.discrete_loss_pos
      discrete_loss_lt_half := oneQuery.discrete_loss_lt_half
      output_loss_le_half := oneQuery.output_loss_le_half
      coefficient_one := coefficientOne
      query_small := querySmall
      delta_le_query := query.2.1
      sqrt_query_small := sqrtQuerySmall
      amplified_query_small := amplifiedQuerySmall
      incidence_nonneg := deltaPos.le
      incidence_le_delta := le_rfl
      rho_small := by
        intro pairIndex hpair scales
        have logicalTop :
            (grid.scale (finiteIntervalOrderedPair
              oneQuery.gridSchedule.gridN pairIndex).1 : ℝ) ≤
              Real.sqrt query.1 := by
          rw [← grid.scale_top]
          have hk := scales.first_lt_second.le.trans scales.second_le_gridN
          have hmono : ∀ offset : ℕ,
              (finiteIntervalOrderedPair oneQuery.gridSchedule.gridN pairIndex).1 +
                  offset ≤ oneQuery.gridSchedule.gridN →
              (grid.scale (finiteIntervalOrderedPair
                  oneQuery.gridSchedule.gridN pairIndex).1 : ℝ) ≤
                grid.scale
                  ((finiteIntervalOrderedPair
                    oneQuery.gridSchedule.gridN pairIndex).1 + offset) := by
            intro offset
            induction offset with
            | zero => simp
            | succ offset ih =>
                intro hsum
                exact (ih (by omega)).trans (grid.scale_mono _ (by omega))
          have result := hmono (oneQuery.gridSchedule.gridN -
            (finiteIntervalOrderedPair oneQuery.gridSchedule.gridN pairIndex).1)
            (Nat.add_sub_of_le hk).le
          rw [Nat.add_sub_of_le hk] at result
          exact result
        have rhoHatBound : scales.rhoHat.1 ≤ 2 * Real.sqrt query.1 :=
          scales.rhoHat_le_two_logicalR.trans <|
            mul_le_mul_of_nonneg_left logicalTop (by norm_num)
        have sqrtPower : Real.sqrt query.1 ≤
            Real.rpow delta (outer.loss (outerIndex + 1) / 2) := by
          calc
            Real.sqrt query.1 ≤ Real.sqrt
                (Real.rpow delta (outer.loss (outerIndex + 1))) :=
              Real.sqrt_le_sqrt window.2
            _ = Real.rpow delta
                (outer.loss (outerIndex + 1) / 2) := by
              calc
                Real.sqrt (Real.rpow delta (outer.loss (outerIndex + 1))) =
                    Real.rpow (Real.rpow delta
                      (outer.loss (outerIndex + 1))) (1 / 2 : ℝ) :=
                  Real.sqrt_eq_rpow _
                _ = Real.rpow delta
                    (outer.loss (outerIndex + 1) * (1 / 2 : ℝ)) :=
                  (Real.rpow_mul deltaPos.le _ _).symm
                _ = Real.rpow delta
                    (outer.loss (outerIndex + 1) / 2) := by congr 1 <;> ring
        exact rhoHatBound.trans <|
          (mul_le_mul_of_nonneg_left sqrtPower (by norm_num)).trans <|
            (coordinate.pair_scale deltaPos deltaCoordinate).trans
              (min_le_right _ _)
      firstOutput_gap_small := by
        intro pairIndex hpair
        simpa only [coordinate, oneQuery, outer] using
          coordinate.first_output_gap deltaPos deltaCoordinate pairIndex hpair
    }
    exact {
      global := {
        scalar := scalar
        paperCutoff := coordinate.paper.paperCutoff
        firstUniformCutoff := coordinate.paper.firstUniformCutoff
        currentReentryAbsorption :=
          coordinate.paper.currentReentryAbsorption
        finalCandidateLiftAbsorption :=
          coordinate.paper.finalCandidateLiftAbsorption
        rho_le_paper_pair := by
          intro pairIndex hpair scales
          have logicalTop :
              (grid.scale (finiteIntervalOrderedPair
                oneQuery.gridSchedule.gridN pairIndex).1 : ℝ) ≤
                Real.sqrt query.1 := by
            rw [← grid.scale_top]
            have hk := scales.first_lt_second.le.trans scales.second_le_gridN
            have hmono : ∀ offset : ℕ,
                (finiteIntervalOrderedPair oneQuery.gridSchedule.gridN pairIndex).1 +
                    offset ≤ oneQuery.gridSchedule.gridN →
                (grid.scale (finiteIntervalOrderedPair
                    oneQuery.gridSchedule.gridN pairIndex).1 : ℝ) ≤
                  grid.scale
                    ((finiteIntervalOrderedPair
                      oneQuery.gridSchedule.gridN pairIndex).1 + offset) := by
              intro offset
              induction offset with
              | zero => simp
              | succ offset ih =>
                  intro hsum
                  exact (ih (by omega)).trans (grid.scale_mono _ (by omega))
            have result := hmono (oneQuery.gridSchedule.gridN -
              (finiteIntervalOrderedPair oneQuery.gridSchedule.gridN pairIndex).1)
              (Nat.add_sub_of_le hk).le
            rw [Nat.add_sub_of_le hk] at result
            exact result
          have rhoHatBound : scales.rhoHat.1 ≤ 2 * Real.sqrt query.1 :=
            scales.rhoHat_le_two_logicalR.trans <|
              mul_le_mul_of_nonneg_left logicalTop (by norm_num)
          exact rhoHatBound.trans <|
            (mul_le_mul_of_nonneg_left (by
              calc
                Real.sqrt query.1 ≤ Real.sqrt
                    (Real.rpow delta
                      (outer.loss (outerIndex + 1))) :=
                  Real.sqrt_le_sqrt window.2
                _ = Real.rpow delta
                    (outer.loss (outerIndex + 1) / 2) := by
                  calc
                    Real.sqrt (Real.rpow delta
                        (outer.loss (outerIndex + 1))) =
                        Real.rpow (Real.rpow delta
                          (outer.loss (outerIndex + 1))) (1 / 2 : ℝ) :=
                      Real.sqrt_eq_rpow _
                    _ = Real.rpow delta
                        (outer.loss (outerIndex + 1) * (1 / 2 : ℝ)) :=
                      (Real.rpow_mul deltaPos.le _ _).symm
                    _ = Real.rpow delta
                        (outer.loss (outerIndex + 1) / 2) := by congr 1 <;> ring)
              (by norm_num)).trans <|
              (coordinate.pair_scale deltaPos deltaCoordinate).trans <|
                (min_le_left _ _).trans
                  (coordinate.paper.rhoCommon.le_threshold pairIndex hpair)
        delta_le_current := by
          intro pairIndex hpair
          exact (deltaCoordinate.trans coordinate.delta₀_le_paperFine).trans <|
            (coordinate.paper.deltaCommon.le_threshold pairIndex hpair).trans
              (min_le_left _ _)
        delta_le_final := by
          intro pairIndex hpair
          exact (deltaCoordinate.trans coordinate.delta₀_le_paperFine).trans <|
            (coordinate.paper.deltaCommon.le_threshold pairIndex hpair).trans <|
              (min_le_right _ _).trans (min_le_left _ _)
        delta_le_aligned := by
          intro pairIndex hpair
          exact (deltaCoordinate.trans coordinate.delta₀_le_paperFine).trans <|
            (coordinate.paper.deltaCommon.le_threshold pairIndex hpair).trans <|
              (min_le_right _ _).trans <|
                (min_le_right _ _).trans (min_le_left _ _)
        delta_le_first := by
          intro pairIndex hpair
          exact (deltaCoordinate.trans coordinate.delta₀_le_paperFine).trans <|
            (coordinate.paper.deltaCommon.le_threshold pairIndex hpair).trans <|
              (min_le_right _ _).trans <|
                (min_le_right _ _).trans (min_le_right _ _)
      }
    }

end Kakeya.Assouad.PureWZ2

end
