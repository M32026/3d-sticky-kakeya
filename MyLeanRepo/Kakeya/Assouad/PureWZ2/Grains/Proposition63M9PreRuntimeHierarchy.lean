import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FromCritical
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63Lemma412OuterSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PreliminaryAnalyticSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PreliminaryLocalGrain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9PreliminaryPlaninessRuntime
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9PreliminaryOuterTerminal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9SampledCoarseRuntime
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9PreliminaryOuterCutoff
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RootMapOuterTerminal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9SameExtremizerCutoff
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9TwoCallRobustSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9FirstChartDensity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9FirstChartTraceDensity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9FirstChartCutoff
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9CoarseGlobalAbsorption
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBoundaryLogCoefficient

/-!
# M9 pre-runtime loss hierarchy

This module fixes the M8 central interval and every nested M7 schedule before
choosing the Lemma 4.7 loss.  The latter is then selected below the actual
M8 input loss and below all finite cubic/quartic coefficient gaps.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- Every finite family of positive real numbers admits a single positive
strict lower bound.  In M9 this is applied only after the complete M8/M7
schedule has been frozen. -/
private theorem exists_pos_lt_forall_finite
    {α : Type*} [Fintype α] (f : α → ℝ)
    (hf : ∀ index, 0 < f index) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ index, bound < f index := by
  classical
  let values : Finset ℝ := insert 1 (Finset.univ.image f)
  have values_nonempty : values.Nonempty :=
    ⟨1, Finset.mem_insert_self 1 _⟩
  let lower := values.min' values_nonempty
  have lower_pos : 0 < lower := by
    have lower_mem : lower ∈ values := Finset.min'_mem values values_nonempty
    rcases (Finset.mem_insert.mp lower_mem) with lower_one | lower_image
    · simpa [lower_one]
    · rcases Finset.mem_image.mp lower_image with ⟨index, _, hindex⟩
      rw [← hindex]
      exact hf index
  refine ⟨lower / 2, div_pos lower_pos (by norm_num), ?_⟩
  intro index
  have lower_le : lower ≤ f index := by
    apply Finset.min'_le values (f index)
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨index, Finset.mem_univ index, rfl⟩)
  linarith

structure Proposition63M9PreRuntimeHierarchy
    (sigma outputLoss : ℝ) where
  N : ℕ
  preGrainLoss : ℝ
  gridLoss : ℝ
  midLoss : ℝ
  m8 : Proposition63Lemma412PreRuntimeScheduleData sigma gridLoss midLoss N
  lemma47N : ℕ
  lemma47Loss : ℝ
  lemma47Schedule : Proposition63ExtremalFiniteLipschitzScheduleData
    sigma lemma47Loss lemma47N
  lemma47N_two : 2 ≤ lemma47N
  lemma47N_budget : (2 : ℝ) / lemma47N < lemma47Loss
  stickyLoss : ℝ
  lemma44Loss : ℝ
  preGrain_pos : 0 < preGrainLoss
  preGrain_lt_output : preGrainLoss < outputLoss
  eighteen_preGrain_lt_output : 18 * preGrainLoss < outputLoss
  thirty_preGrain_lt_output : 30 * preGrainLoss < outputLoss
  eightyFour_preGrain_lt_output : 84 * preGrainLoss < outputLoss
  preGrain_lt_sigma_quarter : preGrainLoss < sigma / 4
  gridLoss_eq : gridLoss = preGrainLoss / 8
  midLoss_eq : midLoss = preGrainLoss / 4
  N_ge_nine : 9 ≤ N
  one_over_N_lt_grid : (1 : ℝ) / N < gridLoss
  gridLoss_pos : 0 < gridLoss
  gridLoss_le_half : gridLoss ≤ 1 / 2
  gridLoss_lt_sigma : gridLoss < 2 * sigma / 5
  gridLoss_le_mid : gridLoss ≤ midLoss
  midLoss_pos : 0 < midLoss
  midLoss_le_third : midLoss ≤ 1 / 3
  lemma47Loss_pos : 0 < lemma47Loss
  lemma47Loss_le_outer_input : lemma47Loss ≤ m8.outer.loss 0
  lemma47Loss_lt_preGrain : lemma47Loss < preGrainLoss
  coefficient_query_gap : ∀ index (hindex : index < m8.centralTemplate.count),
    lemma47Loss < m8.outer.loss (index + 1) *
      (m8.outer.oneQuery index hindex).gridSchedule.discreteLoss / 2
  coefficient_coarse_gap : ∀ index
      (hindex : index < m8.centralTemplate.count),
    ∀ pairIndex (hpair : pairIndex <
      (finiteIntervalOrderedPairs
        (m8.outer.oneQuery index hindex).gridSchedule.gridN).length),
      3 * lemma47Loss <
        ((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair).schedule.firstOutputLoss *
          (((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair).paperCandidateLoss -
            ((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair).finalLoss -
            proposition63FourCallPaperCoarseBurden
              ((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair).schedule.fourth.normalizationLoss
              ((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair).fourthKernel.internalLoss
              ((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair).epsilon₁
              ((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair).paperAngularExponent
              ((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair).floorLoss)
  coefficient_first_gap : ∀ index
      (hindex : index < m8.centralTemplate.count),
    ∀ pairIndex (hpair : pairIndex <
      (finiteIntervalOrderedPairs
        (m8.outer.oneQuery index hindex).gridSchedule.gridN).length),
      4 * lemma47Loss <
        ((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair).alignedAbsorption.internalLoss -
          proposition63FourCallNormalizedFirstEnvelopeLoss
            ((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair)
  sticky_pos : 0 < stickyLoss
  sticky_lt_lemma44 : stickyLoss < lemma44Loss
  two_sticky_le_lemma44 : 2 * stickyLoss ≤ lemma44Loss
  sticky_le_lemma47_root_source : stickyLoss ≤ lemma47Schedule.rootSourceLoss
  two_sticky_le_lemma47_root_normalization :
    2 * stickyLoss ≤ lemma47Schedule.rootNormalizationLoss
  sticky_le_m8_root_source : ∀ index
    (hindex : index < m8.centralTemplate.count),
      stickyLoss ≤ (m8.outer.oneQuery index hindex).rootSourceLoss
  two_sticky_le_m8_root_normalization : ∀ index
    (hindex : index < m8.centralTemplate.count),
      2 * stickyLoss ≤
        (m8.outer.oneQuery index hindex).backward.rootNormalizationLoss
  lemma44_le_lemma47_input : lemma44Loss ≤ lemma47Schedule.inputLoss
  lemma47_input_le_final : lemma47Schedule.inputLoss ≤ lemma47Loss
  lemma44_lt_lemma47 : lemma44Loss < lemma47Loss
  sticky_le_sigma_half : stickyLoss ≤ sigma / 2
  sigma_half_le_one_sub_sticky : sigma / 2 ≤ 1 - stickyLoss

/-- Freeze the complete M8/M7 hierarchy first and only then choose a single
Lemma 4.7 loss below every coefficient-dependent gap. -/
theorem proposition63_m9_pre_runtime_hierarchy
    {sigma outputLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtput : 0 < outputLoss) :
    Nonempty (Proposition63M9PreRuntimeHierarchy sigma outputLoss) := by
  classical
  let budget : ℝ := min outputLoss (sigma / 4)
  have budget_pos : 0 < budget := by
    dsimp only [budget]
    exact lt_min houtput (by positivity)
  let preGrainLoss : ℝ := budget / 128
  let gridLoss : ℝ := preGrainLoss / 8
  let midLoss : ℝ := preGrainLoss / 4
  have preGrain_pos : 0 < preGrainLoss := by
    dsimp only [preGrainLoss]
    positivity
  have preGrain_lt_output : preGrainLoss < outputLoss := by
    have budget_le := min_le_left outputLoss (sigma / 4)
    dsimp only [preGrainLoss]
    linarith
  have eighteen_preGrain_lt_output : 18 * preGrainLoss < outputLoss := by
    have budget_le := min_le_left outputLoss (sigma / 4)
    dsimp only [preGrainLoss]
    linarith
  have thirty_preGrain_lt_output : 30 * preGrainLoss < outputLoss := by
    have budget_le := min_le_left outputLoss (sigma / 4)
    dsimp only [preGrainLoss]
    linarith
  have eightyFour_preGrain_lt_output : 84 * preGrainLoss < outputLoss := by
    have budget_le := min_le_left outputLoss (sigma / 4)
    dsimp only [preGrainLoss]
    linarith
  have preGrain_lt_sigma_quarter : preGrainLoss < sigma / 4 := by
    have budget_le := min_le_right outputLoss (sigma / 4)
    dsimp only [preGrainLoss]
    linarith
  have gridLoss_pos : 0 < gridLoss := by
    dsimp only [gridLoss]
    positivity
  have gridLoss_le_half : gridLoss ≤ 1 / 2 := by
    have preGrain_lt_one : preGrainLoss < 1 :=
      preGrain_lt_sigma_quarter.trans (by linarith)
    dsimp only [gridLoss]
    linarith
  have gridLoss_lt_sigma : gridLoss < 2 * sigma / 5 := by
    dsimp only [gridLoss]
    linarith [preGrain_lt_sigma_quarter]
  have midLoss_pos : 0 < midLoss := by
    dsimp only [midLoss]
    positivity
  have midLoss_le_third : midLoss ≤ 1 / 3 := by
    have preGrain_lt_one : preGrainLoss < 1 :=
      preGrain_lt_sigma_quarter.trans (by linarith)
    dsimp only [midLoss]
    linarith
  rcases exists_nat_gt (max (9 : ℝ) (1 / gridLoss)) with ⟨N, N_large⟩
  have N_ge_nine : 9 ≤ N := by
    have nine_lt : (9 : ℝ) < N :=
      (le_max_left (9 : ℝ) (1 / gridLoss)).trans_lt N_large
    exact_mod_cast nine_lt.le
  have N_pos : 0 < (N : ℝ) := by positivity
  have one_over_N_lt_grid : (1 : ℝ) / N < gridLoss := by
    have reciprocal_lt : 1 / gridLoss < (N : ℝ) :=
      (le_max_right (9 : ℝ) (1 / gridLoss)).trans_lt N_large
    have scaled : 1 < gridLoss * (N : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ gridLoss_pos).mp reciprocal_lt
    rw [div_lt_iff₀ N_pos]
    simpa [mul_comm] using scaled
  rcases proposition63_lemma412_pre_runtime_schedule sigma critical
      gridLoss gridLoss midLoss N gridLoss_pos gridLoss_le_half
      gridLoss_pos gridLoss_lt_sigma midLoss_pos midLoss_le_third
      N_ge_nine with ⟨m8⟩
  let QueryIndex := Fin m8.centralTemplate.count
  let queryGap : QueryIndex → ℝ := fun index =>
    m8.outer.loss (index.val + 1) *
      (m8.outer.oneQuery index.val index.isLt).gridSchedule.discreteLoss / 2
  have queryGap_pos : ∀ index, 0 < queryGap index := by
    intro index
    dsimp only [queryGap]
    exact div_pos (mul_pos (m8.outer.loss_pos (index.val + 1) (by omega))
      (m8.outer.oneQuery index.val index.isLt).gridSchedule.discrete_loss_pos)
      (by norm_num)
  rcases exists_pos_lt_forall_finite queryGap queryGap_pos with
    ⟨queryBound, queryBound_pos, queryBound_lt⟩
  let PairIndex := Σ index : QueryIndex,
    Fin (finiteIntervalOrderedPairs
      (m8.outer.oneQuery index.val index.isLt).gridSchedule.gridN).length
  let pairSeed (pair : PairIndex) :=
    (m8.outer.oneQuery pair.1.val pair.1.isLt).backward.seed
      pair.2.val pair.2.isLt
  let coarseGap : PairIndex → ℝ := fun pair =>
    (pairSeed pair).schedule.firstOutputLoss *
      ((pairSeed pair).paperCandidateLoss - (pairSeed pair).finalLoss -
        proposition63FourCallPaperCoarseBurden
          (pairSeed pair).schedule.fourth.normalizationLoss
          (pairSeed pair).fourthKernel.internalLoss
          (pairSeed pair).epsilon₁
          (pairSeed pair).paperAngularExponent
          (pairSeed pair).floorLoss) / 3
  have coarseGap_pos : ∀ pair, 0 < coarseGap pair := by
    intro pair
    let seed := pairSeed pair
    have residual_pos : 0 < seed.paperCandidateLoss - seed.finalLoss -
        proposition63FourCallPaperCoarseBurden
          seed.schedule.fourth.normalizationLoss
          seed.fourthKernel.internalLoss seed.epsilon₁
          seed.paperAngularExponent seed.floorLoss := by
      dsimp only [proposition63FourCallPaperCoarseBurden]
      linarith [seed.paperCoarseBurden_lt_candidate]
    change 0 < seed.schedule.firstOutputLoss *
      (seed.paperCandidateLoss - seed.finalLoss -
        proposition63FourCallPaperCoarseBurden
          seed.schedule.fourth.normalizationLoss
          seed.fourthKernel.internalLoss seed.epsilon₁
          seed.paperAngularExponent seed.floorLoss) / 3
    exact div_pos (mul_pos seed.schedule.firstOutputLoss_pos residual_pos)
      (by norm_num)
  rcases exists_pos_lt_forall_finite coarseGap coarseGap_pos with
    ⟨coarseBound, coarseBound_pos, coarseBound_lt⟩
  let firstGap : PairIndex → ℝ := fun pair =>
    ((pairSeed pair).alignedAbsorption.internalLoss -
      proposition63FourCallNormalizedFirstEnvelopeLoss (pairSeed pair)) / 4
  have firstGap_pos : ∀ pair, 0 < firstGap pair := by
    intro pair
    let seed := pairSeed pair
    change 0 < (seed.alignedAbsorption.internalLoss -
      proposition63FourCallNormalizedFirstEnvelopeLoss seed) / 4
    exact div_pos (sub_pos.mpr seed.normalizedFirstEnvelopeLoss_lt)
      (by norm_num)
  rcases exists_pos_lt_forall_finite firstGap firstGap_pos with
    ⟨firstBound, firstBound_pos, firstBound_lt⟩
  let lemma47Ceiling := min (m8.outer.loss 0) <|
    min preGrainLoss <| min queryBound <| min coarseBound firstBound
  have lemma47Ceiling_pos : 0 < lemma47Ceiling := by
    dsimp only [lemma47Ceiling]
    exact lt_min (m8.outer.loss_pos 0 (by omega)) <|
      lt_min preGrain_pos <| lt_min queryBound_pos <|
        lt_min coarseBound_pos firstBound_pos
  let lemma47Loss := lemma47Ceiling / 2
  have lemma47Loss_pos : 0 < lemma47Loss := by
    dsimp only [lemma47Loss]
    positivity
  have lemma47Loss_lt_ceiling : lemma47Loss < lemma47Ceiling := by
    dsimp only [lemma47Loss]
    linarith
  have lemma47Loss_lt_outer : lemma47Loss < m8.outer.loss 0 :=
    lemma47Loss_lt_ceiling.trans_le (min_le_left _ _)
  have lemma47Loss_lt_preGrain : lemma47Loss < preGrainLoss :=
    lemma47Loss_lt_ceiling.trans_le <|
      (min_le_right _ _).trans (min_le_left _ _)
  have lemma47Loss_lt_queryBound : lemma47Loss < queryBound :=
    lemma47Loss_lt_ceiling.trans_le <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have lemma47Loss_lt_coarseBound : lemma47Loss < coarseBound :=
    lemma47Loss_lt_ceiling.trans_le <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
  have lemma47Loss_lt_firstBound : lemma47Loss < firstBound :=
    lemma47Loss_lt_ceiling.trans_le <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_right _ _)
  have lemma47Loss_le_one : lemma47Loss ≤ 1 := by
    have outer_le_grid := m8.outer.loss_le_terminal 0 (by omega)
    linarith
  rcases exists_nat_gt (8 / lemma47Loss) with ⟨lemma47N, lemma47N_large⟩
  have one_lt_eight_over : (1 : ℝ) < 8 / lemma47Loss := by
    apply (lt_div_iff₀ lemma47Loss_pos).2
    linarith [lemma47Loss_le_one]
  have lemma47N_two : 2 ≤ lemma47N := by
    have one_lt_N : (1 : ℝ) < lemma47N :=
      one_lt_eight_over.trans lemma47N_large
    exact_mod_cast one_lt_N
  have lemma47N_pos : 0 < (lemma47N : ℝ) := by positivity
  have lemma47N_budget : (2 : ℝ) / lemma47N < lemma47Loss := by
    have scaled : 8 < lemma47Loss * (lemma47N : ℝ) := by
      simpa [mul_comm] using
        (div_lt_iff₀ lemma47Loss_pos).mp lemma47N_large
    rw [div_lt_iff₀ lemma47N_pos]
    linarith
  rcases proposition63_extremal_finite_lipschitz_schedule sigma critical
      lemma47Loss lemma47Loss_pos lemma47Loss_le_one lemma47N
      lemma47N_two lemma47N_budget with ⟨lemma47Schedule⟩
  let lemma44Loss :=
    min (lemma47Schedule.inputLoss / 2) (lemma47Loss / 2)
  have lemma44Loss_pos : 0 < lemma44Loss := by
    dsimp only [lemma44Loss]
    exact lt_min
      (div_pos lemma47Schedule.inputLoss_pos (by norm_num))
      (div_pos lemma47Loss_pos (by norm_num))
  let m8RootGap : QueryIndex → ℝ := fun index =>
    min (m8.outer.oneQuery index.val index.isLt).rootSourceLoss
      ((m8.outer.oneQuery index.val index.isLt).backward.rootNormalizationLoss / 2)
  have m8RootGap_pos : ∀ index, 0 < m8RootGap index := by
    intro index
    dsimp only [m8RootGap]
    exact lt_min
      (m8.outer.oneQuery index.val index.isLt).rootSourceLoss_pos
      (div_pos
        (m8.outer.oneQuery index.val index.isLt).rootNormalizationLoss_pos
        (by norm_num))
  rcases exists_pos_lt_forall_finite m8RootGap m8RootGap_pos with
    ⟨m8RootBound, m8RootBound_pos, m8RootBound_lt⟩
  let stickyLoss := min (lemma44Loss / 4) <|
    min lemma47Schedule.rootSourceLoss <|
      min (lemma47Schedule.rootNormalizationLoss / 2) m8RootBound
  have stickyLoss_pos : 0 < stickyLoss := by
    dsimp only [stickyLoss]
    exact lt_min (div_pos lemma44Loss_pos (by norm_num)) <|
      lt_min lemma47Schedule.rootSourceLoss_pos <|
        lt_min (div_pos lemma47Schedule.rootNormalizationLoss_pos
          (by norm_num)) m8RootBound_pos
  have sticky_le_lemma44_quarter : stickyLoss ≤ lemma44Loss / 4 :=
    min_le_left _ _
  have sticky_le_m8RootBound : stickyLoss ≤ m8RootBound :=
    (min_le_right _ _).trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans (le_refl _)
  have sticky_le_budget : stickyLoss ≤ budget / 16 := by
    have lemma44_le : lemma44Loss ≤ lemma47Loss / 2 := min_le_right _ _
    have lemma47_le : lemma47Loss ≤ preGrainLoss :=
      lemma47Loss_lt_preGrain.le
    have lemma47_le_budget : lemma47Loss ≤ budget / 128 := by
      simpa only [preGrainLoss] using lemma47_le
    calc
      stickyLoss ≤ lemma44Loss / 4 := sticky_le_lemma44_quarter
      _ ≤ (lemma47Loss / 2) / 4 := by gcongr
      _ ≤ (budget / 128 / 2) / 4 := by gcongr
      _ ≤ budget / 16 := by linarith [budget_pos]
  refine ⟨{
    N := N
    preGrainLoss := preGrainLoss
    gridLoss := gridLoss
    midLoss := midLoss
    m8 := m8
    lemma47N := lemma47N
    lemma47Loss := lemma47Loss
    lemma47Schedule := lemma47Schedule
    lemma47N_two := lemma47N_two
    lemma47N_budget := lemma47N_budget
    stickyLoss := stickyLoss
    lemma44Loss := lemma44Loss
    preGrain_pos := preGrain_pos
    preGrain_lt_output := preGrain_lt_output
    eighteen_preGrain_lt_output := eighteen_preGrain_lt_output
    thirty_preGrain_lt_output := thirty_preGrain_lt_output
    eightyFour_preGrain_lt_output := eightyFour_preGrain_lt_output
    preGrain_lt_sigma_quarter := preGrain_lt_sigma_quarter
    gridLoss_eq := rfl
    midLoss_eq := rfl
    N_ge_nine := N_ge_nine
    one_over_N_lt_grid := one_over_N_lt_grid
    gridLoss_pos := gridLoss_pos
    gridLoss_le_half := gridLoss_le_half
    gridLoss_lt_sigma := gridLoss_lt_sigma
    gridLoss_le_mid := by
      dsimp only [gridLoss, midLoss]
      linarith [preGrain_pos]
    midLoss_pos := midLoss_pos
    midLoss_le_third := midLoss_le_third
    lemma47Loss_pos := lemma47Loss_pos
    lemma47Loss_le_outer_input := lemma47Loss_lt_outer.le
    lemma47Loss_lt_preGrain := lemma47Loss_lt_preGrain
    coefficient_query_gap := ?_
    coefficient_coarse_gap := ?_
    coefficient_first_gap := ?_
    sticky_pos := stickyLoss_pos
    sticky_lt_lemma44 := by linarith
    two_sticky_le_lemma44 := by linarith
    sticky_le_lemma47_root_source :=
      (min_le_right _ _).trans (min_le_left _ _)
    two_sticky_le_lemma47_root_normalization := by
      have h : stickyLoss ≤
          lemma47Schedule.rootNormalizationLoss / 2 :=
        (min_le_right (lemma44Loss / 4) _).trans <|
          (min_le_right lemma47Schedule.rootSourceLoss _).trans
            (min_le_left _ _)
      linarith
    sticky_le_m8_root_source := ?_
    two_sticky_le_m8_root_normalization := ?_
    lemma44_le_lemma47_input :=
      (min_le_left _ _).trans (by
        linarith [lemma47Schedule.inputLoss_pos])
    lemma47_input_le_final := lemma47Schedule.inputLoss_le_output
    lemma44_lt_lemma47 := by
      have h := min_le_right
        (lemma47Schedule.inputLoss / 2) (lemma47Loss / 2)
      dsimp only [lemma44Loss]
      linarith
    sticky_le_sigma_half := by
      have budget_le := min_le_right outputLoss (sigma / 4)
      linarith [sticky_le_budget]
    sigma_half_le_one_sub_sticky := by
      have budget_le := min_le_right outputLoss (sigma / 4)
      linarith [sticky_le_budget]
  }⟩
  · intro index hindex
    let query : QueryIndex := ⟨index, hindex⟩
    have gap_lt := lemma47Loss_lt_queryBound.trans (queryBound_lt query)
    simpa only [queryGap, query] using gap_lt
  · intro index hindex pairIndex hpair
    let pair : PairIndex := ⟨⟨index, hindex⟩, ⟨pairIndex, hpair⟩⟩
    have gap_lt := lemma47Loss_lt_coarseBound.trans (coarseBound_lt pair)
    have expanded : lemma47Loss <
        ((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair).schedule.firstOutputLoss *
          (((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair).paperCandidateLoss -
            ((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair).finalLoss -
            proposition63FourCallPaperCoarseBurden
              ((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair).schedule.fourth.normalizationLoss
              ((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair).fourthKernel.internalLoss
              ((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair).epsilon₁
              ((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair).paperAngularExponent
              ((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair).floorLoss) / 3 := by
      simpa only [coarseGap, pairSeed, pair] using gap_lt
    linarith
  · intro index hindex pairIndex hpair
    let pair : PairIndex := ⟨⟨index, hindex⟩, ⟨pairIndex, hpair⟩⟩
    have gap_lt := lemma47Loss_lt_firstBound.trans (firstBound_lt pair)
    have expanded : lemma47Loss <
        (((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair).alignedAbsorption.internalLoss -
          proposition63FourCallNormalizedFirstEnvelopeLoss
            ((m8.outer.oneQuery index hindex).backward.seed pairIndex hpair)) / 4 := by
      simpa only [firstGap, pairSeed, pair] using gap_lt
    linarith
  · intro index hindex
    let query : QueryIndex := ⟨index, hindex⟩
    have root_lt := m8RootBound_lt query
    have root_le := min_le_left
      (m8.outer.oneQuery index hindex).rootSourceLoss
      ((m8.outer.oneQuery index hindex).backward.rootNormalizationLoss / 2)
    exact sticky_le_m8RootBound.trans (root_lt.le.trans root_le)
  · intro index hindex
    let query : QueryIndex := ⟨index, hindex⟩
    have root_lt := m8RootBound_lt query
    have root_le := min_le_right
      (m8.outer.oneQuery index hindex).rootSourceLoss
      ((m8.outer.oneQuery index hindex).backward.rootNormalizationLoss / 2)
    have sticky_le_half := sticky_le_m8RootBound.trans
      (root_lt.le.trans root_le)
    linarith

/-- The actual Lemma 4.7 coefficient, packaged in the nonnegative type used
by the M7 four-call implementation. -/
noncomputable def Proposition63M9PreRuntimeHierarchy.sourceCoefficient
    {sigma outputLoss rho : ℝ}
    (data : Proposition63M9PreRuntimeHierarchy sigma outputLoss) : NNReal :=
  Real.toNNReal (Real.rpow rho (-data.lemma47Loss))

@[simp] theorem Proposition63M9PreRuntimeHierarchy.sourceCoefficient_coe
    {sigma outputLoss rho : ℝ}
    (data : Proposition63M9PreRuntimeHierarchy sigma outputLoss)
    (rho_pos : 0 < rho) :
    (data.sourceCoefficient (rho := rho) : ℝ) =
      Real.rpow rho (-data.lemma47Loss) := by
  exact Real.coe_toNNReal _ (Real.rpow_pos_of_pos rho_pos _).le

/-- The amplified M7 coefficient has a fixed cubic power envelope. -/
theorem Proposition63M9PreRuntimeHierarchy.coarseCoefficient_envelope
    {sigma outputLoss rho : ℝ}
    (data : Proposition63M9PreRuntimeHierarchy sigma outputLoss)
    (rho_pos : 0 < rho) (rho_le_one : rho ≤ 1) :
    proposition63FourCallPaperCoarseCoefficient
        ((4 : NNReal) * (lipschitzExtensionConstant Point3 *
          data.sourceCoefficient (rho := rho))) ≤
      (1643791358363649 : ENNReal) *
        (((4 : ENNReal) * (lipschitzExtensionConstant Point3 : ENNReal)) ^ 3) *
        Kakeya.realRpowENN rho (-3 * data.lemma47Loss) := by
  let coefficient : NNReal :=
    (4 : NNReal) * (lipschitzExtensionConstant Point3 *
      data.sourceCoefficient (rho := rho))
  have coefficient_one : 1 ≤ (coefficient : ℝ) := by
    have source_one : 1 ≤ Real.rpow rho (-data.lemma47Loss) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge rho_pos rho_le_one
        (show -data.lemma47Loss ≤ 0 by linarith [data.lemma47Loss_pos])
    have extension_one : 1 ≤ (lipschitzExtensionConstant Point3 : ℝ) := by
      simp [lipschitzExtensionConstant]
    dsimp only [coefficient]
    push_cast
    rw [data.sourceCoefficient_coe rho_pos]
    nlinarith
  calc
    proposition63FourCallPaperCoarseCoefficient coefficient ≤
        (1643791358363649 : ENNReal) * (coefficient : ENNReal) ^ 3 :=
      proposition63_four_call_paper_coarse_coefficient_le_cubic
        coefficient coefficient_one
    _ = (1643791358363649 : ENNReal) *
        (((4 : ENNReal) * (lipschitzExtensionConstant Point3 : ENNReal)) ^ 3) *
          Kakeya.realRpowENN rho (-3 * data.lemma47Loss) := by
      rw [show (coefficient : ENNReal) =
          ((4 : ENNReal) * (lipschitzExtensionConstant Point3 : ENNReal)) *
            Kakeya.realRpowENN rho (-data.lemma47Loss) by
        dsimp only [coefficient, Proposition63M9PreRuntimeHierarchy.sourceCoefficient]
        push_cast
        rw [ENNReal.ofNNReal_toNNReal]
        simp only [Kakeya.realRpowENN]
        ring]
      rw [mul_pow]
      have power_eq : Kakeya.realRpowENN rho (-data.lemma47Loss) ^ 3 =
          Kakeya.realRpowENN rho (-3 * data.lemma47Loss) := by
        rw [pow_three, ← realRpowENN_add rho_pos,
          ← realRpowENN_add rho_pos]
        congr 1
        ring
      rw [power_eq]
      ring

/-- The normalized-first endpoint has the corresponding fixed quartic power
envelope. -/
theorem Proposition63M9PreRuntimeHierarchy.normalizedFirstFixed_envelope
    {sigma outputLoss rho : ℝ}
    (data : Proposition63M9PreRuntimeHierarchy sigma outputLoss)
    (rho_pos : 0 < rho) (rho_le_one : rho ≤ 1) :
    proposition63NestedIntervalCoefficient
          (((4 : NNReal) * (lipschitzExtensionConstant Point3 *
            data.sourceCoefficient (rho := rho))) : ℝ) *
        proposition63FourCallNormalizedFirstAmplitude
          ((4 : NNReal) * (lipschitzExtensionConstant Point3 *
            data.sourceCoefficient (rho := rho))) ≤
      (6695347109068800000 : ENNReal) *
        (((4 : ENNReal) * (lipschitzExtensionConstant Point3 : ENNReal)) ^ 4) *
        Kakeya.realRpowENN rho (-4 * data.lemma47Loss) := by
  let coefficient : NNReal :=
    (4 : NNReal) * (lipschitzExtensionConstant Point3 *
      data.sourceCoefficient (rho := rho))
  have coefficient_one : 1 ≤ (coefficient : ℝ) := by
    have source_one : 1 ≤ Real.rpow rho (-data.lemma47Loss) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge rho_pos rho_le_one
        (show -data.lemma47Loss ≤ 0 by linarith [data.lemma47Loss_pos])
    have extension_one : 1 ≤ (lipschitzExtensionConstant Point3 : ℝ) := by
      simp [lipschitzExtensionConstant]
    dsimp only [coefficient]
    push_cast
    rw [data.sourceCoefficient_coe rho_pos]
    nlinarith
  calc
    proposition63NestedIntervalCoefficient (coefficient : ℝ) *
          proposition63FourCallNormalizedFirstAmplitude coefficient ≤
        (6695347109068800000 : ENNReal) * (coefficient : ENNReal) ^ 4 :=
      proposition63_normalized_first_fixed_le_quartic coefficient coefficient_one
    _ = (6695347109068800000 : ENNReal) *
        (((4 : ENNReal) * (lipschitzExtensionConstant Point3 : ENNReal)) ^ 4) *
          Kakeya.realRpowENN rho (-4 * data.lemma47Loss) := by
      rw [show (coefficient : ENNReal) =
          ((4 : ENNReal) * (lipschitzExtensionConstant Point3 : ENNReal)) *
            Kakeya.realRpowENN rho (-data.lemma47Loss) by
        dsimp only [coefficient, Proposition63M9PreRuntimeHierarchy.sourceCoefficient]
        push_cast
        rw [ENNReal.ofNNReal_toNNReal]
        simp only [Kakeya.realRpowENN]
        ring]
      rw [mul_pow]
      have power_eq : Kakeya.realRpowENN rho (-data.lemma47Loss) ^ 4 =
          Kakeya.realRpowENN rho (-4 * data.lemma47Loss) := by
        rw [pow_succ, pow_three, ← realRpowENN_add rho_pos,
          ← realRpowENN_add rho_pos, ← realRpowENN_add rho_pos]
        congr 1
        ring
      rw [power_eq]
      ring

/-- One ordered pair's constant-only smallness threshold.  It is chosen
before the outer Lemma 4.7 scale and pays exactly the residual gaps left after
the cubic and quartic powers of its runtime coefficient. -/
structure Proposition63M9PairPowerCutoffData
    {sigma outputLoss seedOutputLoss discreteLoss : ℝ}
    (data : Proposition63M9PreRuntimeHierarchy sigma outputLoss)
    (seed : Proposition63FourCallInnerLossSeed sigma seedOutputLoss discreteLoss) where
  base : Proposition63FourCallPaperSeedCutoffData seed 1
  rho₀ : ℝ
  rho₀_pos : 0 < rho₀
  rho₀_le_one : rho₀ ≤ 1
  coarse_fixed : ∀ {rho : ℝ}, 0 < rho → rho ≤ rho₀ →
    (1643791358363649 : ENNReal) *
        (((4 : ENNReal) * (lipschitzExtensionConstant Point3 : ENNReal)) ^ 3) ≤
      Kakeya.realRpowENN rho
        (-(seed.schedule.firstOutputLoss *
            (seed.paperCandidateLoss - seed.finalLoss -
              proposition63FourCallPaperCoarseBurden
                seed.schedule.fourth.normalizationLoss
                seed.fourthKernel.internalLoss seed.epsilon₁
                seed.paperAngularExponent seed.floorLoss) -
          3 * data.lemma47Loss))
  first_fixed : ∀ {rho : ℝ}, 0 < rho → rho ≤ rho₀ →
    (6695347109068800000 : ENNReal) *
        (((4 : ENNReal) * (lipschitzExtensionConstant Point3 : ENNReal)) ^ 4) ≤
      Kakeya.realRpowENN rho
        (-((seed.alignedAbsorption.internalLoss -
            proposition63FourCallNormalizedFirstEnvelopeLoss seed) -
          4 * data.lemma47Loss))
  inner_scale : ∀ {rho : ℝ}, 0 < rho → rho ≤ rho₀ →
    Real.rpow rho seed.schedule.firstOutputLoss ≤ base.rhoCutoff
  inner_scale_small : ∀ {rho : ℝ}, 0 < rho → rho ≤ rho₀ →
    Real.rpow rho seed.schedule.firstOutputLoss ≤ 1 / 144
  first_output_gap_small : ∀ {rho : ℝ}, 0 < rho → rho ≤ rho₀ →
    Real.rpow rho
      (discreteLoss - seed.schedule.firstOutputLoss) ≤ 1 / 2

theorem proposition63_m9_pair_power_cutoff
    {sigma outputLoss seedOutputLoss discreteLoss : ℝ}
    (data : Proposition63M9PreRuntimeHierarchy sigma outputLoss)
    (seed : Proposition63FourCallInnerLossSeed sigma seedOutputLoss discreteLoss)
    (coarse_gap : 3 * data.lemma47Loss <
      seed.schedule.firstOutputLoss *
        (seed.paperCandidateLoss - seed.finalLoss -
          proposition63FourCallPaperCoarseBurden
            seed.schedule.fourth.normalizationLoss
            seed.fourthKernel.internalLoss seed.epsilon₁
            seed.paperAngularExponent seed.floorLoss))
    (first_gap : 4 * data.lemma47Loss <
      seed.alignedAbsorption.internalLoss -
        proposition63FourCallNormalizedFirstEnvelopeLoss seed) :
    Nonempty (Proposition63M9PairPowerCutoffData data seed) := by
  have coarse_residual : 0 <
      seed.schedule.firstOutputLoss *
          (seed.paperCandidateLoss - seed.finalLoss -
            proposition63FourCallPaperCoarseBurden
              seed.schedule.fourth.normalizationLoss
              seed.fourthKernel.internalLoss seed.epsilon₁
              seed.paperAngularExponent seed.floorLoss) -
        3 * data.lemma47Loss := by linarith
  have first_residual : 0 <
      (seed.alignedAbsorption.internalLoss -
          proposition63FourCallNormalizedFirstEnvelopeLoss seed) -
        4 * data.lemma47Loss := by linarith
  let coarseConstant : ENNReal :=
    (1643791358363649 : ENNReal) *
      (((4 : ENNReal) * (lipschitzExtensionConstant Point3 : ENNReal)) ^ 3)
  let firstConstant : ENNReal :=
    (6695347109068800000 : ENNReal) *
      (((4 : ENNReal) * (lipschitzExtensionConstant Point3 : ENNReal)) ^ 4)
  let base := proposition63FourCallPaperSeedBaseCutoff seed
  have coarse_finite : coarseConstant ≠ ⊤ := by
    dsimp only [coarseConstant]
    finiteness
  have first_finite : firstConstant ≠ ⊤ := by
    dsimp only [firstConstant]
    finiteness
  rcases exists_delta_realRpowENN_bound coarseConstant coarse_finite
      coarse_residual with
    ⟨coarseCutoff, coarseCutoff_pos, coarseCutoff_le_one, coarse_bound⟩
  rcases exists_delta_realRpowENN_bound firstConstant first_finite
      first_residual with
    ⟨firstCutoff, firstCutoff_pos, firstCutoff_le_one, first_bound⟩
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := min base.rhoCutoff (1 / 2))
      (s := seed.schedule.firstOutputLoss)
      (lt_min base.rhoCutoff_pos (by norm_num))
      seed.schedule.firstOutputLoss_pos with
    ⟨baseCutoff, baseCutoff_pos, baseCutoff_le_one, base_bound⟩
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := (1 / 144 : ℝ))
      (s := seed.schedule.firstOutputLoss) (by norm_num)
      seed.schedule.firstOutputLoss_pos with
    ⟨smallCutoff, smallCutoff_pos, smallCutoff_le_one, small_bound⟩
  have firstOutput_lt_discrete :
      seed.schedule.firstOutputLoss < discreteLoss := by
    exact seed.schedule.firstOutputLoss_lt_secondSource.trans_le <|
      seed.schedule.second.sourceLoss_le_half.trans <|
        (half_le_self seed.schedule.second.normalizationLoss_pos.le).trans <|
          seed.schedule.second.normalizationLoss_lt_output.le.trans
            seed.secondOutputLoss_le_discrete
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := (1 / 2 : ℝ))
      (s := discreteLoss - seed.schedule.firstOutputLoss) (by norm_num)
      (sub_pos.mpr firstOutput_lt_discrete) with
    ⟨gapCutoff, gapCutoff_pos, gapCutoff_le_one, gap_bound⟩
  let rho₀ := min coarseCutoff <| min firstCutoff <|
    min baseCutoff <| min smallCutoff gapCutoff
  exact ⟨{
    base := base
    rho₀ := rho₀
    rho₀_pos := lt_min coarseCutoff_pos <|
      lt_min firstCutoff_pos <| lt_min baseCutoff_pos <|
        lt_min smallCutoff_pos gapCutoff_pos
    rho₀_le_one := (min_le_left _ _).trans coarseCutoff_le_one
    coarse_fixed := by
      intro rho rho_pos rho_le
      exact coarse_bound rho rho_pos (rho_le.trans (min_le_left _ _))
    first_fixed := by
      intro rho rho_pos rho_le
      exact first_bound rho rho_pos <| rho_le.trans <|
        (min_le_right _ _).trans (min_le_left _ _)
    inner_scale := by
      intro rho rho_pos rho_le
      exact (base_bound rho rho_pos <| rho_le.trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_left _ _)).trans (min_le_left _ _)
    inner_scale_small := by
      intro rho rho_pos rho_le
      exact small_bound rho rho_pos <| rho_le.trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
    first_output_gap_small := by
      intro rho rho_pos rho_le
      exact gap_bound rho rho_pos <| rho_le.trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_right _ _)
  }⟩

/-- Instantiate the coefficient-aware coarse absorption at the fixed power
of the outer Lemma 4.7 scale.  The only asymptotic input is the endpoint bound
for the constant part of the cubic envelope. -/
noncomputable def Proposition63M9PreRuntimeHierarchy.paperCoarseAbsorptionAt
    {sigma outputLoss seedOutputLoss discreteLoss sourceScale cutoffScale : ℝ}
    (data : Proposition63M9PreRuntimeHierarchy sigma outputLoss)
    (seed : Proposition63FourCallInnerLossSeed sigma seedOutputLoss discreteLoss)
    (sourceScale_pos : 0 < sourceScale)
    (sourceScale_le_one : sourceScale ≤ 1)
    (cutoffScale_pos : 0 < cutoffScale) (cutoffScale_le_one : cutoffScale ≤ 1)
    (cutoffScale_eq : cutoffScale =
      Real.rpow sourceScale seed.schedule.firstOutputLoss)
    (strengthened_gap : 3 * data.lemma47Loss <
      seed.schedule.firstOutputLoss *
        (seed.paperCandidateLoss - seed.finalLoss -
          proposition63FourCallPaperCoarseBurden
            seed.schedule.fourth.normalizationLoss
            seed.fourthKernel.internalLoss seed.epsilon₁
            seed.paperAngularExponent seed.floorLoss))
    (fixed_bound :
      (1643791358363649 : ENNReal) *
          (((4 : ENNReal) * (lipschitzExtensionConstant Point3 : ENNReal)) ^ 3) ≤
        Kakeya.realRpowENN sourceScale
          (-(seed.schedule.firstOutputLoss *
              (seed.paperCandidateLoss - seed.finalLoss -
                proposition63FourCallPaperCoarseBurden
                  seed.schedule.fourth.normalizationLoss
                  seed.fourthKernel.internalLoss seed.epsilon₁
                  seed.paperAngularExponent seed.floorLoss) -
            3 * data.lemma47Loss))) :
    Proposition63FourCallPaperCoarseAbsorptionData
      (proposition63FourCallPaperCoarseCoefficient
        ((4 : NNReal) * (lipschitzExtensionConstant Point3 *
          data.sourceCoefficient (rho := sourceScale))))
      seed.schedule.fourth.normalizationLoss seed.fourthKernel.internalLoss
      seed.epsilon₁ seed.paperAngularExponent seed.floorLoss
      seed.paperCandidateLoss seed.finalLoss := by
  let residual := seed.paperCandidateLoss - seed.finalLoss -
    proposition63FourCallPaperCoarseBurden
      seed.schedule.fourth.normalizationLoss seed.fourthKernel.internalLoss
      seed.epsilon₁ seed.paperAngularExponent seed.floorLoss
  have residual_pos : 0 < residual := by
    dsimp only [residual]
    have product_pos : 0 < seed.schedule.firstOutputLoss * residual := by
      dsimp only [residual] at strengthened_gap ⊢
      linarith [strengthened_gap, data.lemma47Loss_pos]
    rcases mul_pos_iff.mp product_pos with positive | negative
    · exact positive.2
    · exfalso
      linarith [seed.schedule.firstOutputLoss_pos, negative.1]
  apply proposition63_four_call_paper_coarse_absorption_at
    (proposition63FourCallPaperCoarseCoefficient
      ((4 : NNReal) * (lipschitzExtensionConstant Point3 *
        data.sourceCoefficient (rho := sourceScale))))
    seed.schedule.fourth.normalizationLoss seed.fourthKernel.internalLoss
    seed.epsilon₁ seed.paperAngularExponent seed.floorLoss
    seed.paperCandidateLoss seed.finalLoss
    cutoffScale cutoffScale_pos cutoffScale_le_one
    (by
      dsimp only [proposition63FourCallPaperCoarseBurden]
      linarith [seed.paperCoarseBurden_lt_candidate])
  have coefficient_bound := data.coarseCoefficient_envelope
    sourceScale_pos sourceScale_le_one
  calc
    proposition63FourCallPaperCoarseCoefficient
          ((4 : NNReal) * (lipschitzExtensionConstant Point3 *
            data.sourceCoefficient (rho := sourceScale))) ≤
        (1643791358363649 : ENNReal) *
          (((4 : ENNReal) * (lipschitzExtensionConstant Point3 : ENNReal)) ^ 3) *
          Kakeya.realRpowENN sourceScale (-3 * data.lemma47Loss) :=
      coefficient_bound
    _ ≤ Kakeya.realRpowENN sourceScale
          (-(seed.schedule.firstOutputLoss * residual -
            3 * data.lemma47Loss)) *
          Kakeya.realRpowENN sourceScale (-3 * data.lemma47Loss) := by gcongr
    _ = Kakeya.realRpowENN cutoffScale (-residual) := by
      rw [cutoffScale_eq]
      rw [← realRpowENN_add sourceScale_pos]
      simp only [Kakeya.realRpowENN]
      congr 1
      calc
        Real.rpow sourceScale
            (-(seed.schedule.firstOutputLoss * residual -
                3 * data.lemma47Loss) + -3 * data.lemma47Loss) =
            Real.rpow sourceScale
              (seed.schedule.firstOutputLoss * (-residual)) := by
          congr 1
          ring
        _ = Real.rpow (Real.rpow sourceScale seed.schedule.firstOutputLoss)
            (-residual) := Real.rpow_mul sourceScale_pos.le _ _

/-- Instantiate the normalized-first cutoff at the outer Lemma 4.7 scale.
The quartic coefficient is paid by the preselected endpoint bound. -/
noncomputable def Proposition63M9PreRuntimeHierarchy.firstUniformCutoffAt
    {sigma outputLoss seedOutputLoss discreteLoss rho : ℝ}
    (data : Proposition63M9PreRuntimeHierarchy sigma outputLoss)
    (seed : Proposition63FourCallInnerLossSeed sigma seedOutputLoss discreteLoss)
    (rho_pos : 0 < rho) (rho_le_one : rho ≤ 1)
    (_strengthened_gap : 4 * data.lemma47Loss <
      seed.alignedAbsorption.internalLoss -
        proposition63FourCallNormalizedFirstEnvelopeLoss seed)
    (fixed_bound :
      (6695347109068800000 : ENNReal) *
          (((4 : ENNReal) * (lipschitzExtensionConstant Point3 : ENNReal)) ^ 4) ≤
        Kakeya.realRpowENN rho
          (-((seed.alignedAbsorption.internalLoss -
            proposition63FourCallNormalizedFirstEnvelopeLoss seed) -
            4 * data.lemma47Loss))) :
    Proposition63FourCallFirstUniformCutoffData seed
      ((4 : NNReal) * (lipschitzExtensionConstant Point3 *
        data.sourceCoefficient (rho := rho))) := by
  apply proposition63_four_call_first_uniform_cutoff_at seed
    ((4 : NNReal) * (lipschitzExtensionConstant Point3 *
      data.sourceCoefficient (rho := rho))) rho_pos rho_le_one
  have coefficient_bound :=
    data.normalizedFirstFixed_envelope rho_pos rho_le_one
  calc
    proposition63NestedIntervalCoefficient
          (((4 : NNReal) * (lipschitzExtensionConstant Point3 *
            data.sourceCoefficient (rho := rho))) : ℝ) *
        proposition63FourCallNormalizedFirstAmplitude
          ((4 : NNReal) * (lipschitzExtensionConstant Point3 *
            data.sourceCoefficient (rho := rho))) ≤
        (6695347109068800000 : ENNReal) *
          (((4 : ENNReal) * (lipschitzExtensionConstant Point3 : ENNReal)) ^ 4) *
          Kakeya.realRpowENN rho (-4 * data.lemma47Loss) := coefficient_bound
    _ ≤ Kakeya.realRpowENN rho
          (-((seed.alignedAbsorption.internalLoss -
              proposition63FourCallNormalizedFirstEnvelopeLoss seed) -
            4 * data.lemma47Loss)) *
          Kakeya.realRpowENN rho (-4 * data.lemma47Loss) := by gcongr
    _ = Kakeya.realRpowENN rho
          (-(seed.alignedAbsorption.internalLoss -
            proposition63FourCallNormalizedFirstEnvelopeLoss seed)) := by
      rw [← realRpowENN_add rho_pos]
      congr 1
      ring

noncomputable def Proposition63M9PairPowerCutoffData.paperCutoff
    {sigma outputLoss seedOutputLoss discreteLoss rho : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {seed : Proposition63FourCallInnerLossSeed sigma seedOutputLoss discreteLoss}
    (cutoff : Proposition63M9PairPowerCutoffData data seed)
    (rho_pos : 0 < rho) (rho_le : rho ≤ cutoff.rho₀)
    (coarse_gap : 3 * data.lemma47Loss <
      seed.schedule.firstOutputLoss *
        (seed.paperCandidateLoss - seed.finalLoss -
          proposition63FourCallPaperCoarseBurden
            seed.schedule.fourth.normalizationLoss
            seed.fourthKernel.internalLoss seed.epsilon₁
            seed.paperAngularExponent seed.floorLoss)) :
    Proposition63FourCallPaperSeedCutoffData seed
      ((4 : NNReal) * (lipschitzExtensionConstant Point3 *
        data.sourceCoefficient (rho := rho))) :=
  cutoff.base.withCoarseAbsorption
    ((4 : NNReal) * (lipschitzExtensionConstant Point3 *
      data.sourceCoefficient (rho := rho)))
    (data.paperCoarseAbsorptionAt seed rho_pos
      (rho_le.trans cutoff.rho₀_le_one)
      (Real.rpow_pos_of_pos rho_pos _)
      (Real.rpow_le_one rho_pos.le (rho_le.trans cutoff.rho₀_le_one)
        seed.schedule.firstOutputLoss_pos.le) rfl coarse_gap
      (cutoff.coarse_fixed rho_pos rho_le))

noncomputable def Proposition63M9PairPowerCutoffData.firstUniformCutoff
    {sigma outputLoss seedOutputLoss discreteLoss rho : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {seed : Proposition63FourCallInnerLossSeed sigma seedOutputLoss discreteLoss}
    (cutoff : Proposition63M9PairPowerCutoffData data seed)
    (rho_pos : 0 < rho) (rho_le : rho ≤ cutoff.rho₀)
    (first_gap : 4 * data.lemma47Loss <
      seed.alignedAbsorption.internalLoss -
        proposition63FourCallNormalizedFirstEnvelopeLoss seed) :
    Proposition63FourCallFirstUniformCutoffData seed
      ((4 : NNReal) * (lipschitzExtensionConstant Point3 *
        data.sourceCoefficient (rho := rho))) :=
  data.firstUniformCutoffAt seed rho_pos (rho_le.trans cutoff.rho₀_le_one)
    first_gap (cutoff.first_fixed rho_pos rho_le)

/-- Freeze the constant-only power cutoffs at every M8/M7 coordinate. -/
structure Proposition63M9PowerCutoffFamilyData
    {sigma outputLoss : ℝ}
    (data : Proposition63M9PreRuntimeHierarchy sigma outputLoss) where
  pairCutoff : ∀ outerIndex
    (houter : outerIndex < data.m8.centralTemplate.count),
    ∀ pairIndex (hpair : pairIndex <
      (finiteIntervalOrderedPairs
        (data.m8.outer.oneQuery outerIndex houter).gridSchedule.gridN).length),
      Proposition63M9PairPowerCutoffData data
        ((data.m8.outer.oneQuery outerIndex houter).backward.seed
          pairIndex hpair)
  outerCutoff : Proposition63FinitePositiveCutoff
    data.m8.centralTemplate.count
    (fun outerIndex houter =>
      (Classical.choice <| proposition63_finite_positive_cutoff
        (finiteIntervalOrderedPairs
          (data.m8.outer.oneQuery outerIndex houter).gridSchedule.gridN).length
        (fun pairIndex hpair =>
          (pairCutoff outerIndex houter pairIndex hpair).rho₀)
        (fun pairIndex hpair =>
          (pairCutoff outerIndex houter pairIndex hpair).rho₀_pos)).delta₀)

theorem proposition63_m9_power_cutoff_family
    {sigma outputLoss : ℝ}
    (data : Proposition63M9PreRuntimeHierarchy sigma outputLoss) :
    Nonempty (Proposition63M9PowerCutoffFamilyData data) := by
  let pairCutoff : ∀ outerIndex
      (houter : outerIndex < data.m8.centralTemplate.count),
      ∀ pairIndex (hpair : pairIndex <
        (finiteIntervalOrderedPairs
          (data.m8.outer.oneQuery outerIndex houter).gridSchedule.gridN).length),
        Proposition63M9PairPowerCutoffData data
          ((data.m8.outer.oneQuery outerIndex houter).backward.seed
            pairIndex hpair) :=
    fun outerIndex houter pairIndex hpair => Classical.choice <|
      proposition63_m9_pair_power_cutoff data
        ((data.m8.outer.oneQuery outerIndex houter).backward.seed
          pairIndex hpair)
        (data.coefficient_coarse_gap outerIndex houter pairIndex hpair)
        (data.coefficient_first_gap outerIndex houter pairIndex hpair)
  let innerCutoff := fun outerIndex
      (houter : outerIndex < data.m8.centralTemplate.count) =>
    Classical.choice <|
      proposition63_finite_positive_cutoff
        (finiteIntervalOrderedPairs
          (data.m8.outer.oneQuery outerIndex houter).gridSchedule.gridN).length
        (fun pairIndex hpair =>
          (pairCutoff outerIndex houter pairIndex hpair).rho₀)
        (fun pairIndex hpair =>
          (pairCutoff outerIndex houter pairIndex hpair).rho₀_pos)
  let outerCutoff := Classical.choice <|
    proposition63_finite_positive_cutoff data.m8.centralTemplate.count
      (fun outerIndex houter => (innerCutoff outerIndex houter).delta₀)
      (fun outerIndex houter => (innerCutoff outerIndex houter).delta₀_pos)
  exact ⟨{ pairCutoff := pairCutoff, outerCutoff := outerCutoff }⟩

/-- The common outer cutoff is below each pair's own threshold, but the M9
runtime will use the stronger pairwise inequality after translating its
actual inner scale. -/
theorem Proposition63M9PowerCutoffFamilyData.outerCutoff_le_pair
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PowerCutoffFamilyData data)
    {outerIndex : ℕ}
    (houter : outerIndex < data.m8.centralTemplate.count)
    {pairIndex : ℕ} (hpair : pairIndex <
      (finiteIntervalOrderedPairs
        (data.m8.outer.oneQuery outerIndex houter).gridSchedule.gridN).length) :
    cutoff.outerCutoff.delta₀ ≤
      (cutoff.pairCutoff outerIndex houter pairIndex hpair).rho₀ := by
  let innerCutoff := Classical.choice <|
    proposition63_finite_positive_cutoff
      (finiteIntervalOrderedPairs
        (data.m8.outer.oneQuery outerIndex houter).gridSchedule.gridN).length
      (fun pairIndex hpair =>
        (cutoff.pairCutoff outerIndex houter pairIndex hpair).rho₀)
      (fun pairIndex hpair =>
        (cutoff.pairCutoff outerIndex houter pairIndex hpair).rho₀_pos)
  have outer_le : cutoff.outerCutoff.delta₀ ≤ innerCutoff.delta₀ :=
    cutoff.outerCutoff.le_threshold outerIndex houter
  exact outer_le.trans (innerCutoff.le_threshold pairIndex hpair)

/-- The root-density payment for one frozen M7 schedule.  This cutoff is
chosen from losses only, before an ambient re-entry or runtime family exists. -/
structure Proposition63M9RootBindingCutoffData
    {sigma gridOutputLoss : ℝ}
    (schedule : Proposition63Lemma411ScheduleData sigma gridOutputLoss) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  density_absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    Kakeya.realRpowENN delta schedule.backward.rootDensityLoss ≤
      Kakeya.realRpowENN delta schedule.rootSourceLoss / 2

/-- Select the root-density cutoff from the strict loss gap built into the
backward M7 schedule. -/
theorem proposition63_m9_root_binding_cutoff
    {sigma gridOutputLoss : ℝ}
    (schedule : Proposition63Lemma411ScheduleData sigma gridOutputLoss) :
    Nonempty (Proposition63M9RootBindingCutoffData schedule) := by
  have gap_pos : 0 < schedule.backward.rootDensityLoss -
      schedule.rootSourceLoss := by
    dsimp [Proposition63Lemma411ScheduleData.rootSourceLoss,
      Proposition63FourCallInnerBackwardLossSchedule.rootDensityLoss,
      Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss]
    linarith [schedule.backward.rootBudget_pos]
  rcases exists_delta_realRpowENN_bound (2 : ENNReal) (by norm_num)
      gap_pos with
    ⟨delta₀, delta₀_pos, delta₀_le_one, bound⟩
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := delta₀_pos
    delta₀_le_one := delta₀_le_one
    density_absorb := ?_
  }⟩
  intro delta delta_pos delta_le
  apply (ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).2
  calc
    Kakeya.realRpowENN delta schedule.backward.rootDensityLoss * 2 =
        2 * Kakeya.realRpowENN delta
          schedule.backward.rootDensityLoss := by ring
    _ ≤ Kakeya.realRpowENN delta
          (-(schedule.backward.rootDensityLoss - schedule.rootSourceLoss)) *
            Kakeya.realRpowENN delta
              schedule.backward.rootDensityLoss := by
      gcongr
      exact bound delta delta_pos delta_le
    _ = Kakeya.realRpowENN delta schedule.rootSourceLoss := by
      rw [← realRpowENN_add delta_pos]
      simp [Kakeya.realRpowENN]

/-- The two query-scale payments at one M8 coordinate.  The first bound pays
the dynamic Lemma 4.7 coefficient; the second gives the square-root window. -/
structure Proposition63M9QueryCutoffData
    {sigma outputLoss : ℝ}
    (data : Proposition63M9PreRuntimeHierarchy sigma outputLoss)
    (outerIndex : ℕ)
    (houter : outerIndex < data.m8.centralTemplate.count) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  amplified_endpoint : ∀ {rho : ℝ}, 0 < rho → rho ≤ delta₀ →
    (64 * (lipschitzExtensionConstant Point3 : ℝ)) *
        Real.rpow rho
          (data.m8.outer.loss (outerIndex + 1) *
              (data.m8.outer.oneQuery outerIndex houter).gridSchedule.discreteLoss / 2 -
            data.lemma47Loss) ≤ 1
  query_power_endpoint : ∀ {rho : ℝ}, 0 < rho → rho ≤ delta₀ →
    Real.rpow rho
      (data.m8.outer.loss (outerIndex + 1) *
        (data.m8.outer.oneQuery outerIndex houter).gridSchedule.discreteLoss / 2) ≤
      1 / 2
  query_endpoint : ∀ {rho : ℝ}, 0 < rho → rho ≤ delta₀ →
    Real.rpow rho (data.m8.outer.loss (outerIndex + 1)) ≤ 1 / 4

theorem proposition63_m9_query_cutoff
    {sigma outputLoss : ℝ}
    (data : Proposition63M9PreRuntimeHierarchy sigma outputLoss)
    (outerIndex : ℕ)
    (houter : outerIndex < data.m8.centralTemplate.count) :
    Nonempty (Proposition63M9QueryCutoffData data outerIndex houter) := by
  let queryLoss := data.m8.outer.loss (outerIndex + 1)
  let discreteLoss :=
    (data.m8.outer.oneQuery outerIndex houter).gridSchedule.discreteLoss
  have gap_pos : 0 < queryLoss * discreteLoss / 2 - data.lemma47Loss := by
    dsimp only [queryLoss, discreteLoss]
    linarith [data.coefficient_query_gap outerIndex houter]
  rcases exists_delta_mul_rpow_le_rpow
      (64 * (lipschitzExtensionConstant Point3 : ℝ)) (by positivity)
      (alpha := queryLoss * discreteLoss / 2 - data.lemma47Loss)
      (beta := 0)
      (show (0 : ℝ) < queryLoss * discreteLoss / 2 - data.lemma47Loss by
        exact gap_pos) with
    ⟨amplifiedCutoff, amplifiedCutoff_pos, amplifiedCutoff_le_one,
      amplified⟩
  have queryLoss_pos : 0 < queryLoss := by
    dsimp only [queryLoss]
    exact data.m8.outer.loss_pos (outerIndex + 1) (by omega)
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := (1 / 2 : ℝ))
      (s := queryLoss * discreteLoss / 2) (by norm_num)
      (mul_pos (mul_pos queryLoss_pos
        (data.m8.outer.oneQuery outerIndex houter).gridSchedule.discrete_loss_pos)
        (by norm_num)) with
    ⟨queryPowerCutoff, queryPowerCutoff_pos, queryPowerCutoff_le_one,
      query_power_small⟩
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := (1 / 4 : ℝ)) (s := queryLoss) (by norm_num)
      queryLoss_pos with
    ⟨queryCutoff, queryCutoff_pos, queryCutoff_le_one, query_small⟩
  let delta₀ := min amplifiedCutoff (min queryPowerCutoff queryCutoff)
  exact ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min amplifiedCutoff_pos <|
      lt_min queryPowerCutoff_pos queryCutoff_pos
    delta₀_le_one := (min_le_left _ _).trans amplifiedCutoff_le_one
    amplified_endpoint := by
      intro rho rho_pos rho_le
      calc
        (64 * (lipschitzExtensionConstant Point3 : ℝ)) *
            Real.rpow rho
              (data.m8.outer.loss (outerIndex + 1) *
                  (data.m8.outer.oneQuery outerIndex houter).gridSchedule.discreteLoss / 2 -
                data.lemma47Loss) ≤ Real.rpow rho 0 := by
          simpa only [queryLoss, discreteLoss] using
            amplified rho rho_pos (rho_le.trans (min_le_left _ _))
        _ = 1 := Real.rpow_zero rho
    query_power_endpoint := by
      intro rho rho_pos rho_le
      simpa only [queryLoss, discreteLoss] using
        query_power_small rho rho_pos <| rho_le.trans <|
          (min_le_right _ _).trans (min_le_left _ _)
    query_endpoint := by
      intro rho rho_pos rho_le
      exact query_small rho rho_pos
        (rho_le.trans <| (min_le_right _ _).trans (min_le_right _ _))
  }⟩

/-- Loss-only fine-scale witnesses for one ordered pair. -/
structure Proposition63M9PairFineCutoffData
    {sigma gridOutputLoss : ℝ}
    (schedule : Proposition63Lemma411ScheduleData sigma gridOutputLoss)
    (pairIndex : ℕ)
    (hpair : pairIndex <
      (finiteIntervalOrderedPairs schedule.gridSchedule.gridN).length) where
  currentReentryAbsorption : Proposition63CurrentReentryAbsorptionData
    schedule.rootSourceLoss schedule.backward.rootNormalizationLoss
    schedule.backward.rootDensityLoss (schedule.backward.loss pairIndex)
    (schedule.backward.currentWeightLoss pairIndex hpair)
    (schedule.backward.seed pairIndex hpair).schedule.first.sourceLoss
    (proposition63CanonicalNearbyLevelCount
      schedule.backward.rootNormalizationLoss)
  finalCandidateLiftAbsorption : Proposition63ReentryDensityLiftAbsorptionData
    (schedule.backward.currentWeightLoss pairIndex hpair)
    (schedule.backward.seed pairIndex hpair).goodCellCandidateLoss
    (schedule.backward.loss (pairIndex + 1))
    (proposition63CanonicalNearbyLevelCount
      schedule.backward.rootNormalizationLoss)
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_current : delta₀ ≤ currentReentryAbsorption.delta₀
  delta₀_le_final : delta₀ ≤ finalCandidateLiftAbsorption.delta₀
  delta₀_le_aligned :
    delta₀ ≤ (schedule.backward.seed pairIndex hpair).alignedAbsorption.delta₀

/-- The canonical fine cutoff for one ordered pair. -/
noncomputable def proposition63M9PairFineCutoffData
    {sigma gridOutputLoss : ℝ}
    (schedule : Proposition63Lemma411ScheduleData sigma gridOutputLoss)
    (pairIndex : ℕ)
    (hpair : pairIndex <
      (finiteIntervalOrderedPairs schedule.gridSchedule.gridN).length) :
    Proposition63M9PairFineCutoffData schedule pairIndex hpair := by
  have source_lt_density :
      schedule.rootSourceLoss < schedule.backward.rootDensityLoss := by
    dsimp [Proposition63Lemma411ScheduleData.rootSourceLoss,
      Proposition63FourCallInnerBackwardLossSchedule.rootDensityLoss,
      Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss]
    linarith [schedule.backward.rootBudget_pos]
  let current := proposition63_four_call_inner_current_reentry_absorption_at
    schedule.backward source_lt_density pairIndex hpair
  let final := proposition63_four_call_inner_final_lift_absorption_at
    schedule.backward pairIndex hpair
  let aligned := (schedule.backward.seed pairIndex hpair).alignedAbsorption
  let delta₀ := min current.delta₀ (min final.delta₀ aligned.delta₀)
  exact {
    currentReentryAbsorption := current
    finalCandidateLiftAbsorption := final
    delta₀ := delta₀
    delta₀_pos := lt_min current.delta₀_pos <|
      lt_min final.delta₀_pos aligned.delta₀_pos
    delta₀_le_one := (min_le_left _ _).trans current.delta₀_le_one
    delta₀_le_current := min_le_left _ _
    delta₀_le_final :=
      (min_le_right _ _).trans (min_le_left _ _)
    delta₀_le_aligned :=
      (min_le_right _ _).trans (min_le_right _ _)
  }

/-- The three fixed terminal payments of Lemma 4.12, together with its
explicit small-scale hypothesis. -/
structure Proposition63M9Lemma412CutoffData
    {sigma outputLoss : ℝ}
    (data : Proposition63M9PreRuntimeHierarchy sigma outputLoss) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  rho_small : delta₀ ≤ 1 / 24
  residue : ∀ {rho : ℝ}, 0 < rho → rho ≤ delta₀ →
    27 * Kakeya.realRpowENN rho data.preGrainLoss ≤
      Kakeya.realRpowENN rho data.gridLoss
  interpolation : ∀ {rho : ℝ}, 0 < rho → rho ≤ delta₀ →
    (100 : ℝ) * Real.rpow rho
        (-data.gridLoss - data.midLoss - 1 / (data.N : ℝ)) ≤
      Real.rpow rho (-data.preGrainLoss)
  fine : ∀ {rho : ℝ}, 0 < rho → rho ≤ delta₀ →
    (100 : ℝ) * Real.rpow rho
        (-data.midLoss - 1 / (data.N : ℝ)) ≤
      Real.rpow rho (-data.preGrainLoss)

/-- One fixed coefficient dominating both logarithmic cardinality envelopes
which occur in the first sampled-fiber regularization. -/
def proposition63M9SampledFiberLogCoefficient : ℝ :=
  max proposition63OneScaleLogCoefficient wz2PaperBoundaryLogCoefficient

def proposition63M9SampledFiberLogEnvelope (delta : ℝ) : ENNReal :=
  ENNReal.ofReal
    (proposition63M9SampledFiberLogCoefficient *
      (1 + Real.log delta⁻¹))

theorem proposition63M9SampledFiberLogCoefficient_nonneg :
    0 ≤ proposition63M9SampledFiberLogCoefficient :=
  proposition63OneScaleLogCoefficient_nonneg.trans
    (le_max_left _ _)

/-- Family-free small-scale absorption for the first sampled complete-fiber
regularization.  The degree branch uses the full output gap `8b`; after the
canonical fiber weight cancels, the mass branch has exactly three ambient
copies `rho^(-b)` and therefore uses only the remaining `5b`. -/
structure Proposition63M9SampledFiberAbsorptionData
    (stickyLoss : ℝ) (levelCount : ℕ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_tiny : delta₀ ≤ 1 / 100000
  degree_absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    (16 : ENNReal) * ((levelCount + 1 : ℕ) : ENNReal) *
        proposition63M9SampledFiberLogEnvelope delta ^ (levelCount + 1) ≤
      Kakeya.realRpowENN delta (-(8 * stickyLoss * stickyLoss))
  mass_absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    ((256 : ENNReal) *
        ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
        ((levelCount + 1 : ℕ) : ENNReal)) *
        proposition63M9SampledFiberLogEnvelope delta ^
          (2 * levelCount + 4) ≤
      Kakeya.realRpowENN delta (-(5 * stickyLoss * stickyLoss))
  source_mass_absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    (8 : ENNReal) * proposition63M9SampledFiberLogEnvelope delta ^
        (levelCount + 64) ≤
      Kakeya.realRpowENN delta (-stickyLoss)

/-- Root-scale smallness needed by the one-coordinate finite-planiness step
on the first regularized fine family.  The two power comparisons are exactly
the nearby-cover and sparse-incidence payments after the aligned coarse scale
is bounded below by half of its upper power-window endpoint. -/
structure Proposition63M9SampledPlaninessCutoffData
    (sigma planinessLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_small : delta₀ ≤ 1 / 24
  planiness_small : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    Kakeya.realRpowENN delta planinessLoss < 1 / 4
  fixed_absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
      Kakeya.realRpowENN delta (-sigma + 4 * planinessLoss)
  nearby_gap : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    128 * Real.rpow delta (1 - planinessLoss) ≤
      Real.rpow delta (planinessLoss / 2)
  sparse_incidence : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    64 * Real.rpow delta (sigma - (17 / 2 : ℝ) * planinessLoss) ≤
      Real.rpow delta planinessLoss

/-- Freeze all family-independent scalar payments for the first sampled
finite-planiness call before the critical sequence chooses its root scale. -/
theorem proposition63_m9_sampled_planiness_cutoff
    {sigma planinessLoss : ℝ}
    (hplaniness : 0 < planinessLoss)
    (hsigmaOne : sigma < 1)
    (hplaninessSigma : (19 / 2 : ℝ) * planinessLoss < sigma) :
    Nonempty (Proposition63M9SampledPlaninessCutoffData
      sigma planinessLoss) := by
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := (1 / 8 : ℝ)) (s := planinessLoss)
      (by norm_num) hplaniness with
    ⟨smallDelta, smallDeltaPos, smallDeltaOne, smallBound⟩
  have fixedGap : 0 < sigma - 4 * planinessLoss := by
    linarith [hplaniness]
  rcases exists_delta_realRpowENN_bound
      ((288 : ENNReal) * ENNReal.ofReal Real.pi)
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) fixedGap with
    ⟨fixedDelta, fixedDeltaPos, fixedDeltaOne, fixedBound⟩
  have nearbyGap : planinessLoss / 2 < 1 - planinessLoss := by
    have planinessLtOne : planinessLoss < 1 := by
      linarith [hplaninessSigma]
    linarith
  rcases exists_delta_mul_rpow_le_rpow (128 : ℝ) (by norm_num)
      nearbyGap with
    ⟨nearbyDelta, nearbyDeltaPos, nearbyDeltaOne, nearbyBound⟩
  have sparseGap : planinessLoss <
      sigma - (17 / 2 : ℝ) * planinessLoss := by
    linarith
  rcases exists_delta_mul_rpow_le_rpow (64 : ℝ) (by norm_num)
      sparseGap with
    ⟨sparseDelta, sparseDeltaPos, sparseDeltaOne, sparseBound⟩
  let delta₀ := min smallDelta <| min fixedDelta <|
    min nearbyDelta <| min sparseDelta (1 / 24)
  exact ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min smallDeltaPos <| lt_min fixedDeltaPos <|
      lt_min nearbyDeltaPos <| lt_min sparseDeltaPos (by norm_num)
    delta₀_le_one := (min_le_left _ _).trans smallDeltaOne
    delta₀_le_small := (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _)
    planiness_small := by
      intro delta deltaPos deltaLe
      have bound := smallBound delta deltaPos (deltaLe.trans (min_le_left _ _))
      have strict : Real.rpow delta planinessLoss < 1 / 4 :=
        bound.trans_lt (by norm_num)
      have hquarter : (1 / 4 : ENNReal) =
          ENNReal.ofReal (1 / 4 : ℝ) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
      rw [hquarter]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 strict
    fixed_absorb := by
      intro delta deltaPos deltaLe
      simpa only [show -(sigma - 4 * planinessLoss) =
          -sigma + 4 * planinessLoss by ring] using
        fixedBound delta deltaPos <| deltaLe.trans <|
          (min_le_right _ _).trans (min_le_left _ _)
    nearby_gap := by
      intro delta deltaPos deltaLe
      exact nearbyBound delta deltaPos <| deltaLe.trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans
          (min_le_left _ _)
    sparse_incidence := by
      intro delta deltaPos deltaLe
      exact sparseBound delta deltaPos <| deltaLe.trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
  }⟩

/-- Select the sampled-fiber absorption threshold before the root scale and
the two runtime families are known. -/
theorem proposition63_m9_sampled_fiber_absorption
    (stickyLoss : ℝ) (levelCount : ℕ)
    (stickyLoss_pos : 0 < stickyLoss) :
    Nonempty (Proposition63M9SampledFiberAbsorptionData
      stickyLoss levelCount) := by
  let degreeFixed : ENNReal :=
    (16 : ENNReal) * ((levelCount + 1 : ℕ) : ENNReal)
  have degreeFixedTop : degreeFixed ≠ ⊤ := by
    dsimp only [degreeFixed]
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)
  have degreeGapPos : 0 < 8 * stickyLoss * stickyLoss := by positivity
  rcases exists_delta_C_pow_log_absorbed_ennreal
      degreeFixed degreeFixedTop proposition63M9SampledFiberLogCoefficient
      proposition63M9SampledFiberLogCoefficient_nonneg degreeGapPos
      (show 0 < levelCount + 1 by omega) with
    ⟨degreeDelta, degreeDeltaPos, degreeDeltaOne, degreeAbsorb⟩
  let geometry : ENNReal :=
    (55296 : ENNReal) * Kakeya.deltaTubeVolume 1
  let massFixed : ENNReal :=
    (256 : ENNReal) * geometry * ((levelCount + 1 : ℕ) : ENNReal)
  have geometryTop : geometry ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top
  have massFixedTop : massFixed ≠ ⊤ := by
    dsimp only [massFixed]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) geometryTop)
      (ENNReal.natCast_ne_top _)
  have massGapPos : 0 < 5 * stickyLoss * stickyLoss := by positivity
  rcases exists_delta_C_pow_log_absorbed_ennreal
      massFixed massFixedTop proposition63M9SampledFiberLogCoefficient
      proposition63M9SampledFiberLogCoefficient_nonneg massGapPos
      (show 0 < 2 * levelCount + 4 by omega) with
    ⟨massDelta, massDeltaPos, massDeltaOne, massAbsorb⟩
  rcases exists_delta_C_pow_log_absorbed_ennreal
      (8 : ENNReal) (by norm_num) proposition63M9SampledFiberLogCoefficient
      proposition63M9SampledFiberLogCoefficient_nonneg stickyLoss_pos
      (show 0 < levelCount + 64 by omega) with
    ⟨sourceMassDelta, sourceMassDeltaPos, sourceMassDeltaOne,
      sourceMassAbsorb⟩
  let delta₀ := min degreeDelta <|
    min massDelta <| min sourceMassDelta (1 / 100000)
  exact ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min degreeDeltaPos <|
      lt_min massDeltaPos <| lt_min sourceMassDeltaPos (by norm_num)
    delta₀_le_one := (min_le_left _ _).trans degreeDeltaOne
    delta₀_le_tiny := (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_right _ _)
    degree_absorb := by
      intro delta deltaPos deltaLe
      simpa [degreeFixed, proposition63M9SampledFiberLogEnvelope] using
        degreeAbsorb delta deltaPos (deltaLe.trans (min_le_left _ _))
    mass_absorb := by
      intro delta deltaPos deltaLe
      simpa [massFixed, geometry, proposition63M9SampledFiberLogEnvelope] using
        massAbsorb delta deltaPos <|
          deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
    source_mass_absorb := by
      intro delta deltaPos deltaLe
      simpa [proposition63M9SampledFiberLogEnvelope] using
        sourceMassAbsorb delta deltaPos <|
          deltaLe.trans <| (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_left _ _)
  }⟩

theorem proposition63_m9_lemma412_cutoff
    {sigma outputLoss : ℝ}
    (data : Proposition63M9PreRuntimeHierarchy sigma outputLoss) :
    Nonempty (Proposition63M9Lemma412CutoffData data) := by
  have residue_gap : 0 < data.preGrainLoss - data.gridLoss := by
    rw [data.gridLoss_eq]
    linarith [data.preGrain_pos]
  rcases exists_delta_realRpowENN_bound (27 : ENNReal) (by norm_num)
      residue_gap with
    ⟨residueCutoff, residueCutoff_pos, residueCutoff_le_one,
      residue_bound⟩
  have interpolation_gap :
      -data.preGrainLoss <
        -data.gridLoss - data.midLoss - 1 / (data.N : ℝ) := by
    have reciprocal_lt : (1 : ℝ) / data.N < data.gridLoss :=
      data.one_over_N_lt_grid
    rw [data.gridLoss_eq] at reciprocal_lt
    rw [data.gridLoss_eq, data.midLoss_eq]
    linarith [data.preGrain_pos]
  rcases exists_delta_mul_rpow_le_rpow (100 : ℝ) (by norm_num)
      interpolation_gap with
    ⟨interpolationCutoff, interpolationCutoff_pos,
      interpolationCutoff_le_one, interpolation_bound⟩
  have fine_gap :
      -data.preGrainLoss <
        -data.midLoss - 1 / (data.N : ℝ) := by
    have reciprocal_lt : (1 : ℝ) / data.N < data.gridLoss :=
      data.one_over_N_lt_grid
    rw [data.gridLoss_eq] at reciprocal_lt
    rw [data.midLoss_eq]
    linarith [data.preGrain_pos]
  rcases exists_delta_mul_rpow_le_rpow (100 : ℝ) (by norm_num)
      fine_gap with
    ⟨fineCutoff, fineCutoff_pos, fineCutoff_le_one, fine_bound⟩
  let delta₀ := min residueCutoff <| min interpolationCutoff <|
    min fineCutoff (1 / 24)
  exact ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min residueCutoff_pos <|
      lt_min interpolationCutoff_pos <| lt_min fineCutoff_pos (by norm_num)
    delta₀_le_one := (min_le_left _ _).trans residueCutoff_le_one
    rho_small :=
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (le_refl _)
    residue := by
      intro rho rho_pos rho_le
      have fixed := residue_bound rho rho_pos
        (rho_le.trans (min_le_left _ _))
      calc
        27 * Kakeya.realRpowENN rho data.preGrainLoss ≤
            Kakeya.realRpowENN rho
                (-(data.preGrainLoss - data.gridLoss)) *
              Kakeya.realRpowENN rho data.preGrainLoss := by gcongr
        _ = Kakeya.realRpowENN rho data.gridLoss := by
          rw [← realRpowENN_add rho_pos]
          congr 1
          ring
    interpolation := by
      intro rho rho_pos rho_le
      exact interpolation_bound rho rho_pos <| rho_le.trans <|
        (min_le_right _ _).trans (min_le_left _ _)
    fine := by
      intro rho rho_pos rho_le
      exact fine_bound rho rho_pos <| rho_le.trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans
          (min_le_left _ _)
  }⟩

/-- Every loss-only cutoff needed by the second sticky call, Lemma 4.7, all
central Lemma 4.11 calls, and the Lemma 4.12 endpoint.  No field depends on
the root scale, an extremal family, or a current shading. -/
structure Proposition63M9PreNode3CutoffData
    {sigma outputLoss : ℝ}
    (data : Proposition63M9PreRuntimeHierarchy sigma outputLoss) where
  richSchedule : Proposition63RichStickyKernelScheduleData sigma data.stickyLoss
  twoCall : Proposition63M9TwoCallRobustScheduleData sigma data.stickyLoss
  twoCall_second : twoCall.schedule.second = richSchedule
  power : Proposition63M9PowerCutoffFamilyData data
  queryCutoff : ∀ outerIndex
    (houter : outerIndex < data.m8.centralTemplate.count),
      Proposition63M9QueryCutoffData data outerIndex houter
  rootCutoff : ∀ outerIndex
    (houter : outerIndex < data.m8.centralTemplate.count),
      Proposition63M9RootBindingCutoffData
        (data.m8.outer.oneQuery outerIndex houter)
  pairFineCutoff : ∀ outerIndex
    (houter : outerIndex < data.m8.centralTemplate.count),
    ∀ pairIndex (hpair : pairIndex <
      (finiteIntervalOrderedPairs
        (data.m8.outer.oneQuery outerIndex houter).gridSchedule.gridN).length),
      Proposition63M9PairFineCutoffData
        (data.m8.outer.oneQuery outerIndex houter) pairIndex hpair
  pairFineCommon : ∀ outerIndex
    (houter : outerIndex < data.m8.centralTemplate.count),
      Proposition63FinitePositiveCutoff
        (finiteIntervalOrderedPairs
          (data.m8.outer.oneQuery outerIndex houter).gridSchedule.gridN).length
        (fun pairIndex hpair =>
          (pairFineCutoff outerIndex houter pairIndex hpair).delta₀)
  coordinateCommon : Proposition63FinitePositiveCutoff
    data.m8.centralTemplate.count
    (fun outerIndex houter =>
      min (queryCutoff outerIndex houter).delta₀ <|
      min (rootCutoff outerIndex houter).delta₀ <|
      min (data.m8.outer.oneQuery outerIndex houter).gridSchedule.delta₀
        (pairFineCommon outerIndex houter).delta₀)
  lemma412Cutoff : Proposition63M9Lemma412CutoffData data
  initial : Proposition63InitialLossHierarchy sigma richSchedule.sourceLoss
  firstChartCutoff : Proposition63M9FirstChartCutoffData
    twoCall.schedule.first.sourceLoss initial.stickyLoss
  initial_lemma43_lt_firstSource :
    initial.lemma43SourceLoss < twoCall.schedule.first.sourceLoss
  initial_lemma43_lt_firstChartNearby :
    initial.lemma43SourceLoss < firstChartCutoff.nearbyInputLoss
  initial_local_global_gap :
    4 * initial.localLoss < (sigma / (2 + sigma)) * data.preGrainLoss
  globalADAbsorption :
    Proposition63ChartSelectionData.Proposition63M9CoarseGlobalAbsorptionCutoffData
      initial.localLoss
  robustFirstRootScale : ℝ
  robustFirstRootScale_pos : 0 < robustFirstRootScale
  robustFirstRootScale_le_one : robustFirstRootScale ≤ 1
  robustFirst_root_power_le : ∀ {delta : ℝ}, 0 < delta →
    delta ≤ robustFirstRootScale →
      Real.rpow delta initial.stickyLoss ≤ twoCall.rootCutoff
  sameExtremizerRootNormalizationLoss : ℝ
  sameExtremizerRootNormalizationLoss_eq :
    sameExtremizerRootNormalizationLoss = richSchedule.sourceLoss / 16
  initial_lemma43_le_sameExtremizerRoot_half :
    initial.lemma43SourceLoss ≤ sameExtremizerRootNormalizationLoss / 2
  sameExtremizer : Proposition63M9SameExtremizerCutoffData
    initial.lemma43SourceLoss sameExtremizerRootNormalizationLoss
    richSchedule.sourceLoss
  sameExtremizerRootScale : ℝ
  sameExtremizerRootScale_pos : 0 < sameExtremizerRootScale
  sameExtremizerRootScale_le_one : sameExtremizerRootScale ≤ 1
  sameExtremizer_root_power_le : ∀ {delta : ℝ}, 0 < delta →
    delta ≤ sameExtremizerRootScale →
    Real.rpow delta initial.stickyLoss ≤ sameExtremizer.absorption.delta₀
  sameExtremizer_restore_root_power_le : ∀ {delta : ℝ}, 0 < delta →
    delta ≤ sameExtremizerRootScale →
    Real.rpow delta initial.stickyLoss ≤ sameExtremizer.lemma43Restore.delta₀
  firstRichSchedule :
    Proposition63RichStickyKernelScheduleData sigma initial.stickyLoss
  preliminaryStickyLoss : ℝ
  planinessLoss : ℝ
  preliminaryProducerLoss : ℝ
  sampledM8 : Proposition63M9PreliminaryM8ScheduleData
    sigma preliminaryProducerLoss initial.localLoss
  sampledM8RootLosses : Proposition63M9PreliminaryRootLossData
    sampledM8 firstRichSchedule.sourceLoss
  sampledM8Cutoff : Proposition63M9PreliminaryOuterCutoffData
    sampledM8 sampledM8RootLosses
  sampledFiberAbsorption : Proposition63M9SampledFiberAbsorptionData
    sampledM8RootLosses.stickyLoss
    (proposition63CanonicalNearbyLevelCount
      sampledM8RootLosses.stickyLoss)
  sampledPlaninessCutoff : Proposition63M9SampledPlaninessCutoffData
    sigma planinessLoss
  preliminaryStickyLoss_eq :
    preliminaryStickyLoss = sampledM8RootLosses.stickyLoss
  planinessLoss_eq :
    planinessLoss = sampledM8RootLosses.planinessLoss
  preliminaryProducerLoss_eq :
    preliminaryProducerLoss = firstRichSchedule.sourceLoss / 8
  preliminaryStickyLoss_pos : 0 < preliminaryStickyLoss
  preliminaryStickyLoss_lt_planiness :
    preliminaryStickyLoss < planinessLoss
  planinessLoss_lt_producer : planinessLoss < preliminaryProducerLoss
  preliminaryProducerLoss_lt_firstSource :
    preliminaryProducerLoss < firstRichSchedule.sourceLoss
  planinessLoss_lt_sigma_quarter : planinessLoss < sigma / 4
  preliminaryAnalytic : Proposition63PreliminaryAnalyticSchedule
    sigma preliminaryStickyLoss planinessLoss
  firstChartDensity : Proposition63M9FirstChartDensityCutoffData
    sigma initial.stickyLoss initial.localLoss initial.lemma43SourceLoss
  firstChartTraceGap :
    sigma * initial.stickyLoss +
        (1 + sigma / 2) * firstRichSchedule.sourceLoss <
      initial.lemma43SourceLoss
  firstChartTraceDensity : Proposition63M9FirstChartTraceDensityCutoffData
    sigma initial.stickyLoss firstRichSchedule.sourceLoss
      initial.lemma43SourceLoss
  firstChartRootScale : ℝ
  firstChartRootScale_pos : 0 < firstChartRootScale
  firstChartRootScale_le_one : firstChartRootScale ≤ 1
  firstChartRootScale_le_cutoffRoot :
    firstChartRootScale ≤ firstChartCutoff.rootCutoff
  firstChart_root_power_le : ∀ {delta : ℝ}, 0 < delta →
    delta ≤ firstChartRootScale →
      Real.rpow delta (sigma / (2 + sigma)) ≤
        firstChartDensity.delta₀
  firstChart_trace_root_power_le : ∀ {delta : ℝ}, 0 < delta →
    delta ≤ firstChartRootScale →
      Real.rpow delta (sigma / (2 + sigma)) ≤
        firstChartTraceDensity.delta₀
  preliminaryRootSourceLoss : ℝ
  preliminaryRootNormalizationLoss : ℝ
  preliminaryReentryDensityLoss : ℝ
  preliminaryReentryWeightLoss : ℝ
  preliminaryRootSourceLoss_eq :
    preliminaryRootSourceLoss = preliminaryStickyLoss / 2
  preliminaryRootNormalizationLoss_eq :
    preliminaryRootNormalizationLoss = preliminaryStickyLoss
  preliminaryReentryDensityLoss_eq :
    preliminaryReentryDensityLoss = firstRichSchedule.sourceLoss / 16
  preliminaryReentryWeightLoss_eq :
    preliminaryReentryWeightLoss = firstRichSchedule.sourceLoss / 2
  preliminaryReentryAbsorption : Proposition63CurrentReentryAbsorptionData
    preliminaryRootSourceLoss preliminaryRootNormalizationLoss
    preliminaryReentryDensityLoss preliminaryProducerLoss
    preliminaryReentryWeightLoss firstRichSchedule.sourceLoss
    (proposition63CanonicalNearbyLevelCount
      preliminaryRootNormalizationLoss)
  alignedRootScale :
    Proposition63AlignedPowerWindowCutoffData preliminaryStickyLoss
  sampledFiberScale : ℝ
  sampledFiberScale_pos : 0 < sampledFiberScale
  sampledFiberScale_le_one : sampledFiberScale ≤ 1
  sampledFiber_ambient : ∀ {rho : ℝ}, 0 < rho → rho ≤ sampledFiberScale →
    (3 : ENNReal) ≤ Kakeya.realRpowENN rho (-preliminaryStickyLoss)

/-- The common outer-scale threshold.  It is deliberately a threshold for
the coarse scale selected by the root realization, not for the finer root
scale itself. -/
noncomputable def Proposition63M9PreNode3CutoffData.outerScaleCeiling
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) : ℝ :=
  min cutoff.richSchedule.delta₀ <|
  min data.lemma47Schedule.delta₀ <|
  min cutoff.power.outerCutoff.delta₀ <|
  min cutoff.coordinateCommon.delta₀ <|
  min cutoff.lemma412Cutoff.delta₀ <|
  min cutoff.firstRichSchedule.delta₀ <|
  min cutoff.preliminaryAnalytic.propertyPScale <|
  min cutoff.preliminaryAnalytic.sparseCVScale <|
  min cutoff.preliminaryReentryAbsorption.delta₀ <|
    min cutoff.alignedRootScale.delta₀ <|
    min cutoff.sampledM8Cutoff.delta₀ <|
      min cutoff.sampledFiberScale <|
        min cutoff.sampledFiberAbsorption.delta₀
          (min cutoff.sampledPlaninessCutoff.delta₀
            (min cutoff.sameExtremizerRootScale
              (min cutoff.sampledM8RootLosses.sampledFirstRichAbsorption.delta₀
                (min cutoff.firstChartRootScale
                  (min cutoff.robustFirstRootScale
                    cutoff.globalADAbsorption.delta₀)))))

/-- Node 3 selects the root scale below the square of the desired coarse
ceiling; its canonical realized scale is the square root of that root scale. -/
noncomputable def Proposition63M9PreNode3CutoffData.scaleCeiling
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) : ℝ :=
  min ((cutoff.outerScaleCeiling / 2) ^ 2)
    (Real.rpow cutoff.outerScaleCeiling
      (1 / cutoff.preliminaryStickyLoss))

theorem proposition63_m9_pre_node3_cutoff
    {sigma outputLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (data : Proposition63M9PreRuntimeHierarchy sigma outputLoss) :
    Nonempty (Proposition63M9PreNode3CutoffData data) := by
  have sticky_le_one : data.stickyLoss ≤ 1 :=
    data.sticky_le_sigma_half.trans (by
      linarith [critical.sigma_lt_one])
  rcases proposition63_rich_sticky_kernel sigma critical data.stickyLoss
      data.sticky_pos sticky_le_one with ⟨richSchedule⟩
  rcases proposition63_m9_two_call_robust_schedule_of_second
      sigma critical richSchedule data.sticky_le_sigma_half
      data.sigma_half_le_one_sub_sticky with ⟨twoCall, twoCallSecond⟩
  rcases proposition63_m9_power_cutoff_family data with ⟨power⟩
  let queryCutoff : ∀ outerIndex
      (houter : outerIndex < data.m8.centralTemplate.count),
        Proposition63M9QueryCutoffData data outerIndex houter :=
    fun outerIndex houter => Classical.choice <|
      proposition63_m9_query_cutoff data outerIndex houter
  let rootCutoff : ∀ outerIndex
      (houter : outerIndex < data.m8.centralTemplate.count),
        Proposition63M9RootBindingCutoffData
          (data.m8.outer.oneQuery outerIndex houter) :=
    fun outerIndex houter => Classical.choice <|
      proposition63_m9_root_binding_cutoff
        (data.m8.outer.oneQuery outerIndex houter)
  let pairFineCutoff : ∀ outerIndex
      (houter : outerIndex < data.m8.centralTemplate.count),
      ∀ pairIndex (hpair : pairIndex <
        (finiteIntervalOrderedPairs
          (data.m8.outer.oneQuery outerIndex houter).gridSchedule.gridN).length),
        Proposition63M9PairFineCutoffData
          (data.m8.outer.oneQuery outerIndex houter) pairIndex hpair :=
    fun outerIndex houter pairIndex hpair =>
      proposition63M9PairFineCutoffData
        (data.m8.outer.oneQuery outerIndex houter) pairIndex hpair
  let pairFineCommon : ∀ outerIndex
      (houter : outerIndex < data.m8.centralTemplate.count),
        Proposition63FinitePositiveCutoff
          (finiteIntervalOrderedPairs
            (data.m8.outer.oneQuery outerIndex houter).gridSchedule.gridN).length
          (fun pairIndex hpair =>
            (pairFineCutoff outerIndex houter pairIndex hpair).delta₀) :=
    fun outerIndex houter => Classical.choice <|
      proposition63_finite_positive_cutoff
        (finiteIntervalOrderedPairs
          (data.m8.outer.oneQuery outerIndex houter).gridSchedule.gridN).length
        (fun pairIndex hpair =>
          (pairFineCutoff outerIndex houter pairIndex hpair).delta₀)
        (fun pairIndex hpair =>
          (pairFineCutoff outerIndex houter pairIndex hpair).delta₀_pos)
  let coordinateThreshold : ∀ outerIndex,
      outerIndex < data.m8.centralTemplate.count → ℝ :=
    fun outerIndex houter =>
      min (queryCutoff outerIndex houter).delta₀ <|
      min (rootCutoff outerIndex houter).delta₀ <|
      min (data.m8.outer.oneQuery outerIndex houter).gridSchedule.delta₀
        (pairFineCommon outerIndex houter).delta₀
  have coordinateThreshold_pos : ∀ outerIndex,
      ∀ houter : outerIndex < data.m8.centralTemplate.count,
        0 < coordinateThreshold outerIndex houter := by
    intro outerIndex houter
    exact lt_min (queryCutoff outerIndex houter).delta₀_pos <|
      lt_min (rootCutoff outerIndex houter).delta₀_pos <|
        lt_min
          (data.m8.outer.oneQuery outerIndex houter).gridSchedule.delta₀_pos
          (pairFineCommon outerIndex houter).delta₀_pos
  let coordinateCommon := Classical.choice <|
    proposition63_finite_positive_cutoff data.m8.centralTemplate.count
      coordinateThreshold coordinateThreshold_pos
  rcases proposition63_m9_lemma412_cutoff data with ⟨lemma412Cutoff⟩
  have firstChartTargetLeOne : twoCall.schedule.first.sourceLoss ≤ 1 := by
    nlinarith [twoCall.schedule.first.sourceLoss_le_half,
      twoCall.schedule.first.normalizationLoss_lt_output,
      twoCall.firstOutputLoss_le_sigma_sixteenth,
      critical.sigma_lt_one]
  rcases proposition63_m9_firstChart_nearby_cutoff
      twoCall.schedule.first.sourceLoss_pos firstChartTargetLeOne with
    ⟨firstChartNearby⟩
  let initialBudget := min
    (min twoCall.schedule.first.sourceLoss
      firstChartNearby.nearbyInputLoss)
    ((sigma / (2 + sigma)) * data.preGrainLoss / 16)
  have initialBudgetPos : 0 < initialBudget :=
    lt_min
      (lt_min twoCall.schedule.first.sourceLoss_pos
        firstChartNearby.nearbyInputLoss_pos)
      (div_pos
        (mul_pos
          (div_pos critical.sigma_pos (by linarith [critical.sigma_pos]))
          data.preGrain_pos)
        (by norm_num))
  rcases proposition63_initial_loss_hierarchy critical.sigma_pos
      critical.sigma_lt_one initialBudgetPos with ⟨initialSmall⟩
  let initial : Proposition63InitialLossHierarchy sigma
      richSchedule.sourceLoss := {
    stickyLoss := initialSmall.stickyLoss
    localLoss := initialSmall.localLoss
    lemma43SourceLoss := initialSmall.lemma43SourceLoss
    sticky_pos := initialSmall.sticky_pos
    sticky_lt_local := initialSmall.sticky_lt_local
    local_lt_lemma43 := initialSmall.local_lt_lemma43
    lemma43SourceLoss_eq_three_sticky :=
      initialSmall.lemma43SourceLoss_eq_three_sticky
    lemma43_lt_secondInput := by
      calc
        initialSmall.lemma43SourceLoss <
            twoCall.schedule.first.sourceLoss :=
          initialSmall.lemma43_lt_secondInput.trans_le <|
            (min_le_left _ _).trans (min_le_left _ _)
        _ < twoCall.schedule.firstOutputLoss :=
          twoCall.schedule.first.sourceLoss_le_half.trans_lt <|
            (half_lt_self
              twoCall.schedule.first.normalizationLoss_pos).trans <|
                twoCall.schedule.first.normalizationLoss_lt_output
        _ = richSchedule.sourceLoss / 16 := by
          rw [twoCall.schedule.firstOutputLoss_eq, twoCallSecond]
        _ < richSchedule.sourceLoss := by
          linarith [richSchedule.sourceLoss_pos]
    sticky_le_power := initialSmall.sticky_le_power
    power_le_one_sub_sticky := initialSmall.power_le_one_sub_sticky
    lemma43_lt_sigma_quarter := initialSmall.lemma43_lt_sigma_quarter
  }
  rcases
      Proposition63ChartSelectionData.proposition63_m9_coarse_global_absorption_cutoff
        (initial.sticky_pos.trans initial.sticky_lt_local) with
    ⟨globalADAbsorption⟩
  rcases firstChartNearby.bindRootExponent initial.sticky_pos with
    ⟨firstChartCutoff, firstChartCutoffNearby⟩
  let sameExtremizerRootNormalizationLoss : ℝ :=
    richSchedule.sourceLoss / 16
  rcases pure_wz2_exists_delta₀_rpow_le
      twoCall.rootCutoff_pos initial.sticky_pos with
    ⟨robustFirstRootScale, robustFirstRootScalePos,
      robustFirstRootScaleOne, robustFirstRootPower⟩
  have sameExtremizerRootNormalizationLossPos :
      0 < sameExtremizerRootNormalizationLoss := by
    dsimp only [sameExtremizerRootNormalizationLoss]
    exact div_pos richSchedule.sourceLoss_pos (by norm_num)
  have initialLemma43LtThirtySecond :
      initial.lemma43SourceLoss < richSchedule.sourceLoss / 32 := by
    calc
      initial.lemma43SourceLoss < initialBudget :=
        initialSmall.lemma43_lt_secondInput
      _ ≤ twoCall.schedule.first.sourceLoss :=
        (min_le_left _ _).trans (min_le_left _ _)
      _ ≤ twoCall.schedule.first.normalizationLoss / 2 :=
        twoCall.schedule.first.sourceLoss_le_half
      _ < twoCall.schedule.firstOutputLoss / 2 := by
        linarith [twoCall.schedule.first.normalizationLoss_lt_output]
      _ = richSchedule.sourceLoss / 32 := by
        rw [twoCall.schedule.firstOutputLoss_eq, twoCallSecond]
        ring
  have initialLemma43LtEighth :
      initial.lemma43SourceLoss < richSchedule.sourceLoss / 8 := by
    linarith [richSchedule.sourceLoss_pos, initialLemma43LtThirtySecond]
  have sameExtremizerRootNormalizationLossLtEighth :
      sameExtremizerRootNormalizationLoss < richSchedule.sourceLoss / 8 := by
    dsimp only [sameExtremizerRootNormalizationLoss]
    linarith [richSchedule.sourceLoss_pos]
  rcases proposition63_m9_same_extremizer_cutoff
      initial.lemma43SourceLoss sameExtremizerRootNormalizationLoss
      richSchedule.sourceLoss richSchedule.sourceLoss_pos
      initialLemma43LtEighth sameExtremizerRootNormalizationLossPos
      sameExtremizerRootNormalizationLossLtEighth with ⟨sameExtremizer⟩
  let sameExtremizerCombinedCutoff : ℝ :=
    min sameExtremizer.absorption.delta₀ sameExtremizer.lemma43Restore.delta₀
  have sameExtremizerCombinedCutoffPos :
      0 < sameExtremizerCombinedCutoff := by
    dsimp only [sameExtremizerCombinedCutoff]
    exact lt_min sameExtremizer.absorption.delta₀_pos
      sameExtremizer.lemma43Restore.delta₀_pos
  rcases pure_wz2_exists_delta₀_rpow_le
      sameExtremizerCombinedCutoffPos initial.sticky_pos with
    ⟨sameExtremizerRootScale, sameExtremizerRootScalePos,
      sameExtremizerRootScaleOne, sameExtremizerRootPower⟩
  have initial_sticky_le_one : initial.stickyLoss ≤ 1 :=
    initial.sticky_le_power.trans <| by
      have denominator_pos : 0 < 2 + sigma := by
        linarith [critical.sigma_pos]
      rw [div_le_one denominator_pos]
      linarith
  rcases proposition63_rich_sticky_kernel sigma critical initial.stickyLoss
      initial.sticky_pos initial_sticky_le_one with ⟨firstRichSchedule⟩
  let preliminaryProducerLoss : ℝ := firstRichSchedule.sourceLoss / 8
  have preliminaryProducerPos : 0 < preliminaryProducerLoss := by
    dsimp only [preliminaryProducerLoss]
    exact div_pos firstRichSchedule.sourceLoss_pos (by norm_num)
  have preliminaryProducerLocal : preliminaryProducerLoss ≤
      initial.localLoss := by
    have firstSourceLtInitialSticky : firstRichSchedule.sourceLoss <
        initial.stickyLoss :=
      firstRichSchedule.sourceLoss_le_half.trans_lt <|
        (half_lt_self firstRichSchedule.normalizationLoss_pos).trans <|
          firstRichSchedule.normalizationLoss_lt_output
    dsimp only [preliminaryProducerLoss]
    linarith [firstRichSchedule.sourceLoss_pos,
      firstSourceLtInitialSticky, initial.sticky_lt_local]
  have preliminaryProducerSigma : preliminaryProducerLoss < sigma / 4 :=
    preliminaryProducerLocal.trans_lt <|
      initial.local_lt_lemma43.trans initial.lemma43_lt_sigma_quarter
  rcases proposition63_m9_preliminary_m8_schedule sigma critical
      preliminaryProducerLoss initial.localLoss preliminaryProducerPos
      preliminaryProducerLocal preliminaryProducerSigma with ⟨sampledM8⟩
  rcases proposition63_m9_preliminary_root_losses sampledM8
      firstRichSchedule.sourceLoss firstRichSchedule.sourceLoss_pos with
    ⟨sampledM8RootLosses⟩
  rcases proposition63_m9_preliminary_outer_cutoff sampledM8
      sampledM8RootLosses with ⟨sampledM8Cutoff⟩
  rcases proposition63_m9_sampled_fiber_absorption
      sampledM8RootLosses.stickyLoss
      (proposition63CanonicalNearbyLevelCount
        sampledM8RootLosses.stickyLoss)
      sampledM8RootLosses.stickyLoss_pos with
    ⟨sampledFiberAbsorption⟩
  let preliminaryStickyLoss : ℝ := sampledM8RootLosses.stickyLoss
  let planinessLoss : ℝ := sampledM8RootLosses.planinessLoss
  have preliminaryStickyLoss_pos : 0 < preliminaryStickyLoss := by
    exact sampledM8RootLosses.stickyLoss_pos
  have planinessLoss_pos : 0 < planinessLoss := by
    dsimp only [planinessLoss]
    rw [sampledM8RootLosses.planinessLoss_eq]
    positivity
  have planinessLoss_lt_sigma_quarter : planinessLoss < sigma / 4 := by
    have firstSourceLtInitialSticky : firstRichSchedule.sourceLoss <
        initial.stickyLoss :=
      firstRichSchedule.sourceLoss_le_half.trans_lt <|
        (half_lt_self firstRichSchedule.normalizationLoss_pos).trans <|
          firstRichSchedule.normalizationLoss_lt_output
    have firstSourceSigma : firstRichSchedule.sourceLoss < sigma / 4 :=
      firstSourceLtInitialSticky.trans <| initial.sticky_lt_local.trans <|
        initial.local_lt_lemma43.trans initial.lemma43_lt_sigma_quarter
    calc
      planinessLoss < sampledM8RootLosses.reentryNormalizationLoss := by
        dsimp only [planinessLoss]
        rw [sampledM8RootLosses.planinessLoss_eq,
          sampledM8RootLosses.reentryNormalizationLoss_eq]
        linarith [sampledM8RootLosses.stickyLoss_pos]
      _ < firstRichSchedule.sourceLoss :=
        sampledM8RootLosses.reentryNormalization_lt_nextSource
      _ < sigma / 4 := firstSourceSigma
  have planinessLoss_nineteen_half_lt_sigma :
      (19 / 2 : ℝ) * planinessLoss < sigma := by
    have firstSourceSigma : firstRichSchedule.sourceLoss < sigma / 4 :=
      firstRichSchedule.sourceLoss_le_half.trans_lt <|
        (half_lt_self firstRichSchedule.normalizationLoss_pos).trans <|
          firstRichSchedule.normalizationLoss_lt_output |>.trans <|
            initial.sticky_lt_local.trans <|
              initial.local_lt_lemma43.trans initial.lemma43_lt_sigma_quarter
    have small := sampledM8RootLosses.reentryNormalization_lt_nextSource
    rw [sampledM8RootLosses.reentryNormalizationLoss_eq] at small
    dsimp only [planinessLoss]
    rw [sampledM8RootLosses.planinessLoss_eq]
    nlinarith [sampledM8RootLosses.stickyLoss_pos, small, firstSourceSigma]
  rcases proposition63_m9_sampled_planiness_cutoff planinessLoss_pos
      critical.sigma_lt_one
      planinessLoss_nineteen_half_lt_sigma with
    ⟨sampledPlaninessCutoff⟩
  rcases proposition63_preliminary_analytic_schedule sigma
      preliminaryStickyLoss planinessLoss critical.sigma_pos
      critical.sigma_lt_one preliminaryStickyLoss_pos
      (by
        rw [show preliminaryStickyLoss = planinessLoss / 2 by
          dsimp only [preliminaryStickyLoss, planinessLoss]
          rw [sampledM8RootLosses.planinessLoss_eq]
          ring]
        linarith [planinessLoss_lt_sigma_quarter, critical.sigma_pos])
      planinessLoss_pos
    with ⟨preliminaryAnalytic⟩
  have sigmaInitialStickyLtLocal :
      sigma * initial.stickyLoss < initial.localLoss := by
    have sigmaStickyLt : sigma * initial.stickyLoss <
        initial.stickyLoss := by
      nlinarith [critical.sigma_lt_one, initial.sticky_pos]
    exact sigmaStickyLt.trans initial.sticky_lt_local
  have sigmaInitialStickyLtLemma43 :
      sigma * initial.stickyLoss < initial.lemma43SourceLoss :=
    sigmaInitialStickyLtLocal.trans initial.local_lt_lemma43
  rcases proposition63_m9_firstChart_density_cutoff
      sigmaInitialStickyLtLocal sigmaInitialStickyLtLemma43 with
    ⟨firstChartDensity⟩
  have firstRichSourceLtInitialSticky :
      firstRichSchedule.sourceLoss < initial.stickyLoss :=
    firstRichSchedule.sourceLoss_le_half.trans_lt <|
      (half_lt_self firstRichSchedule.normalizationLoss_pos).trans <|
        firstRichSchedule.normalizationLoss_lt_output
  have firstChartTraceGap :
      sigma * initial.stickyLoss +
          (1 + sigma / 2) * firstRichSchedule.sourceLoss <
        initial.lemma43SourceLoss := by
    have sigmaStickyLt :
        sigma * initial.stickyLoss < initial.stickyLoss := by
      nlinarith [critical.sigma_lt_one, initial.sticky_pos]
    have scaledInputLt :
        (1 + sigma / 2) * firstRichSchedule.sourceLoss <
          (3 / 2 : ℝ) * initial.stickyLoss := by
      have coefficientPos : 0 < 1 + sigma / 2 := by
        nlinarith [critical.sigma_pos]
      have coefficientLt : 1 + sigma / 2 < 3 / 2 := by
        linarith [critical.sigma_lt_one]
      have firstRichSourceLtHalf :
          firstRichSchedule.sourceLoss < initial.stickyLoss / 2 :=
        by
          linarith [firstRichSchedule.sourceLoss_le_half,
            firstRichSchedule.normalizationLoss_lt_output]
      nlinarith [firstRichSchedule.sourceLoss_pos, initial.sticky_pos]
    rw [initial.lemma43SourceLoss_eq_three_sticky]
    nlinarith [initial.sticky_pos]
  rcases proposition63_m9_firstChart_trace_density_cutoff
      critical.sigma_pos critical.sigma_lt_one
      firstRichSchedule.sourceLoss_pos firstChartTraceGap with
    ⟨firstChartTraceDensity⟩
  have firstChartPowerExponent : 0 < sigma / (2 + sigma) := by
    exact div_pos critical.sigma_pos (by linarith [critical.sigma_pos])
  rcases pure_wz2_exists_delta₀_rpow_le firstChartDensity.delta₀_pos
      firstChartPowerExponent with
    ⟨firstChartDensityRootScale, firstChartDensityRootScalePos,
      firstChartDensityRootScaleOne, firstChartDensityRootPower⟩
  rcases pure_wz2_exists_delta₀_rpow_le firstChartTraceDensity.delta₀_pos
      firstChartPowerExponent with
    ⟨firstChartTraceRootScale, firstChartTraceRootScalePos,
      firstChartTraceRootScaleOne, firstChartTraceRootPower⟩
  let firstChartRootScale :=
    min firstChartDensityRootScale <|
      min firstChartTraceRootScale firstChartCutoff.rootCutoff
  have firstChartRootScalePos : 0 < firstChartRootScale :=
    lt_min firstChartDensityRootScalePos <|
      lt_min firstChartTraceRootScalePos firstChartCutoff.rootCutoff_pos
  have firstChartRootScaleOne : firstChartRootScale ≤ 1 :=
    (min_le_left _ _).trans firstChartDensityRootScaleOne
  let preliminaryRootSourceLoss : ℝ := preliminaryStickyLoss / 2
  let preliminaryRootNormalizationLoss : ℝ := preliminaryStickyLoss
  let preliminaryReentryDensityLoss : ℝ :=
    firstRichSchedule.sourceLoss / 16
  let preliminaryReentryWeightLoss : ℝ := firstRichSchedule.sourceLoss / 2
  have preliminaryRootSource_lt_density : preliminaryRootSourceLoss <
      preliminaryReentryDensityLoss := by
    have small := sampledM8RootLosses.reentryNormalization_lt_nextSource
    rw [sampledM8RootLosses.reentryNormalizationLoss_eq] at small
    dsimp only [preliminaryRootSourceLoss, preliminaryStickyLoss,
      preliminaryReentryDensityLoss]
    linarith [sampledM8RootLosses.stickyLoss_pos]
  have density_current_lt_weight : preliminaryReentryDensityLoss +
      preliminaryProducerLoss < preliminaryReentryWeightLoss := by
    dsimp only [preliminaryReentryDensityLoss, preliminaryProducerLoss,
      preliminaryReentryWeightLoss]
    linarith [firstRichSchedule.sourceLoss_pos]
  have weight_lt_reentry : preliminaryReentryWeightLoss <
      firstRichSchedule.sourceLoss := by
    dsimp only [preliminaryReentryWeightLoss]
    linarith [firstRichSchedule.sourceLoss_pos]
  have regularization_gap : 0 < firstRichSchedule.sourceLoss -
      preliminaryReentryWeightLoss -
        2 * preliminaryRootNormalizationLoss := by
    have small := sampledM8RootLosses.reentryNormalization_lt_nextSource
    rw [sampledM8RootLosses.reentryNormalizationLoss_eq] at small
    dsimp only [preliminaryReentryWeightLoss,
      preliminaryRootNormalizationLoss, preliminaryStickyLoss]
    linarith [sampledM8RootLosses.stickyLoss_pos]
  rcases proposition63_current_reentry_absorption
      preliminaryRootSourceLoss preliminaryRootNormalizationLoss
      preliminaryReentryDensityLoss preliminaryProducerLoss
      preliminaryReentryWeightLoss firstRichSchedule.sourceLoss
      (proposition63CanonicalNearbyLevelCount
        preliminaryRootNormalizationLoss)
      preliminaryRootSource_lt_density preliminaryStickyLoss_pos
      density_current_lt_weight weight_lt_reentry
      (proposition63CanonicalNearbyLevelCount_pos preliminaryStickyLoss_pos)
      firstRichSchedule.sourceLoss_pos regularization_gap
    with ⟨preliminaryReentryAbsorption⟩
  have preliminary_sticky_half : preliminaryStickyLoss < 1 / 2 := by
    rw [show preliminaryStickyLoss = planinessLoss / 2 by
      dsimp only [preliminaryStickyLoss, planinessLoss]
      rw [sampledM8RootLosses.planinessLoss_eq]
      ring]
    linarith [planinessLoss_lt_sigma_quarter, critical.sigma_pos,
      critical.sigma_lt_one]
  rcases proposition63_aligned_power_window_cutoff preliminaryStickyLoss
      preliminaryStickyLoss_pos preliminary_sticky_half
    with ⟨alignedRootScale⟩
  rcases exists_delta_realRpowENN_bound (3 : ENNReal) (by norm_num)
      preliminaryStickyLoss_pos with
    ⟨sampledFiberScale, sampledFiberScalePos, sampledFiberScaleOne,
      sampledFiberAmbient⟩
  exact ⟨{
    richSchedule := richSchedule
    twoCall := twoCall
    twoCall_second := twoCallSecond
    power := power
    queryCutoff := queryCutoff
    rootCutoff := rootCutoff
    pairFineCutoff := pairFineCutoff
    pairFineCommon := pairFineCommon
    coordinateCommon := coordinateCommon
    lemma412Cutoff := lemma412Cutoff
    firstChartCutoff := firstChartCutoff
    initial := initial
    initial_lemma43_lt_firstSource :=
      initialSmall.lemma43_lt_secondInput.trans_le <|
        (min_le_left _ _).trans (min_le_left _ _)
    initial_lemma43_lt_firstChartNearby :=
      by
        rw [show firstChartCutoff.nearbyInputLoss =
            firstChartNearby.nearbyInputLoss by
          exact congrArg Proposition63M9FirstChartNearbyCutoffData.nearbyInputLoss
            firstChartCutoffNearby]
        exact initialSmall.lemma43_lt_secondInput.trans_le
          ((min_le_left _ _).trans (min_le_right _ _))
    initial_local_global_gap := by
      have budgetLe : initialBudget ≤
          (sigma / (2 + sigma)) * data.preGrainLoss / 16 :=
        min_le_right _ _
      have initialLocalLt : initial.localLoss < initialBudget :=
        initialSmall.local_lt_lemma43.trans
          initialSmall.lemma43_lt_secondInput
      have targetPos : 0 < (sigma / (2 + sigma)) * data.preGrainLoss := by
        exact mul_pos
          (div_pos critical.sigma_pos (by linarith [critical.sigma_pos]))
          data.preGrain_pos
      calc
        4 * initial.localLoss < 4 * initialBudget := by linarith
        _ ≤ 4 *
            ((sigma / (2 + sigma)) * data.preGrainLoss / 16) := by
          gcongr
        _ = ((sigma / (2 + sigma)) * data.preGrainLoss) / 4 := by ring
        _ < (sigma / (2 + sigma)) * data.preGrainLoss := by
          linarith
    globalADAbsorption := globalADAbsorption
    robustFirstRootScale := robustFirstRootScale
    robustFirstRootScale_pos := robustFirstRootScalePos
    robustFirstRootScale_le_one := robustFirstRootScaleOne
    robustFirst_root_power_le := fun {delta} deltaPos deltaLe =>
      robustFirstRootPower delta deltaPos deltaLe
    sameExtremizerRootNormalizationLoss := sameExtremizerRootNormalizationLoss
    sameExtremizerRootNormalizationLoss_eq := rfl
    initial_lemma43_le_sameExtremizerRoot_half := by
      dsimp only [sameExtremizerRootNormalizationLoss]
      calc
        initial.lemma43SourceLoss ≤ richSchedule.sourceLoss / 32 :=
          initialLemma43LtThirtySecond.le
        _ = richSchedule.sourceLoss / 16 / 2 := by ring
    sameExtremizer := sameExtremizer
    sameExtremizerRootScale := sameExtremizerRootScale
    sameExtremizerRootScale_pos := sameExtremizerRootScalePos
    sameExtremizerRootScale_le_one := sameExtremizerRootScaleOne
    sameExtremizer_root_power_le := fun {delta} deltaPos deltaLe =>
      (sameExtremizerRootPower delta deltaPos deltaLe).trans
        (min_le_left _ _)
    sameExtremizer_restore_root_power_le := fun {delta} deltaPos deltaLe =>
      (sameExtremizerRootPower delta deltaPos deltaLe).trans
        (min_le_right _ _)
    firstRichSchedule := firstRichSchedule
    sampledM8 := sampledM8
    sampledM8RootLosses := sampledM8RootLosses
    sampledM8Cutoff := sampledM8Cutoff
    sampledFiberAbsorption := sampledFiberAbsorption
    sampledPlaninessCutoff := sampledPlaninessCutoff
    preliminaryStickyLoss := preliminaryStickyLoss
    planinessLoss := planinessLoss
    preliminaryProducerLoss := preliminaryProducerLoss
    preliminaryStickyLoss_eq := rfl
    planinessLoss_eq := rfl
    preliminaryProducerLoss_eq := rfl
    preliminaryStickyLoss_pos := preliminaryStickyLoss_pos
    preliminaryStickyLoss_lt_planiness := by
      dsimp only [preliminaryStickyLoss, planinessLoss]
      rw [sampledM8RootLosses.planinessLoss_eq]
      linarith [sampledM8RootLosses.stickyLoss_pos]
    planinessLoss_lt_producer := by
      have small := sampledM8RootLosses.reentryNormalization_lt_nextSource
      rw [sampledM8RootLosses.reentryNormalizationLoss_eq] at small
      dsimp only [planinessLoss, preliminaryProducerLoss]
      rw [sampledM8RootLosses.planinessLoss_eq]
      linarith [sampledM8RootLosses.stickyLoss_pos]
    preliminaryProducerLoss_lt_firstSource := by
      dsimp only [preliminaryProducerLoss]
      linarith [firstRichSchedule.sourceLoss_pos]
    planinessLoss_lt_sigma_quarter := planinessLoss_lt_sigma_quarter
    preliminaryAnalytic := preliminaryAnalytic
    firstChartDensity := firstChartDensity
    firstChartTraceGap := firstChartTraceGap
    firstChartTraceDensity := firstChartTraceDensity
    firstChartRootScale := firstChartRootScale
    firstChartRootScale_pos := firstChartRootScalePos
    firstChartRootScale_le_one := firstChartRootScaleOne
    firstChartRootScale_le_cutoffRoot := by
      dsimp only [firstChartRootScale]
      exact (min_le_right _ _).trans (min_le_right _ _)
    firstChart_root_power_le := fun {delta} deltaPos deltaLe =>
      firstChartDensityRootPower delta deltaPos
        (deltaLe.trans (min_le_left _ _))
    firstChart_trace_root_power_le := fun {delta} deltaPos deltaLe =>
      firstChartTraceRootPower delta deltaPos
        (deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _))
    preliminaryRootSourceLoss := preliminaryRootSourceLoss
    preliminaryRootNormalizationLoss := preliminaryRootNormalizationLoss
    preliminaryReentryDensityLoss := preliminaryReentryDensityLoss
    preliminaryReentryWeightLoss := preliminaryReentryWeightLoss
    preliminaryRootSourceLoss_eq := rfl
    preliminaryRootNormalizationLoss_eq := rfl
    preliminaryReentryDensityLoss_eq := rfl
    preliminaryReentryWeightLoss_eq := rfl
    preliminaryReentryAbsorption := preliminaryReentryAbsorption
    alignedRootScale := alignedRootScale
    sampledFiberScale := sampledFiberScale
    sampledFiberScale_pos := sampledFiberScalePos
    sampledFiberScale_le_one := sampledFiberScaleOne
    sampledFiber_ambient := fun {rho} rhoPos rhoLe =>
      sampledFiberAmbient rho rhoPos rhoLe
  }⟩

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_pos
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    0 < cutoff.outerScaleCeiling := by
  unfold Proposition63M9PreNode3CutoffData.outerScaleCeiling
  exact lt_min cutoff.richSchedule.delta₀_pos <|
    lt_min data.lemma47Schedule.delta₀_pos <|
      lt_min cutoff.power.outerCutoff.delta₀_pos <|
        lt_min cutoff.coordinateCommon.delta₀_pos <|
          lt_min cutoff.lemma412Cutoff.delta₀_pos <|
            lt_min cutoff.firstRichSchedule.delta₀_pos <|
              lt_min cutoff.preliminaryAnalytic.propertyPScale_pos <|
                lt_min cutoff.preliminaryAnalytic.sparseCVScale_pos <|
                  lt_min cutoff.preliminaryReentryAbsorption.delta₀_pos <|
                    lt_min cutoff.alignedRootScale.delta₀_pos <|
                      lt_min cutoff.sampledM8Cutoff.delta₀_pos <|
                        lt_min cutoff.sampledFiberScale_pos <|
                          lt_min cutoff.sampledFiberAbsorption.delta₀_pos <|
                            lt_min cutoff.sampledPlaninessCutoff.delta₀_pos <|
                              lt_min cutoff.sameExtremizerRootScale_pos <|
                                lt_min cutoff.sampledM8RootLosses.sampledFirstRichAbsorption.delta₀_pos <|
                                  lt_min cutoff.firstChartRootScale_pos <|
                                    lt_min cutoff.robustFirstRootScale_pos
                                      cutoff.globalADAbsorption.delta₀_pos

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_one
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ 1 :=
  (min_le_left _ _).trans cutoff.richSchedule.delta₀_le_one

theorem Proposition63M9PreNode3CutoffData.scaleCeiling_pos
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    0 < cutoff.scaleCeiling := by
  unfold Proposition63M9PreNode3CutoffData.scaleCeiling
  exact lt_min
    (sq_pos_of_pos (div_pos cutoff.outerScaleCeiling_pos (by norm_num)))
    (Real.rpow_pos_of_pos cutoff.outerScaleCeiling_pos _)

theorem Proposition63M9PreNode3CutoffData.scaleCeiling_le_outerScaleCeiling
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.scaleCeiling ≤ cutoff.outerScaleCeiling := by
  calc
    cutoff.scaleCeiling ≤ (cutoff.outerScaleCeiling / 2) ^ 2 := by
      unfold Proposition63M9PreNode3CutoffData.scaleCeiling
      exact min_le_left _ _
    _ ≤ cutoff.outerScaleCeiling := by
      have hhalf : 0 ≤ cutoff.outerScaleCeiling / 2 :=
        (div_pos cutoff.outerScaleCeiling_pos (by norm_num)).le
      have hhalf_one : cutoff.outerScaleCeiling / 2 ≤ 1 := by
        linarith [cutoff.outerScaleCeiling_le_one]
      have hproduct : 0 ≤ (cutoff.outerScaleCeiling / 2) *
          (1 - cutoff.outerScaleCeiling / 2) :=
        mul_nonneg hhalf (sub_nonneg.mpr hhalf_one)
      nlinarith [cutoff.outerScaleCeiling_pos]

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_rich
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ cutoff.richSchedule.delta₀ :=
  min_le_left _ _

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_lemma47
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ data.lemma47Schedule.delta₀ :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_power
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ cutoff.power.outerCutoff.delta₀ :=
  (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_left _ _)

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_coordinate
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ cutoff.coordinateCommon.delta₀ :=
  (min_le_right _ _).trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans (min_le_left _ _)

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_lemma412
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ cutoff.lemma412Cutoff.delta₀ :=
  (min_le_right _ _).trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans <| (min_le_right _ _).trans
      (min_le_left _ _)

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_firstRich
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ cutoff.firstRichSchedule.delta₀ :=
  (min_le_right _ _).trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_preliminaryPropertyP
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ cutoff.preliminaryAnalytic.propertyPScale :=
  (min_le_right _ _).trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans
        (min_le_left _ _)

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_preliminarySparse
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ cutoff.preliminaryAnalytic.sparseCVScale :=
  (min_le_right _ _).trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_preliminaryReentry
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ cutoff.preliminaryReentryAbsorption.delta₀ :=
  (min_le_right _ _).trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans
          (min_le_left _ _)

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_alignedRoot
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ cutoff.alignedRootScale.delta₀ :=
  (min_le_right _ _).trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans <| (min_le_right _ _).trans
      <| (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_preliminaryM8
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ cutoff.sampledM8Cutoff.delta₀ :=
  (min_le_right _ _).trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans <| (min_le_right _ _).trans
      <| (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          ((min_le_right _ _).trans <| (min_le_right _ _).trans
            (min_le_left _ _))

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_sampledFiber
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ cutoff.sampledFiberScale :=
  (min_le_right _ _).trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans <| (min_le_right _ _).trans
      <| (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          ((min_le_right _ _).trans <| (min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_left _ _)))

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_sampledFiberAbsorption
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ cutoff.sampledFiberAbsorption.delta₀ :=
  (min_le_right _ _).trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans <| (min_le_right _ _).trans
      <| (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          ((min_le_right _ _).trans <| (min_le_right _ _).trans <|
            ((min_le_right _ _).trans <| (min_le_right _ _).trans
              (min_le_left _ _)))

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_sampledPlaniness
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ cutoff.sampledPlaninessCutoff.delta₀ :=
  (min_le_right _ _).trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans <| (min_le_right _ _).trans
      <| (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          ((min_le_right _ _).trans <| (min_le_right _ _).trans <|
            ((min_le_right _ _).trans <| (min_le_right _ _).trans
              ((min_le_right _ _).trans (min_le_left _ _))))

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_sameExtremizerRoot
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ cutoff.sameExtremizerRootScale := by
  simp [Proposition63M9PreNode3CutoffData.outerScaleCeiling]

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_sampledFirstRich
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤
      cutoff.sampledM8RootLosses.sampledFirstRichAbsorption.delta₀ := by
  simp [Proposition63M9PreNode3CutoffData.outerScaleCeiling]

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_robustFirstRoot
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ cutoff.robustFirstRootScale := by
  simp [Proposition63M9PreNode3CutoffData.outerScaleCeiling]

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_firstChartRoot
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ cutoff.firstChartRootScale := by
  simp [Proposition63M9PreNode3CutoffData.outerScaleCeiling]

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_globalADAbsorption
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.outerScaleCeiling ≤ cutoff.globalADAbsorption.delta₀ := by
  simp [Proposition63M9PreNode3CutoffData.outerScaleCeiling]

theorem Proposition63M9PreNode3CutoffData.firstChartPower_le_densityCutoff
    {sigma outputLoss delta : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    (delta_pos : 0 < delta) (delta_le : delta ≤ cutoff.outerScaleCeiling) :
    Real.rpow delta (sigma / (2 + sigma)) ≤
      cutoff.firstChartDensity.delta₀ :=
  cutoff.firstChart_root_power_le delta_pos
    (delta_le.trans cutoff.outerScaleCeiling_le_firstChartRoot)

theorem Proposition63M9PreNode3CutoffData.firstChartPower_le_traceDensityCutoff
    {sigma outputLoss delta : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    (delta_pos : 0 < delta) (delta_le : delta ≤ cutoff.outerScaleCeiling) :
    Real.rpow delta (sigma / (2 + sigma)) ≤
      cutoff.firstChartTraceDensity.delta₀ :=
  cutoff.firstChart_trace_root_power_le delta_pos
    (delta_le.trans cutoff.outerScaleCeiling_le_firstChartRoot)

/-- The outer cutoff also pulls the dedicated first-chart finite-nearby
threshold back through the exact chart ratio. -/
theorem Proposition63M9PreNode3CutoffData.firstChartRatio_le_nearbyCutoff
    {sigma outputLoss delta : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    (delta_pos : 0 < delta) (delta_le : delta ≤ cutoff.outerScaleCeiling)
    (firstScale : WZ2PaperRequestedScale delta)
    (firstScale_lower : Real.rpow delta
      (1 - cutoff.initial.stickyLoss) ≤ firstScale.1) :
    delta / firstScale.1 ≤ cutoff.firstChartCutoff.ratioCutoff := by
  exact cutoff.firstChartCutoff.ratio_le_cutoff delta_pos
    (delta_le.trans cutoff.outerScaleCeiling_le_firstChartRoot |>.trans
      cutoff.firstChartRootScale_le_cutoffRoot)
    firstScale firstScale_lower

/-- The same pulled-back cutoff pays the canonical trace and paper-carrier
scale bounds at the actual first-chart ratio. -/
theorem Proposition63M9PreNode3CutoffData.firstChartScaleAbsorption
    {sigma outputLoss delta : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    (delta_pos : 0 < delta) (delta_le : delta ≤ cutoff.outerScaleCeiling)
    (firstScale : WZ2PaperRequestedScale delta)
    (firstScale_lower : Real.rpow delta
      (1 - cutoff.initial.stickyLoss) ≤ firstScale.1) :
    let q := delta / firstScale.1
    (96 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN q
            (cutoff.twoCall.schedule.first.sourceLoss -
              cutoff.firstChartCutoff.nearbyInputLoss) ≤ 1 ∧
      ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN q
            (cutoff.twoCall.schedule.first.sourceLoss -
              cutoff.firstChartCutoff.nearbyInputLoss) ≤
        (73 / 100 : ENNReal) := by
  exact cutoff.firstChartCutoff.scale_absorption_at_ratio delta_pos
    (delta_le.trans cutoff.outerScaleCeiling_le_firstChartRoot |>.trans
      cutoff.firstChartRootScale_le_cutoffRoot)
    firstScale firstScale_lower

/-- Pull the robust first-call cutoff back through the actual first-chart
scale window.  This controls the post-chart ratio, not merely the outer root
scale. -/
theorem Proposition63M9PreNode3CutoffData.firstChartRatio_le_twoCallRoot
    {sigma outputLoss delta : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    (delta_pos : 0 < delta) (delta_le : delta ≤ cutoff.outerScaleCeiling)
    (firstScale : WZ2PaperRequestedScale delta)
    (firstScale_lower : Real.rpow delta
      (1 - cutoff.initial.stickyLoss) ≤ firstScale.1) :
    delta / firstScale.1 ≤ cutoff.twoCall.rootCutoff := by
  have firstScale_pos : 0 < firstScale.1 :=
    delta_pos.trans_le firstScale.2.1
  have ratio_le_power : delta / firstScale.1 ≤
      Real.rpow delta cutoff.initial.stickyLoss := by
    rw [div_le_iff₀ firstScale_pos]
    calc
      delta = Real.rpow delta 1 := (Real.rpow_one delta).symm
      _ = Real.rpow delta
          ((1 - cutoff.initial.stickyLoss) + cutoff.initial.stickyLoss) := by
        congr 1
        ring
      _ = Real.rpow delta (1 - cutoff.initial.stickyLoss) *
          Real.rpow delta cutoff.initial.stickyLoss := by
        exact Real.rpow_add delta_pos _ _
      _ ≤ firstScale.1 *
          Real.rpow delta cutoff.initial.stickyLoss := by
        exact mul_le_mul_of_nonneg_right firstScale_lower
          (Real.rpow_nonneg delta_pos.le cutoff.initial.stickyLoss)
      _ = Real.rpow delta cutoff.initial.stickyLoss * firstScale.1 :=
        mul_comm _ _
  exact ratio_le_power.trans <|
    cutoff.robustFirst_root_power_le delta_pos <|
      delta_le.trans cutoff.outerScaleCeiling_le_robustFirstRoot

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_query
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    {outerIndex : ℕ} (houter : outerIndex < data.m8.centralTemplate.count) :
    cutoff.outerScaleCeiling ≤ (cutoff.queryCutoff outerIndex houter).delta₀ :=
  cutoff.outerScaleCeiling_le_coordinate.trans <|
    (cutoff.coordinateCommon.le_threshold outerIndex houter).trans <|
      min_le_left _ _

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_root
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    {outerIndex : ℕ} (houter : outerIndex < data.m8.centralTemplate.count) :
    cutoff.outerScaleCeiling ≤ (cutoff.rootCutoff outerIndex houter).delta₀ :=
  cutoff.outerScaleCeiling_le_coordinate.trans <|
    (cutoff.coordinateCommon.le_threshold outerIndex houter).trans <|
      (min_le_right _ _).trans (min_le_left _ _)

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_grid
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    {outerIndex : ℕ} (houter : outerIndex < data.m8.centralTemplate.count) :
    cutoff.outerScaleCeiling ≤
      (data.m8.outer.oneQuery outerIndex houter).gridSchedule.delta₀ :=
  cutoff.outerScaleCeiling_le_coordinate.trans <|
    (cutoff.coordinateCommon.le_threshold outerIndex houter).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans
        (min_le_left _ _)

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_pairFine
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    {outerIndex : ℕ} (houter : outerIndex < data.m8.centralTemplate.count)
    {pairIndex : ℕ} (hpair : pairIndex <
      (finiteIntervalOrderedPairs
        (data.m8.outer.oneQuery outerIndex houter).gridSchedule.gridN).length) :
    cutoff.outerScaleCeiling ≤
      (cutoff.pairFineCutoff outerIndex houter pairIndex hpair).delta₀ :=
  cutoff.outerScaleCeiling_le_coordinate.trans <|
    (cutoff.coordinateCommon.le_threshold outerIndex houter).trans <|
      ((min_le_right _ _).trans <| (min_le_right _ _).trans
        (min_le_right _ _)).trans <|
          (cutoff.pairFineCommon outerIndex houter).le_threshold
            pairIndex hpair

theorem Proposition63M9PreNode3CutoffData.outerScaleCeiling_le_powerPair
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    {outerIndex : ℕ} (houter : outerIndex < data.m8.centralTemplate.count)
    {pairIndex : ℕ} (hpair : pairIndex <
      (finiteIntervalOrderedPairs
        (data.m8.outer.oneQuery outerIndex houter).gridSchedule.gridN).length) :
    cutoff.outerScaleCeiling ≤
      (cutoff.power.pairCutoff outerIndex houter pairIndex hpair).rho₀ :=
  cutoff.outerScaleCeiling_le_power.trans <|
    cutoff.power.outerCutoff_le_pair houter hpair

theorem Proposition63M9PreNode3CutoffData.sqrt_le_outerScaleCeiling
    {sigma outputLoss delta : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    (_delta_nonneg : 0 ≤ delta) (delta_le : delta ≤ cutoff.scaleCeiling) :
    Real.sqrt delta ≤ cutoff.outerScaleCeiling := by
  have delta_le_square : delta ≤ (cutoff.outerScaleCeiling / 2) ^ 2 :=
    delta_le.trans <| by
      unfold Proposition63M9PreNode3CutoffData.scaleCeiling
      exact min_le_left _ _
  have sqrt_le : Real.sqrt delta ≤
      Real.sqrt ((cutoff.outerScaleCeiling / 2) ^ 2) :=
    Real.sqrt_le_sqrt delta_le_square
  calc
    Real.sqrt delta ≤
        Real.sqrt ((cutoff.outerScaleCeiling / 2) ^ 2) := sqrt_le
    _ = cutoff.outerScaleCeiling / 2 := by
      rw [Real.sqrt_sq_eq_abs,
        abs_of_pos (div_pos cutoff.outerScaleCeiling_pos (by norm_num))]
    _ ≤ cutoff.outerScaleCeiling := by
      linarith [cutoff.outerScaleCeiling_pos]

theorem Proposition63M9PreNode3CutoffData.scaleCeiling_lt_one
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data) :
    cutoff.scaleCeiling < 1 := by
  unfold Proposition63M9PreNode3CutoffData.scaleCeiling
  exact (min_le_left _ _).trans_lt <| by
    have hhalf_pos : 0 < cutoff.outerScaleCeiling / 2 :=
      div_pos cutoff.outerScaleCeiling_pos (by norm_num)
    have hhalf_le : cutoff.outerScaleCeiling / 2 ≤ 1 / 2 := by
      linarith [cutoff.outerScaleCeiling_le_one]
    nlinarith [sq_nonneg (cutoff.outerScaleCeiling / 2)]

theorem Proposition63M9PreNode3CutoffData.rootDelta_le_outerScaleCeiling
    {sigma outputLoss rootOutputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    {normalizationExponent logExponent : ℕ}
    (root : PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := rootOutputLoss)
      (scaleCeiling := cutoff.scaleCeiling)
      normalizationExponent logExponent) :
    root.realization.delta ≤ cutoff.outerScaleCeiling := by
  have ceiling_le_outer : cutoff.scaleCeiling ≤
      cutoff.outerScaleCeiling := by
    exact Proposition63M9PreNode3CutoffData.scaleCeiling_le_outerScaleCeiling
      cutoff
  exact root.realization.delta_le_ceiling.trans ceiling_le_outer

theorem Proposition63M9PreNode3CutoffData.rootPower_le_outerScaleCeiling
    {sigma outputLoss rootOutputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    {normalizationExponent logExponent : ℕ}
    (root : PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := rootOutputLoss)
      (scaleCeiling := cutoff.scaleCeiling)
      normalizationExponent logExponent) :
    Real.rpow root.realization.delta cutoff.preliminaryStickyLoss ≤
      cutoff.outerScaleCeiling := by
  have delta_le_power : root.realization.delta ≤
      Real.rpow cutoff.outerScaleCeiling
        (1 / cutoff.preliminaryStickyLoss) :=
    root.realization.delta_le_ceiling.trans <| by
      unfold Proposition63M9PreNode3CutoffData.scaleCeiling
      exact min_le_right _ _
  calc
    Real.rpow root.realization.delta cutoff.preliminaryStickyLoss ≤
        Real.rpow
          (Real.rpow cutoff.outerScaleCeiling
            (1 / cutoff.preliminaryStickyLoss))
          cutoff.preliminaryStickyLoss :=
      Real.rpow_le_rpow root.realization.delta_pos.le delta_le_power
        cutoff.preliminaryStickyLoss_pos.le
    _ = Real.rpow cutoff.outerScaleCeiling
          ((1 / cutoff.preliminaryStickyLoss) *
            cutoff.preliminaryStickyLoss) :=
      (Real.rpow_mul cutoff.outerScaleCeiling_pos.le
        (1 / cutoff.preliminaryStickyLoss)
        cutoff.preliminaryStickyLoss).symm
    _ = Real.rpow cutoff.outerScaleCeiling 1 := by
      congr 1
      field_simp [cutoff.preliminaryStickyLoss_pos.ne']
    _ = cutoff.outerScaleCeiling := Real.rpow_one _

/-- Invoke the public Node 3 realization only after every M8/M7 loss and
cutoff has been frozen.  The square on `scaleCeiling` is precisely the
conversion needed for the canonical realized scale `sqrt delta`. -/
theorem Proposition63M9PreNode3CutoffData.realize
    {sigma outputLoss rootOutputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    (capability : PureWZ2PropStickyCapability)
    (critical : PureWZ2CriticalPackage sigma)
    (rootOutputLoss_pos : 0 < rootOutputLoss) :
    Nonempty (PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := rootOutputLoss)
      (scaleCeiling := cutoff.scaleCeiling)
      capability.normalizationExponent capability.logExponent) :=
  capability.rootReentrant sigma critical rootOutputLoss
    cutoff.scaleCeiling rootOutputLoss_pos cutoff.scaleCeiling_pos

theorem Proposition63M9PreNode3CutoffData.realizedRho_le_outerScaleCeiling
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    {normalizationExponent logExponent : ℕ}
    (root : PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := cutoff.preliminaryStickyLoss)
      (scaleCeiling := cutoff.scaleCeiling)
      normalizationExponent logExponent) :
    root.realization.realizedRho.1 ≤ cutoff.outerScaleCeiling := by
  rw [root.realization.realizedRho_eq_sqrt]
  exact cutoff.sqrt_le_outerScaleCeiling root.realization.delta_pos.le
    root.realization.delta_le_ceiling

/-- Choose the exact integer-aligned first coarse scale only after Node 3 has
selected the root radius.  The loss-only rounding cutoff was already included
in `outerScaleCeiling`, so this runtime choice stays inside the same sticky
window and does not identify the canonical square-root output with a grid
multiple. -/
theorem Proposition63M9PreNode3CutoffData.alignedFirstScale
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    {normalizationExponent logExponent : ℕ}
    (root : PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := cutoff.preliminaryStickyLoss)
      (scaleCeiling := cutoff.scaleCeiling)
      normalizationExponent logExponent)
    (hsigmaOne : sigma < 1) :
    Nonempty (Proposition63AlignedPowerRequestedScaleData
      root.realization.delta cutoff.preliminaryStickyLoss) := by
  have sticky_half : cutoff.preliminaryStickyLoss < 1 / 2 := by
    linarith [cutoff.preliminaryStickyLoss_lt_planiness,
      cutoff.planinessLoss_lt_sigma_quarter, hsigmaOne]
  apply cutoff.alignedRootScale.requestedScale
    cutoff.preliminaryStickyLoss_pos sticky_half root.realization.delta_pos
  have ceiling_le_outer : cutoff.scaleCeiling ≤
      cutoff.outerScaleCeiling := by
    calc
      cutoff.scaleCeiling ≤ (cutoff.outerScaleCeiling / 2) ^ 2 := by
        unfold Proposition63M9PreNode3CutoffData.scaleCeiling
        exact min_le_left _ _
      _ ≤ cutoff.outerScaleCeiling := by
        have hhalf : 0 ≤ cutoff.outerScaleCeiling / 2 :=
          (div_pos cutoff.outerScaleCeiling_pos (by norm_num)).le
        have hhalf_one : cutoff.outerScaleCeiling / 2 ≤ 1 := by
          linarith [cutoff.outerScaleCeiling_le_one]
        have hproduct : 0 ≤ (cutoff.outerScaleCeiling / 2) *
            (1 - cutoff.outerScaleCeiling / 2) :=
          mul_nonneg hhalf (sub_nonneg.mpr hhalf_one)
        nlinarith [cutoff.outerScaleCeiling_pos]
  exact root.realization.delta_le_ceiling.trans <|
    ceiling_le_outer.trans cutoff.outerScaleCeiling_le_alignedRoot

/-- The aligned request together with the genuine Node-3 output on exactly
that request.  This is the first M9 boundary at which the grid alignment and
the sticky provenance are stored in one dependent object. -/
structure Proposition63M9AlignedFirstStickyData
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    {normalizationExponent logExponent : ℕ}
    (root : PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := cutoff.preliminaryStickyLoss)
      (scaleCeiling := cutoff.scaleCeiling)
      normalizationExponent logExponent) where
  aligned : Proposition63AlignedPowerRequestedScaleData
    root.realization.delta cutoff.preliminaryStickyLoss
  sticky : PureWZ2ReentrantPropStickyData
    (sigma := sigma) (outputLoss := cutoff.preliminaryStickyLoss)
    root.realization.normalized.croppedRefined aligned.requested
    normalizationExponent logExponent
  scale_le_outerScaleCeiling :
    aligned.requested.1 ≤ cutoff.outerScaleCeiling

/-- Run the universal root output at the newly selected aligned request. -/
theorem Proposition63M9PreNode3CutoffData.alignedFirstSticky
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    {normalizationExponent logExponent : ℕ}
    (root : PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := cutoff.preliminaryStickyLoss)
      (scaleCeiling := cutoff.scaleCeiling)
      normalizationExponent logExponent)
    (hsigmaOne : sigma < 1) :
    Nonempty (Proposition63M9AlignedFirstStickyData cutoff root) := by
  rcases cutoff.alignedFirstScale root hsigmaOne with ⟨aligned⟩
  have root_lower : Real.rpow root.realization.delta
        (1 - root.realization.continuationLoss) ≤ aligned.requested.1 :=
    (Real.rpow_le_rpow_of_exponent_ge root.realization.delta_pos
      root.realization.normalized.final_extremal.delta_le_one
      (by linarith [root.realization.continuationLoss_lt_output])).trans
        aligned.lower_window
  have root_upper : aligned.requested.1 ≤ Real.rpow root.realization.delta
      root.realization.continuationLoss :=
    aligned.upper_window.trans <|
      Real.rpow_le_rpow_of_exponent_ge root.realization.delta_pos
        root.realization.normalized.final_extremal.delta_le_one
        root.realization.continuationLoss_lt_output.le
  rcases root.reentrantOutput aligned.requested root_lower root_upper
    with ⟨sticky⟩
  exact ⟨{
    aligned := aligned
    sticky := sticky
    scale_le_outerScaleCeiling := aligned.upper_window.trans <| by
      exact cutoff.rootPower_le_outerScaleCeiling root
  }⟩

/-- Retarget the hidden losses of the synchronized root to the fixed pair
chosen by the M9 hierarchy.  This removes the remaining dependency of the
preliminary re-entry cutoff on Node 3's runtime loss witnesses while retaining
the exact ordinary/cropped normalization geometry. -/
noncomputable def Proposition63M9AlignedFirstStickyData.preliminaryRootNormalization
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData data}
    {normalizationExponent logExponent : ℕ}
    {root : PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := cutoff.preliminaryStickyLoss)
      (scaleCeiling := cutoff.scaleCeiling)
      normalizationExponent logExponent}
    (_first : Proposition63M9AlignedFirstStickyData cutoff root) :
    PureWZ2CroppedCriticalNormalizationData
      (outputLoss := cutoff.preliminaryRootNormalizationLoss)
      (weaken_extremal_configuration root.realization.source
        (by
          have normalization_lt_preliminary :=
            root.realization.normalizationLoss_lt_continuation.trans
              root.realization.continuationLoss_lt_output
          calc
            root.realization.sourceLoss ≤
                root.realization.normalizationLoss / 2 :=
              root.realization.sourceLoss_le_half
            _ ≤ cutoff.preliminaryStickyLoss / 2 := by linarith
            _ = cutoff.preliminaryRootSourceLoss :=
              cutoff.preliminaryRootSourceLoss_eq.symm)
        (by
          rw [cutoff.preliminaryRootSourceLoss_eq]
          exact half_pos cutoff.preliminaryStickyLoss_pos)
        root.realization.delta_pos
        root.realization.normalized.final_extremal.delta_le_one)
      normalizationExponent :=
  weaken_normalized_data root.realization.normalized
    (by
      have normalization_lt_preliminary :=
        root.realization.normalizationLoss_lt_continuation.trans
          root.realization.continuationLoss_lt_output
      calc
        root.realization.sourceLoss ≤ root.realization.normalizationLoss / 2 :=
          root.realization.sourceLoss_le_half
        _ ≤ cutoff.preliminaryStickyLoss / 2 := by linarith
        _ = cutoff.preliminaryRootSourceLoss :=
          cutoff.preliminaryRootSourceLoss_eq.symm)
    (by
      rw [cutoff.preliminaryRootNormalizationLoss_eq]
      exact root.realization.normalizationLoss_lt_continuation.trans
        root.realization.continuationLoss_lt_output |>.le)
    (by
      rw [cutoff.preliminaryRootSourceLoss_eq]
      exact half_pos cutoff.preliminaryStickyLoss_pos)
    (by
      rw [cutoff.preliminaryRootNormalizationLoss_eq]
      exact cutoff.preliminaryStickyLoss_pos)
    root.realization.delta_pos
    root.realization.normalized.final_extremal.delta_le_one
    (by
      rw [cutoff.preliminaryRootSourceLoss_eq,
        cutoff.preliminaryRootNormalizationLoss_eq])

/-- Re-enter the actual preliminary local-grain shading at the fixed source
and normalization losses of the first rich call.  The scalar absorption was
selected before Node 3, while the runtime construction uses exactly the
preliminary subshading and its restored extremality. -/
theorem Proposition63M9AlignedFirstStickyData.prepareFirstRich
    {sigma outputLoss localLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData data}
    {normalizationExponent logExponent : ℕ}
    {root : PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := cutoff.preliminaryStickyLoss)
      (scaleCeiling := cutoff.scaleCeiling)
      normalizationExponent logExponent}
    (first : Proposition63M9AlignedFirstStickyData cutoff root)
    (preliminary : Proposition63PreliminaryLocalGrainData
      (localLoss := localLoss)
      (reentryLoss := cutoff.preliminaryProducerLoss)
      first.preliminaryRootNormalization) :
    ∃ current : Proposition63CurrentShadingReentryData
        (reentryLoss := cutoff.firstRichSchedule.sourceLoss)
        first.preliminaryRootNormalization preliminary.shading,
      current.reentryNormalizationLoss =
        cutoff.firstRichSchedule.normalizationLoss := by
  let rootData : Proposition63RootNormalizationData
      (outputLoss := cutoff.preliminaryRootNormalizationLoss)
      (weaken_extremal_configuration root.realization.source
        (by
          have normalization_lt_preliminary :=
            root.realization.normalizationLoss_lt_continuation.trans
              root.realization.continuationLoss_lt_output
          calc
            root.realization.sourceLoss ≤
                root.realization.normalizationLoss / 2 :=
              root.realization.sourceLoss_le_half
            _ ≤ cutoff.preliminaryStickyLoss / 2 := by linarith
            _ = cutoff.preliminaryRootSourceLoss :=
              cutoff.preliminaryRootSourceLoss_eq.symm)
        (by
          rw [cutoff.preliminaryRootSourceLoss_eq]
          exact half_pos cutoff.preliminaryStickyLoss_pos)
        root.realization.delta_pos
        root.realization.normalized.final_extremal.delta_le_one)
      normalizationExponent
      cutoff.preliminaryReentryDensityLoss :=
    Proposition63RootNormalizationData.ofNormalization
      first.preliminaryRootNormalization
      (cutoff.preliminaryReentryAbsorption.density_absorb
        root.realization.delta_pos <|
          (cutoff.rootDelta_le_outerScaleCeiling root).trans
            cutoff.outerScaleCeiling_le_preliminaryReentry)
  have delta_le_absorption : root.realization.delta ≤
      cutoff.preliminaryReentryAbsorption.delta₀ :=
    (cutoff.rootDelta_le_outerScaleCeiling root).trans
      cutoff.outerScaleCeiling_le_preliminaryReentry
  have ambientTwo := cutoff.preliminaryReentryAbsorption.ambient_two
    root.realization.delta_pos delta_le_absorption
  rcases rootData.finiteNearbySchedule
      (reentryLoss := cutoff.firstRichSchedule.sourceLoss)
      (by
        rw [cutoff.preliminaryRootNormalizationLoss_eq]
        exact cutoff.preliminaryStickyLoss_pos)
      ambientTwo
      (by
        rw [cutoff.preliminaryRootNormalizationLoss_eq]
        rw [cutoff.preliminaryStickyLoss_eq]
        have small :=
          cutoff.sampledM8RootLosses.reentryNormalization_lt_nextSource
        rw [cutoff.sampledM8RootLosses.reentryNormalizationLoss_eq] at small
        linarith [cutoff.sampledM8RootLosses.stickyLoss_pos])
    with ⟨nearbySchedule⟩
  have regularizationAbsorb :=
    cutoff.preliminaryReentryAbsorption.regularization_absorb
      rootData.normalization rfl nearbySchedule rfl rfl
      root.realization.delta_pos delta_le_absorption
  rcases rootData.currentShadingReentryFromExtremal preliminary.shading
      nearbySchedule ambientTwo preliminary.extremal
      cutoff.preliminaryProducerLoss_lt_firstSource.le
      (by
        exact preliminary.extremal.nonempty |> fun _ =>
          lt_of_lt_of_le cutoff.preliminaryStickyLoss_pos
            cutoff.preliminaryStickyLoss_lt_planiness.le |> fun h =>
          lt_of_lt_of_le h cutoff.planinessLoss_lt_producer.le)
      cutoff.firstRichSchedule.normalizationLoss
      cutoff.firstRichSchedule.normalizationLoss_pos
      cutoff.firstRichSchedule.sourceLoss_le_half
      (cutoff.preliminaryReentryAbsorption.canonical_weight_absorb
        root.realization.delta_pos delta_le_absorption)
      (cutoff.preliminaryReentryAbsorption.trace_fixed_absorb
        root.realization.delta_pos delta_le_absorption)
      (cutoff.preliminaryReentryAbsorption.paper_fixed_absorb
        root.realization.delta_pos delta_le_absorption)
      regularizationAbsorb
      (by simpa only [rootData,
        Proposition63M9AlignedFirstStickyData.preliminaryRootNormalization,
        Proposition63RootNormalizationData.ofNormalization,
        weaken_normalized_data] using
          preliminary.subshading)
      preliminary.cubical
      (delta_le_absorption.trans
        cutoff.preliminaryReentryAbsorption.delta₀_le_tiny |>.trans
          (by norm_num))
    with ⟨current, _weight, _weightUpper, _level, normalizationLossEq⟩
  exact ⟨current, normalizationLossEq⟩

/-- The first paper power-scale call, bundled with the preliminary local-grain
map restricted through the exact current-shading re-entry. -/
structure Proposition63M9FirstRichBoundaryData
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData data}
    {normalizationExponent logExponent : ℕ}
    {root : PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := cutoff.preliminaryStickyLoss)
      (scaleCeiling := cutoff.scaleCeiling)
      normalizationExponent logExponent}
    (alignedFirst : Proposition63M9AlignedFirstStickyData cutoff root)
    (preliminary : Proposition63PreliminaryLocalGrainData
      (localLoss := cutoff.initial.localLoss)
      (reentryLoss := cutoff.preliminaryProducerLoss)
      alignedFirst.preliminaryRootNormalization) where
  current : Proposition63CurrentShadingReentryData
    (reentryLoss := cutoff.firstRichSchedule.sourceLoss)
    alignedFirst.preliminaryRootNormalization
    preliminary.shading
  current_normalization_loss : current.reentryNormalizationLoss =
    cutoff.firstRichSchedule.normalizationLoss
  power : Proposition63PowerScale root.realization.delta sigma
  sticky : PureWZ2ReentrantPropStickyData
    (sigma := sigma) (outputLoss := cutoff.initial.stickyLoss)
    current.normalization.croppedRefined power.requested 0 61
  localGrains : Proposition63InitialWeakLocalGrainData
    (incidence := preliminary.incidence) current.normalization.croppedRefined
    sigma (Kakeya.realRpowENN root.realization.delta
      (-cutoff.initial.localLoss)) preliminary.lipschitz

/-- Execute the first exact power-scale call after the preliminary finite-grid
stage.  The returned local-grain map is definitionally the restriction of the
preliminary map through this same re-entry. -/
theorem Proposition63M9AlignedFirstStickyData.runFirstRich
    {sigma outputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData data}
    {logExponent : ℕ}
    {root : PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := cutoff.preliminaryStickyLoss)
      (scaleCeiling := cutoff.scaleCeiling)
      0 logExponent}
    (alignedFirst : Proposition63M9AlignedFirstStickyData cutoff root)
    (preliminary : Proposition63PreliminaryLocalGrainData
      (localLoss := cutoff.initial.localLoss)
      (reentryLoss := cutoff.preliminaryProducerLoss)
      alignedFirst.preliminaryRootNormalization)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    Nonempty (Proposition63M9FirstRichBoundaryData alignedFirst preliminary) := by
  rcases alignedFirst.prepareFirstRich preliminary with
    ⟨current, currentNormalizationLoss⟩
  have delta_lt_one : root.realization.delta < 1 :=
    root.realization.delta_le_ceiling.trans_lt cutoff.scaleCeiling_lt_one
  rcases proposition63_power_scale root.realization.delta_pos delta_lt_one
      hsigma hsigmaOne with ⟨power⟩
  have window := power.first_sticky_window root.realization.delta_pos
    delta_lt_one.le cutoff.initial.sticky_le_power
    cutoff.initial.power_le_one_sub_sticky
  have delta_le_firstRich : root.realization.delta ≤
      cutoff.firstRichSchedule.delta₀ :=
    (cutoff.rootDelta_le_outerScaleCeiling root).trans
      cutoff.outerScaleCeiling_le_firstRich
  have initialAxialWindow : ∀ index point,
      point ∈ alignedFirst.preliminaryRootNormalization.frame ''
          alignedFirst.preliminaryRootNormalization.ordinaryRefined.carrier
            index →
        |point (2 : Fin 3)| ≤ 1 / 8 := by
    simpa only [
          Proposition63M9AlignedFirstStickyData.preliminaryRootNormalization,
          weaken_normalized_data] using
        root.realization.normalized_ordinary_axial_window_eighth
  rcases proposition63InitialLocalGrainReentry_richSticky
      (initialNormalized :=
        alignedFirst.preliminaryRootNormalization)
      (localLoss := cutoff.initial.localLoss)
      (localIncidence := preliminary.incidence)
      (L := preliminary.lipschitz)
      (localShading := preliminary.shading)
      (localGrains := preliminary.localGrains) current
      cutoff.firstRichSchedule rfl currentNormalizationLoss
      delta_le_firstRich initialAxialWindow
      power.requested window.1 window.2 with ⟨sticky, localGrains⟩
  exact ⟨{
    current := current
    current_normalization_loss := currentNormalizationLoss
    power := power
    sticky := sticky
    localGrains := Classical.choice localGrains
  }⟩

/-- Materialize every M7 root and smallness receipt after the outer scale has
been chosen below the pre-Node-3 ceiling.  The ambient re-entry is shared by
all coordinates; only loss weakening and loss-only scalar receipts vary. -/
noncomputable def Proposition63M9PreNode3CutoffData.outerBindingInputs
    {sigma outputLoss delta ambientSourceLoss ambientNormalizationLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {normalizationExponent : ℕ}
    (ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) ambientShading normalizationExponent
        ambientSourceLoss ambientNormalizationLoss)
    (ambient_source_le : ambientSourceLoss ≤ data.stickyLoss)
    (ambient_normalization_le : ambientNormalizationLoss ≤ 2 * data.stickyLoss)
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ cutoff.outerScaleCeiling)
    (K : ℝ) :
    Proposition63Lemma411OuterBindingInputs (incidence := delta)
      (data.m8.specialize delta_pos
        (delta_le.trans cutoff.outerScaleCeiling_le_one)).central
      (data.m8.specialize delta_pos
        (delta_le.trans cutoff.outerScaleCeiling_le_one)).outer
      ambientReentry K (data.sourceCoefficient (rho := delta))
      data.gridLoss_le_mid := by
  let schedule := data.m8.specialize delta_pos
    (delta_le.trans cutoff.outerScaleCeiling_le_one)
  let rootBinding : ∀ outerIndex
      (houter : outerIndex < schedule.central.count),
      Proposition63Lemma411OuterRootBindingData
        (schedule.outer.oneQuery outerIndex houter) ambientReentry :=
    fun outerIndex houter => {
      ambient_source_le := ambient_source_le.trans
        (data.sticky_le_m8_root_source outerIndex houter)
      ambient_normalization_le := ambient_normalization_le.trans
        (data.two_sticky_le_m8_root_normalization outerIndex houter)
      density_absorb :=
        (cutoff.rootCutoff outerIndex houter).density_absorb delta_pos
          (delta_le.trans (cutoff.outerScaleCeiling_le_root houter))
    }
  refine {
    rootBinding := rootBinding
    delta_le_grid := ?_
    smallness := ?_
  }
  · intro outerIndex houter
    exact delta_le.trans (cutoff.outerScaleCeiling_le_grid houter)
  · intro outerIndex houter
    have houterData : outerIndex < data.m8.centralTemplate.count := by
      simpa only [schedule,
        Proposition63Lemma412PreRuntimeScheduleData.specialize,
        Proposition63Lemma412CentralGridData.rebase_count] using houter
    let oneQuery := schedule.outer.oneQuery outerIndex houter
    let root := (rootBinding outerIndex houter).root
    let loss_le_mid : schedule.outer.loss (outerIndex + 1) ≤ data.midLoss := by
      change data.m8.outer.loss (outerIndex + 1) ≤ data.midLoss
      exact (data.m8.outer.loss_le_terminal (outerIndex + 1)
        (by omega)).trans data.gridLoss_le_mid
    let window := schedule.central.query_window
      root.normalization.final_extremal.delta_pos
      root.normalization.final_extremal.delta_le_one houter loss_le_mid
    let query := schedule.central.query outerIndex houter
    let grid := oneQuery.runtimeGrid query
      root.normalization.final_extremal.delta_pos
      (delta_le.trans (cutoff.outerScaleCeiling_le_grid houter))
      window.1 window.2
    let queryCutoff := cutoff.queryCutoff outerIndex houterData
    have delta_query_le : delta ≤ queryCutoff.delta₀ :=
      delta_le.trans (cutoff.outerScaleCeiling_le_query houterData)
    have coefficient_one : 1 ≤
        (((4 : NNReal) * (lipschitzExtensionConstant Point3 *
          data.sourceCoefficient (rho := delta))) : ℝ) := by
      have source_one : 1 ≤ Real.rpow delta (-data.lemma47Loss) := by
        simpa using Real.rpow_le_rpow_of_exponent_ge delta_pos
          (delta_le.trans cutoff.outerScaleCeiling_le_one)
          (show -data.lemma47Loss ≤ 0 by linarith [data.lemma47Loss_pos])
      have extension_one : 1 ≤
          (lipschitzExtensionConstant Point3 : ℝ) := by
        simp [lipschitzExtensionConstant]
      push_cast
      rw [data.sourceCoefficient_coe delta_pos]
      nlinarith
    have query_power : Real.rpow query.1
          (oneQuery.gridSchedule.discreteLoss / 2) ≤
        Real.rpow delta
          (schedule.outer.loss (outerIndex + 1) *
            oneQuery.gridSchedule.discreteLoss / 2) := by
      calc
        Real.rpow query.1 (oneQuery.gridSchedule.discreteLoss / 2) ≤
            Real.rpow
              (Real.rpow delta (schedule.outer.loss (outerIndex + 1)))
              (oneQuery.gridSchedule.discreteLoss / 2) :=
          Real.rpow_le_rpow (delta_pos.trans_le query.2.1).le window.2
            (div_nonneg oneQuery.gridSchedule.discrete_loss_pos.le
              (by norm_num))
        _ = Real.rpow delta
            (schedule.outer.loss (outerIndex + 1) *
              oneQuery.gridSchedule.discreteLoss / 2) := by
          rw [show schedule.outer.loss (outerIndex + 1) *
                oneQuery.gridSchedule.discreteLoss / 2 =
              schedule.outer.loss (outerIndex + 1) *
                (oneQuery.gridSchedule.discreteLoss / 2) by ring]
          exact (Real.rpow_mul delta_pos.le _ _).symm
    have query_power_small : Real.rpow query.1
          (oneQuery.gridSchedule.discreteLoss / 2) ≤ 1 / 2 :=
      query_power.trans (queryCutoff.query_power_endpoint delta_pos delta_query_le)
    have query_small : 2 * Real.rpow query.1
          (oneQuery.gridSchedule.discreteLoss / 2) ≤ 1 := by
      linarith
    have query_quarter : query.1 ≤ 1 / 4 := by
      exact window.2.trans <|
        queryCutoff.query_endpoint delta_pos delta_query_le
    have sqrt_query_small : 2 * Real.sqrt query.1 ≤ 1 := by
      have sqrt_le : Real.sqrt query.1 ≤ Real.sqrt (1 / 4 : ℝ) :=
        Real.sqrt_le_sqrt query_quarter
      norm_num at sqrt_le ⊢
      linarith
    have amplified_query_small : Real.rpow query.1
          (oneQuery.gridSchedule.discreteLoss / 2) ≤
        1 / (16 * (((4 : NNReal) *
          (lipschitzExtensionConstant Point3 *
            data.sourceCoefficient (rho := delta))) : ℝ)) := by
      have denominator_pos : 0 < 16 * (((4 : NNReal) *
          (lipschitzExtensionConstant Point3 *
            data.sourceCoefficient (rho := delta))) : ℝ) := by
        positivity
      rw [le_div_iff₀ denominator_pos]
      calc
        Real.rpow query.1 (oneQuery.gridSchedule.discreteLoss / 2) *
              (16 * (((4 : NNReal) *
                (lipschitzExtensionConstant Point3 *
                  data.sourceCoefficient (rho := delta))) : ℝ)) ≤
            Real.rpow delta
                (schedule.outer.loss (outerIndex + 1) *
                  oneQuery.gridSchedule.discreteLoss / 2) *
              (16 * (((4 : NNReal) *
                (lipschitzExtensionConstant Point3 *
                  data.sourceCoefficient (rho := delta))) : ℝ)) := by
          gcongr
        _ = (64 * (lipschitzExtensionConstant Point3 : ℝ)) *
            Real.rpow delta
              (schedule.outer.loss (outerIndex + 1) *
                  oneQuery.gridSchedule.discreteLoss / 2 -
                data.lemma47Loss) := by
          push_cast
          rw [data.sourceCoefficient_coe delta_pos]
          rw [show Real.rpow delta
                (schedule.outer.loss (outerIndex + 1) *
                    oneQuery.gridSchedule.discreteLoss / 2 -
                  data.lemma47Loss) =
              Real.rpow delta
                  (schedule.outer.loss (outerIndex + 1) *
                    oneQuery.gridSchedule.discreteLoss / 2) *
                Real.rpow delta (-data.lemma47Loss) by
            calc
              Real.rpow delta
                    (schedule.outer.loss (outerIndex + 1) *
                        oneQuery.gridSchedule.discreteLoss / 2 -
                      data.lemma47Loss) =
                  Real.rpow delta
                    (schedule.outer.loss (outerIndex + 1) *
                        oneQuery.gridSchedule.discreteLoss / 2 +
                      (-data.lemma47Loss)) := by ring
              _ = Real.rpow delta
                    (schedule.outer.loss (outerIndex + 1) *
                      oneQuery.gridSchedule.discreteLoss / 2) *
                    Real.rpow delta (-data.lemma47Loss) :=
                Real.rpow_add delta_pos _ _]
          ring
        _ ≤ 1 := queryCutoff.amplified_endpoint delta_pos delta_query_le
    have delta_lt_one : delta < 1 := by
      linarith [delta_le, cutoff.outerScaleCeiling_le_lemma412,
        cutoff.lemma412Cutoff.rho_small]
    let scalar : Proposition63Lemma411ScalarSmallnessData
        (incidence := delta) oneQuery.backward root grid
        (data.sourceCoefficient (rho := delta)) := {
      delta_lt_one := delta_lt_one
      sigma_pos := oneQuery.sigma_pos
      sigma_lt_one := oneQuery.sigma_lt_one
      discrete_loss_pos := oneQuery.gridSchedule.discrete_loss_pos
      discrete_loss_lt_half := oneQuery.discrete_loss_lt_half
      output_loss_le_half := oneQuery.output_loss_le_half
      coefficient_one := coefficient_one
      query_small := query_small
      delta_le_query := query.2.1
      sqrt_query_small := sqrt_query_small
      amplified_query_small := amplified_query_small
      incidence_nonneg := delta_pos.le
      incidence_le_delta := le_rfl
      rho_small := by
        intro pairIndex hpair scales
        have outer_power_le :=
          (cutoff.power.pairCutoff outerIndex houterData pairIndex hpair).inner_scale_small
            delta_pos
            (delta_le.trans (cutoff.outerScaleCeiling_le_powerPair
              houterData hpair))
        exact (scales.rhoHat_le_output_rpow delta_pos
          (by
            let seed := oneQuery.backward.seed pairIndex hpair
            exact seed.schedule.firstOutputLoss_lt_secondSource.trans_le <|
              seed.schedule.second.sourceLoss_le_half.trans <|
                (half_le_self seed.schedule.second.normalizationLoss_pos.le).trans <|
                  seed.schedule.second.normalizationLoss_lt_output.le.trans
                    seed.secondOutputLoss_le_discrete)
          ((cutoff.power.pairCutoff outerIndex houterData pairIndex hpair).first_output_gap_small
            delta_pos
            (delta_le.trans (cutoff.outerScaleCeiling_le_powerPair
              houterData hpair)))).trans outer_power_le
      firstOutput_gap_small := by
        intro pairIndex hpair
        exact (cutoff.power.pairCutoff outerIndex houterData pairIndex hpair).first_output_gap_small
          delta_pos (delta_le.trans
            (cutoff.outerScaleCeiling_le_powerPair houterData hpair))
    }
    let paperCutoff : ∀ pairIndex
        (hpair : pairIndex <
          (finiteIntervalOrderedPairs oneQuery.gridSchedule.gridN).length),
          Proposition63FourCallPaperSeedCutoffData
            (oneQuery.backward.seed pairIndex hpair)
            ((4 : NNReal) * (lipschitzExtensionConstant Point3 *
              data.sourceCoefficient (rho := delta))) :=
      fun pairIndex hpair =>
        (cutoff.power.pairCutoff outerIndex houterData pairIndex hpair).paperCutoff
          delta_pos (delta_le.trans
            (cutoff.outerScaleCeiling_le_powerPair houterData hpair))
          (data.coefficient_coarse_gap outerIndex houterData pairIndex hpair)
    let firstUniformCutoff : ∀ pairIndex
        (hpair : pairIndex <
          (finiteIntervalOrderedPairs oneQuery.gridSchedule.gridN).length),
          Proposition63FourCallFirstUniformCutoffData
            (oneQuery.backward.seed pairIndex hpair)
            ((4 : NNReal) * (lipschitzExtensionConstant Point3 *
              data.sourceCoefficient (rho := delta))) :=
      fun pairIndex hpair =>
        (cutoff.power.pairCutoff outerIndex houterData pairIndex hpair).firstUniformCutoff
          delta_pos (delta_le.trans
            (cutoff.outerScaleCeiling_le_powerPair houterData hpair))
          (data.coefficient_first_gap outerIndex houterData pairIndex hpair)
    let fine := fun pairIndex
        (hpair : pairIndex <
          (finiteIntervalOrderedPairs oneQuery.gridSchedule.gridN).length) =>
      cutoff.pairFineCutoff outerIndex houterData pairIndex hpair
    exact {
      global := {
        scalar := scalar
        paperCutoff := paperCutoff
        firstUniformCutoff := firstUniformCutoff
        currentReentryAbsorption :=
          fun pairIndex hpair => (fine pairIndex hpair).currentReentryAbsorption
        finalCandidateLiftAbsorption :=
          fun pairIndex hpair => (fine pairIndex hpair).finalCandidateLiftAbsorption
        rho_le_paper_pair := by
          intro pairIndex hpair scales
          have pair_le : delta ≤
              (cutoff.power.pairCutoff outerIndex houterData pairIndex hpair).rho₀ :=
            delta_le.trans
              (cutoff.outerScaleCeiling_le_powerPair houterData hpair)
          have rhoHat_le : scales.rhoHat.1 ≤ Real.rpow delta
              (oneQuery.backward.seed pairIndex hpair).schedule.firstOutputLoss :=
            scales.rhoHat_le_output_rpow delta_pos
              (by
                let seed := oneQuery.backward.seed pairIndex hpair
                exact seed.schedule.firstOutputLoss_lt_secondSource.trans_le <|
                  seed.schedule.second.sourceLoss_le_half.trans <|
                    (half_le_self seed.schedule.second.normalizationLoss_pos.le).trans <|
                      seed.schedule.second.normalizationLoss_lt_output.le.trans
                        seed.secondOutputLoss_le_discrete)
              ((cutoff.power.pairCutoff outerIndex houterData pairIndex hpair).first_output_gap_small
                delta_pos pair_le)
          change scales.rhoHat.1 ≤ min
            (cutoff.power.pairCutoff outerIndex houterData pairIndex hpair).base.rhoCutoff
            (Real.rpow delta
              (oneQuery.backward.seed pairIndex hpair).schedule.firstOutputLoss)
          exact le_min
            (rhoHat_le.trans <|
              (cutoff.power.pairCutoff outerIndex houterData pairIndex hpair).inner_scale
                delta_pos pair_le) rhoHat_le
        delta_le_current := by
          intro pairIndex hpair
          exact (delta_le.trans
            (cutoff.outerScaleCeiling_le_pairFine houterData hpair)).trans
              (fine pairIndex hpair).delta₀_le_current
        delta_le_final := by
          intro pairIndex hpair
          exact (delta_le.trans
            (cutoff.outerScaleCeiling_le_pairFine houterData hpair)).trans
              (fine pairIndex hpair).delta₀_le_final
        delta_le_aligned := by
          intro pairIndex hpair
          exact (delta_le.trans
            (cutoff.outerScaleCeiling_le_pairFine houterData hpair)).trans
              (fine pairIndex hpair).delta₀_le_aligned
        delta_le_first := by
          intro pairIndex hpair
          change delta ≤ delta
          exact le_rfl
      }
    }

/-- Specialize the outer binding to the exact coarse re-entry carried by a
rich second Proposition 6.2 output. -/
noncomputable def Proposition63M9PreNode3CutoffData.outerBindingInputsOfRich
    {sigma outputLoss delta sourceLoss normalizationLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {normalizationExponent : ℕ}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
        sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := data.stickyLoss) croppedShading reentry rho)
    (rootAxialWindow : ∀ index point,
      point ∈ reentry.geometry.frame ''
          reentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (rho_le : rho.1 ≤ cutoff.outerScaleCeiling)
    (K : ℝ) :
    Proposition63Lemma411OuterBindingInputs (incidence := rho.1)
      (data.m8.specialize rich.data.coarse_extremal.delta_pos
        rich.data.coarse_extremal.delta_le_one).central
      (data.m8.specialize rich.data.coarse_extremal.delta_pos
        rich.data.coarse_extremal.delta_le_one).outer
      (rich.coarseReentry rootAxialWindow) K
      (data.sourceCoefficient (rho := rho.1)) data.gridLoss_le_mid := by
  exact cutoff.outerBindingInputs (rich.coarseReentry rootAxialWindow)
    (by linarith [rich.coarseSourceLoss_budget, rich.coarseSourceLoss_pos])
    (by
      rw [rich.coarseNormalizationLoss_eq]
      linarith [rich.coarseSourceLoss_budget, rich.coarseSourceLoss_pos])
    rich.data.coarse_extremal.delta_pos rho_le K

/-- M8 endpoint for the case relevant to M9, where Lemma 4.7 already
supplies the required global Lipschitz bound.  The M7 iteration only restricts
that same map, so no second finite Lipschitz selection or extra factor `27`
is needed. -/
theorem proposition63_lemma412_output_of_lemma411_outer_inputs_lipschitz
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss lemma44Loss
      lemma47Loss coefficient gridLoss midLoss outputLoss
      ambientSourceLoss ambientNormalizationLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent normalizationExponent N : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    {lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss}
    (lemma47 : Proposition63Lemma47Data lemma44 lemma47Loss coefficient)
    (ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sticky.croppedCoarseShading normalizationExponent
        ambientSourceLoss ambientNormalizationLoss)
    (ambientAxialEighth : ∀ tube point,
      point ∈ ambientReentry.geometry.frame ''
          ambientReentry.geometry.ordinaryRefined.carrier tube →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (schedule : Proposition63Lemma412ScheduleData
      sigma gridLoss rho.1 midLoss N)
    (K : ℝ)
    (hgridLossMid : gridLoss ≤ midLoss)
    (inputs : Proposition63Lemma411OuterBindingInputs (incidence := rho.1)
      schedule.central schedule.outer ambientReentry K
        (Real.toNNReal coefficient) hgridLossMid)
    (hlemma47Input : lemma47Loss ≤ schedule.outer.loss 0)
    (hrhoSmall : rho.1 ≤ 1 / 24)
    (_houtputLossPos : 0 < outputLoss)
    (hlemma47Output : lemma47Loss ≤ outputLoss)
    (hgridOutput : gridLoss ≤ outputLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (habsorbInterpolation :
      (100 : ℝ) * Real.rpow rho.1
          (-gridLoss - midLoss - 1 / (N : ℝ)) ≤
        Real.rpow rho.1 (-outputLoss))
    (habsorbFine :
      (100 : ℝ) * Real.rpow rho.1
          (-midLoss - 1 / (N : ℝ)) ≤
        Real.rpow rho.1 (-outputLoss)) :
    Nonempty (Proposition63Lemma412OutputData lemma47 outputLoss) := by
  rcases proposition63_lemma411_central_binding schedule.central
      schedule.outer ambientReentry K (Real.toNNReal coefficient)
      hgridLossMid inputs with ⟨binding⟩
  have current_extremal : WZ2PaperCroppedIsExtremal sigma
      (schedule.outer.loss 0) sticky.coarse lemma47.shading :=
    lemma47.extremal.mono_loss hlemma47Input
  have current_cwa : WZ2PaperConvexWolffBound sticky.coarse
      (Kakeya.realRpowENN rho.1 (-(schedule.outer.loss 0))) := by
    apply weaken_convex_wolff_bound lemma47.top_level_cwa
    exact realRpowENN_antitone lemma47.extremal.delta_pos
      lemma47.extremal.delta_le_one (by
        linarith [hlemma47Input])
  have current_sub_ambient : PaperIsSubshading lemma47.shading
      sticky.croppedCoarseShading := fun tube point point_mem =>
    lemma44.coarse_subshading tube (lemma47.subshading tube point_mem)
  have current_mass_pos : 0 < lemma47.shading.mass :=
    cropped_extremal_shading_mass_pos lemma47.extremal
      sticky.cover.coarse_line_class hrhoSmall
  let identitySub : PaperIsSubshading lemma47.shading lemma47.shading :=
    fun _ => Set.Subset.rfl
  rcases binding.binding.run ambientAxialEighth lemma47.planeMap
      lemma47.lipschitz identitySub current_sub_ambient current_extremal
      current_cwa current_mass_pos (fun _ => 0) (fun _ => 0)
      (by simp) with ⟨finite⟩
  let finalMap := finite.planeMap
  let finalFn : {point : Point3 // point ∈ finite.shading.union} → Point3 :=
    fun point => finalMap.planeMap point
  have finalLipschitz : LipschitzWith (Real.toNNReal coefficient) finalFn := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    have firstSource : (first : Point3) ∈ lemma47.shading.union :=
      paperSubshading_union finite.subshading first.prop
    have secondSource : (second : Point3) ∈ lemma47.shading.union :=
      paperSubshading_union finite.subshading second.prop
    change dist (finalMap.planeMap first) (finalMap.planeMap second) ≤
      (Real.toNNReal coefficient : ℝ) * dist first second
    rw [finite.same_plane_map]
    exact lemma47.lipschitz.dist_le_mul
      ⟨first, firstSource⟩ ⟨second, secondSource⟩
  have finalUnit : ∀ point, ‖finalFn point‖ = 1 := by
    intro point
    exact finalMap.unit point point.prop
  have finalIncidence : ∀ index point,
      ∀ hpoint : point ∈ finite.shading.carrier index,
        |inner ℝ (sticky.coarse.tube index).direction
          (finalFn ⟨point, ⟨index, hpoint⟩⟩)| ≤ rho.1 := by
    intro index point hpoint
    exact finalMap.incidence index point hpoint
  let localGrains : PureWZ2RelaxedLocalGrainData finite.shading sigma
      (Kakeya.realRpowENN rho.1 (-outputLoss))
      (Real.toNNReal coefficient) :=
    finite_grid_isAD_to_relaxed_local_grain finalFn finalLipschitz finalUnit
      finalIncidence lemma47.extremal.delta_pos
      lemma47.extremal.delta_le_one hsigma hsigmaOne
      (by
        rw [← schedule.outer.final_loss]
        exact schedule.outer.loss_pos schedule.central.count le_rfl)
      schedule.central.midLoss_pos schedule.central.N_pos
      schedule.central.kMin_eq schedule.central.kMin_le_kMax
      schedule.central.kMax_lower schedule.central.admissible
      (by
        intro index indexRange point
        have sourceAD := finite.local_ad
          (index - schedule.central.kMin) (by
            dsimp [Proposition63Lemma412CentralGridData.count]
            omega) (point : Point3) point.prop
        have globalIndex : schedule.central.globalIndex
            (index - schedule.central.kMin) = index := by
          dsimp [Proposition63Lemma412CentralGridData.globalIndex]
          omega
        rw [binding.query_eq (index - schedule.central.kMin) (by
          dsimp [Proposition63Lemma412CentralGridData.count]
          omega), globalIndex, schedule.outer.final_loss] at sourceAD
        simpa only [finalFn] using sourceAD)
      habsorbInterpolation habsorbFine
  exact ⟨{
    shading := finite.shading
    subshading := finite.subshading
    cubical := finite.cubical
    localGrains := localGrains
    same_plane_map := by
      intro point
      change finalMap.planeMap point = lemma44.planeMap.planeMap point
      calc
        finalMap.planeMap point =
            (paperWeakPlaneMapRestrict lemma47.planeMap identitySub).planeMap
              point := congrFun finite.same_plane_map point
        _ = lemma47.planeMap.planeMap point := rfl
        _ = lemma44.planeMap.planeMap point :=
          congrFun lemma47.same_plane_map point
    extremal := finite.extremal.mono_loss (by
      rw [schedule.outer.final_loss]
      exact hgridOutput)
    top_level_cwa := by
      apply weaken_convex_wolff_bound lemma47.top_level_cwa
      exact realRpowENN_antitone lemma47.extremal.delta_pos
        lemma47.extremal.delta_le_one (by linarith [hlemma47Output])
  }⟩

/-- Close the complete M8 stage from the frozen M9 envelope and the exact
rich sticky output at the same outer scale.  The finite Lipschitz schedule
supplies its own all-distance covering data, while the M7 coordinate calls use
the pairwise cutoff package assembled above. -/
theorem Proposition63M9PreNode3CutoffData.runLemma412
    {sigma outputLoss delta sourceLoss normalizationLoss
      lemma43SourceLoss inputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := inputLoss) source (rho.1 / 2)}
    {normalizationExponent : ℕ}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) lemma43.shading normalizationExponent
        sourceLoss normalizationLoss}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := data.stickyLoss) lemma43.shading reentry rho)
    (rootAxialWindow : ∀ index point,
      point ∈ reentry.geometry.frame ''
          reentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (coarseAxialWindow : ∀ index point,
      point ∈ (rich.coarseReentry rootAxialWindow).geometry.frame ''
          (rich.coarseReentry rootAxialWindow).geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (rho_le : rho.1 ≤ cutoff.outerScaleCeiling)
    (lemma44 : Proposition63Lemma44Data lemma43 rich.data data.lemma44Loss)
    (lemma47 : Proposition63Lemma47Data lemma44 data.lemma47Loss
      (Real.rpow rho.1 (-data.lemma47Loss)))
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    Nonempty (Proposition63Lemma412OutputData lemma47 data.preGrainLoss) := by
  let schedule := data.m8.specialize rich.data.coarse_extremal.delta_pos
    rich.data.coarse_extremal.delta_le_one
  let inputs := cutoff.outerBindingInputsOfRich rich rootAxialWindow rho_le 1
  have rho_pos : 0 < rho.1 := rich.data.coarse_extremal.delta_pos
  exact proposition63_lemma412_output_of_lemma411_outer_inputs_lipschitz lemma47
    (rich.coarseReentry rootAxialWindow)
    coarseAxialWindow
    schedule 1 data.gridLoss_le_mid inputs data.lemma47Loss_le_outer_input
    (rho_le.trans cutoff.outerScaleCeiling_le_lemma412 |>.trans
      cutoff.lemma412Cutoff.rho_small) data.preGrain_pos
    data.lemma47Loss_lt_preGrain.le
    (by rw [data.gridLoss_eq]; linarith [data.preGrain_pos])
    hsigma hsigmaOne
    (cutoff.lemma412Cutoff.interpolation rho_pos
      (rho_le.trans cutoff.outerScaleCeiling_le_lemma412))
    (cutoff.lemma412Cutoff.fine rho_pos
      (rho_le.trans cutoff.outerScaleCeiling_le_lemma412))

/-- Strict axial specialization of `runLemma412`.  One genuine root margin
certificate supplies both the root `1 / 8` input and, through the rich
producer's exact frozen-cell provenance, the coarse `1 / 8` input. -/
theorem Proposition63M9PreNode3CutoffData.runLemma412OfAxialMargin
    {sigma outputLoss delta sourceLoss normalizationLoss
      lemma43SourceLoss inputLoss : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := inputLoss) source (rho.1 / 2)}
    {normalizationExponent : ℕ}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) lemma43.shading normalizationExponent
        sourceLoss normalizationLoss}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := data.stickyLoss) lemma43.shading reentry rho)
    (rootAxialMargin : ∀ index point,
      point ∈ reentry.geometry.frame ''
          reentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| + rho.1 ≤ 1 / 8)
    (rho_le : rho.1 ≤ cutoff.outerScaleCeiling)
    (lemma44 : Proposition63Lemma44Data lemma43 rich.data data.lemma44Loss)
    (lemma47 : Proposition63Lemma47Data lemma44 data.lemma47Loss
      (Real.rpow rho.1 (-data.lemma47Loss)))
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    Nonempty (Proposition63Lemma412OutputData lemma47 data.preGrainLoss) := by
  let rootAxialWindow :=
    proposition63_reentry_axial_window_of_margin reentry rho rootAxialMargin
  exact cutoff.runLemma412 rich rootAxialWindow
    (rich.coarse_reentry_axial_window_of_margin rootAxialMargin) rho_le
    lemma44 lemma47 hsigma hsigmaOne

def Proposition63M9PreRuntimeHierarchy.toTerminal
    {sigma outputLoss : ℝ}
    (data : Proposition63M9PreRuntimeHierarchy sigma outputLoss) :
    Proposition63TerminalLossHierarchy sigma outputLoss where
  N := data.lemma47N
  stickyLoss := data.stickyLoss
  lemma44Loss := data.lemma44Loss
  lemma47Loss := data.lemma47Loss
  preGrainLoss := data.preGrainLoss
  lemma47Schedule := data.lemma47Schedule
  N_two := data.lemma47N_two
  N_budget := data.lemma47N_budget
  sticky_pos := data.sticky_pos
  sticky_lt_lemma44 := data.sticky_lt_lemma44
  two_sticky_le_lemma44 := data.two_sticky_le_lemma44
  sticky_le_lemma47_root_source := data.sticky_le_lemma47_root_source
  two_sticky_le_lemma47_root_normalization :=
    data.two_sticky_le_lemma47_root_normalization
  lemma44_le_lemma47_input := data.lemma44_le_lemma47_input
  lemma47_input_le_final := data.lemma47_input_le_final
  lemma44_lt_lemma47 := data.lemma44_lt_lemma47
  lemma47_lt_preGrain := data.lemma47Loss_lt_preGrain
  preGrain_lt_output := data.preGrain_lt_output
  preGrain_lt_sigma_quarter := data.preGrain_lt_sigma_quarter
  sticky_le_sigma_half := data.sticky_le_sigma_half
  sigma_half_le_one_sub_sticky := data.sigma_half_le_one_sub_sticky

/-- Run the complete second rich call through Lemma 4.12 from one dependent
preparation package.  The package binds external-weight regularization and
the strict axial margin to the same normalized Lemma 4.3 source; the only
remaining inputs are the frozen scale inequalities. -/
theorem Proposition63M9PreNode3CutoffData.runSecondCallThroughLemma412
    {sigma outputLoss delta lemma43SourceLoss lemma43Loss
      _incidenceBudget : ℝ}
    {data : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData data)
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {ordinary : Kakeya.Streamlined.TubeShading family}
    {normalizationExponent : ℕ}
    (preparation : Proposition63SecondCallPreparationData
      lemma43 ordinary cutoff.richSchedule.sourceLoss
        cutoff.richSchedule.normalizationLoss normalizationExponent rho)
    (delta_le : delta ≤ cutoff.outerScaleCeiling)
    (rho_lower : Real.rpow delta (1 - data.stickyLoss) ≤ rho.1)
    (rho_upper : rho.1 ≤ Real.rpow delta data.stickyLoss)
    (rho_le : rho.1 ≤ cutoff.outerScaleCeiling)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    ∃ second : Proposition63ThroughLemma412Data
        (logExponent := 61) lemma43 ordinary preparation.prepared
        data.stickyLoss data.lemma44Loss data.lemma47Loss
        data.preGrainLoss
        (Real.rpow rho.1 (-data.lemma47Loss)),
      ∀ parent, ‖wz2PaperTubeMidpoint
        (second.sticky.coarse.tube parent)‖ ≤ 3 := by
  let prepared := preparation.prepared
  let reentry := prepared.normalization.toPropStickyReentryData
    prepared.target_loss_pos prepared.normalization_loss_pos
  rcases cutoff.richSchedule.runTerminal delta lemma43.extremal.delta_pos
      (delta_le.trans cutoff.outerScaleCeiling_le_rich)
      prepared.regularized.selected.family
      prepared.restrictedLemma43.shading reentry rho
      rho_lower rho_upper with
    ⟨rawRich⟩
  have rich : Proposition63RichTerminalStickyData
      (sigma := sigma) (outputLoss := data.stickyLoss)
      prepared.restrictedLemma43.shading reentry rho := by
    exact rawRich
  have rootAxialMargin := preparation.root_axial_margin
  let rootAxialWindow :=
    proposition63_reentry_axial_window_of_margin reentry rho rootAxialMargin
  have lemma44LossPos : 0 < data.lemma44Loss :=
    data.sticky_pos.trans data.sticky_lt_lemma44
  rcases proposition63_paper_lemma44_coarse_pair_of_terminal
      (terminalLoss := rich.terminalLoss)
      prepared.restrictedLemma43 reentry rich
      data.two_sticky_le_lemma44 lemma44LossPos with
    ⟨lemma44⟩
  rcases data.toTerminal.runLemma47 rich lemma44
      (rho_le.trans cutoff.outerScaleCeiling_le_lemma47)
      rootAxialWindow with
    ⟨lemma47⟩
  rcases cutoff.runLemma412OfAxialMargin rich rootAxialMargin rho_le
      lemma44 lemma47 hsigma hsigmaOne with
    ⟨lemma412⟩
  let second : Proposition63ThroughLemma412Data
      (logExponent := 61) lemma43 ordinary preparation.prepared
      data.stickyLoss data.lemma44Loss data.lemma47Loss
      data.preGrainLoss
      (Real.rpow rho.1 (-data.lemma47Loss)) := {
    sticky := rich.data
    lemma44 := lemma44
    lemma47 := lemma47
    lemma412 := lemma412
  }
  exact ⟨second, by
    intro parent
    exact rich.coarse_midpoint_local parent⟩

end Kakeya.Assouad.PureWZ2
