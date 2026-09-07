import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantPrefix

/-!
# Variable-depth backward schedule for the reentrant hierarchy

This is the reentrant analogue of `PureWZ2OrdinaryPrefixScheduleData`.  The
losses and all scale cutoffs are selected backwards before a runtime source
exists.  The forward constructor then consumes the literal `step.next` source
at each of the first `N - 1` paper scales.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Backward-chosen parameters for `N - 1` source-dependent reentrant calls. -/
structure PureWZ2ReentrantPrefixScheduleData
    (N : ℕ) (sigma hierarchyLoss : ℝ)
    (normalizationExponent : ℕ) where
  levelCount_two : 2 ≤ N
  exactSourceCeiling : ℝ
  exactSourceCeiling_pos : 0 < exactSourceCeiling
  outputLoss : Fin (N - 1) → ℝ
  sourceCeiling : Fin (N - 1) → ℝ
  deltaThreshold : Fin (N - 1) → ℝ
  produce : ∀ level : Fin (N - 1),
    ∀ inputLoss : ℝ, 0 < inputLoss → inputLoss ≤ sourceCeiling level →
      ∀ delta : ℝ, 0 < delta → delta ≤ deltaThreshold level →
        ∀ current : PureWZ2ReentrantGrainSource
            sigma inputLoss delta normalizationExponent,
          ∀ rho : ℝ, delta ≤ rho → rho ≤ 1 →
            Real.rpow delta (1 - outputLoss level) ≤ rho →
            rho ≤ Real.rpow delta (outputLoss level) →
              Nonempty
                (PureWZ2ReentrantOneScaleOutput
                  current (outputLoss level) rho)
  outputLoss_pos : ∀ level, 0 < outputLoss level
  sourceCeiling_pos : ∀ level, 0 < sourceCeiling level
  deltaThreshold_pos : ∀ level, 0 < deltaThreshold level
  deltaThreshold_le_one : ∀ level, deltaThreshold level ≤ 1
  sourceCeiling_le :
    ∀ level, sourceCeiling level ≤ outputLoss level / 100
  outputLoss_le_next_ceiling :
    ∀ level : Fin (N - 1), ∀ hnext : (level : ℕ) + 1 < N - 1,
      outputLoss level ≤ sourceCeiling ⟨(level : ℕ) + 1, hnext⟩
  outputLoss_le_hierarchy : ∀ level, outputLoss level ≤ hierarchyLoss
  outputLoss_le_half_levelCount :
    ∀ level, outputLoss level ≤ 1 / (2 * (N : ℝ))
  outputLoss_last_le_exactSourceCeiling :
    outputLoss ⟨N - 2, by omega⟩ ≤ exactSourceCeiling

namespace PureWZ2ReentrantPrefixScheduleData

variable {N : ℕ} {sigma hierarchyLoss : ℝ}
    {normalizationExponent : ℕ}
    (schedule : PureWZ2ReentrantPrefixScheduleData
      N sigma hierarchyLoss normalizationExponent)

private def finZero : Fin (N - 1) :=
  ⟨0, by have hN := schedule.levelCount_two; omega⟩

/-- Source loss accepted by the first reentrant call. -/
def initialSourceCeiling : ℝ :=
  schedule.sourceCeiling schedule.finZero

theorem initialSourceCeiling_pos : 0 < schedule.initialSourceCeiling :=
  schedule.sourceCeiling_pos _

/-- One cutoff valid at every ordinary level. -/
noncomputable def commonDeltaThreshold : ℝ :=
  let image : Finset ℝ := Finset.image schedule.deltaThreshold Finset.univ
  have hnonempty : image.Nonempty := by
    exact ⟨schedule.deltaThreshold schedule.finZero,
      Finset.mem_image.mpr ⟨schedule.finZero, Finset.mem_univ _, rfl⟩⟩
  Finset.min' image hnonempty

theorem commonDeltaThreshold_pos :
    0 < schedule.commonDeltaThreshold := by
  let image : Finset ℝ := Finset.image schedule.deltaThreshold Finset.univ
  have hnonempty : image.Nonempty := by
    exact ⟨schedule.deltaThreshold schedule.finZero,
      Finset.mem_image.mpr ⟨schedule.finZero, Finset.mem_univ _, rfl⟩⟩
  have hmem : Finset.min' image hnonempty ∈ image :=
    Finset.min'_mem image hnonempty
  rcases Finset.mem_image.mp hmem with ⟨level, _, hlevel⟩
  change 0 < Finset.min' image hnonempty
  rw [← hlevel]
  exact schedule.deltaThreshold_pos level

theorem commonDeltaThreshold_le (level : Fin (N - 1)) :
    schedule.commonDeltaThreshold ≤ schedule.deltaThreshold level := by
  let image : Finset ℝ := Finset.image schedule.deltaThreshold Finset.univ
  have hnonempty : image.Nonempty := by
    exact ⟨schedule.deltaThreshold schedule.finZero,
      Finset.mem_image.mpr ⟨schedule.finZero, Finset.mem_univ _, rfl⟩⟩
  exact Finset.min'_le image _
    (Finset.mem_image.mpr ⟨level, Finset.mem_univ _, rfl⟩)

theorem commonDeltaThreshold_le_one :
    schedule.commonDeltaThreshold ≤ 1 :=
  (schedule.commonDeltaThreshold_le schedule.finZero).trans
    (schedule.deltaThreshold_le_one schedule.finZero)

/-- The paper scale at every nonterminal level lies in the window fixed by
the corresponding backward-scheduled producer. -/
theorem scale_window
    (level : Fin (N - 1))
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    let levelN : Fin N := ⟨level, by omega⟩
    Real.rpow delta (1 - schedule.outputLoss level) ≤
        wz1Corollary26Scale delta N levelN ∧
      wz1Corollary26Scale delta N levelN ≤
        Real.rpow delta (schedule.outputLoss level) := by
  let levelN : Fin N := ⟨level, by omega⟩
  by_cases hstrict : delta < 1
  · have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast (show 0 < N by
        have hN := schedule.levelCount_two
        omega)
    have hlossHalf := schedule.outputLoss_le_half_levelCount level
    have hhalfLe : 1 / (2 * (N : ℝ)) ≤ 1 / (N : ℝ) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    have hlossN : schedule.outputLoss level ≤ 1 / (N : ℝ) :=
      hlossHalf.trans hhalfLe
    have hlevelUpper :
        (((levelN : ℕ) + 1 : ℝ) / (N : ℝ)) ≤
          1 - 1 / (N : ℝ) := by
      have hnat : (levelN : ℕ) + 2 ≤ N := by
        have hlevelBound := level.isLt
        dsimp only [levelN]
        omega
      have hreal : ((levelN : ℕ) + 2 : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hnat
      rw [div_le_iff₀ hNpos]
      field_simp [hNpos.ne']
      linarith
    have hlowerExponent :
        (((levelN : ℕ) + 1 : ℝ) / (N : ℝ)) ≤
          1 - schedule.outputLoss level := by
      linarith
    have hlevelLower : 1 / (N : ℝ) ≤
        (((levelN : ℕ) + 1 : ℝ) / (N : ℝ)) := by
      apply div_le_div_of_nonneg_right
      · norm_num
      · positivity
    have hupperExponent : schedule.outputLoss level ≤
        (((levelN : ℕ) + 1 : ℝ) / (N : ℝ)) :=
      hlossN.trans hlevelLower
    exact
      ⟨Real.rpow_le_rpow_of_exponent_ge
          hdelta hstrict.le hlowerExponent,
        Real.rpow_le_rpow_of_exponent_ge
          hdelta hstrict.le hupperExponent⟩
  · have hdeltaEq : delta = 1 := by linarith
    simp [hdeltaEq, wz1Corollary26Scale]

end PureWZ2ReentrantPrefixScheduleData

namespace PureWZ2ReentrantPrefixSchedule

private abbrev ProducerFn
    (sigma : ℝ) (normalizationExponent : ℕ)
    (outputLoss sourceCeiling deltaThreshold : ℝ) : Prop :=
  ∀ inputLoss : ℝ, 0 < inputLoss → inputLoss ≤ sourceCeiling →
    ∀ delta : ℝ, 0 < delta → delta ≤ deltaThreshold →
      ∀ current : PureWZ2ReentrantGrainSource
          sigma inputLoss delta normalizationExponent,
        ∀ rho : ℝ, delta ≤ rho → rho ≤ 1 →
          Real.rpow delta (1 - outputLoss) ≤ rho →
          rho ≤ Real.rpow delta outputLoss →
            Nonempty
              (PureWZ2ReentrantOneScaleOutput current outputLoss rho)

private structure ReversedLevel
    (N : ℕ) (sigma hierarchyLoss exactSourceCeiling : ℝ)
    (normalizationExponent : ℕ) where
  outputLoss : ℝ
  sourceCeiling : ℝ
  deltaThreshold : ℝ
  produce : ProducerFn sigma normalizationExponent outputLoss
    sourceCeiling deltaThreshold
  outputLoss_pos : 0 < outputLoss
  sourceCeiling_pos : 0 < sourceCeiling
  deltaThreshold_pos : 0 < deltaThreshold
  deltaThreshold_le_one : deltaThreshold ≤ 1
  sourceCeiling_le : sourceCeiling ≤ outputLoss / 100
  outputLoss_le_hierarchy : outputLoss ≤ hierarchyLoss
  outputLoss_le_half : outputLoss ≤ 1 / (2 * (N : ℝ))
  outputLoss_le_exact : outputLoss ≤ exactSourceCeiling

private noncomputable def buildReversed
    {N : ℕ} {sigma hierarchyLoss exactSourceCeiling : ℝ}
    {normalizationExponent : ℕ}
    (intermediate :
      PureWZ2ReentrantOneScaleAtStatement sigma normalizationExponent)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hexactSourceCeiling : 0 < exactSourceCeiling)
    (hN : 2 ≤ N) :
    ℕ → ReversedLevel N sigma hierarchyLoss exactSourceCeiling
      normalizationExponent
  | 0 => by
      let outputLoss := min exactSourceCeiling
        (min hierarchyLoss (1 / (2 * (N : ℝ))))
      have houtputLoss : 0 < outputLoss := by
        exact lt_min hexactSourceCeiling
          (lt_min hhierarchyLoss (by positivity))
      let existsData := intermediate outputLoss
        hsigma hsigmaOne houtputLoss
      let sourceCeiling := Classical.choose existsData
      let thresholdData := Classical.choose_spec existsData
      let deltaThreshold := Classical.choose thresholdData
      let data := Classical.choose_spec thresholdData
      exact {
        outputLoss := outputLoss
        sourceCeiling := sourceCeiling
        deltaThreshold := deltaThreshold
        produce := data.2.2.2.2
        outputLoss_pos := houtputLoss
        sourceCeiling_pos := data.1
        deltaThreshold_pos := data.2.2.1
        deltaThreshold_le_one := data.2.2.2.1
        sourceCeiling_le := data.2.1
        outputLoss_le_hierarchy :=
          (min_le_right _ _).trans (min_le_left _ _)
        outputLoss_le_half :=
          (min_le_right _ _).trans (min_le_right _ _)
        outputLoss_le_exact := min_le_left _ _ }
  | index + 1 => by
      let next := buildReversed intermediate hsigma hsigmaOne
        hhierarchyLoss hexactSourceCeiling hN index
      let outputLoss := min next.sourceCeiling
        (min hierarchyLoss (1 / (2 * (N : ℝ))))
      have houtputLoss : 0 < outputLoss := by
        exact lt_min next.sourceCeiling_pos
          (lt_min hhierarchyLoss (by positivity))
      let existsData := intermediate outputLoss
        hsigma hsigmaOne houtputLoss
      let sourceCeiling := Classical.choose existsData
      let thresholdData := Classical.choose_spec existsData
      let deltaThreshold := Classical.choose thresholdData
      let data := Classical.choose_spec thresholdData
      exact {
        outputLoss := outputLoss
        sourceCeiling := sourceCeiling
        deltaThreshold := deltaThreshold
        produce := data.2.2.2.2
        outputLoss_pos := houtputLoss
        sourceCeiling_pos := data.1
        deltaThreshold_pos := data.2.2.1
        deltaThreshold_le_one := data.2.2.2.1
        sourceCeiling_le := data.2.1
        outputLoss_le_hierarchy :=
          (min_le_right _ _).trans (min_le_left _ _)
        outputLoss_le_half :=
          (min_le_right _ _).trans (min_le_right _ _)
        outputLoss_le_exact := by
          have hsourceOutput : next.sourceCeiling ≤ next.outputLoss :=
            next.sourceCeiling_le.trans (by
              have hpos := next.outputLoss_pos
              linarith)
          exact (min_le_left _ _).trans
            (hsourceOutput.trans next.outputLoss_le_exact) }

private theorem buildReversed_succ_output_le_previous_ceiling
    {N : ℕ} {sigma hierarchyLoss exactSourceCeiling : ℝ}
    {normalizationExponent : ℕ}
    (intermediate :
      PureWZ2ReentrantOneScaleAtStatement sigma normalizationExponent)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hexactSourceCeiling : 0 < exactSourceCeiling)
    (hN : 2 ≤ N) (index : ℕ) :
    (buildReversed intermediate hsigma hsigmaOne hhierarchyLoss
      hexactSourceCeiling hN (index + 1)).outputLoss ≤
    (buildReversed intermediate hsigma hsigmaOne hhierarchyLoss
      hexactSourceCeiling hN index).sourceCeiling := by
  simp [buildReversed]

/-- Construct all reentrant ordinary losses in backwards paper order. -/
noncomputable def construct
    {sigma hierarchyLoss exactSourceCeiling : ℝ}
    {normalizationExponent : ℕ}
    (intermediate :
      PureWZ2ReentrantOneScaleAtStatement sigma normalizationExponent)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hexactSourceCeiling : 0 < exactSourceCeiling)
    {N : ℕ} (hN : 2 ≤ N) :
    PureWZ2ReentrantPrefixScheduleData
      N sigma hierarchyLoss normalizationExponent := by
  let reversed := buildReversed intermediate hsigma hsigmaOne
    hhierarchyLoss hexactSourceCeiling hN
  let outputLoss : Fin (N - 1) → ℝ := fun level =>
    (reversed (N - 2 - (level : ℕ))).outputLoss
  let sourceCeiling : Fin (N - 1) → ℝ := fun level =>
    (reversed (N - 2 - (level : ℕ))).sourceCeiling
  let deltaThreshold : Fin (N - 1) → ℝ := fun level =>
    (reversed (N - 2 - (level : ℕ))).deltaThreshold
  have hlastIndex : N - 2 - (N - 2) = 0 := by omega
  refine {
    levelCount_two := hN
    exactSourceCeiling := exactSourceCeiling
    exactSourceCeiling_pos := hexactSourceCeiling
    outputLoss := outputLoss
    sourceCeiling := sourceCeiling
    deltaThreshold := deltaThreshold
    produce := ?_
    outputLoss_pos := ?_
    sourceCeiling_pos := ?_
    deltaThreshold_pos := ?_
    deltaThreshold_le_one := ?_
    sourceCeiling_le := ?_
    outputLoss_le_next_ceiling := ?_
    outputLoss_le_hierarchy := ?_
    outputLoss_le_half_levelCount := ?_
    outputLoss_last_le_exactSourceCeiling := ?_ }
  · intro level
    exact (reversed (N - 2 - (level : ℕ))).produce
  · intro level
    exact (reversed (N - 2 - (level : ℕ))).outputLoss_pos
  · intro level
    exact (reversed (N - 2 - (level : ℕ))).sourceCeiling_pos
  · intro level
    exact (reversed (N - 2 - (level : ℕ))).deltaThreshold_pos
  · intro level
    exact (reversed (N - 2 - (level : ℕ))).deltaThreshold_le_one
  · intro level
    exact (reversed (N - 2 - (level : ℕ))).sourceCeiling_le
  · intro level hnext
    have hindex : ∃ index, N - 2 - (level : ℕ) = index + 1 := by
      exact ⟨N - 3 - (level : ℕ), by omega⟩
    rcases hindex with ⟨index, hindex⟩
    have hnextIndex : N - 2 - ((level : ℕ) + 1) = index := by omega
    dsimp only [outputLoss, sourceCeiling]
    rw [hindex, hnextIndex]
    exact buildReversed_succ_output_le_previous_ceiling intermediate
      hsigma hsigmaOne hhierarchyLoss hexactSourceCeiling hN index
  · intro level
    exact (reversed (N - 2 - (level : ℕ))).outputLoss_le_hierarchy
  · intro level
    exact (reversed (N - 2 - (level : ℕ))).outputLoss_le_half
  · dsimp only [outputLoss]
    rw [hlastIndex]
    exact (reversed 0).outputLoss_le_exact

end PureWZ2ReentrantPrefixSchedule

private noncomputable def pureWZ2RunReentrantPrefixLevel
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    {normalizationExponent : ℕ}
    (schedule : PureWZ2ReentrantPrefixScheduleData
      N sigma hierarchyLoss normalizationExponent)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (level : Fin (N - 1))
    {inputLoss : ℝ}
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent)
    (hinputLoss : 0 < inputLoss)
    (hinputCeiling : inputLoss ≤ schedule.sourceCeiling level) :
    PureWZ2ReentrantOneScaleOutput current (schedule.outputLoss level)
      (wz1Corollary26Scale delta N ⟨level, by omega⟩) := by
  have hdeltaLevel : delta ≤ schedule.deltaThreshold level :=
    hdeltaThreshold.trans (schedule.commonDeltaThreshold_le level)
  have hwindow := schedule.scale_window level hdelta hdeltaOne
  exact (schedule.produce level inputLoss hinputLoss hinputCeiling
    delta hdelta hdeltaLevel current
    (wz1Corollary26Scale delta N ⟨level, by omega⟩)
    (pureWZ2Hierarchy_delta_le_scale schedule.levelCount_two
      hdelta hdeltaOne ⟨level, by omega⟩)
    (pureWZ2HierarchyScale_le_one hdelta hdeltaOne ⟨level, by omega⟩)
    hwindow.1 hwindow.2).some

private noncomputable def pureWZ2BuildReentrantPrefixFrom
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    {normalizationExponent : ℕ}
    (schedule : PureWZ2ReentrantPrefixScheduleData
      N sigma hierarchyLoss normalizationExponent)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (level remaining : ℕ) (hlevels : level + remaining = N - 1)
    {inputLoss : ℝ}
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent)
    (hinputLoss : 0 < inputLoss)
    (hinputCeiling : ∀ hremaining : 0 < remaining,
      inputLoss ≤ schedule.sourceCeiling ⟨level, by omega⟩) :
    PureWZ2ReentrantPrefixChain sigma delta normalizationExponent
      current remaining :=
  match remaining with
  | 0 => .nil current
  | next + 1 => by
      let levelPrefix : Fin (N - 1) := ⟨level, by omega⟩
      let output := pureWZ2RunReentrantPrefixLevel schedule hdelta
        hdeltaOne hdeltaThreshold levelPrefix current hinputLoss
        (hinputCeiling (by omega))
      have hnextCeiling : ∀ hnext : 0 < next,
          schedule.outputLoss levelPrefix ≤
            schedule.sourceCeiling ⟨level + 1, by omega⟩ := by
        intro hnext
        have hlevelNext : level + 1 < N - 1 := by omega
        exact schedule.outputLoss_le_next_ceiling levelPrefix hlevelNext
      exact .cons output.step
        (pureWZ2BuildReentrantPrefixFrom schedule hdelta hdeltaOne
          hdeltaThreshold (level + 1) next (by omega) output.step.next
          (schedule.outputLoss_pos levelPrefix) hnextCeiling)
termination_by remaining

private theorem pureWZ2BuildReentrantPrefixFrom_outputAt
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    {normalizationExponent : ℕ}
    (schedule : PureWZ2ReentrantPrefixScheduleData
      N sigma hierarchyLoss normalizationExponent)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (level remaining : ℕ) (hlevels : level + remaining = N - 1)
    {inputLoss : ℝ}
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent)
    (hinputLoss : 0 < inputLoss)
    (hinputCeiling : ∀ hremaining : 0 < remaining,
      inputLoss ≤ schedule.sourceCeiling ⟨level, by omega⟩)
    (index : Fin remaining) :
    let chain := pureWZ2BuildReentrantPrefixFrom schedule hdelta hdeltaOne
      hdeltaThreshold level remaining hlevels current hinputLoss hinputCeiling
    let scheduleLevel : Fin (N - 1) := ⟨level + (index : ℕ), by omega⟩
    (chain.outputAt index).outputLoss = schedule.outputLoss scheduleLevel ∧
      (chain.outputAt index).rho =
        wz1Corollary26Scale delta N ⟨scheduleLevel, by omega⟩ := by
  induction remaining generalizing level inputLoss current with
  | zero =>
      exact Fin.elim0 index
  | succ next ih =>
      refine Fin.cases ?_ (fun later => ?_) index
      · simp [pureWZ2BuildReentrantPrefixFrom,
          PureWZ2ReentrantPrefixChain.outputAt]
      · let levelPrefix : Fin (N - 1) := ⟨level, by omega⟩
        let output := pureWZ2RunReentrantPrefixLevel schedule hdelta
          hdeltaOne hdeltaThreshold levelPrefix current hinputLoss
          (hinputCeiling (by omega))
        have hnextCeiling : ∀ hnext : 0 < next,
            schedule.outputLoss levelPrefix ≤
              schedule.sourceCeiling ⟨level + 1, by omega⟩ := by
          intro hnext
          have hlevelNext : level + 1 < N - 1 := by omega
          exact schedule.outputLoss_le_next_ceiling
            levelPrefix hlevelNext
        have hrec := ih (level := level + 1) (by omega)
          output.step.next (schedule.outputLoss_pos levelPrefix)
          hnextCeiling later
        have houtputEq :
            pureWZ2RunReentrantPrefixLevel schedule hdelta hdeltaOne
                hdeltaThreshold (⟨level, by omega⟩ : Fin (N - 1))
                current hinputLoss (hinputCeiling (by omega)) =
              output := by
          dsimp only [output, levelPrefix]
        rw [pureWZ2BuildReentrantPrefixFrom]
        dsimp only
        rw [houtputEq]
        rw [PureWZ2ReentrantPrefixChain.outputAt_cons_succ]
        change
          let tail := pureWZ2BuildReentrantPrefixFrom schedule hdelta
            hdeltaOne hdeltaThreshold (level + 1) next (by omega)
            output.step.next (schedule.outputLoss_pos levelPrefix)
            hnextCeiling
          (tail.outputAt later).outputLoss =
              schedule.outputLoss
                (⟨level + (later.succ : ℕ), by omega⟩ :
                  Fin (N - 1)) ∧
            (tail.outputAt later).rho =
              wz1Corollary26Scale delta N
                ⟨level + (later.succ : ℕ), by omega⟩
        rcases hrec with ⟨hloss, hrho⟩
        have hindex :
            (⟨level + (later.succ : ℕ), by omega⟩ : Fin (N - 1)) =
              ⟨level + 1 + (later : ℕ), by omega⟩ := by
          apply Fin.ext
          change level + ((later : ℕ) + 1) =
            level + 1 + (later : ℕ)
          omega
        constructor
        · rw [hindex]
          exact hloss
        · have htotal :
              (⟨level + (later.succ : ℕ), by omega⟩ : Fin N) =
                ⟨level + 1 + (later : ℕ), by omega⟩ := by
            apply Fin.ext
            change level + ((later : ℕ) + 1) =
              level + 1 + (later : ℕ)
            omega
          rw [htotal]
          exact hrho

/-- The complete literal `N - 1` chain together with its schedule provenance. -/
structure PureWZ2ReentrantPrefixConstructionData
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    {normalizationExponent : ℕ}
    (schedule : PureWZ2ReentrantPrefixScheduleData
      N sigma hierarchyLoss normalizationExponent)
    {initialLoss : ℝ}
    (initial : PureWZ2ReentrantGrainSource sigma
      initialLoss delta normalizationExponent) where
  chain : PureWZ2ReentrantPrefixChain sigma delta normalizationExponent
    initial (N - 1)
  compatible : chain.IsHierarchyPrefix hierarchyLoss N
  outputLoss_eq : ∀ level : Fin (N - 1),
    (chain.outputAt level).outputLoss = schedule.outputLoss level

/-- Run all `N - 1` scheduled reentrant calls, each on the literal next source
returned by its predecessor. -/
noncomputable def pureWZ2_construct_reentrant_prefix_chain
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    {normalizationExponent : ℕ}
    (schedule : PureWZ2ReentrantPrefixScheduleData
      N sigma hierarchyLoss normalizationExponent)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    {initialLoss : ℝ}
    (initial : PureWZ2ReentrantGrainSource sigma
      initialLoss delta normalizationExponent)
    (hinitialLoss : 0 < initialLoss)
    (hinitialCeiling : initialLoss ≤ schedule.initialSourceCeiling) :
    PureWZ2ReentrantPrefixConstructionData schedule initial := by
  let chain := pureWZ2BuildReentrantPrefixFrom schedule hdelta hdeltaOne
    hdeltaThreshold 0 (N - 1) (by omega) initial
    hinitialLoss (by
      intro _
      exact hinitialCeiling)
  have houtput : ∀ level : Fin (N - 1),
      (chain.outputAt level).outputLoss = schedule.outputLoss level := by
    intro level
    have hresult := pureWZ2BuildReentrantPrefixFrom_outputAt schedule
      hdelta hdeltaOne hdeltaThreshold 0 (N - 1) (by omega) initial
      hinitialLoss (by
        intro _
        exact hinitialCeiling) level
    simpa [chain] using hresult.1
  refine {
    chain := chain
    compatible := {
      levelCount_two := schedule.levelCount_two
      levelCount_succ := by
        have hN := schedule.levelCount_two
        omega
      outputLoss_le := ?_
      rho_eq := ?_ }
    outputLoss_eq := houtput }
  · intro level
    rw [houtput level]
    exact schedule.outputLoss_le_hierarchy level
  · intro level
    have hresult := pureWZ2BuildReentrantPrefixFrom_outputAt schedule
      hdelta hdeltaOne hdeltaThreshold 0 (N - 1) (by omega) initial
      hinitialLoss (by
        intro _
        exact hinitialCeiling) level
    simpa [chain] using hresult.2

namespace PureWZ2ReentrantPrefixConstructionData

variable
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    {normalizationExponent : ℕ}
    {schedule : PureWZ2ReentrantPrefixScheduleData
      N sigma hierarchyLoss normalizationExponent}
    {initialLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource sigma
      initialLoss delta normalizationExponent}
    (construction : PureWZ2ReentrantPrefixConstructionData schedule initial)

theorem finalLoss_pos : 0 < construction.chain.finalSource.1 := by
  have hcount : 0 < N - 1 := by
    have hN := schedule.levelCount_two
    omega
  rw [construction.chain.finalSource_loss_eq_last_outputAt hcount]
  rw [construction.outputLoss_eq]
  exact schedule.outputLoss_pos _

theorem finalLoss_le_exactSourceCeiling :
    construction.chain.finalSource.1 ≤ schedule.exactSourceCeiling := by
  have hcount : 0 < N - 1 := by
    have hN := schedule.levelCount_two
    omega
  rw [construction.chain.finalSource_loss_eq_last_outputAt hcount]
  rw [construction.outputLoss_eq]
  have hlast :
      (⟨N - 1 - 1, by omega⟩ : Fin (N - 1)) =
        ⟨N - 2, by omega⟩ := by
    apply Fin.ext
    change N - 1 - 1 = N - 2
    omega
  rw [hlast]
  exact schedule.outputLoss_last_le_exactSourceCeiling

/-- The variable chain's complete ordinary hierarchy on its literal final
source. -/
noncomputable def toOrdinaryPrefix :
    PureWZ2OrdinaryHierarchyPrefixData
      construction.chain.finalSource.2.grain hierarchyLoss N :=
  construction.chain.toOrdinaryPrefix construction.compatible

end PureWZ2ReentrantPrefixConstructionData

end Kakeya.Assouad

end
