import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleStatements

/-!
# Backward loss schedule for the Pure WZ2 Corollary 5.6 hierarchy

This is the paper's finite parameter choice in Lemma 25 / Corollary 26.
The finest (terminal) loss is chosen first.  Every preceding Lemma-24 loss
is then chosen small enough to be admitted as the source loss at the next
level.  No tube structure or geometric conclusion is added here.
-/

noncomputable section

namespace Kakeya.Assouad

private abbrev PureWZ2TerminalProducerFn
    (sigma outputLoss sourceCeiling deltaThreshold : ℝ) : Prop :=
  ∀ inputLoss : ℝ, 0 < inputLoss → inputLoss ≤ sourceCeiling →
    ∀ delta : ℝ, 0 < delta → delta ≤ deltaThreshold →
      ∀ source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta,
        Nonempty (PureWZ2LocallyLinearOneScaleData
          source outputLoss delta)

private abbrev PureWZ2IntermediateProducerFn
    (sigma outputLoss sourceCeiling deltaThreshold : ℝ) : Prop :=
  ∀ inputLoss : ℝ, 0 < inputLoss → inputLoss ≤ sourceCeiling →
    ∀ delta : ℝ, 0 < delta → delta ≤ deltaThreshold →
      ∀ source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta,
        ∀ rho : ℝ,
          delta ≤ rho → rho ≤ 1 →
          Real.rpow delta (1 - outputLoss) ≤ rho →
          rho ≤ Real.rpow delta outputLoss →
            Nonempty (PureWZ2LocallyLinearOneScaleData
              source outputLoss rho)

def pureWZ2FinLast (N : ℕ) (hN : 2 ≤ N) : Fin N :=
  ⟨N - 1, by omega⟩

/-- A complete backward-recursive loss schedule for the paper scales
`rho_j = delta^((j+1)/N)`. -/
structure PureWZ2BackwardScheduleData
    (N : ℕ) (sigma hierarchyLoss : ℝ) where
  levelCount_two : 2 ≤ N
  outputLoss : Fin N → ℝ
  sourceCeiling : Fin N → ℝ
  deltaThreshold : Fin N → ℝ
  produce_intermediate :
    ∀ level : Fin N, (level : ℕ) + 1 < N →
      PureWZ2IntermediateProducerFn sigma (outputLoss level)
        (sourceCeiling level) (deltaThreshold level)
  terminalLoss : ℝ
  terminalLoss_pos : 0 < terminalLoss
  terminalLoss_le_hierarchyLoss : terminalLoss ≤ hierarchyLoss
  produce_terminal :
    PureWZ2TerminalProducerFn sigma terminalLoss
      (sourceCeiling (pureWZ2FinLast N levelCount_two))
      (deltaThreshold (pureWZ2FinLast N levelCount_two))
  outputLoss_pos : ∀ level, 0 < outputLoss level
  sourceCeiling_pos : ∀ level, 0 < sourceCeiling level
  deltaThreshold_pos : ∀ level, 0 < deltaThreshold level
  deltaThreshold_le_one : ∀ level, deltaThreshold level ≤ 1
  sourceCeiling_le :
    ∀ level, sourceCeiling level ≤ outputLoss level / 100
  outputLoss_last :
    outputLoss (pureWZ2FinLast N levelCount_two) = terminalLoss
  outputLoss_le_next_ceiling :
    ∀ level : Fin N, ∀ hnext : (level : ℕ) + 1 < N,
      outputLoss level ≤ sourceCeiling ⟨(level : ℕ) + 1, hnext⟩
  outputLoss_le_terminal : ∀ level, outputLoss level ≤ terminalLoss
  outputLoss_le_half_levelCount :
    ∀ level : Fin N, (level : ℕ) + 1 < N →
      outputLoss level ≤ 1 / (2 * (N : ℝ))

namespace PureWZ2BackwardScheduleData

variable {N : ℕ} {sigma hierarchyLoss : ℝ}
    (schedule : PureWZ2BackwardScheduleData N sigma hierarchyLoss)

private def finZero (N : ℕ) (hN : 2 ≤ N) : Fin N :=
  ⟨0, by omega⟩

/-- Source loss accepted at the first (coarsest) hierarchy level. -/
def initialSourceCeiling : ℝ :=
  schedule.sourceCeiling (finZero N schedule.levelCount_two)

theorem initialSourceCeiling_pos : 0 < schedule.initialSourceCeiling :=
  schedule.sourceCeiling_pos _

theorem initialSourceCeiling_le_hierarchyLoss_div_100 :
    schedule.initialSourceCeiling ≤ hierarchyLoss / 100 := by
  have hfirst := schedule.sourceCeiling_le
    (finZero N schedule.levelCount_two)
  have hwork := schedule.outputLoss_le_terminal
    (finZero N schedule.levelCount_two)
  have hterminal := schedule.terminalLoss_le_hierarchyLoss
  exact hfirst.trans ((div_le_div_of_nonneg_right
    (hwork.trans hterminal) (by norm_num)))

/-- One threshold valid at every level of the finite hierarchy. -/
noncomputable def commonDeltaThreshold : ℝ :=
  let image : Finset ℝ := Finset.image schedule.deltaThreshold Finset.univ
  have hnonempty : image.Nonempty := by
    exact ⟨schedule.deltaThreshold (finZero N schedule.levelCount_two),
      Finset.mem_image.mpr
        ⟨finZero N schedule.levelCount_two, Finset.mem_univ _, rfl⟩⟩
  Finset.min' image hnonempty

theorem commonDeltaThreshold_pos : 0 < schedule.commonDeltaThreshold := by
  let image : Finset ℝ := Finset.image schedule.deltaThreshold Finset.univ
  have hnonempty : image.Nonempty := by
    exact ⟨schedule.deltaThreshold (finZero N schedule.levelCount_two),
      Finset.mem_image.mpr
        ⟨finZero N schedule.levelCount_two, Finset.mem_univ _, rfl⟩⟩
  have hmem : Finset.min' image hnonempty ∈ image :=
    Finset.min'_mem image hnonempty
  rcases Finset.mem_image.mp hmem with ⟨level, _, hlevel⟩
  change 0 < Finset.min' image hnonempty
  rw [← hlevel]
  exact schedule.deltaThreshold_pos level

theorem commonDeltaThreshold_le (level : Fin N) :
    schedule.commonDeltaThreshold ≤ schedule.deltaThreshold level := by
  let image : Finset ℝ := Finset.image schedule.deltaThreshold Finset.univ
  have hnonempty : image.Nonempty := by
    exact ⟨schedule.deltaThreshold (finZero N schedule.levelCount_two),
      Finset.mem_image.mpr
        ⟨finZero N schedule.levelCount_two, Finset.mem_univ _, rfl⟩⟩
  exact Finset.min'_le image _
    (Finset.mem_image.mpr ⟨level, Finset.mem_univ _, rfl⟩)

theorem commonDeltaThreshold_le_one :
    schedule.commonDeltaThreshold ≤ 1 :=
  (schedule.commonDeltaThreshold_le
      (finZero N schedule.levelCount_two)).trans
    (schedule.deltaThreshold_le_one
      (finZero N schedule.levelCount_two))

/-- The paper scale at a nonterminal level lies in the window accepted by
that level's one-scale producer. -/
theorem scale_window
    (level : Fin N) (hnext : (level : ℕ) + 1 < N)
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    Real.rpow delta (1 - schedule.outputLoss level) ≤
        wz1Corollary26Scale delta N level ∧
      wz1Corollary26Scale delta N level ≤
        Real.rpow delta (schedule.outputLoss level) := by
  by_cases hstrict : delta < 1
  · have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast (show 0 < N by omega)
    have hlossHalf :=
      schedule.outputLoss_le_half_levelCount level hnext
    have hhalfLe : 1 / (2 * (N : ℝ)) ≤ 1 / (N : ℝ) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    have hlossN : schedule.outputLoss level ≤ 1 / (N : ℝ) :=
      hlossHalf.trans hhalfLe
    have hlevelUpper :
        (((level : ℕ) + 1 : ℝ) / (N : ℝ)) ≤
          1 - 1 / (N : ℝ) := by
      have hnat : (level : ℕ) + 2 ≤ N := by omega
      have hreal : ((level : ℕ) + 2 : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hnat
      rw [div_le_iff₀ hNpos]
      field_simp [hNpos.ne']
      linarith
    have hlowerExponent :
        (((level : ℕ) + 1 : ℝ) / (N : ℝ)) ≤
          1 - schedule.outputLoss level := by
      linarith
    have hlevelLower : 1 / (N : ℝ) ≤
        (((level : ℕ) + 1 : ℝ) / (N : ℝ)) := by
      apply div_le_div_of_nonneg_right
      · norm_num
      · positivity
    have hupperExponent : schedule.outputLoss level ≤
        (((level : ℕ) + 1 : ℝ) / (N : ℝ)) :=
      hlossN.trans hlevelLower
    exact ⟨
      Real.rpow_le_rpow_of_exponent_ge hdelta hstrict.le hlowerExponent,
      Real.rpow_le_rpow_of_exponent_ge hdelta hstrict.le hupperExponent⟩
  · have hdeltaEq : delta = 1 := by linarith
    simp [hdeltaEq, wz1Corollary26Scale]

end PureWZ2BackwardScheduleData

namespace PureWZ2BackwardSchedule

private inductive ReversedLevel
    (N : ℕ) (sigma terminalLoss : ℝ) where
  | terminal (sourceCeiling deltaThreshold : ℝ)
      (produce : PureWZ2TerminalProducerFn sigma terminalLoss
        sourceCeiling deltaThreshold)
      (sourceCeiling_pos : 0 < sourceCeiling)
      (deltaThreshold_pos : 0 < deltaThreshold)
      (deltaThreshold_le_one : deltaThreshold ≤ 1)
      (sourceCeiling_le : sourceCeiling ≤ terminalLoss / 100)
  | intermediate (outputLoss sourceCeiling deltaThreshold : ℝ)
      (produce : PureWZ2IntermediateProducerFn sigma outputLoss
        sourceCeiling deltaThreshold)
      (outputLoss_pos : 0 < outputLoss)
      (sourceCeiling_pos : 0 < sourceCeiling)
      (deltaThreshold_pos : 0 < deltaThreshold)
      (deltaThreshold_le_one : deltaThreshold ≤ 1)
      (sourceCeiling_le : sourceCeiling ≤ outputLoss / 100)
      (outputLoss_le_terminal : outputLoss ≤ terminalLoss)
      (outputLoss_le_half : outputLoss ≤ 1 / (2 * (N : ℝ)))

private def ReversedLevel.outputLoss
    {N sigma terminalLoss}
    (level : ReversedLevel N sigma terminalLoss) : ℝ :=
  match level with
  | .terminal _ _ _ _ _ _ _ => terminalLoss
  | .intermediate outputLoss _ _ _ _ _ _ _ _ _ _ => outputLoss

private def ReversedLevel.sourceCeiling
    {N sigma terminalLoss}
    (level : ReversedLevel N sigma terminalLoss) : ℝ :=
  match level with
  | .terminal sourceCeiling _ _ _ _ _ _ => sourceCeiling
  | .intermediate _ sourceCeiling _ _ _ _ _ _ _ _ _ => sourceCeiling

private def ReversedLevel.deltaThreshold
    {N sigma terminalLoss}
    (level : ReversedLevel N sigma terminalLoss) : ℝ :=
  match level with
  | .terminal _ deltaThreshold _ _ _ _ _ => deltaThreshold
  | .intermediate _ _ deltaThreshold _ _ _ _ _ _ _ _ => deltaThreshold

private def ReversedLevel.isIntermediate
    {N sigma terminalLoss}
    (level : ReversedLevel N sigma terminalLoss) : Bool :=
  match level with
  | .terminal _ _ _ _ _ _ _ => false
  | .intermediate _ _ _ _ _ _ _ _ _ _ _ => true

private theorem ReversedLevel.intermediate_producer
    {N sigma terminalLoss}
    (level : ReversedLevel N sigma terminalLoss)
    (hlevel : level.isIntermediate = true) :
    PureWZ2IntermediateProducerFn sigma level.outputLoss
      level.sourceCeiling level.deltaThreshold := by
  cases level with
  | terminal => simp [ReversedLevel.isIntermediate] at hlevel
  | intermediate _ _ _ produce =>
      simpa [ReversedLevel.outputLoss, ReversedLevel.sourceCeiling,
        ReversedLevel.deltaThreshold] using produce

private theorem ReversedLevel.terminal_producer
    {N sigma terminalLoss}
    (level : ReversedLevel N sigma terminalLoss)
    (hlevel : level.isIntermediate = false) :
    PureWZ2TerminalProducerFn sigma terminalLoss
      level.sourceCeiling level.deltaThreshold := by
  cases level with
  | terminal _ _ produce =>
      simpa [ReversedLevel.sourceCeiling, ReversedLevel.deltaThreshold] using
        produce
  | intermediate => simp [ReversedLevel.isIntermediate] at hlevel

private theorem ReversedLevel.outputLoss_of_terminal
    {N sigma terminalLoss}
    (level : ReversedLevel N sigma terminalLoss)
    (hlevel : level.isIntermediate = false) :
    level.outputLoss = terminalLoss := by
  cases level with
  | terminal => rfl
  | intermediate => simp [ReversedLevel.isIntermediate] at hlevel

private def ReversedLevel.valid
    {N sigma terminalLoss}
    (level : ReversedLevel N sigma terminalLoss) : Prop :=
  0 < level.sourceCeiling ∧
    0 < level.deltaThreshold ∧
    level.deltaThreshold ≤ 1 ∧
    level.sourceCeiling ≤ level.outputLoss / 100 ∧
    0 < level.outputLoss ∧
    level.outputLoss ≤ terminalLoss

private noncomputable def buildAllLevels
    {N : ℕ} {sigma terminalLoss : ℝ}
    (intermediate : PureWZ2LocallyLinearOneScaleAtStatement sigma)
    (terminal : PureWZ2LocallyLinearTerminalScaleAtStatement sigma)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hterminalLoss : 0 < terminalLoss) (hN : 2 ≤ N) :
    ℕ → {level : ReversedLevel N sigma terminalLoss // level.valid}
  | 0 => by
      let existsData := terminal terminalLoss hsigma hsigmaOne hterminalLoss
      let sourceCeiling := Classical.choose existsData
      let thresholdData := Classical.choose_spec existsData
      let deltaThreshold := Classical.choose thresholdData
      let data := Classical.choose_spec thresholdData
      let level : ReversedLevel N sigma terminalLoss :=
        .terminal sourceCeiling deltaThreshold data.2.2.2.2
          data.1 data.2.2.1 data.2.2.2.1 data.2.1
      exact ⟨level, by
        simp [ReversedLevel.valid, ReversedLevel.sourceCeiling,
          ReversedLevel.deltaThreshold, ReversedLevel.outputLoss]
        exact ⟨data.1, data.2.2.1, data.2.2.2.1, data.2.1,
          hterminalLoss, le_rfl⟩⟩
  | index + 1 => by
      let previousData := buildAllLevels intermediate terminal
        hsigma hsigmaOne hterminalLoss hN index
      let previous := previousData.1
      have hprevious := previousData.2
      let outputLoss := min previous.sourceCeiling
        (min terminalLoss (1 / (2 * (N : ℝ))))
      have houtputLoss : 0 < outputLoss := by
        exact lt_min hprevious.1
          (lt_min hterminalLoss (by positivity))
      let existsData := intermediate outputLoss
        hsigma hsigmaOne houtputLoss
      let sourceCeiling := Classical.choose existsData
      let thresholdData := Classical.choose_spec existsData
      let deltaThreshold := Classical.choose thresholdData
      let data := Classical.choose_spec thresholdData
      have houtputTerminal : outputLoss ≤ terminalLoss :=
        (min_le_right _ _).trans (min_le_left _ _)
      have houtputHalf : outputLoss ≤ 1 / (2 * (N : ℝ)) :=
        (min_le_right _ _).trans (min_le_right _ _)
      let level : ReversedLevel N sigma terminalLoss :=
        .intermediate outputLoss sourceCeiling deltaThreshold
          data.2.2.2.2 houtputLoss data.1 data.2.2.1
          data.2.2.2.1 data.2.1 houtputTerminal houtputHalf
      exact ⟨level, by
        simp [ReversedLevel.valid, ReversedLevel.sourceCeiling,
          ReversedLevel.deltaThreshold, ReversedLevel.outputLoss]
        exact ⟨data.1, data.2.2.1, data.2.2.2.1, data.2.1,
          houtputLoss, houtputTerminal⟩⟩

private theorem buildAllLevels_succ_output_le_previous_ceiling
    {N : ℕ} {sigma terminalLoss : ℝ}
    (intermediate : PureWZ2LocallyLinearOneScaleAtStatement sigma)
    (terminal : PureWZ2LocallyLinearTerminalScaleAtStatement sigma)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hterminalLoss : 0 < terminalLoss) (hN : 2 ≤ N) (index : ℕ) :
    (buildAllLevels intermediate terminal hsigma hsigmaOne hterminalLoss hN
      (index + 1)).1.outputLoss ≤
    (buildAllLevels intermediate terminal hsigma hsigmaOne hterminalLoss hN
      index).1.sourceCeiling := by
  simp [buildAllLevels, ReversedLevel.outputLoss, ReversedLevel.sourceCeiling]

private theorem buildAllLevels_succ_output_le_half
    {N : ℕ} {sigma terminalLoss : ℝ}
    (intermediate : PureWZ2LocallyLinearOneScaleAtStatement sigma)
    (terminal : PureWZ2LocallyLinearTerminalScaleAtStatement sigma)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hterminalLoss : 0 < terminalLoss) (hN : 2 ≤ N) (index : ℕ) :
    (buildAllLevels intermediate terminal hsigma hsigmaOne hterminalLoss hN
      (index + 1)).1.outputLoss ≤ 1 / (2 * (N : ℝ)) := by
  simp [buildAllLevels, ReversedLevel.outputLoss]

private theorem buildAllLevels_succ_isIntermediate
    {N : ℕ} {sigma terminalLoss : ℝ}
    (intermediate : PureWZ2LocallyLinearOneScaleAtStatement sigma)
    (terminal : PureWZ2LocallyLinearTerminalScaleAtStatement sigma)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hterminalLoss : 0 < terminalLoss) (hN : 2 ≤ N) (index : ℕ) :
    (buildAllLevels intermediate terminal hsigma hsigmaOne hterminalLoss hN
      (index + 1)).1.isIntermediate = true := by
  simp [buildAllLevels, ReversedLevel.isIntermediate]

private theorem buildAllLevels_zero_isTerminal
    {N : ℕ} {sigma terminalLoss : ℝ}
    (intermediate : PureWZ2LocallyLinearOneScaleAtStatement sigma)
    (terminal : PureWZ2LocallyLinearTerminalScaleAtStatement sigma)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hterminalLoss : 0 < terminalLoss) (hN : 2 ≤ N) :
    (buildAllLevels intermediate terminal hsigma hsigmaOne hterminalLoss hN
      0).1.isIntermediate = false := by
  simp [buildAllLevels, ReversedLevel.isIntermediate]

/-- Construct the Pure loss schedule in the same backwards order as the
paper proof of Lemma 25. -/
noncomputable def construct
    {sigma hierarchyLoss terminalLoss : ℝ}
    (intermediate : PureWZ2LocallyLinearOneScaleAtStatement sigma)
    (terminal : PureWZ2LocallyLinearTerminalScaleAtStatement sigma)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hterminalLoss : 0 < terminalLoss)
    (hterminalHierarchy : terminalLoss ≤ hierarchyLoss)
    {N : ℕ} (hN : 2 ≤ N) :
    PureWZ2BackwardScheduleData N sigma hierarchyLoss := by
  let reversed := buildAllLevels intermediate terminal
    hsigma hsigmaOne hterminalLoss hN
  let outputLoss : Fin N → ℝ := fun level =>
    (reversed (N - 1 - (level : ℕ))).1.outputLoss
  let sourceCeiling : Fin N → ℝ := fun level =>
    (reversed (N - 1 - (level : ℕ))).1.sourceCeiling
  let deltaThreshold : Fin N → ℝ := fun level =>
    (reversed (N - 1 - (level : ℕ))).1.deltaThreshold
  have hvalid : ∀ index, (reversed index).1.valid :=
    fun index => (reversed index).2
  have hlastIndex :
      N - 1 - (pureWZ2FinLast N hN : ℕ) = 0 := by
    simp [pureWZ2FinLast]
  refine {
    levelCount_two := hN
    outputLoss := outputLoss
    sourceCeiling := sourceCeiling
    deltaThreshold := deltaThreshold
    produce_intermediate := ?_
    terminalLoss := terminalLoss
    terminalLoss_pos := hterminalLoss
    terminalLoss_le_hierarchyLoss := hterminalHierarchy
    produce_terminal := ?_
    outputLoss_pos := ?_
    sourceCeiling_pos := ?_
    deltaThreshold_pos := ?_
    deltaThreshold_le_one := ?_
    sourceCeiling_le := ?_
    outputLoss_last := ?_
    outputLoss_le_next_ceiling := ?_
    outputLoss_le_terminal := ?_
    outputLoss_le_half_levelCount := ?_ }
  · intro level hnext
    have hindex : ∃ index, N - 1 - (level : ℕ) = index + 1 := by
      exact ⟨N - 2 - (level : ℕ), by omega⟩
    rcases hindex with ⟨index, hindex⟩
    have hisIntermediate :
        (reversed (N - 1 - (level : ℕ))).1.isIntermediate = true := by
      rw [hindex]
      exact buildAllLevels_succ_isIntermediate intermediate terminal
        hsigma hsigmaOne hterminalLoss hN index
    exact (reversed (N - 1 - (level : ℕ))).1.intermediate_producer
      hisIntermediate
  · have hisTerminal : (reversed 0).1.isIntermediate = false :=
      buildAllLevels_zero_isTerminal intermediate terminal
        hsigma hsigmaOne hterminalLoss hN
    have hsource : sourceCeiling (pureWZ2FinLast N hN) =
        (reversed 0).1.sourceCeiling := by
      dsimp only [sourceCeiling]
      rw [hlastIndex]
    have hdelta : deltaThreshold (pureWZ2FinLast N hN) =
        (reversed 0).1.deltaThreshold := by
      dsimp only [deltaThreshold]
      rw [hlastIndex]
    rw [hsource, hdelta]
    exact (reversed 0).1.terminal_producer hisTerminal
  · intro level
    exact (hvalid _).2.2.2.2.1
  · intro level
    exact (hvalid _).1
  · intro level
    exact (hvalid _).2.1
  · intro level
    exact (hvalid _).2.2.1
  · intro level
    exact (hvalid _).2.2.2.1
  · dsimp only [outputLoss]
    rw [hlastIndex]
    exact (reversed 0).1.outputLoss_of_terminal
      (buildAllLevels_zero_isTerminal intermediate terminal
        hsigma hsigmaOne hterminalLoss hN)
  · intro level hnext
    have hindex : ∃ index, N - 1 - (level : ℕ) = index + 1 := by
      exact ⟨N - 2 - (level : ℕ), by omega⟩
    rcases hindex with ⟨index, hindex⟩
    have hnextIndex :
        N - 1 - ((level : ℕ) + 1) = index := by omega
    dsimp only [outputLoss, sourceCeiling]
    rw [hindex, hnextIndex]
    exact buildAllLevels_succ_output_le_previous_ceiling
      intermediate terminal hsigma hsigmaOne hterminalLoss hN index
  · intro level
    exact (hvalid _).2.2.2.2.2
  · intro level hnext
    have hindex : ∃ index, N - 1 - (level : ℕ) = index + 1 := by
      exact ⟨N - 2 - (level : ℕ), by omega⟩
    rcases hindex with ⟨index, hindex⟩
    dsimp only [outputLoss]
    rw [hindex]
    exact buildAllLevels_succ_output_le_half
      intermediate terminal hsigma hsigmaOne hterminalLoss hN index

end PureWZ2BackwardSchedule

end Kakeya.Assouad
