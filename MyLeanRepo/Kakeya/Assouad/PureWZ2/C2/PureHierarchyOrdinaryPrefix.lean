import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyExactTerminalAssembly

/-!
# The ordinary prefix of the exact-terminal Corollary-5.6 hierarchy

This is the first `N - 1` stages of the paper iteration.  The scale at prefix
index `j` is still `delta^((j+1)/N)`; the denominator is never changed to
`N - 1`.  The final ordinary output remains a full grain configuration and is
therefore a valid input to multiplicity refinement and same-extremizer Node 4.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Backward-chosen parameters for the `N - 1` ordinary levels. -/
structure PureWZ2OrdinaryPrefixScheduleData
    (N : ℕ) (sigma hierarchyLoss : ℝ) where
  levelCount_two : 2 ≤ N
  exactSourceCeiling : ℝ
  exactSourceCeiling_pos : 0 < exactSourceCeiling
  outputLoss : Fin (N - 1) → ℝ
  sourceCeiling : Fin (N - 1) → ℝ
  deltaThreshold : Fin (N - 1) → ℝ
  produce : ∀ level : Fin (N - 1),
    ∀ inputLoss : ℝ, 0 < inputLoss → inputLoss ≤ sourceCeiling level →
      ∀ delta : ℝ, 0 < delta → delta ≤ deltaThreshold level →
        ∀ source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta,
          ∀ rho : ℝ, delta ≤ rho → rho ≤ 1 →
            Real.rpow delta (1 - outputLoss level) ≤ rho →
            rho ≤ Real.rpow delta (outputLoss level) →
              Nonempty (PureWZ2LocallyLinearOneScaleData
                source (outputLoss level) rho)
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

namespace PureWZ2OrdinaryPrefixScheduleData

variable {N : ℕ} {sigma hierarchyLoss : ℝ}
    (schedule : PureWZ2OrdinaryPrefixScheduleData N sigma hierarchyLoss)

private def finZero
    (schedule : PureWZ2OrdinaryPrefixScheduleData N sigma hierarchyLoss) :
    Fin (N - 1) :=
  ⟨0, by have hN := schedule.levelCount_two; omega⟩

/-- The source loss requested from the initial critical configuration. -/
def initialSourceCeiling : ℝ := schedule.sourceCeiling schedule.finZero

theorem initialSourceCeiling_pos : 0 < schedule.initialSourceCeiling :=
  schedule.sourceCeiling_pos _

/-- One threshold valid at every ordinary prefix level. -/
noncomputable def commonDeltaThreshold : ℝ :=
  let image : Finset ℝ := Finset.image schedule.deltaThreshold Finset.univ
  have hnonempty : image.Nonempty := by
    exact ⟨schedule.deltaThreshold schedule.finZero,
      Finset.mem_image.mpr ⟨schedule.finZero, Finset.mem_univ _, rfl⟩⟩
  Finset.min' image hnonempty

theorem commonDeltaThreshold_pos : 0 < schedule.commonDeltaThreshold := by
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

/-- The paper scale for an ordinary prefix level lies in the one-scale
producer's accepted power window. -/
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
    have hlevelUpper : (((levelN : ℕ) + 1 : ℝ) / (N : ℝ)) ≤
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
    have hlowerExponent : (((levelN : ℕ) + 1 : ℝ) / (N : ℝ)) ≤
        1 - schedule.outputLoss level := by linarith
    have hlevelLower : 1 / (N : ℝ) ≤
        (((levelN : ℕ) + 1 : ℝ) / (N : ℝ)) := by
      apply div_le_div_of_nonneg_right
      · norm_num
      · positivity
    have hupperExponent : schedule.outputLoss level ≤
        (((levelN : ℕ) + 1 : ℝ) / (N : ℝ)) :=
      hlossN.trans hlevelLower
    exact ⟨
      Real.rpow_le_rpow_of_exponent_ge hdelta hstrict.le hlowerExponent,
      Real.rpow_le_rpow_of_exponent_ge hdelta hstrict.le hupperExponent⟩
  · have hdeltaEq : delta = 1 := by linarith
    simp [hdeltaEq, wz1Corollary26Scale]

end PureWZ2OrdinaryPrefixScheduleData

namespace PureWZ2OrdinaryPrefixSchedule

private abbrev ProducerFn
    (sigma outputLoss sourceCeiling deltaThreshold : ℝ) : Prop :=
  ∀ inputLoss : ℝ, 0 < inputLoss → inputLoss ≤ sourceCeiling →
    ∀ delta : ℝ, 0 < delta → delta ≤ deltaThreshold →
      ∀ source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta,
        ∀ rho : ℝ, delta ≤ rho → rho ≤ 1 →
          Real.rpow delta (1 - outputLoss) ≤ rho →
          rho ≤ Real.rpow delta outputLoss →
            Nonempty (PureWZ2LocallyLinearOneScaleData source outputLoss rho)

private structure ReversedLevel
    (N : ℕ) (sigma hierarchyLoss exactSourceCeiling : ℝ) where
  outputLoss : ℝ
  sourceCeiling : ℝ
  deltaThreshold : ℝ
  produce : ProducerFn sigma outputLoss sourceCeiling deltaThreshold
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
    (intermediate : PureWZ2LocallyLinearOneScaleAtStatement sigma)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hexactSourceCeiling : 0 < exactSourceCeiling)
    (hN : 2 ≤ N) :
    ℕ → ReversedLevel N sigma hierarchyLoss exactSourceCeiling
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
    (intermediate : PureWZ2LocallyLinearOneScaleAtStatement sigma)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hexactSourceCeiling : 0 < exactSourceCeiling)
    (hN : 2 ≤ N) (index : ℕ) :
    (buildReversed intermediate hsigma hsigmaOne hhierarchyLoss
      hexactSourceCeiling hN (index + 1)).outputLoss ≤
    (buildReversed intermediate hsigma hsigmaOne hhierarchyLoss
      hexactSourceCeiling hN index).sourceCeiling := by
  simp [buildReversed]

/-- Construct the ordinary-prefix loss schedule backwards from the source-loss
ceiling accepted by the exact terminal producer. -/
noncomputable def construct
    {sigma hierarchyLoss exactSourceCeiling : ℝ}
    (intermediate : PureWZ2LocallyLinearOneScaleAtStatement sigma)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hexactSourceCeiling : 0 < exactSourceCeiling)
    {N : ℕ} (hN : 2 ≤ N) :
    PureWZ2OrdinaryPrefixScheduleData N sigma hierarchyLoss := by
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

end PureWZ2OrdinaryPrefixSchedule

/-- Input loss at prefix level zero, and the preceding output loss thereafter. -/
def pureWZ2OrdinaryPrefixInputLoss
    {N : ℕ} {sigma hierarchyLoss : ℝ}
    (schedule : PureWZ2OrdinaryPrefixScheduleData N sigma hierarchyLoss)
    (level : ℕ) (hlevel : level < N - 1) : ℝ :=
  match level with
  | 0 => schedule.initialSourceCeiling
  | previous + 1 => schedule.outputLoss ⟨previous, by omega⟩

theorem pureWZ2OrdinaryPrefixInputLoss_pos
    {N : ℕ} {sigma hierarchyLoss : ℝ}
    (schedule : PureWZ2OrdinaryPrefixScheduleData N sigma hierarchyLoss)
    (level : ℕ) (hlevel : level < N - 1) :
    0 < pureWZ2OrdinaryPrefixInputLoss schedule level hlevel := by
  cases level with
  | zero => exact schedule.initialSourceCeiling_pos
  | succ previous => exact schedule.outputLoss_pos _

theorem pureWZ2OrdinaryPrefixInputLoss_le_ceiling
    {N : ℕ} {sigma hierarchyLoss : ℝ}
    (schedule : PureWZ2OrdinaryPrefixScheduleData N sigma hierarchyLoss)
    (level : ℕ) (hlevel : level < N - 1) :
    pureWZ2OrdinaryPrefixInputLoss schedule level hlevel ≤
      schedule.sourceCeiling ⟨level, hlevel⟩ := by
  cases level with
  | zero =>
      change schedule.sourceCeiling schedule.finZero ≤
        schedule.sourceCeiling ⟨0, hlevel⟩
      rw [show schedule.finZero = ⟨0, hlevel⟩ from Fin.ext rfl]
  | succ previous =>
      simpa [pureWZ2OrdinaryPrefixInputLoss] using
        schedule.outputLoss_le_next_ceiling ⟨previous, by omega⟩ (by omega)

theorem pureWZ2OrdinaryPrefixInputLoss_le_outputLoss
    {N : ℕ} {sigma hierarchyLoss : ℝ}
    (schedule : PureWZ2OrdinaryPrefixScheduleData N sigma hierarchyLoss)
    (level : ℕ) (hlevel : level < N - 1) :
    pureWZ2OrdinaryPrefixInputLoss schedule level hlevel ≤
      schedule.outputLoss ⟨level, hlevel⟩ := by
  exact (pureWZ2OrdinaryPrefixInputLoss_le_ceiling schedule level hlevel).trans
    ((schedule.sourceCeiling_le _).trans (by
      have hpos := schedule.outputLoss_pos ⟨level, hlevel⟩
      linarith))

/-- Forward dependent construction of one ordinary prefix level. -/
noncomputable def pureWZ2BuildOrdinaryPrefixLevel
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (schedule : PureWZ2OrdinaryPrefixScheduleData N sigma hierarchyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (source0 : PureWZ2QuantitativeGrainConfiguration sigma
      schedule.initialSourceCeiling delta)
    (level : ℕ) (hlevel : level < N - 1) :
    let levelPrefix : Fin (N - 1) := ⟨level, hlevel⟩
    let levelN : Fin N := ⟨level, by omega⟩
    Σ source : PureWZ2QuantitativeGrainConfiguration sigma
        (pureWZ2OrdinaryPrefixInputLoss schedule level hlevel) delta,
      PureWZ2LocallyLinearOneScaleData source
        (schedule.outputLoss levelPrefix)
        (wz1Corollary26Scale delta N levelN) :=
  match level with
  | 0 =>
      let levelPrefix : Fin (N - 1) := ⟨0, by omega⟩
      let levelN : Fin N := ⟨0, by omega⟩
      have hdeltaLevel : delta ≤ schedule.deltaThreshold levelPrefix :=
        hdeltaThreshold.trans (schedule.commonDeltaThreshold_le levelPrefix)
      have hwindow := schedule.scale_window levelPrefix hdelta hdeltaOne
      have hzero : schedule.finZero = levelPrefix := Fin.ext rfl
      have hinputCeiling : schedule.initialSourceCeiling ≤
          schedule.sourceCeiling levelPrefix := by
        simp only [PureWZ2OrdinaryPrefixScheduleData.initialSourceCeiling]
        rw [hzero]
      let produced := schedule.produce levelPrefix
        schedule.initialSourceCeiling schedule.initialSourceCeiling_pos hinputCeiling
        delta hdelta hdeltaLevel source0
        (wz1Corollary26Scale delta N levelN)
        (pureWZ2Hierarchy_delta_le_scale schedule.levelCount_two
          hdelta hdeltaOne levelN)
        (pureWZ2HierarchyScale_le_one hdelta hdeltaOne levelN)
        hwindow.1 hwindow.2
      ⟨source0, produced.some⟩
  | previous + 1 =>
      let previousData := pureWZ2BuildOrdinaryPrefixLevel schedule hdelta
        hdeltaOne hdeltaThreshold source0 previous (by omega)
      have hadvance : pureWZ2OrdinaryPrefixInputLoss schedule previous
          (by omega) ≤ schedule.outputLoss ⟨previous, by omega⟩ :=
        pureWZ2OrdinaryPrefixInputLoss_le_outputLoss schedule previous (by omega)
      let nextSource : PureWZ2QuantitativeGrainConfiguration sigma
          (schedule.outputLoss ⟨previous, by omega⟩) delta :=
        previousData.2.toGrainConfiguration hadvance
      have hinputEq : schedule.outputLoss ⟨previous, by omega⟩ =
          pureWZ2OrdinaryPrefixInputLoss schedule (previous + 1) hlevel := by
        simp [pureWZ2OrdinaryPrefixInputLoss]
      let source : PureWZ2QuantitativeGrainConfiguration sigma
          (pureWZ2OrdinaryPrefixInputLoss schedule (previous + 1) hlevel)
          delta := hinputEq ▸ nextSource
      let levelPrefix : Fin (N - 1) := ⟨previous + 1, hlevel⟩
      let levelN : Fin N := ⟨previous + 1, by omega⟩
      have hdeltaLevel : delta ≤ schedule.deltaThreshold levelPrefix :=
        hdeltaThreshold.trans (schedule.commonDeltaThreshold_le levelPrefix)
      have hwindow := schedule.scale_window levelPrefix hdelta hdeltaOne
      let produced := schedule.produce levelPrefix
        (pureWZ2OrdinaryPrefixInputLoss schedule (previous + 1) hlevel)
        (pureWZ2OrdinaryPrefixInputLoss_pos schedule _ hlevel)
        (pureWZ2OrdinaryPrefixInputLoss_le_ceiling schedule _ hlevel)
        delta hdelta hdeltaLevel source
        (wz1Corollary26Scale delta N levelN)
        (pureWZ2Hierarchy_delta_le_scale schedule.levelCount_two
          hdelta hdeltaOne levelN)
        (pureWZ2HierarchyScale_le_one hdelta hdeltaOne levelN)
        hwindow.1 hwindow.2
      ⟨source, produced.some⟩

/-- The source of prefix level `k+1` is the retained output at level `k`. -/
theorem pureWZ2BuildOrdinaryPrefixLevel_source_shading
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (schedule : PureWZ2OrdinaryPrefixScheduleData N sigma hierarchyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (source0 : PureWZ2QuantitativeGrainConfiguration sigma
      schedule.initialSourceCeiling delta)
    {level : ℕ} (hlevel : level + 1 < N - 1) :
    HEq
      (pureWZ2BuildOrdinaryPrefixLevel schedule hdelta hdeltaOne
        hdeltaThreshold source0 (level + 1) hlevel).1.shading
      (pureWZ2BuildOrdinaryPrefixLevel schedule hdelta hdeltaOne
        hdeltaThreshold source0 level (by omega)).2.shading := by
  rw [pureWZ2BuildOrdinaryPrefixLevel]
  rfl

/-- Every recursively produced prefix source retains the initial slope. -/
theorem pureWZ2BuildOrdinaryPrefixLevel_slope
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (schedule : PureWZ2OrdinaryPrefixScheduleData N sigma hierarchyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (source0 : PureWZ2QuantitativeGrainConfiguration sigma
      schedule.initialSourceCeiling delta)
    (level : ℕ) (hlevel : level < N - 1) :
    (pureWZ2BuildOrdinaryPrefixLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 level hlevel).1.globalGrains.slope =
        source0.globalGrains.slope := by
  induction level with
  | zero => rfl
  | succ previous ih =>
      have hadvance : pureWZ2OrdinaryPrefixInputLoss schedule previous
          (by omega) ≤ schedule.outputLoss ⟨previous, by omega⟩ :=
        pureWZ2OrdinaryPrefixInputLoss_le_outputLoss schedule previous (by omega)
      have hstep :=
        PureWZ2LocallyLinearOneScaleData.toGrainConfiguration_slope
          (pureWZ2BuildOrdinaryPrefixLevel schedule hdelta hdeltaOne
            hdeltaThreshold source0 previous (by omega)).2 hadvance
      rw [pureWZ2BuildOrdinaryPrefixLevel]
      exact hstep.trans (ih (by omega))

/-- Later prefix outputs are subshadings of every earlier prefix output. -/
theorem pureWZ2BuildOrdinaryPrefixLevel_union_chain
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (schedule : PureWZ2OrdinaryPrefixScheduleData N sigma hierarchyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (source0 : PureWZ2QuantitativeGrainConfiguration sigma
      schedule.initialSourceCeiling delta)
    {first last : ℕ} (hfirst : first < N - 1) (hlast : last < N - 1)
    (horder : first ≤ last) :
    (pureWZ2BuildOrdinaryPrefixLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 last hlast).2.shading.union ⊆
    (pureWZ2BuildOrdinaryPrefixLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 first hfirst).2.shading.union := by
  induction last with
  | zero =>
      have hfirstZero : first = 0 := by omega
      subst first
      exact Set.Subset.rfl
  | succ previous ih =>
      by_cases heq : first = previous + 1
      · subst first
        exact Set.Subset.rfl
      · have hfirstPrevious : first ≤ previous := by omega
        let current := pureWZ2BuildOrdinaryPrefixLevel schedule hdelta
          hdeltaOne hdeltaThreshold source0 (previous + 1) hlast
        let prior := pureWZ2BuildOrdinaryPrefixLevel schedule hdelta
          hdeltaOne hdeltaThreshold source0 previous (by omega)
        have hstep : current.2.shading.union ⊆ current.1.shading.union :=
          current.2.subshading.union_subset
        have hsource := pureWZ2BuildOrdinaryPrefixLevel_source_shading
          schedule hdelta hdeltaOne hdeltaThreshold source0 hlast
        have hsourceUnion : current.1.shading.union = prior.2.shading.union := by
          cases hsource
          rfl
        rw [hsourceUnion] at hstep
        exact hstep.trans (ih (by omega) hfirstPrevious)

/-- Package the final ordinary source together with all `N - 1` prefix
trapezoid families, still indexed by the eventual total depth `N`. -/
theorem pureWZ2_construct_ordinary_hierarchy_prefix_with_terminal_bound
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (schedule : PureWZ2OrdinaryPrefixScheduleData N sigma hierarchyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (source0 : PureWZ2QuantitativeGrainConfiguration sigma
      schedule.initialSourceCeiling delta) :
    ∃ terminalInputLoss : ℝ,
      0 < terminalInputLoss ∧
      terminalInputLoss ≤ schedule.exactSourceCeiling ∧
      ∃ terminalSource : PureWZ2QuantitativeGrainConfiguration
          sigma terminalInputLoss delta,
        Nonempty (PureWZ2OrdinaryHierarchyPrefixData
          terminalSource hierarchyLoss N) := by
  let last : ℕ := N - 2
  have hlast : last < N - 1 := by
    have hN := schedule.levelCount_two
    omega
  let finalData := pureWZ2BuildOrdinaryPrefixLevel schedule hdelta hdeltaOne
    hdeltaThreshold source0 last hlast
  let lastFin : Fin (N - 1) := ⟨last, hlast⟩
  have hadvance : pureWZ2OrdinaryPrefixInputLoss schedule last hlast ≤
      schedule.outputLoss lastFin :=
    pureWZ2OrdinaryPrefixInputLoss_le_outputLoss schedule last hlast
  let terminalInputLoss := schedule.outputLoss lastFin
  let terminalSource : PureWZ2QuantitativeGrainConfiguration
      sigma terminalInputLoss delta :=
    finalData.2.toGrainConfiguration hadvance
  let trapezoids : ∀ level : Fin N, (level : ℕ) + 1 < N →
      Finset WZ1VerticalTrapezoid := fun level hlevel =>
    (pureWZ2BuildOrdinaryPrefixLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 (level : ℕ) (by omega)).2.trapezoids
  have hterminalUnion : terminalSource.shading.union = finalData.2.shading.union := rfl
  have hterminalSlope : terminalSource.globalGrains.slope =
      source0.globalGrains.slope := by
    exact finalData.2.slope_eq.trans
      (pureWZ2BuildOrdinaryPrefixLevel_slope schedule hdelta hdeltaOne
        hdeltaThreshold source0 last hlast)
  refine ⟨terminalInputLoss, schedule.outputLoss_pos lastFin,
    schedule.outputLoss_last_le_exactSourceCeiling, terminalSource, ⟨{
    levelCount_two := schedule.levelCount_two
    trapezoids := trapezoids
    level_nonempty := ?_
    height_eq := ?_
    slope_bound := ?_
    length_bounds := ?_
    separated_cores := ?_
    slope_approximation := ?_
    active_height_coverage := ?_ }⟩⟩
  · intro level hlevel
    exact (pureWZ2BuildOrdinaryPrefixLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 (level : ℕ) (by omega)).2.trapezoids_nonempty
  · intro level hlevel trapezoid htrapezoid
    exact (pureWZ2BuildOrdinaryPrefixLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 (level : ℕ) (by omega)).2.height_eq
        trapezoid htrapezoid
  · intro level hlevel trapezoid htrapezoid
    exact (pureWZ2BuildOrdinaryPrefixLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 (level : ℕ) (by omega)).2.slope_bound
        trapezoid htrapezoid
  · intro level hlevel trapezoid htrapezoid
    have hraw := (pureWZ2BuildOrdinaryPrefixLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 (level : ℕ) (by omega)).2.length_bounds
        trapezoid htrapezoid
    have hloss : schedule.outputLoss ⟨level, by omega⟩ ≤ hierarchyLoss :=
      schedule.outputLoss_le_hierarchy _
    have hscalePos := pureWZ2HierarchyScale_pos hdelta
      (⟨level, by omega⟩ : Fin N)
    have hscaleOne := pureWZ2HierarchyScale_le_one hdelta hdeltaOne
      (⟨level, by omega⟩ : Fin N)
    exact ⟨(Real.rpow_le_rpow_of_exponent_ge hscalePos hscaleOne
      (by linarith)).trans hraw.1, hraw.2⟩
  · intro level hlevel first hfirst second hsecond hne z hz w hw
    exact (pureWZ2BuildOrdinaryPrefixLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 (level : ℕ) (by omega)).2.separated_cores
        first hfirst second hsecond hne z hz w hw
  · intro level hlevel trapezoid htrapezoid z hz hslice
    have hlevelLast : (level : ℕ) ≤ last := by
      dsimp only [last]
      omega
    have hfinalSub := pureWZ2BuildOrdinaryPrefixLevel_union_chain schedule
      hdelta hdeltaOne hdeltaThreshold source0
      (first := (level : ℕ)) (last := last) (by omega) hlast hlevelLast
    have hlevelSlice : horizontalSlice
        (pureWZ2BuildOrdinaryPrefixLevel schedule hdelta hdeltaOne
          hdeltaThreshold source0 (level : ℕ) (by omega)).2.shading.union z ≠ ∅ := by
      apply Set.Nonempty.ne_empty
      apply Set.Nonempty.mono _ (Set.nonempty_iff_ne_empty.mpr hslice)
      intro point hpoint
      rw [hterminalUnion] at hpoint
      exact ⟨hfinalSub hpoint.1, hpoint.2⟩
    have hraw := (pureWZ2BuildOrdinaryPrefixLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 (level : ℕ) (by omega)).2.slope_approximation
        trapezoid htrapezoid z hz hlevelSlice
    have hlevelSlope :=
      (pureWZ2BuildOrdinaryPrefixLevel schedule hdelta hdeltaOne
        hdeltaThreshold source0 (level : ℕ) (by omega)).2.slope_eq.trans
      (pureWZ2BuildOrdinaryPrefixLevel_slope schedule hdelta hdeltaOne
        hdeltaThreshold source0 (level : ℕ) (by omega))
    rw [hlevelSlope] at hraw
    rw [hterminalSlope]
    simpa using hraw
  · intro level hlevel z hz hslice
    have hlevelLast : (level : ℕ) ≤ last := by
      dsimp only [last]
      omega
    have hfinalSub := pureWZ2BuildOrdinaryPrefixLevel_union_chain schedule
      hdelta hdeltaOne hdeltaThreshold source0
      (first := (level : ℕ)) (last := last) (by omega) hlast hlevelLast
    have hlevelSlice : horizontalSlice
        (pureWZ2BuildOrdinaryPrefixLevel schedule hdelta hdeltaOne
          hdeltaThreshold source0 (level : ℕ) (by omega)).2.shading.union z ≠ ∅ := by
      apply Set.Nonempty.ne_empty
      apply Set.Nonempty.mono _ (Set.nonempty_iff_ne_empty.mpr hslice)
      intro point hpoint
      rw [hterminalUnion] at hpoint
      exact ⟨hfinalSub hpoint.1, hpoint.2⟩
    exact (pureWZ2BuildOrdinaryPrefixLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 (level : ℕ) (by omega)).2.active_height_coverage
        z hz hlevelSlice

/-- Compatibility projection which forgets the terminal source-loss bound. -/
theorem pureWZ2_construct_ordinary_hierarchy_prefix
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (schedule : PureWZ2OrdinaryPrefixScheduleData N sigma hierarchyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (source0 : PureWZ2QuantitativeGrainConfiguration sigma
      schedule.initialSourceCeiling delta) :
    ∃ terminalInputLoss : ℝ,
      ∃ terminalSource : PureWZ2QuantitativeGrainConfiguration
          sigma terminalInputLoss delta,
        Nonempty (PureWZ2OrdinaryHierarchyPrefixData
          terminalSource hierarchyLoss N) := by
  rcases pureWZ2_construct_ordinary_hierarchy_prefix_with_terminal_bound
      schedule hdelta hdeltaOne hdeltaThreshold source0 with
    ⟨terminalInputLoss, _hterminalPos, _hterminalBound,
      terminalSource, ordinary⟩
  exact ⟨terminalInputLoss, terminalSource, ordinary⟩

/-- Full source and index provenance of the prefix/terminal join. -/
structure PureWZ2MixedHierarchyConstructionData
    (sigma finalLoss hierarchyLoss delta : ℝ) (N : ℕ) where
  terminalInputLoss : ℝ
  terminalInputLoss_pos : 0 < terminalInputLoss
  terminalInputLoss_le_hierarchy : terminalInputLoss ≤ hierarchyLoss
  terminalSource : PureWZ2QuantitativeGrainConfiguration
    sigma terminalInputLoss delta
  mixed : PureWZ2MixedRawHierarchyData
    terminalSource finalLoss hierarchyLoss
  levelCount_eq : mixed.levelCount = N

/-- Build the mixed hierarchy while applying the exact terminal schedule to
the precise source retained by the ordinary prefix. -/
theorem pureWZ2_construct_mixed_hierarchy_with_provenance
    {N : ℕ} {sigma hierarchyLoss finalLoss delta : ℝ}
    (ordinarySchedule : PureWZ2OrdinaryPrefixScheduleData
      N sigma hierarchyLoss)
    (terminalSchedule : PureWZ2ExactTerminalScaleSchedule sigma finalLoss)
    (hterminalCeiling : ordinarySchedule.exactSourceCeiling ≤
      terminalSchedule.sourceLossCeiling)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaOrdinary : delta ≤ ordinarySchedule.commonDeltaThreshold)
    (hdeltaTerminal : delta ≤ terminalSchedule.delta₀)
    (hfinalHierarchy : finalLoss ≤ hierarchyLoss)
    (source0 : PureWZ2QuantitativeGrainConfiguration sigma
      ordinarySchedule.initialSourceCeiling delta) :
    Nonempty (PureWZ2MixedHierarchyConstructionData
      sigma finalLoss hierarchyLoss delta N) := by
  rcases pureWZ2_construct_ordinary_hierarchy_prefix_with_terminal_bound
      ordinarySchedule hdelta hdeltaOne hdeltaOrdinary source0 with
    ⟨terminalInputLoss, hterminalInputPos, hterminalInput,
      terminalSource, ordinary⟩
  rcases ordinary with ⟨ordinary⟩
  rcases terminalSchedule.produce terminalInputLoss hterminalInputPos
      (hterminalInput.trans hterminalCeiling) delta hdelta hdeltaTerminal
      terminalSource with ⟨terminal⟩
  rcases ordinary.appendExactTerminalWithLevelCount terminal hfinalHierarchy with
    ⟨mixed⟩
  exact ⟨{
    terminalInputLoss := terminalInputLoss
    terminalInputLoss_pos := hterminalInputPos
    terminalInputLoss_le_hierarchy := by
      have hceilingHierarchy :
          terminalSchedule.sourceLossCeiling ≤ hierarchyLoss := by
        linarith [terminalSchedule.sourceLossCeiling_pos,
          terminalSchedule.sourceLossCeiling_le, hfinalHierarchy]
      exact (hterminalInput.trans hterminalCeiling).trans hceilingHierarchy
    terminalSource := terminalSource
    mixed := mixed.1
    levelCount_eq := mixed.2 }⟩

/-- Compatibility projection which forgets the terminal loss and depth
certificates. -/
theorem pureWZ2_construct_mixed_hierarchy
    {N : ℕ} {sigma hierarchyLoss finalLoss delta : ℝ}
    (ordinarySchedule : PureWZ2OrdinaryPrefixScheduleData
      N sigma hierarchyLoss)
    (terminalSchedule : PureWZ2ExactTerminalScaleSchedule sigma finalLoss)
    (hterminalCeiling : ordinarySchedule.exactSourceCeiling ≤
      terminalSchedule.sourceLossCeiling)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaOrdinary : delta ≤ ordinarySchedule.commonDeltaThreshold)
    (hdeltaTerminal : delta ≤ terminalSchedule.delta₀)
    (hfinalHierarchy : finalLoss ≤ hierarchyLoss)
    (source0 : PureWZ2QuantitativeGrainConfiguration sigma
      ordinarySchedule.initialSourceCeiling delta) :
    ∃ terminalInputLoss : ℝ,
      ∃ terminalSource : PureWZ2QuantitativeGrainConfiguration
          sigma terminalInputLoss delta,
        Nonempty (PureWZ2MixedRawHierarchyData
          terminalSource finalLoss hierarchyLoss) := by
  rcases pureWZ2_construct_mixed_hierarchy_with_provenance ordinarySchedule
      terminalSchedule hterminalCeiling hdelta hdeltaOne hdeltaOrdinary
      hdeltaTerminal hfinalHierarchy source0 with ⟨output⟩
  exact ⟨output.terminalInputLoss, output.terminalSource, ⟨output.mixed⟩⟩

end Kakeya.Assouad

end
