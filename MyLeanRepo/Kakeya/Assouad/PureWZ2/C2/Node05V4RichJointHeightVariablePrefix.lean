import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightActualOneScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantVariableSchedule

/-!
# Variable-depth production from the actual joint-height ordinary step

This driver runs the P0-scheduled P3 producer only at the paper scales
`delta^((j+1)/N)`.  Each recursive call consumes the literal `step.next`
source and refreshed re-entry returned by its predecessor.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2C2OrdinaryGlobalSchedule

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2OrdinaryGlobalSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal)

private noncomputable def runJointHeightPrefixLevel
    {sourceDelta inputLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (level : Fin (schedule.mild.levelCount - 1))
    (current : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinputCeiling : inputLoss ≤
      schedule.ordinaryPrefix.sourceLossCeiling level)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    PureWZ2ReentrantOneScaleOutput current
      (schedule.ordinaryPrefix.level level).level.transition.transitionLoss
      (wz1Corollary26Scale sourceDelta schedule.mild.levelCount
        ⟨level, by omega⟩) := by
  have hinputCeiling' : inputLoss ≤
      (schedule.ordinaryPrefix.level level).level.sourceLossCeiling := by
    rw [← schedule.ordinaryPrefix.sourceLossCeiling_eq_level level]
    exact hinputCeiling
  exact Classical.choice <| schedule.actualLevel_jointHeightOutput
    hsourceDelta hsourceSmall level current hinputNonneg hinputCeiling' hbridge

private noncomputable def buildJointHeightPrefixFrom
    {sourceDelta : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (level remaining : ℕ)
    (hlevels : level + remaining = schedule.mild.levelCount - 1)
    {inputLoss : ℝ}
    (current : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinputCeiling : ∀ hremaining : 0 < remaining,
      inputLoss ≤ schedule.ordinaryPrefix.sourceLossCeiling
        ⟨level, by omega⟩)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    PureWZ2ReentrantPrefixChain sigma sourceDelta
      capability.normalizationExponent current remaining :=
  match remaining with
  | 0 => .nil current
  | next + 1 => by
      let levelIndex : Fin (schedule.mild.levelCount - 1) :=
        ⟨level, by omega⟩
      let output := schedule.runJointHeightPrefixLevel hsourceDelta hsourceSmall
        levelIndex current hinputNonneg (hinputCeiling (by omega)) hbridge
      have hnextCeiling : ∀ hnext : 0 < next,
          (schedule.ordinaryPrefix.level levelIndex).level.transition.transitionLoss ≤
            schedule.ordinaryPrefix.sourceLossCeiling
              ⟨level + 1, by omega⟩ := by
        intro hnext
        have hlevelNext : level + 1 < schedule.mild.levelCount - 1 := by
          omega
        rw [← schedule.ordinaryPrefix.outputLoss_eq_level levelIndex]
        exact schedule.ordinaryPrefix.outputLoss_le_next_ceiling levelIndex
          hlevelNext
      exact .cons output.step <|
        buildJointHeightPrefixFrom hsourceDelta hsourceSmall
          (level + 1) next (by omega) output.step.next
          ((schedule.ordinaryPrefix.level levelIndex).level.transition
            |>.transitionLoss_pos.le)
          hnextCeiling hbridge
termination_by remaining

private theorem buildJointHeightPrefixFrom_outputAt
    {sourceDelta : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (level remaining : ℕ)
    (hlevels : level + remaining = schedule.mild.levelCount - 1)
    {inputLoss : ℝ}
    (current : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinputCeiling : ∀ hremaining : 0 < remaining,
      inputLoss ≤ schedule.ordinaryPrefix.sourceLossCeiling
        ⟨level, by omega⟩)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (index : Fin remaining) :
    let chain := schedule.buildJointHeightPrefixFrom hsourceDelta hsourceSmall
      level remaining hlevels current hinputNonneg hinputCeiling hbridge
    let scheduleLevel : Fin (schedule.mild.levelCount - 1) :=
      ⟨level + (index : ℕ), by omega⟩
    (chain.outputAt index).outputLoss =
        schedule.ordinaryPrefix.outputLoss scheduleLevel ∧
      (chain.outputAt index).rho =
        wz1Corollary26Scale sourceDelta schedule.mild.levelCount
          ⟨scheduleLevel, by omega⟩ := by
  induction remaining generalizing level inputLoss current with
  | zero => exact Fin.elim0 index
  | succ next ih =>
      refine Fin.cases ?_ (fun later => ?_) index
      · simp [buildJointHeightPrefixFrom, runJointHeightPrefixLevel,
          PureWZ2ReentrantPrefixChain.outputAt]
        exact (schedule.ordinaryPrefix.outputLoss_eq_level
          (⟨level, by omega⟩ : Fin (schedule.mild.levelCount - 1))).symm
      · let levelIndex : Fin (schedule.mild.levelCount - 1) :=
          ⟨level, by omega⟩
        let output := schedule.runJointHeightPrefixLevel hsourceDelta
          hsourceSmall levelIndex current hinputNonneg
          (hinputCeiling (by omega)) hbridge
        have hnextCeiling : ∀ hnext : 0 < next,
            (schedule.ordinaryPrefix.level levelIndex).level.transition.transitionLoss ≤
              schedule.ordinaryPrefix.sourceLossCeiling
                ⟨level + 1, by omega⟩ := by
          intro hnext
          have hlevelNext : level + 1 < schedule.mild.levelCount - 1 := by
            omega
          rw [← schedule.ordinaryPrefix.outputLoss_eq_level levelIndex]
          exact schedule.ordinaryPrefix.outputLoss_le_next_ceiling
            levelIndex hlevelNext
        have hrec := ih (level := level + 1) (by omega) output.step.next
          ((schedule.ordinaryPrefix.level levelIndex).level.transition
            |>.transitionLoss_pos.le)
          hnextCeiling later
        have houtputEq :
            runJointHeightPrefixLevel schedule hsourceDelta hsourceSmall
                (⟨level, by omega⟩ :
                  Fin (schedule.mild.levelCount - 1))
                current hinputNonneg (hinputCeiling (by omega)) hbridge =
              output := by
          dsimp only [output, levelIndex]
        rw [buildJointHeightPrefixFrom]
        dsimp only
        rw [houtputEq]
        rw [PureWZ2ReentrantPrefixChain.outputAt_cons_succ]
        rcases hrec with ⟨hloss, hrho⟩
        have hindex :
            (⟨level + (later.succ : ℕ), by omega⟩ :
              Fin (schedule.mild.levelCount - 1)) =
              ⟨level + 1 + (later : ℕ), by omega⟩ := by
          apply Fin.ext
          change level + ((later : ℕ) + 1) =
            level + 1 + (later : ℕ)
          omega
        constructor
        · rw [hindex]
          exact hloss
        · have htotal :
              (⟨level + (later.succ : ℕ), by omega⟩ :
                Fin schedule.mild.levelCount) =
                ⟨level + 1 + (later : ℕ), by omega⟩ := by
            apply Fin.ext
            omega
          rw [htotal]
          exact hrho

/-- The completed actual ordinary prefix, before the identity/nontrivial
endpoint scale is appended. -/
structure ActualJointHeightPrefixData
    {sourceDelta inputLoss : ℝ}
    (initial : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent) where
  chain : PureWZ2ReentrantPrefixChain sigma sourceDelta
    capability.normalizationExponent initial (schedule.mild.levelCount - 1)
  compatible : chain.IsHierarchyPrefix schedule.mild.epsilon₂
    schedule.mild.levelCount
  outputLoss_eq : ∀ level : Fin (schedule.mild.levelCount - 1),
    (chain.outputAt level).outputLoss =
      schedule.ordinaryPrefix.outputLoss level

/-- Run all actual ordinary scales on one literal dependent re-entry chain. -/
noncomputable def actualJointHeightPrefix
    {sourceDelta inputLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (initial : PureWZ2ReentrantGrainSource sigma inputLoss sourceDelta
      capability.normalizationExponent)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinitialCeiling : inputLoss ≤
      schedule.ordinaryPrefix.sourceLossCeiling
        ⟨0, by
          have hN := schedule.mild.levelCount_ge_two
          omega⟩)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    schedule.ActualJointHeightPrefixData initial := by
  let chain := schedule.buildJointHeightPrefixFrom hsourceDelta hsourceSmall
    0 (schedule.mild.levelCount - 1) (by simp) initial hinputNonneg
    (by intro _; exact hinitialCeiling) hbridge
  have hresult : ∀ level : Fin (schedule.mild.levelCount - 1),
      (chain.outputAt level).outputLoss =
          schedule.ordinaryPrefix.outputLoss level ∧
        (chain.outputAt level).rho =
          wz1Corollary26Scale sourceDelta schedule.mild.levelCount
            ⟨level, by omega⟩ := by
    intro level
    have hraw := schedule.buildJointHeightPrefixFrom_outputAt hsourceDelta
      hsourceSmall 0 (schedule.mild.levelCount - 1) (by simp) initial
      hinputNonneg (by intro _; exact hinitialCeiling) hbridge level
    have hindex :
        (⟨0 + (level : ℕ), by omega⟩ :
          Fin (schedule.mild.levelCount - 1)) = level := by
      apply Fin.ext
      simp
    rcases hraw with ⟨hloss, hrho⟩
    constructor
    · simpa only [chain, hindex] using hloss
    · change (chain.outputAt level).rho =
        wz1Corollary26Scale sourceDelta schedule.mild.levelCount
          (⟨level, by omega⟩ : Fin schedule.mild.levelCount)
      simpa only [chain, Nat.zero_add] using hrho
  have houtput : ∀ level : Fin (schedule.mild.levelCount - 1),
      (chain.outputAt level).outputLoss =
        schedule.ordinaryPrefix.outputLoss level :=
    fun level => (hresult level).1
  refine {
    chain := chain
    compatible := {
      levelCount_two := schedule.mild.levelCount_ge_two
      levelCount_succ := by
        have hN := schedule.mild.levelCount_ge_two
        omega
      outputLoss_le := ?_
      rho_eq := ?_ }
    outputLoss_eq := houtput }
  · intro level
    rw [houtput level]
    calc
      schedule.ordinaryPrefix.outputLoss level ≤
          (schedule.ordinaryPrefix.level level).nextSourceCeiling := by
        rw [schedule.ordinaryPrefix.outputLoss_eq_level level]
        exact (schedule.ordinaryPrefix.level level).level.transition
          |>.transitionLoss_le_next
      _ ≤ schedule.mild.epsilon₂ * sigma / 1024 :=
        (schedule.ordinaryPrefix.level level).nextSourceCeiling_le_graph
      _ ≤ schedule.mild.epsilon₂ := by
        have hepsilon := schedule.mild.epsilon₂_pos
        nlinarith [schedule.sigma_lt_one]
  · intro level
    exact (hresult level).2

end PureWZ2C2OrdinaryGlobalSchedule

end Kakeya.Assouad

end
