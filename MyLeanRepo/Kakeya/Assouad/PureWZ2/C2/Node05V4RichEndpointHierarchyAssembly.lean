import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichEndpointClosureSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantTerminalQuantitativeAdapter

/-!
# Production assembly of the direct-rich endpoint hierarchy

The sole rich endpoint witness is truncated, passed through the owner-free
paper-order terminal runtime, equipped with its same-residue quantitative
receipt, and appended to the literal ordinary prefix.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2C2RichEndpointClosureSchedule

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal)

/-- The complete same-witness endpoint package before Proposition 5.7
normalization.  Every field is indexed by the preceding concrete field, so
neither the endpoint call nor the terminal residue can be reselected. -/
structure ActualRichEndpointMixedHierarchyData
    {sourceDelta initialLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    (actual : schedule.ordinary.ActualJointHeightPrefixData initial) where
  endpoint :
    schedule.ordinary.ActualJointHeightEndpointInvocationData actual
  terminal : PureWZ2TerminalScaleStickyData
    actual.chain.finalSource.2.grain
      schedule.terminal.kernel.terminal.stickyLoss 72
  runtime : PureWZ2TerminalPaperOrderRuntimeData
    (schedule := schedule.terminal) terminal
  quantitative : PureWZ2TerminalQuantitativeRuntimeData
    (densityLoss := schedule.terminal.kernel.terminal.workingLoss) runtime
  mixed : { mixed : PureWZ2QuantitativeMixedRawHierarchyData
      actual.chain.finalSource.2.grain schedule.terminalFinalLoss
        schedule.ordinary.mild.epsilon₂
        schedule.terminal.kernel.terminal.workingLoss //
    mixed.mixed.levelCount = schedule.ordinary.mild.levelCount }

/-- The final ordinary loss is positive and lies below the terminal
paper-order source ceiling. -/
theorem finalSource_loss_bounds
    {sourceDelta initialLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    (actual : schedule.ordinary.ActualJointHeightPrefixData initial) :
    0 < actual.chain.finalSource.1 ∧
      actual.chain.finalSource.1 ≤ schedule.terminal.sourceLossCeiling := by
  have hcount : 0 < schedule.ordinary.mild.levelCount - 1 := by
    have hN := schedule.ordinary.mild.levelCount_ge_two
    omega
  have hlast :
      (⟨schedule.ordinary.mild.levelCount - 1 - 1, by omega⟩ :
          Fin (schedule.ordinary.mild.levelCount - 1)) =
        ⟨schedule.ordinary.mild.levelCount - 2, by omega⟩ := by
    apply Fin.ext
    simp only [Nat.sub_sub]
  have hfinalEq : actual.chain.finalSource.1 =
      schedule.ordinary.ordinaryPrefix.outputLoss
        ⟨schedule.ordinary.mild.levelCount - 2, by omega⟩ := by
    rw [actual.chain.finalSource_loss_eq_last_outputAt hcount,
      actual.outputLoss_eq, hlast]
  constructor
  · rw [hfinalEq]
    exact schedule.ordinary.ordinaryPrefix.outputLoss_pos _
  · rw [hfinalEq]
    calc
      schedule.ordinary.ordinaryPrefix.outputLoss _ ≤
          schedule.ordinary.endpointKernel.sourceLoss :=
        schedule.ordinary.ordinaryPrefix.outputLoss_last_le_terminal
      _ ≤ schedule.ordinary.endpointOutputLoss := by
        have hsourceHalf := schedule.ordinary.endpointKernel.sourceLoss_le_half
        have hnormalizationPos :=
          schedule.ordinary.endpointKernel.normalizationLoss_pos
        have hnormalizationOutput :=
          schedule.ordinary.endpointKernel.normalizationLoss_lt_output
        linarith
      _ ≤ schedule.terminal.sourceLossCeiling :=
        schedule.endpointLoss_le_terminalSource

/-- Assemble the exact endpoint and append it to the literal ordinary chain.
The endpoint contains the only nontrivial `sqrt sourceDelta` call. -/
theorem actualRichEndpointMixedHierarchy
    {sourceDelta initialLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    (actual : schedule.ordinary.ActualJointHeightPrefixData initial)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (schedule.ActualRichEndpointMixedHierarchyData actual) := by
  have hsourceOrdinary : sourceDelta ≤ schedule.ordinary.commonDelta₀ :=
    hsourceSmall.trans schedule.commonDelta₀_le_ordinary
  rcases schedule.ordinary.actualJointHeightEndpointInvocation
      hsourceDelta hsourceOrdinary actual with ⟨endpoint⟩
  have hsqrtSmall : endpoint.sqrtRequested.1 ≤ 1 / 12 := by
    rw [endpoint.sqrtRequested_eq]
    have hdeltaSquare : sourceDelta ≤ 1 / 144 :=
      hsourceSmall.trans schedule.commonDelta₀_le_endpointSquare
    have hsqrtSq := Real.sq_sqrt hsourceDelta.le
    have hsqrtNonneg := Real.sqrt_nonneg sourceDelta
    nlinarith
  have hrefinement :
      (endpoint.rich.terminal.regularity : ENNReal) *
          wz2PaperPureRefinementFraction sourceDelta 72 ≤
        wz2PaperPureRefinementFraction sourceDelta 61 :=
    schedule.exactCoreAbsorption.absorb hsourceDelta
      (hsourceSmall.trans schedule.commonDelta₀_le_exactCore)
      endpoint.rich.terminal_regularity_bound
  let terminal := endpoint.toTerminalScaleStickyData
    schedule.terminal.kernel.terminal.stickyLoss 72
      schedule.endpointLoss_le_terminalSticky
      (by
        exact add_le_of_le_sub_left <|
          endpoint.rich.terminalLoss_le_output.trans <| by
            linarith [schedule.endpointLoss_twice_le_terminalSticky])
      hsqrtSmall hrefinement
  have hfinal := schedule.finalSource_loss_bounds actual
  rcases pureWZ2_terminalScaleSticky_paperOrderRuntime terminal hfinal.1
      hfinal.2 hsourceDelta
      (hsourceSmall.trans schedule.commonDelta₀_le_terminal) hbridge with
    ⟨runtime⟩
  let quantitative := PureWZ2TerminalQuantitativeRuntimeData.ofAbsorption
    runtime schedule.quantitativeMassAbsorption hfinal.2 hsourceDelta
      (hsourceSmall.trans schedule.commonDelta₀_le_quantitativeMass)
  let ordinary := actual.chain.toOrdinaryPrefix actual.compatible
  have hterminalHierarchy : schedule.terminalFinalLoss ≤
      schedule.ordinary.mild.epsilon₂ := by
    rw [schedule.terminalFinalLoss_eq, ← schedule.mild_eq]
    have hNpos : (0 : ℝ) < schedule.ordinary.mild.levelCount := by
      exact_mod_cast (lt_of_lt_of_le (by omega)
        schedule.ordinary.mild.levelCount_ge_two)
    have hNtwo : (2 : ℝ) ≤ schedule.ordinary.mild.levelCount := by
      exact_mod_cast schedule.ordinary.mild.levelCount_ge_two
    have hdenom : (1 : ℝ) ≤ 8 * schedule.ordinary.mild.levelCount := by
      nlinarith
    exact div_le_self schedule.ordinary.mild.epsilon₂_pos.le hdenom
  rcases quantitative.appendToOrdinaryWithLevelCount ordinary
      hterminalHierarchy with ⟨mixed⟩
  exact ⟨{
    endpoint := endpoint
    terminal := terminal
    runtime := runtime
    quantitative := quantitative
    mixed := mixed }⟩

/-- Repackage the same quantitative mixed hierarchy for the numerical R3
schedule. -/
noncomputable def ActualRichEndpointMixedHierarchyData.toConstruction
    {sourceDelta initialLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (data : schedule.ActualRichEndpointMixedHierarchyData actual) :
    PureWZ2MixedHierarchyConstructionData sigma schedule.terminalFinalLoss
      schedule.ordinary.mild.epsilon₂ sourceDelta
        schedule.ordinary.mild.levelCount where
  terminalInputLoss := actual.chain.finalSource.1
  terminalInputLoss_pos := (schedule.finalSource_loss_bounds actual).1
  terminalInputLoss_le_hierarchy := by
    calc
      actual.chain.finalSource.1 ≤ schedule.terminal.sourceLossCeiling :=
        (schedule.finalSource_loss_bounds actual).2
      _ ≤ schedule.terminalFinalLoss / 100 :=
        schedule.terminal.sourceLossCeiling_le_output
      _ ≤ schedule.ordinary.mild.epsilon₂ := by
        have hfinalPos := schedule.terminalFinalLoss_pos
        have hfinalHierarchy : schedule.terminalFinalLoss ≤
            schedule.ordinary.mild.epsilon₂ := by
          rw [schedule.terminalFinalLoss_eq, ← schedule.mild_eq]
          have hNpos : (0 : ℝ) < schedule.ordinary.mild.levelCount := by
            exact_mod_cast (lt_of_lt_of_le (by omega)
              schedule.ordinary.mild.levelCount_ge_two)
          have hNtwo : (2 : ℝ) ≤ schedule.ordinary.mild.levelCount := by
            exact_mod_cast schedule.ordinary.mild.levelCount_ge_two
          have hdenom : (1 : ℝ) ≤
              8 * schedule.ordinary.mild.levelCount := by nlinarith
          exact div_le_self schedule.ordinary.mild.epsilon₂_pos.le hdenom
        linarith
  terminalSource := actual.chain.finalSource.2.grain
  mixed := data.mixed.1.mixed
  levelCount_eq := data.mixed.2

/-- Run Proposition 5.7 normalization on the production P4 hierarchy while
retaining the exact terminal multiplicity and mass receipts. -/
theorem ActualRichEndpointMixedHierarchyData.toQuantitativeNormalized
    {sourceDelta initialLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (data : schedule.ActualRichEndpointMixedHierarchyData actual)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty { normalized : PureWZ2QuantitativeNormalizedHierarchyOutput
        sigma (outputLoss / 2) sourceDelta //
      normalized.densityLoss = schedule.slabDensityLoss ∧
        0 < normalized.normalized.inputLoss ∧
        normalized.normalized.inputLoss ≤
          schedule.ordinary.mild.epsilon₂ ∧
          normalized.normalized.source.family =
            actual.chain.finalSource.2.grain.family ∧
            normalized.normalized.hierarchy.hierarchy.levelCount =
              schedule.ordinary.mild.levelCount } := by
  let construction := data.toConstruction
  let budget := schedule.mixedNumeric.produce hsourceDelta
    (hsourceSmall.trans schedule.commonDelta₀_le_mixedNumeric) construction
  rcases data.mixed.1.toQuantitativeNormalizedHierarchyOutputWithDensityEq
    (workLoss := outputLoss / 2)
    construction.terminalInputLoss_le_hierarchy
    (by
      linarith [schedule.ordinary.mild.epsilon₂_pos,
        schedule.ordinary.mild.ten_epsilon₂_lt_half_output])
    hbridge schedule.ordinary.sigma_pos
    schedule.ordinary.sigma_lt_one schedule.ordinary.mild.epsilon₂_pos
    budget.finalLoss_le_hierarchy budget.finalLoss_le_level_zero
    budget.delta_strict budget.geometric budget.level_zero budget.removed
    budget.final_volume budget.hierarchyLoss_upper budget.cost_absorb
    budget.threshold budget.source_small with ⟨normalized⟩
  have hdensity : normalized.1.densityLoss ≤ schedule.slabDensityLoss := by
    rw [normalized.2.1]
    change schedule.terminal.kernel.terminal.workingLoss ≤
      schedule.slabDensityLoss
    rw [schedule.slabDensityLoss_eq]
    calc
      schedule.terminal.kernel.terminal.workingLoss ≤
          schedule.terminalFinalLoss :=
        schedule.terminal.kernel.terminal.workingLoss_le_output
      _ ≤ schedule.ordinary.mild.epsilon₂ := by
        rw [schedule.terminalFinalLoss_eq, ← schedule.mild_eq]
        have hNtwo : (2 : ℝ) ≤
            schedule.ordinary.mild.levelCount := by
          exact_mod_cast schedule.ordinary.mild.levelCount_ge_two
        have hdenom : (1 : ℝ) ≤
            8 * schedule.ordinary.mild.levelCount := by nlinarith
        exact div_le_self schedule.ordinary.mild.epsilon₂_pos.le hdenom
      _ ≤ 5 * schedule.ordinary.mild.epsilon₂ := by
        linarith [schedule.ordinary.mild.epsilon₂_pos]
  let weakened := normalized.1.mono_densityLoss
    schedule.slabDensityLoss hdensity
  exact ⟨⟨weakened, rfl,
    by
      change 0 < normalized.1.normalized.inputLoss
      rw [normalized.2.2.1]
      exact construction.terminalInputLoss_pos,
    normalized.2.2.1.trans_le construction.terminalInputLoss_le_hierarchy,
    normalized.2.2.2.1,
    normalized.2.2.2.2.trans data.mixed.2⟩⟩

/-- Production P6 package.  The quantitative hierarchy, mass-heavy slab,
common window, normalized slope and exact affine/local-cleanup geometry are
all retained on one dependent witness. -/
structure ActualRichEndpointP6Data
    {sourceDelta initialLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    (actual : schedule.ordinary.ActualJointHeightPrefixData initial) where
  p4 : schedule.ActualRichEndpointMixedHierarchyData actual
  normalized : PureWZ2QuantitativeNormalizedHierarchyOutput
    sigma (outputLoss / 2) sourceDelta
  densityLoss_eq : normalized.densityLoss = schedule.slabDensityLoss
  inputLoss_pos : 0 < normalized.normalized.inputLoss
  inputLoss_le_epsilon₂ : normalized.normalized.inputLoss ≤
    schedule.ordinary.mild.epsilon₂
  source_bounded_base :
    HasBoundedBase normalized.normalized.source.family 4
  levelCount_eq : normalized.normalized.hierarchy.hierarchy.levelCount =
    schedule.ordinary.mild.levelCount
  sourceSmall_lemma35 : sourceDelta ≤
    pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀
  sourceSmall_selectedSourceFrostman :
    sourceDelta ≤ schedule.selectedSourceFrostman.delta₀
  sourceSmall_jointDensity :
    sourceDelta ≤ schedule.jointDensity.sourceDelta₀
  sourceSmall_p7Rounding :
    sourceDelta ≤ schedule.p7Rounding.delta₀
  sourceSmall_p7Volume :
    sourceDelta ≤ schedule.p7Volume.delta₀
  sourceSmall_p7Terminal :
    sourceDelta ≤ schedule.p7Terminal.delta₀
  geometry :
    PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData
      normalized.normalized sourceSmall_lemma35
  slab_mass_retention :
    ENNReal.ofReal
          (2 * normalized.normalized.prepared.slab.halfHeight) *
        (ENNReal.ofReal (1 / 6) *
          (Kakeya.realRpowENN sourceDelta schedule.slabDensityLoss *
            (wz1PaperBodyFamily
              normalized.normalized.source.family).mass)) ≤
      3 * normalized.normalized.prepared.slab.shading.mass

/-- Instantiate the paper's P6 heavy-slab and exact affine-map construction
on the same quantitative P4 hierarchy. -/
theorem actualRichEndpointP6
    {sourceDelta initialLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    (actual : schedule.ordinary.ActualJointHeightPrefixData initial)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (schedule.ActualRichEndpointP6Data actual) := by
  rcases schedule.actualRichEndpointMixedHierarchy
      hsourceDelta hsourceSmall actual hbridge with ⟨p4⟩
  rcases p4.toQuantitativeNormalized schedule hsourceDelta hsourceSmall hbridge with
    ⟨normalized⟩
  have hlemma35 : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀ :=
    hsourceSmall.trans schedule.commonDelta₀_le_lemma35
  exact ⟨{
    p4 := p4
    normalized := normalized.1
    densityLoss_eq := normalized.2.1
    inputLoss_pos := normalized.2.2.1
    inputLoss_le_epsilon₂ := normalized.2.2.2.1
    source_bounded_base := by
      rw [normalized.2.2.2.2.1]
      exact actual.chain.finalSource.2.reentry.geometry.ordinary_bounded_base
    levelCount_eq := normalized.2.2.2.2.2
    sourceSmall_lemma35 := hlemma35
    sourceSmall_selectedSourceFrostman :=
      hsourceSmall.trans schedule.commonDelta₀_le_selectedSourceFrostman
    sourceSmall_jointDensity :=
      hsourceSmall.trans schedule.commonDelta₀_le_jointDensity
    sourceSmall_p7Rounding :=
      hsourceSmall.trans schedule.commonDelta₀_le_p7Rounding
    sourceSmall_p7Volume :=
      hsourceSmall.trans schedule.commonDelta₀_le_p7Volume
    sourceSmall_p7Terminal :=
      hsourceSmall.trans schedule.commonDelta₀_le_p7Terminal
    geometry := normalized.1.normalized.lemma35GeometricData hlemma35
    slab_mass_retention := by
      simpa only [normalized.2.1] using
        (mul_le_mul_left' normalized.1.normalized_mass_retention _).trans
          normalized.1.normalized.prepared.slab.mass_fraction }⟩

/-- The P0 cutoff absorbs the exact common-window source cost on the same P6
witness.  No family or slab is reselected. -/
noncomputable def ActualRichEndpointP6Data.selectedSourceFrostman
    {sourceDelta initialLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    {actual : schedule.ordinary.ActualJointHeightPrefixData initial}
    (data : schedule.ActualRichEndpointP6Data actual) :
    PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.SelectedSourceFrostmanReceipt
      data.geometry :=
  PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.SelectedSourceFrostmanReceipt.ofQuantitative3200
    data.normalized data.geometry data.source_bounded_base <| by
      have habsorb := schedule.selectedSourceFrostman.absorption
        (sourceDelta := sourceDelta)
        (inputLoss := data.normalized.normalized.inputLoss)
        (halfHeight :=
          data.normalized.normalized.prepared.slab.halfHeight)
        data.normalized.normalized.source.extremal.delta_pos
        data.sourceSmall_selectedSourceFrostman
        data.inputLoss_le_epsilon₂
        (by
          rw [data.normalized.normalized.prepared.slab.halfHeight_eq,
            data.levelCount_eq])
      simpa only [
        PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.selectedSourceWeight,
        data.densityLoss_eq] using habsorb

end PureWZ2C2RichEndpointClosureSchedule

end Kakeya.Assouad

end
