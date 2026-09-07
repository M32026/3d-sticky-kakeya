import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightVariablePrefix

/-!
# The direct-rich endpoint invocation for the actual joint-height prefix

At the terminal paper scale `rho_N = sourceDelta`, the first leg is the
literal final re-entry source of the ordinary prefix.  Thus there is no first
Proposition-6.2 invocation.  This module weakens only that source's two loss
labels to the preselected endpoint schedule and makes the sole nontrivial call
at `sqrt sourceDelta`.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2C2OrdinaryGlobalSchedule

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (schedule : PureWZ2C2OrdinaryGlobalSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal)

/-- The final ordinary source, with only its loss labels weakened to the
preselected endpoint kernel.  Its family, shading, frame, and all geometric
provenance are definitionally unchanged. -/
noncomputable def endpointKernelReentry
    {sourceDelta initialLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    (actual : schedule.ActualJointHeightPrefixData initial)
    (finalLossLe : actual.chain.finalSource.1 ≤
      schedule.endpointKernel.sourceLoss) :
    PureWZ2PropStickyReentryData
      (sigma := sigma) actual.chain.finalSource.2.grain.shading
      capability.normalizationExponent schedule.endpointKernel.sourceLoss
      schedule.endpointKernel.normalizationLoss := by
  let current := actual.chain.finalSource.2
  have ordinaryLossLe :
      current.ordinaryLoss ≤ schedule.endpointKernel.sourceLoss := by
    exact current.reentry.sourceLoss_le_half.trans
      ((div_le_self current.reentry.normalizationLoss_pos.le
        (by norm_num)).trans finalLossLe)
  have sourceLeNormalization :
      schedule.endpointKernel.sourceLoss ≤
        schedule.endpointKernel.normalizationLoss := by
    linarith [schedule.endpointKernel.sourceLoss_le_half,
      schedule.endpointKernel.normalizationLoss_pos]
  exact current.reentry.mono_losses ordinaryLossLe
    (finalLossLe.trans sourceLeNormalization)
    schedule.endpointKernel.sourceLoss_pos
    schedule.endpointKernel.normalizationLoss_pos
    schedule.endpointKernel.sourceLoss_le_half

/-- The endpoint datum stores the literal final source of the ordinary chain
as its identity first leg and the output of exactly one direct-rich call, at
`sqrt sourceDelta`.  No independent source or first-call witness occurs in
this type. -/
structure ActualJointHeightEndpointInvocationData
    {sourceDelta initialLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    (actual : schedule.ActualJointHeightPrefixData initial) where
  finalLossLe : actual.chain.finalSource.1 ≤
    schedule.endpointKernel.sourceLoss
  sqrtRequested : WZ2PaperRequestedScale sourceDelta
  sqrtRequested_eq : sqrtRequested.1 = Real.sqrt sourceDelta
  rich : PureWZ2.Proposition63RichTerminalStickyData
    (outputLoss := schedule.endpointOutputLoss)
    actual.chain.finalSource.2.grain.shading
    (schedule.endpointKernelReentry actual finalLossLe) sqrtRequested

/-- Invoke the preselected endpoint kernel on the literal final source of the
actual ordinary prefix.  The only call is `runTerminal` at
`sqrt sourceDelta`; the paper's first endpoint cover is the unchanged source.
-/
theorem actualJointHeightEndpointInvocation
    {sourceDelta initialLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceSmall : sourceDelta ≤ schedule.commonDelta₀)
    {initial : PureWZ2ReentrantGrainSource sigma initialLoss sourceDelta
      capability.normalizationExponent}
    (actual : schedule.ActualJointHeightPrefixData initial) :
    Nonempty (schedule.ActualJointHeightEndpointInvocationData actual) := by
  have hcount : 0 < schedule.mild.levelCount - 1 := by
    have hN := schedule.mild.levelCount_ge_two
    omega
  have hlast :
      (⟨schedule.mild.levelCount - 1 - 1, by omega⟩ :
          Fin (schedule.mild.levelCount - 1)) =
        ⟨schedule.mild.levelCount - 2, by omega⟩ := by
    apply Fin.ext
    simp only [Nat.sub_sub]
  have hfinalLoss : actual.chain.finalSource.1 ≤
      schedule.endpointKernel.sourceLoss := by
    rw [actual.chain.finalSource_loss_eq_last_outputAt hcount,
      actual.outputLoss_eq, hlast]
    exact schedule.ordinaryPrefix.outputLoss_last_le_terminal
  have hdeltaOne : sourceDelta ≤ 1 :=
    hsourceSmall.trans <| schedule.commonDelta₀_le_endpoint.trans
      schedule.endpointKernel.delta₀_le_one
  have hdeltaSqrt : sourceDelta ≤ Real.sqrt sourceDelta := by
    nlinarith [Real.sqrt_nonneg sourceDelta,
      Real.sq_sqrt hsourceDelta.le, hdeltaOne]
  have hsqrtOne : Real.sqrt sourceDelta ≤ 1 :=
    Real.sqrt_le_one.mpr hdeltaOne
  let sqrtRequested : WZ2PaperRequestedScale sourceDelta :=
    ⟨Real.sqrt sourceDelta, hdeltaSqrt, hsqrtOne⟩
  have hendpointHalf : schedule.endpointOutputLoss ≤ 1 / 2 := by
    have hsigma := schedule.sigma_lt_one
    have hendpoint := schedule.endpointOutputLoss_le_sigma_sixteenth
    nlinarith
  have hsqrtLower :
      Real.rpow sourceDelta (1 - schedule.endpointOutputLoss) ≤
        sqrtRequested.1 := by
    dsimp only [sqrtRequested]
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hsourceDelta hdeltaOne
      (by linarith)
  have hsqrtUpper :
      sqrtRequested.1 ≤
        Real.rpow sourceDelta schedule.endpointOutputLoss := by
    dsimp only [sqrtRequested]
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hsourceDelta hdeltaOne
      hendpointHalf
  have hdeltaEndpoint : sourceDelta ≤ schedule.endpointKernel.delta₀ :=
    hsourceSmall.trans schedule.commonDelta₀_le_endpoint
  rcases schedule.endpointKernel.runTerminal sourceDelta hsourceDelta
      hdeltaEndpoint actual.chain.finalSource.2.grain.family
      actual.chain.finalSource.2.grain.shading
      (schedule.endpointKernelReentry actual hfinalLoss) sqrtRequested
      hsqrtLower hsqrtUpper with
    ⟨rich⟩
  exact ⟨{
    finalLossLe := hfinalLoss
    sqrtRequested := sqrtRequested
    sqrtRequested_eq := rfl
    rich := rich
  }⟩

end PureWZ2C2OrdinaryGlobalSchedule

end Kakeya.Assouad

end
