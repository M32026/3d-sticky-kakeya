import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantTerminalSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalWindowScheduledChain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05OwnerUniversalInputBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PostDeletionReentrantScaleThresholds

/-!
# Runtime construction for the reentrant exact terminal

This module intersects the terminal numerical schedule with the public
re-entry kernel schedule before the runtime source is known.  At runtime the
stored re-entry is weakened to those scheduled losses and the kernel is
actually invoked at `sqrt delta`.  The remaining family-dependent boundary is
split into an exact-owner extension and one final scalar power estimate.
The actual good-block windows retain their canonical supply certificates.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- Terminal scalars and one compatible public re-entry kernel schedule. -/
structure PureWZ2ReentrantTerminalKernelSchedule
    (capability : PureWZ2PropStickyCapability)
    (sigma outputLoss : ℝ) where
  terminal : PureWZ2ReentrantTerminalScalarSchedule sigma outputLoss
  kernel : PureWZ2PropStickyReentryKernelScheduleData
    (sigma := sigma) (outputLoss := terminal.sourceLossCeiling)
    capability.normalizationExponent capability.logExponent
  ownerThresholds :
    SameFamilyOwnerUniformScalarThresholds
      sigma terminal.sourceLossCeiling
  sourceLossCeiling : ℝ :=
    min (terminal.sourceLossCeiling / 100) kernel.sourceLoss
  sourceLossCeiling_eq :
    sourceLossCeiling =
      min (terminal.sourceLossCeiling / 100) kernel.sourceLoss
  sourceLossCeiling_pos : 0 < sourceLossCeiling
  sourceLossCeiling_seed_gap :
    sourceLossCeiling ≤ terminal.sourceLossCeiling / 100
  sourceLossCeiling_terminal :
    sourceLossCeiling ≤ terminal.sourceLossCeiling
  sourceLossCeiling_kernel : sourceLossCeiling ≤ kernel.sourceLoss
  postDeletionThresholds :
    PureWZ2PostDeletionReentrantScaleThresholds
      sourceLossCeiling terminal.sourceLossCeiling
  delta₀ : ℝ :=
    min terminal.delta₀
      (min kernel.delta₀
        (min ownerThresholds.delta₀ postDeletionThresholds.delta₀))
  delta₀_eq :
    delta₀ =
      min terminal.delta₀
        (min kernel.delta₀
          (min ownerThresholds.delta₀ postDeletionThresholds.delta₀))
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_terminal : delta₀ ≤ terminal.delta₀
  delta₀_kernel : delta₀ ≤ kernel.delta₀
  delta₀_owner : delta₀ ≤ ownerThresholds.delta₀
  delta₀_postDeletion : delta₀ ≤ postDeletionThresholds.delta₀
  kernelLoss_le_half : terminal.sourceLossCeiling ≤ 1 / 2

/-- Every admitted runtime source loss is strictly below the public seed
loss.  This is the pre-family exponent gap needed by the post-deletion
actual-to-caller absorption. -/
theorem PureWZ2ReentrantTerminalKernelSchedule.inputLoss_lt_terminalSourceLoss
    {capability : PureWZ2PropStickyCapability} {sigma outputLoss : ℝ}
    (schedule : PureWZ2ReentrantTerminalKernelSchedule
      capability sigma outputLoss)
    {inputLoss : ℝ}
    (hinput : inputLoss ≤ schedule.sourceLossCeiling) :
    inputLoss < schedule.terminal.sourceLossCeiling := by
  have hgap :
      schedule.terminal.sourceLossCeiling / 100 <
        schedule.terminal.sourceLossCeiling := by
    nlinarith [schedule.terminal.sourceLossCeiling_pos]
  exact hinput.trans_lt (schedule.sourceLossCeiling_seed_gap.trans_lt hgap)

/-- Select every source-independent scalar before the runtime reentrant
configuration. -/
theorem pureWZ2_reentrantTerminal_kernelSchedule
    (capability : PureWZ2PropStickyCapability)
    {sigma : ℝ} (critical : PureWZ2CriticalPackage sigma)
    {outputLoss : ℝ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtput : 0 < outputLoss) :
    Nonempty (PureWZ2ReentrantTerminalKernelSchedule
      capability sigma outputLoss) := by
  rcases pureWZ2_reentrantTerminal_scalarSchedule hsigma hsigmaOne houtput with
    ⟨terminal⟩
  have hkernelLossOne : terminal.sourceLossCeiling ≤ 1 := by
    have hworking : terminal.sourceLossCeiling ≤ terminal.workingLoss / 100 :=
      terminal.sourceLossCeiling_working
    linarith [terminal.workingLoss_lt_one]
  rcases capability.kernel sigma critical terminal.sourceLossCeiling
      terminal.sourceLossCeiling_pos hkernelLossOne with ⟨kernel⟩
  rcases sameFamilyOwnerUniformScalarThresholds sigma
      terminal.sourceLossCeiling critical terminal.sourceLossCeiling_pos with
    ⟨ownerThresholds⟩
  let sourceLossCeiling :=
    min (terminal.sourceLossCeiling / 100) kernel.sourceLoss
  have hkernelLossHalf : terminal.sourceLossCeiling ≤ 1 / 2 := by
    have hworking : terminal.sourceLossCeiling ≤ terminal.workingLoss / 100 :=
      terminal.sourceLossCeiling_working
    linarith [terminal.workingLoss_lt_one]
  have hsourceGap :
      sourceLossCeiling < terminal.sourceLossCeiling := by
    have hgap :
        terminal.sourceLossCeiling / 100 <
          terminal.sourceLossCeiling := by
      nlinarith [terminal.sourceLossCeiling_pos]
    exact (min_le_left _ _).trans_lt hgap
  rcases
      pureWZ2_postDeletion_reentrant_scale_thresholds
        hsourceGap hkernelLossHalf
    with
    ⟨postDeletionThresholds⟩
  let delta₀ :=
    min terminal.delta₀
      (min kernel.delta₀
        (min ownerThresholds.delta₀ postDeletionThresholds.delta₀))
  exact ⟨{
    terminal := terminal
    kernel := kernel
    ownerThresholds := ownerThresholds
    sourceLossCeiling := sourceLossCeiling
    sourceLossCeiling_eq := rfl
    sourceLossCeiling_pos :=
      lt_min (div_pos terminal.sourceLossCeiling_pos (by norm_num))
        kernel.sourceLoss_pos
    sourceLossCeiling_seed_gap := min_le_left _ _
    sourceLossCeiling_terminal :=
      (min_le_left _ _).trans
        (div_le_self terminal.sourceLossCeiling_pos.le (by norm_num))
    sourceLossCeiling_kernel := min_le_right _ _
    postDeletionThresholds := postDeletionThresholds
    delta₀ := delta₀
    delta₀_eq := rfl
    delta₀_pos := lt_min terminal.delta₀_pos
      (lt_min kernel.delta₀_pos
        (lt_min ownerThresholds.delta₀_pos
          postDeletionThresholds.delta₀_pos))
    delta₀_le_one := (min_le_left _ _).trans terminal.delta₀_le_one
    delta₀_terminal := min_le_left _ _
    delta₀_kernel := (min_le_right _ _).trans (min_le_left _ _)
    delta₀_owner := (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
    delta₀_postDeletion := (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_right _ _)
    kernelLoss_le_half := hkernelLossHalf }⟩

/-- Restrict the terminal schedule to the common source-loss and scale
thresholds selected together with the kernel schedule. -/
noncomputable def PureWZ2ReentrantTerminalKernelSchedule.toTerminalSchedule
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss : ℝ}
    (schedule : PureWZ2ReentrantTerminalKernelSchedule
      capability sigma outputLoss) :
    PureWZ2ReentrantTerminalScalarSchedule sigma outputLoss where
  workingLoss := schedule.terminal.workingLoss
  stickyLoss := schedule.terminal.stickyLoss
  eta := schedule.terminal.eta
  theoremEta := schedule.terminal.theoremEta
  theoremEta_eq := schedule.terminal.theoremEta_eq
  volumeLoss := schedule.terminal.volumeLoss
  constantLoss := schedule.terminal.constantLoss
  constantLoss_pos := schedule.terminal.constantLoss_pos
  extraLoss := schedule.terminal.extraLoss
  extraLoss_pos := schedule.terminal.extraLoss_pos
  sourceLossCeiling := schedule.sourceLossCeiling
  delta₀ := schedule.delta₀
  sigma_pos := schedule.terminal.sigma_pos
  sigma_lt_one := schedule.terminal.sigma_lt_one
  output_pos := schedule.terminal.output_pos
  workingLoss_pos := schedule.terminal.workingLoss_pos
  workingLoss_le_output := schedule.terminal.workingLoss_le_output
  workingLoss_le_half := schedule.terminal.workingLoss_le_half
  workingLoss_lt_one := schedule.terminal.workingLoss_lt_one
  workingLoss_sigma := schedule.terminal.workingLoss_sigma
  stickyLoss_lt_working := schedule.terminal.stickyLoss_lt_working
  stickyLoss_le_working_quarter :=
    schedule.terminal.stickyLoss_le_working_quarter
  projection := schedule.terminal.projection
  sourceLossCeiling_pos := schedule.sourceLossCeiling_pos
  sourceLossCeiling_lt_stickyLoss :=
    lt_of_le_of_lt schedule.sourceLossCeiling_terminal
      schedule.terminal.sourceLossCeiling_lt_stickyLoss
  sourceLossCeiling_working :=
    schedule.sourceLossCeiling_terminal.trans
      schedule.terminal.sourceLossCeiling_working
  sourceLossCeiling_constant :=
    schedule.sourceLossCeiling_terminal.trans
      schedule.terminal.sourceLossCeiling_constant
  sourceLossCeiling_sticky_volume :=
    lt_of_le_of_lt
      (by
        simpa [add_comm] using add_le_add_right
          schedule.sourceLossCeiling_terminal
            (5 * schedule.terminal.stickyLoss / 2))
      schedule.terminal.sourceLossCeiling_sticky_volume
  sourceLossCeiling_projection :=
    schedule.sourceLossCeiling_terminal.trans
      schedule.terminal.sourceLossCeiling_projection
  delta₀_pos := schedule.delta₀_pos
  delta₀_le_one := schedule.delta₀_le_one
  delta₀_projection := schedule.delta₀_terminal.trans
    schedule.terminal.delta₀_projection
  budget := fun inputLoss delta hinput hinputCeiling hdelta hdeltaSmall =>
    schedule.terminal.budget inputLoss delta hinput
      (hinputCeiling.trans schedule.sourceLossCeiling_terminal) hdelta
      (hdeltaSmall.trans schedule.delta₀_terminal)
  c_real := fun inputLoss delta hinput hinputCeiling hdelta hdeltaSmall =>
    schedule.terminal.c_real inputLoss delta hinput
      (hinputCeiling.trans schedule.sourceLossCeiling_terminal) hdelta
      (hdeltaSmall.trans schedule.delta₀_terminal)
  volume_budget :=
    fun inputLoss delta hinput hinputCeiling hdelta hdeltaSmall =>
      schedule.terminal.volume_budget inputLoss delta hinput
        (hinputCeiling.trans schedule.sourceLossCeiling_terminal) hdelta
        (hdeltaSmall.trans schedule.delta₀_terminal)
  extra := fun preparedGraph hdelta hdeltaSmall =>
    schedule.terminal.extra preparedGraph hdelta
      (hdeltaSmall.trans schedule.delta₀_terminal)
  edge := fun delta hdelta hdeltaSmall =>
    schedule.terminal.edge delta hdelta
      (hdeltaSmall.trans schedule.delta₀_terminal)
  refined_edge := fun delta hdelta hdeltaSmall =>
    schedule.terminal.refined_edge delta hdelta
      (hdeltaSmall.trans schedule.delta₀_terminal)
  katz := fun delta hdelta hdeltaSmall =>
    schedule.terminal.katz delta hdelta
      (hdeltaSmall.trans schedule.delta₀_terminal)
  refined_katz := fun delta hdelta hdeltaSmall =>
    schedule.terminal.refined_katz delta hdelta
      (hdeltaSmall.trans schedule.delta₀_terminal)
  alternativeA := fun ready hinput hinputCeiling hdeltaSmall =>
    schedule.terminal.alternativeA ready hinput
      (hinputCeiling.trans schedule.sourceLossCeiling_terminal)
      (hdeltaSmall.trans schedule.delta₀_terminal)

/--
Run the closed post-deletion constructor on the exact terminal normalization.
The result depends on the supplied witness, so its family provenance cannot
be replaced after the fact.
-/
noncomputable def pureWZ2ReentrantTerminalPostDeletionInput
    {sigma inputLoss delta : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    (sqrtRequested : WZ2PaperRequestedScale delta)
    (deletionExponent : ℕ)
    (construction : PureWZ2PostDeletionUniversalConstructionWitness
      current.reentry.toNormalizationData sqrtRequested deletionExponent) :
    PureWZ2CroppedPostDeletionUniversalInput
      current.reentry.toNormalizationData sqrtRequested deletionExponent :=
  Classical.choice <|
    pureWZ2_cropped_post_deletion_universal_input
      current.reentry.toNormalizationData sqrtRequested construction

/--
The callback-free actual-owner prefix at the terminal square-root scale.
Only the quantitative/geometric receipt for the canonical owner selection is
stored; every preceding family is reconstructed by closed constructors.
-/
structure PureWZ2ReentrantTerminalActualOwnerInputReceipt
    {sigma inputLoss delta outputLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalKernelSchedule
      capability sigma outputLoss}
    (current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent) where
  sqrtRequested : WZ2PaperRequestedScale delta
  sqrtRequested_eq : sqrtRequested.1 = Real.sqrt delta
  deletionExponent : ℕ
  construction : PureWZ2PostDeletionUniversalConstructionWitness
    current.reentry.toNormalizationData sqrtRequested deletionExponent
  delta_small : delta ≤ schedule.ownerThresholds.delta₀
  rho_lower :
    Real.rpow delta (1 - schedule.terminal.sourceLossCeiling) ≤
      sqrtRequested.1
  rho_upper :
    sqrtRequested.1 ≤
      Real.rpow delta schedule.terminal.sourceLossCeiling
  actualReceipts : SameFamilyOwnerActualReceipts
    (logExponent := capability.logExponent)
    (pureWZ2ReentrantTerminalPostDeletionInput sqrtRequested
      deletionExponent construction)
    schedule.ownerThresholds current.grain.extremal.delta_pos delta_small
    rho_lower rho_upper
    (pureWZ2PostDeletionCanonicalActualOwnerData
      (pureWZ2ReentrantTerminalPostDeletionInput sqrtRequested
        deletionExponent construction))

namespace PureWZ2ReentrantTerminalActualOwnerInputReceipt

noncomputable def post
    {sigma inputLoss delta outputLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalKernelSchedule
      capability sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    (receipt : PureWZ2ReentrantTerminalActualOwnerInputReceipt
      (schedule := schedule) current) :
    PureWZ2CroppedPostDeletionUniversalInput
      current.reentry.toNormalizationData receipt.sqrtRequested
      receipt.deletionExponent :=
  pureWZ2ReentrantTerminalPostDeletionInput receipt.sqrtRequested
    receipt.deletionExponent receipt.construction

noncomputable def input
    {sigma inputLoss delta outputLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalKernelSchedule
      capability sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    (receipt : PureWZ2ReentrantTerminalActualOwnerInputReceipt
      (schedule := schedule) current) :
    PureWZ2CroppedPropStickyUniversalInput
      (outputLoss := schedule.terminal.sourceLossCeiling)
      current.reentry.toNormalizationData receipt.sqrtRequested
      capability.logExponent :=
  pureWZ2CroppedPropStickyUniversalInputOfCanonicalActual receipt.post
    schedule.ownerThresholds schedule.terminal.sigma_pos
    current.grain.extremal.delta_pos receipt.delta_small receipt.rho_lower
    receipt.rho_upper receipt.actualReceipts

end PureWZ2ReentrantTerminalActualOwnerInputReceipt

/--
One genuine terminal Node-5 invocation.  Its sticky datum is definitionally
the deterministic output of the exact canonical actual-owner input.
-/
structure PureWZ2ReentrantTerminalKernelInvocation
    {sigma inputLoss delta outputLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalKernelSchedule
      capability sigma outputLoss}
    (current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent) where
  outputLogExponent : ℕ
  sqrtRequested : WZ2PaperRequestedScale delta
  sqrtRequested_eq : sqrtRequested.1 = Real.sqrt delta
  seed : PureWZ2ReentrantPropStickyData
    (sigma := sigma) (outputLoss := schedule.terminal.sourceLossCeiling)
    current.grain.shading sqrtRequested capability.normalizationExponent
    capability.logExponent
  call : PureWZ2Node05DeterministicOwnerCallReceipt seed
    schedule.terminal.stickyLoss outputLogExponent

namespace PureWZ2ReentrantTerminalKernelInvocation

noncomputable def sticky
    {sigma inputLoss delta outputLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalKernelSchedule
      capability sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    (invocation : PureWZ2ReentrantTerminalKernelInvocation
      (schedule := schedule) current) :
    PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := schedule.terminal.sourceLossCeiling)
      current.grain.shading invocation.sqrtRequested capability.logExponent :=
  invocation.seed.data

end PureWZ2ReentrantTerminalKernelInvocation

/-- Exact-owner continuation of the public kernel output.  The heterogeneous
equality prevents an unrelated universal-owner witness from being substituted. -/
structure PureWZ2ReentrantTerminalKernelOwnerReceipt
    {sigma inputLoss delta outputLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalKernelSchedule
      capability sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    (invocation : PureWZ2ReentrantTerminalKernelInvocation
      (schedule := schedule) current) where
  outputLogExponent : ℕ
  seed : PureWZ2ReentrantPropStickyData
    (sigma := sigma) (outputLoss := schedule.terminal.sourceLossCeiling)
    current.grain.shading invocation.sqrtRequested
    capability.normalizationExponent capability.logExponent
  seed_data_eq : seed.data = invocation.sticky
  call : PureWZ2Node05DeterministicOwnerCallReceipt
    seed schedule.terminal.stickyLoss outputLogExponent

namespace PureWZ2ReentrantTerminalKernelOwnerReceipt

/-- Recover the owner ABI directly from the construction-dependent
invocation.  The deterministic-data equality is reflexive. -/
noncomputable def ofInvocation
    {sigma inputLoss delta outputLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalKernelSchedule
      capability sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    (invocation : PureWZ2ReentrantTerminalKernelInvocation
      (schedule := schedule) current) :
    PureWZ2ReentrantTerminalKernelOwnerReceipt invocation where
  outputLogExponent := invocation.outputLogExponent
  seed := invocation.seed
  seed_data_eq := rfl
  call := invocation.call

/-- Package the exact owner continuation in the terminal owner's ABI. -/
noncomputable def toOwner
    {sigma inputLoss delta outputLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalKernelSchedule
      capability sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {invocation : PureWZ2ReentrantTerminalKernelInvocation
      (schedule := schedule) current}
    (receipt : PureWZ2ReentrantTerminalKernelOwnerReceipt invocation) :
    PureWZ2ReentrantTerminalOwnerCall
      current schedule.terminal.stickyLoss where
  seedLoss := schedule.terminal.sourceLossCeiling
  seedLogExponent := capability.logExponent
  outputLogExponent := receipt.outputLogExponent
  sqrtRequested := invocation.sqrtRequested
  sqrtRequested_eq := invocation.sqrtRequested_eq
  seed := receipt.seed
  call := receipt.call

end PureWZ2ReentrantTerminalKernelOwnerReceipt

/-- The certified-window adapter before `minimum_supply` is erased by
`toGraphWindow`.  The only other input is the source-independent scalar volume
budget selected outside the runtime geometry. -/
theorem PureWZ2TerminalCertifiedWindow.preparedShadowVolume
    {sigma inputLoss delta stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (certified : PureWZ2TerminalCertifiedWindow prepared)
    {line : PureWZ2HorizontalFixedLineCore
      certified.toGraphWindow.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    {residue : PureWZ2TerminalParentYResidueData selection}
    {retained : PureWZ2TerminalRetainedShadingData residue}
    {sources : PureWZ2TerminalSourceFamily retained}
    {band : PureWZ2TerminalFixedBandSelection sources}
    {phase : PureWZ2TerminalHeightPhaseSelection band}
    {anchored : PureWZ2TerminalAnchoredPieceData phase}
    (prep : PureWZ2TerminalExactGraphPreparation anchored)
    (scalarBudget :
      Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
        (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2)) :
    Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) ≤
      MeasureTheory.volume prep.shadow.union :=
  prep.power_volume_lower_of_schedule certified.minimum_supply scalarBudget

/-- The final mass absorption on the actual prepared shadow and balanced
cell mass.  The equality fixes the otherwise freely stored good-family loss
to the scalar schedule's chosen `extraLoss`. -/
structure PureWZ2ReentrantTerminalFinalMassReceipt
    {sigma inputLoss delta outputLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalKernelSchedule
      capability sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    (owner : PureWZ2ReentrantTerminalOwnerCall
      current schedule.terminal.stickyLoss) where
  absorb :
    ∀ {terminalSource : PureWZ2TerminalPreparedSource
          current.grain owner.toTerminalScaleStickyData}
      (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
      {good : PureWZ2TerminalExactGoodBlockFamilyData
        (eta := schedule.terminal.eta)
        (theoremEta := schedule.terminal.theoremEta)
        (outputLoss := schedule.terminal.workingLoss) prepared},
      good.extraLoss = schedule.terminal.extraLoss →
        64 * pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
            pureWZ2TerminalExactHeightRetentionCost delta good.extraLoss *
            Kakeya.realRpowENN delta
              (sigma + schedule.terminal.workingLoss) ≤
          MeasureTheory.volume prepared.shadow.union *
            owner.toTerminalScaleStickyData.sticky.balanced.cellMass *
            pureWZ2TerminalExactRichFloor
              delta schedule.terminal.workingLoss

/-- The genuinely remaining runtime inputs after kernel invocation and scalar
selection.  This is strictly smaller than the final runtime receipt. -/
structure PureWZ2ReentrantTerminalDependentReceipts
    {sigma inputLoss delta outputLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalKernelSchedule
      capability sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    (invocation : PureWZ2ReentrantTerminalKernelInvocation
      (schedule := schedule) current) where
  owner : PureWZ2ReentrantTerminalKernelOwnerReceipt invocation
  finalMass : PureWZ2ReentrantTerminalFinalMassReceipt owner.toOwner

/-- Assemble all good terminal blocks when each actual certified block window
has a dependent chain.  This keeps the window-supply witness attached instead
of requiring a volume estimate for arbitrary erased graph windows. -/
theorem PureWZ2TerminalLemma23Prepared.buildExactGoodBlockFamilyOfWindowChains
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (chainFor : ∀ {block : ℤ}
      (windowData : PureWZ2TerminalBlockWindowData prepared block),
        Nonempty (PureWZ2TerminalWindowChainOutput
          (eta := eta) (theoremEta := theoremEta)
          (outputLoss := outputLoss) windowData.window))
    (hextra : ∀ {window : PureWZ2TerminalWindow prepared}
      (chain : PureWZ2TerminalWindowChainOutput
        (eta := eta) (theoremEta := theoremEta)
        (outputLoss := outputLoss) window),
      (chain.preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow delta (-extraLoss))
    (hgood : (pureWZ2GoodTerminalBlocks prepared).Nonempty) :
    Nonempty { good : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared // good.extraLoss = extraLoss } := by
  let goodBlocks := pureWZ2GoodTerminalBlocks prepared
  let goodEquiv := goodBlocks.equivFin
  let block : Fin goodBlocks.card → ℤ := fun index =>
    (goodEquiv.symm index).1
  have hblockMem : ∀ index, block index ∈ goodBlocks := fun index =>
    (goodEquiv.symm index).2
  have hblockInjective : Function.Injective block := by
    intro first second heq
    apply goodEquiv.symm.injective
    exact Subtype.ext heq
  let windowData : ∀ index : Fin goodBlocks.card,
      PureWZ2TerminalBlockWindowData prepared (block index) := fun index =>
    Classical.choice (prepared.windowDataOfGoodBlock (hblockMem index))
  let chain : ∀ index, PureWZ2TerminalWindowChainOutput
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) (windowData index).window := fun index =>
    Classical.choice (chainFor (windowData index))
  let heightLift : ∀ index, PureWZ2TerminalExactHeightLift
      (chain index).exactTrapezoid := fun index =>
    Classical.choice (chain index).exactTrapezoid.toHeightLift
  let good : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared := {
    indexCount := goodBlocks.card
    indexCount_pos := Finset.card_pos.mpr hgood
    block := block
    block_injective := hblockInjective
    block_mem := hblockMem
    block_surjective := by
      intro target htarget
      let index := goodEquiv ⟨target, htarget⟩
      refine ⟨index, ?_⟩
      change (goodEquiv.symm index).1 = target
      simp [index]
    windowData := windowData
    chain := chain
    heightLift := heightLift
    extraLoss := extraLoss
    extraCost_power := fun index => hextra (chain index) }
  exact ⟨⟨good, rfl⟩⟩

/-- Build the exact good-block family while retaining the definitional value
of its extra-loss field.  The older existential API erases this equality. -/
theorem PureWZ2TerminalLemma23Prepared.buildExactGoodBlockFamilyWithExtraLoss
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (budget : PureWZ2TerminalChainBudget
      sigma inputLoss delta stickyLoss eta theoremEta outputLoss)
    (certificates : PureWZ2TerminalChainCertificates
      eta theoremEta outputLoss terminal)
    (hextra : ∀ {window : PureWZ2TerminalWindow prepared}
      (chain : PureWZ2TerminalWindowChainOutput
        (eta := eta) (theoremEta := theoremEta)
        (outputLoss := outputLoss) window),
      (chain.preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow delta (-extraLoss))
    (hgood : (pureWZ2GoodTerminalBlocks prepared).Nonempty) :
    Nonempty { good : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared // good.extraLoss = extraLoss } := by
  let goodBlocks := pureWZ2GoodTerminalBlocks prepared
  let goodEquiv := goodBlocks.equivFin
  let block : Fin goodBlocks.card → ℤ := fun index =>
    (goodEquiv.symm index).1
  have hblockMem : ∀ index, block index ∈ goodBlocks := fun index =>
    (goodEquiv.symm index).2
  have hblockInjective : Function.Injective block := by
    intro first second heq
    apply goodEquiv.symm.injective
    exact Subtype.ext heq
  let windowData : ∀ index : Fin goodBlocks.card,
      PureWZ2TerminalBlockWindowData prepared (block index) := fun index =>
    Classical.choice (prepared.windowDataOfGoodBlock (hblockMem index))
  have hchain : ∀ index, Nonempty (PureWZ2TerminalWindowChainOutput
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) (windowData index).window) := fun index =>
    pureWZ2_terminal_window_chain_of_certificates
      (windowData index).window hbridge budget certificates
  let chain : ∀ index, PureWZ2TerminalWindowChainOutput
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) (windowData index).window := fun index =>
    Classical.choice (hchain index)
  let heightLift : ∀ index, PureWZ2TerminalExactHeightLift
      (chain index).exactTrapezoid := fun index =>
    Classical.choice (chain index).exactTrapezoid.toHeightLift
  let good : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared := {
    indexCount := goodBlocks.card
    indexCount_pos := Finset.card_pos.mpr hgood
    block := block
    block_injective := hblockInjective
    block_mem := hblockMem
    block_surjective := by
      intro target htarget
      let index := goodEquiv ⟨target, htarget⟩
      refine ⟨index, ?_⟩
      change (goodEquiv.symm index).1 = target
      simp [index]
    windowData := windowData
    chain := chain
    heightLift := heightLift
    extraLoss := extraLoss
    extraCost_power := fun index => hextra (chain index) }
  exact ⟨⟨good, rfl⟩⟩

namespace PureWZ2ReentrantTerminalDependentReceipts

/-- Construct the exact terminal directly with the fixed scheduled extra
loss.  This deliberately bypasses the older runtime receipt, whose final
absorption quantified over the freely stored `good.extraLoss`. -/
theorem toExactTerminal
    {sigma inputLoss delta outputLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalKernelSchedule
      capability sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {invocation : PureWZ2ReentrantTerminalKernelInvocation
      (schedule := schedule) current}
    (hinput : 0 < inputLoss)
    (hinputCeiling : inputLoss ≤ schedule.sourceLossCeiling)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ schedule.delta₀)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (receipts : PureWZ2ReentrantTerminalDependentReceipts invocation) :
    Nonempty (PureWZ2ExactTerminalLevelData
      current.grain outputLoss) := by
  let owner := receipts.owner.toOwner
  let terminal := owner.toTerminalScaleStickyData
  have hCOne : (1 : ENNReal) ≤
      10 * Kakeya.realRpowENN delta (-inputLoss) := by
    have hpower : (1 : ENNReal) ≤
        Kakeya.realRpowENN delta (-inputLoss) := by
      rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num,
        Kakeya.realRpowENN]
      exact ENNReal.ofReal_mono
        (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta
          (hdeltaSmall.trans schedule.delta₀_le_one) (by linarith))
    exact hpower.trans (le_mul_of_one_le_left' (by norm_num))
  rcases terminal.prepareSource with ⟨terminalSource⟩
  rcases terminalSource.toLemma23Prepared hbridge with ⟨prepared⟩
  have hgood := pureWZ2GoodTerminalBlocks_nonempty prepared
  have hdeltaTerminal : delta ≤ schedule.terminal.delta₀ :=
    hdeltaSmall.trans schedule.delta₀_terminal
  let budget := schedule.terminal.budget inputLoss delta hinput
    (hinputCeiling.trans schedule.sourceLossCeiling_terminal) hdelta
    hdeltaTerminal
  have chainFor : ∀ {block : ℤ}
      (windowData : PureWZ2TerminalBlockWindowData prepared block),
        Nonempty (PureWZ2TerminalWindowChainOutput
          (eta := schedule.terminal.eta)
          (theoremEta := schedule.terminal.theoremEta)
          (outputLoss := schedule.terminal.workingLoss) windowData.window) := by
    intro block windowData
    have hvolume : ∀
        {line : PureWZ2HorizontalFixedLineCore
          windowData.window.windowed current.grain.globalGrains.slope}
        {parents : PureWZ2TerminalFixedLineParentData line}
        {selection : PureWZ2TerminalBinParentYSelection parents}
        {residue : PureWZ2TerminalBinParentYResidueData selection}
        {retained : PureWZ2TerminalBinRetainedShadingData residue}
        {sources : PureWZ2TerminalBinSourceFamily retained}
        {band : PureWZ2TerminalBinFixedBandSelection sources}
        {phase : PureWZ2TerminalBinHeightPhaseSelection band}
        {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
        (prep : PureWZ2TerminalExactGraphPreparation anchored),
          Kakeya.realRpowENN delta
              (1 + sigma / 2 + schedule.terminal.volumeLoss) ≤
            MeasureTheory.volume prep.shadow.union := by
      intro line parents selection residue retained sources band phase anchored prep
      exact PureWZ2TerminalExactGraphPreparation.power_volume_lower_of_schedule
        prep windowData.minimum_supply
        (schedule.terminal.volume_budget inputLoss delta hinput
          (hinputCeiling.trans schedule.sourceLossCeiling_terminal) hdelta
          hdeltaTerminal)
    exact pureWZ2_terminal_window_chain_of_numerical_certificates
      windowData.window hbridge budget hCOne
      (schedule.terminal.c_real inputLoss delta hinput
        (hinputCeiling.trans schedule.sourceLossCeiling_terminal) hdelta
        hdeltaTerminal) hvolume
      (fun preparedGraph => schedule.terminal.extra preparedGraph hdelta
        hdeltaTerminal)
      (schedule.terminal.edge delta hdelta hdeltaTerminal)
      (schedule.terminal.refined_edge delta hdelta hdeltaTerminal)
      (schedule.terminal.katz delta hdelta hdeltaTerminal)
      (schedule.terminal.refined_katz delta hdelta hdeltaTerminal)
      (by
        intro line parents selection residue retained sources band phase anchored
          prep graphParents localCells preparedGraph sharp first ready
        exact schedule.terminal.alternativeA ready hinput.le
          (hinputCeiling.trans schedule.sourceLossCeiling_terminal)
          hdeltaTerminal)
  rcases prepared.buildExactGoodBlockFamilyOfWindowChains chainFor
      (fun chain => schedule.terminal.extra chain.preparedGraph hdelta
        hdeltaTerminal)
      hgood with ⟨⟨good, hgoodExtra⟩⟩
  rcases good.selectResidue with ⟨data⟩
  have hfinal :
      64 * pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
          pureWZ2TerminalExactHeightRetentionCost delta good.extraLoss *
          Kakeya.realRpowENN delta
            (sigma + schedule.terminal.workingLoss) ≤
        MeasureTheory.volume prepared.shadow.union *
          terminal.sticky.balanced.cellMass *
          pureWZ2TerminalExactRichFloor
            delta schedule.terminal.workingLoss := by
    exact receipts.finalMass.absorb prepared hgoodExtra
  have hinputWorking : inputLoss ≤ schedule.terminal.workingLoss :=
    hinputCeiling.trans <| schedule.sourceLossCeiling_terminal.trans <|
      schedule.terminal.sourceLossCeiling_working.trans <|
        div_le_self schedule.terminal.workingLoss_pos.le (by norm_num)
  rcases data.toLiftedExactTerminalLevelOfBudget hinputWorking hfinal with
    ⟨workingTerminal⟩
  exact ⟨workingTerminal.mono_loss
    schedule.terminal.workingLoss_le_output⟩

end PureWZ2ReentrantTerminalDependentReceipts

/-- The remaining dependent producer returns one construction-dependent
actual-owner invocation together with its final terminal receipts. -/
def PureWZ2ReentrantTerminalDependentLeavesAt
    (capability : PureWZ2PropStickyCapability)
    (sigma : ℝ) : Prop :=
  ∀ outputLoss : ℝ,
    ∀ schedule : PureWZ2ReentrantTerminalKernelSchedule
      capability sigma outputLoss,
      ∀ inputLoss : ℝ,
        0 < inputLoss → inputLoss ≤ schedule.sourceLossCeiling →
        ∀ delta : ℝ, 0 < delta → delta ≤ schedule.delta₀ →
          ∀ current : PureWZ2ReentrantGrainSource sigma inputLoss delta
              capability.normalizationExponent,
            Nonempty (Sigma fun invocation :
              PureWZ2ReentrantTerminalKernelInvocation
                (schedule := schedule) current =>
              PureWZ2ReentrantTerminalDependentReceipts invocation)

/-- Kernel invocation plus the two narrow dependent receipts imply the
exact terminal statement directly, without the over-quantified historical
runtime receipt. -/
theorem pureWZ2_reentrantExactTerminalScaleAt_of_dependentLeaves
    (capability : PureWZ2PropStickyCapability)
    {sigma : ℝ} (critical : PureWZ2CriticalPackage sigma)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (leaves : PureWZ2ReentrantTerminalDependentLeavesAt capability sigma) :
    PureWZ2ReentrantExactTerminalScaleAtStatement
      sigma capability.normalizationExponent := by
  intro outputLoss hsigma hsigmaOne houtput
  rcases pureWZ2_reentrantTerminal_kernelSchedule capability critical
      hsigma hsigmaOne houtput with ⟨schedule⟩
  refine ⟨schedule.sourceLossCeiling, schedule.delta₀,
    schedule.sourceLossCeiling_pos, ?_, schedule.delta₀_pos,
    schedule.delta₀_le_one, ?_⟩
  · exact schedule.sourceLossCeiling_terminal.trans <|
      schedule.terminal.sourceLossCeiling_working.trans <|
        div_le_div_of_nonneg_right
          schedule.terminal.workingLoss_le_output (by norm_num)
  · intro inputLoss hinput hinputSchedule delta hdelta hdeltaSchedule current
    rcases leaves outputLoss schedule inputLoss hinput hinputSchedule delta
        hdelta hdeltaSchedule current with ⟨⟨invocation, receipts⟩⟩
    exact receipts.toExactTerminal hinput hinputSchedule hdelta hdeltaSchedule
      hbridge

end Kakeya.Assouad

end
