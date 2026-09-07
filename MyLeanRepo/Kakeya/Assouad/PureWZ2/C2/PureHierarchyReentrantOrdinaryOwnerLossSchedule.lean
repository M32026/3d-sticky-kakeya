import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantOrdinaryOwnerFrontEnd
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryOneScaleSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryWeightedTerminalSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinProductionScalar
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerUniversalWitnessProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PostDeletionFixedBalancingInput
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PostDeletionReentrantScaleThresholds
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.BoundedSourceCardLog

/-!
# Pre-runtime loss schedule for the re-entrant ordinary owner

The trace/scalar/final-floor ledger, rich loss, analytic thresholds, normal
parameter, and owner loss are selected first.  The exact Node-4 re-entry
capability then selects its same-extremizer input loss, after which the sticky
loss is chosen below that input loss.  Only then are the kernel and common
runtime cutoffs constructed.  Thus none of these choices depends on a runtime
source, family, shading, or scale.

No unrelated geometric capability is introduced in this module.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Family-independent loss and scale data required by the genuine
post-deletion fixed-balancing input.  Both losses and every cutoff are chosen
before the runtime source family. -/
structure PureWZ2OrdinaryPostDeletionFixedBalancingThresholds
    (internalLossCeiling publicLoss : ℝ) where
  selectionLoss : ℝ
  selectionLoss_pos : 0 < selectionLoss
  combinedLoss_eq :
    internalLossCeiling + selectionLoss = publicLoss / 32
  sourcePublicGap :
    16 * (internalLossCeiling + selectionLoss) < publicLoss
  numerical :
    WZ2PaperFinalGeometricNumericalData
      (internalLossCeiling + selectionLoss) publicLoss publicLoss 0 0
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_numerical : delta₀ ≤ numerical.delta₀
  delta₀_final : delta₀ ≤ pureWZ2PostDeletionFinalBalancingScale
  delta₀_le_twenty_four : delta₀ ≤ 1 / 24
  periodic_scale :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      50 * delta ≤ Real.rpow delta (1 - publicLoss)

/-- Choose the balancing loss from genuine room between the outer public loss
and the internal-loss ceiling, then select all uniform balancing cutoffs. -/
theorem pureWZ2_ordinaryPostDeletion_fixedBalancingThresholds
    {internalLossCeiling publicLoss : ℝ}
    (internalLossCeiling_pos : 0 < internalLossCeiling)
    (publicLoss_pos : 0 < publicLoss)
    (internalLossCeiling_lt : internalLossCeiling < publicLoss / 32) :
    Nonempty
      (PureWZ2OrdinaryPostDeletionFixedBalancingThresholds
        internalLossCeiling publicLoss) := by
  let selectionLoss := publicLoss / 32 - internalLossCeiling
  have selectionLoss_pos : 0 < selectionLoss := by
    dsimp only [selectionLoss]
    exact sub_pos.mpr internalLossCeiling_lt
  have combinedLoss_eq :
      internalLossCeiling + selectionLoss = publicLoss / 32 := by
    dsimp only [selectionLoss]
    ring
  have sourcePublicGap :
      16 * (internalLossCeiling + selectionLoss) < publicLoss := by
    rw [combinedLoss_eq]
    linarith
  rcases
      pureWZ2_postDeletion_fixed_balancing_input_uniform_scales
        internalLossCeiling selectionLoss publicLoss
        internalLossCeiling_pos selectionLoss_pos publicLoss_pos
        sourcePublicGap
    with
    ⟨numerical, delta₀, delta₀_pos, delta₀_le_one, delta₀_numerical,
      delta₀_final, delta₀_le_twenty_four, periodic_scale⟩
  exact
    ⟨{
      selectionLoss := selectionLoss
      selectionLoss_pos := selectionLoss_pos
      combinedLoss_eq := combinedLoss_eq
      sourcePublicGap := sourcePublicGap
      numerical := numerical
      delta₀ := delta₀
      delta₀_pos := delta₀_pos
      delta₀_le_one := delta₀_le_one
      delta₀_numerical := delta₀_numerical
      delta₀_final := delta₀_final
      delta₀_le_twenty_four := delta₀_le_twenty_four
      periodic_scale := fun {delta} hdelta hdeltaSmall =>
        periodic_scale delta hdelta hdeltaSmall
    }⟩

/-- Fixed color-vector and dyadic-band coefficient in the two-coordinate
ordinary caller-weight preselection. -/
def pureWZ2OrdinaryPostDeletionPreselectionCoefficient : ENNReal :=
  ((pureWZ2CallerCenterUniformConflictDegree + 1 : ℕ) : ENNReal) ^ 2 * 8

/-- Family-independent coefficient after multiplying quotient conflict,
caller-weight preselection, and complete-parent regularization. -/
def pureWZ2OrdinaryPostDeletionPreselectionLossCoefficient : ENNReal :=
  (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
    pureWZ2OrdinaryPostDeletionPreselectionCoefficient * 8

/-- Common logarithmic envelope for the caller and actual-parent
cardinalities. -/
def pureWZ2OrdinaryPostDeletionPreselectionEnvelope
    (delta : ℝ) : ENNReal :=
  ENNReal.ofReal
    (pureWZ2BoundedSourceCardLogConstant *
      (1 + Real.log delta⁻¹))

theorem pureWZ2OrdinaryPostDeletionPreselectionLossCoefficient_ne_top :
    pureWZ2OrdinaryPostDeletionPreselectionLossCoefficient ≠ ⊤ := by
  unfold pureWZ2OrdinaryPostDeletionPreselectionLossCoefficient
    pureWZ2OrdinaryPostDeletionPreselectionCoefficient
  exact
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.pow_ne_top ENNReal.coe_ne_top) (by norm_num)))
      (by norm_num)

/-- The source-independent cutoff that absorbs the exact `log^3 * log^3`
preselection and complete-parent loss. -/
structure PureWZ2OrdinaryPostDeletionPreselectionThresholds
    (selectionLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorption :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      Kakeya.realRpowENN delta selectionLoss *
          (pureWZ2OrdinaryPostDeletionPreselectionLossCoefficient *
            pureWZ2OrdinaryPostDeletionPreselectionEnvelope delta ^ 6) ≤
        1

theorem pureWZ2_ordinaryPostDeletion_preselectionThresholds
    {selectionLoss : ℝ}
    (selectionLoss_pos : 0 < selectionLoss) :
    Nonempty
      (PureWZ2OrdinaryPostDeletionPreselectionThresholds selectionLoss) := by
  have logCoefficient_nonneg :
      0 ≤ pureWZ2BoundedSourceCardLogConstant := by
    unfold pureWZ2BoundedSourceCardLogConstant
    exact le_max_of_le_right <|
      div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le
  rcases
      exists_delta_C_pow_log_absorbed_ennreal
        pureWZ2OrdinaryPostDeletionPreselectionLossCoefficient
        pureWZ2OrdinaryPostDeletionPreselectionLossCoefficient_ne_top
        pureWZ2BoundedSourceCardLogConstant logCoefficient_nonneg
        selectionLoss_pos (show 0 < (6 : ℕ) by norm_num)
    with
    ⟨delta₀, delta₀_pos, delta₀_le_one, absorbed⟩
  refine
    ⟨{
      delta₀ := delta₀
      delta₀_pos := delta₀_pos
      delta₀_le_one := delta₀_le_one
      absorption := ?_
    }⟩
  intro delta hdelta hdeltaSmall
  have hbound :
      pureWZ2OrdinaryPostDeletionPreselectionLossCoefficient *
          pureWZ2OrdinaryPostDeletionPreselectionEnvelope delta ^ 6 ≤
        Kakeya.realRpowENN delta (-selectionLoss) := by
    simpa only [pureWZ2OrdinaryPostDeletionPreselectionEnvelope] using
      absorbed delta hdelta hdeltaSmall
  calc
    Kakeya.realRpowENN delta selectionLoss *
          (pureWZ2OrdinaryPostDeletionPreselectionLossCoefficient *
            pureWZ2OrdinaryPostDeletionPreselectionEnvelope delta ^ 6) ≤
        Kakeya.realRpowENN delta selectionLoss *
          Kakeya.realRpowENN delta (-selectionLoss) := by
      gcongr
    _ = 1 := by
      rw [← realRpowENN_add hdelta]
      simp [Kakeya.realRpowENN]

/-- Formula receipt retained by the genuine uniform two-coordinate
preselection constructor.  The generic preselection record alone does not
determine the cardinality of its color type. -/
structure PureWZ2OrdinaryPostDeletionUniformPreselectionData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    {actualRequested :
      WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (scales : Fin 2 → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant) where
  data :
    PureWZ2PostDeletionCallerWeightPreselectionData
      quotient 2 scales scheduled
  retentionConstant_eq :
    data.retentionConstant =
      pureWZ2OrdinaryPostDeletionPreselectionCoefficient *
        (Nat.log 2
          (2 * (pureWZ2PostDeletionPositiveCallerBase quotient).family.card) +
          1 : ENNReal) ^ 3

/-- Construct the ordinary formula receipt together with the genuine uniform
preselection, before any complete-parent regularization. -/
theorem pureWZ2_ordinaryPostDeletion_uniform_preselection
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (fineNonempty : fine.Nonempty)
    (fineBoundedBase : HasBoundedBase fine 4)
    (selectedMassPos : 0 < quotient.selectedShading.mass)
    (scales : Fin 2 → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant) :
    Nonempty
      (PureWZ2OrdinaryPostDeletionUniformPreselectionData
        quotient scales scheduled) := by
  let callerBase := pureWZ2PostDeletionPositiveCallerBase quotient
  let Color : Fin 2 → Type :=
    fun _ => Fin (pureWZ2CallerCenterUniformConflictDegree + 1)
  let coloring :
      ∀ coordinate,
        PureWZ2CallerCenterEnvelopeColoringData
          quotient (scheduled coordinate) callerBase
          (Color coordinate) :=
    fun coordinate =>
      Classical.choice <| by
        simpa only [Color] using
          (pureWZ2_caller_center_envelope_uniform_coloring
            quotient (scheduled coordinate) callerBase
            fineNonempty fineBoundedBase)
  let selection :
      PureWZ2FiniteCallerCenterSelectionData
        quotient callerBase 2 scales scheduled Color coloring
        (pureWZ2PostDeletionPositiveCallerWeight quotient) :=
    Classical.choice <|
      pureWZ2_finite_caller_center_selection
        quotient callerBase 2 (by norm_num) scales scheduled
        Color coloring (pureWZ2PostDeletionPositiveCallerWeight quotient)
  have totalWeightEq :
      (∑ parent : Fin callerBase.family.card,
          pureWZ2PostDeletionPositiveCallerWeight quotient parent) =
        quotient.selectedShading.mass := by
    change
      (∑ parent :
          Fin (quotient.callerCover.hitParentSubfamily
            quotient.positiveCallerFine).family.card,
        quotient.callerActualWeight
          ((quotient.callerCover.hitParentSubfamily
            quotient.positiveCallerFine).embedding parent)) =
        quotient.selectedShading.mass
    exact quotient.sum_positive_hitParent_weight
  have selectedNonempty : selection.selected.family.Nonempty := by
    by_contra hempty
    have selectedSumZero :
        (∑ parent : Fin selection.selected.family.card,
          pureWZ2PostDeletionPositiveCallerWeight quotient
            (selection.selected.embedding parent)) = 0 := by
      apply Finset.sum_eq_zero
      intro parent _
      exact Fin.elim0 (Nat.eq_zero_of_not_pos hempty ▸ parent)
    have retained := selection.retained_weight
    rw [selectedSumZero, mul_zero, totalWeightEq] at retained
    exact (not_le_of_gt selectedMassPos) retained
  letI colorFintype : ∀ coordinate, Fintype (Color coordinate) :=
    fun _ => inferInstance
  letI colorDecidableEq :
      ∀ coordinate, DecidableEq (Color coordinate) :=
    fun _ => inferInstance
  letI colorNonempty : ∀ coordinate, Nonempty (Color coordinate) :=
    fun _ => inferInstance
  let data :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient 2 scales scheduled :=
    {
      Color := Color
      colorFintype := colorFintype
      colorDecidableEq := colorDecidableEq
      colorNonempty := colorNonempty
      coloring := coloring
      selection := selection
      selected := selection.selected
      selected_eq := rfl
      selected_nonempty := selectedNonempty
      retentionConstant := selection.retentionConstant
      retentionConstant_eq := rfl
      retained_weight := selection.retained_weight
      weightLevel := selection.weightLevel
      weightLevel_pos := selection.weightLevel_pos
      weight_band := selection.weight_band
      total_weight_eq := by
        simpa [callerBase] using totalWeightEq
    }
  refine ⟨{ data := data, retentionConstant_eq := ?_ }⟩
  rw [data.retentionConstant_eq, selection.retentionConstant_eq]
  unfold pureWZ2FiniteCallerCenterRetentionConstant
    pureWZ2OrdinaryPostDeletionPreselectionCoefficient
  simp only [Color, Fintype.card_pi, Fintype.card_fin]
  norm_num
  ring

/-- Extension of the existing ordinary owner schedule by the analytic owner
losses and cutoffs which must be fixed before the runtime source.  The
production schedule contains no arbitrary-extremizer grain callback. -/
structure PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule
    (capability : PureWZ2PropStickyCapability)
    (sigma outputLoss sourceLossCeiling : ℝ) where
  paperADBridge : PureWZ2PaperADBridgeStatement
  sigma_lt_one : sigma < 1
  middleLoss : ℝ
  middleLoss_pos : 0 < middleLoss
  ownerSchedule : PureWZ2HierarchyReentrantOrdinaryOwnerSchedule capability
    sigma outputLoss sourceLossCeiling
  stickyLoss_le_middle : ownerSchedule.stickyLoss ≤ middleLoss
  normalEta : ℝ
  normalEta_pos : 0 < normalEta
  normalEta_sigma : 8 * normalEta < sigma
  middleLoss_lt_normal : middleLoss < normalEta
  middleLoss_projection :
    middleLoss < (1 / 2 : ℝ) * ownerSchedule.projection.sourceCostLossCeiling
  middleLoss_constant :
    middleLoss < ownerSchedule.analytic.base.budget.constantLoss
  stickyLoss_normal : 3 * ownerSchedule.stickyLoss / 2 < normalEta
  sourceLoss_core :
    sourceLossCeiling < ownerSchedule.stickyLoss * normalEta
  sourceLoss_density :
    sourceLossCeiling ≤ ownerSchedule.finalFloorSchedule.densityLoss / 64
  normalEta_density :
    normalEta ≤ ownerSchedule.finalFloorSchedule.densityLoss / 64
  middleLoss_density :
    middleLoss ≤ ownerSchedule.finalFloorSchedule.densityLoss / 64
  stickyLoss_density :
    ownerSchedule.stickyLoss ≤
      ownerSchedule.finalFloorSchedule.densityLoss / 64
  fixedBalancing :
    PureWZ2OrdinaryPostDeletionFixedBalancingThresholds
      sourceLossCeiling ownerSchedule.stickyLoss
  postDeletionThresholds :
    PureWZ2PostDeletionReentrantScaleThresholds
      sourceLossCeiling ownerSchedule.stickyLoss
  preselectionThresholds :
    PureWZ2OrdinaryPostDeletionPreselectionThresholds
      fixedBalancing.selectionLoss
  graphOuterLoss : ℝ
  graphOuterLoss_pos : 0 < graphOuterLoss
  commonBinScalar :
    PureWZ2SourceHeavyCommonBinScalarThreshold sigma
      (2 * sourceLossCeiling + middleLoss) middleLoss
      ownerSchedule.stickyLoss ownerSchedule.jointVolumeLoss outputLoss
  core : PureWZ2OrdinaryCoreThreshold sigma sourceLossCeiling middleLoss
    ownerSchedule.stickyLoss normalEta ownerSchedule.stickyLoss
    capability.logExponent
  geometric : PureWZ2SourceHorizontalGeometricThreshold
    sigma normalEta ownerSchedule.richLoss
  weightedTerminal : PureWZ2OrdinaryWeightedTerminalSchedule sigma middleLoss
    ownerSchedule.stickyLoss ownerSchedule.richLoss normalEta
  projectionRho₀ : ℝ
  projectionRho₀_pos : 0 < projectionRho₀
  projectionRho₀_le_one : projectionRho₀ ≤ 1
  projectionSourceCost :
    ∀ {middleLoss' rho : ℝ},
      0 ≤ middleLoss' → middleLoss' ≤ middleLoss →
      0 < rho → rho ≤ projectionRho₀ →
        Kakeya.realRpowENN rho (-middleLoss') ≤
          Kakeya.realRpowENN (wz1Lemma23Theorem22Scale (256 * rho))
            (-ownerSchedule.projection.sourceCostLossCeiling)
  constantRho₀ : ℝ
  constantRho₀_pos : 0 < constantRho₀
  constantRho₀_le_one : constantRho₀ ≤ 1
  constantPower :
    ∀ {middleLoss' rho : ℝ},
      0 ≤ middleLoss' → middleLoss' ≤ middleLoss →
      0 < rho → rho ≤ constantRho₀ →
        (10 * Kakeya.realRpowENN rho (-middleLoss')).toReal ≤
          Real.rpow (256 * rho)
            (-ownerSchedule.analytic.base.budget.constantLoss)
  heightRho₀ : ℝ
  heightRho₀_pos : 0 < heightRho₀
  heightRho₀_le_one : heightRho₀ ≤ 1
  heightCostAbsorption :
    ∀ rho : ℝ, 0 < rho → rho ≤ heightRho₀ →
      512 * pureWZ2OrdinaryPaperOrderWindowHeightCost rho *
          Kakeya.realRpowENN rho ownerSchedule.richLoss ≤
        pureWZ2SourceHorizontalRichFloor rho ownerSchedule.richLoss
  localConstantDelta₀ : ℝ
  localConstantDelta₀_pos : 0 < localConstantDelta₀
  localConstantDelta₀_le_one : localConstantDelta₀ ≤ 1
  localConstant :
    ∀ {inputLoss' delta rho : ℝ},
      0 < inputLoss' → inputLoss' ≤ sourceLossCeiling →
      0 < delta → delta ≤ localConstantDelta₀ →
      0 < rho → rho ≤ 1 → rho ≤ Real.rpow delta outputLoss →
        35 * (10 * Kakeya.realRpowENN delta (-inputLoss')) ≤
          19 * (10 * Kakeya.realRpowENN rho (-middleLoss))
  densityDelta₀ : ℝ
  densityDelta₀_pos : 0 < densityDelta₀
  densityDelta₀_le_one : densityDelta₀ ≤ 1
  densityPower :
    ∀ delta : ℝ, 0 < delta → delta ≤ densityDelta₀ →
      (10 : ENNReal) * Kakeya.realRpowENN delta
          (ownerSchedule.finalFloorSchedule.densityLoss / 2) ≤ 1
  runtimeRho₀ : ℝ
  runtimeRho₀_pos : 0 < runtimeRho₀
  runtimeRho₀_le_core : runtimeRho₀ ≤ core.rho₀
  runtimeRho₀_le_geometric : runtimeRho₀ ≤ geometric.rho0
  runtimeRho₀_le_projection : runtimeRho₀ ≤ projectionRho₀
  runtimeRho₀_le_constant : runtimeRho₀ ≤ constantRho₀
  runtimeRho₀_le_analytic : runtimeRho₀ ≤ ownerSchedule.analytic.rho₀
  runtimeRho₀_le_projectionThreshold :
    runtimeRho₀ ≤ ownerSchedule.projection.rho₀
  runtimeRho₀_le_height : runtimeRho₀ ≤ heightRho₀
  runtimeRho₀_le_weightedTerminal : runtimeRho₀ ≤ weightedTerminal.rho₀
  runtimeRho₀_le_graphOuter :
    runtimeRho₀ ≤
      Classical.choose
        (pureWZ2_sourceWindowHeightBins_power_schedule
          (extraLoss := graphOuterLoss) graphOuterLoss_pos)
  scalarDelta₀ : ℝ
  scalarDelta₀_pos : 0 < scalarDelta₀
  scalarDelta₀_le_one : scalarDelta₀ ≤ 1
  scalarDelta₀_le_owner : scalarDelta₀ ≤ ownerSchedule.delta₀
  ownerThresholds : SameFamilyOwnerUniformScalarThresholds sigma
    ownerSchedule.stickyLoss
  scalarDelta₀_le_ownerThresholds :
    scalarDelta₀ ≤ ownerThresholds.delta₀
  scalarDelta₀_le_core : scalarDelta₀ ≤ core.delta₀
  scalarDelta₀_density : scalarDelta₀ ≤ densityDelta₀
  scalarDelta₀_localConstant : scalarDelta₀ ≤ localConstantDelta₀
  scalarDelta₀_commonBin :
    scalarDelta₀ ≤ commonBinScalar.delta₀
  scalarDelta₀_fixedBalancing :
    scalarDelta₀ ≤ fixedBalancing.delta₀
  scalarDelta₀_postDeletion :
    scalarDelta₀ ≤ postDeletionThresholds.delta₀
  scalarDelta₀_preselection :
    scalarDelta₀ ≤ preselectionThresholds.delta₀
  targetRho_small :
    ∀ {delta targetRho : ℝ},
      0 < delta → delta ≤ scalarDelta₀ → delta ≤ targetRho →
      targetRho ≤ Real.rpow delta outputLoss →
        pureWZ2SourceHorizontalInternalScale targetRho ≤ runtimeRho₀

namespace PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss sourceLossCeiling : ℝ}

/-- Projection to the pre-existing schedule consumed by the runtime kernel
and scalar closure. -/
abbrev toOwnerSchedule
    (schedule : PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability
      sigma outputLoss sourceLossCeiling) :=
  schedule.ownerSchedule

@[simp] theorem toOwnerSchedule_stickyLoss
    (schedule : PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability
      sigma outputLoss sourceLossCeiling) :
    schedule.toOwnerSchedule.stickyLoss =
      schedule.ownerSchedule.stickyLoss := rfl

/-- Collect the exact family-independent hypotheses used when the ordinary
post-deletion leaf invokes the fixed-balancing constructor. -/
theorem fixedBalancing_input_scalars
    (schedule : PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability
      sigma outputLoss sourceLossCeiling)
    {inputLoss delta : ℝ}
    (hinputCeiling : inputLoss ≤ sourceLossCeiling)
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ schedule.scalarDelta₀)
    (callerRequested : WZ2PaperRequestedScale delta)
    (callerLower :
      Real.rpow delta
          (1 - schedule.ownerSchedule.stickyLoss) ≤ callerRequested.1) :
    0 < schedule.fixedBalancing.selectionLoss ∧
      16 * (inputLoss + schedule.fixedBalancing.selectionLoss) <
        schedule.ownerSchedule.stickyLoss ∧
      delta ≤ 1 / 24 ∧
      50 * delta ≤ callerRequested.1 ∧
      delta ≤ schedule.fixedBalancing.numerical.delta₀ ∧
      delta ≤ pureWZ2PostDeletionFinalBalancingScale := by
  have hbalancing :
      delta ≤ schedule.fixedBalancing.delta₀ :=
    hdeltaSmall.trans schedule.scalarDelta₀_fixedBalancing
  refine
    ⟨schedule.fixedBalancing.selectionLoss_pos, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      (mul_le_mul_of_nonneg_left
        (by
          simpa [add_comm] using
            add_le_add_right hinputCeiling
              schedule.fixedBalancing.selectionLoss)
        (by norm_num)).trans_lt
        schedule.fixedBalancing.sourcePublicGap
  · exact hbalancing.trans schedule.fixedBalancing.delta₀_le_twenty_four
  · exact
      (schedule.fixedBalancing.periodic_scale hdelta hbalancing).trans
        callerLower
  · exact hbalancing.trans schedule.fixedBalancing.delta₀_numerical
  · exact hbalancing.trans schedule.fixedBalancing.delta₀_final

/-- The minimum actual request used by the ordinary post-deletion
construction.  It is fixed by the runtime scale and introduces no additional
choice or hypothesis. -/
noncomputable def postDeletionActualRequested
    (schedule : PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability
      sigma outputLoss sourceLossCeiling)
    {inputLoss delta : ℝ}
    (_current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent)
    (hdeltaSmall : delta ≤ schedule.scalarDelta₀) :
    WZ2PaperRequestedScale delta :=
  ⟨delta, le_rfl, hdeltaSmall.trans schedule.scalarDelta₀_le_one⟩

/-- Fixed-runtime actual-to-caller estimate for the exact current
normalization.  The first inequality uses the loss-gap threshold, while the
second is the caller's ordinary sticky-loss lower window. -/
theorem postDeletion_actual_to_caller
    (schedule : PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability
      sigma outputLoss sourceLossCeiling)
    {inputLoss delta : ℝ}
    (hinputCeiling : inputLoss ≤ sourceLossCeiling)
    (hdeltaSmall : delta ≤ schedule.scalarDelta₀)
    (current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent)
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        current.reentry.toNormalizationData.croppedFamily
        (schedule.postDeletionActualRequested current hdeltaSmall)
        (Kakeya.realRpowENN delta (-inputLoss)))
    (callerRequested : WZ2PaperRequestedScale delta)
    (callerLower :
      Real.rpow delta
          (1 - schedule.ownerSchedule.stickyLoss) ≤ callerRequested.1) :
    2400000 * actualNearby.rho ≤
        Real.rpow delta (1 - schedule.ownerSchedule.stickyLoss) ∧
      Real.rpow delta (1 - schedule.ownerSchedule.stickyLoss) ≤
        callerRequested.1 := by
  have hdelta : 0 < delta := current.grain.extremal.delta_pos
  have hpostDeletion :
      delta ≤ schedule.postDeletionThresholds.delta₀ :=
    hdeltaSmall.trans schedule.scalarDelta₀_postDeletion
  have nearbyWindow :
      ENNReal.ofReal actualNearby.rho <
        ENNReal.ofReal (Real.rpow delta (1 - inputLoss)) := by
    calc
      ENNReal.ofReal actualNearby.rho <
          Kakeya.realRpowENN delta (-inputLoss) *
            ENNReal.ofReal
              (schedule.postDeletionActualRequested
                current hdeltaSmall).1 :=
        actualNearby.within_factor
      _ =
          Kakeya.realRpowENN delta (-inputLoss) *
            ENNReal.ofReal delta := by
        rfl
      _ =
          ENNReal.ofReal (Real.rpow delta (1 - inputLoss)) :=
        pureWZ2_min_requested_window_identity hdelta
  have nearbyUpper :
      actualNearby.rho < Real.rpow delta (1 - inputLoss) :=
    (ENNReal.ofReal_lt_ofReal_iff
      (Real.rpow_pos_of_pos hdelta _)).mp nearbyWindow
  refine ⟨?_, callerLower⟩
  calc
    2400000 * actualNearby.rho ≤
        2400000 * Real.rpow delta (1 - inputLoss) := by
      gcongr
    _ ≤ Real.rpow delta
          (1 - schedule.ownerSchedule.stickyLoss) :=
      schedule.postDeletionThresholds.actual_to_caller_window
        hinputCeiling hdelta hpostDeletion

/-- Absorb the exact weight-preselection and complete-parent formulas for the
ordinary two-coordinate package.  Runtime cardinalities occur only in this
application theorem, never in the pre-runtime schedule. -/
theorem postDeletion_preselection_absorption
    (schedule : PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability
      sigma outputLoss sourceLossCeiling)
    {inputLoss delta : ℝ}
    (hdeltaSmall : delta ≤ schedule.scalarDelta₀)
    (current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent)
    {actualRequested callerRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        current.reentry.toNormalizationData.croppedFamily actualRequested
        (Kakeya.realRpowENN delta (-inputLoss)))
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested
        current.reentry.toNormalizationData.croppedRefined)
    (scales : Fin 2 → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          current.reentry.toNormalizationData.croppedFamily
          (scales coordinate)
          (Kakeya.realRpowENN delta (-inputLoss)))
    (preselection :
      PureWZ2OrdinaryPostDeletionUniformPreselectionData
        quotient scales scheduled) :
    Kakeya.realRpowENN delta
          schedule.fixedBalancing.selectionLoss *
        ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          preselection.data.retentionConstant *
          pureWZ2CompleteParentRegularizationLoss
            actualNearby.scaleData.coarse.card 2) ≤
      1 := by
  let normalized := current.reentry.toNormalizationData
  let envelope :=
    pureWZ2OrdinaryPostDeletionPreselectionEnvelope delta
  have hdelta : 0 < delta := current.grain.extremal.delta_pos
  have hdeltaOne : delta ≤ 1 :=
    hdeltaSmall.trans schedule.scalarDelta₀_le_one
  have hpreselectionSmall :
      delta ≤ schedule.preselectionThresholds.delta₀ :=
    hdeltaSmall.trans schedule.scalarDelta₀_preselection
  have ambientLogBound :
      (Nat.log 2 (2 * normalized.croppedFamily.card) + 1 : ENNReal) ≤
        envelope := by
    have rawCard :=
      pureWZ2_bounded_source_card_le hdelta
        normalized.final_extremal.cwa_nearby_scales.2.2.1
        normalized.ordinary_bounded_base
    have rawLog :=
      pureWZ2_bounded_source_card_log_bound
        hdelta hdeltaOne normalized.final_extremal.nonempty rawCard
    have converted := ENNReal.ofReal_mono rawLog
    have castEq :
        ENNReal.ofReal
            (Nat.log 2 (2 * normalized.croppedFamily.card) + 1 : ℝ) =
          (Nat.log 2 (2 * normalized.croppedFamily.card) + 1 :
            ENNReal) := by
      rw [ENNReal.ofReal_add (by positivity)]
      norm_num
      positivity
    rw [castEq] at converted
    simpa only [envelope,
      pureWZ2OrdinaryPostDeletionPreselectionEnvelope] using converted
  have actualCardLe :
      actualNearby.scaleData.coarse.card ≤ normalized.croppedFamily.card := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_surjective
        actualNearby.scaleData.cover.parent
        (actualNearby.scaleData.cover.parent_surjective_of_uniform
          actualNearby.scaleData.rho_pos.le
          normalized.final_extremal.nonempty
          actualNearby.scaleData.full_fiber_uniform)
  have callerBaseCardLe :
      (pureWZ2PostDeletionPositiveCallerBase quotient).family.card ≤
        normalized.croppedFamily.card := by
    have baseToCaller :
        (pureWZ2PostDeletionPositiveCallerBase quotient).family.card ≤
          quotient.callerCoarse.card := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective
          (pureWZ2PostDeletionPositiveCallerBase quotient).embedding
          (pureWZ2PostDeletionPositiveCallerBase quotient).embedding.injective
    have callerToSelected :
        quotient.callerCoarse.card ≤ quotient.selected.family.card := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_surjective
          quotient.section6Cover.toWZ1PaperTubeCover.parent
          quotient.section6Cover.toWZ1PaperTubeCover.parent_surjective
    have selectedToFine :
        quotient.selected.family.card ≤ normalized.croppedFamily.card := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective quotient.selected.embedding
          quotient.selected.embedding.injective
    exact baseToCaller.trans <| callerToSelected.trans selectedToFine
  have actualLogBound :
      (Nat.log 2 (2 * actualNearby.scaleData.coarse.card) + 1 : ENNReal) ≤
        envelope := by
    have natBound :
        Nat.log 2 (2 * actualNearby.scaleData.coarse.card) + 1 ≤
          Nat.log 2 (2 * normalized.croppedFamily.card) + 1 :=
      Nat.add_le_add_right
        (Nat.log_mono_right (Nat.mul_le_mul_left 2 actualCardLe)) 1
    exact
      (by exact_mod_cast natBound : (Nat.log 2
          (2 * actualNearby.scaleData.coarse.card) + 1 : ENNReal) ≤
        (Nat.log 2 (2 * normalized.croppedFamily.card) + 1 : ENNReal)).trans
        ambientLogBound
  have callerLogBound :
      (Nat.log 2
          (2 * (pureWZ2PostDeletionPositiveCallerBase quotient).family.card) +
          1 : ENNReal) ≤ envelope := by
    have natBound :
        Nat.log 2
              (2 *
                (pureWZ2PostDeletionPositiveCallerBase quotient).family.card) +
            1 ≤
          Nat.log 2 (2 * normalized.croppedFamily.card) + 1 :=
      Nat.add_le_add_right
        (Nat.log_mono_right
          (Nat.mul_le_mul_left 2 callerBaseCardLe)) 1
    exact
      (by exact_mod_cast natBound : (Nat.log 2
          (2 * (pureWZ2PostDeletionPositiveCallerBase quotient).family.card) +
          1 : ENNReal) ≤
        (Nat.log 2 (2 * normalized.croppedFamily.card) + 1 : ENNReal)).trans
        ambientLogBound
  have runtimeLossBound :
      (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            preselection.data.retentionConstant *
            pureWZ2CompleteParentRegularizationLoss
              actualNearby.scaleData.coarse.card 2 ≤
        pureWZ2OrdinaryPostDeletionPreselectionLossCoefficient *
          envelope ^ 6 := by
    rw [preselection.retentionConstant_eq]
    unfold pureWZ2CompleteParentRegularizationLoss
    norm_num
    calc
      (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            (pureWZ2OrdinaryPostDeletionPreselectionCoefficient *
              (Nat.log 2
                (2 *
                  (pureWZ2PostDeletionPositiveCallerBase quotient).family.card) +
                1 : ENNReal) ^ 3) *
            (8 *
              (Nat.log 2 (2 * actualNearby.scaleData.coarse.card) + 1 :
                ENNReal) ^ 3) ≤
          (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            (pureWZ2OrdinaryPostDeletionPreselectionCoefficient *
              envelope ^ 3) *
            (8 * envelope ^ 3) := by
        gcongr
      _ =
          pureWZ2OrdinaryPostDeletionPreselectionLossCoefficient *
            envelope ^ 6 := by
        unfold pureWZ2OrdinaryPostDeletionPreselectionLossCoefficient
        ring
  calc
    Kakeya.realRpowENN delta
          schedule.fixedBalancing.selectionLoss *
        ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          preselection.data.retentionConstant *
          pureWZ2CompleteParentRegularizationLoss
            actualNearby.scaleData.coarse.card 2) ≤
      Kakeya.realRpowENN delta
          schedule.fixedBalancing.selectionLoss *
        (pureWZ2OrdinaryPostDeletionPreselectionLossCoefficient *
          pureWZ2OrdinaryPostDeletionPreselectionEnvelope delta ^ 6) := by
      gcongr
    _ ≤ 1 :=
      schedule.preselectionThresholds.absorption
        hdelta hpreselectionSmall

end PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule

/-- The source-heavy common-bin powers fit inside the ordinary loss ledger.
This arithmetic is isolated from the dependent schedule constructor so that
the constructor remains within the default elaboration budget. -/
private theorem reentrantOrdinary_commonBinScalarThreshold
    {sigma sourceLossCeiling middleLoss stickyLoss jointVolumeLoss outputLoss
      extraLoss constantLoss theoremEta : ℝ}
    (hsourceLossCeiling : 0 < sourceLossCeiling)
    (hmiddle : 0 < middleLoss)
    (hsticky : 0 < stickyLoss)
    (hjointVolumeLoss : 0 < jointVolumeLoss)
    (houtput : 0 < outputLoss)
    (hsourceGraph :
      sourceLossCeiling ≤ outputLoss * middleLoss / 4)
    (hmiddleGraphScale :
      middleLoss ≤ outputLoss * jointVolumeLoss / 1024)
    (hmiddleGraphInverse :
      middleLoss ≤ jointVolumeLoss / (1024 * outputLoss))
    (hstickyHalf : stickyLoss ≤ middleLoss / 2)
    (hedge :
      8 * ((jointVolumeLoss + extraLoss) + constantLoss) < theoremEta)
    (hextra : 0 < extraLoss)
    (hconstant : 0 < constantLoss)
    (htheoremEtaSmall : theoremEta ≤ 1 / 100) :
    Nonempty (PureWZ2SourceHeavyCommonBinScalarThreshold sigma
      (2 * sourceLossCeiling + middleLoss) middleLoss stickyLoss
      jointVolumeLoss outputLoss) := by
  have hmiddleJointHalf : middleLoss < jointVolumeLoss / 2 := by
    by_cases houtputOne : outputLoss ≤ 1
    · have houtputJoint :
          outputLoss * jointVolumeLoss ≤ jointVolumeLoss := by
        calc
          outputLoss * jointVolumeLoss ≤ 1 * jointVolumeLoss :=
            mul_le_mul_of_nonneg_right houtputOne hjointVolumeLoss.le
          _ = jointVolumeLoss := one_mul _
      calc
        middleLoss ≤ outputLoss * jointVolumeLoss / 1024 :=
          hmiddleGraphScale
        _ ≤ jointVolumeLoss / 1024 := by gcongr
        _ < jointVolumeLoss / 2 := by
          simpa [div_eq_mul_inv] using
            (mul_lt_mul_of_pos_left
              (show (1 / 1024 : ℝ) < 1 / 2 by norm_num)
              hjointVolumeLoss)
    · have houtputOne' : 1 < outputLoss := lt_of_not_ge houtputOne
      have hscaledMiddle :
          middleLoss * (1024 * outputLoss) ≤ jointVolumeLoss :=
        (le_div_iff₀ (mul_pos (by norm_num) houtput)).mp
          hmiddleGraphInverse
      have hstrict :
          2 * middleLoss < middleLoss * (1024 * outputLoss) := by
        have hcoefficient : (2 : ℝ) < 1024 * outputLoss := by
          nlinarith only [houtputOne']
        simpa [mul_comm] using
          mul_lt_mul_of_pos_left hcoefficient hmiddle
      apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      simpa [mul_comm] using hstrict.trans_le hscaledMiddle
  have hgraphOuterGap :
      sourceLossCeiling < outputLoss * (jointVolumeLoss / 8) := by
    calc
      sourceLossCeiling ≤ outputLoss * middleLoss / 4 := hsourceGraph
      _ < outputLoss * (jointVolumeLoss / 2) / 4 := by gcongr
      _ = outputLoss * (jointVolumeLoss / 8) := by ring
  have hlegacyGraphGap :
      sourceLossCeiling + middleLoss <
        outputLoss *
          (jointVolumeLoss - jointVolumeLoss / 8 - middleLoss -
            5 * stickyLoss / 2) := by
    by_cases houtputOne : outputLoss ≤ 1
    · have houtputMiddle :
          outputLoss * middleLoss ≤ middleLoss :=
        by simpa using
          (mul_le_mul_of_nonneg_right houtputOne hmiddle.le)
      nlinarith only [hsourceGraph, hmiddleGraphScale, hstickyHalf,
        hjointVolumeLoss, houtput, houtputMiddle]
    · have houtputOne' : 1 < outputLoss := lt_of_not_ge houtputOne
      have hscaledMiddle :
          middleLoss * (1024 * outputLoss) ≤ jointVolumeLoss :=
        (le_div_iff₀ (mul_pos (by norm_num) houtput)).mp
          hmiddleGraphInverse
      have hmiddleLeOutputMiddle :
          middleLoss ≤ outputLoss * middleLoss := by
        calc
          middleLoss = 1 * middleLoss := by ring
          _ ≤ outputLoss * middleLoss :=
            mul_le_mul_of_nonneg_right houtputOne'.le hmiddle.le
      have hjointLeOutputJoint :
          jointVolumeLoss ≤ outputLoss * jointVolumeLoss := by
        calc
          jointVolumeLoss = 1 * jointVolumeLoss := by ring
          _ ≤ outputLoss * jointVolumeLoss :=
            mul_le_mul_of_nonneg_right houtputOne'.le
              hjointVolumeLoss.le
      nlinarith only [hsourceGraph, hscaledMiddle, hstickyHalf, houtput,
        hjointVolumeLoss, hmiddleLeOutputMiddle, hjointLeOutputJoint]
  have hcommonBinGraphGap :
      2 * sourceLossCeiling + middleLoss <
        outputLoss *
          (jointVolumeLoss - middleLoss - 5 * stickyLoss / 2) := by
    calc
      2 * sourceLossCeiling + middleLoss =
          (sourceLossCeiling + middleLoss) + sourceLossCeiling := by ring
      _ < outputLoss *
            (jointVolumeLoss - jointVolumeLoss / 8 - middleLoss -
              5 * stickyLoss / 2) +
          outputLoss * (jointVolumeLoss / 8) :=
        add_lt_add hlegacyGraphGap hgraphOuterGap
      _ = outputLoss *
          (jointVolumeLoss - middleLoss - 5 * stickyLoss / 2) := by ring
  have hjointHalf : jointVolumeLoss ≤ 1 / 2 := by
    have hjointEight : jointVolumeLoss < 8 * jointVolumeLoss := by
      simpa [one_mul] using
        mul_lt_mul_of_pos_right (show (1 : ℝ) < 8 by norm_num)
          hjointVolumeLoss
    have hbudget : 8 * jointVolumeLoss < theoremEta := by
      calc
        8 * jointVolumeLoss ≤
            8 * ((jointVolumeLoss + extraLoss) + constantLoss) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact (le_add_of_nonneg_right hextra.le).trans
            (le_add_of_nonneg_right hconstant.le)
        _ < theoremEta := hedge
    exact (hjointEight.trans hbudget).le.trans
      (htheoremEtaSmall.trans (by norm_num))
  have hcommonBinPopularGap :
      2 * sourceLossCeiling + middleLoss <
        outputLoss * (1 / 2 - stickyLoss - middleLoss) := by
    have hinner :
        jointVolumeLoss - middleLoss - 5 * stickyLoss / 2 ≤
          1 / 2 - stickyLoss - middleLoss := by
      nlinarith only [hjointHalf, hsticky.le]
    exact hcommonBinGraphGap.trans_le
      (mul_le_mul_of_nonneg_left hinner houtput.le)
  have hcommonBinSourceCost :
      0 ≤ 2 * sourceLossCeiling + middleLoss :=
    add_nonneg (mul_nonneg (by norm_num) hsourceLossCeiling.le) hmiddle.le
  exact pureWZ2_sourceHeavyCommonBin_scalar_threshold
    (sigma := sigma)
    (sourceCostCeiling := 2 * sourceLossCeiling + middleLoss)
    (coarseLossCeiling := middleLoss)
    (stickyLoss := stickyLoss)
    (volumeLoss := jointVolumeLoss)
    (scaleLoss := outputLoss)
    hcommonBinSourceCost hmiddle.le houtput hcommonBinPopularGap
      hcommonBinGraphGap

/-- Select the complete ordinary-owner loss schedule before any runtime
source.  The proof exposes the paper order: final floor and rich loss, analytic
thresholds and normal parameter, `middleLoss`, `stickyLoss`, and finally all
common runtime cutoffs.  Proposition 6.3 is not invoked here. -/
theorem pureWZ2_reentrantOrdinaryOwnerLossSchedule
    (paperADBridge : PureWZ2PaperADBridgeStatement)
    (capability : PureWZ2PropStickyCapability)
    {sigma outputLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (_hsigma : 0 < sigma) (_hsigmaOne : sigma < 1)
    (houtput : 0 < outputLoss) :
    Nonempty (Sigma fun sourceLossCeiling =>
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling) := by
  let structuralBudget := outputLoss / 2
  have hstructuralBudget : 0 < structuralBudget := by
    dsimp only [structuralBudget]
    positivity
  have hstructuralOutput : structuralBudget ≤ outputLoss := by
    dsimp only [structuralBudget]
    linarith
  rcases critical.reentryTraceFloorSchedule houtput hstructuralBudget
      hstructuralOutput with ⟨traceSchedule⟩
  rcases pureWZ2_reentrantOrdinary_scalarClosure traceSchedule le_rfl with
    ⟨scalarClosure⟩
  have hgrainLoss : 0 < scalarClosure.grainLoss := by
    rw [scalarClosure.grainLoss_eq]
    exact div_pos traceSchedule.densityLoss_pos (by norm_num)
  let finalStructuralBudget := min (scalarClosure.grainLoss / 2) (sigma / 2)
  have hfinalStructuralBudget : 0 < finalStructuralBudget := by
    dsimp only [finalStructuralBudget]
    exact lt_min (div_pos hgrainLoss (by norm_num))
      (div_pos _hsigma (by norm_num))
  have hfinalStructuralGrain :
      finalStructuralBudget ≤ scalarClosure.grainLoss := by
    exact (min_le_left _ _).trans (by linarith)
  rcases critical.reentryTraceFloorSchedule hgrainLoss
      hfinalStructuralBudget hfinalStructuralGrain with
    ⟨finalFloorSchedule⟩
  let richLoss := finalFloorSchedule.densityLoss / 4
  have hrichLoss : 0 < richLoss := by
    dsimp only [richLoss]
    exact div_pos finalFloorSchedule.densityLoss_pos (by norm_num)
  have hrichGrain : richLoss ≤ scalarClosure.grainLoss := by
    dsimp only [richLoss]
    exact (div_le_self finalFloorSchedule.densityLoss_pos.le
      (by norm_num)).trans finalFloorSchedule.densityLoss_le_floor
  have hrichHalfDensity :
      richLoss / 2 < finalFloorSchedule.densityLoss := by
    dsimp only [richLoss]
    linarith [finalFloorSchedule.densityLoss_pos]
  have hrichSigma : richLoss < sigma := by
    have hfinalStructuralSigma : finalStructuralBudget ≤ sigma / 2 :=
      min_le_right _ _
    have hcritical :
        finalFloorSchedule.criticalFloor.structuralLoss ≤
          finalStructuralBudget :=
      finalFloorSchedule.criticalFloor.structuralLoss_le
    have hdensity : finalFloorSchedule.densityLoss ≤
        finalStructuralBudget / 4 := by
      rw [finalFloorSchedule.densityLoss_eq]
      linarith
    dsimp only [richLoss]
    linarith
  have hrichOne : richLoss < 1 := hrichSigma.trans _hsigmaOne
  have hrichHalfSigma : richLoss / 2 < sigma := by
    linarith [hrichLoss, hrichSigma]
  rcases pureWZ2_sourceHorizontal_projection_threshold _hsigma hrichLoss
      hrichOne hrichHalfSigma with ⟨projection⟩
  rcases pureWZ2_terminalExact_projection_threshold _hsigma hrichLoss hrichOne
      hrichHalfSigma with ⟨terminalProjection⟩
  rcases pureWZ2_sourceFixedBinCoarse_analytic_threshold
      projection.theoremEta_pos with ⟨analytic⟩
  let jointVolumeLoss := analytic.base.budget.volumeLoss
  have hjointVolumeLoss : 0 < jointVolumeLoss := by
    exact analytic.base.budget.volumeLoss_pos
  let graphOuterLoss := jointVolumeLoss / 8
  have hgraphOuterLoss : 0 < graphOuterLoss := by
    dsimp only [graphOuterLoss]
    positivity
  let normalEta := min (sigma / 16)
    (min (richLoss / 16) (finalFloorSchedule.densityLoss / 64))
  have hnormalEta : 0 < normalEta := by
    dsimp only [normalEta]
    exact lt_min (div_pos _hsigma (by norm_num))
      (lt_min (div_pos hrichLoss (by norm_num))
        (div_pos finalFloorSchedule.densityLoss_pos (by norm_num)))
  have hnormalEtaSigma : 8 * normalEta < sigma := by
    have h := min_le_left (sigma / 16)
      (min (richLoss / 16) (finalFloorSchedule.densityLoss / 64))
    dsimp only [normalEta]
    linarith
  let middleLoss := min (outputLoss * jointVolumeLoss / 1024)
    (min (jointVolumeLoss / (1024 * outputLoss))
      (min (normalEta / 4)
        (min (projection.sourceCostLossCeiling / 4)
          (min (analytic.base.budget.constantLoss / 4)
            (min (finalFloorSchedule.densityLoss / 64)
              (min (terminalProjection.sourceLossCeiling / 4)
                (terminalProjection.theoremEta / 2048)))))))
  have hmiddle : 0 < middleLoss := by
    dsimp only [middleLoss]
    exact lt_min (div_pos (mul_pos houtput hjointVolumeLoss) (by norm_num))
      (lt_min (div_pos hjointVolumeLoss (mul_pos (by norm_num) houtput))
        (lt_min (div_pos hnormalEta (by norm_num))
          (lt_min (div_pos projection.sourceCostLossCeiling_pos (by norm_num))
            (lt_min (div_pos analytic.base.budget.constantLoss_pos (by norm_num))
              (lt_min (div_pos finalFloorSchedule.densityLoss_pos (by norm_num))
                (lt_min
                  (div_pos terminalProjection.sourceLossCeiling_pos (by norm_num))
                  (div_pos terminalProjection.theoremEta_pos (by norm_num))))))))
  have hmiddleNormal : middleLoss < normalEta := by
    exact ((min_le_right _ _).trans <| (min_le_right _ _).trans <|
      min_le_left _ _).trans_lt (by linarith [hnormalEta])
  have hmiddleProjection :
      middleLoss < (1 / 2 : ℝ) * projection.sourceCostLossCeiling := by
    have h : middleLoss ≤ projection.sourceCostLossCeiling / 4 :=
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right (normalEta / 4) _).trans
          (min_le_left (projection.sourceCostLossCeiling / 4) _)
    linarith [projection.sourceCostLossCeiling_pos]
  have hmiddleConstant :
      middleLoss < analytic.base.budget.constantLoss := by
    have h : middleLoss ≤ analytic.base.budget.constantLoss / 4 :=
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right (normalEta / 4) _).trans <|
          (min_le_right (projection.sourceCostLossCeiling / 4) _).trans
            (min_le_left _ _)
    linarith [analytic.base.budget.constantLoss_pos]
  have hmiddleDensity :
      middleLoss ≤ finalFloorSchedule.densityLoss / 64 :=
    calc
      middleLoss ≤ min (normalEta / 4)
          (min (projection.sourceCostLossCeiling / 4)
            (min (analytic.base.budget.constantLoss / 4)
              (min (finalFloorSchedule.densityLoss / 64)
                (min (terminalProjection.sourceLossCeiling / 4)
                  (terminalProjection.theoremEta / 2048))))) :=
        (min_le_right _ _).trans (min_le_right _ _)
      _ ≤
          min (projection.sourceCostLossCeiling / 4)
            (min (analytic.base.budget.constantLoss / 4)
              (min (finalFloorSchedule.densityLoss / 64)
                (min (terminalProjection.sourceLossCeiling / 4)
                  (terminalProjection.theoremEta / 2048)))) := min_le_right _ _
      _ ≤ min (analytic.base.budget.constantLoss / 4)
            (min (finalFloorSchedule.densityLoss / 64)
              (min (terminalProjection.sourceLossCeiling / 4)
                (terminalProjection.theoremEta / 2048))) := min_le_right _ _
      _ ≤ min (finalFloorSchedule.densityLoss / 64)
            (min (terminalProjection.sourceLossCeiling / 4)
              (terminalProjection.theoremEta / 2048)) := min_le_right _ _
      _ ≤ finalFloorSchedule.densityLoss / 64 := min_le_left _ _
  let stickyLoss := min (middleLoss / 2)
    (min (finalFloorSchedule.densityLoss / 64)
      (min (outputLoss / 2) (1 / 2)))
  have hsticky : 0 < stickyLoss := by
    dsimp only [stickyLoss]
    exact lt_min (div_pos hmiddle (by norm_num))
      (lt_min (div_pos finalFloorSchedule.densityLoss_pos (by norm_num))
        (lt_min (div_pos houtput (by norm_num)) (by norm_num)))
  have hstickyOutput : stickyLoss < outputLoss := by
    have h : stickyLoss ≤ outputLoss / 2 :=
      (min_le_right (middleLoss / 2) _).trans <|
        (min_le_right (finalFloorSchedule.densityLoss / 64) _).trans
          (min_le_left _ _)
    linarith
  have hstickyOne : stickyLoss ≤ 1 := by
    exact ((min_le_right _ _).trans <|
      (min_le_right (finalFloorSchedule.densityLoss / 64) _).trans <|
        (min_le_right _ _)).trans (by norm_num)
  have hstickyLeHalf : stickyLoss ≤ 1 / 2 :=
    (min_le_right _ _).trans <|
      (min_le_right (finalFloorSchedule.densityLoss / 64) _).trans <|
        (min_le_right _ _)
  have hstickyMiddle : stickyLoss ≤ middleLoss := by
    exact (min_le_left _ _).trans
      (div_le_self hmiddle.le (by norm_num))
  have hstickyNormal : 3 * stickyLoss / 2 < normalEta := by
    have hhalf : stickyLoss ≤ middleLoss / 2 :=
      min_le_left _ _
    linarith [hmiddleNormal]
  have hstickyDensity :
      stickyLoss ≤ finalFloorSchedule.densityLoss / 64 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hmiddleEta : 2 * middleLoss < normalEta := by
    have h : middleLoss ≤ normalEta / 4 :=
      (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_left _ _)
    linarith [hnormalEta]
  have hterminalProjection : 2 * middleLoss ≤
      terminalProjection.sourceLossCeiling := by
    have h : middleLoss ≤ terminalProjection.sourceLossCeiling / 4 :=
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right (normalEta / 4) _).trans <|
          (min_le_right (projection.sourceCostLossCeiling / 4) _).trans <|
            (min_le_right (analytic.base.budget.constantLoss / 4) _).trans <|
              (min_le_right (finalFloorSchedule.densityLoss / 64) _).trans
                (min_le_left _ _)
    linarith [terminalProjection.sourceLossCeiling_pos]
  have hmiddleTerminalEta : middleLoss ≤
      terminalProjection.theoremEta / 2048 :=
    (min_le_right _ _).trans <| (min_le_right _ _).trans <|
      (min_le_right (normalEta / 4) _).trans <|
        (min_le_right (projection.sourceCostLossCeiling / 4) _).trans <|
          (min_le_right (analytic.base.budget.constantLoss / 4) _).trans <|
            (min_le_right (finalFloorSchedule.densityLoss / 64) _).trans
              (min_le_right _ _)
  have hterminalConstant :
      2 * middleLoss < terminalProjection.theoremEta / 64 := by
    linarith [terminalProjection.theoremEta_pos]
  have hterminalVolume :
      2 * middleLoss + 5 * stickyLoss / 2 <
        terminalProjection.theoremEta / 64 := by
    have hstickyHalf : stickyLoss ≤ middleLoss / 2 :=
      min_le_left _ _
    linarith [terminalProjection.theoremEta_pos]
  have hterminalPair : stickyLoss + 3 * richLoss / 4 < richLoss := by
    have hnormalRich : normalEta ≤ richLoss / 16 :=
      (min_le_right (sigma / 16) _).trans (min_le_left _ _)
    have hmiddleNormalQuarter : middleLoss ≤ normalEta / 4 :=
      (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_left _ _)
    have hstickyHalf : stickyLoss ≤ middleLoss / 2 :=
      min_le_left _ _
    linarith [hrichLoss]
  have hrichSigmaThirtyTwo : richLoss ≤ sigma / 32 := by
    have hfinalStructuralSigma : finalStructuralBudget ≤ sigma / 2 :=
      min_le_right _ _
    have hcritical := finalFloorSchedule.criticalFloor.structuralLoss_le
    dsimp only [richLoss]
    rw [finalFloorSchedule.densityLoss_eq]
    linarith
  have hterminalOutput : richLoss + terminalProjection.theoremEta ≤ 1 := by
    linarith [terminalProjection.theoremEta_small]
  rcases pureWZ2_ordinaryWeightedTerminal_schedule _hsigma _hsigmaOne hmiddle
      hsticky (by
        exact min_le_left _ _) hnormalEta
      hnormalEtaSigma hmiddleEta hrichLoss hrichOne hrichHalfSigma
      terminalProjection hterminalProjection hterminalConstant hterminalVolume
      hterminalPair hterminalOutput with ⟨weightedTerminal⟩
  rcases capability.kernel sigma critical stickyLoss hsticky hstickyOne with
    ⟨kernel⟩
  rcases pureWZ2_sourceHorizontal_outerScale_flexible_schedule hsticky
      hstickyOutput with
    ⟨outerDelta₀, houterDelta₀, houterDelta₀One, outerScale⟩
  let sourceLossCeiling := min (outputLoss / 100)
    (min kernel.sourceLoss
      (min scalarClosure.sourceLossCeiling
        (min (finalFloorSchedule.densityLoss / 64)
          (min finalFloorSchedule.traceSourceCeiling
            (min (stickyLoss * normalEta / 2)
              (outputLoss * middleLoss / 4))))))
  have hsourceLossCeiling : 0 < sourceLossCeiling := by
    dsimp only [sourceLossCeiling]
    exact lt_min (div_pos houtput (by norm_num))
      (lt_min kernel.sourceLoss_pos
        (lt_min scalarClosure.sourceLossCeiling_pos
          (lt_min (div_pos finalFloorSchedule.densityLoss_pos (by norm_num))
            (lt_min finalFloorSchedule.traceSourceCeiling_pos
              (lt_min (div_pos (mul_pos hsticky hnormalEta) (by norm_num))
                (div_pos (mul_pos houtput hmiddle) (by norm_num)))))))
  have hsourceCore : sourceLossCeiling < stickyLoss * normalEta := by
    have h : sourceLossCeiling ≤ stickyLoss * normalEta / 2 :=
      (min_le_right (outputLoss / 100) _).trans <|
        (min_le_right kernel.sourceLoss _).trans <|
          (min_le_right scalarClosure.sourceLossCeiling _).trans <|
            (min_le_right (finalFloorSchedule.densityLoss / 64) _).trans <|
              (min_le_right finalFloorSchedule.traceSourceCeiling _).trans
                (min_le_left _ _)
    linarith [mul_pos hsticky hnormalEta]
  have hsourceDensity :
      sourceLossCeiling ≤ finalFloorSchedule.densityLoss / 64 :=
    (min_le_right (outputLoss / 100) _).trans <|
      (min_le_right kernel.sourceLoss _).trans <|
        (min_le_right scalarClosure.sourceLossCeiling _).trans
          (min_le_left _ _)
  have hsourceGraph :
      sourceLossCeiling ≤ outputLoss * middleLoss / 4 :=
    (min_le_right (outputLoss / 100) _).trans <|
      (min_le_right kernel.sourceLoss _).trans <|
        (min_le_right scalarClosure.sourceLossCeiling _).trans <|
          (min_le_right (finalFloorSchedule.densityLoss / 64) _).trans <|
            (min_le_right finalFloorSchedule.traceSourceCeiling _).trans
              (min_le_right _ _)
  have hnormalEtaSixteenth : normalEta < 1 / 16 := by
    have hnormalEtaSigmaSixteenth : normalEta ≤ sigma / 16 :=
      min_le_left _ _
    linarith
  have hsourceStickyThirtySecond :
      sourceLossCeiling < stickyLoss / 32 := by
    have hsourceStickyNormal :
        sourceLossCeiling ≤ stickyLoss * normalEta / 2 :=
      (min_le_right (outputLoss / 100) _).trans <|
        (min_le_right kernel.sourceLoss _).trans <|
          (min_le_right scalarClosure.sourceLossCeiling _).trans <|
            (min_le_right (finalFloorSchedule.densityLoss / 64) _).trans <|
              (min_le_right finalFloorSchedule.traceSourceCeiling _).trans
                (min_le_left _ _)
    have hproduct :
        stickyLoss * normalEta / 2 < stickyLoss / 32 := by
      have hscaled :=
        mul_lt_mul_of_pos_left hnormalEtaSixteenth hsticky
      linarith
    exact hsourceStickyNormal.trans_lt hproduct
  rcases
      pureWZ2_ordinaryPostDeletion_fixedBalancingThresholds
        hsourceLossCeiling hsticky hsourceStickyThirtySecond
    with
    ⟨fixedBalancing⟩
  rcases
      pureWZ2_ordinaryPostDeletion_preselectionThresholds
        fixedBalancing.selectionLoss_pos
    with
    ⟨preselectionThresholds⟩
  have hsourceSticky : sourceLossCeiling < stickyLoss := by
    exact hsourceStickyThirtySecond.trans <|
      div_lt_self hsticky (by norm_num)
  rcases
      pureWZ2_postDeletion_reentrant_scale_thresholds
        hsourceSticky hstickyLeHalf
    with
    ⟨postDeletionThresholds⟩
  have hmiddleGraphScale :
      middleLoss ≤ outputLoss * jointVolumeLoss / 1024 :=
    min_le_left _ _
  have hmiddleGraphInverse :
      middleLoss ≤ jointVolumeLoss / (1024 * outputLoss) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hstickyHalf : stickyLoss ≤ middleLoss / 2 :=
    min_le_left _ _
  rcases reentrantOrdinary_commonBinScalarThreshold
      (sigma := sigma)
      (sourceLossCeiling := sourceLossCeiling)
      (middleLoss := middleLoss)
      (stickyLoss := stickyLoss)
      (jointVolumeLoss := jointVolumeLoss)
      (outputLoss := outputLoss)
      (extraLoss := analytic.base.budget.extraLoss)
      (constantLoss := analytic.base.budget.constantLoss)
      (theoremEta := projection.theoremEta)
      hsourceLossCeiling hmiddle hsticky hjointVolumeLoss houtput hsourceGraph
      hmiddleGraphScale hmiddleGraphInverse hstickyHalf
      analytic.base.budget.edge_budget analytic.base.budget.extraLoss_pos
      analytic.base.budget.constantLoss_pos projection.theoremEta_small with
    ⟨commonBinScalar⟩
  rcases pureWZ2_ordinary_core_threshold capability.logExponent _hsigma
      hsourceLossCeiling.le hmiddle.le hsticky hnormalEta hsticky
      hstickyNormal hmiddleNormal hsourceCore with ⟨core⟩
  rcases pureWZ2_sourceHorizontal_geometric_threshold _hsigma hnormalEta
      hnormalEtaSigma hrichLoss with ⟨geometric⟩
  rcases pureWZ2_sourceFixedBinCoarse_projection_sourceCost_schedule
      hmiddle.le projection.sourceCostLossCeiling_pos hmiddleProjection with
    ⟨projectionRho₀, hprojectionRho₀, hprojectionRho₀One,
      projectionSourceCost⟩
  rcases pureWZ2_sourceFixedBinCoarse_constant_schedule hmiddle.le
      analytic.base.budget.constantLoss_pos
      hmiddleConstant with
    ⟨constantRho₀, hconstantRho₀, hconstantRho₀One, constantPower⟩
  rcases pureWZ2OrdinaryPaperOrderWindowHeightCost_richFloor_schedule
      hrichLoss hrichOne.le with
    ⟨heightRho₀, hheightRho₀, hheightRho₀One, heightCostAbsorption⟩
  have hsourceLocalConstant : sourceLossCeiling < outputLoss * middleLoss := by
    calc
      sourceLossCeiling ≤ outputLoss * middleLoss / 4 := hsourceGraph
      _ < outputLoss * middleLoss :=
        div_lt_self (mul_pos houtput hmiddle) (by norm_num)
  rcases pureWZ2_ordinary_local_constant_schedule houtput
      hsourceLossCeiling.le hmiddle hsourceLocalConstant with
    ⟨localConstantDelta₀, hlocalConstantDelta₀,
      hlocalConstantDelta₀One, localConstant⟩
  rcases pure_wz2_exists_delta₀_constant_rpow_le_one
      (constant := 10)
      (gap := finalFloorSchedule.densityLoss / 2) (by norm_num)
      (div_pos finalFloorSchedule.densityLoss_pos (by norm_num)) with
    ⟨densityDelta₀, hdensityDelta₀, hdensityDelta₀One, densityPower⟩
  let graphOuterThreshold :=
    pureWZ2_sourceWindowHeightBins_power_schedule
      (extraLoss := graphOuterLoss) hgraphOuterLoss
  let graphOuterRho₀ := Classical.choose graphOuterThreshold
  have hgraphOuterRho₀ : 0 < graphOuterRho₀ := by
    exact (Classical.choose_spec graphOuterThreshold).1
  let runtimeRho₀Base := min core.rho₀
    (min geometric.rho0
      (min projectionRho₀
        (min constantRho₀
          (min analytic.rho₀
            (min projection.rho₀ (min heightRho₀ weightedTerminal.rho₀))))))
  let runtimeRho₀ := min runtimeRho₀Base graphOuterRho₀
  have hruntimeRho₀ : 0 < runtimeRho₀ := by
    dsimp only [runtimeRho₀]
    apply lt_min
    · dsimp only [runtimeRho₀Base]
      exact lt_min core.rho₀_pos <|
        lt_min geometric.rho0_pos <| lt_min hprojectionRho₀ <|
          lt_min hconstantRho₀ <| lt_min analytic.rho₀_pos <|
            lt_min projection.rho₀_pos <| lt_min hheightRho₀
              weightedTerminal.rho₀_pos
    · exact hgraphOuterRho₀
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := 1280 * runtimeRho₀)
      (s := outputLoss) (by positivity) houtput with
    ⟨runtimeDelta₀, hruntimeDelta₀, hruntimeDelta₀One,
      runtimeScaleSmall⟩
  rcases sameFamilyOwnerUniformScalarThresholds sigma stickyLoss critical
      hsticky with ⟨ownerThresholds⟩
  let delta₀ := min kernel.delta₀
    (min outerDelta₀ (min scalarClosure.delta₀ finalFloorSchedule.delta₀))
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    exact lt_min kernel.delta₀_pos
      (lt_min houterDelta₀
        (lt_min scalarClosure.delta₀_pos finalFloorSchedule.delta₀_pos))
  let scalarDelta₀Base := min delta₀
    (min ownerThresholds.delta₀
      (min core.delta₀
        (min runtimeDelta₀
          (min densityDelta₀
            (min localConstantDelta₀
              (min fixedBalancing.delta₀
                (min postDeletionThresholds.delta₀
                  preselectionThresholds.delta₀)))))))
  let scalarDelta₀ := min scalarDelta₀Base commonBinScalar.delta₀
  have hscalarDelta₀ : 0 < scalarDelta₀ := by
    dsimp only [scalarDelta₀]
    apply lt_min
    · dsimp only [scalarDelta₀Base]
      exact lt_min hdelta₀ <| lt_min ownerThresholds.delta₀_pos <|
        lt_min core.delta₀_pos <|
          lt_min hruntimeDelta₀ <|
            lt_min hdensityDelta₀ <|
              lt_min hlocalConstantDelta₀ <|
                lt_min fixedBalancing.delta₀_pos
                  (lt_min postDeletionThresholds.delta₀_pos
                    preselectionThresholds.delta₀_pos)
    · exact commonBinScalar.delta₀_pos
  let ownerSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerSchedule capability sigma
        outputLoss sourceLossCeiling :=
    { stickyLoss := stickyLoss
      stickyLoss_pos := hsticky
      stickyLoss_lt_output := hstickyOutput
      kernel := kernel
      structuralBudget := structuralBudget
      structuralBudget_le_half := le_rfl
      traceSchedule := traceSchedule
      scalarClosure := scalarClosure
      finalStructuralBudget := finalStructuralBudget
      finalStructuralBudget_pos := hfinalStructuralBudget
      finalStructuralBudget_le_grain := hfinalStructuralGrain
      finalFloorSchedule := finalFloorSchedule
      richLoss := richLoss
      richLoss_eq := rfl
      richLoss_pos := hrichLoss
      richLoss_lt_one := hrichOne
      richLoss_half_lt_sigma := hrichHalfSigma
      richLoss_le_grain := hrichGrain
      richLoss_half_lt_finalDensity := hrichHalfDensity
      projection := projection
      analytic := analytic
      jointVolumeLoss := jointVolumeLoss
      jointVolumeLoss_eq := rfl
      jointVolumeLoss_pos := hjointVolumeLoss
      sourceLossCeiling_pos := hsourceLossCeiling
      sourceLossCeiling_output := min_le_left _ _
      sourceLossCeiling_kernel :=
        (min_le_right _ _).trans (min_le_left _ _)
      sourceLossCeiling_scalar :=
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
      sourceLossCeiling_finalDensity :=
        hsourceDensity.trans (div_le_self
          finalFloorSchedule.densityLoss_pos.le (by norm_num))
      sourceLossCeiling_finalTrace :=
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans <|
              (min_le_right _ _).trans (min_le_left _ _)
      outerDelta₀ := outerDelta₀
      outerDelta₀_pos := houterDelta₀
      outerDelta₀_le_one := houterDelta₀One
      outerScale := outerScale
      delta₀ := delta₀
      delta₀_pos := hdelta₀
      delta₀_le_one := (min_le_left _ _).trans kernel.delta₀_le_one
      delta₀_kernel := min_le_left _ _
      delta₀_outer := (min_le_right _ _).trans (min_le_left _ _)
      delta₀_scalar := (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
      delta₀_finalFloor := (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _) }
  exact ⟨⟨sourceLossCeiling,
    { middleLoss := middleLoss
      paperADBridge := paperADBridge
      sigma_lt_one := _hsigmaOne
      middleLoss_pos := hmiddle
      ownerSchedule := ownerSchedule
      stickyLoss_le_middle := hstickyMiddle
      normalEta := normalEta
      normalEta_pos := hnormalEta
      normalEta_sigma := hnormalEtaSigma
      middleLoss_lt_normal := hmiddleNormal
      middleLoss_projection := hmiddleProjection
      middleLoss_constant := hmiddleConstant
      stickyLoss_normal := hstickyNormal
      sourceLoss_core := hsourceCore
      sourceLoss_density := hsourceDensity
      normalEta_density := (min_le_right (sigma / 16) _).trans
        (min_le_right _ _)
      middleLoss_density := hmiddleDensity
      stickyLoss_density := hstickyDensity
      fixedBalancing := fixedBalancing
      postDeletionThresholds := postDeletionThresholds
      preselectionThresholds := preselectionThresholds
      graphOuterLoss := graphOuterLoss
      graphOuterLoss_pos := hgraphOuterLoss
      commonBinScalar := commonBinScalar
      core := core
      geometric := geometric
      weightedTerminal := weightedTerminal
      projectionRho₀ := projectionRho₀
      projectionRho₀_pos := hprojectionRho₀
      projectionRho₀_le_one := hprojectionRho₀One
      projectionSourceCost := projectionSourceCost
      constantRho₀ := constantRho₀
      constantRho₀_pos := hconstantRho₀
      constantRho₀_le_one := hconstantRho₀One
      constantPower := constantPower
      heightRho₀ := heightRho₀
      heightRho₀_pos := hheightRho₀
      heightRho₀_le_one := hheightRho₀One
      heightCostAbsorption := heightCostAbsorption
      localConstantDelta₀ := localConstantDelta₀
      localConstantDelta₀_pos := hlocalConstantDelta₀
      localConstantDelta₀_le_one := hlocalConstantDelta₀One
      localConstant := localConstant
      densityDelta₀ := densityDelta₀
      densityDelta₀_pos := hdensityDelta₀
      densityDelta₀_le_one := hdensityDelta₀One
      densityPower := by
        intro runtimeDelta hruntimeDelta hruntimeDeltaSmall
        simpa [ownerSchedule] using
          densityPower runtimeDelta hruntimeDelta hruntimeDeltaSmall
      runtimeRho₀ := runtimeRho₀
      runtimeRho₀_pos := hruntimeRho₀
      runtimeRho₀_le_core := (min_le_left _ _).trans (min_le_left _ _)
      runtimeRho₀_le_geometric := (min_le_left _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
      runtimeRho₀_le_projection := (min_le_left _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
      runtimeRho₀_le_constant := (min_le_left _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
      runtimeRho₀_le_analytic := (min_le_left _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_left _ _)
      runtimeRho₀_le_projectionThreshold := (min_le_left _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_left _ _)
      runtimeRho₀_le_height := (min_le_left _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans <|
            (min_le_right _ _).trans <| (min_le_right _ _).trans
              (min_le_left _ _)
      runtimeRho₀_le_weightedTerminal := (min_le_left _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans <|
            (min_le_right _ _).trans <| (min_le_right _ _).trans
              (min_le_right _ _)
      runtimeRho₀_le_graphOuter := by
        change runtimeRho₀ ≤ graphOuterRho₀
        exact min_le_right _ _
      scalarDelta₀ := scalarDelta₀
      scalarDelta₀_pos := hscalarDelta₀
      scalarDelta₀_le_one := (min_le_left _ _).trans <|
        (min_le_left _ _).trans <| (min_le_left _ _).trans
          kernel.delta₀_le_one
      scalarDelta₀_le_owner := (min_le_left _ _).trans (min_le_left _ _)
      ownerThresholds := ownerThresholds
      scalarDelta₀_le_ownerThresholds := (min_le_left _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
      scalarDelta₀_le_core := (min_le_left _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_left _ _)
      scalarDelta₀_density := (min_le_left _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_left _ _)
      scalarDelta₀_localConstant := (min_le_left _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_left _ _)
      scalarDelta₀_commonBin := min_le_right _ _
      scalarDelta₀_fixedBalancing := (min_le_left _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans <|
            (min_le_right _ _).trans <| (min_le_right _ _).trans
              (min_le_left _ _)
      scalarDelta₀_postDeletion := (min_le_left _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans <|
            (min_le_right _ _).trans <| (min_le_right _ _).trans
              ((min_le_right _ _).trans (min_le_left _ _))
      scalarDelta₀_preselection := (min_le_left _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans <|
            (min_le_right _ _).trans <| (min_le_right _ _).trans <|
              (min_le_right _ _).trans (min_le_right _ _)
      targetRho_small := by
        intro delta targetRho hdelta hdeltaSmall _hdeltaRho htargetUpper
        have hdeltaRuntime : delta ≤ runtimeDelta₀ :=
          hdeltaSmall.trans <| (min_le_left _ _).trans <|
            (min_le_right _ _).trans <| (min_le_right _ _).trans
              ((min_le_right _ _).trans (min_le_left _ _))
        have htarget : targetRho ≤ 1280 * runtimeRho₀ :=
          htargetUpper.trans (runtimeScaleSmall delta hdelta hdeltaRuntime)
        unfold pureWZ2SourceHorizontalInternalScale
        exact (div_le_iff₀ (by norm_num)).2 (by simpa [mul_comm] using htarget) }⟩⟩

/-- Compatibility wrapper for callers which still package the public paper-AD
bridge together with the historical private Node-4 fields.  The production
schedule itself uses only `paperADBridge`. -/
theorem PureWZ2Node05ExactNode4ReentryData.reentrantOrdinaryOwnerLossSchedule
    (node4 : PureWZ2Node05ExactNode4ReentryData)
    (capability : PureWZ2PropStickyCapability)
    {sigma outputLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtput : 0 < outputLoss) :
    Nonempty (Sigma fun sourceLossCeiling =>
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling) :=
  pureWZ2_reentrantOrdinaryOwnerLossSchedule node4.paperADBridge capability
    critical hsigma hsigmaOne houtput

/-- Legacy runtime owner evidence.  The production loss schedule no longer
contains an arbitrary-extremizer callback; compatibility users of this older
exact-owner route must provide that callback locally. -/
structure PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerReceipt
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    (kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer) where
  firstExact : PureWZ2Node05ExactMultiplicityPostRefinementData
    (sigma := sigma)
    (seedLoss := lossSchedule.ownerSchedule.stickyLoss)
    (outputLoss := lossSchedule.ownerSchedule.stickyLoss)
    current.grain.shading kernelOutput.requested
    capability.normalizationExponent kernelOutput.firstSeedLogExponent
    capability.logExponent
  first_data_eq : firstExact.seed.data = kernelOutput.first
  grainSchedule : PureWZ2Node05SameExtremizerSchedule sigma
    lossSchedule.middleLoss
  coarse_slope_eq :
    ∀ coarseGrains : PureWZ2GrainRefinementData
        firstExact.toNode5StickyData.croppedCoarseShading sigma
          lossSchedule.middleLoss,
      coarseGrains.globalGrains.slope = current.grain.globalGrains.slope
  firstLoss_le_input :
    lossSchedule.ownerSchedule.stickyLoss ≤ grainSchedule.inputLoss
  rho_le_grain_schedule : kernelOutput.requested.1 ≤ grainSchedule.delta₀
  sqrtRequested : WZ2PaperRequestedScale kernelOutput.requested.1
  sqrtRequested_eq : sqrtRequested.1 =
    Real.sqrt (pureWZ2SourceHorizontalInternalScale targetRho)
  fineSeedLoss : ℝ
  secondSeedLogExponent : ℕ
  continuation :
    ∀ coarseGrains : PureWZ2GrainRefinementData
        firstExact.toNode5StickyData.croppedCoarseShading sigma
          lossSchedule.middleLoss,
      PureWZ2Node05SecondOwnerContinuation
        (rhoRequested := kernelOutput.requested)
        (fineSeedLoss := fineSeedLoss)
        (secondLoss := lossSchedule.ownerSchedule.stickyLoss)
        (reentryNormalizationExponent := capability.normalizationExponent)
        (secondLogExponent := secondSeedLogExponent)
        (commonLogExponent := capability.logExponent)
        firstExact.toNode5StickyData coarseGrains sqrtRequested

namespace PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerReceipt

/-- Adapter to the existing actual-owner consumer.  Its formerly runtime
selected loss and grain schedule are definitionally the pre-runtime values. -/
noncomputable def toActualOwnerReceipt
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    (receipt : PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerReceipt
      (current := current) kernelOutput) :
    PureWZ2HierarchyReentrantOrdinaryActualOwnerReceipt
      (current := current) kernelOutput where
  middleLoss := lossSchedule.middleLoss
  firstExact := receipt.firstExact
  first_data_eq := receipt.first_data_eq
  grainSchedule := receipt.grainSchedule
  coarse_slope_eq := receipt.coarse_slope_eq
  firstLoss_le_input := receipt.firstLoss_le_input
  rho_le_grain_schedule := receipt.rho_le_grain_schedule
  sqrtRequested := receipt.sqrtRequested
  sqrtRequested_eq := receipt.sqrtRequested_eq
  fineSeedLoss := receipt.fineSeedLoss
  secondSeedLogExponent := receipt.secondSeedLogExponent
  continuation := receipt.continuation

@[simp] theorem toActualOwnerReceipt_middleLoss
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    (receipt : PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerReceipt
      (current := current) kernelOutput) :
    receipt.toActualOwnerReceipt.middleLoss = lossSchedule.middleLoss := rfl

end PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerReceipt

/-- Runtime owner producer after every auxiliary loss and the
same-extremizer schedule have been selected. -/
def PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerProducerAt
    (capability : PureWZ2PropStickyCapability) (sigma : ℝ) : Prop :=
  ∀ {outputLoss sourceLossCeiling : ℝ},
    ∀ lossSchedule :
        PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
          outputLoss sourceLossCeiling,
      ∀ inputLoss : ℝ,
        0 < inputLoss → inputLoss ≤ sourceLossCeiling →
          ∀ delta : ℝ,
            0 < delta → delta ≤ lossSchedule.ownerSchedule.delta₀ →
              ∀ current : PureWZ2ReentrantGrainSource sigma inputLoss delta
                  capability.normalizationExponent,
                ∀ targetRho : ℝ,
                  delta ≤ targetRho → targetRho ≤ 1 →
                    Real.rpow delta (1 - outputLoss) ≤ targetRho →
                      targetRho ≤ Real.rpow delta outputLoss →
                        ∀ outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
                            delta targetRho
                            lossSchedule.ownerSchedule.stickyLoss outputLoss,
                          ∀ kernelOutput :
                              PureWZ2HierarchyReentrantOrdinaryKernelOutput
                                (current := current)
                                lossSchedule.ownerSchedule outer,
                            Nonempty
                              (PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerReceipt
                                (current := current) kernelOutput)

/-- Construction-independent owner output tied to the middle loss fixed by the
pre-runtime schedule. -/
structure PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerOutputReceipt
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    (kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer) where
  ownerOutput : PureWZ2HierarchyReentrantOrdinaryOwnerOutputReceipt
    (current := current) kernelOutput
  middleLoss_eq : ownerOutput.middleLoss = lossSchedule.middleLoss
  coarseLoss_nonneg : 0 ≤ ownerOutput.twoScale.coarseLoss
  coarseLoss_le_max :
    ownerOutput.twoScale.coarseLoss ≤
      max lossSchedule.middleLoss lossSchedule.ownerSchedule.stickyLoss

/-- The post-owner producer is indexed by the complete pre-runtime loss
schedule and by an owner output carrying its equality to that schedule.  This
prevents the middle and coarse losses from being selected after the runtime
family. -/
def PureWZ2HierarchyReentrantOrdinaryPostOwnerProducerAt
    (capability : PureWZ2PropStickyCapability) (sigma : ℝ) : Prop :=
  ∀ {outputLoss sourceLossCeiling : ℝ},
    ∀ lossSchedule :
        PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
          outputLoss sourceLossCeiling,
      ∀ inputLoss : ℝ,
        0 < inputLoss → inputLoss ≤ sourceLossCeiling →
        ∀ delta : ℝ, 0 < delta → delta ≤ lossSchedule.scalarDelta₀ →
          ∀ current : PureWZ2ReentrantGrainSource sigma inputLoss delta
              capability.normalizationExponent,
            ∀ targetRho : ℝ,
              delta ≤ targetRho → targetRho ≤ 1 →
              Real.rpow delta (1 - outputLoss) ≤ targetRho →
              targetRho ≤ Real.rpow delta outputLoss →
                ∀ outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
                    delta targetRho lossSchedule.ownerSchedule.stickyLoss
                      outputLoss,
                  ∀ kernelOutput :
                      PureWZ2HierarchyReentrantOrdinaryKernelOutput
                        (current := current) lossSchedule.ownerSchedule outer,
                    ∀ preOwner :
                        PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerOutputReceipt
                          (current := current) kernelOutput,
                      ∀ pullback : PureWZ2TwoScaleCellPullbackData
                          preOwner.ownerOutput.twoScale,
                        ∀ prepared : PureWZ2SourceCarrierPreparation pullback,
                          Nonempty
                            (PureWZ2HierarchyReentrantOrdinaryPostOwnerReceipt
                              preOwner.ownerOutput pullback prepared)

/-- Completed form of the narrowed post-owner producer. -/
def PureWZ2HierarchyReentrantOrdinaryCompletedPostOwnerProducerAt
    (capability : PureWZ2PropStickyCapability) (sigma : ℝ) : Prop :=
  ∀ {outputLoss sourceLossCeiling : ℝ},
    ∀ lossSchedule :
        PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
          outputLoss sourceLossCeiling,
      ∀ inputLoss : ℝ,
        0 < inputLoss → inputLoss ≤ sourceLossCeiling →
        ∀ delta : ℝ, 0 < delta → delta ≤ lossSchedule.scalarDelta₀ →
          ∀ current : PureWZ2ReentrantGrainSource sigma inputLoss delta
              capability.normalizationExponent,
            ∀ targetRho : ℝ,
              delta ≤ targetRho → targetRho ≤ 1 →
              Real.rpow delta (1 - outputLoss) ≤ targetRho →
              targetRho ≤ Real.rpow delta outputLoss →
                ∀ outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
                    delta targetRho lossSchedule.ownerSchedule.stickyLoss
                      outputLoss,
                  ∀ kernelOutput :
                      PureWZ2HierarchyReentrantOrdinaryKernelOutput
                        (current := current) lossSchedule.ownerSchedule outer,
                    ∀ preOwner :
                        PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerOutputReceipt
                          (current := current) kernelOutput,
                      ∀ pullback : PureWZ2TwoScaleCellPullbackData
                          preOwner.ownerOutput.twoScale,
                        ∀ prepared : PureWZ2SourceCarrierPreparation pullback,
                          Nonempty
                            (PureWZ2HierarchyReentrantOrdinaryCompletedPostOwnerReceipt
                              preOwner.ownerOutput pullback prepared)

namespace PureWZ2HierarchyReentrantOrdinaryOwnerOutputReceipt

/-- Attach a construction-independent owner output to the already fixed
pre-runtime middle loss.  The equality is explicit so a synchronized producer
cannot select that loss after seeing the runtime source. -/
def toPreScheduled
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    (ownerOutput : PureWZ2HierarchyReentrantOrdinaryOwnerOutputReceipt
      (current := current) kernelOutput)
    (middleLoss_eq : ownerOutput.middleLoss = lossSchedule.middleLoss)
    (coarseLoss_nonneg : 0 ≤ ownerOutput.twoScale.coarseLoss)
    (coarseLoss_le_max : ownerOutput.twoScale.coarseLoss ≤
      max lossSchedule.middleLoss lossSchedule.ownerSchedule.stickyLoss) :
    PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerOutputReceipt
      (current := current) kernelOutput :=
  { ownerOutput := ownerOutput
    middleLoss_eq := middleLoss_eq
    coarseLoss_nonneg := coarseLoss_nonneg
    coarseLoss_le_max := coarseLoss_le_max }

end PureWZ2HierarchyReentrantOrdinaryOwnerOutputReceipt

namespace PureWZ2Node05SynchronizedTwoCallStage

/-- Attach one synchronized two-call stage to the exact pre-runtime owner-loss
schedule.  Both equalities are explicit: the first identifies the stage's
ambient seed with the public kernel call, while the second prevents the
selected loss from being chosen after the runtime source. -/
noncomputable def toPreScheduledHierarchyReentrantOrdinaryOwnerOutputReceipt
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho ambientLoss
      sourceLoss normalizationLoss grainLoss outputEta selectedLoss seedLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    {ambientLogExponent ancestorNormalizationExponent
      selectedNormalizationExponent secondSeedLogExponent : ℕ}
    {ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss) current.grain.shading
      kernelOutput.requested ambientLogExponent}
    {ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      ancestorNormalizationExponent sourceLoss normalizationLoss}
    {coarseGrains : PureWZ2GrainRefinementData
      ambient.croppedCoarseShading sigma grainLoss}
    {croppedMassFraction : ENNReal}
    {selection : PureWZ2Node05SynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      ambient ancestor coarseGrains croppedMassFraction}
    {sqrtRequested : WZ2PaperRequestedScale kernelOutput.requested.1}
    (stage : PureWZ2Node05SynchronizedTwoCallStage
      (seedLoss := seedLoss)
      (outputLoss := lossSchedule.ownerSchedule.stickyLoss)
      (firstLogExponent := capability.logExponent)
      (secondSeedLogExponent := secondSeedLogExponent)
      current.grain ambient ancestor coarseGrains croppedMassFraction
      selection sqrtRequested)
    (first_data_eq : HEq ambient.seed.data kernelOutput.first)
    (middleLoss_eq : selectedLoss = lossSchedule.middleLoss) :
    PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerOutputReceipt
      (current := current) kernelOutput :=
  (stage.toHierarchyReentrantOrdinaryOwnerOutputReceipt first_data_eq)
    |>.toPreScheduled middleLoss_eq (by
      change 0 ≤ selectedLoss
      rw [middleLoss_eq]
      exact lossSchedule.middleLoss_pos.le) (by
      change selectedLoss ≤
        max lossSchedule.middleLoss lossSchedule.ownerSchedule.stickyLoss
      rw [middleLoss_eq]
      exact le_max_left _ _)

end PureWZ2Node05SynchronizedTwoCallStage

/-- One complete synchronized owner construction at a pre-scheduled ordinary
runtime point.  All intermediate types are fields of one dependent record,
and the selected loss is definitionally the middle loss fixed before runtime.
This record deliberately leaves the quantitative overlay and second owner
construction as data rather than claiming they follow from the public kernel. -/
structure PureWZ2HierarchyReentrantOrdinarySynchronizedOwnerReceipt
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    (kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer) where
  ambientLoss : ℝ
  sourceLoss : ℝ
  normalizationLoss : ℝ
  grainLoss : ℝ
  outputEta : ℝ
  seedLoss : ℝ
  ambientLogExponent : ℕ
  ancestorNormalizationExponent : ℕ
  selectedNormalizationExponent : ℕ
  secondSeedLogExponent : ℕ
  ambient : PureWZ2Node5StickyData
    (sigma := sigma) (outputLoss := ambientLoss) current.grain.shading
    kernelOutput.requested ambientLogExponent
  first_data_eq : HEq ambient.seed.data kernelOutput.first
  ancestor : PureWZ2PropStickyReentryData
    (sigma := sigma) ambient.croppedCoarseShading
    ancestorNormalizationExponent sourceLoss normalizationLoss
  coarseGrains : PureWZ2GrainRefinementData
    ambient.croppedCoarseShading sigma grainLoss
  croppedMassFraction : ENNReal
  selection : PureWZ2Node05SynchronizedOwnerSelection
    (outputEta := outputEta) (selectedLoss := lossSchedule.middleLoss)
    (selectedNormalizationExponent := selectedNormalizationExponent)
    ambient ancestor coarseGrains croppedMassFraction
  stage : PureWZ2Node05SynchronizedTwoCallStage
    (seedLoss := seedLoss)
    (outputLoss := lossSchedule.ownerSchedule.stickyLoss)
    (firstLogExponent := capability.logExponent)
    (secondSeedLogExponent := secondSeedLogExponent)
    current.grain ambient ancestor coarseGrains croppedMassFraction
    selection kernelOutput.sqrtRequested

namespace PureWZ2HierarchyReentrantOrdinarySynchronizedOwnerReceipt

/-- Forget the synchronized construction only at the public hierarchy
boundary.  No constituent witness is selected again. -/
noncomputable def toPreScheduledOwnerOutput
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    (receipt : PureWZ2HierarchyReentrantOrdinarySynchronizedOwnerReceipt
      (current := current) kernelOutput) :
    PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerOutputReceipt
      (current := current) kernelOutput :=
  receipt.stage.toPreScheduledHierarchyReentrantOrdinaryOwnerOutputReceipt
    receipt.first_data_eq rfl

end PureWZ2HierarchyReentrantOrdinarySynchronizedOwnerReceipt

/-- Runtime producer for the exact dependent synchronized receipt.  It is
strictly stronger than the common owner-output producer and exposes, rather
than hides, the remaining synchronized quantitative inputs. -/
def PureWZ2HierarchyReentrantOrdinaryPreScheduledSynchronizedOwnerProducerAt
    (capability : PureWZ2PropStickyCapability) (sigma : ℝ) : Prop :=
  ∀ {outputLoss sourceLossCeiling : ℝ},
    ∀ lossSchedule :
        PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
          outputLoss sourceLossCeiling,
      ∀ inputLoss : ℝ,
        0 < inputLoss → inputLoss ≤ sourceLossCeiling →
          ∀ delta : ℝ,
            0 < delta → delta ≤ lossSchedule.ownerSchedule.delta₀ →
              ∀ current : PureWZ2ReentrantGrainSource sigma inputLoss delta
                  capability.normalizationExponent,
                ∀ targetRho : ℝ,
                  delta ≤ targetRho → targetRho ≤ 1 →
                    Real.rpow delta (1 - outputLoss) ≤ targetRho →
                      targetRho ≤ Real.rpow delta outputLoss →
                        ∀ outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
                            delta targetRho
                            lossSchedule.ownerSchedule.stickyLoss outputLoss,
                          ∀ kernelOutput :
                              PureWZ2HierarchyReentrantOrdinaryKernelOutput
                                (current := current)
                                lossSchedule.ownerSchedule outer,
                            Nonempty
                              (PureWZ2HierarchyReentrantOrdinarySynchronizedOwnerReceipt
                                (current := current) kernelOutput)

/-- Construction-independent pre-scheduled owner output.  The loss schedule
is still fixed before runtime, but the runtime construction may use either the
legacy exact-truncation route or the synchronized selected-family route. -/
def PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerOutputProducerAt
    (capability : PureWZ2PropStickyCapability) (sigma : ℝ) : Prop :=
  ∀ {outputLoss sourceLossCeiling : ℝ},
    ∀ lossSchedule :
        PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
          outputLoss sourceLossCeiling,
      ∀ inputLoss : ℝ,
        0 < inputLoss → inputLoss ≤ sourceLossCeiling →
          ∀ delta : ℝ,
            0 < delta → delta ≤ lossSchedule.ownerSchedule.delta₀ →
              ∀ current : PureWZ2ReentrantGrainSource sigma inputLoss delta
                  capability.normalizationExponent,
                ∀ targetRho : ℝ,
                  delta ≤ targetRho → targetRho ≤ 1 →
                    Real.rpow delta (1 - outputLoss) ≤ targetRho →
                      targetRho ≤ Real.rpow delta outputLoss →
                        ∀ outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
                            delta targetRho
                            lossSchedule.ownerSchedule.stickyLoss outputLoss,
                          ∀ kernelOutput :
                              PureWZ2HierarchyReentrantOrdinaryKernelOutput
                                (current := current)
                                lossSchedule.ownerSchedule outer,
                            Nonempty
                              (PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerOutputReceipt
                                (current := current) kernelOutput)

/-- Project a synchronized pre-scheduled producer to the construction-neutral
owner-output interface consumed by the hierarchy. -/
theorem pureWZ2_reentrantOrdinaryPreScheduledOwnerOutputProducer_of_synchronized
    {capability : PureWZ2PropStickyCapability} {sigma : ℝ}
    (producer :
      PureWZ2HierarchyReentrantOrdinaryPreScheduledSynchronizedOwnerProducerAt
        capability sigma) :
    PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerOutputProducerAt
      capability sigma := by
  intro outputLoss sourceLossCeiling lossSchedule inputLoss hinput
    hinputCeiling delta hdelta hdeltaSmall current targetRho hdeltaRho
    hrhoOne hrhoLower hrhoUpper outer kernelOutput
  rcases producer lossSchedule inputLoss hinput hinputCeiling delta hdelta
      hdeltaSmall current targetRho hdeltaRho hrhoOne hrhoLower hrhoUpper outer
      kernelOutput with ⟨receipt⟩
  exact ⟨receipt.toPreScheduledOwnerOutput⟩

/-- The legacy pre-scheduled exact owner projects to the common output without
changing its runtime witness. -/
theorem pureWZ2_reentrantOrdinaryPreScheduledOwnerOutputProducer_of_actual
    {capability : PureWZ2PropStickyCapability} {sigma : ℝ}
    (producer :
      PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerProducerAt
        capability sigma) :
    PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerOutputProducerAt
      capability sigma := by
  intro outputLoss sourceLossCeiling lossSchedule inputLoss hinput
    hinputCeiling delta hdelta hdeltaSmall current targetRho hdeltaRho
    hrhoOne hrhoLower hrhoUpper outer kernelOutput
  rcases producer lossSchedule inputLoss hinput hinputCeiling delta hdelta
      hdeltaSmall current targetRho hdeltaRho hrhoOne hrhoLower hrhoUpper outer
      kernelOutput with ⟨preOwner⟩
  let ownerOutput := preOwner.toActualOwnerReceipt.toOwnerOutput
  refine ⟨{
    ownerOutput := ownerOutput
    middleLoss_eq := rfl
    coarseLoss_nonneg := lossSchedule.ownerSchedule.stickyLoss_pos.le
    coarseLoss_le_max := ?_
  }⟩
  change lossSchedule.ownerSchedule.stickyLoss ≤
    max lossSchedule.middleLoss lossSchedule.ownerSchedule.stickyLoss
  exact le_max_right _ _

/-- Direct non-CWA front end using the extended pre-runtime loss schedule and
the construction-independent owner output and explicitly completed post-owner
producer.  No equality with an independently selected historical schedule is
required. -/
theorem pureWZ2_reentrantOrdinaryNonCWAFrontEnd_of_preScheduled_ownerOutput
    (paperADBridge : PureWZ2PaperADBridgeStatement)
    (capability : PureWZ2PropStickyCapability)
    {sigma : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (ownerProducer :
      PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerOutputProducerAt
        capability sigma)
    (postOwnerProducer :
      PureWZ2HierarchyReentrantOrdinaryCompletedPostOwnerProducerAt
        capability sigma) :
    PureWZ2HierarchyReentrantOrdinaryNonCWAFrontEndAt
      sigma capability.normalizationExponent := by
  intro outputLoss hsigma hsigmaOne houtputLoss
  rcases pureWZ2_reentrantOrdinaryOwnerLossSchedule paperADBridge capability
      critical hsigma hsigmaOne houtputLoss with
    ⟨⟨sourceLossCeiling, lossSchedule⟩⟩
  let schedule := lossSchedule.ownerSchedule
  refine ⟨sourceLossCeiling, lossSchedule.scalarDelta₀,
    schedule.sourceLossCeiling_pos, schedule.sourceLossCeiling_output,
    lossSchedule.scalarDelta₀_pos, lossSchedule.scalarDelta₀_le_one, ?_⟩
  refine ⟨{
    structuralBudget := schedule.structuralBudget
    schedule := schedule.traceSchedule
    runtime := ?_
  }⟩
  intro inputLoss hinputLoss hinputCeiling delta hdelta hdeltaSmall current
    targetRho hdeltaRho hrhoOne hrhoLower hrhoUpper
  rcases schedule.outerScale delta hdelta
      ((hdeltaSmall.trans lossSchedule.scalarDelta₀_le_owner).trans
        schedule.delta₀_outer) targetRho hrhoLower hrhoUpper
      with ⟨outer⟩
  rcases schedule.kernelOutput_nonempty hinputCeiling hdelta
      (hdeltaSmall.trans lossSchedule.scalarDelta₀_le_owner) outer with
    ⟨kernelOutput⟩
  rcases ownerProducer lossSchedule inputLoss hinputLoss hinputCeiling delta
      hdelta (hdeltaSmall.trans lossSchedule.scalarDelta₀_le_owner)
      current targetRho hdeltaRho hrhoOne hrhoLower
      hrhoUpper outer kernelOutput with ⟨preOwnerOutput⟩
  let ownerOutput := preOwnerOutput.ownerOutput
  refine PureWZ2HierarchyReentrantOrdinaryCompletedPostOwnerReceipt.toRuntimeNonCWAInputs_nonempty
    ownerOutput ?_ hinputCeiling
      (hdeltaSmall.trans lossSchedule.scalarDelta₀_le_owner)
  intro pullback prepared
  exact postOwnerProducer lossSchedule inputLoss hinputLoss hinputCeiling delta
    hdelta hdeltaSmall current targetRho hdeltaRho hrhoOne hrhoLower
    hrhoUpper outer kernelOutput preOwnerOutput pullback prepared

/-- Compatibility wrapper for the legacy pre-scheduled exact owner producer. -/
theorem pureWZ2_reentrantOrdinaryNonCWAFrontEnd_of_preScheduled_owner
    (paperADBridge : PureWZ2PaperADBridgeStatement)
    (capability : PureWZ2PropStickyCapability)
    {sigma : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (ownerProducer :
      PureWZ2HierarchyReentrantOrdinaryPreScheduledOwnerProducerAt
        capability sigma)
    (postOwnerProducer :
      PureWZ2HierarchyReentrantOrdinaryCompletedPostOwnerProducerAt
        capability sigma) :
    PureWZ2HierarchyReentrantOrdinaryNonCWAFrontEndAt
      sigma capability.normalizationExponent :=
  pureWZ2_reentrantOrdinaryNonCWAFrontEnd_of_preScheduled_ownerOutput
    paperADBridge capability critical
      (pureWZ2_reentrantOrdinaryPreScheduledOwnerOutputProducer_of_actual
        ownerProducer)
      postOwnerProducer

end Kakeya.Assouad

end
