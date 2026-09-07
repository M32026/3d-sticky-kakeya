import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallOrderedPairMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPairScalarChoices

/-!
# Pre-runtime mass schedule for the Proposition 6.3 four-call iteration

This module constructs the three scalar functions used by M6.  The terminal
losses and every index-local scalar seed are selected before the forward
runtime iteration.  In particular, the seed contains no current shading,
nested runtime, pullback object, or prefix mass.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- Turn the backwards-selected output loss of each coordinate into the loss
seen by the forward iterator.  Thus coordinate `index` has output loss
definitionally equal to `loss (index + 1)`. -/
def proposition63FourCallInnerLoss
    (initialLoss : ℝ) (outputLoss : ℕ → ℝ) : ℕ → ℝ
  | 0 => initialLoss
  | index + 1 => outputLoss index

/-- A scale cutoff which absorbs both halves of the ordered-pair mass loss.
It is selected from the two frozen factors and a strict backward loss gap,
before any forward runtime object is exposed. -/
structure Proposition63FourCallInnerMassAbsorptionData
    (leftFactor rightFactor : ENNReal)
    (currentLoss outputLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorb : ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
    2 * Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta currentLoss ∧
      2 * rightFactor * Kakeya.realRpowENN delta outputLoss ≤
        leftFactor * Kakeya.realRpowENN delta currentLoss

/-- Construct the per-index cutoff from a strict loss gap and positive finite
frozen factors.  The second bound absorbs `2 * right / left`; multiplying
back by the positive finite left factor gives the receipt-facing form. -/
theorem proposition63_four_call_inner_mass_absorption
    (leftFactor rightFactor : ENNReal)
    (left_pos : 0 < leftFactor)
    (left_finite : leftFactor ≠ ⊤)
    (right_finite : rightFactor ≠ ⊤)
    (currentLoss outputLoss : ℝ)
    (loss_gap : currentLoss < outputLoss) :
    Nonempty (Proposition63FourCallInnerMassAbsorptionData
      leftFactor rightFactor currentLoss outputLoss) := by
  let gap : ℝ := outputLoss - currentLoss
  have gap_pos : 0 < gap := by
    dsimp only [gap]
    linarith
  let ratio : ENNReal := 2 * rightFactor * leftFactor⁻¹
  have ratio_finite : ratio ≠ ⊤ := by
    dsimp only [ratio]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) right_finite)
      (ENNReal.inv_ne_top.mpr left_pos.ne')
  rcases exists_delta_realRpowENN_bound (2 : ENNReal) (by norm_num) gap_pos with
    ⟨oneDelta, oneDelta_pos, oneDelta_le_one, one_absorb⟩
  rcases exists_delta_realRpowENN_bound ratio ratio_finite gap_pos with
    ⟨ratioDelta, ratioDelta_pos, ratioDelta_le_one, ratio_absorb⟩
  let delta₀ := min oneDelta ratioDelta
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min oneDelta_pos ratioDelta_pos
    delta₀_le_one := (min_le_left _ _).trans oneDelta_le_one
    absorb := ?_
  }⟩
  intro delta delta_pos delta_le
  have delta_le_one : delta ≤ oneDelta :=
    delta_le.trans (min_le_left _ _)
  have delta_le_ratio : delta ≤ ratioDelta :=
    delta_le.trans (min_le_right _ _)
  have power_split :
      Kakeya.realRpowENN delta (-gap) *
          Kakeya.realRpowENN delta outputLoss =
        Kakeya.realRpowENN delta currentLoss := by
    calc
      Kakeya.realRpowENN delta (-gap) *
            Kakeya.realRpowENN delta outputLoss =
          Kakeya.realRpowENN delta (-gap + outputLoss) :=
        (realRpowENN_add delta_pos _ _).symm
      _ = Kakeya.realRpowENN delta currentLoss := by
        congr 1
        dsimp only [gap]
        ring
  constructor
  · calc
      2 * Kakeya.realRpowENN delta outputLoss ≤
          Kakeya.realRpowENN delta (-gap) *
            Kakeya.realRpowENN delta outputLoss := by
        gcongr
        exact one_absorb delta delta_pos delta_le_one
      _ = Kakeya.realRpowENN delta currentLoss := power_split
  · have ratio_power :
        ratio * Kakeya.realRpowENN delta outputLoss ≤
          Kakeya.realRpowENN delta currentLoss := by
      calc
        ratio * Kakeya.realRpowENN delta outputLoss ≤
            Kakeya.realRpowENN delta (-gap) *
              Kakeya.realRpowENN delta outputLoss := by
          gcongr
          exact ratio_absorb delta delta_pos delta_le_ratio
        _ = Kakeya.realRpowENN delta currentLoss := power_split
    have scaled := mul_le_mul_right ratio_power leftFactor
    have ratio_cancel :
        leftFactor * (ratio * Kakeya.realRpowENN delta outputLoss) =
          2 * rightFactor * Kakeya.realRpowENN delta outputLoss := by
      calc
        leftFactor * (ratio * Kakeya.realRpowENN delta outputLoss) =
            (leftFactor * leftFactor⁻¹) *
              (2 * rightFactor * Kakeya.realRpowENN delta outputLoss) := by
          dsimp only [ratio]
          ring
        _ = 2 * rightFactor * Kakeya.realRpowENN delta outputLoss := by
          rw [ENNReal.mul_inv_cancel left_pos.ne' left_finite]
          simp
    calc
      2 * rightFactor * Kakeya.realRpowENN delta outputLoss =
          leftFactor * (ratio * Kakeya.realRpowENN delta outputLoss) :=
        ratio_cancel.symm
      _ ≤ leftFactor * Kakeya.realRpowENN delta currentLoss := scaled

/-- The minimal scalar seed needed at one ordered-pair index.  Its factors
are the frozen actual-left expression and the uniform dependent right
expression used by the runtime majorization lemmas.  The two absorption
bounds are precisely the hypotheses of
`proposition63FourCallUniformMassScheduleOfTwoBounds`. -/
structure Proposition63FourCallInnerMassSeedAt
    {delta sigma inputLoss normalizationLoss densityLoss
      discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (currentLoss outputLoss : ℝ) (index : ℕ) where
  rho : ℝ
  outerLoss : ℝ
  fineWeightLoss : ℝ
  outerLogExponent : ℕ
  ancestorRetentionUpper : ENNReal
  frozenLineCoverBase : ENNReal
  canonicalNestedWeight : ENNReal
  uniformLevel : ℕ
  left_pos : 0 < proposition63FourCallFrozenActualLeftFactor
    root.normalization.croppedFamily delta rho sigma outerLoss
    fineWeightLoss outerLogExponent ancestorRetentionUpper
    frozenLineCoverBase canonicalNestedWeight
  left_finite : proposition63FourCallFrozenActualLeftFactor
    root.normalization.croppedFamily delta rho sigma outerLoss
    fineWeightLoss outerLogExponent ancestorRetentionUpper
    frozenLineCoverBase canonicalNestedWeight ≠ ⊤
  loss_gap : currentLoss < outputLoss
  output_loss_pos : 0 < outputLoss
  absorption : Proposition63FourCallInnerMassAbsorptionData
    (proposition63FourCallFrozenActualLeftFactor
      root.normalization.croppedFamily delta rho sigma outerLoss
      fineWeightLoss outerLogExponent ancestorRetentionUpper
      frozenLineCoverBase canonicalNestedWeight)
    (proposition63UniformDependentRightFactor
      root.normalization.croppedFamily uniformLevel)
    currentLoss outputLoss

/-- Transparently assemble the complete per-index scalar seed.  Only the
absorption receipt is selected noncomputably; all scalar fields reduce to the
corresponding constructor arguments. -/
noncomputable def proposition63FourCallInnerMassSeedOfScalars
    {delta sigma inputLoss normalizationLoss densityLoss
      discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (currentLoss outputLoss rho outerLoss fineWeightLoss : ℝ)
    (outerLogExponent : ℕ)
    (ancestorRetentionUpper frozenLineCoverBase
      canonicalNestedWeight : ENNReal)
    (uniformLevel index : ℕ)
    (left_pos : 0 < proposition63FourCallFrozenActualLeftFactor
      root.normalization.croppedFamily delta rho sigma outerLoss
      fineWeightLoss outerLogExponent ancestorRetentionUpper
      frozenLineCoverBase canonicalNestedWeight)
    (left_finite : proposition63FourCallFrozenActualLeftFactor
      root.normalization.croppedFamily delta rho sigma outerLoss
      fineWeightLoss outerLogExponent ancestorRetentionUpper
      frozenLineCoverBase canonicalNestedWeight ≠ ⊤)
    (loss_gap : currentLoss < outputLoss)
    (output_loss_pos : 0 < outputLoss)
    (delta_pos : 0 < delta) (delta_le_one : delta ≤ 1) :
    Proposition63FourCallInnerMassSeedAt root grid
      currentLoss outputLoss index := by
  have right_finite :=
    (proposition63UniformDependentRightFactor_pos_ne_top
      root.normalization.croppedFamily uniformLevel delta_pos delta_le_one).2
  let absorption := Classical.choice (proposition63_four_call_inner_mass_absorption
      (proposition63FourCallFrozenActualLeftFactor
        root.normalization.croppedFamily delta rho sigma outerLoss
        fineWeightLoss outerLogExponent ancestorRetentionUpper
        frozenLineCoverBase canonicalNestedWeight)
      (proposition63UniformDependentRightFactor
        root.normalization.croppedFamily uniformLevel)
      left_pos left_finite right_finite currentLoss outputLoss loss_gap)
  exact {
    rho := rho
    outerLoss := outerLoss
    fineWeightLoss := fineWeightLoss
    outerLogExponent := outerLogExponent
    ancestorRetentionUpper := ancestorRetentionUpper
    frozenLineCoverBase := frozenLineCoverBase
    canonicalNestedWeight := canonicalNestedWeight
    uniformLevel := uniformLevel
    left_pos := left_pos
    left_finite := left_finite
    loss_gap := loss_gap
    output_loss_pos := output_loss_pos
    absorption := absorption
  }

/-- Compatibility wrapper for the original existence-valued seed API. -/
theorem proposition63_four_call_inner_mass_seed
    {delta sigma inputLoss normalizationLoss densityLoss
      discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (currentLoss outputLoss rho outerLoss fineWeightLoss : ℝ)
    (outerLogExponent : ℕ)
    (ancestorRetentionUpper frozenLineCoverBase
      canonicalNestedWeight : ENNReal)
    (uniformLevel index : ℕ)
    (left_pos : 0 < proposition63FourCallFrozenActualLeftFactor
      root.normalization.croppedFamily delta rho sigma outerLoss
      fineWeightLoss outerLogExponent ancestorRetentionUpper
      frozenLineCoverBase canonicalNestedWeight)
    (left_finite : proposition63FourCallFrozenActualLeftFactor
      root.normalization.croppedFamily delta rho sigma outerLoss
      fineWeightLoss outerLogExponent ancestorRetentionUpper
      frozenLineCoverBase canonicalNestedWeight ≠ ⊤)
    (loss_gap : currentLoss < outputLoss)
    (output_loss_pos : 0 < outputLoss)
    (delta_pos : 0 < delta) (delta_le_one : delta ≤ 1) :
    Nonempty (Proposition63FourCallInnerMassSeedAt root grid
      currentLoss outputLoss index) :=
  ⟨proposition63FourCallInnerMassSeedOfScalars root grid currentLoss outputLoss
    rho outerLoss fineWeightLoss outerLogExponent ancestorRetentionUpper
    frozenLineCoverBase canonicalNestedWeight uniformLevel index left_pos
    left_finite loss_gap output_loss_pos delta_pos delta_le_one⟩

/-- One common positive cutoff for a finite family of positive real thresholds. -/
structure Proposition63FinitePositiveCutoff
    (pairCount : ℕ)
    (threshold : ∀ index, index < pairCount → ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  le_threshold : ∀ index, ∀ hindex : index < pairCount,
    delta₀ ≤ threshold index hindex

/-- A finite family of positive real thresholds has a common positive cutoff. -/
theorem proposition63_finite_positive_cutoff
    (pairCount : ℕ)
    (threshold : ∀ index, index < pairCount → ℝ)
    (threshold_pos : ∀ index, ∀ hindex : index < pairCount,
      0 < threshold index hindex) :
    Nonempty (Proposition63FinitePositiveCutoff
      pairCount threshold) := by
  induction pairCount with
  | zero =>
      exact ⟨{
        delta₀ := 1
        delta₀_pos := by norm_num
        delta₀_le_one := le_rfl
        le_threshold := by intro index hindex; omega
      }⟩
  | succ pairCount inductionHypothesis =>
      let prefixThreshold : ∀ index, index < pairCount → ℝ :=
        fun index hindex => threshold index (hindex.trans (Nat.lt_succ_self _))
      have prefix_pos : ∀ index, ∀ hindex : index < pairCount,
          0 < prefixThreshold index hindex := by
        intro index hindex
        exact threshold_pos index (hindex.trans (Nat.lt_succ_self _))
      rcases inductionHypothesis prefixThreshold prefix_pos with ⟨prior⟩
      let lastThreshold := threshold pairCount (Nat.lt_succ_self _)
      let delta₀ := min prior.delta₀ lastThreshold
      refine ⟨{
        delta₀ := delta₀
        delta₀_pos := lt_min prior.delta₀_pos
          (threshold_pos pairCount (Nat.lt_succ_self _))
        delta₀_le_one := (min_le_left _ _).trans prior.delta₀_le_one
        le_threshold := ?_
      }⟩
      intro index hindex
      by_cases hlast : index = pairCount
      · subst index
        exact min_le_right _ _
      · have hprefix : index < pairCount := by omega
        exact (min_le_left _ _).trans (prior.le_threshold index hprefix)

/-- Compatibility name for the M6 inner-mass finite-family cutoff. -/
abbrev Proposition63FourCallInnerMassFamilyCutoff :=
  Proposition63FinitePositiveCutoff

/-- Compatibility wrapper for the M6 inner-mass cutoff constructor. -/
theorem proposition63_four_call_inner_mass_family_cutoff
    (pairCount : ℕ)
    (threshold : ∀ index, index < pairCount → ℝ)
    (threshold_pos : ∀ index, ∀ hindex : index < pairCount,
      0 < threshold index hindex) :
    Nonempty (Proposition63FourCallInnerMassFamilyCutoff
      pairCount threshold) :=
  proposition63_finite_positive_cutoff pairCount threshold threshold_pos

/-- The actual-left factor selected before the callback at each index. -/
noncomputable def proposition63FourCallInnerLeftFactor
    {delta sigma inputLoss normalizationLoss densityLoss
      discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {loss : ℕ → ℝ}
    (seed : ∀ index, index < (finiteIntervalOrderedPairs gridN).length →
      Proposition63FourCallInnerMassSeedAt
        root grid (loss index) (loss (index + 1)) index)
    (index : ℕ) : ENNReal :=
  if hindex : index < (finiteIntervalOrderedPairs gridN).length then
    proposition63FourCallFrozenActualLeftFactor
      root.normalization.croppedFamily delta (seed index hindex).rho sigma
      (seed index hindex).outerLoss (seed index hindex).fineWeightLoss
      (seed index hindex).outerLogExponent
      (seed index hindex).ancestorRetentionUpper
      (seed index hindex).frozenLineCoverBase
      (seed index hindex).canonicalNestedWeight
  else 1

/-- The uniform dependent right factor selected before the callback. -/
noncomputable def proposition63FourCallInnerRightFactor
    {delta sigma inputLoss normalizationLoss densityLoss
      discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {loss : ℕ → ℝ}
    (seed : ∀ index, index < (finiteIntervalOrderedPairs gridN).length →
      Proposition63FourCallInnerMassSeedAt
        root grid (loss index) (loss (index + 1)) index)
    (index : ℕ) : ENNReal :=
  if hindex : index < (finiteIntervalOrderedPairs gridN).length then
    proposition63UniformDependentRightFactor
      root.normalization.croppedFamily (seed index hindex).uniformLevel
  else 1

/-- A finite family of backwards-selected scalar seeds constructs the actual
M6 mass schedule.  The proof invokes the two-bound constructor, rather than
merely repackaging or aliasing the schedule interface. -/
theorem proposition63FourCallInnerMassSchedule
    {delta sigma inputLoss normalizationLoss densityLoss
      discreteLoss intervalLoss gridOutputLoss queryScale initialLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (nextLoss : ℕ → ℝ)
    (seed : ∀ index, index < (finiteIntervalOrderedPairs gridN).length →
      Proposition63FourCallInnerMassSeedAt root grid
        (proposition63FourCallInnerLoss initialLoss nextLoss index)
        (proposition63FourCallInnerLoss initialLoss nextLoss (index + 1)) index)
    (cutoff : Proposition63FourCallInnerMassFamilyCutoff
      (finiteIntervalOrderedPairs gridN).length
      (fun index hindex => (seed index hindex).absorption.delta₀))
    (delta_le_cutoff : delta ≤ cutoff.delta₀)
    (delta_pos : 0 < delta) (delta_le_one : delta ≤ 1) :
    Proposition63FourCallUniformMassSchedule grid
      (proposition63FourCallInnerLoss initialLoss nextLoss)
      (proposition63FourCallInnerLeftFactor seed)
      (proposition63FourCallInnerRightFactor seed) := by
  apply proposition63FourCallUniformMassScheduleOfTwoBounds
  · intro index hindex
    simp only [proposition63FourCallInnerLeftFactor, dif_pos hindex]
    exact (seed index hindex).left_pos
  · intro index hindex
    simp only [proposition63FourCallInnerLeftFactor, dif_pos hindex]
    exact (seed index hindex).left_finite
  · intro index hindex
    simp only [proposition63FourCallInnerRightFactor, dif_pos hindex]
    exact (proposition63UniformDependentRightFactor_pos_ne_top
      root.normalization.croppedFamily (seed index hindex).uniformLevel
      delta_pos delta_le_one).2
  · intro index hindex
    exact (seed index hindex).loss_gap.le
  · intro index hindex
    exact (seed index hindex).output_loss_pos
  · intro index hindex
    exact ((seed index hindex).absorption.absorb delta delta_pos
      (delta_le_cutoff.trans (cutoff.le_threshold index hindex))).1
  · intro index hindex
    simp only [proposition63FourCallInnerLeftFactor,
      proposition63FourCallInnerRightFactor, dif_pos hindex]
    exact ((seed index hindex).absorption.absorb delta delta_pos
      (delta_le_cutoff.trans (cutoff.le_threshold index hindex))).2

theorem proposition63FourCallInnerLoss_next
    (initialLoss : ℝ) (nextLoss : ℕ → ℝ) (index : ℕ) :
    proposition63FourCallInnerLoss initialLoss nextLoss (index + 1) =
      nextLoss index := by
  rfl

/-- The exact pre-runtime left factor attached to a pair-local scalar core.
This is definitionally the expression required by
`Proposition63FourCallFrozenScalarReceiptsAt.hleftFactor`. -/
noncomputable def proposition63FourCallCoreLeftFactor
    {delta sigma inputLoss discreteLoss intervalLoss gridOutputLoss queryScale
      incidence : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (sourceCoefficient : NNReal)
    (scales : ∀ index, index < (finiteIntervalOrderedPairs gridN).length →
      Proposition63FourCallOrderedPairIndexScales grid index)
    (sqrtRequested : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      WZ2PaperRequestedScale (scales index hindex).rhoHat.1)
    (robustScale : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      WZ2PaperRequestedScale (scales index hindex).rhoHat.1)
    (core : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallPairScalarCoreAt grid backward.loss
        (backward.seed index hindex) sourceCoefficient incidence
        backward.rootNormalizationLoss (scales index hindex)
        (sqrtRequested index hindex) (robustScale index hindex))
    (index : ℕ) : ENNReal :=
  if hindex : index < (finiteIntervalOrderedPairs gridN).length then
    proposition63FourCallFrozenActualLeftFactor
      root.normalization.croppedFamily delta
      (scales index hindex).rhoHat.1 sigma
      (backward.seed index hindex).schedule.firstOutputLoss
      (backward.currentWeightLoss index hindex) 61
      (proposition63FourCallAncestorRetentionUpper
        root.normalization.croppedFamily (scales index hindex).rhoHat.1 sigma
        (backward.seed index hindex).schedule.firstOutputLoss
        (backward.seed index hindex).schedule.second.normalizationLoss
        (backward.seed index hindex).schedule.second.sourceLoss
        (backward.seed index hindex).rhoWeightLoss
        (backward.seed index hindex).firstStageWeightLoss)
      (proposition63FourCallFrozenLineCoverBase
        (core index hindex).cell.cellVolumeFloor
        (sqrtRequested index hindex).1
        (core index hindex).cover.coverBudget)
      (proposition63CanonicalReentryWeight (scales index hindex).rhoHat.1
        (backward.seed index hindex).nextWeightLoss)
  else 1

/-- The exact pre-runtime right factor attached to a pair-local scalar core.
This is definitionally the expression required by
`Proposition63FourCallFrozenScalarReceiptsAt.hrightFactor`. -/
noncomputable def proposition63FourCallCoreRightFactor
    {delta sigma discreteLoss intervalLoss gridOutputLoss queryScale
      incidence : ℝ} {gridN : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (loss : ℕ → ℝ)
    (seed : ∀ index, index < (finiteIntervalOrderedPairs gridN).length →
      Proposition63FourCallInnerLossSeed sigma (loss (index + 1)) discreteLoss)
    (sourceCoefficient : NNReal)
    (currentNormalizationLoss : ℝ)
    (scales : ∀ index, index < (finiteIntervalOrderedPairs gridN).length →
      Proposition63FourCallOrderedPairIndexScales grid index)
    (sqrtRequested : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      WZ2PaperRequestedScale (scales index hindex).rhoHat.1)
    (robustScale : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      WZ2PaperRequestedScale (scales index hindex).rhoHat.1)
    (core : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallPairScalarCoreAt grid loss (seed index hindex)
        sourceCoefficient incidence currentNormalizationLoss
        (scales index hindex) (sqrtRequested index hindex)
        (robustScale index hindex))
    (rootFamily : Kakeya.Streamlined.TubeFamily delta)
    (index : ℕ) : ENNReal :=
  if hindex : index < (finiteIntervalOrderedPairs gridN).length then
    proposition63UniformDependentRightFactor rootFamily
      (core index hindex).level.uniformLevel
  else 1

/-- Pair-local scalar cores canonically produce the complete family of mass
seeds.  The loss gap comes from the backward schedule, while every factor is
the exact frozen receipt expression. -/
theorem proposition63_four_call_inner_mass_seed_family_of_core_with_factor_provenance
    {delta sigma inputLoss discreteLoss intervalLoss gridOutputLoss queryScale
      incidence : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (sourceCoefficient : NNReal)
    (scales : ∀ index, index < (finiteIntervalOrderedPairs gridN).length →
      Proposition63FourCallOrderedPairIndexScales grid index)
    (sqrtRequested : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      WZ2PaperRequestedScale (scales index hindex).rhoHat.1)
    (robustScale : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      WZ2PaperRequestedScale (scales index hindex).rhoHat.1)
    (core : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallPairScalarCoreAt grid backward.loss
        (backward.seed index hindex) sourceCoefficient incidence
        backward.rootNormalizationLoss (scales index hindex)
        (sqrtRequested index hindex) (robustScale index hindex))
    (rho_small : ∀ (index : ℕ) (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      (scales index hindex).rhoHat.1 ≤ 1 / 24)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1) :
    ∃ seed : ∀ index (_hindex : index <
        (finiteIntervalOrderedPairs gridN).length),
        Proposition63FourCallInnerMassSeedAt root grid
          (backward.loss index) (backward.loss (index + 1)) index,
      (∀ index, proposition63FourCallInnerLeftFactor seed index =
        proposition63FourCallCoreLeftFactor backward root grid sourceCoefficient
          scales sqrtRequested robustScale core index) ∧
      ∀ index, proposition63FourCallInnerRightFactor seed index =
        proposition63FourCallCoreRightFactor grid backward.loss backward.seed
          sourceCoefficient backward.rootNormalizationLoss scales sqrtRequested
          robustScale core root.normalization.croppedFamily index := by
  classical
  have delta_le_one : delta ≤ 1 := delta_lt_one.le
  let ancestor : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length), ENNReal := fun index hindex =>
    proposition63FourCallAncestorRetentionUpper
      root.normalization.croppedFamily (scales index hindex).rhoHat.1 sigma
      (backward.seed index hindex).schedule.firstOutputLoss
      (backward.seed index hindex).schedule.second.normalizationLoss
      (backward.seed index hindex).schedule.second.sourceLoss
      (backward.seed index hindex).rhoWeightLoss
      (backward.seed index hindex).firstStageWeightLoss
  let lineCover : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length), ENNReal := fun index hindex =>
    proposition63FourCallFrozenLineCoverBase
      (core index hindex).cell.cellVolumeFloor
      (sqrtRequested index hindex).1 (core index hindex).cover.coverBudget
  let nestedWeight : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length), ENNReal := fun index hindex =>
    proposition63CanonicalReentryWeight (scales index hindex).rhoHat.1
      (backward.seed index hindex).nextWeightLoss
  let build : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallInnerMassSeedAt root grid
        (backward.loss index) (backward.loss (index + 1)) index :=
    fun index hindex => by
    have rho_pos : 0 < (scales index hindex).rhoHat.1 :=
      delta_pos.trans_le (scales index hindex).rhoHat.property.1
    have sqrt_pos : 0 < (sqrtRequested index hindex).1 :=
      rho_pos.trans_le (sqrtRequested index hindex).property.1
    have root_nonempty : root.normalization.croppedFamily.Nonempty :=
      root.normalization.final_extremal.nonempty
    have c73_pos : (0 : ENNReal) < 73 / 100 := by norm_num
    have c73_top : (73 / 100 : ENNReal) ≠ ⊤ :=
      ENNReal.div_ne_top (by norm_num) (by norm_num)
    have c81_pos : (0 : ENNReal) < 81 / 400 := by norm_num
    have c81_top : (81 / 400 : ENNReal) ≠ ⊤ :=
      ENNReal.div_ne_top (by norm_num) (by norm_num)
    have rho_lt_one : (scales index hindex).rhoHat.1 < 1 :=
      (rho_small index hindex).trans_lt (by norm_num)
    have outer_cost := proposition63UniformOuterCoarsePullbackCost_pos_ne_top
      (sigma := sigma)
      (outputLoss := (backward.seed index hindex).schedule.firstOutputLoss)
      root_nonempty delta_pos rho_pos
    have delta_fraction_pos :
        0 < wz2PaperPureRefinementFraction delta 61 := by
      unfold wz2PaperPureRefinementFraction
      exact ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top) 61
    have delta_fraction_top :
        wz2PaperPureRefinementFraction delta 61 ≠ ⊤ := by
      unfold wz2PaperPureRefinementFraction
      apply ENNReal.pow_ne_top
      apply ENNReal.inv_ne_top.mpr
      exact (ENNReal.ofReal_pos.mpr (Real.log_pos
        (one_lt_one_div delta_pos delta_lt_one))).ne'
    have rho_fraction_pos :
        0 < wz2PaperPureRefinementFraction (scales index hindex).rhoHat.1 61 := by
      unfold wz2PaperPureRefinementFraction
      exact ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top) 61
    have rho_fraction_top :
        wz2PaperPureRefinementFraction (scales index hindex).rhoHat.1 61 ≠ ⊤ := by
      unfold wz2PaperPureRefinementFraction
      apply ENNReal.pow_ne_top
      apply ENNReal.inv_ne_top.mpr
      exact (ENNReal.ofReal_pos.mpr (Real.log_pos
        (one_lt_one_div rho_pos rho_lt_one))).ne'
    have line_pos : 0 < lineCover index hindex := by
      dsimp only [lineCover, proposition63FourCallFrozenLineCoverBase]
      exact ENNReal.mul_pos
        (ENNReal.ofReal_pos.mpr (div_pos
          (div_pos (core index hindex).cell.positive (by norm_num))
          (by positivity))).ne'
        (ENNReal.div_pos (by norm_num)
          (ENNReal.mul_ne_top (by norm_num)
            (ENNReal.natCast_ne_top _))).ne'
    have line_top : lineCover index hindex ≠ ⊤ := by
      dsimp only [lineCover, proposition63FourCallFrozenLineCoverBase]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.div_ne_top (by norm_num)
          (ENNReal.mul_pos (by norm_num)
            (by exact_mod_cast (Nat.ne_of_gt
              (core index hindex).cover.positive))).ne')
    have nested_pos : 0 < nestedWeight index hindex := by
      dsimp only [nestedWeight, proposition63CanonicalReentryWeight]
      exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos rho_pos _)
    have nested_top : nestedWeight index hindex ≠ ⊤ := by
      dsimp only [nestedWeight, proposition63CanonicalReentryWeight,
        Kakeya.realRpowENN]
      exact ENNReal.ofReal_ne_top
    have regularization_one :=
      proposition63UniformReentryRegularizationLoss_pos_ne_top
        root.normalization.croppedFamily
        (proposition63CanonicalNearbyLevelCount
          (backward.seed index hindex).schedule.second.normalizationLoss)
    have regularization_two :=
      proposition63UniformReentryRegularizationLoss_pos_ne_top
        root.normalization.croppedFamily
        (proposition63CanonicalNearbyLevelCount
          ((backward.seed index hindex).schedule.second.sourceLoss / 4))
    have first_weight_pos : 0 < proposition63CanonicalReentryWeight
        (scales index hindex).rhoHat.1
        (backward.seed index hindex).firstStageWeightLoss := by
      unfold proposition63CanonicalReentryWeight
      exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos rho_pos _)
    have first_weight_top : proposition63CanonicalReentryWeight
        (scales index hindex).rhoHat.1
        (backward.seed index hindex).firstStageWeightLoss ≠ ⊤ :=
      proposition63CanonicalReentryWeight_ne_top
    have rho_weight_pos : 0 < proposition63CanonicalReentryWeight
        (scales index hindex).rhoHat.1
        (backward.seed index hindex).rhoWeightLoss := by
      unfold proposition63CanonicalReentryWeight
      exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos rho_pos _)
    have rho_weight_top : proposition63CanonicalReentryWeight
        (scales index hindex).rhoHat.1
        (backward.seed index hindex).rhoWeightLoss ≠ ⊤ :=
      proposition63CanonicalReentryWeight_ne_top
    have incoming_pos : 0 < proposition63FourCallIncomingRetentionUpper
        root.normalization.croppedFamily (scales index hindex).rhoHat.1 sigma
        (backward.seed index hindex).schedule.firstOutputLoss := by
      unfold proposition63FourCallIncomingRetentionUpper
      have card_pos : 0 < root.normalization.croppedFamily.enncard := by
        simp only [Kakeya.Streamlined.TubeFamily.enncard]
        exact_mod_cast root_nonempty
      exact ENNReal.mul_pos
        (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos rho_pos _)).ne'
        card_pos.ne'
    have incoming_top : proposition63FourCallIncomingRetentionUpper
        root.normalization.croppedFamily (scales index hindex).rhoHat.1 sigma
        (backward.seed index hindex).schedule.firstOutputLoss ≠ ⊤ := by
      unfold proposition63FourCallIncomingRetentionUpper
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
    have reentry_pos : 0 < proposition63FourCallReentryRetentionFormula
        (proposition63UniformReentryRegularizationLoss
          root.normalization.croppedFamily
          (proposition63CanonicalNearbyLevelCount
            ((backward.seed index hindex).schedule.second.sourceLoss / 4)))
        (proposition63CanonicalReentryWeight (scales index hindex).rhoHat.1
          (backward.seed index hindex).rhoWeightLoss)
        (proposition63FourCallIncomingRetentionUpper
          root.normalization.croppedFamily (scales index hindex).rhoHat.1 sigma
          (backward.seed index hindex).schedule.firstOutputLoss) := by
      unfold proposition63FourCallReentryRetentionFormula
      apply ENNReal.inv_pos.mpr
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr regularization_two.1.ne')
          (ENNReal.mul_ne_top c73_top
            rho_weight_top))
        (ENNReal.inv_ne_top.mpr incoming_pos.ne')
    have reentry_top : proposition63FourCallReentryRetentionFormula
        (proposition63UniformReentryRegularizationLoss
          root.normalization.croppedFamily
          (proposition63CanonicalNearbyLevelCount
            ((backward.seed index hindex).schedule.second.sourceLoss / 4)))
        (proposition63CanonicalReentryWeight (scales index hindex).rhoHat.1
          (backward.seed index hindex).rhoWeightLoss)
        (proposition63FourCallIncomingRetentionUpper
          root.normalization.croppedFamily (scales index hindex).rhoHat.1 sigma
          (backward.seed index hindex).schedule.firstOutputLoss) ≠ ⊤ := by
      unfold proposition63FourCallReentryRetentionFormula
      apply ENNReal.inv_ne_top.mpr
      exact ENNReal.mul_pos
        (ENNReal.mul_pos (ENNReal.inv_pos.mpr regularization_two.2).ne'
          (ENNReal.mul_pos c73_pos.ne' rho_weight_pos.ne').ne').ne'
        (ENNReal.inv_pos.mpr incoming_top).ne' |>.ne'
    have ancestor_pos : 0 < ancestor index hindex := by
      dsimp only [ancestor, proposition63FourCallAncestorRetentionUpper,
        proposition63FourCallPullbackRetentionFormula]
      apply ENNReal.inv_pos.mpr
      exact ENNReal.mul_ne_top rho_fraction_top <|
        ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr regularization_one.1.ne')
            (ENNReal.mul_ne_top c73_top first_weight_top))
          (ENNReal.mul_ne_top rho_fraction_top
            (ENNReal.inv_ne_top.mpr reentry_pos.ne'))
    have ancestor_top : ancestor index hindex ≠ ⊤ := by
      dsimp only [ancestor, proposition63FourCallAncestorRetentionUpper,
        proposition63FourCallPullbackRetentionFormula]
      apply ENNReal.inv_ne_top.mpr
      exact ((ENNReal.mul_pos_iff).2 ⟨rho_fraction_pos,
        (ENNReal.mul_pos_iff).2 ⟨
          (ENNReal.mul_pos_iff).2 ⟨
            ENNReal.inv_pos.mpr regularization_one.2,
            (ENNReal.mul_pos_iff).2 ⟨c73_pos, first_weight_pos⟩⟩,
          (ENNReal.mul_pos_iff).2 ⟨rho_fraction_pos,
            ENNReal.inv_pos.mpr reentry_top⟩⟩⟩).ne'
    have log_inverse_pos : 0 <
        (((Nat.log 2 root.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal))⁻¹ :=
      ENNReal.inv_pos.mpr ENNReal.coe_ne_top
    have log_inverse_top :
        (((Nat.log 2 root.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal))⁻¹ ≠ ⊤ := by
      apply ENNReal.inv_ne_top.mpr
      exact (ENNReal.coe_pos.mpr (by
        exact_mod_cast Nat.zero_lt_succ
          (Nat.log 2 root.normalization.croppedFamily.card))).ne'
    have retained_pos : 0 < proposition63FourCallFrozenNestedRetainedFactor
        (scales index hindex).rhoHat.1
        root.normalization.croppedFamily.card (nestedWeight index hindex) := by
      unfold proposition63FourCallFrozenNestedRetainedFactor
      positivity
    have retained_top : proposition63FourCallFrozenNestedRetainedFactor
        (scales index hindex).rhoHat.1
        root.normalization.croppedFamily.card (nestedWeight index hindex) ≠ ⊤ := by
      unfold proposition63FourCallFrozenNestedRetainedFactor
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · exact ENNReal.mul_ne_top c81_top log_inverse_top
          · exact rho_fraction_top
        · exact ENNReal.mul_ne_top c73_top nested_top
      · exact ENNReal.mul_ne_top c81_top log_inverse_top
    have fine_weight_pos : 0 < proposition63CanonicalReentryWeight delta
        (backward.currentWeightLoss index hindex) := by
      unfold proposition63CanonicalReentryWeight
      exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos delta_pos _)
    have fine_weight_top : proposition63CanonicalReentryWeight delta
        (backward.currentWeightLoss index hindex) ≠ ⊤ :=
      proposition63CanonicalReentryWeight_ne_top
    have left_pos : 0 < proposition63FourCallFrozenActualLeftFactor
        root.normalization.croppedFamily delta (scales index hindex).rhoHat.1 sigma
        (backward.seed index hindex).schedule.firstOutputLoss
        (backward.currentWeightLoss index hindex) 61
        (ancestor index hindex) (lineCover index hindex)
        (nestedWeight index hindex) := by
      unfold proposition63FourCallFrozenActualLeftFactor
        proposition63UniformDependentFinePullbackLeft
      exact ENNReal.mul_pos
        (ENNReal.mul_pos
          (ENNReal.mul_pos
            (ENNReal.mul_pos
              (ENNReal.mul_pos line_pos.ne' retained_pos.ne').ne'
              (ENNReal.inv_pos.mpr ancestor_top).ne').ne'
            (ENNReal.inv_pos.mpr outer_cost.2).ne').ne'
          delta_fraction_pos.ne').ne'
        (ENNReal.mul_pos c73_pos.ne' fine_weight_pos.ne').ne'
    have left_finite : proposition63FourCallFrozenActualLeftFactor
        root.normalization.croppedFamily delta (scales index hindex).rhoHat.1 sigma
        (backward.seed index hindex).schedule.firstOutputLoss
        (backward.currentWeightLoss index hindex) 61
        (ancestor index hindex) (lineCover index hindex)
        (nestedWeight index hindex) ≠ ⊤ := by
      unfold proposition63FourCallFrozenActualLeftFactor
        proposition63UniformDependentFinePullbackLeft
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top
              (ENNReal.mul_ne_top line_top retained_top)
              (ENNReal.inv_ne_top.mpr ancestor_pos.ne'))
            (ENNReal.inv_ne_top.mpr outer_cost.1.ne'))
          delta_fraction_top)
        (ENNReal.mul_ne_top c73_top fine_weight_top)
    exact proposition63FourCallInnerMassSeedOfScalars root grid
      (backward.loss index) (backward.loss (index + 1))
      (scales index hindex).rhoHat.1
      (backward.seed index hindex).schedule.firstOutputLoss
      (backward.currentWeightLoss index hindex) 61
      (ancestor index hindex) (lineCover index hindex)
      (nestedWeight index hindex) (core index hindex).level.uniformLevel index
      left_pos left_finite (backward.loss_lt_next index hindex)
      (backward.loss_pos (index + 1) (by omega)) delta_pos delta_le_one
  let massSeed := fun index hindex => build index hindex
  refine ⟨massSeed, ?_, ?_⟩
  · intro index
    by_cases hindex : index < (finiteIntervalOrderedPairs gridN).length
    · simp only [proposition63FourCallInnerLeftFactor,
        proposition63FourCallCoreLeftFactor, dif_pos hindex]
      simp only [massSeed, build, ancestor, lineCover, nestedWeight,
        proposition63FourCallInnerMassSeedOfScalars]
    · simp only [proposition63FourCallInnerLeftFactor,
        proposition63FourCallCoreLeftFactor, dif_neg hindex]
  · intro index
    by_cases hindex : index < (finiteIntervalOrderedPairs gridN).length
    · simp only [proposition63FourCallInnerRightFactor,
        proposition63FourCallCoreRightFactor, dif_pos hindex]
      simp only [massSeed, build, proposition63FourCallInnerMassSeedOfScalars]
    · simp only [proposition63FourCallInnerRightFactor,
        proposition63FourCallCoreRightFactor, dif_neg hindex]

/-- Compatibility wrapper retaining the original existence-valued family API. -/
theorem proposition63_four_call_inner_mass_seed_family_of_core
    {delta sigma inputLoss discreteLoss intervalLoss gridOutputLoss queryScale
      incidence : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (sourceCoefficient : NNReal)
    (scales : ∀ index, index < (finiteIntervalOrderedPairs gridN).length →
      Proposition63FourCallOrderedPairIndexScales grid index)
    (sqrtRequested : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      WZ2PaperRequestedScale (scales index hindex).rhoHat.1)
    (robustScale : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      WZ2PaperRequestedScale (scales index hindex).rhoHat.1)
    (core : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallPairScalarCoreAt grid backward.loss
        (backward.seed index hindex) sourceCoefficient incidence
        backward.rootNormalizationLoss (scales index hindex)
        (sqrtRequested index hindex) (robustScale index hindex))
    (rho_small : ∀ (index : ℕ) (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      (scales index hindex).rhoHat.1 ≤ 1 / 24)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1) :
    Nonempty (∀ index (_hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallInnerMassSeedAt root grid
        (backward.loss index) (backward.loss (index + 1)) index) := by
  rcases proposition63_four_call_inner_mass_seed_family_of_core_with_factor_provenance
      backward root grid sourceCoefficient scales sqrtRequested robustScale core
      rho_small delta_pos delta_lt_one with ⟨seed, _, _⟩
  exact ⟨seed⟩

/-- Pair-local cores, their exact frozen scalar formulas, and the backward
loss schedule produce one common mass cutoff and the corresponding uniform
M6 mass schedule. -/
theorem proposition63_four_call_uniform_mass_schedule_of_core
    {delta sigma inputLoss discreteLoss intervalLoss gridOutputLoss queryScale
      incidence : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (sourceCoefficient : NNReal)
    (scales : ∀ index, index < (finiteIntervalOrderedPairs gridN).length →
      Proposition63FourCallOrderedPairIndexScales grid index)
    (sqrtRequested : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      WZ2PaperRequestedScale (scales index hindex).rhoHat.1)
    (robustScale : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      WZ2PaperRequestedScale (scales index hindex).rhoHat.1)
    (core : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallPairScalarCoreAt grid backward.loss
        (backward.seed index hindex) sourceCoefficient incidence
        backward.rootNormalizationLoss (scales index hindex)
        (sqrtRequested index hindex) (robustScale index hindex))
    (rho_small : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      (scales index hindex).rhoHat.1 ≤ 1 / 24)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1) :
    ∃ seed : ∀ index (_hindex : index <
        (finiteIntervalOrderedPairs gridN).length),
        Proposition63FourCallInnerMassSeedAt root grid
          (backward.loss index) (backward.loss (index + 1)) index,
      ∃ cutoff : Proposition63FourCallInnerMassFamilyCutoff
          (finiteIntervalOrderedPairs gridN).length
          (fun index hindex => (seed index hindex).absorption.delta₀),
        ∀ _delta_le_cutoff : delta ≤ cutoff.delta₀,
          Proposition63FourCallUniformMassSchedule grid backward.loss
            (proposition63FourCallInnerLeftFactor
              (loss := backward.loss) seed)
            (proposition63FourCallInnerRightFactor
              (loss := backward.loss) seed) := by
  rcases proposition63_four_call_inner_mass_seed_family_of_core_with_factor_provenance
      backward root grid sourceCoefficient scales sqrtRequested robustScale core
      rho_small delta_pos delta_lt_one with ⟨seed, _, _⟩
  rcases proposition63_four_call_inner_mass_family_cutoff
      (finiteIntervalOrderedPairs gridN).length
      (fun index hindex => (seed index hindex).absorption.delta₀)
      (fun index hindex => (seed index hindex).absorption.delta₀_pos) with
    ⟨cutoff⟩
  refine ⟨seed, cutoff, ?_⟩
  intro delta_le_cutoff
  apply proposition63FourCallUniformMassScheduleOfTwoBounds
  · intro index hindex
    simp only [proposition63FourCallInnerLeftFactor, dif_pos hindex]
    exact (seed index hindex).left_pos
  · intro index hindex
    simp only [proposition63FourCallInnerLeftFactor, dif_pos hindex]
    exact (seed index hindex).left_finite
  · intro index hindex
    simp only [proposition63FourCallInnerRightFactor, dif_pos hindex]
    exact (proposition63UniformDependentRightFactor_pos_ne_top
      root.normalization.croppedFamily (seed index hindex).uniformLevel
      delta_pos delta_lt_one.le).2
  · intro index hindex
    exact (seed index hindex).loss_gap.le
  · intro index hindex
    exact (seed index hindex).output_loss_pos
  · intro index hindex
    exact ((seed index hindex).absorption.absorb delta delta_pos
      (delta_le_cutoff.trans (cutoff.le_threshold index hindex))).1
  · intro index hindex
    simp only [proposition63FourCallInnerLeftFactor,
      proposition63FourCallInnerRightFactor, dif_pos hindex]
    exact ((seed index hindex).absorption.absorb delta delta_pos
      (delta_le_cutoff.trans (cutoff.le_threshold index hindex))).2

end Kakeya.Assouad.PureWZ2
