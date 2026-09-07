import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentFinePullback

/-!
# Schedule arithmetic for one dependent Proposition 6.3 step

This record is the auditable scalar certificate for one coordinate of the
finite Lemma 4.12 schedule.  It keeps together the hypotheses used by the
dependent LOW/HIGH dichotomy, Property-(P), CWA boundary pruning, fresh
balancing, the uniform cover, integer-grid pullback, and the final fixed
iterator factors.  Its `run` theorem can only build the standard dependent
step through the paper-order producer.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

/-- A family- and schedule-level envelope for every finite external-weight
regularization loss used in the dependent Proposition 6.3 iteration. -/
def proposition63UniformReentryRegularizationLoss
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta)
    (levelCount : ℕ) : ENNReal :=
  (8 : ENNReal) *
    (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^ (levelCount + 2)

/-- Fixed right-hand loss paid by one dependent full-grain step after both
coarse and fine re-entry regularizations. -/
def proposition63UniformDependentRightFactor
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta)
    (levelCount : ℕ) : ENNReal :=
  (proposition63UniformReentryRegularizationLoss family levelCount *
    (proposition63UniformPreparationLoss family * 2)) *
    proposition63UniformReentryRegularizationLoss family levelCount

/-- Root-cardinality envelope for the multiplicity cost of pulling one
dependent coarse candidate through its outer Proposition 6.2 cover. -/
def proposition63UniformOuterCoarsePullbackCost
    {rootDelta : ℝ}
    (rootFamily : Kakeya.Streamlined.TubeFamily rootDelta)
    (delta rho sigma outputLoss : ℝ) : ENNReal :=
  (Kakeya.realRpowENN rho (2 - sigma - outputLoss) * rootFamily.enncard) *
    (Kakeya.realRpowENN rho (2 - sigma - outputLoss) * rootFamily.enncard) *
    (Kakeya.realRpowENN (delta / rho) (2 - sigma - outputLoss) *
      rootFamily.enncard)

/-- The left factor obtained after replacing the outer cover's runtime
multiplicity cost and the fine re-entry weight by their fixed schedule data. -/
def proposition63UniformDependentFinePullbackLeft
    {rootDelta : ℝ}
    (rootFamily : Kakeya.Streamlined.TubeFamily rootDelta)
    (delta rho sigma outputLoss : ℝ) (outerLogExponent : ℕ)
    (fineNormalizationWeight ancestorRetentionFactor coarseLeft : ENNReal) :
    ENNReal :=
  coarseLeft * ancestorRetentionFactor⁻¹ *
      (proposition63UniformOuterCoarsePullbackCost rootFamily delta rho sigma
        outputLoss)⁻¹ *
      wz2PaperPureRefinementFraction delta outerLogExponent *
    ((73 / 100 : ENNReal) * fineNormalizationWeight)

/-- Fully preselected left factor for one dependent schedule coordinate.  Its
only hereditary-normalization input is a fixed upper budget for the ancestor
retention cost; both normalization weights are canonical powers. -/
def proposition63UniformDependentLeftFactor
    {rootDelta : ℝ}
    (rootFamily : Kakeya.Streamlined.TubeFamily rootDelta)
    (delta rho sigma outerLoss finalLoss fineWeightLoss coarseWeightLoss : ℝ)
    (outerLogExponent innerLogExponent : ℕ)
    (sqrtScale : ℝ) (sqrtScale_pos : 0 < sqrtScale)
    (uniformCoverBudget : ℕ) (ancestorRetentionBudget : ENNReal) : ENNReal :=
  proposition63UniformDependentFinePullbackLeft rootFamily delta rho sigma
    outerLoss outerLogExponent
    (proposition63CanonicalReentryWeight delta fineWeightLoss)
    ancestorRetentionBudget
    (proposition63UniformLineFactor
        (Kakeya.realRpowENN rho (finalLoss + 2)) sqrtScale sqrtScale_pos *
      (((1 : ENNReal) / 2) / (2 * (uniformCoverBudget : ENNReal))) *
      ((proposition63DependentPropertyThreeMassLoss
          rho innerLogExponent)⁻¹ *
        ((73 / 100 : ENNReal) *
          proposition63CanonicalReentryWeight rho coarseWeightLoss)))

theorem proposition63UniformReentryRegularizationLoss_pos_ne_top
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta)
    (levelCount : ℕ) :
    0 < proposition63UniformReentryRegularizationLoss family levelCount ∧
      proposition63UniformReentryRegularizationLoss family levelCount ≠ ⊤ := by
  have hlogPos : (0 : ENNReal) <
      (Nat.log 2 (2 * family.card) : ENNReal) + 1 := by
    exact_mod_cast Nat.zero_lt_succ (Nat.log 2 (2 * family.card))
  have hlogTop :
      (Nat.log 2 (2 * family.card) : ENNReal) + 1 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, by norm_num⟩
  unfold proposition63UniformReentryRegularizationLoss
  exact ⟨ENNReal.mul_pos (by norm_num)
      (ENNReal.pow_pos hlogPos (levelCount + 2)).ne',
    ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hlogTop)⟩

theorem proposition63UniformOuterCoarsePullbackCost_pos_ne_top
    {rootDelta : ℝ}
    {rootFamily : Kakeya.Streamlined.TubeFamily rootDelta}
    (root_nonempty : rootFamily.Nonempty)
    {delta rho sigma outputLoss : ℝ}
    (delta_pos : 0 < delta) (rho_pos : 0 < rho) :
    0 < proposition63UniformOuterCoarsePullbackCost rootFamily delta rho sigma
        outputLoss ∧
      proposition63UniformOuterCoarsePullbackCost rootFamily delta rho sigma
        outputLoss ≠ ⊤ := by
  have hcardPos : (0 : ENNReal) < rootFamily.enncard := by
    change (0 : ENNReal) < (rootFamily.card : ENNReal)
    exact_mod_cast root_nonempty
  have hcardTop : rootFamily.enncard ≠ ⊤ := ENNReal.coe_ne_top
  have hrhoPos : 0 < Kakeya.realRpowENN rho
      (2 - sigma - outputLoss) :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos rho_pos _)
  have hrhoTop : Kakeya.realRpowENN rho
      (2 - sigma - outputLoss) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hratioPos : 0 < Kakeya.realRpowENN (delta / rho)
      (2 - sigma - outputLoss) :=
    ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos (div_pos delta_pos rho_pos) _)
  have hratioTop : Kakeya.realRpowENN (delta / rho)
      (2 - sigma - outputLoss) ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold proposition63UniformOuterCoarsePullbackCost
  exact ⟨ENNReal.mul_pos
      (ENNReal.mul_pos
        (ENNReal.mul_pos hrhoPos.ne' hcardPos.ne').ne'
        (ENNReal.mul_pos hrhoPos.ne' hcardPos.ne').ne').ne'
      (ENNReal.mul_pos hratioPos.ne' hcardPos.ne').ne',
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top hrhoTop hcardTop)
        (ENNReal.mul_ne_top hrhoTop hcardTop))
      (ENNReal.mul_ne_top hratioTop hcardTop)⟩

theorem proposition63FreshBalancingEnvelope_pos_ne_top
    {delta : ℝ} (delta_pos : 0 < delta) (delta_le_one : delta ≤ 1) :
    0 < proposition63FreshBalancingEnvelope delta ∧
      proposition63FreshBalancingEnvelope delta ≠ ⊤ := by
  have hinverse : (1 : ℝ) ≤ delta⁻¹ := by
    calc
      (1 : ℝ) = 1⁻¹ := by norm_num
      _ ≤ delta⁻¹ := by gcongr
  have hcoefficient : 0 < wz2PaperBoundaryLogCoefficient := by
    dsimp only [wz2PaperBoundaryLogCoefficient]
    have : 0 < 5 / Real.log 2 := by positivity
    exact this.trans_le (le_max_right _ _)
  have hreal : 0 < wz2PaperBoundaryLogCoefficient *
      (1 + Real.log delta⁻¹) := by
    have hlog : 0 ≤ Real.log delta⁻¹ := Real.log_nonneg hinverse
    positivity
  have hof : 0 < ENNReal.ofReal
      (wz2PaperBoundaryLogCoefficient * (1 + Real.log delta⁻¹)) :=
    ENNReal.ofReal_pos.mpr hreal
  unfold proposition63FreshBalancingEnvelope
  exact ⟨ENNReal.mul_pos (by norm_num) hof.ne',
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top⟩

theorem proposition63UniformPreparationLoss_pos_ne_top
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta)
    (delta_pos : 0 < delta) (delta_le_one : delta ≤ 1) :
    0 < proposition63UniformPreparationLoss family ∧
      proposition63UniformPreparationLoss family ≠ ⊤ := by
  have hlogPos : (0 : ENNReal) <
      ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) := by
    exact_mod_cast Nat.zero_lt_succ (Nat.log 2 family.card)
  have hlogTop : ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) ≠ ⊤ :=
    ENNReal.coe_ne_top
  have henvelope := proposition63FreshBalancingEnvelope_pos_ne_top
    delta_pos delta_le_one
  unfold proposition63UniformPreparationLoss
  exact ⟨ENNReal.mul_pos hlogPos.ne' henvelope.1.ne',
    ENNReal.mul_ne_top hlogTop henvelope.2⟩

theorem proposition63UniformDependentRightFactor_pos_ne_top
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta)
    (levelCount : ℕ) (delta_pos : 0 < delta) (delta_le_one : delta ≤ 1) :
    0 < proposition63UniformDependentRightFactor family levelCount ∧
      proposition63UniformDependentRightFactor family levelCount ≠ ⊤ := by
  have hreentry :=
    proposition63UniformReentryRegularizationLoss_pos_ne_top family levelCount
  have hpreparation := proposition63UniformPreparationLoss_pos_ne_top family
    delta_pos delta_le_one
  unfold proposition63UniformDependentRightFactor
  exact ⟨ENNReal.mul_pos
      (ENNReal.mul_pos hreentry.1.ne'
        (ENNReal.mul_pos hpreparation.1.ne' (by norm_num)).ne').ne'
      hreentry.1.ne',
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hreentry.2
        (ENNReal.mul_ne_top hpreparation.2 (by norm_num)))
      hreentry.2⟩

/-- Replacing both runtime cover cardinalities by the fixed root cardinality
gives an upper bound for the exact whole-cell pullback cost. -/
theorem proposition63_outerCoarsePullbackCost_le_uniform
    {delta sigma outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss) source rho logExponent)
    {rootDelta : ℝ}
    (rootFamily : Kakeya.Streamlined.TubeFamily rootDelta)
    (coarse_card_le : outer.coarse.card ≤ rootFamily.card)
    (selected_card_le : outer.selected.family.card ≤ rootFamily.card) :
    proposition63OuterCoarsePullbackCost outer ≤
      proposition63UniformOuterCoarsePullbackCost rootFamily delta rho.1
        sigma outputLoss := by
  have hcoarse : outer.coarse.enncard ≤ rootFamily.enncard := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using coarse_card_le
  have hselected : outer.selected.family.enncard ≤ rootFamily.enncard := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using selected_card_le
  unfold proposition63OuterCoarsePullbackCost
    proposition63UniformOuterCoarsePullbackCost
    stickyCoarseMultiplicityCap stickyFiberMultiplicityCap
  gcongr

/-- Specialization of the outer pullback-cost bound along the actual fine
re-entry and outer-cover embeddings used by the fixed-root iterator. -/
theorem proposition63_outerCoarsePullbackCost_le_root
    {delta sigma initialInputLoss normalizationLoss fineReentryLoss outerLoss : ℝ}
    {initialSource :
      PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent outerLogExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {fineCurrent : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) initialNormalized fineCurrent)
    {rho : WZ2PaperRequestedScale delta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent) :
    proposition63OuterCoarsePullbackCost outer ≤
      proposition63UniformOuterCoarsePullbackCost
        initialNormalized.croppedFamily delta rho.1 sigma outerLoss := by
  apply proposition63_outerCoarsePullbackCost_le_uniform outer
  · have houterSelected : outer.coarse.card ≤ outer.selected.family.card := by
      simpa only [Fintype.card_fin] using (Fintype.card_le_of_surjective
        outer.cover.toPaperTubeCover.parent
        outer.cover.toPaperTubeCover.parent_surjective)
    have hselectedFine : outer.selected.family.card ≤
        fineReentry.normalization.croppedFamily.card := by
      simpa only [Fintype.card_fin] using
        (Fintype.card_le_of_injective outer.selected.embedding
          outer.selected.embedding.injective)
    have hreentryFine : fineReentry.normalization.croppedFamily.card ≤
        initialNormalized.croppedFamily.card := by
      rw [fineReentry.normalization_croppedFamily]
      simpa only [Fintype.card_fin] using (Fintype.card_le_of_injective
        fineReentry.regularized.selected.embedding
        fineReentry.regularized.selected.embedding.injective)
    exact houterSelected.trans <| hselectedFine.trans hreentryFine
  · have hselectedFine : outer.selected.family.card ≤
        fineReentry.normalization.croppedFamily.card := by
      simpa only [Fintype.card_fin] using
        (Fintype.card_le_of_injective outer.selected.embedding
          outer.selected.embedding.injective)
    have hreentryFine : fineReentry.normalization.croppedFamily.card ≤
        initialNormalized.croppedFamily.card := by
      rw [fineReentry.normalization_croppedFamily]
      simpa only [Fintype.card_fin] using (Fintype.card_le_of_injective
        fineReentry.regularized.selected.embedding
        fineReentry.regularized.selected.embedding.injective)
    exact hselectedFine.trans hreentryFine

/-- The fixed outer-cost/canonical-weight left factor is no larger than the
exact runtime pullback factor. -/
theorem proposition63_uniformDependentFinePullbackLeft_le
    {delta sigma initialInputLoss normalizationLoss fineReentryLoss outerLoss
      fineWeightLoss : ℝ}
    {initialSource :
      PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent outerLogExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {fineCurrent : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) initialNormalized fineCurrent)
    {rho : WZ2PaperRequestedScale delta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    (ancestorRetentionFactor coarseLeft : ENNReal)
    (weight_eq : fineReentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta fineWeightLoss) :
    proposition63UniformDependentFinePullbackLeft
        initialNormalized.croppedFamily delta rho.1 sigma outerLoss
        outerLogExponent
        (proposition63CanonicalReentryWeight delta fineWeightLoss)
        ancestorRetentionFactor coarseLeft ≤
      proposition63DependentFinePullbackLeft fineReentry outer
        ancestorRetentionFactor coarseLeft := by
  unfold proposition63UniformDependentFinePullbackLeft
    proposition63DependentFinePullbackLeft
  rw [weight_eq]
  gcongr
  exact proposition63_outerCoarsePullbackCost_le_root fineReentry outer

/-- The fully preselected left factor is below the exact runtime pullback
factor when the hereditary coarse normalization obeys its advertised weight
and retention budgets. -/
theorem proposition63_uniformDependentLeftFactor_le
    {delta sigma initialInputLoss normalizationLoss fineReentryLoss outerLoss
      finalLoss fineWeightLoss coarseWeightLoss : ℝ}
    {initialSource :
      PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {fineCurrent : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) initialNormalized fineCurrent)
    {rho : WZ2PaperRequestedScale delta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    {coarseInputLoss coarseNormalizationLoss coarseReentryLoss : ℝ}
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    {coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      normalizationExponent}
    {coarseCurrent : WZ1PaperTubeShading coarseNormalized.croppedFamily}
    (coarseReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := coarseReentryLoss) coarseNormalized coarseCurrent)
    (ancestorRetentionFactor ancestorRetentionBudget : ENNReal)
    (ancestorRetentionFactor_le :
      ancestorRetentionFactor ≤ ancestorRetentionBudget)
    (fine_weight_eq : fineReentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta fineWeightLoss)
    (coarse_weight_eq : coarseReentry.normalizationWeight =
      proposition63CanonicalReentryWeight rho.1 coarseWeightLoss)
    (sqrtScale : ℝ) (sqrtScale_pos : 0 < sqrtScale)
    (uniformCoverBudget : ℕ) :
    proposition63UniformDependentLeftFactor
        initialNormalized.croppedFamily delta rho.1 sigma outerLoss finalLoss
        fineWeightLoss coarseWeightLoss outerLogExponent innerLogExponent
        sqrtScale sqrtScale_pos uniformCoverBudget ancestorRetentionBudget ≤
      proposition63DependentFinePullbackLeft fineReentry outer
        ancestorRetentionFactor
        (proposition63UniformLineFactor
            (Kakeya.realRpowENN rho.1 (finalLoss + 2)) sqrtScale
            sqrtScale_pos *
          (((1 : ENNReal) / 2) /
            (2 * (uniformCoverBudget : ENNReal))) *
          ((proposition63DependentPropertyThreeMassLoss
              rho.1 innerLogExponent)⁻¹ *
            ((73 / 100 : ENNReal) * coarseReentry.normalizationWeight))) := by
  unfold proposition63UniformDependentLeftFactor
  rw [coarse_weight_eq]
  apply proposition63_uniformDependentFinePullbackLeft_le fineReentry outer
    ancestorRetentionBudget _ fine_weight_eq |>.trans
  unfold proposition63DependentFinePullbackLeft
  gcongr

/-- A runtime re-entry regularization loss is controlled by a fixed envelope
as soon as its ambient family cardinality and requested schedule length are. -/
theorem proposition63_reentry_regularizationLoss_le_uniform
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource :
      PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    {referenceDelta : ℝ}
    (referenceFamily : Kakeya.Streamlined.TubeFamily referenceDelta)
    (uniformLevelCount : ℕ)
    (card_le : initialNormalized.croppedFamily.card ≤ referenceFamily.card)
    (levelCount_le : data.levelCount ≤ uniformLevelCount) :
    data.regularized.regularizationLoss ≤
      proposition63UniformReentryRegularizationLoss referenceFamily
        uniformLevelCount := by
  have hlogNat :
      Nat.log 2 (2 * initialNormalized.croppedFamily.card) + 1 ≤
        Nat.log 2 (2 * referenceFamily.card) + 1 := by
    apply Nat.add_le_add_right
    apply Nat.log_mono_right
    exact Nat.mul_le_mul_left 2 card_le
  have hlog :
      (Nat.log 2 (2 * initialNormalized.croppedFamily.card) + 1 :
          ENNReal) ≤
        (Nat.log 2 (2 * referenceFamily.card) + 1 : ENNReal) := by
    exact_mod_cast hlogNat
  have hlogOne : (1 : ENNReal) ≤
      (Nat.log 2 (2 * referenceFamily.card) + 1 : ENNReal) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hexponent : data.schedule.scaleCount + 1 ≤
      uniformLevelCount + 2 := by
    have hschedule := data.schedule.scaleCount_le
    omega
  rw [data.regularized.regularizationLoss_eq]
  unfold proposition63UniformReentryRegularizationLoss
  calc
    (8 : ENNReal) *
          (Nat.log 2 (2 * initialNormalized.croppedFamily.card) + 1 :
            ENNReal) ^ (data.schedule.scaleCount + 1) ≤
        8 * (Nat.log 2 (2 * referenceFamily.card) + 1 : ENNReal) ^
          (data.schedule.scaleCount + 1) := by
      gcongr
    _ ≤ 8 * (Nat.log 2 (2 * referenceFamily.card) + 1 : ENNReal) ^
          (uniformLevelCount + 2) := by
      exact mul_le_mul_left' (pow_le_pow_right' hlogOne hexponent) _

/-- The ambient family normalized before the dependent second Proposition 6.2
call has cardinality at most the fixed root family. -/
theorem proposition63_dependent_coarseNormalized_card_le_root
    {delta sigma initialInputLoss normalizationLoss fineReentryLoss outerLoss
      coarseInputLoss coarseNormalizationLoss : ℝ}
    {initialSource :
      PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent coarseNormalizationExponent outerLogExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {fineCurrent : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) initialNormalized fineCurrent)
    {rho : WZ2PaperRequestedScale delta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      coarseNormalizationExponent)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card) :
    coarseNormalized.croppedFamily.card ≤
      initialNormalized.croppedFamily.card := by
  have hnormalizedOuter : coarseNormalized.croppedFamily.card ≤
      outer.coarse.card := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_le_of_injective ancestorEmbedding
        ancestorEmbedding.injective)
  have houterSelected : outer.coarse.card ≤ outer.selected.family.card := by
    simpa only [Fintype.card_fin] using (Fintype.card_le_of_surjective
      outer.cover.toPaperTubeCover.parent
      outer.cover.toPaperTubeCover.parent_surjective)
  have hselectedFine : outer.selected.family.card ≤
      fineReentry.normalization.croppedFamily.card := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_le_of_injective outer.selected.embedding
        outer.selected.embedding.injective)
  have hreentryFine : fineReentry.normalization.croppedFamily.card ≤
      initialNormalized.croppedFamily.card := by
    rw [fineReentry.normalization_croppedFamily]
    simpa only [Fintype.card_fin] using (Fintype.card_le_of_injective
      fineReentry.regularized.selected.embedding
      fineReentry.regularized.selected.embedding.injective)
  exact hnormalizedOuter.trans <| houterSelected.trans <|
    hselectedFine.trans hreentryFine

/-- The fine current-shading re-entry pays at most the fixed root envelope. -/
theorem proposition63_fine_reentry_regularizationLoss_le_root
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource :
      PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (levelCount_le : data.levelCount ≤
      proposition63CanonicalNearbyLevelCount normalizationLoss) :
    data.regularized.regularizationLoss ≤
      proposition63UniformReentryRegularizationLoss
        initialNormalized.croppedFamily
        (proposition63CanonicalNearbyLevelCount normalizationLoss) :=
  proposition63_reentry_regularizationLoss_le_uniform data
    initialNormalized.croppedFamily
    (proposition63CanonicalNearbyLevelCount normalizationLoss) (by simp)
    levelCount_le

/-- The coarse current-shading re-entry also pays at most the same fixed root
envelope, using the exact ancestor/cover cardinality chain. -/
theorem proposition63_coarse_reentry_regularizationLoss_le_root
    {delta sigma initialInputLoss normalizationLoss fineReentryLoss outerLoss
      coarseInputLoss coarseNormalizationLoss coarseReentryLoss : ℝ}
    {initialSource :
      PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent outerLogExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {fineCurrent : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) initialNormalized fineCurrent)
    {rho : WZ2PaperRequestedScale delta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      normalizationExponent)
    {coarseCurrent : WZ1PaperTubeShading coarseNormalized.croppedFamily}
    (coarseReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := coarseReentryLoss) coarseNormalized coarseCurrent)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (levelCount_le : coarseReentry.levelCount ≤
      proposition63CanonicalNearbyLevelCount normalizationLoss) :
    coarseReentry.regularized.regularizationLoss ≤
      proposition63UniformReentryRegularizationLoss
        initialNormalized.croppedFamily
        (proposition63CanonicalNearbyLevelCount normalizationLoss) :=
  proposition63_reentry_regularizationLoss_le_uniform coarseReentry
    initialNormalized.croppedFamily
    (proposition63CanonicalNearbyLevelCount normalizationLoss)
    (proposition63_dependent_coarseNormalized_card_le_root fineReentry outer
      coarseNormalized ancestorEmbedding) levelCount_le

/-- The physical logarithmic envelope decreases when the geometric scale
increases inside `(0, 1]`. -/
lemma proposition63FreshBalancingEnvelope_antitone
    {delta rho : ℝ} (hdelta : 0 < delta) (hdeltaRho : delta ≤ rho) :
    proposition63FreshBalancingEnvelope rho ≤
      proposition63FreshBalancingEnvelope delta := by
  have hrho : 0 < rho := hdelta.trans_le hdeltaRho
  have hinverse : rho⁻¹ ≤ delta⁻¹ :=
    (inv_le_inv₀ hrho hdelta).2 hdeltaRho
  have hlog : Real.log rho⁻¹ ≤ Real.log delta⁻¹ :=
    Real.log_le_log (inv_pos.mpr hrho) hinverse
  unfold proposition63FreshBalancingEnvelope
  apply mul_le_mul_left'
  exact ENNReal.ofReal_mono <| by
    have hcoefficient : 0 ≤ wz2PaperBoundaryLogCoefficient := by
      dsimp only [wz2PaperBoundaryLogCoefficient]
      positivity
    gcongr

/-- Every runtime coarse normalization in a dependent step has canonical
preparation loss bounded by the fixed root-family budget.  The cardinality
comparison follows through the two re-entry selections, the recorded
coarse-family embedding, and surjectivity of the outer cover's parent map. -/
theorem proposition63_dependent_uniformPreparationLoss_le_root
    {delta sigma initialInputLoss normalizationLoss fineReentryLoss outerLoss
      coarseInputLoss coarseNormalizationLoss coarseReentryLoss : ℝ}
    {initialSource :
      PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {initialNormalizationExponent coarseNormalizationExponent
      outerLogExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource
        initialNormalizationExponent}
    {fineCurrent : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) initialNormalized fineCurrent)
    {rho : WZ2PaperRequestedScale delta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      coarseNormalizationExponent)
    {coarseCurrent : WZ1PaperTubeShading coarseNormalized.croppedFamily}
    (coarseReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := coarseReentryLoss) coarseNormalized coarseCurrent)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card) :
    proposition63UniformPreparationLoss
        coarseReentry.normalization.croppedFamily ≤
      proposition63UniformPreparationLoss initialNormalized.croppedFamily := by
  have hreentryCoarse :
      coarseReentry.normalization.croppedFamily.card ≤
        coarseNormalized.croppedFamily.card := by
    rw [coarseReentry.normalization_croppedFamily]
    simpa only [Fintype.card_fin] using (Fintype.card_le_of_injective
      coarseReentry.regularized.selected.embedding
      coarseReentry.regularized.selected.embedding.injective)
  have hnormalizedRoot :=
    proposition63_dependent_coarseNormalized_card_le_root fineReentry outer
      coarseNormalized ancestorEmbedding
  have hcard : coarseReentry.normalization.croppedFamily.card ≤
      initialNormalized.croppedFamily.card :=
    hreentryCoarse.trans hnormalizedRoot
  have hlogNat :
      Nat.log 2 coarseReentry.normalization.croppedFamily.card + 1 ≤
        Nat.log 2 initialNormalized.croppedFamily.card + 1 :=
    Nat.add_le_add_right (Nat.log_mono_right hcard) 1
  have hlog :
      ((Nat.log 2 coarseReentry.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal) ≤
        ((Nat.log 2 initialNormalized.croppedFamily.card + 1 : ℕ) :
          ENNReal) := by
    exact_mod_cast hlogNat
  unfold proposition63UniformPreparationLoss
  exact mul_le_mul hlog
    (proposition63FreshBalancingEnvelope_antitone
      initialSource.extremal.delta_pos rho.2.1) (by positivity) (by positivity)

/-- Complete numerical certificate for one coordinate of the dependent
finite full-grain schedule. -/
structure Proposition63DependentStepArithmeticData
    {delta sigma initialInputLoss normalizationLoss fineReentryLoss outerLoss
      coarseInputLoss coarseNormalizationLoss coarseReentryLoss innerLoss
      targetLoss middleLoss finalLoss epsilon₁ epsilon₃ fineWeightLoss
      coarseWeightLoss : ℝ}
    {initialSource :
      PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {fineCurrent : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) initialNormalized fineCurrent)
    {rho : WZ2PaperRequestedScale delta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      normalizationExponent)
    (coarseCurrent : WZ1PaperTubeShading coarseNormalized.croppedFamily)
    (coarseReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := coarseReentryLoss) coarseNormalized coarseCurrent)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      coarseNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index))
    (current_sub_outer : ∀ index, coarseCurrent.carrier index ⊆
      outer.croppedCoarseShading.carrier (ancestorEmbedding index))
    (ancestorRetentionFactor : ENNReal)
    (ancestorRetentionFactor_pos : 0 < ancestorRetentionFactor)
    (ancestorRetentionFactor_ne_top : ancestorRetentionFactor ≠ ⊤)
    (current_retained_mass :
      ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
        coarseCurrent.mass)
    {tau : WZ2PaperRequestedScale rho.1}
    (dependent : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      (proposition63DependentCoarseReentryOfCurrent outer coarseNormalized
        coarseCurrent coarseReentry ancestorEmbedding ancestor_tube_eq
        current_sub_outer ancestorRetentionFactor
        ancestorRetentionFactor_pos ancestorRetentionFactor_ne_top
        current_retained_mass) tau)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := dependent.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃)
    (planeMap : Point3 → Point3) (coefficient : NNReal)
    (uniformCoverBudget : ℕ)
    (ancestorRetentionBudget : ENNReal)
    (targetLeft targetRight : ENNReal) where
  lowScale : ℝ
  logScale : ℝ
  C : ENNReal
  incidenceBound : ℝ
  plane_lipschitz : LipschitzWith coefficient planeMap
  plane_unit : ∀ point ∈ (dependent.commonPropertyThree propP).union,
    ‖planeMap point‖ = 1
  plane_incidence : ∀ index point,
    ∀ hpoint : point ∈ propP.propertyOne.carrier index,
      |@Inner.inner ℝ Point3 _
        (coarseReentry.normalization.croppedFamily.tube index).direction
        (planeMap point)| ≤ incidenceBound
  reentry_target : coarseReentry.reentryNormalizationLoss ≤ targetLoss
  targetLoss_pos : 0 < targetLoss
  rho_lt_one : rho.1 < 1
  mass_slack : proposition63DependentPropertyThreeMassLoss
      rho.1 innerLogExponent * Kakeya.realRpowENN rho.1 targetLoss ≤
    Kakeya.realRpowENN rho.1 coarseReentry.reentryNormalizationLoss
  sigma_pos : 0 < sigma
  sigma_lt_one : sigma < 1
  lowScale_pos : 0 < lowScale
  lowScale_small : lowScale ≤ 1 / 10000
  low_constant : Kakeya.realRpowENN lowScale (-1) ≤
    Kakeya.realRpowENN rho.1 (-targetLoss)
  tau_sqrt : tau.1 = Real.sqrt rho.1
  tau_small : tau.1 ≤ 1 / 12
  rho_small : rho.1 ≤ 1 / 1000
  rho_le_tau : rho.1 ≤ tau.1
  tau_sq : tau.1 ^ 2 ≤ 4 * rho.1
  tau_le_one : tau.1 ≤ 1
  epsilon₁_pos : 0 < epsilon₁
  epsilon₃_pos : 0 < epsilon₃
  epsilon_sum : epsilon₁ + epsilon₃ < 1
  rho_le_logScale : rho.1 ≤ logScale
  logarithmic_bound : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
    scale ≤ logScale → ∀ k : ℕ, 0 < k →
    (k : ℝ) ≤ 100 / scale ^ 3 →
      Real.rpow scale epsilon₁ *
        (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108
  propertyThree_full :
    ∀ index point, point ∈ propP.propertyThree.carrier index →
      Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
          ENNReal.ofReal tau.1 ≤
        volume (propP.propertyThree.carrier index ∩
          Metric.closedBall point tau.1)
  axis_budget : 4 * (6 * rho.1) ^ 2 ≤
    (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2
  covering_arithmetic :
    ENNReal.ofReal
        (((5832 * Real.rpow rho.1 (sigma - outerLoss) *
            Real.rpow tau.1 (3 - sigma - 2 * innerLoss)) /
            (Real.rpow rho.1 (1 + 7 * epsilon₁ + epsilon₃) *
              tau.1 ^ 2 / 200)) *
          (2 * proposition63DependentSlabWidth rho.1 tau.1 incidenceBound
            coefficient /
            rho.1 + 2)) ≤
      C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)
  effective_one : (1 : ENNReal) ≤
    C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)
  effective_ne_top :
    C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma) ≠ ⊤
  high_constant : 10 *
      (C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)) ≤
    Kakeya.realRpowENN rho.1 (-targetLoss)
  target_le_middle : targetLoss ≤ middleLoss
  middleLoss_pos : 0 < middleLoss
  multiplicity_slack :
    (((Nat.log 2 coarseReentry.normalization.croppedFamily.card + 1 : ℕ) :
        ENNReal) * Kakeya.realRpowENN rho.1 middleLoss) ≤
      Kakeya.realRpowENN rho.1 targetLoss
  rho_small_24 : rho.1 ≤ 1 / 24
  periodic_scale : 50 * rho.1 ≤ tau.1
  tau_pos : 0 < tau.1
  boundary_scalar :
    2 * 24000000 *
        (Kakeya.realRpowENN rho.1 (-middleLoss) *
            wz2PaperBoundaryGeometryConstant + 1) *
        ENNReal.ofReal (Real.sqrt (rho.1 / tau.1)) <
      Kakeya.realRpowENN rho.1 middleLoss
  middle_le_final : middleLoss ≤ finalLoss
  finalLoss_pos : 0 < finalLoss
  balancing_slack : proposition63FreshBalancingEnvelope rho.1 *
      Kakeya.realRpowENN rho.1 finalLoss ≤
    Kakeya.realRpowENN rho.1 middleLoss
  cover_budget :
    (512 : ENNReal) *
        ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
          (9 * Kakeya.realRpowENN rho.1 (-finalLoss) *
            Kakeya.realRpowENN (1 / rho.1) (1 - sigma))) ≤
      (uniformCoverBudget : ENNReal)
  scaleFactor : ℕ
  scaleFactor_pos : 0 < scaleFactor
  rho_aligned : rho.1 = (scaleFactor : ℝ) * delta
  fine_normalizationWeight : fineReentry.normalizationWeight =
    proposition63CanonicalReentryWeight delta fineWeightLoss
  coarse_normalizationWeight : coarseReentry.normalizationWeight =
    proposition63CanonicalReentryWeight rho.1 coarseWeightLoss
  ancestorRetentionFactor_le :
    ancestorRetentionFactor ≤ ancestorRetentionBudget
  fine_levelCount : fineReentry.levelCount ≤
    proposition63CanonicalNearbyLevelCount normalizationLoss
  coarse_levelCount : coarseReentry.levelCount ≤
    proposition63CanonicalNearbyLevelCount normalizationLoss
  left_budget : targetLeft ≤
    proposition63UniformDependentLeftFactor
      initialNormalized.croppedFamily delta rho.1 sigma outerLoss finalLoss
      fineWeightLoss coarseWeightLoss outerLogExponent innerLogExponent
      tau.1 tau_pos uniformCoverBudget ancestorRetentionBudget
  right_budget : proposition63UniformDependentRightFactor
      initialNormalized.croppedFamily
      (proposition63CanonicalNearbyLevelCount normalizationLoss) ≤ targetRight

/-- Execute a fully audited scalar certificate through the unique standard
dependent LOW/HIGH-to-fine-family producer. -/
theorem Proposition63DependentStepArithmeticData.run
    {delta sigma initialInputLoss normalizationLoss fineReentryLoss outerLoss
      coarseInputLoss coarseNormalizationLoss coarseReentryLoss innerLoss
      targetLoss middleLoss finalLoss epsilon₁ epsilon₃ fineWeightLoss
      coarseWeightLoss : ℝ}
    {initialSource :
      PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {fineCurrent : WZ1PaperTubeShading initialNormalized.croppedFamily}
    {fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) initialNormalized fineCurrent}
    {rho : WZ2PaperRequestedScale delta}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent}
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    {coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      normalizationExponent}
    {coarseCurrent : WZ1PaperTubeShading coarseNormalized.croppedFamily}
    {coarseReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := coarseReentryLoss) coarseNormalized coarseCurrent}
    {ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card}
    {ancestor_tube_eq : ∀ index,
      coarseNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index)}
    {current_sub_outer : ∀ index, coarseCurrent.carrier index ⊆
      outer.croppedCoarseShading.carrier (ancestorEmbedding index)}
    {ancestorRetentionFactor : ENNReal}
    {ancestorRetentionFactor_pos : 0 < ancestorRetentionFactor}
    {ancestorRetentionFactor_ne_top : ancestorRetentionFactor ≠ ⊤}
    {current_retained_mass :
      ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
        coarseCurrent.mass}
    {tau : WZ2PaperRequestedScale rho.1}
    {dependent : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      (proposition63DependentCoarseReentryOfCurrent outer coarseNormalized
        coarseCurrent coarseReentry ancestorEmbedding ancestor_tube_eq
        current_sub_outer ancestorRetentionFactor
        ancestorRetentionFactor_pos ancestorRetentionFactor_ne_top
        current_retained_mass) tau}
    {propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := dependent.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃}
    {planeMap : Point3 → Point3} {coefficient : NNReal}
    {uniformCoverBudget : ℕ}
    {ancestorRetentionBudget : ENNReal}
    {targetLeft targetRight : ENNReal}
    (data : Proposition63DependentStepArithmeticData
      (targetLoss := targetLoss) (middleLoss := middleLoss)
      (finalLoss := finalLoss) (fineWeightLoss := fineWeightLoss)
      (coarseWeightLoss := coarseWeightLoss)
      fineReentry outer
      coarseNormalized coarseCurrent coarseReentry ancestorEmbedding
      ancestor_tube_eq current_sub_outer ancestorRetentionFactor
      ancestorRetentionFactor_pos ancestorRetentionFactor_ne_top
      current_retained_mass dependent propP planeMap coefficient
      uniformCoverBudget ancestorRetentionBudget targetLeft targetRight) :
    Nonempty (Proposition63DependentFullGrainStepData
      (firstLoss := targetLoss) (secondLoss := finalLoss)
      (sqrtScale := tau.1) fineReentry outer planeMap coefficient
      (proposition63UniformPreparationLoss initialNormalized.croppedFamily)
      uniformCoverBudget targetLeft targetRight) := by
  exact proposition63_dependentFullGrainStep_of_dependentLowHigh fineReentry
    outer coarseNormalized coarseCurrent coarseReentry ancestorEmbedding
    ancestor_tube_eq current_sub_outer ancestorRetentionFactor
    ancestorRetentionFactor_pos ancestorRetentionFactor_ne_top
    current_retained_mass dependent propP planeMap coefficient
    data.incidenceBound
    (proposition63UniformPreparationLoss initialNormalized.croppedFamily)
    uniformCoverBudget data.plane_lipschitz data.plane_unit
    data.plane_incidence
    data.reentry_target
    data.targetLoss_pos data.rho_lt_one data.mass_slack data.sigma_pos
    data.sigma_lt_one data.lowScale_pos data.lowScale_small data.low_constant
    data.tau_sqrt data.tau_small data.rho_small
    data.rho_le_tau data.tau_sq data.tau_le_one data.epsilon₁_pos
    data.epsilon₃_pos data.epsilon_sum data.logScale data.rho_le_logScale
    data.logarithmic_bound data.propertyThree_full data.axis_budget data.C
    data.covering_arithmetic data.effective_one data.effective_ne_top
    data.high_constant data.target_le_middle data.middleLoss_pos
    data.multiplicity_slack data.rho_small_24 data.periodic_scale
    data.tau_pos data.boundary_scalar data.middle_le_final
    data.finalLoss_pos data.balancing_slack data.cover_budget
    (proposition63_dependent_uniformPreparationLoss_le_root fineReentry outer
      coarseNormalized coarseReentry ancestorEmbedding)
    data.scaleFactor data.scaleFactor_pos data.rho_aligned targetLeft
    targetRight (data.left_budget.trans
      (proposition63_uniformDependentLeftFactor_le fineReentry outer
        coarseReentry ancestorRetentionFactor ancestorRetentionBudget
        data.ancestorRetentionFactor_le data.fine_normalizationWeight
        data.coarse_normalizationWeight tau.1 data.tau_pos
        uniformCoverBudget)) (by
      unfold proposition63DependentFinePullbackRight
      calc
        (coarseReentry.regularized.regularizationLoss *
              (proposition63UniformPreparationLoss
                initialNormalized.croppedFamily * 2)) *
            fineReentry.regularized.regularizationLoss ≤
          proposition63UniformDependentRightFactor
            initialNormalized.croppedFamily
            (proposition63CanonicalNearbyLevelCount normalizationLoss) := by
          unfold proposition63UniformDependentRightFactor
          gcongr
          · exact proposition63_coarse_reentry_regularizationLoss_le_root
              fineReentry outer coarseNormalized coarseReentry
                ancestorEmbedding
              data.coarse_levelCount
          · exact proposition63_fine_reentry_regularizationLoss_le_root
              fineReentry data.fine_levelCount
        _ ≤ targetRight := data.right_budget)

/-- All runtime geometric data for one coordinate, ending in the explicit
arithmetic certificate above.  Unlike a direct `FullGrainStepData` callback,
this package exposes the actual outer-coarse normalization, second cover, and
Property-(P) witness which generate the step. -/
structure Proposition63DependentStepScheduleData
    {delta sigma initialInputLoss normalizationLoss fineReentryLoss outerLoss
      targetLoss middleLoss finalLoss fineWeightLoss coarseWeightLoss : ℝ}
    {initialSource :
      PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {fineCurrent : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) initialNormalized fineCurrent)
    {rho : WZ2PaperRequestedScale delta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    (planeMap : Point3 → Point3) (coefficient : NNReal)
    (uniformCoverBudget : ℕ)
    (ancestorRetentionBudget : ENNReal)
    (targetLeft targetRight : ENNReal) where
  coarseInputLoss : ℝ
  coarseNormalizationLoss : ℝ
  coarseReentryLoss : ℝ
  innerLoss : ℝ
  epsilon₁ : ℝ
  epsilon₃ : ℝ
  coarseSource : PureWZ2ExtremalConfiguration sigma coarseInputLoss rho.1
  coarseNormalized : PureWZ2CroppedCriticalNormalizationData
    (outputLoss := coarseNormalizationLoss) coarseSource
      normalizationExponent
  coarseCurrent : WZ1PaperTubeShading coarseNormalized.croppedFamily
  coarseReentry : Proposition63CurrentShadingReentryData
    (reentryLoss := coarseReentryLoss) coarseNormalized coarseCurrent
  ancestorEmbedding :
    Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card
  ancestor_tube_eq : ∀ index,
    coarseNormalized.croppedFamily.tube index =
      outer.coarse.tube (ancestorEmbedding index)
  current_sub_outer : ∀ index, coarseCurrent.carrier index ⊆
    outer.croppedCoarseShading.carrier (ancestorEmbedding index)
  ancestorRetentionFactor : ENNReal
  ancestorRetentionFactor_pos : 0 < ancestorRetentionFactor
  ancestorRetentionFactor_ne_top : ancestorRetentionFactor ≠ ⊤
  current_retained_mass :
    ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
      coarseCurrent.mass
  tau : WZ2PaperRequestedScale rho.1
  dependent : Proposition63DependentTwoLevelCoverData
    (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
    (proposition63DependentCoarseReentryOfCurrent outer coarseNormalized
      coarseCurrent coarseReentry ancestorEmbedding ancestor_tube_eq
      current_sub_outer ancestorRetentionFactor ancestorRetentionFactor_pos
      ancestorRetentionFactor_ne_top current_retained_mass) tau
  propP : PureWZ2PropertyPData
    (sigma := sigma) (coarseShading := dependent.ambientRefined)
    (tau := tau.1) epsilon₁ epsilon₃
  arithmetic : Proposition63DependentStepArithmeticData
    (targetLoss := targetLoss) (middleLoss := middleLoss)
    (finalLoss := finalLoss) (fineWeightLoss := fineWeightLoss)
    (coarseWeightLoss := coarseWeightLoss)
    fineReentry outer coarseNormalized coarseCurrent
    coarseReentry ancestorEmbedding ancestor_tube_eq current_sub_outer
    ancestorRetentionFactor ancestorRetentionFactor_pos
    ancestorRetentionFactor_ne_top current_retained_mass dependent propP
    planeMap coefficient uniformCoverBudget ancestorRetentionBudget
    targetLeft targetRight

/-- Execute the exposed geometric and numerical package for one schedule
coordinate. -/
theorem Proposition63DependentStepScheduleData.run
    {delta sigma initialInputLoss normalizationLoss fineReentryLoss outerLoss
      targetLoss middleLoss finalLoss fineWeightLoss coarseWeightLoss : ℝ}
    {initialSource :
      PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {fineCurrent : WZ1PaperTubeShading initialNormalized.croppedFamily}
    {fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) initialNormalized fineCurrent}
    {rho : WZ2PaperRequestedScale delta}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent}
    {planeMap : Point3 → Point3} {coefficient : NNReal}
    {uniformCoverBudget : ℕ}
    {ancestorRetentionBudget : ENNReal}
    {targetLeft targetRight : ENNReal}
    (data : Proposition63DependentStepScheduleData
      (targetLoss := targetLoss) (middleLoss := middleLoss)
      (finalLoss := finalLoss) (fineWeightLoss := fineWeightLoss)
      (coarseWeightLoss := coarseWeightLoss)
      (innerLogExponent := innerLogExponent)
      fineReentry outer planeMap coefficient
      uniformCoverBudget ancestorRetentionBudget targetLeft targetRight) :
    Nonempty (Proposition63DependentFullGrainStepData
      (firstLoss := targetLoss) (secondLoss := finalLoss)
      (sqrtScale := data.tau.1) fineReentry outer planeMap coefficient
      (proposition63UniformPreparationLoss initialNormalized.croppedFamily)
      uniformCoverBudget targetLeft targetRight) :=
  data.arithmetic.run

/-- Root finite iteration whose per-coordinate callback exposes the complete
dependent paper construction and scalar ledger. -/
theorem proposition63_finite_dependent_arithmetic_iteration_from_root
    {sigma inputLoss normalizationLoss densityLoss currentLoss weightLoss
      reentryLoss stickyLoss firstLoss middleLoss secondLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent logExponent innerLogExponent N : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss)
    (planeMap : Point3 → Point3)
    (requested : Fin N → WZ2PaperRequestedScale delta)
    (queryScale sqrtScale spatialScale variationScale : ℕ → ℝ)
    (constant : ENNReal)
    (leftFactor rightFactor : ℕ → ENNReal)
    (uniformCoverBudget : ℕ → ℕ)
    (ancestorRetentionBudget : ℕ → ENNReal)
    (coarseWeightLoss : ℕ → ℝ)
    (parameters : Proposition63RootFiniteReentryParameters
      (currentLoss := currentLoss) (weightLoss := weightLoss)
      (reentryLoss := reentryLoss) (N := N) root leftFactor rightFactor)
    (coefficient : NNReal)
    (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (planeLipschitz : LipschitzWith coefficient planeMap)
    (variationBudget : ∀ index, index < N →
      (coefficient : ℝ) * spatialScale index ≤ variationScale index)
    (hSticky : ∀ reentrySource :
        PureWZ2ExtremalConfiguration sigma reentryLoss delta,
      ∀ reentryNormalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := parameters.reentryNormalizationLoss) reentrySource
          normalizationExponent,
      ∀ rho : WZ2PaperRequestedScale delta,
        Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
        rho.1 ≤ Real.rpow delta stickyLoss →
        Nonempty (PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          reentryNormalized.croppedRefined rho logExponent))
    (requested_lower : ∀ index,
      Real.rpow delta (1 - stickyLoss) ≤ (requested index).1)
    (requested_upper : ∀ index,
      (requested index).1 ≤ Real.rpow delta stickyLoss)
    (query_eq : ∀ index (index_lt : index < N),
      queryScale index = (requested ⟨index, index_lt⟩).1)
    (query_small : ∀ index (index_lt : index < N),
      queryScale index ≤ 1 / 4)
    (sqrt_eq : ∀ index (index_lt : index < N),
      sqrtScale index = Real.sqrt (queryScale index))
    (coverBudget_pos : ∀ index, index < N →
      0 < uniformCoverBudget index)
    (target_constant : ∀ index (index_lt : index < N),
      Kakeya.realRpowENN (queryScale index) (-secondLoss) ≤ constant)
    (rho_small : ∀ index (index_lt : index < N),
      queryScale index ≤ 1 / 12)
    (stepData : ∀ index : ℕ, ∀ index_lt : index < N,
      ∀ current : WZ1PaperTubeShading root.normalization.croppedFamily,
        ∀ current_sub : PaperIsSubshading current
          root.normalization.croppedRefined,
        ∀ current_cubical : WZ1PaperIsCubicalShading current,
        ∀ current_multiplicity : ∀ point ∈ current.union,
          current.pointMultiplicity point =
            root.normalization.croppedRefined.pointMultiplicity point,
        ∀ current_mass_ledger :
          (∏ prior ∈ Finset.range index, leftFactor prior) *
              root.normalization.croppedRefined.mass ≤
            (∏ prior ∈ Finset.range index, rightFactor prior) * current.mass,
        ∀ current_mass_pos : 0 < current.mass,
        ∀ data : Proposition63CurrentShadingReentryData
          (reentryLoss := reentryLoss) root.normalization current,
        data.normalizationWeight =
          proposition63CanonicalReentryWeight delta weightLoss →
        data.levelCount =
          proposition63CanonicalNearbyLevelCount normalizationLoss →
        ∀ sticky : PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          data.normalization.croppedRefined
          (requested ⟨index, index_lt⟩) logExponent,
          Nonempty (Proposition63DependentStepScheduleData
            (targetLoss := firstLoss) (middleLoss := middleLoss)
            (finalLoss := secondLoss) (fineWeightLoss := weightLoss)
            (coarseWeightLoss := coarseWeightLoss index)
            (innerLogExponent := innerLogExponent)
            data sticky planeMap coefficient (uniformCoverBudget index)
            (ancestorRetentionBudget index)
            (leftFactor index)
            (rightFactor index))) :
    ∃ final : WZ1PaperTubeShading root.normalization.croppedFamily,
      PaperIsSubshading final root.normalization.croppedRefined ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        final.pointMultiplicity point =
          root.normalization.croppedRefined.pointMultiplicity point) ∧
      (∀ index, index < N → ∀ first ∈ final.union,
        ∀ second ∈ final.union, dist first second ≤ spatialScale index →
          dist (planeMap first) (planeMap second) ≤ variationScale index) ∧
      (∀ index, index < N → ∀ point ∈ final.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (final.union ∩ Metric.closedBall point
              (Real.sqrt (queryScale index))))
          (queryScale index) (1 - sigma) constant) ∧
      (∏ index ∈ Finset.range N, leftFactor index) *
          root.normalization.croppedRefined.mass ≤
        (∏ index ∈ Finset.range N, rightFactor index) * final.mass ∧
      0 < final.mass := by
  apply proposition63_finite_dependent_fullGrain_iteration_from_root root
    planeMap requested queryScale sqrtScale spatialScale variationScale
    constant leftFactor rightFactor
    (fun _ => proposition63UniformPreparationLoss
      root.normalization.croppedFamily)
    uniformCoverBudget parameters coefficient hcoefficientOne
    planeLipschitz variationBudget hSticky requested_lower requested_upper
    query_eq query_small sqrt_eq coverBudget_pos target_constant rho_small
  intro index index_lt current current_sub current_cubical
    current_multiplicity current_mass_ledger current_mass_pos data
    normalization_weight levelCount_eq sticky
  let packaged := Classical.choice <|
    stepData index index_lt current current_sub current_cubical
      current_multiplicity current_mass_ledger current_mass_pos data
      normalization_weight levelCount_eq sticky
  have hsqrtRequested :
      sqrtScale index =
        Real.sqrt (requested ⟨index, index_lt⟩).1 := by
    rw [← query_eq index index_lt]
    exact sqrt_eq index index_lt
  have htau : packaged.tau.1 = sqrtScale index :=
    packaged.arithmetic.tau_sqrt.trans hsqrtRequested.symm
  rw [← htau]
  exact packaged.run

end Kakeya.Assouad.PureWZ2

end
