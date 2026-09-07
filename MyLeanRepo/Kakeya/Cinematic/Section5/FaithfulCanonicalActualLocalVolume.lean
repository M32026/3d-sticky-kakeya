import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedLocalTargetBranches
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedSelectedLayerLocalVolumeBranches
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalActualOrdinaryInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalActualSelectedLayerBounds
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedLayerMassCancellation

/-!
# Actual fixed-bin volume at the faithful canonical scales

This module feeds the concrete selected-cardinality dichotomy through the
selected-layer mass cancellation and then applies the canonical coefficient
ledger.  The dyadic retention loss is multiplied before ambient-bin
summation, so it is counted exactly once.
-/

open MeasureTheory

namespace Kakeya.Cinematic

noncomputable def faithfulCanonicalActualBranchLocalTarget
    (branchConstant parentConstant retentionConstant clusterConstant
      D propositionExponent coverExponent metricExponent
      geometricConstant delta : ℝ)
    (mu : ℕ) : ℝ :=
  branchConstant *
      faithfulCanonicalFinalCoefficientConstant
        parentConstant retentionConstant clusterConstant D
        propositionExponent coverExponent *
      Real.rpow delta
        (-(faithfulCanonicalStructuredScaleLoss
              (propositionExponent +
                (7 / 2 : ℝ) * coverExponent)
              metricExponent +
            faithfulCanonicalOrdinaryLoss metricExponent)) *
      (geometricConstant * delta) *
      Real.rpow (mu : ℝ) (-3 / 2 : ℝ)

noncomputable def faithfulCanonicalActualCommonConstant
    (parentConstant retentionConstant clusterConstant D
      C_positive C_singleton coverExponent tangency : ℝ) : ℝ :=
  max
    ((4 *
        faithfulCanonicalPositiveBranchConstant
          C_positive tangency) *
      faithfulCanonicalFinalCoefficientConstant
        parentConstant retentionConstant clusterConstant D
        C_positive coverExponent)
    ((4 *
        faithfulCanonicalSingletonBranchConstant
          C_singleton tangency) *
      faithfulCanonicalFinalCoefficientConstant
        parentConstant retentionConstant clusterConstant D
        C_singleton coverExponent)

noncomputable def faithfulCanonicalActualCommonLocalTarget
    (parentConstant retentionConstant clusterConstant D
      C_positive C_singleton coverExponent tangency metricExponent
      geometricConstant delta : ℝ)
    (mu : ℕ) : ℝ :=
  faithfulCanonicalActualCommonConstant
      parentConstant retentionConstant clusterConstant D
      C_positive C_singleton coverExponent tangency *
    Real.rpow delta
      (-faithfulCanonicalFullLoss
        (faithfulCanonicalBranchParameter
          D C_positive C_singleton)
        metricExponent) *
    (geometricConstant * delta) *
    Real.rpow (mu : ℝ) (-3 / 2 : ℝ)

lemma faithful_canonical_actual_branch_targets_le_common
    (parentConstant retentionConstant clusterConstant D
      C_positive C_singleton coverExponent tangency metricExponent
      geometricConstant delta : ℝ)
    (mu : ℕ)
    (hparent : 0 < parentConstant)
    (hretention : 0 < retentionConstant)
    (hcluster : 0 < clusterConstant)
    (hD : 1 ≤ D)
    (hC_positive : 1 ≤ C_positive)
    (hC_singleton : 1 ≤ C_singleton)
    (hcover :
      coverExponent = Real.log D / Real.log 2)
    (htangency : 1 ≤ tangency)
    (hmetric : 0 < metricExponent)
    (hmetricUpper : metricExponent ≤ 1 / 16)
    (hgeometric : 0 ≤ geometricConstant)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1) :
    faithfulCanonicalActualBranchLocalTarget
        (4 *
          faithfulCanonicalPositiveBranchConstant
            C_positive tangency)
        parentConstant retentionConstant clusterConstant D
        C_positive coverExponent metricExponent geometricConstant
        delta mu ≤
      faithfulCanonicalActualCommonLocalTarget
        parentConstant retentionConstant clusterConstant D
        C_positive C_singleton coverExponent tangency metricExponent
        geometricConstant delta mu ∧
    faithfulCanonicalActualBranchLocalTarget
        (4 *
          faithfulCanonicalSingletonBranchConstant
            C_singleton tangency)
        parentConstant retentionConstant clusterConstant D
        C_singleton coverExponent metricExponent geometricConstant
        delta mu ≤
      faithfulCanonicalActualCommonLocalTarget
        parentConstant retentionConstant clusterConstant D
        C_positive C_singleton coverExponent tangency metricExponent
        geometricConstant delta mu := by
  let branchParameter :=
    faithfulCanonicalBranchParameter
      D C_positive C_singleton
  let positiveConstant :=
    (4 *
        faithfulCanonicalPositiveBranchConstant
          C_positive tangency) *
      faithfulCanonicalFinalCoefficientConstant
        parentConstant retentionConstant clusterConstant D
        C_positive coverExponent
  let singletonConstant :=
    (4 *
        faithfulCanonicalSingletonBranchConstant
          C_singleton tangency) *
      faithfulCanonicalFinalCoefficientConstant
        parentConstant retentionConstant clusterConstant D
        C_singleton coverExponent
  let commonConstant := max positiveConstant singletonConstant
  have hpositiveParameter :
      C_positive + (7 / 2 : ℝ) * coverExponent ≤
        branchParameter := by
    dsimp only [branchParameter,
      faithfulCanonicalBranchParameter]
    rw [hcover]
    linarith [le_max_left C_positive C_singleton]
  have hsingletonParameter :
      C_singleton + (7 / 2 : ℝ) * coverExponent ≤
        branchParameter := by
    dsimp only [branchParameter,
      faithfulCanonicalBranchParameter]
    rw [hcover]
    linarith [le_max_right C_positive C_singleton]
  have hstructuredPositive :
      faithfulCanonicalStructuredScaleLoss
            (C_positive +
              (7 / 2 : ℝ) * coverExponent)
            metricExponent +
          faithfulCanonicalOrdinaryLoss metricExponent ≤
        faithfulCanonicalFullLoss
          branchParameter metricExponent := by
    have hmono :
        faithfulCanonicalStructuredScaleLoss
            (C_positive +
              (7 / 2 : ℝ) * coverExponent)
            metricExponent ≤
          faithfulCanonicalStructuredScaleLoss
            branchParameter metricExponent := by
      dsimp only [faithfulCanonicalStructuredScaleLoss]
      gcongr
    exact
      (add_le_add hmono (le_refl _)).trans
        (faithfulCanonicalStructuredScaleLoss_add_ordinary_le_full
          branchParameter metricExponent hmetric.le hmetricUpper)
  have hstructuredSingleton :
      faithfulCanonicalStructuredScaleLoss
            (C_singleton +
              (7 / 2 : ℝ) * coverExponent)
            metricExponent +
          faithfulCanonicalOrdinaryLoss metricExponent ≤
        faithfulCanonicalFullLoss
          branchParameter metricExponent := by
    have hmono :
        faithfulCanonicalStructuredScaleLoss
            (C_singleton +
              (7 / 2 : ℝ) * coverExponent)
            metricExponent ≤
          faithfulCanonicalStructuredScaleLoss
            branchParameter metricExponent := by
      dsimp only [faithfulCanonicalStructuredScaleLoss]
      gcongr
    exact
      (add_le_add hmono (le_refl _)).trans
        (faithfulCanonicalStructuredScaleLoss_add_ordinary_le_full
          branchParameter metricExponent hmetric.le hmetricUpper)
  have hpowerPositive :
      Real.rpow delta
          (-(faithfulCanonicalStructuredScaleLoss
              (C_positive +
                (7 / 2 : ℝ) * coverExponent)
              metricExponent +
            faithfulCanonicalOrdinaryLoss metricExponent)) ≤
        Real.rpow delta
          (-faithfulCanonicalFullLoss
            branchParameter metricExponent) :=
    Real.rpow_le_rpow_of_exponent_ge
      hdelta hdeltaOne (by linarith)
  have hpowerSingleton :
      Real.rpow delta
          (-(faithfulCanonicalStructuredScaleLoss
              (C_singleton +
                (7 / 2 : ℝ) * coverExponent)
              metricExponent +
            faithfulCanonicalOrdinaryLoss metricExponent)) ≤
        Real.rpow delta
          (-faithfulCanonicalFullLoss
            branchParameter metricExponent) :=
    Real.rpow_le_rpow_of_exponent_ge
      hdelta hdeltaOne (by linarith)
  have hpositiveConstantNonneg :
      0 ≤ positiveConstant := by
    have hbranch :
        0 <
          faithfulCanonicalPositiveBranchConstant
            C_positive tangency := by
      dsimp only [faithfulCanonicalPositiveBranchConstant]
      exact mul_pos
        (mul_pos
          (mul_pos (by norm_num)
            (mul_pos (by norm_num)
              (Real.sqrt_pos.2 (by norm_num))))
          (zero_lt_one.trans_le hC_positive))
        (Real.rpow_pos_of_pos
          (zero_lt_one.trans_le htangency) _)
    have hfinal :
        0 <
          faithfulCanonicalFinalCoefficientConstant
            parentConstant retentionConstant clusterConstant D
            C_positive coverExponent := by
      dsimp only [faithfulCanonicalFinalCoefficientConstant]
      exact mul_pos
        (mul_pos
          (Real.rpow_pos_of_pos hparent _)
          hretention)
        (mul_pos
          (Real.rpow_pos_of_pos hcluster _)
          (Real.rpow_pos_of_pos
            (mul_pos (zero_lt_one.trans_le hD)
              (Real.rpow_pos_of_pos
                (mul_pos (by norm_num) hcluster) _)) _))
    dsimp only [positiveConstant]
    positivity
  have hsingletonConstantNonneg :
      0 ≤ singletonConstant := by
    have hbranch :
        0 <
          faithfulCanonicalSingletonBranchConstant
            C_singleton tangency := by
      dsimp only [faithfulCanonicalSingletonBranchConstant]
      exact mul_pos
        (mul_pos
          (mul_pos (by norm_num)
            (mul_pos
              (mul_pos (by norm_num)
                (Real.sqrt_pos.2 (by norm_num)))
              (Real.rpow_pos_of_pos (by norm_num) _)))
          (zero_lt_one.trans_le hC_singleton))
        (Real.rpow_pos_of_pos
          (zero_lt_one.trans_le htangency) _)
    have hfinal :
        0 <
          faithfulCanonicalFinalCoefficientConstant
            parentConstant retentionConstant clusterConstant D
            C_singleton coverExponent := by
      dsimp only [faithfulCanonicalFinalCoefficientConstant]
      exact mul_pos
        (mul_pos
          (Real.rpow_pos_of_pos hparent _)
          hretention)
        (mul_pos
          (Real.rpow_pos_of_pos hcluster _)
          (Real.rpow_pos_of_pos
            (mul_pos (zero_lt_one.trans_le hD)
              (Real.rpow_pos_of_pos
                (mul_pos (by norm_num) hcluster) _)) _))
    dsimp only [singletonConstant]
    positivity
  have hcommonNonneg :
      0 ≤ commonConstant :=
    hpositiveConstantNonneg.trans
      (le_max_left _ _)
  have hgeomDelta :
      0 ≤ geometricConstant * delta :=
    mul_nonneg hgeometric hdelta.le
  have hmuPower :
      0 ≤ Real.rpow (mu : ℝ) (-3 / 2 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg mu) _
  have hpositivePowerNonneg :
      0 ≤
        Real.rpow delta
          (-(faithfulCanonicalStructuredScaleLoss
              (C_positive +
                (7 / 2 : ℝ) * coverExponent)
              metricExponent +
            faithfulCanonicalOrdinaryLoss metricExponent)) :=
    Real.rpow_nonneg hdelta.le _
  have hsingletonPowerNonneg :
      0 ≤
        Real.rpow delta
          (-(faithfulCanonicalStructuredScaleLoss
              (C_singleton +
                (7 / 2 : ℝ) * coverExponent)
              metricExponent +
            faithfulCanonicalOrdinaryLoss metricExponent)) :=
    Real.rpow_nonneg hdelta.le _
  constructor
  · dsimp only [faithfulCanonicalActualBranchLocalTarget,
      faithfulCanonicalActualCommonLocalTarget,
      faithfulCanonicalActualCommonConstant]
    change
      positiveConstant * _ *
            (geometricConstant * delta) * _ ≤
        commonConstant * _ *
            (geometricConstant * delta) * _
    apply mul_le_mul_of_nonneg_right _ hmuPower
    apply mul_le_mul_of_nonneg_right _ hgeomDelta
    calc
      positiveConstant * _ ≤ commonConstant * _ :=
        mul_le_mul_of_nonneg_right
          (le_max_left _ _) hpositivePowerNonneg
      _ ≤ commonConstant * _ :=
        mul_le_mul_of_nonneg_left hpowerPositive hcommonNonneg
  · dsimp only [faithfulCanonicalActualBranchLocalTarget,
      faithfulCanonicalActualCommonLocalTarget,
      faithfulCanonicalActualCommonConstant]
    change
      singletonConstant * _ *
            (geometricConstant * delta) * _ ≤
        commonConstant * _ *
            (geometricConstant * delta) * _
    apply mul_le_mul_of_nonneg_right _ hmuPower
    apply mul_le_mul_of_nonneg_right _ hgeomDelta
    calc
      singletonConstant * _ ≤ commonConstant * _ :=
        mul_le_mul_of_nonneg_right
          (le_max_right _ _) hsingletonPowerNonneg
      _ ≤ commonConstant * _ :=
        mul_le_mul_of_nonneg_left hpowerSingleton hcommonNonneg

lemma faithful_canonical_actual_branch_max_le_common
    (diameter T C_R C_inc D C_positive C_singleton tangency
      metricExponent geometricConstant delta : ℝ)
    (mu : ℕ)
    (hdiameter : 0 < diameter)
    (hT : 0 < T)
    (hC_R : 0 < C_R)
    (hC_inc : 0 < C_inc)
    (hD : 1 ≤ D)
    (hC_positive : 1 ≤ C_positive)
    (hC_singleton : 1 ≤ C_singleton)
    (htangency : 1 ≤ tangency)
    (hmetric : 0 < metricExponent)
    (hmetricUpper : metricExponent ≤ 1 / 16)
    (hgeometric : 0 ≤ geometricConstant)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1) :
    let coverExponent := Real.log D / Real.log 2
    let parentConstant :=
      faithfulCanonicalParentScaleConstant
        diameter T C_R C_inc metricExponent
    let retentionConstant :=
      faithfulCanonicalRetentionInverseConstant
        diameter T metricExponent
    let clusterConstant :=
      faithfulCanonicalClusterConstant T C_R metricExponent
    let positiveTarget :=
      faithfulCanonicalActualBranchLocalTarget
        (4 *
          faithfulCanonicalPositiveBranchConstant
            C_positive tangency)
        parentConstant retentionConstant clusterConstant D
        C_positive coverExponent metricExponent geometricConstant
        delta mu
    let singletonTarget :=
      faithfulCanonicalActualBranchLocalTarget
        (4 *
          faithfulCanonicalSingletonBranchConstant
            C_singleton tangency)
        parentConstant retentionConstant clusterConstant D
        C_singleton coverExponent metricExponent geometricConstant
        delta mu
    let commonTarget :=
      faithfulCanonicalActualCommonLocalTarget
        parentConstant retentionConstant clusterConstant D
        C_positive C_singleton coverExponent tangency metricExponent
        geometricConstant delta mu
    max positiveTarget singletonTarget ≤ commonTarget := by
  dsimp only
  have hparent :
      0 <
        faithfulCanonicalParentScaleConstant
          diameter T C_R C_inc metricExponent := by
    have hincidence :
        0 <
          faithfulCanonicalIncidenceConstant
            T C_R C_inc metricExponent := by
      let radicand :=
        32 * C_R *
          Real.rpow
            (96 *
              Real.rpow (2 * T)
                (metricExponent ^ 2))
            (1 / metricExponent) *
          Real.rpow 24
            (1 / (metricExponent ^ 2))
      have hproduct :
          0 ≤ C_inc * Real.sqrt radicand :=
        mul_nonneg hC_inc.le (Real.sqrt_nonneg radicand)
      dsimp only [faithfulCanonicalIncidenceConstant]
      exact add_pos_of_nonneg_of_pos hproduct zero_lt_one
    have hretention :
        0 <
          faithfulCanonicalRetentionConstant
            diameter T metricExponent := by
      dsimp only [faithfulCanonicalRetentionConstant]
      exact mul_pos
        (Real.rpow_pos_of_pos
          (mul_pos (by norm_num) hdiameter) _)
        (Real.rpow_pos_of_pos
          (mul_pos (by norm_num) hT) _)
    dsimp only [faithfulCanonicalParentScaleConstant]
    positivity
  have hretention :
      0 <
        faithfulCanonicalRetentionInverseConstant
          diameter T metricExponent := by
    dsimp only [faithfulCanonicalRetentionInverseConstant]
    exact mul_pos
      (Real.rpow_pos_of_pos
        (mul_pos (by norm_num) hdiameter) _)
      (Real.rpow_pos_of_pos
        (mul_pos (by norm_num) hT) _)
  have hcluster :
      0 <
        faithfulCanonicalClusterConstant
          T C_R metricExponent := by
    dsimp only [faithfulCanonicalClusterConstant]
    exact mul_pos
      (mul_pos (by norm_num) hC_R)
      (Real.rpow_pos_of_pos
        (mul_pos (by norm_num)
          (Real.rpow_pos_of_pos
            (mul_pos (by norm_num) hT) _)) _)
  rcases faithful_canonical_actual_branch_targets_le_common
      (faithfulCanonicalParentScaleConstant
        diameter T C_R C_inc metricExponent)
      (faithfulCanonicalRetentionInverseConstant
        diameter T metricExponent)
      (faithfulCanonicalClusterConstant T C_R metricExponent)
      D C_positive C_singleton (Real.log D / Real.log 2) tangency
      metricExponent geometricConstant delta mu
      hparent hretention hcluster hD hC_positive hC_singleton rfl
      htangency hmetric hmetricUpper hgeometric hdelta hdeltaOne with
    ⟨hpositive, hsingleton⟩
  exact max_le hpositive hsingleton

theorem faithful_canonical_actual_fixed_bin_volume_le
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K D delta diameter metricExponent tRep DeltaRep C_R₀ : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter metricExponent (metricExponent ^ 2)
        tRep DeltaRep C_R₀)
    (center : C2Function)
    (hE : MeasurableSet E)
    {C_R C_count C_shading C_volume : ℝ}
    (fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume)
    (coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE fineSetup)
    {massExponent : ℝ}
    (refinement : AmbientRestrictedLargeBinRefinementData
      data center hE fineSetup coarseSetup massExponent)
    (incidence : AmbientRestrictedJointIncidenceSetupData
      data center hE fineSetup coarseSetup refinement)
    (cluster : AmbientRestrictedJointClusterSetupData
      (D := D) data center hE fineSetup coarseSetup refinement incidence)
    (T C_KT C_out C_inc outerLoss C_positive C_singleton : ℝ)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hdiameter : 0 < diameter)
    (hT : 0 < T)
    (htT : tRep ≤ T)
    (hC_R : 0 < C_R)
    (hC_shading : 0 < C_shading)
    (hC_KT : 0 < C_KT)
    (hC_out : 0 < C_out)
    (hC_inc : 0 < C_inc)
    (hD : 1 ≤ D)
    (hmetric : 0 < metricExponent)
    (hC_positive : 1 ≤ C_positive)
    (hC_singleton : 1 ≤ C_singleton)
    (houterLoss : 0 ≤ outerLoss)
    (hKT : data.ambientSource.HasKatzTaoBound delta C_KT)
    (hpositiveLog :
      0 ≤
        Real.log
          (8 * (cluster.cover.centers.card : ℝ) *
              ((data.ambientSource.cluster
                center (3 * tRep)).card : ℝ) /
            (2 ^ incidence.heavySetup.supportLevel : ℕ)))
    (hsingletonLog :
      0 ≤
        Real.log
          (2 *
            ((data.ambientSource.cluster
              center (3 * tRep)).card : ℝ)))
    (hlogLoss :
      incidence.heavySetup.heavyLogLoss ≤
        Real.rpow delta (-(metricExponent ^ 3)))
    (hpositiveOrdinary :
      faithfulCanonicalOrdinaryDyadicLoss
          outerLoss
          (Real.log
            (8 * (cluster.cover.centers.card : ℝ) *
                ((data.ambientSource.cluster
                  center (3 * tRep)).card : ℝ) /
              (2 ^ incidence.heavySetup.supportLevel : ℕ)))
          refinement.layerCount data.ambientSource.card
          fineSetup.fine.card refinement.selected.card ≤
        Real.rpow delta
          (-faithfulCanonicalOrdinaryLoss metricExponent))
    (hsingletonOrdinary :
      faithfulCanonicalOrdinaryDyadicLoss
          outerLoss
          (Real.log
            (2 *
              ((data.ambientSource.cluster
                center (3 * tRep)).card : ℝ)))
          refinement.layerCount data.ambientSource.card
          fineSetup.fine.card refinement.selected.card ≤
        Real.rpow delta
          (-faithfulCanonicalOrdinaryLoss metricExponent))
    (cardinalityResult :
      AmbientRestrictedSelectedCardinalityResultOfFiber
        refinement.selected.card
        cluster.cover.centers.card
        (data.ambientSource.cluster center (3 * tRep)).card
        (2 ^ incidence.heavySetup.supportLevel)
        data.mu 4
        (Nat.log2 refinement.selected.card + 1)
        incidence.heavySetup.degreeLoss
        (Nat.log2 incidence.heavySetup.ambient.card + 1)
        incidence.retention
        (faithfulCanonicalParentArea C_out DeltaRep C_R tRep /
          (((2 : ENNReal) ^ refinement.layer.val *
            refinement.cutoff).toReal))
        (faithfulCanonicalCutoffParentScale
          delta tRep DeltaRep C_R C_inc
          incidence.heavySetup.heavyLogLoss metricExponent
          incidence.retention incidence.heavySetup.degreeLoss)
        C_positive C_singleton coarseSetup.tangency cluster.A) :
    let coverExponent := Real.log D / Real.log 2
    let geometricConstant :=
      Real.sqrt (3 * C_KT) *
          Real.rpow (4 * C_out ^ 2) (1 / 4 : ℝ) *
          Real.rpow
            (2 * C_shading * Real.sqrt C_shading)
            (3 / 4 : ℝ) /
        Real.sqrt C_R
    let positiveTarget :=
      faithfulCanonicalActualBranchLocalTarget
        (4 *
          faithfulCanonicalPositiveBranchConstant
            C_positive coarseSetup.tangency)
        (faithfulCanonicalParentScaleConstant
          diameter T C_R C_inc metricExponent)
        (faithfulCanonicalRetentionInverseConstant
          diameter T metricExponent)
        (faithfulCanonicalClusterConstant T C_R metricExponent)
        D C_positive coverExponent metricExponent geometricConstant
        delta data.mu
    let singletonTarget :=
      faithfulCanonicalActualBranchLocalTarget
        (4 *
          faithfulCanonicalSingletonBranchConstant
            C_singleton coarseSetup.tangency)
        (faithfulCanonicalParentScaleConstant
          diameter T C_R C_inc metricExponent)
        (faithfulCanonicalRetentionInverseConstant
          diameter T metricExponent)
        (faithfulCanonicalClusterConstant T C_R metricExponent)
        D C_singleton coverExponent metricExponent geometricConstant
        delta data.mu
    ENNReal.ofReal outerLoss *
        volume (ambientRestrictedSet data center) ≤
      ENNReal.ofReal (max positiveTarget singletonTarget) *
        (data.ambientSource.cluster center (3 * tRep)).card := by
  dsimp only
  let parentScale :=
    faithfulCanonicalCutoffParentScale
      delta tRep DeltaRep C_R C_inc
      incidence.heavySetup.heavyLogLoss metricExponent
      incidence.retention incidence.heavySetup.degreeLoss
  let parentArea :=
    faithfulCanonicalParentArea C_out DeltaRep C_R tRep
  let cardUpper :=
    faithfulCanonicalAmbientCardUpper C_KT tRep delta
  let coverExponent := Real.log D / Real.log 2
  let geometricConstant :=
    Real.sqrt (3 * C_KT) *
        Real.rpow (4 * C_out ^ 2) (1 / 4 : ℝ) *
        Real.rpow
          (2 * C_shading * Real.sqrt C_shading)
          (3 / 4 : ℝ) /
      Real.sqrt C_R
  let positiveTarget :=
    faithfulCanonicalActualBranchLocalTarget
      (4 *
        faithfulCanonicalPositiveBranchConstant
          C_positive coarseSetup.tangency)
      (faithfulCanonicalParentScaleConstant
        diameter T C_R C_inc metricExponent)
      (faithfulCanonicalRetentionInverseConstant
        diameter T metricExponent)
      (faithfulCanonicalClusterConstant T C_R metricExponent)
      D C_positive coverExponent metricExponent geometricConstant
      delta data.mu
  let singletonTarget :=
    faithfulCanonicalActualBranchLocalTarget
      (4 *
        faithfulCanonicalSingletonBranchConstant
          C_singleton coarseSetup.tangency)
      (faithfulCanonicalParentScaleConstant
        diameter T C_R C_inc metricExponent)
      (faithfulCanonicalRetentionInverseConstant
        diameter T metricExponent)
      (faithfulCanonicalClusterConstant T C_R metricExponent)
      D C_singleton coverExponent metricExponent geometricConstant
      delta data.mu
  have hDelta : 0 < DeltaRep :=
    hdelta.trans_le data.delta_le_DeltaRep
  have hparentScale : 0 ≤ parentScale := by
    dsimp only [parentScale, faithfulCanonicalCutoffParentScale]
    exact ambientRestrictedParentTangencyScale_nonneg
      _ 4 incidence.heavySetup.heavyLogLoss incidence.retention
      incidence.heavySetup.degreeLoss
      (add_nonneg
        (mul_nonneg hC_inc.le (Real.sqrt_nonneg _))
        (by norm_num))
      (by norm_num) incidence.retention_pos.le
  have hparentArea : 0 ≤ parentArea := by
    dsimp only [parentArea, faithfulCanonicalParentArea]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg C_out))
        hDelta.le)
      (Real.sqrt_nonneg _)
  have hcardUpper : 0 ≤ cardUpper := by
    dsimp only [cardUpper, faithfulCanonicalAmbientCardUpper]
    exact mul_nonneg hC_KT.le <|
      div_nonneg
        (mul_nonneg (by norm_num) data.tRep_pos.le)
        hdelta.le
  have hambientCard :
      ((data.ambientSource.cluster center (3 * tRep)).card : ℝ) ≤
        cardUpper := by
    dsimp only [cardUpper, faithfulCanonicalAmbientCardUpper]
    exact ambient_cluster_katz_tao_cardinality
      data.ambientSource center delta tRep C_KT hdelta
      data.tRep_pos
      (data.delta_le_DeltaRep.trans data.DeltaRep_le_tRep) hKT
  have hvolume :=
    ambient_restricted_selected_layer_local_volume_branches
      selected_layer_mass_cancellation data center hE fineSetup
      coarseSetup refinement incidence.degreeSetup incidence.q_fiber
      incidence.fiberBound 4 incidence.heavySetup
      cluster.radius cluster.A cluster.cover C_positive C_singleton
      incidence.retention parentArea parentScale cardUpper
      cluster.A_ge_one hC_positive hC_singleton
      incidence.retention_pos (by norm_num) hparentArea
      hparentScale hC_shading.le hdelta.le hcardUpper hambientCard
      hpositiveLog hsingletonLog cardinalityResult
  rcases faithful_canonical_actual_selected_layer_coefficients_le
      data center hE fineSetup coarseSetup refinement incidence cluster
      T C_KT C_out C_inc outerLoss
      (Real.log
        (8 * (cluster.cover.centers.card : ℝ) *
            ((data.ambientSource.cluster
              center (3 * tRep)).card : ℝ) /
          (2 ^ incidence.heavySetup.supportLevel : ℕ)))
      (Real.log
        (2 *
          ((data.ambientSource.cluster
            center (3 * tRep)).card : ℝ)))
      C_positive C_singleton hdelta hdeltaOne hdiameter hT htT
      hC_R hC_shading hC_KT hC_out hC_inc hD hmetric
      (zero_le_one.trans hC_positive) (zero_le_one.trans hC_singleton)
      houterLoss hpositiveLog
      hsingletonLog hlogLoss hpositiveOrdinary hsingletonOrdinary with
    ⟨hpositive, hsingleton⟩
  have hpositive' :
      outerLoss *
          ambientRestrictedLayerLinearizedLocalCoefficient
            (ambientRestrictedPositiveLayerBaseCoefficientOfFiber
              4
              (((Nat.log2 refinement.selected.card + 1 : ℕ) : ℝ))
              (incidence.heavySetup.degreeLoss : ℝ)
              (((Nat.log2 incidence.heavySetup.ambient.card + 1 : ℕ) : ℝ))
              incidence.retention parentScale cluster.cover.centers.card
              C_positive coarseSetup.tangency cluster.A data.mu)
            (8 * (cluster.cover.centers.card : ℝ))
            cardUpper
            (Real.log
              (8 * (cluster.cover.centers.card : ℝ) *
                  ((data.ambientSource.cluster
                    center (3 * tRep)).card : ℝ) /
                (2 ^ incidence.heavySetup.supportLevel : ℕ)))
            (((2 * refinement.massFactor : ℕ) : ℝ))
            parentArea
            (ambientRestrictedSelectedFineGeometricArea
              C_shading delta C_R tRep DeltaRep) ≤
        positiveTarget := by
    simpa only [positiveTarget, coverExponent, geometricConstant,
      faithfulCanonicalActualBranchLocalTarget] using hpositive
  have hsingleton' :
      outerLoss *
          ambientRestrictedLayerLinearizedLocalCoefficient
            (ambientRestrictedSingletonLayerBaseCoefficientOfFiber
              4
              (((Nat.log2 refinement.selected.card + 1 : ℕ) : ℝ))
              (incidence.heavySetup.degreeLoss : ℝ)
              (((Nat.log2 incidence.heavySetup.ambient.card + 1 : ℕ) : ℝ))
              incidence.retention parentScale cluster.cover.centers.card
              C_singleton coarseSetup.tangency cluster.A data.mu)
            2 cardUpper
            (Real.log
              (2 *
                ((data.ambientSource.cluster
                  center (3 * tRep)).card : ℝ)))
            (((2 * refinement.massFactor : ℕ) : ℝ))
            parentArea
            (ambientRestrictedSelectedFineGeometricArea
              C_shading delta C_R tRep DeltaRep) ≤
        singletonTarget := by
    simpa only [singletonTarget, coverExponent, geometricConstant,
      faithfulCanonicalActualBranchLocalTarget] using hsingleton
  have hscaled :
      ENNReal.ofReal outerLoss *
          volume (ambientRestrictedSet data center) ≤
        ENNReal.ofReal (max positiveTarget singletonTarget) *
          (data.ambientSource.cluster center (3 * tRep)).card :=
    ambient_restricted_scaled_local_target_branches
      (localTarget := max positiveTarget singletonTarget)
      hvolume houterLoss
      (by
        simpa only [Nat.cast_add, Nat.cast_one] using
          hpositive'.trans (le_max_left positiveTarget singletonTarget))
      (by
        simpa only [Nat.cast_add, Nat.cast_one] using
          hsingleton'.trans (le_max_right positiveTarget singletonTarget))
  simpa only [positiveTarget, singletonTarget] using hscaled

theorem faithful_canonical_actual_fixed_bin_volume_le_of_small_scale
    (metricExponent C_count massExponent T C_KT C_R D : ℝ)
    (hmetric : 0 < metricExponent)
    (hC_count : 0 < C_count)
    (hmassExponent : 0 ≤ massExponent)
    (hT : 0 < T)
    (hC_KT : 0 < C_KT)
    (hC_R : 0 < C_R)
    (hD : 1 ≤ D) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 / 2 ∧
      ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
        {K delta diameter tRep DeltaRep C_R₀ : ℝ}
        (data : DyadicFineAssignmentData
          family E K delta diameter metricExponent
            (metricExponent ^ 2) tRep DeltaRep C_R₀)
        (center : C2Function)
        (hE : MeasurableSet E)
        {C_shading C_volume : ℝ}
        (fineSetup : AmbientRestrictedFSVSetupData
          data center hE C_R C_count C_shading C_volume)
        (coarseSetup : AmbientRestrictedCoarseSetupData
          data center hE fineSetup)
        (refinement : AmbientRestrictedLargeBinRefinementData
          data center hE fineSetup coarseSetup massExponent)
        (incidence : AmbientRestrictedJointIncidenceSetupData
          data center hE fineSetup coarseSetup refinement)
        (cluster : AmbientRestrictedJointClusterSetupData
          (D := D) data center hE fineSetup coarseSetup refinement
            incidence)
        (C_out C_inc outerLoss C_positive C_singleton : ℝ),
        0 < delta →
        delta ≤ delta₀ →
        0 < diameter →
        tRep ≤ T →
        0 < C_shading →
        0 < C_out →
        0 < C_inc →
        1 ≤ C_positive →
        1 ≤ C_singleton →
        0 ≤ outerLoss →
        data.ambientSource.HasKatzTaoBound delta C_KT →
        incidence.heavySetup.heavyLogLoss ≤
          Real.rpow delta (-(metricExponent ^ 3)) →
        outerLoss ≤
          Real.rpow delta (-(metricExponent / 16)) →
        AmbientRestrictedSelectedCardinalityResultOfFiber
          refinement.selected.card
          cluster.cover.centers.card
          (data.ambientSource.cluster center (3 * tRep)).card
          (2 ^ incidence.heavySetup.supportLevel)
          data.mu 4
          (Nat.log2 refinement.selected.card + 1)
          incidence.heavySetup.degreeLoss
          (Nat.log2 incidence.heavySetup.ambient.card + 1)
          incidence.retention
          (faithfulCanonicalParentArea C_out DeltaRep C_R tRep /
            (((2 : ENNReal) ^ refinement.layer.val *
              refinement.cutoff).toReal))
          (faithfulCanonicalCutoffParentScale
            delta tRep DeltaRep C_R C_inc
            incidence.heavySetup.heavyLogLoss metricExponent
            incidence.retention incidence.heavySetup.degreeLoss)
          C_positive C_singleton coarseSetup.tangency cluster.A →
        let coverExponent := Real.log D / Real.log 2
        let geometricConstant :=
          Real.sqrt (3 * C_KT) *
              Real.rpow (4 * C_out ^ 2) (1 / 4 : ℝ) *
              Real.rpow
                (2 * C_shading * Real.sqrt C_shading)
                (3 / 4 : ℝ) /
            Real.sqrt C_R
        let positiveTarget :=
          faithfulCanonicalActualBranchLocalTarget
            (4 *
              faithfulCanonicalPositiveBranchConstant
                C_positive coarseSetup.tangency)
            (faithfulCanonicalParentScaleConstant
              diameter T C_R C_inc metricExponent)
            (faithfulCanonicalRetentionInverseConstant
              diameter T metricExponent)
            (faithfulCanonicalClusterConstant T C_R metricExponent)
            D C_positive coverExponent metricExponent geometricConstant
            delta data.mu
        let singletonTarget :=
          faithfulCanonicalActualBranchLocalTarget
            (4 *
              faithfulCanonicalSingletonBranchConstant
                C_singleton coarseSetup.tangency)
            (faithfulCanonicalParentScaleConstant
              diameter T C_R C_inc metricExponent)
            (faithfulCanonicalRetentionInverseConstant
              diameter T metricExponent)
            (faithfulCanonicalClusterConstant T C_R metricExponent)
            D C_singleton coverExponent metricExponent geometricConstant
            delta data.mu
        ENNReal.ofReal outerLoss *
            volume (ambientRestrictedSet data center) ≤
          ENNReal.ofReal (max positiveTarget singletonTarget) *
            (data.ambientSource.cluster center (3 * tRep)).card := by
  rcases faithful_canonical_actual_ordinary_bounds
      metricExponent C_count massExponent T C_KT C_R D
      hmetric hC_count hmassExponent hT hC_KT hC_R hD with
    ⟨delta₀, hdelta₀, hdelta₀Half, hordinary⟩
  refine ⟨delta₀, hdelta₀, hdelta₀Half, ?_⟩
  intro family E K delta diameter tRep DeltaRep C_R₀ data center hE
    C_shading C_volume fineSetup coarseSetup refinement incidence
    cluster C_out C_inc outerLoss C_positive C_singleton
    hdelta hdeltaBound hdiameter htT hC_shading hC_out hC_inc
    hC_positive hC_singleton houterLoss hKT hlogLoss houter
    cardinalityResult
  have hdeltaOne : delta ≤ 1 :=
    hdeltaBound.trans (hdelta₀Half.trans (by norm_num))
  rcases hordinary data center hE fineSetup coarseSetup refinement
      incidence cluster outerLoss hdelta hdeltaBound htT hKT
      hlogLoss houter with
    ⟨hpositiveOrdinary, hsingletonOrdinary⟩
  exact faithful_canonical_actual_fixed_bin_volume_le
    data center hE fineSetup coarseSetup refinement incidence cluster
    T C_KT C_out C_inc outerLoss C_positive C_singleton
    hdelta hdeltaOne hdiameter hT htT hC_R hC_shading hC_KT
    hC_out hC_inc hD hmetric hC_positive hC_singleton
    houterLoss hKT
    (faithful_canonical_positive_log_tail_nonneg cluster)
    (faithful_canonical_singleton_log_tail_nonneg
      incidence.heavySetup)
    hlogLoss hpositiveOrdinary hsingletonOrdinary cardinalityResult

end Kakeya.Cinematic
