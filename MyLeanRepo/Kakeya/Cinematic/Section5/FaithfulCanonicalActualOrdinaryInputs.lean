import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalActualSelectedLayerBounds
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalOrdinaryLoss

/-!
# Ordinary-loss inputs at the actual faithful canonical scales

This module turns the polynomial center-cover and Katz--Tao cardinality
bounds into ordinary logarithmic tails.  It does not absorb the outer
dyadic-retention loss a second time.
-/

namespace Kakeya.Cinematic

lemma outer_loss_le_rpow_of_scaled_power_product_le_one
    (scale delta exponent outerLoss : ℝ)
    (hscale : 0 < scale)
    (hdelta : 0 < delta)
    (hsmall :
      outerLoss * scale ^ exponent * delta ^ exponent ≤ 1) :
    outerLoss ≤ Real.rpow (scale * delta) (-exponent) := by
  have hscaledPos :
      0 < Real.rpow (scale * delta) exponent :=
    Real.rpow_pos_of_pos (mul_pos hscale hdelta) _
  have hfactor :
      scale ^ exponent * delta ^ exponent =
        Real.rpow (scale * delta) exponent :=
    (Real.mul_rpow hscale.le hdelta.le).symm
  have hproduct :
      outerLoss * Real.rpow (scale * delta) exponent ≤ 1 := by
    rw [← hfactor]
    simpa only [mul_assoc] using hsmall
  have hdiv :
      outerLoss ≤
        1 / Real.rpow (scale * delta) exponent :=
    (le_div_iff₀ hscaledPos).2 <| by
      simpa only [mul_one] using hproduct
  calc
    outerLoss ≤
        1 / Real.rpow (scale * delta) exponent := hdiv
    _ = (Real.rpow (scale * delta) exponent)⁻¹ := by
      rw [one_div]
    _ = Real.rpow (scale * delta) (-exponent) :=
      (Real.rpow_neg (mul_pos hscale hdelta).le exponent).symm

theorem faithful_canonical_heavy_log_loss_absorption
    (C_count metricExponent : ℝ)
    (hC_count : 0 ≤ C_count)
    (hmetric : 0 < metricExponent) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 / 2 ∧
      ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
        {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
        (data : DyadicFineAssignmentData
          family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
        (center : C2Function)
        (hE : MeasurableSet E)
        {C_R C_shading C_volume : ℝ}
        (fineSetup : AmbientRestrictedFSVSetupData
          data center hE C_R C_count C_shading C_volume)
        (coarseSetup : AmbientRestrictedCoarseSetupData
          data center hE fineSetup)
        {massExponent : ℝ}
        (refinement : AmbientRestrictedLargeBinRefinementData
          data center hE fineSetup coarseSetup massExponent)
        (incidence : AmbientRestrictedJointIncidenceSetupData
          data center hE fineSetup coarseSetup refinement),
        0 < delta →
        delta ≤ delta₀ →
        incidence.heavySetup.heavyLogLoss ≤
          Real.rpow delta (-(metricExponent ^ 3)) := by
  have hcubic : 0 < metricExponent ^ 3 := by
    positivity
  rcases dyadic_log_loss_absorption
      C_count (metricExponent ^ 3) hC_count hcubic with
    ⟨delta₀, hdelta₀, hdelta₀Half, hmain⟩
  refine ⟨delta₀, hdelta₀, hdelta₀Half, ?_⟩
  intro family E K delta diameter epsilon eta tRep DeltaRep C_R₀
    data center hE C_R C_shading C_volume fineSetup coarseSetup
    massExponent refinement incidence hdelta hdeltaBound
  have hraw :=
    hmain hdelta hdeltaBound fineSetup.fine_card
  rw [incidence.heavySetup.heavyLogLoss_eq,
    incidence.heavySetup.degreeLoss_eq]
  simpa using hraw

lemma log_le_polynomial_log_loss
    (delta C exponent x : ℝ)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hexponent : 0 ≤ exponent)
    (hx : 0 < x)
    (hbound :
      x ≤ C * Real.rpow delta (-exponent)) :
    Real.log x ≤
      (exponent + 1) *
        (Real.log (max C 1 / delta) + 1) := by
  let C' := max C 1
  have hC' : 0 < C' := by
    dsimp only [C']
    exact lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  have hC_le : C ≤ C' := by
    dsimp only [C']
    exact le_max_left _ _
  have hinv : 1 ≤ 1 / delta := by
    apply (le_div_iff₀ hdelta).2
    simpa only [one_mul] using hdeltaOne
  have hlogC : 0 ≤ Real.log C' :=
    Real.log_nonneg (by
      dsimp only [C']
      exact le_max_right C 1)
  have hlogInv : 0 ≤ Real.log (1 / delta) :=
    Real.log_nonneg hinv
  have hbound' :
      x ≤ C' * Real.rpow delta (-exponent) :=
    hbound.trans <| mul_le_mul_of_nonneg_right hC_le
      (Real.rpow_nonneg hdelta.le _)
  have hlogBound :
      Real.log x ≤
        Real.log (C' * Real.rpow delta (-exponent)) :=
    Real.log_le_log hx hbound'
  have hlogProduct :
      Real.log (C' * Real.rpow delta (-exponent)) =
        Real.log C' + exponent * Real.log (1 / delta) := by
    calc
      Real.log (C' * Real.rpow delta (-exponent)) =
          Real.log C' + Real.log (Real.rpow delta (-exponent)) :=
        Real.log_mul hC'.ne'
          (Real.rpow_pos_of_pos hdelta _).ne'
      _ = Real.log C' + (-exponent) * Real.log delta := by
        have hrpowLog :
            Real.log (Real.rpow delta (-exponent)) =
              (-exponent) * Real.log delta := by
          simpa using Real.log_rpow hdelta (-exponent)
        rw [hrpowLog]
      _ = Real.log C' + exponent * Real.log (1 / delta) := by
        rw [one_div, Real.log_inv]
        ring
  have hlogQuotient :
      Real.log (C' / delta) =
        Real.log C' + Real.log (1 / delta) := by
    calc
      Real.log (C' / delta) =
          Real.log C' - Real.log delta :=
        Real.log_div hC'.ne' hdelta.ne'
      _ = Real.log C' + Real.log (1 / delta) := by
        rw [one_div, Real.log_inv]
        ring
  calc
    Real.log x ≤
        Real.log C' + exponent * Real.log (1 / delta) := by
      rw [← hlogProduct]
      exact hlogBound
    _ ≤
        (exponent + 1) *
          (Real.log (C' / delta) + 1) := by
      rw [hlogQuotient]
      nlinarith [mul_nonneg hexponent hlogC,
        mul_nonneg hexponent hlogInv]
    _ =
        (exponent + 1) *
          (Real.log (max C 1 / delta) + 1) := by rfl

noncomputable def faithfulCanonicalPositiveTailExponent
    (D metricExponent : ℝ) : ℝ :=
  (metricExponent + metricExponent ^ 2) *
      (Real.log D / Real.log 2) +
    1

noncomputable def faithfulCanonicalPositiveTailConstant
    (T C_KT C_R D metricExponent : ℝ) : ℝ :=
  8 *
    (D *
      Real.rpow
        (48 *
          faithfulCanonicalClusterConstant
            T C_R metricExponent)
        (Real.log D / Real.log 2)) *
    C_KT

lemma faithful_canonical_positive_log_tail_le
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
    (T C_KT : ℝ)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hT : 0 < T)
    (htT : tRep ≤ T)
    (hC_R : 0 < C_R)
    (hC_KT : 0 < C_KT)
    (hD : 1 ≤ D)
    (hmetric : 0 < metricExponent)
    (hKT : data.ambientSource.HasKatzTaoBound delta C_KT)
    (hlogLoss :
      incidence.heavySetup.heavyLogLoss ≤
        Real.rpow delta (-(metricExponent ^ 3))) :
    Real.log
        (8 * (cluster.cover.centers.card : ℝ) *
            ((data.ambientSource.cluster
              center (3 * tRep)).card : ℝ) /
          (2 ^ incidence.heavySetup.supportLevel : ℕ)) ≤
      (faithfulCanonicalPositiveTailExponent D metricExponent + 1) *
        (Real.log
            (max
                (faithfulCanonicalPositiveTailConstant
                  T C_KT C_R D metricExponent)
                1 /
              delta) +
          1) := by
  let coverExponent := Real.log D / Real.log 2
  let branchExponent := metricExponent + metricExponent ^ 2
  let clusterConstant :=
    faithfulCanonicalClusterConstant T C_R metricExponent
  let centerConstant :=
    D * Real.rpow (48 * clusterConstant) coverExponent
  let tailExponent := branchExponent * coverExponent + 1
  let tailConstant := 8 * centerConstant * C_KT
  have hDelta : 0 < DeltaRep :=
    hdelta.trans_le data.delta_le_DeltaRep
  have hheavy : 0 < incidence.heavySetup.heavyLogLoss :=
    lt_of_lt_of_le zero_lt_one
      incidence.heavySetup.one_le_heavyLogLoss
  have hcoverExponent : 0 ≤ coverExponent := by
    dsimp only [coverExponent]
    exact div_nonneg (Real.log_nonneg hD)
      (Real.log_nonneg (by norm_num))
  have hbranchExponent : 0 ≤ branchExponent := by
    dsimp only [branchExponent]
    positivity
  have htailExponent : 0 ≤ tailExponent := by
    dsimp only [tailExponent]
    positivity
  have hclusterConstant : 0 < clusterConstant := by
    dsimp only [clusterConstant, faithfulCanonicalClusterConstant]
    exact mul_pos
      (mul_pos (by norm_num) hC_R)
      (Real.rpow_pos_of_pos
        (mul_pos (by norm_num)
          (Real.rpow_pos_of_pos
            (mul_pos (by norm_num) hT) _)) _)
  have hA :
      cluster.A ≤ clusterConstant *
        Real.rpow delta (-branchExponent) := by
    dsimp only [clusterConstant, branchExponent]
    rw [cluster.A_eq, cluster.fiberRatio_eq]
    exact canonical_paper_cluster_parameter_le
      delta tRep DeltaRep T C_R
      incidence.heavySetup.heavyLogLoss metricExponent
      hdelta hDelta hT hC_R hheavy hmetric
      data.delta_le_DeltaRep data.DeltaRep_le_tRep htT hlogLoss
  have hcentersPaper :
      (cluster.cover.centers.card : ℝ) ≤
        D * Real.rpow (48 * cluster.A) coverExponent := by
    dsimp only [coverExponent]
    exact cluster.cover.centers_card_le_paper_parameter
      cluster.radius_pos cluster.A_ge_one cluster.scale_identity
  have hcenters :
      (cluster.cover.centers.card : ℝ) ≤
        centerConstant *
          Real.rpow delta
            (-(branchExponent * coverExponent)) := by
    dsimp only [centerConstant]
    exact canonical_cluster_cover_card_le
      delta D cluster.A clusterConstant branchExponent coverExponent
      hdelta (zero_lt_one.trans_le hD)
      (zero_le_one.trans cluster.A_ge_one) hclusterConstant
      hcoverExponent hA cluster.cover.centers.card hcentersPaper
  have hambientNat :
      (data.ambientSource.cluster center (3 * tRep)).card ≤
        data.ambientSource.card :=
    cluster_card_le data.ambientSource center (3 * tRep)
  have hambient :
      ((data.ambientSource.cluster center (3 * tRep)).card : ℝ) ≤
        C_KT * Real.rpow delta (-1) := by
    calc
      ((data.ambientSource.cluster center (3 * tRep)).card : ℝ) ≤
          (data.ambientSource.card : ℝ) := by
        exact_mod_cast hambientNat
      _ ≤ C_KT / delta := hKT.1
      _ = C_KT * Real.rpow delta (-1) := by
        rw [div_eq_mul_inv]
        congr 1
        exact (Real.rpow_neg_one delta).symm
  have hsupportPos :
      0 <
        (((2 ^ incidence.heavySetup.supportLevel : ℕ) : ℝ)) := by
    positivity
  have hsupportOne :
      1 ≤
        (((2 ^ incidence.heavySetup.supportLevel : ℕ) : ℝ)) := by
    exact_mod_cast Nat.one_le_two_pow
  have hcentersPos :
      0 < (cluster.cover.centers.card : ℝ) := by
    exact_mod_cast cluster.cover.centers_nonempty.card_pos
  have hambientPos :
      0 <
        ((data.ambientSource.cluster
          center (3 * tRep)).card : ℝ) := by
    rw [← incidence.heavySetup.ambient_card_eq_cluster_card]
    exact_mod_cast incidence.heavySetup.ambient_card_pos
  have hargumentPos :
      0 <
        8 * (cluster.cover.centers.card : ℝ) *
            ((data.ambientSource.cluster
              center (3 * tRep)).card : ℝ) /
          (2 ^ incidence.heavySetup.supportLevel : ℕ) := by
    positivity
  have hargumentNumerator :
      8 * (cluster.cover.centers.card : ℝ) *
            ((data.ambientSource.cluster
              center (3 * tRep)).card : ℝ) /
          (2 ^ incidence.heavySetup.supportLevel : ℕ) ≤
        8 * (cluster.cover.centers.card : ℝ) *
          ((data.ambientSource.cluster
            center (3 * tRep)).card : ℝ) := by
    apply (div_le_iff₀ hsupportPos).2
    have hnumerator :
        0 ≤
          8 * (cluster.cover.centers.card : ℝ) *
            ((data.ambientSource.cluster
              center (3 * tRep)).card : ℝ) := by
      positivity
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hsupportOne hnumerator
  have hpowers :
      Real.rpow delta
            (-(branchExponent * coverExponent)) *
          Real.rpow delta (-1) =
        Real.rpow delta (-tailExponent) := by
    dsimp only [tailExponent]
    calc
      Real.rpow delta
            (-(branchExponent * coverExponent)) *
          Real.rpow delta (-1) =
        Real.rpow delta
          (-(branchExponent * coverExponent) + -1) :=
        (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta
          (-(branchExponent * coverExponent + 1)) := by
        congr 1
        ring
  have hnumerator :
      8 * (cluster.cover.centers.card : ℝ) *
          ((data.ambientSource.cluster
            center (3 * tRep)).card : ℝ) ≤
        tailConstant * Real.rpow delta (-tailExponent) := by
    have hproduct :=
      mul_le_mul hcenters hambient
        (by positivity)
        (mul_nonneg
          (by
            dsimp only [centerConstant]
            exact mul_nonneg (zero_le_one.trans hD)
              (Real.rpow_nonneg
                (mul_nonneg (by norm_num) hclusterConstant.le) _))
          (Real.rpow_nonneg hdelta.le _))
    have hscaled :=
      mul_le_mul_of_nonneg_left hproduct
        (show (0 : ℝ) ≤ 8 by norm_num)
    dsimp only [tailConstant]
    rw [← hpowers]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hargument :
      8 * (cluster.cover.centers.card : ℝ) *
            ((data.ambientSource.cluster
              center (3 * tRep)).card : ℝ) /
          (2 ^ incidence.heavySetup.supportLevel : ℕ) ≤
        tailConstant * Real.rpow delta (-tailExponent) :=
    hargumentNumerator.trans hnumerator
  have htail :=
    log_le_polynomial_log_loss
      delta tailConstant tailExponent
      (8 * (cluster.cover.centers.card : ℝ) *
          ((data.ambientSource.cluster
            center (3 * tRep)).card : ℝ) /
        (2 ^ incidence.heavySetup.supportLevel : ℕ))
      hdelta hdeltaOne htailExponent hargumentPos hargument
  simpa only [tailExponent, tailConstant, centerConstant,
    branchExponent, coverExponent, clusterConstant,
    faithfulCanonicalPositiveTailExponent,
    faithfulCanonicalPositiveTailConstant] using htail

lemma faithful_canonical_singleton_log_tail_le
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    {data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀}
    {center : C2Function}
    {hE : MeasurableSet E}
    {C_R C_count C_shading C_volume : ℝ}
    {fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume}
    {coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE fineSetup}
    {massExponent : ℝ}
    {refinement : AmbientRestrictedLargeBinRefinementData
      data center hE fineSetup coarseSetup massExponent}
    {degreeSetup : RetainedIncidenceDegreeSetupData
      data center hE fineSetup coarseSetup refinement}
    {q_fiber : ℕ}
    {fiberBound : ℝ}
    (heavySetup : RetainedHeavySupportSetupData
      data center hE fineSetup coarseSetup refinement
        degreeSetup q_fiber fiberBound)
    (C_KT : ℝ)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hC_KT : 0 < C_KT)
    (hKT : data.ambientSource.HasKatzTaoBound delta C_KT) :
    Real.log
        (2 *
          ((data.ambientSource.cluster
            center (3 * tRep)).card : ℝ)) ≤
      2 * (Real.log (max (2 * C_KT) 1 / delta) + 1) := by
  have hambientNat :
      (data.ambientSource.cluster center (3 * tRep)).card ≤
        data.ambientSource.card :=
    cluster_card_le data.ambientSource center (3 * tRep)
  have hambient :
      ((data.ambientSource.cluster center (3 * tRep)).card : ℝ) ≤
        C_KT * Real.rpow delta (-1) := by
    calc
      ((data.ambientSource.cluster center (3 * tRep)).card : ℝ) ≤
          (data.ambientSource.card : ℝ) := by
        exact_mod_cast hambientNat
      _ ≤ C_KT / delta := hKT.1
      _ = C_KT * Real.rpow delta (-1) := by
        rw [div_eq_mul_inv]
        congr 1
        exact (Real.rpow_neg_one delta).symm
  have hambientPos :
      0 <
        ((data.ambientSource.cluster
          center (3 * tRep)).card : ℝ) := by
    rw [← heavySetup.ambient_card_eq_cluster_card]
    exact_mod_cast heavySetup.ambient_card_pos
  have hargument :
      2 *
          ((data.ambientSource.cluster
            center (3 * tRep)).card : ℝ) ≤
        (2 * C_KT) * Real.rpow delta (-1) := by
    nlinarith [mul_le_mul_of_nonneg_left hambient
      (show (0 : ℝ) ≤ 2 by norm_num)]
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using
    log_le_polynomial_log_loss
      delta (2 * C_KT) 1
      (2 *
        ((data.ambientSource.cluster
          center (3 * tRep)).card : ℝ))
      hdelta hdeltaOne (by norm_num) (by positivity) hargument

theorem faithful_canonical_actual_ordinary_bounds
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
        (outerLoss : ℝ),
        0 < delta →
        delta ≤ delta₀ →
        tRep ≤ T →
        data.ambientSource.HasKatzTaoBound delta C_KT →
        incidence.heavySetup.heavyLogLoss ≤
          Real.rpow delta (-(metricExponent ^ 3)) →
        outerLoss ≤
          Real.rpow delta (-(metricExponent / 16)) →
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
            (-faithfulCanonicalOrdinaryLoss metricExponent) ∧
        faithfulCanonicalOrdinaryDyadicLoss
            outerLoss
            (Real.log
              (2 *
                ((data.ambientSource.cluster
                  center (3 * tRep)).card : ℝ)))
            refinement.layerCount data.ambientSource.card
            fineSetup.fine.card refinement.selected.card ≤
          Real.rpow delta
            (-faithfulCanonicalOrdinaryLoss metricExponent) := by
  let layerA := 8 * (C_count + massExponent + 2)
  let positiveTailA :=
    faithfulCanonicalPositiveTailExponent D metricExponent + 1
  let positiveTailC :=
    max
      (faithfulCanonicalPositiveTailConstant
        T C_KT C_R D metricExponent)
      1
  let singletonTailC := max (2 * C_KT) 1
  have hlayerA : 0 < layerA := by
    dsimp only [layerA]
    positivity
  have hpositiveTailA : 0 < positiveTailA := by
    have hcover :
        0 ≤ Real.log D / Real.log 2 :=
      div_nonneg (Real.log_nonneg hD)
        (Real.log_nonneg (by norm_num))
    dsimp only [positiveTailA,
      faithfulCanonicalPositiveTailExponent]
    positivity
  have hpositiveTailC : 0 < positiveTailC := by
    dsimp only [positiveTailC]
    exact zero_lt_one.trans_le (le_max_right _ _)
  have hsingletonTailC : 0 < singletonTailC := by
    dsimp only [singletonTailC]
    exact zero_lt_one.trans_le (le_max_right _ _)
  rcases faithful_canonical_remaining_dyadic_loss_absorption
      metricExponent layerA 1 positiveTailA positiveTailC
      2 C_count hmetric hlayerA (by norm_num)
      hpositiveTailA hpositiveTailC (by norm_num) hC_count.le with
    ⟨deltaPositive, hdeltaPositive, hdeltaPositiveHalf,
      hpositiveMain⟩
  rcases faithful_canonical_remaining_dyadic_loss_absorption
      metricExponent layerA 1 2 singletonTailC
      2 C_count hmetric hlayerA (by norm_num)
      (by norm_num) hsingletonTailC (by norm_num) hC_count.le with
    ⟨deltaSingleton, hdeltaSingleton, hdeltaSingletonHalf,
      hsingletonMain⟩
  rcases fixed_constant_rpow_absorption
      C_KT 1 hC_KT (by norm_num) with
    ⟨deltaAmbient, hdeltaAmbient, hdeltaAmbientOne,
      hambientMain⟩
  let delta₀ := min deltaAmbient (min deltaPositive deltaSingleton)
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀Half : delta₀ ≤ 1 / 2 := by
    dsimp only [delta₀]
    exact
      (min_le_right _ _).trans
        ((min_le_left _ _).trans hdeltaPositiveHalf)
  refine ⟨delta₀, hdelta₀, hdelta₀Half, ?_⟩
  intro family E K delta diameter tRep DeltaRep C_R₀ data center hE
    C_shading C_volume fineSetup coarseSetup refinement incidence
    cluster outerLoss hdelta hdeltaBound htT hKT hlogLoss houter
  have hdeltaOne : delta ≤ 1 :=
    hdeltaBound.trans (hdelta₀Half.trans (by norm_num))
  have hdeltaAmbient' : delta ≤ deltaAmbient :=
    hdeltaBound.trans (by
      dsimp only [delta₀]
      exact min_le_left _ _)
  have hdeltaPositive' : delta ≤ deltaPositive :=
    hdeltaBound.trans (by
      dsimp only [delta₀]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hdeltaSingleton' : delta ≤ deltaSingleton :=
    hdeltaBound.trans (by
      dsimp only [delta₀]
      exact (min_le_right _ _).trans (min_le_right _ _))
  have hCKTdelta :
      C_KT * delta ≤ 1 := by
    calc
      C_KT * delta =
          C_KT * Real.rpow delta 1 := by
        congr 1
        exact (Real.rpow_one delta).symm
      _ ≤ 1 := hambientMain hdelta hdeltaAmbient'
  have hambient :
      (data.ambientSource.card : ℝ) ≤
        Real.rpow delta (-2) := by
    calc
      (data.ambientSource.card : ℝ) ≤ C_KT / delta := hKT.1
      _ ≤ (1 / delta) / delta := by
        gcongr
        exact (le_div_iff₀ hdelta).2 hCKTdelta
      _ = Real.rpow delta (-2) := by
        calc
          1 / delta / delta = (delta * delta)⁻¹ := by
            field_simp [hdelta.ne']
          _ = (Real.rpow delta (2 : ℝ))⁻¹ := by
            congr 1
            calc
              delta * delta = delta ^ 2 := (pow_two delta).symm
              _ = Real.rpow delta (2 : ℝ) :=
                (Real.rpow_two delta).symm
          _ = Real.rpow delta (-2) :=
            (Real.rpow_neg hdelta.le (2 : ℝ)).symm
  have hfine :
      (fineSetup.fine.card : ℝ) ≤
        Real.rpow delta (-C_count) :=
    fineSetup.fine_card
  have hselected :
      refinement.selected.card ≤ fineSetup.fine.card :=
    refinement.selected_card_le_fine_card
  have hlayer :
      (((8 * refinement.layerCount : ℕ) : ℝ)) ≤
        layerA * (Real.logb 2 (1 / delta) + 1) := by
    have hscaled :=
      mul_le_mul_of_nonneg_left refinement.layerCount_bound
        (show (0 : ℝ) ≤ 8 by norm_num)
    dsimp only [layerA]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hpositiveNonneg :=
    faithful_canonical_positive_log_tail_nonneg cluster
  have hsingletonNonneg :=
    faithful_canonical_singleton_log_tail_nonneg
      incidence.heavySetup
  have hpositiveTail :=
    faithful_canonical_positive_log_tail_le
      data center hE fineSetup coarseSetup refinement incidence cluster
      T C_KT hdelta hdeltaOne hT htT hC_R hC_KT hD hmetric
      hKT hlogLoss
  have hsingletonTail :=
    faithful_canonical_singleton_log_tail_le
      incidence.heavySetup C_KT hdelta hdeltaOne hC_KT hKT
  constructor
  · apply hpositiveMain hdelta hdeltaPositive' houter
      (by
        simpa only [one_div] using hlayer)
      hambient hfine hselected hpositiveNonneg
    simpa only [positiveTailA, positiveTailC] using hpositiveTail
  · apply hsingletonMain hdelta hdeltaSingleton' houter
      (by
        simpa only [one_div] using hlayer)
      hambient hfine hselected hsingletonNonneg
    simpa only [singletonTailC] using hsingletonTail

end Kakeya.Cinematic
