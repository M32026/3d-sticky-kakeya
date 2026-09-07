import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalActualLocalVolume
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalLargeFiberCardinality

/-!
# Faithful canonical volume bound for one large ambient bin

This module combines the canonical large-fiber cardinality branch with the
fixed-bin volume estimate and absorbs both Proposition 26 branches into one
common local target.
-/

open MeasureTheory

namespace Kakeya.Cinematic

theorem faithful_canonical_large_bin_volume_le_of_small_scale
    (metricExponent C_count massExponent T C_KT C_R D : ℝ)
    (hmetric : 0 < metricExponent)
    (hmetricUpper : metricExponent ≤ 1 / 16)
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
        (C_out C_inc outerLoss C_positive C_singleton : ℝ)
        (hCluster :
          delta <
              11 *
                ambientRestrictedPaperClusterRadius
                  tRep metricExponent
                    incidence.heavySetup.heavyLogLoss
                    (4 *
                      Real.rpow (2 * tRep / DeltaRep)
                        (metricExponent ^ 2)) →
            Nonempty
              (AmbientRestrictedJointClusterSetupData
                (D := D) data center hE fineSetup coarseSetup
                  refinement incidence))
        (hParentMeasure :
          IsCinematicFamily family K D →
            0 < delta →
              1 ≤ C_R →
                ((2 ^ refinement.parentLevel : ℕ) : ℝ) ≤
                  faithfulCanonicalParentArea
                      C_out DeltaRep C_R tRep /
                    (((2 : ENNReal) ^ refinement.layer.val *
                      refinement.cutoff).toReal))
        (hParentTangency :
          IsCinematicFamily family K D →
            0 < delta →
              0 < C_R →
                2 ≤ incidence.q_fiber →
                  (∀ p : ambientRestrictedSet data center,
                    delta /
                        (ambientRestrictedData data center hE).exactT p <
                      selectedIncidenceMetricCut
                        incidence.heavySetup.heavyLogLoss
                        (4 *
                          Real.rpow (2 * tRep / DeltaRep)
                            (metricExponent ^ 2))
                        metricExponent) →
                    10 * delta ≤
                      (selectedIncidenceMetricCut
                            incidence.heavySetup.heavyLogLoss
                            (4 *
                              Real.rpow (2 * tRep / DeltaRep)
                                (metricExponent ^ 2))
                            metricExponent *
                          tRep / 8) /
                        (6 * K) →
                      100 * delta ≤
                        C_R * tRep * DeltaRep / delta →
                        (∀ p : E,
                          ((data.assignment.fiber p).card : ℝ) <
                            2 * (data.mu : ℝ)) →
                          ((incidence.heavySetup.M_parent : ℕ) : ℝ) ≤
                            faithfulCanonicalCutoffParentScale
                                delta tRep DeltaRep C_R C_inc
                                incidence.heavySetup.heavyLogLoss
                                metricExponent incidence.retention
                                incidence.heavySetup.degreeLoss *
                              Real.rpow (data.mu : ℝ) (-2) *
                              Real.rpow
                                (2 ^
                                  incidence.heavySetup.supportLevel :
                                    ℕ) 2)
        (hQCluster :
          ∀ cluster : AmbientRestrictedJointClusterSetupData
              (D := D) data center hE fineSetup coarseSetup
                refinement incidence,
            QClusterCoarseCardinalityResult
              incidence.heavySetup.selectedCoarse.card
              (2 ^ incidence.heavySetup.supportLevel)
              cluster.cover.centers.card
              (data.ambientSource.cluster
                center (3 * tRep)).card
              C_positive C_singleton coarseSetup.tangency cluster.A)
        (hInterpolate : CoarseMultiplicityInterpolationStatement),
        1 ≤ K →
        IsCinematicFamily family K D →
        0 < delta →
        delta ≤ delta₀ →
        0 < diameter →
        tRep ≤ T →
        100 ≤ C_R →
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
        8 * incidence.heavySetup.heavyLogLoss ≤
          (incidence.q_fiber : ℝ) →
        480 * K * delta ≤
          selectedIncidenceMetricCut
              incidence.heavySetup.heavyLogLoss
              (4 *
                Real.rpow (2 * tRep / DeltaRep)
                  (metricExponent ^ 2))
              metricExponent *
            tRep →
        (∀ p : E,
          ((data.assignment.fiber p).card : ℝ) <
            2 * (data.mu : ℝ)) →
        let coverExponent := Real.log D / Real.log 2
        let geometricConstant :=
          Real.sqrt (3 * C_KT) *
              Real.rpow (4 * C_out ^ 2) (1 / 4 : ℝ) *
              Real.rpow
                (2 * C_shading * Real.sqrt C_shading)
                (3 / 4 : ℝ) /
            Real.sqrt C_R
        let commonTarget :=
          faithfulCanonicalActualCommonLocalTarget
            (faithfulCanonicalParentScaleConstant
              diameter T C_R C_inc metricExponent)
            (faithfulCanonicalRetentionInverseConstant
              diameter T metricExponent)
            (faithfulCanonicalClusterConstant
              T C_R metricExponent)
            D C_positive C_singleton coverExponent
            coarseSetup.tangency metricExponent geometricConstant
            delta data.mu
        ∃ cluster : AmbientRestrictedJointClusterSetupData
            (D := D) data center hE fineSetup coarseSetup
              refinement incidence,
          ENNReal.ofReal outerLoss *
              volume (ambientRestrictedSet data center) ≤
            ENNReal.ofReal commonTarget *
              (data.ambientSource.cluster center (3 * tRep)).card := by
  rcases faithful_canonical_actual_fixed_bin_volume_le_of_small_scale
      metricExponent C_count massExponent T C_KT C_R D
      hmetric hC_count hmassExponent hT hC_KT hC_R hD with
    ⟨delta₀, hdelta₀, hdelta₀Half, hfixed⟩
  refine ⟨delta₀, hdelta₀, hdelta₀Half, ?_⟩
  intro family E K delta diameter tRep DeltaRep C_R₀ data center hE
    C_shading C_volume fineSetup coarseSetup refinement incidence
    C_out C_inc outerLoss C_positive C_singleton
    hCluster hParentMeasure hParentTangency hQCluster hInterpolate
    hK hfamily hdelta hdeltaBound hdiameter htT hhundred
    hC_shading hC_out hC_inc hC_positive hC_singleton houterLoss
    hKT hlogLoss houter hlarge hmetricCut hfiberUpper
  rcases faithful_canonical_large_fiber_cardinality
      data center hE fineSetup coarseSetup refinement incidence
      C_out C_inc C_positive C_singleton
      hCluster hParentMeasure hParentTangency hQCluster hInterpolate
      hK hfamily hdelta hhundred hC_out hC_inc hC_positive
      hC_singleton hlarge hmetricCut hfiberUpper with
    ⟨cluster, hcardinality⟩
  refine ⟨cluster, ?_⟩
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
  let commonTarget :=
    faithfulCanonicalActualCommonLocalTarget
      (faithfulCanonicalParentScaleConstant
        diameter T C_R C_inc metricExponent)
      (faithfulCanonicalRetentionInverseConstant
        diameter T metricExponent)
      (faithfulCanonicalClusterConstant T C_R metricExponent)
      D C_positive C_singleton coverExponent coarseSetup.tangency
      metricExponent geometricConstant delta data.mu
  have hvolume :
      ENNReal.ofReal outerLoss *
          volume (ambientRestrictedSet data center) ≤
        ENNReal.ofReal (max positiveTarget singletonTarget) *
          (data.ambientSource.cluster center (3 * tRep)).card := by
    simpa only [coverExponent, geometricConstant, positiveTarget,
      singletonTarget] using
      hfixed data center hE fineSetup coarseSetup refinement incidence
        cluster C_out C_inc outerLoss C_positive C_singleton
        hdelta hdeltaBound hdiameter htT hC_shading hC_out hC_inc
        hC_positive hC_singleton houterLoss hKT hlogLoss houter
        hcardinality
  have hgeometric : 0 ≤ geometricConstant := by
    dsimp only [geometricConstant]
    apply div_nonneg
    · exact mul_nonneg
        (mul_nonneg
          (Real.sqrt_nonneg _)
          (Real.rpow_nonneg
            (mul_nonneg (by norm_num) (sq_nonneg C_out)) _))
        (Real.rpow_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) hC_shading.le)
            (Real.sqrt_nonneg _)) _)
    · exact Real.sqrt_nonneg _
  have hmax :
      max positiveTarget singletonTarget ≤ commonTarget := by
    simpa only [coverExponent, geometricConstant, positiveTarget,
      singletonTarget, commonTarget] using
      faithful_canonical_actual_branch_max_le_common
        diameter T C_R C_inc D C_positive C_singleton
        coarseSetup.tangency metricExponent geometricConstant delta
        data.mu hdiameter hT hC_R hC_inc hD hC_positive
        hC_singleton
        (by linarith [coarseSetup.tangency_ge_five])
        hmetric hmetricUpper hgeometric hdelta
        (hdeltaBound.trans (hdelta₀Half.trans (by norm_num)))
  exact hvolume.trans <| by
    gcongr

end Kakeya.Cinematic
