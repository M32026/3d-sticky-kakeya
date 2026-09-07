import MyLeanRepo.Kakeya.Cinematic.Section5.UniformC2FaithfulAssemblyInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulScaleAbsorption
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalScaleLoss
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalLargeBinVolume
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalFinalAbsorption
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulSmallVolumeRegime
import MyLeanRepo.Kakeya.Cinematic.Section5.FineShadingCoverVolume
import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredRectangleEnlargement
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedFSVGeometry
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedFineCoarseSetup
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedParentMeasureScale
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedCutoffParentTangencyScale
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedParentTangencyScale
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedIncidenceFiberGoodPairs
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedIncidenceTangencyAutomaticGoodPairs
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedFiberPairIncidence
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedJointParentPairIncidenceTangencyAutomatic
import MyLeanRepo.Kakeya.Cinematic.Section5.QClusterCoarseCardinalityBranches
import MyLeanRepo.Kakeya.Cinematic.Section5.SingletonSeparatedTangentBallPairAt
import MyLeanRepo.Kakeya.Cinematic.Section5.SingletonClusterCoarseCardinalityWitness
import MyLeanRepo.Kakeya.Cinematic.Section5.ShadingVolume
import MyLeanRepo.Kakeya.Cinematic.Section5.DisjointPieceMass
import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseFiberAssignedMass
import MyLeanRepo.Kakeya.Cinematic.Section5.FinsetRectangleSubfamily
import MyLeanRepo.Kakeya.Cinematic.Section5.RetainedMeasure
import MyLeanRepo.Kakeya.Cinematic.Section5.PolynomialDyadicPieceRefinement
import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicFineAssignment
import MyLeanRepo.Kakeya.Cinematic.Section5.PackingAndRefinement
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientBallRestriction
import MyLeanRepo.Kakeya.Cinematic.Section5.RetainedAmbientBallVolumeAssembly
import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseGroupingSetup
import MyLeanRepo.Kakeya.Cinematic.Section5.TangencyAutoCounting
import MyLeanRepo.Kakeya.Cinematic.Section5.MetricAutomaticPairIncidence
import MyLeanRepo.Kakeya.Cinematic.Section5.DirectFiberFunctionIncidence
import MyLeanRepo.Kakeya.Cinematic.Section5.SingletonFiberDataAbsorption
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedSmallJointFiberExit
import MyLeanRepo.Kakeya.Cinematic.Section5.SmallJointFiberScaleAbsorption
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedJointMetricCutoffExit
import MyLeanRepo.Kakeya.Cinematic.Section5.JointMetricCutoffScaleExit
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedLargeBinMassThreshold
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedLargeBinRefinement
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedJointIncidenceSetup
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedJointClusterSetup
import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicNonThinFineRectangleCount
import MyLeanRepo.Kakeya.Cinematic.Section5.ScaleFreeNormalCoarseCountFromPairs

open MeasureTheory

namespace Kakeya.Cinematic


theorem wz2_uniformC2_short_curve_level_set_from_faithful_inputs :
    WZ2UniformC2ShortCurveLevelSetFromFaithfulInputsStatement := by
  intro hShadingComp hMaximal hFCMA hDyadicRefine hPolyRange hNonThin
    hContain hCommon hFineToCoarse hFineToCoarseCentral
    hFineTangencyLift hCoarseGrouping hCompCoarseTan hFiniteAmbient
    hLemma45 hPointwiseGood hCoarseNonconc hFinePairInc
    hCoarseInterp hProductScale hFiniteTangent hFiberSep
    hSharedPigeon hNormalCount hScaleFreeNormal hTangencyGeom
    hComparable hPacking hTransitivity hPolyScaleCount hSubfamily
    hRefinement hPolyRefinement hBipartite hTwoEnds
    hTangencyTwoEnds hFineAssignment hGoodPair hPairIncidence
  intro K D C_KT lambda M hK hD hC_KT hlambda hM epsilon hepsilon
  let L : ℝ := M
  have hL : 0 ≤ L := hM
  let scaleFactor : ℝ := (1 + L) * lambda
  have hscaleFactor : 1 ≤ scaleFactor := by
    dsimp only [scaleFactor]
    nlinarith [mul_le_mul (show (1 : ℝ) ≤ 1 + L by linarith)
      hlambda (by norm_num) (by linarith)]
  have hscaleFactorPos : 0 < scaleFactor :=
    zero_lt_one.trans_le hscaleFactor

  rcases hFineAssignment K D hK hD with
    ⟨C_R₀, hC_R₀Large, hFineAssignmentMain⟩
  have hC_R₀Pos : 0 < C_R₀ := by
    have hKPos : 0 < K := zero_lt_one.trans_le hK
    nlinarith [sq_pos_of_pos hKPos]
  let T : ℝ := 8 * K
  have hT : 1 ≤ T := by
    dsimp only [T]
    linarith
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  rcases ambient_restricted_fine_coarse_setup_uniform_tangency
      fine_shading_cover_volume centered_rectangle_enlargement
      hShadingComp hMaximal hPolyScaleCount hComparable hTransitivity
      ambient_restricted_fsv_geometry hCoarseGrouping
      hFineToCoarseCentral hSubfamily hFineTangencyLift
      hCompCoarseTan hTangencyGeom K D T C_R₀ hK hD hT hC_R₀Pos with
    ⟨tangency, C_R, C_count, C_shading, C_volume,
      htangency, hC_R₀_le, hC_R, hC_count, hC_shading, hC_volume,
      deltaFSV, hdeltaFSV, hdeltaFSVOne, hSetup⟩
  have hC_RPos : 0 < C_R := by linarith
  have hC_shadingOne : 1 ≤ C_shading := by linarith

  rcases ambient_restricted_parent_measure_scale
      hContain hCommon hComparable K D C_shading hK hD
      hC_shadingOne with
    ⟨C_out, hC_out, hParentMeasure⟩
  have hC_outPos : 0 < C_out := zero_lt_one.trans_le hC_out

  rcases ambient_restricted_cutoff_parent_tangency_scale
      selected_incidence_canonical_cutoffs
      selected_incidence_fiber_good_pairs
      selected_incidence_tangency_automatic_good_pairs
      selected_fiber_pair_incidence
      ambient_restricted_joint_parent_pair_incidence
      ambient_restricted_joint_parent_pair_incidence_tangency_automatic
      ambient_restricted_automatic_parent_tangency_scale
      ambient_restricted_parent_tangency_scale K D hK hD with
    ⟨C_inc, hC_inc, hParentTangency⟩

  rcases q_cluster_coarse_cardinality_branches
      hBipartite hScaleFreeNormal
      scale_free_normal_coarse_rectangle_count_from_pairs
      singleton_separated_tangent_ball_pair_at
      singleton_cluster_coarse_cardinality_witness K hK with
    ⟨C_positive, C_singleton, hC_positive, hC_singleton, hQCluster⟩

  rcases choose_faithful_canonical_metric_exponent
      epsilon D C_positive C_singleton hepsilon hD hC_positive with
    ⟨metricExponent, hmetricEq, hmetric, hmetricUpper,
      hmetricEight, hrepresentativeLoss, hfullLoss, hsmallJointMargin⟩

  let outerExponent : ℝ := metricExponent / 16
  have houterExponent : 0 < outerExponent := by
    dsimp only [outerExponent]
    positivity
  have houterTarget : outerExponent < epsilon := by
    dsimp only [outerExponent]
    linarith
  let coverExponent : ℝ := Real.log D / Real.log 2
  let branchParameter : ℝ :=
    faithfulCanonicalBranchParameter D C_positive C_singleton
  let loss : ℝ :=
    faithfulCanonicalFullLoss branchParameter metricExponent
  have hloss : 0 ≤ loss := by
    have hbranch :
        0 ≤ branchParameter := by
      dsimp only [branchParameter]
      exact faithfulCanonicalBranchParameter_nonneg
        D C_positive C_singleton hD hC_positive
    dsimp only [loss, faithfulCanonicalFullLoss,
      faithfulCanonicalRepresentativeLoss]
    positivity
  have hlossTarget : loss < epsilon := by
    simpa only [loss, branchParameter] using hfullLoss
  have hgap : 0 < 1 / 2 + loss - outerExponent := by
    have houterUpper : outerExponent ≤ 1 / 256 := by
      dsimp only [outerExponent]
      linarith
    linarith

  let parentConstant : ℝ :=
    faithfulCanonicalParentScaleConstant
      K T C_R C_inc metricExponent
  let retentionConstant : ℝ :=
    faithfulCanonicalRetentionInverseConstant K T metricExponent
  let clusterConstant : ℝ :=
    faithfulCanonicalClusterConstant T C_R metricExponent
  let localConstant : ℝ :=
    faithfulCanonicalActualCommonConstant
      parentConstant retentionConstant clusterConstant D
      C_positive C_singleton coverExponent tangency
  have hKPos : 0 < K := zero_lt_one.trans_le hK
  have hDPos : 0 < D := zero_lt_one.trans_le hD
  have hC_positivePos : 0 < C_positive :=
    zero_lt_one.trans_le hC_positive
  have htangencyPos : 0 < tangency := by linarith
  have hparentConstant : 0 < parentConstant := by
    have hincidence :
        0 <
          faithfulCanonicalIncidenceConstant
            T C_R C_inc metricExponent := by
      have hsqrtArgument :
          0 <
            32 * C_R *
              Real.rpow
                (96 *
                  Real.rpow (2 * T)
                    (metricExponent ^ 2))
                (1 / metricExponent) *
              Real.rpow 24
                (1 / (metricExponent ^ 2)) := by
        exact mul_pos
          (mul_pos
            (mul_pos (by norm_num) hC_RPos)
            (Real.rpow_pos_of_pos
              (mul_pos (by norm_num)
                (Real.rpow_pos_of_pos
                  (mul_pos (by norm_num) hTPos) _)) _))
          (Real.rpow_pos_of_pos (by norm_num) _)
      dsimp only [faithfulCanonicalIncidenceConstant]
      exact add_pos_of_pos_of_nonneg
        (mul_pos hC_inc (Real.sqrt_pos.2 hsqrtArgument))
        zero_le_one
    have hretention :
        0 <
          faithfulCanonicalRetentionConstant
            K T metricExponent := by
      dsimp only [faithfulCanonicalRetentionConstant]
      exact mul_pos
        (Real.rpow_pos_of_pos (mul_pos (by norm_num) hKPos) _)
        (Real.rpow_pos_of_pos (mul_pos (by norm_num) hTPos) _)
    dsimp only [parentConstant,
      faithfulCanonicalParentScaleConstant]
    positivity
  have hretentionConstant : 0 < retentionConstant := by
    dsimp only [retentionConstant,
      faithfulCanonicalRetentionInverseConstant]
    exact mul_pos
      (Real.rpow_pos_of_pos (mul_pos (by norm_num) hKPos) _)
      (Real.rpow_pos_of_pos (mul_pos (by norm_num) hTPos) _)
  have hclusterConstant : 0 < clusterConstant := by
    dsimp only [clusterConstant, faithfulCanonicalClusterConstant]
    exact mul_pos (mul_pos (by norm_num) hC_RPos)
      (Real.rpow_pos_of_pos
        (mul_pos (by norm_num)
          (Real.rpow_pos_of_pos
            (mul_pos (by norm_num) hTPos) _)) _)
  have hlocalConstant : 0 < localConstant := by
    let positiveConstant :=
      (4 *
          faithfulCanonicalPositiveBranchConstant
            C_positive tangency) *
        faithfulCanonicalFinalCoefficientConstant
          parentConstant retentionConstant clusterConstant D
          C_positive coverExponent
    have hbranchConstant :
        0 <
          faithfulCanonicalPositiveBranchConstant
            C_positive tangency := by
      dsimp only [faithfulCanonicalPositiveBranchConstant]
      exact mul_pos
        (mul_pos
          (mul_pos (by norm_num)
            (mul_pos (by norm_num)
              (Real.sqrt_pos.2 (by norm_num))))
          hC_positivePos)
        (Real.rpow_pos_of_pos htangencyPos _)
    have hfinalConstant :
        0 <
          faithfulCanonicalFinalCoefficientConstant
            parentConstant retentionConstant clusterConstant D
            C_positive coverExponent := by
      dsimp only [faithfulCanonicalFinalCoefficientConstant]
      exact mul_pos
        (mul_pos
          (Real.rpow_pos_of_pos hparentConstant _)
          hretentionConstant)
        (mul_pos
          (Real.rpow_pos_of_pos hclusterConstant _)
          (Real.rpow_pos_of_pos
            (mul_pos hDPos
              (Real.rpow_pos_of_pos
                (mul_pos (by norm_num) hclusterConstant) _)) _))
    have hpositiveConstant : 0 < positiveConstant := by
      dsimp only [positiveConstant]
      exact mul_pos (mul_pos (by norm_num) hbranchConstant)
        hfinalConstant
    dsimp only [localConstant,
      faithfulCanonicalActualCommonConstant]
    exact hpositiveConstant.trans_le (le_max_left _ _)

  let localC_KT : ℝ := scaleFactor * C_KT
  have hlocalC_KT : 0 < localC_KT := by
    dsimp only [localC_KT]
    positivity
  let geometricConstant : ℝ :=
    Real.sqrt (3 * localC_KT) *
        Real.rpow (4 * C_out ^ 2) (1 / 4 : ℝ) *
        Real.rpow
          (2 * C_shading * Real.sqrt C_shading)
          (3 / 4 : ℝ) /
      Real.sqrt C_R
  have hgeometricConstant : 0 < geometricConstant := by
    dsimp only [geometricConstant]
    exact div_pos
      (mul_pos
        (mul_pos
          (Real.sqrt_pos.2 (mul_pos (by norm_num) hlocalC_KT))
          (Real.rpow_pos_of_pos
            (mul_pos (by norm_num) (sq_pos_of_pos hC_outPos)) _))
        (Real.rpow_pos_of_pos
          (mul_pos
            (mul_pos (by norm_num)
              (zero_lt_one.trans_le hC_shadingOne))
            (Real.sqrt_pos.2
              (zero_lt_one.trans_le hC_shadingOne))) _))
      (Real.sqrt_pos.2 hC_RPos)

  rcases faithful_canonical_scaled_local_ambient_absorption
      localConstant geometricConstant scaleFactor D C_KT loss epsilon
      hlocalConstant hgeometricConstant hscaleFactor
      (zero_lt_one.trans_le hD) (zero_lt_one.trans_le hC_KT)
      hloss hlossTarget with
    ⟨deltaAmbient, hdeltaAmbient, hdeltaAmbientOne, hAmbientAbsorb⟩
  rcases faithful_canonical_scaled_small_bin_absorption
      localConstant geometricConstant scaleFactor C_KT loss outerExponent
      hlocalConstant hgeometricConstant hscaleFactorPos
      (zero_lt_one.trans_le hC_KT) hgap with
    ⟨deltaSmallBin, hdeltaSmallBin, hdeltaSmallBinOne, hSmallBinAbsorb⟩
  rcases faithful_canonical_heavy_log_loss_absorption
      C_count metricExponent hC_count.le hmetric with
    ⟨deltaHeavy, hdeltaHeavy, hdeltaHeavyHalf, hHeavyLog⟩
  rcases faithful_canonical_large_bin_volume_le_of_small_scale
      metricExponent C_count 3 T localC_KT C_R D
      hmetric hmetricUpper hC_count (by norm_num) hTPos
      hlocalC_KT hC_RPos hD with
    ⟨deltaLarge, hdeltaLarge, hdeltaLargeHalf, hLargeBin⟩

  rcases wz2_absorption_lemma
      K L lambda epsilon outerExponent 1 deltaFSV 1
      hK hL hlambda hepsilon houterExponent houterTarget
      (by norm_num) hdeltaFSV (by norm_num) with
    ⟨deltaBase, hdeltaBase, hdeltaBaseLambda, hdeltaBaseK,
      hdeltaBaseFSV, hdeltaBaseScaledFSV, hdeltaBaseScaledHalf,
      hdeltaBaseOne, hDyadicScale⟩
  rcases ambient_restricted_joint_metric_cutoff_exit
      joint_metric_cutoff_scale_exit
      K C_KT scaleFactor C_count metricExponent epsilon
      hK hC_KT hscaleFactor hC_count.le hmetric
      (hmetricUpper.trans (by norm_num)) hepsilon
      (le_of_lt hmetricEight) with
    ⟨deltaMetric, hdeltaMetric, hdeltaMetricHalf, hMetricExit⟩
  rcases ambient_restricted_small_joint_fiber_exit
      small_joint_fiber_scale_absorption
      K C_count metricExponent epsilon
      hK hC_count.le hmetric
      (hmetricUpper.trans (by norm_num)) hepsilon
      (by linarith [hmetricEight]) with
    ⟨deltaSmallJoint, hdeltaSmallJoint,
      hdeltaSmallJointHalf, hSmallJointExit⟩

  let delta₀ : ℝ :=
    min deltaBase <|
      min deltaAmbient <|
        min (deltaSmallBin / scaleFactor) <|
          min (deltaHeavy / scaleFactor) <|
            min (deltaLarge / scaleFactor) <|
              min (deltaMetric / scaleFactor)
                (deltaSmallJoint / scaleFactor)
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀Lambda : delta₀ ≤ 1 / lambda := by
    exact (show delta₀ ≤ deltaBase by simp [delta₀]).trans
      hdeltaBaseLambda

  refine ⟨delta₀, hdelta₀, hdelta₀Lambda, ?_⟩
  intro delta hdelta hdeltaBound family hfamily hUniform
    I hI F hF_family hF_separated hF_KT c mu hmu
    E₀ hE₀_meas hE₀_sub hmult

  let target : ℝ :=
    Real.rpow delta (-epsilon) *
      Real.rpow (mu : ℝ) (-3 / 2 : ℝ)
  have htarget : 0 ≤ target := by
    dsimp only [target]
    exact mul_nonneg
      (Real.rpow_nonneg hdelta.le _)
      (Real.rpow_nonneg (by exact_mod_cast hmu.le) _)
  by_cases hE₀_empty : E₀ = ∅
  · rw [hE₀_empty]
    simp
  have hE₀_nonempty : E₀.Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hE₀_empty
  have hstrip :
      E₀ ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c (c + 1) := by
    exact hE₀_sub.trans <| Set.prod_mono
      (fun _ hx => hx.1) (Set.Subset.refl _)
  have hstripVolume :
      volume (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c (c + 1)) = 1 := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    rw [MeasureTheory.Measure.prod_prod
      (Set.Icc (0 : ℝ) 1) (Set.Icc c (c + 1))]
    rw [Real.volume_Icc, Real.volume_Icc]
    norm_num
  have hE₀Volume : volume E₀ ≤ 1 :=
    (measure_mono hstrip).trans hstripVolume.le
  by_cases htargetOne : 1 ≤ target
  · calc
      volume E₀ ≤ 1 := hE₀Volume
      _ = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal target :=
        ENNReal.ofReal_le_ofReal htargetOne
  have htargetLtOne : target < 1 := lt_of_not_ge htargetOne

  have hdeltaBaseBound : delta ≤ deltaBase :=
    hdeltaBound.trans <| by simp [delta₀]
  have hdeltaAmbientBound : delta ≤ deltaAmbient :=
    hdeltaBound.trans <| by simp [delta₀]
  have hdeltaScaledSmallBin :
      scaleFactor * delta ≤ deltaSmallBin := by
    have hbound :
        delta ≤ deltaSmallBin / scaleFactor :=
      hdeltaBound.trans <| by simp [delta₀]
    calc
      scaleFactor * delta ≤
          scaleFactor * (deltaSmallBin / scaleFactor) := by
        gcongr
      _ = deltaSmallBin := by
        field_simp [hscaleFactorPos.ne']
  have hdeltaScaledHeavy :
      scaleFactor * delta ≤ deltaHeavy := by
    have hbound :
        delta ≤ deltaHeavy / scaleFactor :=
      hdeltaBound.trans <| by simp [delta₀]
    calc
      scaleFactor * delta ≤
          scaleFactor * (deltaHeavy / scaleFactor) := by
        gcongr
      _ = deltaHeavy := by
        field_simp [hscaleFactorPos.ne']
  have hdeltaScaledLarge :
      scaleFactor * delta ≤ deltaLarge := by
    have hbound :
        delta ≤ deltaLarge / scaleFactor :=
      hdeltaBound.trans <| by simp [delta₀]
    calc
      scaleFactor * delta ≤
          scaleFactor * (deltaLarge / scaleFactor) := by
        gcongr
      _ = deltaLarge := by
        field_simp [hscaleFactorPos.ne']
  have hdeltaScaledMetric :
      scaleFactor * delta ≤ deltaMetric := by
    have hbound :
        delta ≤ deltaMetric / scaleFactor :=
      hdeltaBound.trans <| by simp [delta₀]
    calc
      scaleFactor * delta ≤
          scaleFactor * (deltaMetric / scaleFactor) := by
        gcongr
      _ = deltaMetric := by
        field_simp [hscaleFactorPos.ne']
  have hdeltaScaledSmallJoint :
      scaleFactor * delta ≤ deltaSmallJoint := by
    have hbound :
        delta ≤ deltaSmallJoint / scaleFactor :=
      hdeltaBound.trans <| by simp [delta₀]
    calc
      scaleFactor * delta ≤
          scaleFactor * (deltaSmallJoint / scaleFactor) := by
        gcongr
      _ = deltaSmallJoint := by
        field_simp [hscaleFactorPos.ne']

  rcases hDyadicScale delta hdelta hdeltaBaseBound with
    ⟨N, hNScale, hNOuter, hNOuterSmall⟩
  let outerLoss : ℝ := (N : ℝ) ^ 2 + 1
  have houterLoss : 0 ≤ outerLoss := by
    dsimp only [outerLoss]
    positivity
  have houterLossOne : 1 ≤ outerLoss := by
    dsimp only [outerLoss]
    nlinarith only [sq_nonneg (N : ℝ)]
  have houterBound :
      outerLoss ≤
        Real.rpow (scaleFactor * delta) (-outerExponent) := by
    exact outer_loss_le_rpow_of_scaled_power_product_le_one
      scaleFactor delta outerExponent outerLoss hscaleFactorPos hdelta
      (by simpa only [outerLoss] using hNOuterSmall)

  let deltaBasePhysical : ℝ := lambda * delta
  let deltaVert : ℝ := (1 + L) * deltaBasePhysical
  have hdeltaBasePhysical : 0 < deltaBasePhysical := by
    dsimp only [deltaBasePhysical]
    positivity
  have hdeltaVert : 0 < deltaVert := by
    dsimp only [deltaVert]
    positivity
  have hdeltaVertEq : deltaVert = scaleFactor * delta := by
    dsimp only [deltaVert, deltaBasePhysical, scaleFactor]
    ring
  have hdeltaVertK : deltaVert ≤ K := by
    calc
      deltaVert = scaleFactor * delta := hdeltaVertEq
      _ ≤ scaleFactor * deltaBase := by
        gcongr
      _ ≤
          scaleFactor * (K / scaleFactor) := by
        gcongr
      _ = K := by
        field_simp [hscaleFactorPos.ne']
  have hNScale' :
      (2 : ℝ) ^ N * (1 + L) * deltaBasePhysical ≥ 4 * K := by
    simpa only [deltaBasePhysical, scaleFactor, mul_assoc] using hNScale
  have hNCard : (N * N : ℝ) ≤ outerLoss := by
    dsimp only [outerLoss]
    norm_num [pow_two]
  have hN2 : 2 ≤ N := by
    have hpow : 4 ≤ (2 : ℝ) ^ N := by
      have hscaled :
          (2 : ℝ) ^ N * deltaVert ≤
            (2 : ℝ) ^ N * K := by
        gcongr
      have hKscaled :
          4 * K ≤ (2 : ℝ) ^ N * K := by
        calc
          4 * K ≤ (2 : ℝ) ^ N * deltaVert := by
            simpa only [deltaVert, mul_assoc] using hNScale'
          _ ≤ (2 : ℝ) ^ N * K := hscaled
      exact le_of_mul_le_mul_right hKscaled hKPos
    by_contra hN
    have hNlt : N < 2 := Nat.lt_of_not_ge hN
    interval_cases N <;> norm_num at hpow
  have hbounds :
      ∀ f ∈ family, ∀ z : UnitPoint,
        |f.firstDeriv z| ≤ L := by
    intro f hf z
    exact HasUniformC2Bound.firstDerivative hUniform hf z

  rcases dyadic_fine_assignment_at_fixed_constant_with_level_bounds
      hTwoEnds hTangencyTwoEnds hK hD
      C_R₀ hC_R₀Large hFineAssignmentMain
      hfamily hF_family hI hdeltaBasePhysical
      (separationScale := delta) hdelta hF_separated hmu
      L hL hbounds hdeltaVertK
      metricExponent hmetric (metricExponent ^ 2)
      (sq_pos_of_pos hmetric)
      (c := c) hE₀_meas hE₀_nonempty hE₀_sub hmult
      outerLoss houterLossOne N hN2 hNScale' hNCard with
    ⟨E₂, tRep, DeltaRep, data, hdataMu, hambientSource,
      hsourceUpper, hfiberUpper, hE₂_meas, hE₂_sub, hretention⟩

  by_cases hE₂_empty : E₂ = ∅
  · have hzero : volume E₀ = 0 := by
      have hle := hretention
      rw [hE₂_empty, measure_empty, mul_zero] at hle
      exact le_bot_iff.mp hle
    rw [hzero]
    exact bot_le
  have hE₂_nonempty : E₂.Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hE₂_empty

  rcases hE₂_nonempty with ⟨point₂, hpoint₂⟩
  let point₂' : E₂ := ⟨point₂, hpoint₂⟩
  have htRepT : tRep ≤ T := by
    exact data.tRep_le_eight_diameter hdeltaVert point₂'
  have hdeltaVertFSV : deltaVert ≤ deltaFSV := by
    calc
      deltaVert = scaleFactor * delta := hdeltaVertEq
      _ ≤ scaleFactor * deltaBase := by
        gcongr
      _ ≤ deltaFSV := hdeltaBaseScaledFSV
  have hdeltaVertHalf : deltaVert ≤ 1 / 2 := by
    calc
      deltaVert = scaleFactor * delta := hdeltaVertEq
      _ ≤ scaleFactor * deltaBase := by
        gcongr
      _ ≤ 1 / 2 := hdeltaBaseScaledHalf
  have hC_RLarge : 9216 * K ^ 2 ≤ C_R :=
    hC_R₀Large.trans hC_R₀_le
  have hlocalKT :
      data.ambientSource.HasKatzTaoBound deltaVert localC_KT := by
    have htransport :=
      hF_KT.rescale_base hdelta hscaleFactor
    rw [hambientSource]
    simpa only [hdeltaVertEq, localC_KT] using htransport
  have hmuReal : 0 < (mu : ℝ) := by
    exact_mod_cast hmu
  have hmuUpper : (mu : ℝ) ≤ C_KT / delta := by
    let point₀ : E₀ :=
      ⟨hE₀_nonempty.some, hE₀_nonempty.some_mem⟩
    calc
      (mu : ℝ) ≤
          multiplicity F (lambda * delta) point₀ :=
        (hmult point₀ point₀.property).1
      _ ≤ (F.card : ℝ) :=
        multiplicity_le_family_card F (lambda * delta) point₀
      _ ≤ C_KT / delta := hF_KT.1
  have hdataMuReal : (data.mu : ℝ) = (mu : ℝ) := by
    exact_mod_cast hdataMu
  have hdeltaToVert : delta ≤ deltaVert := by
    rw [hdeltaVertEq]
    exact le_mul_of_one_le_left hdelta.le hscaleFactor
  have hrpowVert :
      Real.rpow deltaVert (-epsilon) ≤
        Real.rpow delta (-epsilon) :=
    Real.rpow_le_rpow_of_nonpos hdelta hdeltaToVert (by linarith)
  have hexitContradiction :
      1 ≤
          Real.rpow deltaVert (-epsilon) *
            Real.rpow (data.mu : ℝ) (-3 / 2 : ℝ) →
        False := by
    intro hexit
    have hmuPower :
        0 ≤ Real.rpow (mu : ℝ) (-3 / 2 : ℝ) :=
      Real.rpow_nonneg hmuReal.le _
    have hone : 1 ≤ target := by
      rw [hdataMuReal] at hexit
      exact hexit.trans <| by
        dsimp only [target]
        exact mul_le_mul_of_nonneg_right hrpowVert hmuPower
    exact (not_le_of_gt htargetLtOne) hone

  let commonTarget : ℝ :=
    faithfulCanonicalActualCommonLocalTarget
      parentConstant retentionConstant clusterConstant D
      C_positive C_singleton coverExponent tangency
      metricExponent geometricConstant deltaVert data.mu
  have hcommonTarget : 0 < commonTarget := by
    dsimp only [commonTarget,
      faithfulCanonicalActualCommonLocalTarget]
    exact mul_pos
      (mul_pos
        (mul_pos hlocalConstant
          (Real.rpow_pos_of_pos hdeltaVert _))
        (mul_pos hgeometricConstant hdeltaVert))
      (Real.rpow_pos_of_pos (by
        rw [hdataMuReal]
        exact hmuReal) _)
  have hsmallBin :
      outerLoss * deltaVert ^ 3 ≤ commonTarget := by
    have hraw :=
      hSmallBinAbsorb hdelta hdeltaScaledSmallBin hmuReal
        hmuUpper houterLoss houterBound
    rw [← hdeltaVertEq] at hraw
    rw [← hdataMuReal] at hraw
    simpa only [commonTarget,
      faithfulCanonicalActualCommonLocalTarget,
      localConstant, loss, branchParameter] using hraw
  have hglobalAbsorb :
      commonTarget * (D ^ 3 * (C_KT / delta)) ≤ target := by
    have hraw :=
      hAmbientAbsorb hdelta hdeltaAmbientBound hmuReal.le
    rw [← hdeltaVertEq] at hraw
    rw [← hdataMuReal] at hraw
    calc
      commonTarget * (D ^ 3 * (C_KT / delta)) ≤
          Real.rpow delta (-epsilon) *
            Real.rpow (data.mu : ℝ) (-3 / 2 : ℝ) := by
        simpa only [commonTarget,
          faithfulCanonicalActualCommonLocalTarget,
          localConstant, loss, branchParameter] using hraw
      _ = target := by
        rw [hdataMuReal]

  rcases ambient_ball_restricted_dyadic_decomposition
      hFiniteAmbient hD hdeltaVert hfamily hE₂_meas data with
    ⟨centers, hcover, hbinsMeasurable, hbinsSubset,
      hclusterFamily, hclusterDiameter, hfiberCluster, hcard⟩
  let bins : C2Function → Set (ℝ × ℝ) :=
    fun center => ambientRestrictedSet data center
  let ambient : C2Function → FiniteFunctionFamily :=
    fun center => data.ambientSource.cluster center (3 * tRep)

  have hlocal :
      ∀ center ∈ centers,
        ENNReal.ofReal outerLoss * volume (bins center) ≤
          ENNReal.ofReal commonTarget * (ambient center).card := by
    intro center hcenter
    by_cases hbinEmpty : bins center = ∅
    · rw [hbinEmpty, measure_empty, mul_zero]
      exact bot_le
    have hbin : (bins center).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hbinEmpty
    by_cases hsmall :
        volume (bins center) ≤ ENNReal.ofReal (deltaVert ^ 3)
    · have hsmallCard :
          volume (bins center) ≤
            ENNReal.ofReal (deltaVert ^ 3) *
              (ambient center).card := by
        exact ambientRestrictedSet_small_volume_exit
          data hdeltaVert center hE₂_meas hbin
          (deltaVert ^ 3) hsmall
      calc
        ENNReal.ofReal outerLoss * volume (bins center) ≤
            ENNReal.ofReal outerLoss *
              (ENNReal.ofReal (deltaVert ^ 3) *
                (ambient center).card) := by
          gcongr
        _ =
            ENNReal.ofReal
                (outerLoss * deltaVert ^ 3) *
              (ambient center).card := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul houterLoss]
        _ ≤
            ENNReal.ofReal commonTarget *
              (ambient center).card := by
          gcongr
    · have hmass :
          ENNReal.ofReal
              (Real.rpow deltaVert 3) <
            volume (bins center) := by
        have hrpowThree :
            Real.rpow deltaVert 3 = deltaVert ^ 3 :=
          Real.rpow_natCast deltaVert 3
        rw [hrpowThree]
        exact lt_of_not_ge hsmall
      have hbinOne : volume (bins center) ≤ 1 := by
        have hsubset : bins center ⊆ E₀ :=
          (hbinsSubset center hcenter).trans hE₂_sub
        exact (measure_mono (hsubset.trans hstrip)).trans
          hstripVolume.le
      rcases hSetup data center hfamily hE₂_meas hbin
          hdeltaVert hdeltaVertFSV htRepT hC_RLarge with
        ⟨fineSetup, coarseSetup, hcoarseTangency⟩
      rcases ambient_restricted_large_bin_refinement
          hFCMA hDyadicRefine hPolyRange
          joint_fiber_cardinality_regularization
          (data := data) (center := center) (hE := hE₂_meas)
          (fineSetup := fineSetup) (coarseSetup := coarseSetup)
          (massExponent := 3)
          hdeltaVert hdeltaVertHalf hC_count.le
          (by linarith [hC_shading]) (by norm_num)
          (by
            simpa only [deltaVert] using hmass)
          hbinOne with
        ⟨refinement⟩
      rcases ambient_restricted_joint_incidence_setup
          retained_incidence_degree_setup
          retained_heavy_support_setup
          ambient_restricted_parent_fiber_regularization
          data center hE₂_meas fineSetup coarseSetup refinement
          hdeltaVert with
        ⟨incidence⟩
      have hheavy :
          incidence.heavySetup.heavyLogLoss ≤
            Real.rpow deltaVert (-(metricExponent ^ 3)) :=
        hHeavyLog data center hE₂_meas fineSetup coarseSetup
          refinement incidence hdeltaVert (by
            simpa only [deltaBasePhysical, scaleFactor, mul_assoc] using
              hdeltaScaledHeavy)
      by_cases hqSmall :
          (incidence.q_fiber : ℝ) <
            8 * incidence.heavySetup.heavyLogLoss
      · exact False.elim <| hexitContradiction <|
          hSmallJointExit
            (D := D) data center hE₂_meas fineSetup coarseSetup
            refinement incidence rfl rfl rfl hdeltaVert
            (by
              simpa only [deltaBasePhysical, scaleFactor, mul_assoc] using
                hdeltaScaledSmallJoint)
            hqSmall
      have hqLarge :
          8 * incidence.heavySetup.heavyLogLoss ≤
            (incidence.q_fiber : ℝ) :=
        le_of_not_gt hqSmall
      let metricCut :=
        selectedIncidenceMetricCut
          incidence.heavySetup.heavyLogLoss
          (4 *
            Real.rpow (2 * tRep / DeltaRep)
              (metricExponent ^ 2))
          metricExponent * tRep
      by_cases hmetricCut :
          480 * K * deltaVert ≤ metricCut
      · have hcluster :
            deltaVert <
                  11 *
                    ambientRestrictedPaperClusterRadius
                      tRep metricExponent
                        incidence.heavySetup.heavyLogLoss
                        (4 *
                          Real.rpow (2 * tRep / DeltaRep)
                            (metricExponent ^ 2)) →
              Nonempty
                (AmbientRestrictedJointClusterSetupData
                  (D := D) data center hE₂_meas fineSetup
                    coarseSetup refinement incidence) := by
          intro hradius
          exact ambient_restricted_joint_cluster_setup
            ambient_restricted_paper_cluster_scale
            ambient_restricted_selected_fiber_ball_bound_on_retained
            selected_support_nonconcentration_setup
            selected_support_tangent_ball_cover
            data center hE₂_meas fineSetup coarseSetup
            refinement incidence (by linarith [hC_R]) hD
            hfamily hdeltaVert hradius
        have hqCluster :
            ∀ cluster : AmbientRestrictedJointClusterSetupData
                (D := D) data center hE₂_meas fineSetup
                  coarseSetup refinement incidence,
              QClusterCoarseCardinalityResult
                incidence.heavySetup.selectedCoarse.card
                (2 ^ incidence.heavySetup.supportLevel)
                cluster.cover.centers.card
                (data.ambientSource.cluster
                  center (3 * tRep)).card
                C_positive C_singleton coarseSetup.tangency
                cluster.A := by
          intro cluster
          exact hQCluster data center hE₂_meas fineSetup coarseSetup
            refinement incidence.degreeSetup incidence.q_fiber
            incidence.fiberBound incidence.heavySetup
            ((2 * incidence.heavySetup.heavyLogLoss) *
              cluster.coefficient)
            cluster.radius cluster.A cluster.nonconcentration
            cluster.cover hfamily cluster.ballCoefficient_small
            cluster.radius_pos cluster.A_ge_one
            cluster.scale_identity
            (data.delta_le_DeltaRep.trans
              cluster.proposition26_admissible)
        have hParentMeasure' :
            IsCinematicFamily family K D →
              0 < deltaVert →
                1 ≤ C_R →
                  ((2 ^ refinement.parentLevel : ℕ) : ℝ) ≤
                    faithfulCanonicalParentArea
                        C_out DeltaRep C_R tRep /
                      (((2 : ENNReal) ^ refinement.layer.val *
                        refinement.cutoff).toReal) := by
          intro hfamily' hdeltaVert' hC_ROne
          simpa only [faithfulCanonicalParentArea] using
            hParentMeasure data center hE₂_meas fineSetup
              coarseSetup refinement hfamily' hdeltaVert' hC_ROne
        have hParentTangency' :
            IsCinematicFamily family K D →
              0 < deltaVert →
                0 < C_R →
                  2 ≤ incidence.q_fiber →
                    (∀ p : ambientRestrictedSet data center,
                      deltaVert /
                          (ambientRestrictedData data center
                            hE₂_meas).exactT p <
                        selectedIncidenceMetricCut
                          incidence.heavySetup.heavyLogLoss
                          (4 *
                            Real.rpow (2 * tRep / DeltaRep)
                              (metricExponent ^ 2))
                          metricExponent) →
                      10 * deltaVert ≤
                        (selectedIncidenceMetricCut
                              incidence.heavySetup.heavyLogLoss
                              (4 *
                                Real.rpow (2 * tRep / DeltaRep)
                                  (metricExponent ^ 2))
                              metricExponent *
                            tRep / 8) /
                          (6 * K) →
                        100 * deltaVert ≤
                          C_R * tRep * DeltaRep / deltaVert →
                          (∀ p : E₂,
                            ((data.assignment.fiber p).card : ℝ) <
                              2 * (data.mu : ℝ)) →
                            ((incidence.heavySetup.M_parent : ℕ) : ℝ) ≤
                              faithfulCanonicalCutoffParentScale
                                  deltaVert tRep DeltaRep C_R C_inc
                                  incidence.heavySetup.heavyLogLoss
                                  metricExponent incidence.retention
                                  incidence.heavySetup.degreeLoss *
                                Real.rpow (data.mu : ℝ) (-2) *
                                Real.rpow
                                  (2 ^
                                    incidence.heavySetup.supportLevel :
                                      ℕ) 2 := by
          intro hfamily' hdeltaVert' hC_R'
            hq hmetricPointwise hten hhundred hfiber
          simpa only [faithfulCanonicalCutoffParentScale] using
            hParentTangency data center hE₂_meas fineSetup
              coarseSetup refinement incidence hfamily'
              hdeltaVert' hC_R' hq hmetricPointwise hten
              hhundred hfiber
        have hlargeResult :=
          hLargeBin data center hE₂_meas fineSetup coarseSetup
            refinement incidence C_out C_inc outerLoss
            C_positive C_singleton hcluster hParentMeasure'
            hParentTangency' hqCluster hCoarseInterp hK hfamily
            hdeltaVert (by
              simpa only [deltaBasePhysical, scaleFactor, mul_assoc] using
                hdeltaScaledLarge)
            hKPos htRepT hC_R
            (by linarith [hC_shading]) hC_outPos hC_inc
            hC_positive hC_singleton houterLoss hlocalKT
            hheavy (by
              simpa only [deltaBasePhysical, scaleFactor, mul_assoc,
                outerExponent] using houterBound)
            hqLarge hmetricCut (by
              simpa only [hdataMu] using hfiberUpper)
        rcases hlargeResult with ⟨cluster, hvolume⟩
        simpa only [commonTarget, parentConstant,
          retentionConstant, clusterConstant, coverExponent,
          geometricConstant, localC_KT, hcoarseTangency] using hvolume
      · have hmetricFailure : metricCut < 480 * K * deltaVert :=
          lt_of_not_ge hmetricCut
        exact False.elim <| hexitContradiction <|
          hMetricExit
            (baseDelta := delta)
            data center hE₂_meas fineSetup coarseSetup
            refinement incidence hdeltaVert (by
              simpa only [deltaBasePhysical, scaleFactor, mul_assoc] using
                hdeltaScaledMetric)
            hdelta hdeltaVertEq
            (by
              rw [hambientSource]
              exact hF_KT)
            rfl rfl rfl hmetricFailure

  have hcard' :
      (∑ center ∈ centers, ((ambient center).card : ℝ)) ≤
        D ^ 3 * (F.card : ℝ) := by
    simpa only [ambient, hambientSource] using hcard
  exact retained_ambient_ball_volume_assembly_of_scaled_local
    bins ambient hDPos.le hdelta houterLoss hF_KT
    hcommonTarget.le htarget hretention hcover hlocal hcard'
    hglobalAbsorb

end Kakeya.Cinematic
