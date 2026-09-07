import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63SequentialReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63AlignedOneScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DyadicPropertyThreeMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DyadicCurrentReentry

/-!
# Aligned Phase-1 candidate for Proposition 6.3

This module composes the certified Property-(P) construction with the aligned
critical-to-query scale transport.  It is the concrete one-scale analytic
leaf used by the finite Lemma 4.11/4.12 iteration: the fresh sticky witness,
the retained candidate shading, and the ambient plane map are unchanged.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

/-- Produce one finite-grid query estimate from the fresh current-relative
Proposition 6.2 witness.  Property-(P) gives the estimate at
`48 * rho ^ 2`; integer alignment and a strict loss gap transport it to the
original query scale without changing the candidate or its mass ledger. -/
theorem Proposition63CurrentShadingReentryData.phase1AlignedCandidate_of_bounds
    {delta sigma initialInputLoss normalizationLoss reentryLoss stickyDataLoss
      phase1Loss sourceADLoss criticalLoss queryLoss queryScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent logExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    {rho : WZ2PaperRequestedScale delta}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyDataLoss)
      data.normalization.croppedRefined rho logExponent)
    (planeMap : Point3 → Point3)
    (leftFactor rightFactor : ENNReal)
    (hleft : leftFactor ≤
      (73 / 100 : ENNReal) * data.normalizationWeight)
    (hright : data.regularized.regularizationLoss *
        propertyThreeCommonHullMassLoss sticky ≤ rightFactor)
    (hplaneUnit : ∀ point ∈ data.normalization.croppedRefined.union,
      ‖planeMap point‖ = 1)
    (hrhoAligned : rho.1 = alignedCoarseScale delta queryScale)
    (hphase1Loss : 0 < phase1Loss)
    (hreentryPhase1 : data.reentryNormalizationLoss ≤ phase1Loss)
    (hphase1Slack :
      (wz2PaperPureRefinementFraction delta logExponent)⁻¹ *
          Kakeya.realRpowENN delta phase1Loss ≤
        Kakeya.realRpowENN delta data.reentryNormalizationLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hreentryLoss : 0 < data.reentryNormalizationLoss)
    (hreentrySticky : data.reentryNormalizationLoss ≤ stickyDataLoss)
    (hstickySmall : 6 * stickyDataLoss <
      sigma + 2 * data.reentryNormalizationLoss)
    (hrhoSmall : rho.1 ≤ 1 / 10000)
    (hrhoPropertyP : rho.1 ≤ (3 : ℝ) ^ (-(20 / sigma)))
    (hhavg :
      (PureWZ2.h_avg_m_val sigma data.reentryNormalizationLoss rho.1 : ℝ) *
          rho.1 ^ (sigma - 3 * stickyDataLoss) < 1 / 8)
    (hreentryCritical : data.reentryNormalizationLoss ≤ criticalLoss)
    (hcommonSlack : propertyThreeCommonHullMassLoss sticky *
        Kakeya.realRpowENN delta criticalLoss ≤
      Kakeya.realRpowENN delta data.reentryNormalizationLoss)
    (hdeltaOne : delta < 1)
    (hcriticalLoss : 0 < criticalLoss)
    (hsourceADLoss : 0 < sourceADLoss)
    (hADGap : sourceADLoss < criticalLoss)
    (hADSmall : delta ≤ Real.rpow (10 : ℝ)
      (-1 / (criticalLoss - sourceADLoss)))
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : ∀ epsilon₁ : ℝ, epsilon₁ =
        (sigma - 2 * data.reentryNormalizationLoss) / 20 →
      0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hrhoLower : Real.rpow delta stickyDataLoss ≤ rho.1)
    (hrhoBound : rho.1 ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (hstickyAD : 3 * stickyDataLoss ≤ sourceADLoss)
    (hqueryPos : 0 < queryScale)
    (hquerySmall : queryScale ≤ 1 / 4)
    (hqueryGridFloor : 48 * delta ^ 2 ≤ queryScale)
    (hcriticalQuery : criticalLoss < queryLoss)
    (hqueryAbsorb : delta ≤ Real.rpow (40 : ℝ)
      (-1 / (queryLoss - criticalLoss))) :
    ∃ oneScale : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := queryLoss)
        (rho := queryScale)
        (Y := data.normalization.croppedRefined)
        (fun point => planeMap point),
      leftFactor * current.mass ≤
        rightFactor * oneScale.shading.mass := by
  have alignedMultiplicityPos :
      0 < alignedCoarseMultiplicity delta queryScale :=
    alignedCoarseMultiplicity_pos data.reentry_extremal.delta_pos hqueryPos
  have requestedAligned :
      rho.1 = (alignedCoarseMultiplicity delta queryScale : ℝ) * delta := by
    simpa only [alignedCoarseScale] using hrhoAligned
  rcases data.phase1CriticalCandidate_of_bounds sticky planeMap
      leftFactor rightFactor hleft hright hplaneUnit
      (alignedCoarseMultiplicity delta queryScale) alignedMultiplicityPos
      requestedAligned hphase1Loss hreentryPhase1 hphase1Slack hsigma
      hsigmaOne hreentryLoss hreentrySticky hstickySmall hrhoSmall
      hrhoPropertyP hhavg hreentryCritical hcommonSlack hdeltaOne
      hcriticalLoss hsourceADLoss hADGap hADSmall logScale hrhoLog hlog
      hrhoLower hrhoBound hstickyAD with ⟨critical, criticalMass⟩
  have queryCritical : queryScale ≤ 48 * rho.1 ^ 2 := by
    rw [hrhoAligned]
    exact query_le_fortyEight_mul_alignedCoarseScale_sq
      data.reentry_extremal.delta_pos hqueryPos
  have criticalRatio : 48 * rho.1 ^ 2 < 4 * queryScale := by
    rw [hrhoAligned]
    exact fortyEight_mul_alignedCoarseScale_sq_lt_four_mul_query
      data.reentry_extremal.delta_pos hqueryPos hqueryGridFloor
  have criticalOne : 48 * rho.1 ^ 2 ≤ 1 :=
    criticalRatio.le.trans (by linarith)
  let query :=
    PureWZ2OneScaleLocalGrainData.refineAlignedQueryScale critical
      hqueryPos queryCritical criticalRatio criticalOne
      hcriticalQuery hqueryAbsorb
  refine ⟨query, ?_⟩
  simpa only [query,
    PureWZ2OneScaleLocalGrainData.refineAlignedQueryScale,
    PureWZ2OneScaleLocalGrainData.refineQueryScale] using criticalMass

/-- Sharper aligned Phase-1 candidate for a current shading which is already
in one dyadic point-multiplicity band.  The common-spatial pullback then pays
only one coarse multiplicity cap; the selected fine-family cardinality is
cancelled before extremality is restored. -/
theorem Proposition63CurrentShadingReentryData.phase1AlignedDyadicCandidate_of_bounds
    {delta sigma initialInputLoss normalizationLoss reentryLoss stickyDataLoss
      phase1Loss sourceADLoss criticalLoss queryLoss queryScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent logExponent multiplicity : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    {rho : WZ2PaperRequestedScale delta}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyDataLoss)
      data.normalization.croppedRefined rho logExponent)
    (planeMap : Point3 → Point3)
    (leftFactor rightFactor : ENNReal)
    (hleft : leftFactor ≤
      (73 / 100 : ENNReal) * data.normalizationWeight)
    (hright : data.regularized.regularizationLoss *
        propertyThreeDyadicCommonHullMassLoss sticky ≤ rightFactor)
    (hcurrentLower : ∀ point ∈ data.normalization.croppedRefined.union,
      multiplicity ≤ data.normalization.croppedRefined.pointMultiplicity point)
    (hcurrentUpper : ∀ point ∈ data.normalization.croppedRefined.union,
      data.normalization.croppedRefined.pointMultiplicity point <
        2 * multiplicity)
    (hplaneUnit : ∀ point ∈ data.normalization.croppedRefined.union,
      ‖planeMap point‖ = 1)
    (hrhoAligned : rho.1 = alignedCoarseScale delta queryScale)
    (hphase1Loss : 0 < phase1Loss)
    (hreentryPhase1 : data.reentryNormalizationLoss ≤ phase1Loss)
    (hphase1Slack :
      (wz2PaperPureRefinementFraction delta logExponent)⁻¹ *
          Kakeya.realRpowENN delta phase1Loss ≤
        Kakeya.realRpowENN delta data.reentryNormalizationLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hreentryLoss : 0 < data.reentryNormalizationLoss)
    (hreentrySticky : data.reentryNormalizationLoss ≤ stickyDataLoss)
    (hstickySmall : 6 * stickyDataLoss <
      sigma + 2 * data.reentryNormalizationLoss)
    (hrhoSmall : rho.1 ≤ 1 / 10000)
    (hrhoPropertyP : rho.1 ≤ (3 : ℝ) ^ (-(20 / sigma)))
    (hhavg :
      (PureWZ2.h_avg_m_val sigma data.reentryNormalizationLoss rho.1 : ℝ) *
          rho.1 ^ (sigma - 3 * stickyDataLoss) < 1 / 8)
    (hreentryCritical : data.reentryNormalizationLoss ≤ criticalLoss)
    (hcommonSlack : propertyThreeDyadicCommonHullMassLoss sticky *
        Kakeya.realRpowENN delta criticalLoss ≤
      Kakeya.realRpowENN delta data.reentryNormalizationLoss)
    (hdeltaOne : delta < 1)
    (hcriticalLoss : 0 < criticalLoss)
    (hsourceADLoss : 0 < sourceADLoss)
    (hADGap : sourceADLoss < criticalLoss)
    (hADSmall : delta ≤ Real.rpow (10 : ℝ)
      (-1 / (criticalLoss - sourceADLoss)))
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : ∀ epsilon₁ : ℝ, epsilon₁ =
        (sigma - 2 * data.reentryNormalizationLoss) / 20 →
      0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hrhoLower : Real.rpow delta stickyDataLoss ≤ rho.1)
    (hrhoBound : rho.1 ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (hstickyAD : 3 * stickyDataLoss ≤ sourceADLoss)
    (hqueryPos : 0 < queryScale)
    (hquerySmall : queryScale ≤ 1 / 4)
    (hqueryGridFloor : 48 * delta ^ 2 ≤ queryScale)
    (hcriticalQuery : criticalLoss < queryLoss)
    (hqueryAbsorb : delta ≤ Real.rpow (40 : ℝ)
      (-1 / (queryLoss - criticalLoss))) :
    ∃ oneScale : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := queryLoss)
        (rho := queryScale)
        (Y := data.normalization.croppedRefined)
        (fun point => planeMap point),
      leftFactor * current.mass ≤ rightFactor * oneScale.shading.mass := by
  rcases phase1_sticky_to_Z_and_propertyP_certified sticky
      data.normalization.final_extremal
      data.normalization.cropped_top_level_cwa hphase1Loss hreentryPhase1
      hrhoSmall hphase1Slack hsigma hsigmaOne hreentryLoss hreentrySticky
      hstickySmall hrhoPropertyP hhavg with
    ⟨_Z, _hZSub, _hZExtremal, _hZCWA, epsilon₁, epsilon₃, propP,
      hepsilon₁Def, hepsilon₁, hepsilon₁Small, hepsilon₃,
      hepsilon₃Def, hepsilonSum, htauPos, hrhoTau, htauSq, htauOne,
      hpropertyThreeEq, _hZCoarse, _⟩
  let massLoss : ENNReal := propertyThreeDyadicCommonHullMassLoss sticky
  have hmassLoss := propertyThreeDyadicCommonHullMassLoss_pos_ne_top
    sticky data.reentry_extremal.delta_pos hdeltaOne
  have hmass : massLoss⁻¹ * data.normalization.croppedRefined.mass ≤
      (ambientPropertyThreeCommonHull sticky propP.propertyThree).mass := by
    exact propertyThreeDyadicCommonHullMassLoss_inv_mul_source_mass_le
      sticky propP data.reentry_extremal.delta_pos hdeltaOne
      hcurrentLower hcurrentUpper
  have hsqrtThree : Real.sqrt 3 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have htauTwenty : rho.1 * Real.sqrt 3 ≤ 20 * rho.1 := by
    have hscaled := mul_le_mul_of_nonneg_left hsqrtThree
      sticky.coarse_extremal.delta_pos.le
    nlinarith [hscaled]
  have hrhoThousand : rho.1 ≤ 1 / 1000 :=
    hrhoSmall.trans (by norm_num)
  have hrhoHalf : rho.1 ≤ 1 / 2 := hrhoSmall.trans (by norm_num)
  have hpropertyThree : ∀ parent : Fin sticky.coarse.card,
      ∀ point : Point3, point ∈ propP.propertyThree.carrier parent →
        Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
            ENNReal.ofReal (rho.1 * Real.sqrt 3) ≤
          volume (propP.propertyThree.carrier parent ∩
            Metric.closedBall point (rho.1 * Real.sqrt 3)) := by
    rw [hpropertyThreeEq]
    exact propP.propertyOne_full
  have hepsilon₃Large : 9 / 10 < epsilon₃ := by
    rw [hepsilon₃Def, hepsilon₁Def]
    linarith
  have hepsilon₃One : epsilon₃ < 1 := by
    rw [hepsilon₃Def]
    linarith
  have haxis := cordoba_ax_condition rho.1 epsilon₃
    sticky.coarse_extremal.delta_pos hrhoSmall hepsilon₃Large hepsilon₃One
  rcases data.criticalPropertyThreeCandidate sticky propP planeMap hplaneUnit
      (alignedCoarseMultiplicity delta queryScale)
      (alignedCoarseMultiplicity_pos data.reentry_extremal.delta_pos hqueryPos)
      (by simpa only [alignedCoarseScale] using hrhoAligned)
      massLoss hmassLoss.1 hmassLoss.2 hmass
      hreentryCritical hcommonSlack hdeltaOne hcriticalLoss hsourceADLoss
      hADGap hADSmall rfl htauPos htauTwenty hrhoTau htauSq htauOne
      hrhoThousand hrhoHalf hsigma hsigmaOne hepsilon₁ hepsilon₁Small
      hepsilon₃ hepsilon₃Def hepsilonSum logScale hrhoLog
      (hlog epsilon₁ hepsilon₁Def) hpropertyThree haxis hrhoLower
      hrhoBound hstickyAD with ⟨critical, criticalMass⟩
  have queryCritical : queryScale ≤ 48 * rho.1 ^ 2 := by
    rw [hrhoAligned]
    exact query_le_fortyEight_mul_alignedCoarseScale_sq
      data.reentry_extremal.delta_pos hqueryPos
  have criticalRatio : 48 * rho.1 ^ 2 < 4 * queryScale := by
    rw [hrhoAligned]
    exact fortyEight_mul_alignedCoarseScale_sq_lt_four_mul_query
      data.reentry_extremal.delta_pos hqueryPos hqueryGridFloor
  have criticalOne : 48 * rho.1 ^ 2 ≤ 1 :=
    criticalRatio.le.trans (by linarith)
  let query :=
    PureWZ2OneScaleLocalGrainData.refineAlignedQueryScale critical
      hqueryPos queryCritical criticalRatio criticalOne
      hcriticalQuery hqueryAbsorb
  refine ⟨query, ?_⟩
  calc
    leftFactor * current.mass ≤
        ((73 / 100 : ENNReal) * data.normalizationWeight) * current.mass :=
      mul_le_mul_left hleft _
    _ ≤ data.regularized.regularizationLoss *
        data.normalization.croppedRefined.mass := data.reentryMassRetention
    _ ≤ data.regularized.regularizationLoss *
        (massLoss * query.shading.mass) := by
      apply mul_le_mul_right
      simpa only [query,
        PureWZ2OneScaleLocalGrainData.refineAlignedQueryScale,
        PureWZ2OneScaleLocalGrainData.refineQueryScale] using criticalMass
    _ = (data.regularized.regularizationLoss * massLoss) *
        query.shading.mass := by ring
    _ ≤ rightFactor * query.shading.mass :=
      mul_le_mul_left (by simpa only [massLoss] using hright) _

/-- The production Phase-1 entry point after pre-Phase-1 dyadic selection.
The sticky witness is applied to the exact ordinary re-entry source carried
by `dyadic.reentry`; the point-multiplicity band is therefore an explicit
hypothesis on that same source, never on the pre-re-entry ambient shading. -/
theorem Proposition63DyadicCurrentReentryData.phase1AlignedCandidate_of_bounds
    {delta sigma initialInputLoss normalizationLoss densityLoss incidence
      currentLoss dyadicLoss weightLoss reentryLoss reentryNormalizationLoss
      stickyDataLoss phase1Loss sourceADLoss criticalLoss queryLoss queryScale :
      ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent logExponent multiplicity : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent
        densityLoss}
    {current : WZ1PaperTubeShading root.normalization.croppedFamily}
    {currentMap : PaperWZ1WeakPlaneMapData current incidence}
    (dyadic : Proposition63DyadicCurrentReentryData
      (currentLoss := currentLoss) (dyadicLoss := dyadicLoss)
      (weightLoss := weightLoss) (reentryLoss := reentryLoss)
      (reentryNormalizationLoss := reentryNormalizationLoss)
      root current currentMap)
    {rho : WZ2PaperRequestedScale delta}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyDataLoss)
      dyadic.reentry.normalization.croppedRefined rho logExponent)
    (leftFactor rightFactor : ENNReal)
    (hleft : leftFactor ≤
      (73 / 100 : ENNReal) * dyadic.reentry.normalizationWeight)
    (hright : dyadic.reentry.regularized.regularizationLoss *
        propertyThreeDyadicCommonHullMassLoss sticky ≤ rightFactor)
    (hsourceLower : ∀ point ∈
      dyadic.reentry.normalization.croppedRefined.union,
      multiplicity ≤
        dyadic.reentry.normalization.croppedRefined.pointMultiplicity point)
    (hsourceUpper : ∀ point ∈
      dyadic.reentry.normalization.croppedRefined.union,
      dyadic.reentry.normalization.croppedRefined.pointMultiplicity point <
        2 * multiplicity)
    (hrhoAligned : rho.1 = alignedCoarseScale delta queryScale)
    (hphase1Loss : 0 < phase1Loss)
    (hreentryPhase1 : dyadic.reentry.reentryNormalizationLoss ≤ phase1Loss)
    (hphase1Slack :
      (wz2PaperPureRefinementFraction delta logExponent)⁻¹ *
          Kakeya.realRpowENN delta phase1Loss ≤
        Kakeya.realRpowENN delta
          dyadic.reentry.reentryNormalizationLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hreentryLoss : 0 < dyadic.reentry.reentryNormalizationLoss)
    (hreentrySticky :
      dyadic.reentry.reentryNormalizationLoss ≤ stickyDataLoss)
    (hstickySmall : 6 * stickyDataLoss <
      sigma + 2 * dyadic.reentry.reentryNormalizationLoss)
    (hrhoSmall : rho.1 ≤ 1 / 10000)
    (hrhoPropertyP : rho.1 ≤ (3 : ℝ) ^ (-(20 / sigma)))
    (hhavg :
      (PureWZ2.h_avg_m_val sigma
          dyadic.reentry.reentryNormalizationLoss rho.1 : ℝ) *
          rho.1 ^ (sigma - 3 * stickyDataLoss) < 1 / 8)
    (hreentryCritical :
      dyadic.reentry.reentryNormalizationLoss ≤ criticalLoss)
    (hcommonSlack : propertyThreeDyadicCommonHullMassLoss sticky *
        Kakeya.realRpowENN delta criticalLoss ≤
      Kakeya.realRpowENN delta dyadic.reentry.reentryNormalizationLoss)
    (hdeltaOne : delta < 1)
    (hcriticalLoss : 0 < criticalLoss)
    (hsourceADLoss : 0 < sourceADLoss)
    (hADGap : sourceADLoss < criticalLoss)
    (hADSmall : delta ≤ Real.rpow (10 : ℝ)
      (-1 / (criticalLoss - sourceADLoss)))
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : ∀ epsilon₁ : ℝ, epsilon₁ =
        (sigma - 2 * dyadic.reentry.reentryNormalizationLoss) / 20 →
      0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hrhoLower : Real.rpow delta stickyDataLoss ≤ rho.1)
    (hrhoBound : rho.1 ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (hstickyAD : 3 * stickyDataLoss ≤ sourceADLoss)
    (hqueryPos : 0 < queryScale)
    (hquerySmall : queryScale ≤ 1 / 4)
    (hqueryGridFloor : 48 * delta ^ 2 ≤ queryScale)
    (hcriticalQuery : criticalLoss < queryLoss)
    (hqueryAbsorb : delta ≤ Real.rpow (40 : ℝ)
      (-1 / (queryLoss - criticalLoss))) :
    ∃ oneScale : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := queryLoss)
        (rho := queryScale)
        (Y := dyadic.reentry.normalization.croppedRefined)
        (fun point => dyadic.planeMap.planeMap point),
      leftFactor * dyadic.shading.mass ≤
        rightFactor * oneScale.shading.mass := by
  have hplaneUnit : ∀ point ∈
      dyadic.reentry.normalization.croppedRefined.union,
      ‖dyadic.planeMap.planeMap point‖ = 1 := by
    intro point hpoint
    have pointDyadic : point ∈ dyadic.shading.union :=
      dyadic.reentry.normalization_croppedRefined_union_subset_current hpoint
    exact dyadic.planeMap.unit point pointDyadic
  exact dyadic.reentry.phase1AlignedDyadicCandidate_of_bounds sticky
    dyadic.planeMap.planeMap leftFactor rightFactor hleft hright
    hsourceLower hsourceUpper hplaneUnit hrhoAligned hphase1Loss
    hreentryPhase1 hphase1Slack hsigma hsigmaOne hreentryLoss
    hreentrySticky hstickySmall hrhoSmall hrhoPropertyP hhavg
    hreentryCritical hcommonSlack hdeltaOne hcriticalLoss hsourceADLoss
    hADGap hADSmall logScale hrhoLog hlog hrhoLower hrhoBound hstickyAD
    hqueryPos hquerySmall hqueryGridFloor hcriticalQuery hqueryAbsorb

/-- Run the sharp Phase-1 construction after a genuine current-shading
re-entry has selected a tube subfamily.  The sticky fine source supplies the
upper multiplicity bound through restriction, while the outer common hull
restores the lower multiplicity of the pre-re-entry dyadic shading. -/
theorem Proposition63DyadicCurrentReentryData.phase1AlignedAmbientCandidate_of_bounds
    {delta sigma initialInputLoss normalizationLoss densityLoss incidence
      currentLoss dyadicLoss weightLoss reentryLoss reentryNormalizationLoss
      stickyDataLoss phase1Loss sourceADLoss criticalLoss queryLoss queryScale :
      ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent logExponent : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent
        densityLoss}
    {current : WZ1PaperTubeShading root.normalization.croppedFamily}
    {currentMap : PaperWZ1WeakPlaneMapData current incidence}
    (dyadic : Proposition63DyadicCurrentReentryData
      (currentLoss := currentLoss) (dyadicLoss := dyadicLoss)
      (weightLoss := weightLoss) (reentryLoss := reentryLoss)
      (reentryNormalizationLoss := reentryNormalizationLoss)
      root current currentMap)
    {rho : WZ2PaperRequestedScale delta}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyDataLoss)
      dyadic.reentry.normalization.croppedRefined rho logExponent)
    (coarseMultiplicity regularity : ENNReal)
    (hcoarseMultiplicityPos : 0 < coarseMultiplicity)
    (hcoarseMultiplicityTop : coarseMultiplicity ≠ ⊤)
    (hregularityPos : 0 < regularity)
    (hregularityTop : regularity ≠ ⊤)
    (hcoarseLower : ∀ point ∈ sticky.croppedCoarseShading.union,
      coarseMultiplicity ≤
        sticky.croppedCoarseShading.pointMultiplicity point)
    (hcoarseUpper : ∀ point ∈ sticky.croppedCoarseShading.union,
      (sticky.croppedCoarseShading.pointMultiplicity point : ENNReal) ≤
        regularity * coarseMultiplicity)
    (leftFactor rightFactor : ENNReal)
    (hleft : leftFactor ≤
      (73 / 100 : ENNReal) * dyadic.reentry.normalizationWeight)
    (hright : dyadic.reentry.regularized.regularizationLoss *
        ((4 * regularity) *
          (wz2PaperPureRefinementFraction delta logExponent)⁻¹) ≤
        rightFactor)
    (hrhoAligned : rho.1 = alignedCoarseScale delta queryScale)
    (hphase1Loss : 0 < phase1Loss)
    (hreentryPhase1 : dyadic.reentry.reentryNormalizationLoss ≤ phase1Loss)
    (hphase1Slack :
      (wz2PaperPureRefinementFraction delta logExponent)⁻¹ *
          Kakeya.realRpowENN delta phase1Loss ≤
        Kakeya.realRpowENN delta
          dyadic.reentry.reentryNormalizationLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hreentryLoss : 0 < dyadic.reentry.reentryNormalizationLoss)
    (hreentrySticky :
      dyadic.reentry.reentryNormalizationLoss ≤ stickyDataLoss)
    (hstickySmall : 6 * stickyDataLoss <
      sigma + 2 * dyadic.reentry.reentryNormalizationLoss)
    (hrhoSmall : rho.1 ≤ 1 / 10000)
    (hrhoPropertyP : rho.1 ≤ (3 : ℝ) ^ (-(20 / sigma)))
    (hhavg :
      (PureWZ2.h_avg_m_val sigma
          dyadic.reentry.reentryNormalizationLoss rho.1 : ℝ) *
          rho.1 ^ (sigma - 3 * stickyDataLoss) < 1 / 8)
    (hdyadicCritical : dyadicLoss ≤ criticalLoss)
    (hnormalizationCritical : normalizationLoss ≤ criticalLoss)
    (hcommonDensityLift :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (dyadic.reentry.regularized.regularizationLoss *
            dyadic.reentry.weightUpper *
              ((4 * regularity) *
                (wz2PaperPureRefinementFraction delta logExponent)⁻¹)) *
          Kakeya.realRpowENN delta criticalLoss ≤
        dyadic.reentry.normalizationWeight *
          Kakeya.realRpowENN delta
            dyadic.reentry.reentryNormalizationLoss)
    (hdeltaOne : delta < 1)
    (_hcriticalLoss : 0 < criticalLoss)
    (hsourceADLoss : 0 < sourceADLoss)
    (hADGap : sourceADLoss < criticalLoss)
    (hADSmall : delta ≤ Real.rpow (10 : ℝ)
      (-1 / (criticalLoss - sourceADLoss)))
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : ∀ epsilon₁ : ℝ, epsilon₁ =
        (sigma - 2 * dyadic.reentry.reentryNormalizationLoss) / 20 →
      0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hrhoLower : Real.rpow delta stickyDataLoss ≤ rho.1)
    (hrhoBound : rho.1 ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (hstickyAD : 3 * stickyDataLoss ≤ sourceADLoss)
    (hqueryPos : 0 < queryScale)
    (hquerySmall : queryScale ≤ 1 / 4)
    (hqueryGridFloor : 48 * delta ^ 2 ≤ queryScale)
    (hcriticalQuery : criticalLoss < queryLoss)
    (hqueryAbsorb : delta ≤ Real.rpow (40 : ℝ)
      (-1 / (queryLoss - criticalLoss))) :
    ∃ oneScale : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := queryLoss)
        (rho := queryScale) (Y := dyadic.shading)
        (fun point => dyadic.planeMap.planeMap point),
      leftFactor * dyadic.shading.mass ≤
        rightFactor * oneScale.shading.mass := by
  rcases phase1_sticky_to_Z_and_propertyP_certified sticky
      dyadic.reentry.normalization.final_extremal
      dyadic.reentry.normalization.cropped_top_level_cwa hphase1Loss
      hreentryPhase1 hrhoSmall hphase1Slack hsigma hsigmaOne hreentryLoss
      hreentrySticky hstickySmall hrhoPropertyP hhavg with
    ⟨_Z, _hZSub, _hZExtremal, _hZCWA, epsilon₁, epsilon₃, propP,
      hepsilon₁Def, hepsilon₁, hepsilon₁Small, hepsilon₃, hepsilon₃Def,
      hepsilonSum, htauPos, hrhoTau, htauSq, htauOne, hpropertyThreeEq,
      _hZCoarse, _⟩
  have hsourceSub : PaperIsSubshading
      dyadic.reentry.normalization.croppedRefined
      (restrictPaperShading dyadic.reentry.regularized.selected
        dyadic.shading) := by
    rw [dyadic.reentry.normalization_croppedRefined_current]
    exact dyadic.reentry.denseSubshading
  let target := ambientSubfamilyPropertyThreeCommonHull dyadic.shading
    dyadic.reentry.regularized.selected sticky propP.propertyThree
  let massLoss := (4 * regularity) *
    (wz2PaperPureRefinementFraction delta logExponent)⁻¹
  have hfraction := pure_refinement_fraction_pos_ne_top
    dyadic.extremal.delta_pos hdeltaOne logExponent
  have hmassLoss : 0 < massLoss ∧ massLoss ≠ ⊤ := by
    dsimp only [massLoss]
    exact ⟨ENNReal.mul_pos
        (ENNReal.mul_pos (by norm_num) hregularityPos.ne').ne'
        (ENNReal.inv_ne_zero.mpr hfraction.2),
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) hregularityTop)
        (ENNReal.inv_ne_top.mpr hfraction.1.ne')⟩
  have hmass : massLoss⁻¹ *
        dyadic.reentry.normalization.croppedRefined.mass ≤ target.mass := by
    change
      (((4 * regularity) *
          (wz2PaperPureRefinementFraction delta logExponent)⁻¹)⁻¹ *
        dyadic.reentry.normalization.croppedRefined.mass ≤ target.mass)
    exact ambientPropertyThreeCommonHull_source_mass_lower_of_two_bands
      dyadic.shading dyadic.reentry.regularized.selected hsourceSub sticky
      propP.propertyThree
      (fun index => (propP.propertyThree_sub index).trans
        (propP.propertyOne_sub index))
      propP.propertyThree_cubical propP.propertyThree_mass
      coarseMultiplicity regularity hcoarseMultiplicityPos
      hcoarseMultiplicityTop hregularityPos hregularityTop
      hcoarseLower hcoarseUpper
      (fineMultiplicity := 2 ^ dyadic.level)
      (fun point hpoint => by
        exact_mod_cast dyadic.multiplicity_lower point hpoint)
      (fun point hpoint => by
        exact_mod_cast dyadic.multiplicity_upper point hpoint)
  have hsqrtThree : Real.sqrt 3 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have htauTwenty : rho.1 * Real.sqrt 3 ≤ 20 * rho.1 := by
    have hscaled := mul_le_mul_of_nonneg_left hsqrtThree
      sticky.coarse_extremal.delta_pos.le
    nlinarith [hscaled]
  have hrhoThousand : rho.1 ≤ 1 / 1000 :=
    hrhoSmall.trans (by norm_num)
  have hrhoHalf : rho.1 ≤ 1 / 2 := hrhoSmall.trans (by norm_num)
  have hpropertyThree : ∀ parent : Fin sticky.coarse.card,
      ∀ point : Point3, point ∈ propP.propertyThree.carrier parent →
        Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
            ENNReal.ofReal (rho.1 * Real.sqrt 3) ≤
          volume (propP.propertyThree.carrier parent ∩
            Metric.closedBall point (rho.1 * Real.sqrt 3)) := by
    rw [hpropertyThreeEq]
    exact propP.propertyOne_full
  have hepsilon₃Large : 9 / 10 < epsilon₃ := by
    rw [hepsilon₃Def, hepsilon₁Def]
    linarith
  have hepsilon₃One : epsilon₃ < 1 := by
    rw [hepsilon₃Def]
    linarith
  have haxis := cordoba_ax_condition rho.1 epsilon₃
    sticky.coarse_extremal.delta_pos hrhoSmall hepsilon₃Large hepsilon₃One
  have hplaneUnit : ∀ point :
      {point : Point3 // point ∈ dyadic.shading.union},
      ‖dyadic.planeMap.planeMap point‖ = 1 :=
    fun point => dyadic.planeMap.unit point point.prop
  have htargetCubical : WZ1PaperIsCubicalShading target := by
    apply ambientSubfamilyPropertyThreeCommonHull_cubical
      dyadic.reentry.regularized.selected sticky propP.propertyThree
      dyadic.cubical
    exact ambientPropertyThreeCommonHull_cubical sticky propP.propertyThree
      dyadic.reentry.normalization.cropped_cubical
      (propertyThreeFinePullbackShading_cubical sticky.cover sticky.refined
        propP.propertyThree sticky.refined_cubical
        (alignedCoarseMultiplicity delta queryScale)
        (alignedCoarseMultiplicity_pos dyadic.extremal.delta_pos hqueryPos)
        (by simpa only [alignedCoarseScale] using hrhoAligned))
  have htargetSub : PaperIsSubshading target dyadic.shading :=
    ambientSubfamilyPropertyThreeCommonHull_subshading sticky
      propP.propertyThree
  have htargetExtremal : WZ2PaperCroppedIsExtremal sigma criticalLoss
      root.normalization.croppedFamily target := by
    have cardinality :
        dyadic.reentry.normalizationWeight *
            root.normalization.croppedFamily.enncard ≤
          (dyadic.reentry.regularized.regularizationLoss *
            dyadic.reentry.weightUpper) *
              dyadic.reentry.normalization.croppedFamily.enncard := by
      simpa only [dyadic.reentry.normalization_croppedFamily] using
        dyadic.reentry.regularized.cardinality_retention
    have ambientBodyUpper :
        (wz1PaperBodyFamily root.normalization.croppedFamily).mass ≤
          ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN delta 2 *
              root.normalization.croppedFamily.enncard := by
      let fullShading : WZ1PaperTubeShading
          root.normalization.croppedFamily :=
        { carrier := fun index => wz1PaperTubeCarrier
            (root.normalization.croppedFamily.tube index)
          measurable_carrier := fun index =>
            wz1PaperTubeCarrier_measurable
              (root.normalization.croppedFamily.tube index)
          subset_body := fun _ => Set.Subset.rfl }
      have upper := wz2_paper_shading_mass_upper dyadic.extremal.delta_pos
        ((rho.2.1.trans hrhoSmall).trans (by norm_num))
        root.normalization.line_class fullShading
      change (wz1PaperBodyFamily root.normalization.croppedFamily).mass ≤
        ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta 2 *
            root.normalization.croppedFamily.enncard at upper
      exact upper
    have selectedBodyLower :
        Kakeya.realRpowENN delta 2 *
            dyadic.reentry.normalization.croppedFamily.enncard ≤
          (wz1PaperBodyFamily
            dyadic.reentry.normalization.croppedFamily).mass :=
      paperBodyFamily_mass_lower_rpow_two dyadic.extremal.delta_pos
        ((rho.2.1.trans hrhoSmall).trans (by norm_num))
        dyadic.reentry.normalization.line_class
    have sourceToTarget :
        dyadic.reentry.normalization.croppedRefined.mass ≤
          massLoss * target.mass :=
      (ENNReal.inv_mul_le_iff hmassLoss.1.ne' hmassLoss.2).mp hmass
    let common := massLoss * dyadic.reentry.normalizationWeight
    have hcommonPos : 0 < common := ENNReal.mul_pos hmassLoss.1.ne'
      dyadic.reentry.normalization_weight_ne_zero
    have hcommonTop : common ≠ ⊤ := ENNReal.mul_ne_top hmassLoss.2
      dyadic.reentry.normalization_weight_ne_top
    have scaledDensity : common *
          (Kakeya.realRpowENN delta criticalLoss *
            (wz1PaperBodyFamily root.normalization.croppedFamily).mass) ≤
        common * target.mass := by
      calc
        common * (Kakeya.realRpowENN delta criticalLoss *
            (wz1PaperBodyFamily root.normalization.croppedFamily).mass) ≤
          common * (Kakeya.realRpowENN delta criticalLoss *
            (((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN delta 2 *
                root.normalization.croppedFamily.enncard)) := by gcongr
        _ ≤ (((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
              (dyadic.reentry.regularized.regularizationLoss *
                dyadic.reentry.weightUpper * massLoss) *
              Kakeya.realRpowENN delta criticalLoss) *
            (Kakeya.realRpowENN delta 2 *
              dyadic.reentry.normalization.croppedFamily.enncard) := by
          dsimp only [common]
          simpa only [mul_assoc, mul_comm, mul_left_comm] using
            (mul_le_mul_right cardinality
              (((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
                massLoss * Kakeya.realRpowENN delta criticalLoss *
                  Kakeya.realRpowENN delta 2))
        _ ≤ (dyadic.reentry.normalizationWeight *
              Kakeya.realRpowENN delta
                dyadic.reentry.reentryNormalizationLoss) *
            (Kakeya.realRpowENN delta 2 *
              dyadic.reentry.normalization.croppedFamily.enncard) := by
          exact mul_le_mul_left hcommonDensityLift _
        _ ≤ (dyadic.reentry.normalizationWeight *
              Kakeya.realRpowENN delta
                dyadic.reentry.reentryNormalizationLoss) *
            (wz1PaperBodyFamily
              dyadic.reentry.normalization.croppedFamily).mass := by
          exact mul_le_mul_right selectedBodyLower _
        _ ≤ dyadic.reentry.normalizationWeight *
            dyadic.reentry.normalization.croppedRefined.mass := by
          simpa only [mul_assoc] using
            (mul_le_mul_right
              dyadic.reentry.normalization.final_extremal.dense
              dyadic.reentry.normalizationWeight)
        _ ≤ dyadic.reentry.normalizationWeight *
            (massLoss * target.mass) := by
          exact mul_le_mul_right sourceToTarget _
        _ = common * target.mass := by
          dsimp only [common]
          ring
    have targetDense : target.IsLambdaDense
        (Kakeya.realRpowENN delta criticalLoss) := by
      rw [Kakeya.Streamlined.Shading.IsLambdaDense]
      exact (ENNReal.mul_le_mul_iff_left hcommonPos.ne' hcommonTop).mp <| by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using scaledDensity
    have weakened := dyadic.extremal.mono_loss hdyadicCritical
    exact
      { delta_pos := weakened.delta_pos
        delta_le_one := weakened.delta_le_one
        nonempty := weakened.nonempty
        cwa_nearby_scales := weakened.cwa_nearby_scales
        cubical := htargetCubical
        dense := targetDense
        volume_upper := (measure_mono <| paperSubshading_union htargetSub).trans
          weakened.volume_upper }
  have htargetCWA : WZ2PaperConvexWolffBound
      root.normalization.croppedFamily
      (Kakeya.realRpowENN delta (-criticalLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := root.normalization.croppedRefined)
      (_shading2 := target) root.normalization.cropped_top_level_cwa
      hnormalizationCritical dyadic.extremal.delta_pos
      dyadic.extremal.delta_le_one
  have htargetAD : ∀ point : Point3, ∀ hpoint : point ∈ target.union,
      PureWZ2PaperADSet1
        (scalarProjection
          (dyadic.planeMap.planeMap point)
          (target.union ∩ Metric.closedBall point
            (Real.sqrt (48 * rho.1 ^ 2))))
        (48 * rho.1 ^ 2) (1 - sigma)
        (Kakeya.realRpowENN delta (-sourceADLoss)) := by
    intro point hpoint
    have hpullback : point ∈
        (propertyThreeFinePullbackShading sticky.cover sticky.refined
          propP.propertyThree).union := by
      rw [← ambientSubfamilyPropertyThreeCommonHull_union
        dyadic.reentry.regularized.selected hsourceSub sticky
          propP.propertyThree]
      exact hpoint
    let sourcePoint : {point : Point3 // point ∈
        dyadic.reentry.normalization.croppedRefined.union} :=
      ⟨point, by
        rcases hpullback with ⟨index, hindex⟩
        exact ⟨sticky.selected.embedding index,
          sticky.subshading index hindex.1⟩⟩
    let S : Set Point3 := sticky.croppedCoarseShading.union ∩
      Metric.closedBall point (4 * (rho.1 * Real.sqrt 3))
    have hinvCube : Real.rpow rho.1 (-3 : ℝ) ≤
        Real.rpow delta (-sourceADLoss) :=
      aligned_scale_inv_cube_bound dyadic.extremal.delta_pos hdeltaOne
        hrhoLower hstickyAD
    have hcritical :=
      propertyThreeFinePullback_high_local_ad_at_critical_scale_of_inv_cube_bound
        sticky.balanced epsilon₁ epsilon₃ propP
        (dyadic.planeMap.planeMap sourcePoint)
        (by
          have pointDyadic : point ∈ dyadic.shading.union :=
            paperSubshading_union htargetSub hpoint
          exact dyadic.planeMap.unit point pointDyadic)
        point hpullback S rfl
        (sticky.croppedCoarseShading.union_measurable.inter
          Metric.isClosed_closedBall.measurableSet)
        (by intro other hother; exact hother.2) rfl htauPos htauTwenty
        hrhoTau htauSq htauOne hrhoThousand sticky.coarse_extremal.delta_pos
        hrhoHalf hsigma hsigmaOne hepsilon₁ hepsilon₁Small hepsilon₃
        hepsilon₃Def hepsilonSum logScale hrhoLog
        (hlog epsilon₁ hepsilon₁Def) hpropertyThree haxis
        dyadic.extremal.delta_pos hdeltaOne hsourceADLoss hrhoBound hinvCube
    have htargetUnion : target.union =
        (propertyThreeFinePullbackShading sticky.cover sticky.refined
          propP.propertyThree).union :=
      ambientSubfamilyPropertyThreeCommonHull_union
        dyadic.reentry.regularized.selected hsourceSub sticky
          propP.propertyThree
    exact ambientSubfamilyPropertyThreeCommonHull_ad
      dyadic.reentry.regularized.selected hsourceSub sticky
      propP.propertyThree (dyadic.planeMap.planeMap point) point
      (Kakeya.realRpowENN delta (-sourceADLoss)) hcritical
  have hconstant : 10 * Kakeya.realRpowENN delta (-sourceADLoss) ≤
      Kakeya.realRpowENN delta (-criticalLoss) := by
    simpa using realRpowENN_neg_loss_gap_absorb (factor := (10 : ℝ))
      (delta := delta) (sourceLoss := sourceADLoss)
      (targetLoss := criticalLoss) (by norm_num) hADGap
      dyadic.extremal.delta_pos hADSmall
  have htargetLocal : ∀ point ∈ target.union,
      IsADSet1
        (scalarProjection (dyadic.planeMap.planeMap point)
          (target.union ∩ Metric.closedBall point
            (Real.sqrt (48 * rho.1 ^ 2))))
        (48 * rho.1 ^ 2) (1 - sigma)
        (Kakeya.realRpowENN delta (-criticalLoss)) := by
    intro point hpoint
    have hbounded :
        scalarProjection (dyadic.planeMap.planeMap point)
            (target.union ∩ Metric.closedBall point
              (Real.sqrt (48 * rho.1 ^ 2))) ⊆ Set.Icc (-4 : ℝ) 4 := by
      apply scalarProjection_bounded
        (dyadic.planeMap.unit point (paperSubshading_union htargetSub hpoint))
        (scalarProjection (dyadic.planeMap.planeMap point)
          (target.union ∩ Metric.closedBall point
            (Real.sqrt (48 * rho.1 ^ 2))))
      rintro value ⟨other, hother, rfl⟩
      exact ⟨other, paperSubshading_union htargetSub hother.1, rfl⟩
    exact (pure_wz2_paper_ad_bridge.1 _ _ _ _ hbounded
      (htargetAD point hpoint)).mono_constant hconstant
  let critical : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := criticalLoss)
      (rho := 48 * rho.1 ^ 2) (Y := dyadic.shading)
      (fun point => dyadic.planeMap.planeMap point) :=
    { shading := target
      subshading := htargetSub
      extremal := htargetExtremal
      cwa := htargetCWA
      local_ad := htargetLocal }
  have queryCritical : queryScale ≤ 48 * rho.1 ^ 2 := by
    rw [hrhoAligned]
    exact query_le_fortyEight_mul_alignedCoarseScale_sq
      dyadic.extremal.delta_pos hqueryPos
  have criticalRatio : 48 * rho.1 ^ 2 < 4 * queryScale := by
    rw [hrhoAligned]
    exact fortyEight_mul_alignedCoarseScale_sq_lt_four_mul_query
      dyadic.extremal.delta_pos hqueryPos hqueryGridFloor
  have criticalOne : 48 * rho.1 ^ 2 ≤ 1 :=
    criticalRatio.le.trans (by linarith)
  let query := PureWZ2OneScaleLocalGrainData.refineAlignedQueryScale critical
    hqueryPos queryCritical criticalRatio criticalOne hcriticalQuery
    hqueryAbsorb
  have hsourceMass :
      ((73 / 100 : ENNReal) * dyadic.reentry.normalizationWeight) *
          dyadic.shading.mass ≤
        dyadic.reentry.regularized.regularizationLoss *
          dyadic.reentry.normalization.croppedRefined.mass :=
    dyadic.reentry.reentryMassRetention
  have htargetMassFromDyadic :
      dyadic.reentry.normalization.croppedRefined.mass ≤ massLoss * target.mass := by
    apply (ENNReal.inv_mul_le_iff hmassLoss.1.ne' hmassLoss.2).mp
    simpa only [massLoss] using hmass
  refine ⟨query, ?_⟩
  calc
    leftFactor * dyadic.shading.mass ≤
        ((73 / 100 : ENNReal) *
          dyadic.reentry.normalizationWeight) * dyadic.shading.mass :=
      mul_le_mul_left hleft _
    _ ≤ dyadic.reentry.regularized.regularizationLoss *
          dyadic.reentry.normalization.croppedRefined.mass := hsourceMass
    _ ≤ dyadic.reentry.regularized.regularizationLoss *
          (massLoss * target.mass) := by gcongr
    _ = (dyadic.reentry.regularized.regularizationLoss * massLoss) *
          query.shading.mass := by
      simp only [query,
        PureWZ2OneScaleLocalGrainData.refineAlignedQueryScale,
        PureWZ2OneScaleLocalGrainData.refineQueryScale, critical]
      ring
    _ ≤ rightFactor * query.shading.mass :=
      mul_le_mul_left (by simpa only [massLoss] using hright) _

/-- When the ordinary re-entry's fresh cropped source itself retains the
dyadic band, the production wrapper needs no free multiplicity hypotheses.
This equality is the exact bridge still required from the re-entry geometry:
it states that the same point multiplicity survives the ordinary-trace and
dense-cubical normalization, not merely that the new source is a subshading. -/
theorem Proposition63DyadicCurrentReentryData.phase1AlignedCandidate
    {delta sigma initialInputLoss normalizationLoss densityLoss incidence
      currentLoss dyadicLoss weightLoss reentryLoss reentryNormalizationLoss
      stickyDataLoss phase1Loss sourceADLoss criticalLoss queryLoss queryScale :
      ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent logExponent : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent
        densityLoss}
    {current : WZ1PaperTubeShading root.normalization.croppedFamily}
    {currentMap : PaperWZ1WeakPlaneMapData current incidence}
    (dyadic : Proposition63DyadicCurrentReentryData
      (currentLoss := currentLoss) (dyadicLoss := dyadicLoss)
      (weightLoss := weightLoss) (reentryLoss := reentryLoss)
      (reentryNormalizationLoss := reentryNormalizationLoss)
      root current currentMap)
    {rho : WZ2PaperRequestedScale delta}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyDataLoss)
      dyadic.reentry.normalization.croppedRefined rho logExponent)
    (hsourceMultiplicity : ∀ point ∈
      dyadic.reentry.normalization.croppedRefined.union,
      dyadic.reentry.normalization.croppedRefined.pointMultiplicity point =
        dyadic.shading.pointMultiplicity point)
    (leftFactor rightFactor : ENNReal)
    (hleft : leftFactor ≤
      (73 / 100 : ENNReal) * dyadic.reentry.normalizationWeight)
    (hright : dyadic.reentry.regularized.regularizationLoss *
        propertyThreeDyadicCommonHullMassLoss sticky ≤ rightFactor)
    (hrhoAligned : rho.1 = alignedCoarseScale delta queryScale)
    (hphase1Loss : 0 < phase1Loss)
    (hreentryPhase1 : dyadic.reentry.reentryNormalizationLoss ≤ phase1Loss)
    (hphase1Slack :
      (wz2PaperPureRefinementFraction delta logExponent)⁻¹ *
          Kakeya.realRpowENN delta phase1Loss ≤
        Kakeya.realRpowENN delta
          dyadic.reentry.reentryNormalizationLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hreentryLoss : 0 < dyadic.reentry.reentryNormalizationLoss)
    (hreentrySticky :
      dyadic.reentry.reentryNormalizationLoss ≤ stickyDataLoss)
    (hstickySmall : 6 * stickyDataLoss <
      sigma + 2 * dyadic.reentry.reentryNormalizationLoss)
    (hrhoSmall : rho.1 ≤ 1 / 10000)
    (hrhoPropertyP : rho.1 ≤ (3 : ℝ) ^ (-(20 / sigma)))
    (hhavg :
      (PureWZ2.h_avg_m_val sigma
          dyadic.reentry.reentryNormalizationLoss rho.1 : ℝ) *
          rho.1 ^ (sigma - 3 * stickyDataLoss) < 1 / 8)
    (hreentryCritical :
      dyadic.reentry.reentryNormalizationLoss ≤ criticalLoss)
    (hcommonSlack : propertyThreeDyadicCommonHullMassLoss sticky *
        Kakeya.realRpowENN delta criticalLoss ≤
      Kakeya.realRpowENN delta dyadic.reentry.reentryNormalizationLoss)
    (hdeltaOne : delta < 1)
    (hcriticalLoss : 0 < criticalLoss)
    (hsourceADLoss : 0 < sourceADLoss)
    (hADGap : sourceADLoss < criticalLoss)
    (hADSmall : delta ≤ Real.rpow (10 : ℝ)
      (-1 / (criticalLoss - sourceADLoss)))
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : ∀ epsilon₁ : ℝ, epsilon₁ =
        (sigma - 2 * dyadic.reentry.reentryNormalizationLoss) / 20 →
      0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hrhoLower : Real.rpow delta stickyDataLoss ≤ rho.1)
    (hrhoBound : rho.1 ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (hstickyAD : 3 * stickyDataLoss ≤ sourceADLoss)
    (hqueryPos : 0 < queryScale)
    (hquerySmall : queryScale ≤ 1 / 4)
    (hqueryGridFloor : 48 * delta ^ 2 ≤ queryScale)
    (hcriticalQuery : criticalLoss < queryLoss)
    (hqueryAbsorb : delta ≤ Real.rpow (40 : ℝ)
      (-1 / (queryLoss - criticalLoss))) :
    ∃ oneScale : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := queryLoss)
        (rho := queryScale)
        (Y := dyadic.reentry.normalization.croppedRefined)
        (fun point => dyadic.planeMap.planeMap point),
      leftFactor * dyadic.shading.mass ≤
        rightFactor * oneScale.shading.mass := by
  apply dyadic.phase1AlignedCandidate_of_bounds sticky leftFactor rightFactor
    hleft hright
  · intro point hpoint
    rw [hsourceMultiplicity point hpoint]
    exact_mod_cast dyadic.multiplicity_lower point
      (dyadic.reentry.normalization_croppedRefined_union_subset_current hpoint)
  · intro point hpoint
    rw [hsourceMultiplicity point hpoint]
    exact_mod_cast dyadic.multiplicity_upper point
      (dyadic.reentry.normalization_croppedRefined_union_subset_current hpoint)
  · exact hrhoAligned
  · exact hphase1Loss
  · exact hreentryPhase1
  · exact hphase1Slack
  · exact hsigma
  · exact hsigmaOne
  · exact hreentryLoss
  · exact hreentrySticky
  · exact hstickySmall
  · exact hrhoSmall
  · exact hrhoPropertyP
  · exact hhavg
  · exact hreentryCritical
  · exact hcommonSlack
  · exact hdeltaOne
  · exact hcriticalLoss
  · exact hsourceADLoss
  · exact hADGap
  · exact hADSmall
  · exact hrhoLog
  · exact hlog
  · exact hrhoLower
  · exact hrhoBound
  · exact hstickyAD
  · exact hqueryPos
  · exact hquerySmall
  · exact hqueryGridFloor
  · exact hcriticalQuery
  · exact hqueryAbsorb

end Kakeya.Assouad.PureWZ2

end
