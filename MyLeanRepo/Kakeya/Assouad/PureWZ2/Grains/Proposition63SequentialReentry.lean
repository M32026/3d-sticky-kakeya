import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentCoarseReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSpatialInvariant
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SubfamilyGrainConfigurationExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeCriticalOneScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinitePlaninessInitial
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Phase1StickyToPropertyP
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63OneScaleFullGrainCandidate

/-!
# Current-relative Proposition 6.2 re-entry for finite Lemma 4.12 iteration

At a finite-grid step the current shading is first returned to the ordinary
model and normalized by `Proposition63CurrentShadingReentryData`.  Proposition
6.2 may then select a genuine tube subfamily.  This file zero-extends a
candidate on that selected family back to the fixed ambient family and takes
its common-spatial hull relative to the current shading.

The resulting output is a genuine nested step: it is contained in the current
shading, is cubical, preserves every current tube membership at retained
points, and carries variation and local AD for the same ambient plane map.
No sticky witness sampled from the original source is reused at a later step.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Zero-extend a shading produced on the current re-entry family back to the
fixed family of the initial normalization. -/
noncomputable def Proposition63CurrentShadingReentryData.extendCandidate
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (candidate : WZ1PaperTubeShading data.normalization.croppedFamily) :
    WZ1PaperTubeShading initialNormalized.croppedFamily :=
  extendShading data.regularized.selected candidate

/-- A candidate below the exact normalized re-entry shading extends to a
subshading of the current ambient shading. -/
lemma Proposition63CurrentShadingReentryData.extendCandidate_subshading
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    {candidate : WZ1PaperTubeShading data.normalization.croppedFamily}
    (hsub : PaperIsSubshading candidate data.normalization.croppedRefined) :
    PaperIsSubshading (data.extendCandidate candidate) current := by
  intro ambientIndex point hpoint
  by_cases himage : ∃ selectedIndex,
      data.regularized.selected.embedding selectedIndex = ambientIndex
  · rcases himage with ⟨selectedIndex, rfl⟩
    rw [extendCandidate, extendShading_carrier_mem] at hpoint
    have hdense : point ∈ data.denseShading.carrier selectedIndex := by
      have hdense' := hsub selectedIndex hpoint
      change point ∈ data.denseShading.carrier selectedIndex at hdense'
      exact hdense'
    exact data.denseSubshading selectedIndex hdense
  · rw [extendCandidate, extendShading_carrier_empty himage] at hpoint
    exact False.elim hpoint

/-- Zero-extension changes neither the geometric union nor the shaded mass. -/
lemma Proposition63CurrentShadingReentryData.extendCandidate_union
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (candidate : WZ1PaperTubeShading data.normalization.croppedFamily) :
    (data.extendCandidate candidate).union = candidate.union :=
  extendShading_union data.regularized.selected candidate

lemma Proposition63CurrentShadingReentryData.extendCandidate_mass
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (candidate : WZ1PaperTubeShading data.normalization.croppedFamily) :
    (data.extendCandidate candidate).mass = candidate.mass :=
  extendShading_mass data.regularized.selected candidate

/-- A one-scale local-grain output constructed on the freshly normalized
selected family supplies the geometric candidate required by the ambient
iteration.  Variation is read from the same fixed ambient plane map, while
the local AD field is definitionally the one carried by `oneScale`. -/
theorem Proposition63CurrentShadingReentryData.oneScaleCandidate
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      oneScaleLoss localScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (planeMap : Point3 → Point3)
    (constant leftFactor rightFactor : ENNReal)
    (spatialScale variationScale : ℝ)
    (coefficient : NNReal)
    (hlipschitz : LipschitzWith coefficient planeMap)
    (hvariationBudget : (coefficient : ℝ) * spatialScale ≤ variationScale)
    (oneScale : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := oneScaleLoss)
      (rho := localScale) (Y := data.normalization.croppedRefined)
      (fun point => planeMap point))
    (hconstant : Kakeya.realRpowENN delta (-oneScaleLoss) ≤ constant)
    (hmass : leftFactor * current.mass ≤
      rightFactor * oneScale.shading.mass) :
    ∃ candidate : WZ1PaperTubeShading data.normalization.croppedFamily,
      PaperIsSubshading candidate data.normalization.croppedRefined ∧
      WZ1PaperIsCubicalShading candidate ∧
      (∀ first ∈ candidate.union, ∀ second ∈ candidate.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) ∧
      (∀ point ∈ candidate.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (candidate.union ∩ Metric.closedBall point
              (Real.sqrt localScale)))
          localScale (1 - sigma) constant) ∧
      leftFactor * current.mass ≤ rightFactor * candidate.mass := by
  refine ⟨oneScale.shading, oneScale.subshading,
    oneScale.extremal.cubical, ?_, ?_, hmass⟩
  · intro first _ second _ hdistance
    calc
      dist (planeMap first) (planeMap second) ≤
          (coefficient : ℝ) * dist first second :=
        hlipschitz.dist_le_mul first second
      _ ≤ (coefficient : ℝ) * spatialScale := by gcongr
      _ ≤ variationScale := hvariationBudget
  · intro point hpoint
    exact (oneScale.local_ad point hpoint).mono_constant hconstant

/-- The closed critical-scale Property-(P) theorem is a concrete candidate
producer for one sequential re-entry step.  All scalar hypotheses remain
visible; the wrapper contributes only the exact mass-factor orientation used
by the finite iterator. -/
theorem Proposition63CurrentShadingReentryData.criticalPropertyThreeCandidate
    {delta sigma initialInputLoss normalizationLoss reentryLoss stickyDataLoss
      sourceADLoss targetLoss tau epsilon₁ epsilon₃ : ℝ}
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
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (planeMap : Point3 → Point3)
    (hplaneUnit : ∀ point ∈ data.normalization.croppedRefined.union,
      ‖planeMap point‖ = 1)
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * delta)
    (massLoss : ENNReal)
    (hmassLossPos : 0 < massLoss)
    (hmassLossFinite : massLoss ≠ ⊤)
    (hmass : massLoss⁻¹ * data.normalization.croppedRefined.mass ≤
      (ambientPropertyThreeCommonHull sticky propP.propertyThree).mass)
    (hloss : data.reentryNormalizationLoss ≤ targetLoss)
    (hslack : massLoss * Kakeya.realRpowENN delta targetLoss ≤
      Kakeya.realRpowENN delta data.reentryNormalizationLoss)
    (hdeltaOne : delta < 1)
    (htargetLoss : 0 < targetLoss)
    (hsourceADLoss : 0 < sourceADLoss)
    (hADGap : sourceADLoss < targetLoss)
    (hADSmall : delta ≤ Real.rpow (10 : ℝ)
      (-1 / (targetLoss - sourceADLoss)))
    (htauDef : tau = rho.1 * Real.sqrt 3)
    (htauPos : 0 < tau)
    (htauLeTwenty : tau ≤ 20 * rho.1)
    (hrhoTau : rho.1 ≤ tau)
    (htauSq : tau ^ 2 ≤ 4 * rho.1)
    (htauOne : tau ≤ 1)
    (hrhoSmall : rho.1 ≤ 1 / 1000)
    (hrhoHalf : rho.1 ≤ 1 / 2)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₁Small : epsilon₁ < 1 / 20)
    (hepsilon₃ : 0 < epsilon₃)
    (hepsilon₃Def : epsilon₃ = 1 - 2 * epsilon₁)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hpropertyThree : ∀ parent : Fin sticky.coarse.card,
      ∀ point : Point3, point ∈ propP.propertyThree.carrier parent →
        Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
            ENNReal.ofReal tau ≤
          volume (propP.propertyThree.carrier parent ∩
            Metric.closedBall point tau))
    (haxis : 4 * (6 * rho.1) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (hrhoLower : Real.rpow delta stickyDataLoss ≤ rho.1)
    (hrhoBound : rho.1 ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (hstickyAD : 3 * stickyDataLoss ≤ sourceADLoss) :
    ∃ oneScale : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := targetLoss)
        (rho := 48 * rho.1 ^ 2)
        (Y := data.normalization.croppedRefined)
        (fun point => planeMap point),
      data.normalization.croppedRefined.mass ≤
        massLoss * oneScale.shading.mass := by
  have hunit : ∀ point :
      {point : Point3 // point ∈ data.normalization.croppedRefined.union},
      ‖(fun point : Point3 => planeMap point) point‖ = 1 :=
    fun point => hplaneUnit point point.prop
  rcases propertyThreeCommonHull_critical_one_scale_output
      (sourceLoss := data.reentryNormalizationLoss)
      (planeMap := fun point => planeMap point) hunit sticky propP
      data.normalization.cropped_cubical scaleFactor hscaleFactor
      hrhoAligned data.normalization.final_extremal
      data.normalization.cropped_top_level_cwa massLoss hmassLossPos
      hmassLossFinite hmass hloss hslack
      data.reentry_extremal.delta_pos hdeltaOne htargetLoss
      hsourceADLoss hADGap hADSmall htauDef htauPos htauLeTwenty
      hrhoTau htauSq htauOne hrhoSmall sticky.coarse_extremal.delta_pos
      hrhoHalf hsigma hsigmaOne hepsilon₁ hepsilon₁Small hepsilon₃
      hepsilon₃Def hepsilonSum logScale hrhoLog hlog hpropertyThree haxis
      hrhoLower hrhoBound hstickyAD with ⟨oneScale, honeScale⟩
  refine ⟨oneScale, ?_⟩
  apply (ENNReal.inv_mul_le_iff hmassLossPos.ne' hmassLossFinite).mp
  rw [honeScale]
  exact hmass

/-- The actual paper Phase-1 construction supplies the Property-(P) input for
one critical-scale sequential step.  The conclusion exposes the two distinct
mass losses: ordinary-trace re-entry and the Property-Three common hull. -/
theorem Proposition63CurrentShadingReentryData.phase1CriticalCandidate
    {delta sigma initialInputLoss normalizationLoss reentryLoss stickyDataLoss
      phase1Loss sourceADLoss targetLoss : ℝ}
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
    (hplaneUnit : ∀ point ∈ data.normalization.croppedRefined.union,
      ‖planeMap point‖ = 1)
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * delta)
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
    (hloss : data.reentryNormalizationLoss ≤ targetLoss)
    (hcommonSlack : propertyThreeCommonHullMassLoss sticky *
        Kakeya.realRpowENN delta targetLoss ≤
      Kakeya.realRpowENN delta data.reentryNormalizationLoss)
    (hdeltaOne : delta < 1)
    (htargetLoss : 0 < targetLoss)
    (hsourceADLoss : 0 < sourceADLoss)
    (hADGap : sourceADLoss < targetLoss)
    (hADSmall : delta ≤ Real.rpow (10 : ℝ)
      (-1 / (targetLoss - sourceADLoss)))
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
    (hstickyAD : 3 * stickyDataLoss ≤ sourceADLoss) :
    ∃ oneScale : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := targetLoss)
        (rho := 48 * rho.1 ^ 2)
        (Y := data.normalization.croppedRefined)
        (fun point => planeMap point),
      ((73 / 100 : ENNReal) * data.normalizationWeight) * current.mass ≤
        (data.regularized.regularizationLoss *
          propertyThreeCommonHullMassLoss sticky) *
            oneScale.shading.mass := by
  rcases phase1_sticky_to_Z_and_propertyP_certified sticky
      data.normalization.final_extremal
      data.normalization.cropped_top_level_cwa hphase1Loss hreentryPhase1
      hrhoSmall hphase1Slack hsigma hsigmaOne hreentryLoss hreentrySticky
      hstickySmall hrhoPropertyP hhavg with
    ⟨_Z, _hZSub, _hZExtremal, _hZCWA, epsilon₁, epsilon₃, propP,
      hepsilon₁Def, hepsilon₁, hepsilon₁Small, hepsilon₃,
      hepsilon₃Def, hepsilonSum, htauPos, hrhoTau, htauSq, htauOne,
      hpropertyThreeEq, _hZCoarse, _⟩
  have htauTwenty : rho.1 * Real.sqrt 3 ≤ 20 * rho.1 := by
    have hsqrt : Real.sqrt 3 ≤ 20 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left hsqrt sticky.coarse_extremal.delta_pos.le
  have hrhoThousand : rho.1 ≤ 1 / 1000 := hrhoSmall.trans (by norm_num)
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
  have hmassPos : 0 < propertyThreeCommonHullMassLoss sticky :=
    propertyThreeCommonHullMassLoss_pos sticky
  have hmassFinite : propertyThreeCommonHullMassLoss sticky ≠ ⊤ :=
    propertyThreeCommonHullMassLoss_ne_top sticky
      data.reentry_extremal.delta_pos hdeltaOne
  have hmass : (propertyThreeCommonHullMassLoss sticky)⁻¹ *
        data.normalization.croppedRefined.mass ≤
      (ambientPropertyThreeCommonHull sticky propP.propertyThree).mass :=
    propertyThreeCommonHullMassLoss_inv_mul_source_mass_le sticky propP
      data.reentry_extremal.delta_pos
  rcases data.criticalPropertyThreeCandidate sticky propP planeMap hplaneUnit
      scaleFactor hscaleFactor hrhoAligned
      (propertyThreeCommonHullMassLoss sticky) hmassPos hmassFinite hmass
      hloss hcommonSlack hdeltaOne htargetLoss hsourceADLoss hADGap
      hADSmall rfl htauPos htauTwenty hrhoTau htauSq htauOne
      hrhoThousand hrhoHalf hsigma hsigmaOne hepsilon₁ hepsilon₁Small
      hepsilon₃ hepsilon₃Def hepsilonSum logScale hrhoLog
      (hlog epsilon₁ hepsilon₁Def) hpropertyThree haxis hrhoLower
      hrhoBound hstickyAD with ⟨oneScale, honeScaleMass⟩
  refine ⟨oneScale, ?_⟩
  calc
    ((73 / 100 : ENNReal) * data.normalizationWeight) * current.mass ≤
        data.regularized.regularizationLoss *
          data.normalization.croppedRefined.mass := data.reentryMassRetention
    _ ≤ data.regularized.regularizationLoss *
        (propertyThreeCommonHullMassLoss sticky * oneScale.shading.mass) :=
      mul_le_mul_left' honeScaleMass _
    _ = (data.regularized.regularizationLoss *
          propertyThreeCommonHullMassLoss sticky) *
        oneScale.shading.mass := by ring

/-- Uniformize the data-dependent re-entry and common-hull factors so that a
finite schedule may choose its product ledger before the successive sticky
witnesses are constructed. -/
theorem Proposition63CurrentShadingReentryData.phase1CriticalCandidate_of_bounds
    {delta sigma initialInputLoss normalizationLoss reentryLoss stickyDataLoss
      phase1Loss sourceADLoss targetLoss : ℝ}
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
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * delta)
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
    (hloss : data.reentryNormalizationLoss ≤ targetLoss)
    (hcommonSlack : propertyThreeCommonHullMassLoss sticky *
        Kakeya.realRpowENN delta targetLoss ≤
      Kakeya.realRpowENN delta data.reentryNormalizationLoss)
    (hdeltaOne : delta < 1)
    (htargetLoss : 0 < targetLoss)
    (hsourceADLoss : 0 < sourceADLoss)
    (hADGap : sourceADLoss < targetLoss)
    (hADSmall : delta ≤ Real.rpow (10 : ℝ)
      (-1 / (targetLoss - sourceADLoss)))
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
    (hstickyAD : 3 * stickyDataLoss ≤ sourceADLoss) :
    ∃ oneScale : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := targetLoss)
        (rho := 48 * rho.1 ^ 2)
        (Y := data.normalization.croppedRefined)
        (fun point => planeMap point),
      leftFactor * current.mass ≤ rightFactor * oneScale.shading.mass := by
  rcases data.phase1CriticalCandidate sticky planeMap hplaneUnit scaleFactor
      hscaleFactor hrhoAligned hphase1Loss hreentryPhase1 hphase1Slack
      hsigma hsigmaOne hreentryLoss hreentrySticky hstickySmall hrhoSmall
      hrhoPropertyP hhavg hloss hcommonSlack hdeltaOne htargetLoss
      hsourceADLoss hADGap hADSmall logScale hrhoLog hlog hrhoLower
      hrhoBound hstickyAD with ⟨oneScale, hmass⟩
  refine ⟨oneScale, ?_⟩
  calc
    leftFactor * current.mass ≤
        ((73 / 100 : ENNReal) * data.normalizationWeight) *
          current.mass := mul_le_mul_right' hleft _
    _ ≤ (data.regularized.regularizationLoss *
          propertyThreeCommonHullMassLoss sticky) *
        oneScale.shading.mass := hmass
    _ ≤ rightFactor * oneScale.shading.mass :=
      mul_le_mul_right' hright _

/-- Convert one candidate built after a fresh current-relative Proposition
6.2 call into the exact nested step consumed by the finite iteration. -/
theorem Proposition63CurrentShadingReentryData.candidate_joint_one_scale
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {spatialScale localScale variationScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (candidate : WZ1PaperTubeShading data.normalization.croppedFamily)
    (planeMap : Point3 → Point3)
    (constant leftFactor rightFactor : ENNReal)
    (hsub : PaperIsSubshading candidate data.normalization.croppedRefined)
    (hcubical : WZ1PaperIsCubicalShading candidate)
    (hvariation : ∀ first ∈ candidate.union, ∀ second ∈ candidate.union,
      dist first second ≤ spatialScale →
        dist (planeMap first) (planeMap second) ≤ variationScale)
    (hlocalAD : ∀ point ∈ candidate.union,
      IsADSet1
        (scalarProjection (planeMap point)
          (candidate.union ∩ Metric.closedBall point
            (Real.sqrt localScale)))
        localScale (1 - sigma) constant)
    (hmass : leftFactor * current.mass ≤
      rightFactor * candidate.mass) :
    ∃ next : WZ1PaperTubeShading initialNormalized.croppedFamily,
      PaperIsSubshading next current ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union,
        next.pointMultiplicity point = current.pointMultiplicity point) ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) ∧
      (∀ point ∈ next.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (next.union ∩ Metric.closedBall point
              (Real.sqrt localScale)))
          localScale (1 - sigma) constant) ∧
      leftFactor * current.mass ≤ rightFactor * next.mass := by
  let ambientCandidate := data.extendCandidate candidate
  have hambientSub : PaperIsSubshading ambientCandidate current :=
    data.extendCandidate_subshading hsub
  have hambientCubical : WZ1PaperIsCubicalShading ambientCandidate :=
    extendShading_cubical data.regularized.selected hcubical
  have hambientVariation : ∀ first ∈ ambientCandidate.union,
      ∀ second ∈ ambientCandidate.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale := by
    simpa only [ambientCandidate, data.extendCandidate_union candidate] using
      hvariation
  have hambientAD : ∀ point ∈ ambientCandidate.union,
      IsADSet1
        (scalarProjection (planeMap point)
          (ambientCandidate.union ∩ Metric.closedBall point
            (Real.sqrt localScale)))
        localScale (1 - sigma) constant := by
    simpa only [ambientCandidate, data.extendCandidate_union candidate] using
      hlocalAD
  have hambientMass : leftFactor * current.mass ≤
      rightFactor * ambientCandidate.mass := by
    simpa only [ambientCandidate, data.extendCandidate_mass candidate] using
      hmass
  exact commonSpatialHull_joint_one_scale current ambientCandidate planeMap
    constant leftFactor rightFactor hambientSub data.current_cubical
    hambientCubical hambientVariation hambientAD hambientMass

/-- Enlarge the right loss factor and/or decrease the left retained factor of
an already constructed current-relative candidate. -/
theorem Proposition63CurrentShadingReentryData.candidate_joint_one_scale_of_factors
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {spatialScale localScale variationScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (candidate : WZ1PaperTubeShading data.normalization.croppedFamily)
    (planeMap : Point3 → Point3)
    (constant exactLeft exactRight targetLeft targetRight : ENNReal)
    (hsub : PaperIsSubshading candidate data.normalization.croppedRefined)
    (hcubical : WZ1PaperIsCubicalShading candidate)
    (hvariation : ∀ first ∈ candidate.union, ∀ second ∈ candidate.union,
      dist first second ≤ spatialScale →
        dist (planeMap first) (planeMap second) ≤ variationScale)
    (hlocalAD : ∀ point ∈ candidate.union,
      IsADSet1
        (scalarProjection (planeMap point)
          (candidate.union ∩ Metric.closedBall point
            (Real.sqrt localScale)))
        localScale (1 - sigma) constant)
    (hmass : exactLeft * current.mass ≤ exactRight * candidate.mass)
    (hleft : targetLeft ≤ exactLeft)
    (hright : exactRight ≤ targetRight) :
    ∃ next : WZ1PaperTubeShading initialNormalized.croppedFamily,
      PaperIsSubshading next current ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union,
        next.pointMultiplicity point = current.pointMultiplicity point) ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) ∧
      (∀ point ∈ next.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (next.union ∩ Metric.closedBall point
              (Real.sqrt localScale)))
          localScale (1 - sigma) constant) ∧
      targetLeft * current.mass ≤ targetRight * next.mass := by
  have hmass' : targetLeft * current.mass ≤
      targetRight * candidate.mass := by
    calc
      targetLeft * current.mass ≤ exactLeft * current.mass :=
        mul_le_mul_right' hleft _
      _ ≤ exactRight * candidate.mass := hmass
      _ ≤ targetRight * candidate.mass := mul_le_mul_right' hright _
  exact data.candidate_joint_one_scale candidate planeMap constant
    targetLeft targetRight hsub hcubical hvariation hlocalAD hmass'

/-- Feed a genuine line-hit full-grain candidate into the current-relative
finite-iteration interface.  The displayed factors are exactly the incoming
one-scale mass factors multiplied by the line-hit geometry ledger. -/
theorem Proposition63CurrentShadingReentryData.lineHitCandidate_joint_one_scale
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      firstLoss secondLoss queryScale sqrtScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (planeMap : Point3 → Point3)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := reentry.normalization.croppedRefined)
      (fun point => planeMap point))
    (prepared : Proposition63OneScaleConstantMultiplicityData
      (secondLoss := secondLoss) planeMap original)
    (cells : Proposition63BalancedCellData (scale := sqrtScale)
      prepared.refined.shading)
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) (hqueryScale : 0 < queryScale)
    (hsqrtScale : 0 < sqrtScale)
    (coefficient : NNReal) (hlipschitz : LipschitzWith coefficient planeMap)
    (spatialScale variationScale : ℝ)
    (hvariationBudget :
      (coefficient : ℝ) * spatialScale ≤ variationScale)
    (constant : ENNReal)
    (hconstant : Kakeya.realRpowENN delta (-secondLoss) ≤ constant)
    (leftFactor rightFactor : ENNReal)
    (hincoming : leftFactor * current.mass ≤
      rightFactor * original.shading.mass) :
    let lineFactor :=
      ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2))
    let threshold :=
      (cells.cellMass / 2) / (2 * (coverBudget : ENNReal))
    let preparationLoss := prepared.preparationLoss
    let geometryFactor :=
      2 * cells.cellMass * ENNReal.ofReal (4 * queryScale)
    ∃ next : WZ1PaperTubeShading initialNormalized.croppedFamily,
      PaperIsSubshading next current ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union,
        next.pointMultiplicity point = current.pointMultiplicity point) ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) ∧
      (∀ point ∈ next.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (next.union ∩ Metric.closedBall point
              (Real.sqrt queryScale)))
          queryScale (1 - sigma) constant) ∧
      (lineFactor * threshold * leftFactor) * current.mass ≤
        (rightFactor * (preparationLoss * geometryFactor)) * next.mass := by
  dsimp only
  have hcandidateAD : ∀ point ∈ (full.lineHitCandidate hdelta).union,
      IsADSet1
        (scalarProjection (planeMap point)
          ((full.lineHitCandidate hdelta).union ∩
            Metric.closedBall point (Real.sqrt queryScale)))
        queryScale (1 - sigma) constant := by
    intro point hpoint
    exact (full.lineHitCandidate_local_ad hdelta point hpoint).mono_constant
      hconstant
  exact reentry.candidate_joint_one_scale
    (full.lineHitCandidate hdelta) planeMap constant
    (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
      ((cells.cellMass / 2) / (2 * (coverBudget : ENNReal))) *
      leftFactor)
    (rightFactor *
      (prepared.preparationLoss *
        (2 * cells.cellMass * ENNReal.ofReal (4 * queryScale))))
    (full.lineHitCandidate_subshading_source hdelta)
    (full.lineHitCandidate_cubical hdelta)
    (full.lineHitCandidate_variation hdelta coefficient hlipschitz
      spatialScale variationScale hvariationBudget)
    hcandidateAD
    (full.lineHitCandidate_mass_from_current (current := current)
      leftFactor rightFactor hincoming hdelta hqueryScale hsqrtScale)

/-- The current-relative line-hit step after cancelling the positive finite
balanced-cell mass.  This is the stable interface for uniform finite-schedule
loss accounting: no quantity chosen by the fresh cell decomposition remains,
apart from its explicit natural-number covering budget. -/
theorem Proposition63CurrentShadingReentryData.lineHitCandidate_joint_one_scale_cancel_cellMass
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      firstLoss secondLoss queryScale sqrtScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (planeMap : Point3 → Point3)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := reentry.normalization.croppedRefined)
      (fun point => planeMap point))
    (prepared : Proposition63OneScaleConstantMultiplicityData
      (secondLoss := secondLoss) planeMap original)
    (cells : Proposition63BalancedCellData (scale := sqrtScale)
      prepared.refined.shading)
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) (hqueryScale : 0 < queryScale)
    (hsqrtScale : 0 < sqrtScale)
    (coefficient : NNReal) (hlipschitz : LipschitzWith coefficient planeMap)
    (spatialScale variationScale : ℝ)
    (hvariationBudget :
      (coefficient : ℝ) * spatialScale ≤ variationScale)
    (constant : ENNReal)
    (hconstant : Kakeya.realRpowENN delta (-secondLoss) ≤ constant)
    (leftFactor rightFactor : ENNReal)
    (hincoming : leftFactor * current.mass ≤
      rightFactor * original.shading.mass) :
    let lineFactor :=
      ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2))
    let inverseCoverFactor :=
      ((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))
    let preparationLoss := prepared.preparationLoss
    let queryFactor := ENNReal.ofReal (4 * queryScale)
    ∃ next : WZ1PaperTubeShading initialNormalized.croppedFamily,
      PaperIsSubshading next current ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union,
        next.pointMultiplicity point = current.pointMultiplicity point) ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) ∧
      (∀ point ∈ next.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (next.union ∩ Metric.closedBall point
              (Real.sqrt queryScale)))
          queryScale (1 - sigma) constant) ∧
      (lineFactor * inverseCoverFactor * leftFactor) * current.mass ≤
        (rightFactor * (preparationLoss * (2 * queryFactor))) * next.mass := by
  dsimp only
  have hcandidateAD : ∀ point ∈ (full.lineHitCandidate hdelta).union,
      IsADSet1
        (scalarProjection (planeMap point)
          ((full.lineHitCandidate hdelta).union ∩
            Metric.closedBall point (Real.sqrt queryScale)))
        queryScale (1 - sigma) constant := by
    intro point hpoint
    exact (full.lineHitCandidate_local_ad hdelta point hpoint).mono_constant
      hconstant
  exact reentry.candidate_joint_one_scale
    (full.lineHitCandidate hdelta) planeMap constant
    (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
      (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) * leftFactor)
    (rightFactor *
      (prepared.preparationLoss *
        (2 * ENNReal.ofReal (4 * queryScale))))
    (full.lineHitCandidate_subshading_source hdelta)
    (full.lineHitCandidate_cubical hdelta)
    (full.lineHitCandidate_variation hdelta coefficient hlipschitz
      spatialScale variationScale hvariationBudget)
    hcandidateAD
    (full.lineHitCandidate_mass_from_current_cancel_cellMass
      (current := current) leftFactor rightFactor hincoming hdelta
      hqueryScale hsqrtScale)

/-- Replace all step-dependent numerical losses in the cell-mass-cancelled
line-hit step by bounds fixed before the finite iteration.  The ambient-family
logarithm is already fixed because every re-entry returns to the same root
cropped family. -/
theorem Proposition63CurrentShadingReentryData.lineHitCandidate_joint_one_scale_of_uniform_budget
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      firstLoss secondLoss queryScale sqrtScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (planeMap : Point3 → Point3)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := reentry.normalization.croppedRefined)
      (fun point => planeMap point))
    (prepared : Proposition63OneScaleConstantMultiplicityData
      (secondLoss := secondLoss) planeMap original)
    (cells : Proposition63BalancedCellData (scale := sqrtScale)
      prepared.refined.shading)
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) (hqueryScale : 0 < queryScale)
    (hquerySmall : queryScale ≤ 1 / 4)
    (hsqrtScale : 0 < sqrtScale)
    (coefficient : NNReal) (hlipschitz : LipschitzWith coefficient planeMap)
    (spatialScale variationScale : ℝ)
    (hvariationBudget :
      (coefficient : ℝ) * spatialScale ≤ variationScale)
    (constant : ENNReal)
    (hconstant : Kakeya.realRpowENN delta (-secondLoss) ≤ constant)
    (leftFactor rightFactor uniformLineFactor uniformPreparationLoss : ENNReal)
    (uniformCoverBudget : ℕ)
    (hincoming : leftFactor * current.mass ≤
      rightFactor * original.shading.mass)
    (hlineFactor : uniformLineFactor ≤
      ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)))
    (hpreparationLoss : prepared.preparationLoss ≤ uniformPreparationLoss)
    (hcoverBudget : coverBudget ≤ uniformCoverBudget) :
    let inverseUniformCoverFactor :=
      ((1 : ENNReal) / 2) / (2 * (uniformCoverBudget : ENNReal))
    ∃ next : WZ1PaperTubeShading initialNormalized.croppedFamily,
      PaperIsSubshading next current ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union,
        next.pointMultiplicity point = current.pointMultiplicity point) ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) ∧
      (∀ point ∈ next.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (next.union ∩ Metric.closedBall point
              (Real.sqrt queryScale)))
          queryScale (1 - sigma) constant) ∧
      (uniformLineFactor * inverseUniformCoverFactor * leftFactor) *
          current.mass ≤
        (rightFactor * (uniformPreparationLoss * 2)) * next.mass := by
  dsimp only
  have hcoverCast : (coverBudget : ENNReal) ≤
      (uniformCoverBudget : ENNReal) := by
    exact_mod_cast hcoverBudget
  have hinverseCover :
      ((1 : ENNReal) / 2) /
          (2 * (uniformCoverBudget : ENNReal)) ≤
        ((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal)) := by
    exact ENNReal.div_le_div_left (mul_le_mul_left' hcoverCast 2) _
  have hqueryFactor : ENNReal.ofReal (4 * queryScale) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hleft :
      uniformLineFactor *
          (((1 : ENNReal) / 2) /
            (2 * (uniformCoverBudget : ENNReal))) * leftFactor ≤
        ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          (((1 : ENNReal) / 2) /
            (2 * (coverBudget : ENNReal))) * leftFactor := by
    gcongr
  have hright :
      rightFactor *
          (prepared.preparationLoss *
            (2 * ENNReal.ofReal (4 * queryScale))) ≤
        rightFactor *
          (uniformPreparationLoss * 2) := by
    apply mul_le_mul_left'
    calc
      prepared.preparationLoss *
            (2 * ENNReal.ofReal (4 * queryScale)) ≤
          uniformPreparationLoss *
            (2 * ENNReal.ofReal (4 * queryScale)) := by gcongr
      _ ≤ uniformPreparationLoss * 2 := by
        gcongr
        simpa using mul_le_mul_left' hqueryFactor 2
  have hcandidateAD : ∀ point ∈ (full.lineHitCandidate hdelta).union,
      IsADSet1
        (scalarProjection (planeMap point)
          ((full.lineHitCandidate hdelta).union ∩
            Metric.closedBall point (Real.sqrt queryScale)))
        queryScale (1 - sigma) constant := by
    intro point hpoint
    exact (full.lineHitCandidate_local_ad hdelta point hpoint).mono_constant
      hconstant
  exact reentry.candidate_joint_one_scale_of_factors
    (full.lineHitCandidate hdelta) planeMap constant
    (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
      (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) * leftFactor)
    (rightFactor *
      (prepared.preparationLoss *
        (2 * ENNReal.ofReal (4 * queryScale))))
    (uniformLineFactor *
      (((1 : ENNReal) / 2) /
        (2 * (uniformCoverBudget : ENNReal))) * leftFactor)
    (rightFactor *
      (uniformPreparationLoss * 2))
    (full.lineHitCandidate_subshading_source hdelta)
    (full.lineHitCandidate_cubical hdelta)
    (full.lineHitCandidate_variation hdelta coefficient hlipschitz
      spatialScale variationScale hvariationBudget)
    hcandidateAD
    (full.lineHitCandidate_mass_from_current_cancel_cellMass
      (current := current) leftFactor rightFactor hincoming hdelta
      hqueryScale hsqrtScale)
    hleft hright

/-- One complete current-relative finite-grid step.  The sticky witness is
obtained only after re-entering the actual current shading; the caller then
builds variation and AD on one common candidate from that witness. -/
theorem proposition63_current_reentry_joint_one_scale
    {delta sigma initialInputLoss normalizationLoss reentryLoss stickyLoss : ℝ}
    {spatialScale localScale variationScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent logExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (hSticky : ∀ source : PureWZ2ExtremalConfiguration sigma reentryLoss delta,
      ∀ normalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := data.reentryNormalizationLoss) source
          normalizationExponent,
      ∀ rho : WZ2PaperRequestedScale delta,
        Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
        rho.1 ≤ Real.rpow delta stickyLoss →
        Nonempty (PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          normalized.croppedRefined rho logExponent))
    (rho : WZ2PaperRequestedScale delta)
    (hrhoLower : Real.rpow delta (1 - stickyLoss) ≤ rho.1)
    (hrhoUpper : rho.1 ≤ Real.rpow delta stickyLoss)
    (planeMap : Point3 → Point3)
    (constant leftFactor rightFactor : ENNReal)
    (candidateStep : ∀ sticky : PureWZ2PropStickyData
        (sigma := sigma) (outputLoss := stickyLoss)
        data.normalization.croppedRefined rho logExponent,
      ∃ candidate : WZ1PaperTubeShading data.normalization.croppedFamily,
        PaperIsSubshading candidate data.normalization.croppedRefined ∧
        WZ1PaperIsCubicalShading candidate ∧
        (∀ first ∈ candidate.union, ∀ second ∈ candidate.union,
          dist first second ≤ spatialScale →
            dist (planeMap first) (planeMap second) ≤ variationScale) ∧
        (∀ point ∈ candidate.union,
          IsADSet1
            (scalarProjection (planeMap point)
              (candidate.union ∩ Metric.closedBall point
                (Real.sqrt localScale)))
            localScale (1 - sigma) constant) ∧
        leftFactor * current.mass ≤ rightFactor * candidate.mass) :
    ∃ next : WZ1PaperTubeShading initialNormalized.croppedFamily,
      PaperIsSubshading next current ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union,
        next.pointMultiplicity point = current.pointMultiplicity point) ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) ∧
      (∀ point ∈ next.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (next.union ∩ Metric.closedBall point
              (Real.sqrt localScale)))
          localScale (1 - sigma) constant) ∧
      leftFactor * current.mass ≤ rightFactor * next.mass := by
  rcases proposition63CurrentShadingReentry_sticky data hSticky rho
      hrhoLower hrhoUpper with ⟨sticky⟩
  rcases candidateStep sticky with
    ⟨candidate, hsub, hcubical, hvariation, hlocalAD, hmass⟩
  exact data.candidate_joint_one_scale candidate planeMap constant
    leftFactor rightFactor hsub hcubical hvariation hlocalAD hmass

/-- Finite Lemma 4.12 bookkeeping with a fresh ordinary-trace Proposition
6.2 re-entry at every scheduled scale.  Unlike
`RestrictedExactCoverSchedule`, no sticky witness is chosen from the original
source in advance: `prepare` is applied to the actual current shading, and
only its normalization is passed to `hSticky`. -/
theorem proposition63_finite_sequential_reentry_iteration
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      reentryNormalizationLoss stickyLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent logExponent N : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (planeMap : Point3 → Point3)
    (requested : Fin N → WZ2PaperRequestedScale delta)
    (spatialScale localScale variationScale : ℕ → ℝ)
    (constant : ENNReal)
    (leftFactor rightFactor : ℕ → ENNReal)
    (hSticky : ∀ source : PureWZ2ExtremalConfiguration sigma reentryLoss delta,
      ∀ normalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := reentryNormalizationLoss) source normalizationExponent,
      ∀ rho : WZ2PaperRequestedScale delta,
        Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
        rho.1 ≤ Real.rpow delta stickyLoss →
        Nonempty (PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          normalized.croppedRefined rho logExponent))
    (hlower : ∀ index,
      Real.rpow delta (1 - stickyLoss) ≤ (requested index).1)
    (hupper : ∀ index,
      (requested index).1 ≤ Real.rpow delta stickyLoss)
    (prepare : ∀ index : ℕ, ∀ hindex : index < N,
      ∀ current : WZ1PaperTubeShading initialNormalized.croppedFamily,
        PaperIsSubshading current initialNormalized.croppedRefined →
        WZ1PaperIsCubicalShading current →
        (∀ point ∈ current.union, current.pointMultiplicity point =
          initialNormalized.croppedRefined.pointMultiplicity point) →
        ∃ data : Proposition63CurrentShadingReentryData
            (reentryLoss := reentryLoss) initialNormalized current,
          data.reentryNormalizationLoss = reentryNormalizationLoss)
    (candidateStep : ∀ index : ℕ, ∀ hindex : index < N,
      ∀ current : WZ1PaperTubeShading initialNormalized.croppedFamily,
        ∀ hcurrentSub : PaperIsSubshading current
          initialNormalized.croppedRefined,
        ∀ hcurrentCubical : WZ1PaperIsCubicalShading current,
        ∀ hcurrentMultiplicity : ∀ point ∈ current.union,
          current.pointMultiplicity point =
            initialNormalized.croppedRefined.pointMultiplicity point,
        ∀ data : Proposition63CurrentShadingReentryData
          (reentryLoss := reentryLoss) initialNormalized current,
        ∀ sticky : PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          data.normalization.croppedRefined
          (requested ⟨index, hindex⟩) logExponent,
          ∃ candidate : WZ1PaperTubeShading
              data.normalization.croppedFamily,
            PaperIsSubshading candidate
              data.normalization.croppedRefined ∧
            WZ1PaperIsCubicalShading candidate ∧
            (∀ first ∈ candidate.union, ∀ second ∈ candidate.union,
              dist first second ≤ spatialScale index →
                dist (planeMap first) (planeMap second) ≤
                  variationScale index) ∧
            (∀ point ∈ candidate.union,
              IsADSet1
                (scalarProjection (planeMap point)
                  (candidate.union ∩ Metric.closedBall point
                    (Real.sqrt (localScale index))))
                (localScale index) (1 - sigma) constant) ∧
            leftFactor index * current.mass ≤
              rightFactor index * candidate.mass) :
    ∃ final : WZ1PaperTubeShading initialNormalized.croppedFamily,
      PaperIsSubshading final initialNormalized.croppedRefined ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union, final.pointMultiplicity point =
        initialNormalized.croppedRefined.pointMultiplicity point) ∧
      (∀ index, index < N → ∀ first ∈ final.union,
        ∀ second ∈ final.union, dist first second ≤ spatialScale index →
          dist (planeMap first) (planeMap second) ≤ variationScale index) ∧
      (∀ index, index < N → ∀ point ∈ final.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (final.union ∩ Metric.closedBall point
              (Real.sqrt (localScale index))))
          (localScale index) (1 - sigma) constant) ∧
      (∏ index ∈ Finset.range N, leftFactor index) *
          initialNormalized.croppedRefined.mass ≤
        (∏ index ∈ Finset.range N, rightFactor index) * final.mass := by
  apply joint_finite_variation_local_ad_iteration
    initialNormalized.croppedRefined initialNormalized.cropped_cubical
      planeMap N spatialScale localScale variationScale constant
      leftFactor rightFactor
  intro index hindex current hcurrentSub hcurrentCubical
    hcurrentMultiplicity
  rcases prepare index hindex current hcurrentSub hcurrentCubical
      hcurrentMultiplicity with ⟨data, hnormalizationLoss⟩
  have hStickyData :
      ∀ source : PureWZ2ExtremalConfiguration sigma reentryLoss delta,
        ∀ normalized : PureWZ2CroppedCriticalNormalizationData
          (outputLoss := data.reentryNormalizationLoss) source
            normalizationExponent,
          ∀ rho : WZ2PaperRequestedScale delta,
            Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
            rho.1 ≤ Real.rpow delta stickyLoss →
              Nonempty (PureWZ2PropStickyData
                (sigma := sigma) (outputLoss := stickyLoss)
                normalized.croppedRefined rho logExponent) := by
    rw [hnormalizationLoss]
    exact hSticky
  apply proposition63_current_reentry_joint_one_scale data hStickyData
    (requested ⟨index, hindex⟩)
    (hlower ⟨index, hindex⟩) (hupper ⟨index, hindex⟩) planeMap constant
    (leftFactor index) (rightFactor index)
  exact candidateStep index hindex current hcurrentSub hcurrentCubical
    hcurrentMultiplicity data

/-- Positive-mass finite Lemma 4.12 iteration.  This is the form needed by
the concrete ordinary-trace producer: every successive current shading is
certified nonzero before re-entry is requested. -/
theorem proposition63_finite_sequential_reentry_iteration_of_mass_pos
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      reentryNormalizationLoss stickyLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent logExponent N : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (planeMap : Point3 → Point3)
    (requested : Fin N → WZ2PaperRequestedScale delta)
    (spatialScale localScale variationScale : ℕ → ℝ)
    (constant : ENNReal)
    (leftFactor rightFactor : ℕ → ENNReal)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hleftFactorPos : ∀ index, index < N → 0 < leftFactor index)
    (hSticky : ∀ source : PureWZ2ExtremalConfiguration sigma reentryLoss delta,
      ∀ normalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := reentryNormalizationLoss) source normalizationExponent,
      ∀ rho : WZ2PaperRequestedScale delta,
        Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
        rho.1 ≤ Real.rpow delta stickyLoss →
        Nonempty (PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          normalized.croppedRefined rho logExponent))
    (hlower : ∀ index,
      Real.rpow delta (1 - stickyLoss) ≤ (requested index).1)
    (hupper : ∀ index,
      (requested index).1 ≤ Real.rpow delta stickyLoss)
    (prepare : ∀ index : ℕ, ∀ hindex : index < N,
      ∀ current : WZ1PaperTubeShading initialNormalized.croppedFamily,
        PaperIsSubshading current initialNormalized.croppedRefined →
        WZ1PaperIsCubicalShading current →
        (∀ point ∈ current.union, current.pointMultiplicity point =
          initialNormalized.croppedRefined.pointMultiplicity point) →
        (∏ prior ∈ Finset.range index, leftFactor prior) *
            initialNormalized.croppedRefined.mass ≤
          (∏ prior ∈ Finset.range index, rightFactor prior) * current.mass →
        0 < current.mass →
        ∃ data : Proposition63CurrentShadingReentryData
            (reentryLoss := reentryLoss) initialNormalized current,
          data.reentryNormalizationLoss = reentryNormalizationLoss)
    (candidateStep : ∀ index : ℕ, ∀ hindex : index < N,
      ∀ current : WZ1PaperTubeShading initialNormalized.croppedFamily,
        ∀ hcurrentSub : PaperIsSubshading current
          initialNormalized.croppedRefined,
        ∀ hcurrentCubical : WZ1PaperIsCubicalShading current,
        ∀ hcurrentMultiplicity : ∀ point ∈ current.union,
          current.pointMultiplicity point =
            initialNormalized.croppedRefined.pointMultiplicity point,
        ∀ hcurrentMassLedger :
          (∏ prior ∈ Finset.range index, leftFactor prior) *
              initialNormalized.croppedRefined.mass ≤
            (∏ prior ∈ Finset.range index, rightFactor prior) * current.mass,
        ∀ hcurrentMass : 0 < current.mass,
        ∀ data : Proposition63CurrentShadingReentryData
          (reentryLoss := reentryLoss) initialNormalized current,
        ∀ sticky : PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          data.normalization.croppedRefined
          (requested ⟨index, hindex⟩) logExponent,
          ∃ candidate : WZ1PaperTubeShading
              data.normalization.croppedFamily,
            PaperIsSubshading candidate
              data.normalization.croppedRefined ∧
            WZ1PaperIsCubicalShading candidate ∧
            (∀ first ∈ candidate.union, ∀ second ∈ candidate.union,
              dist first second ≤ spatialScale index →
                dist (planeMap first) (planeMap second) ≤
                  variationScale index) ∧
            (∀ point ∈ candidate.union,
              IsADSet1
                (scalarProjection (planeMap point)
                  (candidate.union ∩ Metric.closedBall point
                    (Real.sqrt (localScale index))))
                (localScale index) (1 - sigma) constant) ∧
            leftFactor index * current.mass ≤
              rightFactor index * candidate.mass) :
    ∃ final : WZ1PaperTubeShading initialNormalized.croppedFamily,
      PaperIsSubshading final initialNormalized.croppedRefined ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        final.pointMultiplicity point =
          initialNormalized.croppedRefined.pointMultiplicity point) ∧
      (∀ index, index < N → ∀ first ∈ final.union,
        ∀ second ∈ final.union, dist first second ≤ spatialScale index →
          dist (planeMap first) (planeMap second) ≤ variationScale index) ∧
      (∀ index, index < N → ∀ point ∈ final.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (final.union ∩ Metric.closedBall point
              (Real.sqrt (localScale index))))
          (localScale index) (1 - sigma) constant) ∧
      (∏ index ∈ Finset.range N, leftFactor index) *
          initialNormalized.croppedRefined.mass ≤
        (∏ index ∈ Finset.range N, rightFactor index) * final.mass ∧
      0 < final.mass := by
  apply joint_finite_variation_local_ad_iteration_of_mass_pos
    initialNormalized.croppedRefined initialNormalized.cropped_cubical
      (cropped_extremal_shading_mass_pos
        initialNormalized.final_extremal initialNormalized.line_class
        hdeltaSmall)
      planeMap N spatialScale localScale variationScale constant
      leftFactor rightFactor hleftFactorPos
  intro index hindex current hcurrentSub hcurrentCubical
    hcurrentMultiplicity hcurrentMassLedger hcurrentMass
  rcases prepare index hindex current hcurrentSub hcurrentCubical
      hcurrentMultiplicity hcurrentMassLedger hcurrentMass with
    ⟨data, hnormalizationLoss⟩
  have hStickyData :
      ∀ source : PureWZ2ExtremalConfiguration sigma reentryLoss delta,
        ∀ normalized : PureWZ2CroppedCriticalNormalizationData
          (outputLoss := data.reentryNormalizationLoss) source
            normalizationExponent,
          ∀ rho : WZ2PaperRequestedScale delta,
            Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
            rho.1 ≤ Real.rpow delta stickyLoss →
              Nonempty (PureWZ2PropStickyData
                (sigma := sigma) (outputLoss := stickyLoss)
                normalized.croppedRefined rho logExponent) := by
    rw [hnormalizationLoss]
    exact hSticky
  apply proposition63_current_reentry_joint_one_scale data hStickyData
    (requested ⟨index, hindex⟩)
    (hlower ⟨index, hindex⟩) (hupper ⟨index, hindex⟩) planeMap constant
    (leftFactor index) (rightFactor index)
  exact candidateStep index hindex current hcurrentSub hcurrentCubical
    hcurrentMultiplicity hcurrentMassLedger hcurrentMass data

/-- Specialized finite wrapper whose analytic input is the standard
`PureWZ2OneScaleLocalGrainData`.  It makes the remaining mathematical leaf
precise: after current-relative re-entry and Proposition 6.2, produce one
one-scale local-grain output on the normalized selected family together with
its mass comparison. -/
theorem proposition63_finite_sequential_oneScale_iteration
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      reentryNormalizationLoss stickyLoss oneScaleLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent logExponent N : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (planeMap : Point3 → Point3)
    (requested : Fin N → WZ2PaperRequestedScale delta)
    (spatialScale localScale variationScale : ℕ → ℝ)
    (constant : ENNReal)
    (leftFactor rightFactor : ℕ → ENNReal)
    (coefficient : NNReal)
    (hlipschitz : LipschitzWith coefficient planeMap)
    (hvariationBudget : ∀ index, index < N →
      (coefficient : ℝ) * spatialScale index ≤ variationScale index)
    (hSticky : ∀ source : PureWZ2ExtremalConfiguration sigma reentryLoss delta,
      ∀ normalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := reentryNormalizationLoss) source normalizationExponent,
      ∀ rho : WZ2PaperRequestedScale delta,
        Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
        rho.1 ≤ Real.rpow delta stickyLoss →
        Nonempty (PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          normalized.croppedRefined rho logExponent))
    (hlower : ∀ index,
      Real.rpow delta (1 - stickyLoss) ≤ (requested index).1)
    (hupper : ∀ index,
      (requested index).1 ≤ Real.rpow delta stickyLoss)
    (prepare : ∀ index : ℕ, ∀ hindex : index < N,
      ∀ current : WZ1PaperTubeShading initialNormalized.croppedFamily,
        PaperIsSubshading current initialNormalized.croppedRefined →
        WZ1PaperIsCubicalShading current →
        (∀ point ∈ current.union, current.pointMultiplicity point =
          initialNormalized.croppedRefined.pointMultiplicity point) →
        ∃ data : Proposition63CurrentShadingReentryData
            (reentryLoss := reentryLoss) initialNormalized current,
          data.reentryNormalizationLoss = reentryNormalizationLoss)
    (oneScaleStep : ∀ index : ℕ, ∀ hindex : index < N,
      ∀ current : WZ1PaperTubeShading initialNormalized.croppedFamily,
        ∀ hcurrentSub : PaperIsSubshading current
          initialNormalized.croppedRefined,
        ∀ hcurrentCubical : WZ1PaperIsCubicalShading current,
        ∀ hcurrentMultiplicity : ∀ point ∈ current.union,
          current.pointMultiplicity point =
            initialNormalized.croppedRefined.pointMultiplicity point,
        ∀ data : Proposition63CurrentShadingReentryData
          (reentryLoss := reentryLoss) initialNormalized current,
        ∀ sticky : PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          data.normalization.croppedRefined
          (requested ⟨index, hindex⟩) logExponent,
          ∃ oneScale : PureWZ2OneScaleLocalGrainData
              (sigma := sigma) (outputLoss := oneScaleLoss)
              (rho := localScale index)
              (Y := data.normalization.croppedRefined)
              (fun point => planeMap point),
            leftFactor index * current.mass ≤
              rightFactor index * oneScale.shading.mass)
    (hconstant : Kakeya.realRpowENN delta (-oneScaleLoss) ≤ constant) :
    ∃ final : WZ1PaperTubeShading initialNormalized.croppedFamily,
      PaperIsSubshading final initialNormalized.croppedRefined ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union, final.pointMultiplicity point =
        initialNormalized.croppedRefined.pointMultiplicity point) ∧
      (∀ index, index < N → ∀ first ∈ final.union,
        ∀ second ∈ final.union, dist first second ≤ spatialScale index →
          dist (planeMap first) (planeMap second) ≤ variationScale index) ∧
      (∀ index, index < N → ∀ point ∈ final.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (final.union ∩ Metric.closedBall point
              (Real.sqrt (localScale index))))
          (localScale index) (1 - sigma) constant) ∧
      (∏ index ∈ Finset.range N, leftFactor index) *
          initialNormalized.croppedRefined.mass ≤
        (∏ index ∈ Finset.range N, rightFactor index) * final.mass := by
  apply proposition63_finite_sequential_reentry_iteration initialNormalized
    planeMap requested spatialScale localScale variationScale constant
    leftFactor rightFactor hSticky hlower hupper prepare
  intro index hindex current hcurrentSub hcurrentCubical
    hcurrentMultiplicity data sticky
  rcases oneScaleStep index hindex current hcurrentSub hcurrentCubical
      hcurrentMultiplicity data sticky with
    ⟨oneScale, hmass⟩
  exact data.oneScaleCandidate planeMap constant
    (leftFactor index) (rightFactor index)
    (spatialScale index) (variationScale index) coefficient hlipschitz
    (hvariationBudget index hindex) oneScale hconstant hmass

/-- Positive-mass specialization of the finite one-scale iterator. -/
theorem proposition63_finite_sequential_oneScale_iteration_of_mass_pos
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      reentryNormalizationLoss stickyLoss oneScaleLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent logExponent N : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (planeMap : Point3 → Point3)
    (requested : Fin N → WZ2PaperRequestedScale delta)
    (spatialScale localScale variationScale : ℕ → ℝ)
    (constant : ENNReal)
    (leftFactor rightFactor : ℕ → ENNReal)
    (coefficient : NNReal)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hleftFactorPos : ∀ index, index < N → 0 < leftFactor index)
    (hlipschitz : LipschitzWith coefficient planeMap)
    (hvariationBudget : ∀ index, index < N →
      (coefficient : ℝ) * spatialScale index ≤ variationScale index)
    (hSticky : ∀ source : PureWZ2ExtremalConfiguration sigma reentryLoss delta,
      ∀ normalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := reentryNormalizationLoss) source normalizationExponent,
      ∀ rho : WZ2PaperRequestedScale delta,
        Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
        rho.1 ≤ Real.rpow delta stickyLoss →
        Nonempty (PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          normalized.croppedRefined rho logExponent))
    (hlower : ∀ index,
      Real.rpow delta (1 - stickyLoss) ≤ (requested index).1)
    (hupper : ∀ index,
      (requested index).1 ≤ Real.rpow delta stickyLoss)
    (prepare : ∀ index : ℕ, ∀ hindex : index < N,
      ∀ current : WZ1PaperTubeShading initialNormalized.croppedFamily,
        PaperIsSubshading current initialNormalized.croppedRefined →
        WZ1PaperIsCubicalShading current →
        (∀ point ∈ current.union, current.pointMultiplicity point =
          initialNormalized.croppedRefined.pointMultiplicity point) →
        (∏ prior ∈ Finset.range index, leftFactor prior) *
            initialNormalized.croppedRefined.mass ≤
          (∏ prior ∈ Finset.range index, rightFactor prior) * current.mass →
        0 < current.mass →
        ∃ data : Proposition63CurrentShadingReentryData
            (reentryLoss := reentryLoss) initialNormalized current,
          data.reentryNormalizationLoss = reentryNormalizationLoss)
    (oneScaleStep : ∀ index : ℕ, ∀ hindex : index < N,
      ∀ current : WZ1PaperTubeShading initialNormalized.croppedFamily,
        ∀ hcurrentSub : PaperIsSubshading current
          initialNormalized.croppedRefined,
        ∀ hcurrentCubical : WZ1PaperIsCubicalShading current,
        ∀ hcurrentMultiplicity : ∀ point ∈ current.union,
          current.pointMultiplicity point =
            initialNormalized.croppedRefined.pointMultiplicity point,
        ∀ hcurrentMassLedger :
          (∏ prior ∈ Finset.range index, leftFactor prior) *
              initialNormalized.croppedRefined.mass ≤
            (∏ prior ∈ Finset.range index, rightFactor prior) * current.mass,
        ∀ hcurrentMass : 0 < current.mass,
        ∀ data : Proposition63CurrentShadingReentryData
          (reentryLoss := reentryLoss) initialNormalized current,
        ∀ sticky : PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          data.normalization.croppedRefined
          (requested ⟨index, hindex⟩) logExponent,
          ∃ oneScale : PureWZ2OneScaleLocalGrainData
              (sigma := sigma) (outputLoss := oneScaleLoss)
              (rho := localScale index)
              (Y := data.normalization.croppedRefined)
              (fun point => planeMap point),
            leftFactor index * current.mass ≤
              rightFactor index * oneScale.shading.mass)
    (hconstant : Kakeya.realRpowENN delta (-oneScaleLoss) ≤ constant) :
    ∃ final : WZ1PaperTubeShading initialNormalized.croppedFamily,
      PaperIsSubshading final initialNormalized.croppedRefined ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        final.pointMultiplicity point =
          initialNormalized.croppedRefined.pointMultiplicity point) ∧
      (∀ index, index < N → ∀ first ∈ final.union,
        ∀ second ∈ final.union, dist first second ≤ spatialScale index →
          dist (planeMap first) (planeMap second) ≤ variationScale index) ∧
      (∀ index, index < N → ∀ point ∈ final.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (final.union ∩ Metric.closedBall point
              (Real.sqrt (localScale index))))
          (localScale index) (1 - sigma) constant) ∧
      (∏ index ∈ Finset.range N, leftFactor index) *
          initialNormalized.croppedRefined.mass ≤
        (∏ index ∈ Finset.range N, rightFactor index) * final.mass ∧
      0 < final.mass := by
  apply proposition63_finite_sequential_reentry_iteration_of_mass_pos
    initialNormalized planeMap requested spatialScale localScale
      variationScale constant leftFactor rightFactor hdeltaSmall
      hleftFactorPos hSticky hlower hupper prepare
  intro index hindex current hcurrentSub hcurrentCubical
    hcurrentMultiplicity hcurrentMassLedger hcurrentMass data
      sticky
  rcases oneScaleStep index hindex current hcurrentSub hcurrentCubical
      hcurrentMultiplicity hcurrentMassLedger hcurrentMass data
      sticky with
    ⟨oneScale, hmass⟩
  exact data.oneScaleCandidate planeMap constant
    (leftFactor index) (rightFactor index)
    (spatialScale index) (variationScale index) coefficient hlipschitz
    (hvariationBudget index hindex) oneScale hconstant hmass

end Kakeya.Assouad.PureWZ2

end
