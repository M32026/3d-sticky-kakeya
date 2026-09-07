import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63InitialLocalGrainReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentOneScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentFinePullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63OneScaleMultiplicityPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FreshBalancedCells
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63OneScaleFullGrainCell
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63LineHitGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CardinalityFix
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63SequentialReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63UniformLineHitBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PureCriticalTailBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedCriticalFloorSelection
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma18CenteredIntervalTransfer
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma18CloseProjectionIntervalTransfer
import MyLeanRepo.Kakeya.Assouad.WZ1.GridCellPruning

/-!
# The nested two-cover input to the Proposition 6.3 full-grain step

The paper first proves a point-centered covering estimate at an arbitrary
interval scale `tauScale`.  It then re-enters Proposition 6.2 on that exact
refinement and proves a second point-centered estimate at
`sqrt queryScale`.  Only after both estimates live on the same final shading
does the full-grain/Fubini argument begin.

This file records that dependency without assuming the final one-scale AD
conclusion.  In particular, it never covers a square-root cell by
`tauScale`-balls and therefore introduces no three-dimensional covering
factor.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

attribute [local instance] Classical.propDecidable

/-- All hypotheses of one dependent HIGH point-cover call, with no local-AD
conclusion in the input.  This package is used twice in Lemma 4.10: first at
the arbitrary interval radius and then at the square-root radius. -/
structure Proposition63DependentHighPointCoverInput
    {delta sigma outerLoss reentryLoss innerLoss targetLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    (data : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau)
    (planeMap : Point3 → Point3)
    (coefficient : NNReal) where
  epsilon₁ : ℝ
  epsilon₃ : ℝ
  propP : PureWZ2PropertyPData
    (sigma := sigma) (coarseShading := data.ambientRefined)
    (tau := tau.1) epsilon₁ epsilon₃
  incidenceBound : ℝ
  plane_unit : ∀ point ∈ propP.propertyThree.union, ‖planeMap point‖ = 1
  plane_lipschitz : LipschitzWith coefficient planeMap
  plane_incidence : ∀ index point,
    ∀ hpoint : point ∈ propP.propertyOne.carrier index,
      |@Inner.inner ℝ Point3 _
        (reentry.normalization.croppedFamily.tube index).direction
        (planeMap point)| ≤ incidenceBound
  reentry_target : reentryLoss ≤ targetLoss
  target_loss_pos : 0 < targetLoss
  rho_lt_one : rho.1 < 1
  mass_slack : proposition63DependentPropertyThreeMassLoss
      rho.1 innerLogExponent * Kakeya.realRpowENN rho.1 targetLoss ≤
    Kakeya.realRpowENN rho.1 reentryLoss
  tau_small : tau.1 ≤ 1 / 12
  rho_small : rho.1 ≤ 1 / 1000
  rho_le_tau : rho.1 ≤ tau.1
  tau_sq : tau.1 ^ 2 ≤ 4 * rho.1
  tau_le_one : tau.1 ≤ 1
  sigma_pos : 0 < sigma
  sigma_lt_one : sigma < 1
  epsilon₁_pos : 0 < epsilon₁
  epsilon₃_pos : 0 < epsilon₃
  epsilon_sum : epsilon₁ + epsilon₃ < 1
  logScale : ℝ
  rho_le_logScale : rho.1 ≤ logScale
  logarithmic_bound : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
    scale ≤ logScale → ∀ k : ℕ, 0 < k →
    (k : ℝ) ≤ 100 / scale ^ 3 →
      Real.rpow scale epsilon₁ *
        (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108
  propertyThree_full : ∀ index point,
    point ∈ propP.propertyThree.carrier index →
      Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
          ENNReal.ofReal tau.1 ≤
        volume (propP.propertyThree.carrier index ∩
          Metric.closedBall point tau.1)
  axis_budget : 4 * (6 * rho.1) ^ 2 ≤
    (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2
  C : ENNReal
  covering_arithmetic :
    ENNReal.ofReal
        (((5832 * Real.rpow rho.1 (sigma - outerLoss) *
            Real.rpow tau.1 (3 - sigma - 2 * innerLoss)) /
            (Real.rpow rho.1 (1 + 7 * epsilon₁ + epsilon₃) *
              tau.1 ^ 2 / 200)) *
          (2 * proposition63DependentSlabWidth rho.1 tau.1
            incidenceBound coefficient / rho.1 + 2)) ≤
      C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)

namespace Proposition63DependentHighPointCoverInput

/-- Build the packaged HIGH input directly from the CWA Property-(P)
producer.  Unit-normality and incidence are assumed only on the ambient
refinement; they restrict to the selected whole-cell shading.  The concrete
Property-(P) equality supplies `propertyThree_full` internally. -/
theorem of_cwa
    {delta sigma outerLoss reentryLoss innerLoss targetLoss densityLoss
      epsilon₁ epsilon₃ kappa : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    (data : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau)
    (planeMap : Point3 → Point3)
    (coefficient : NNReal)
    (incidenceBound : ℝ)
    (hplaneUnit : ∀ point ∈ data.ambientRefined.union,
      ‖planeMap point‖ = 1)
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneIncidence : ∀ index point,
      point ∈ data.ambientRefined.carrier index →
        |@Inner.inner ℝ Point3 _
          (reentry.normalization.croppedFamily.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (hreentryTarget : reentryLoss ≤ targetLoss)
    (hretention : Kakeya.realRpowENN rho.1 targetLoss ≤
      wz2PaperPureRefinementFraction rho.1 innerLogExponent *
        Kakeya.realRpowENN rho.1 reentryLoss)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hsmall : Kakeya.realRpowENN rho.1 targetLoss < 1 / 4)
    (hrhoSmall24 : rho.1 ≤ 1 / 24)
    (hrhoSmall10000 : rho.1 ≤ 1 / 10000)
    (hpackingAbsorb :
      (12 * ((2 * 4 * 601 ^ 3 * 12001 ^ 3 + 1 : ℕ) : ENNReal)) *
          ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN rho.1 (-sigma + 4 * targetLoss))
    (hepsilon₁ : 0 < epsilon₁)
    (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (htau : 0 < tau.1)
    (hrhoTau : rho.1 ≤ tau.1)
    (htauLarge : rho.1 * Real.sqrt 3 ≤ tau.1)
    (htauSq : tau.1 ^ 2 ≤ 4 * rho.1)
    (htauOne : tau.1 ≤ 1)
    (hcell :
      Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
          ENNReal.ofReal tau.1 ≤
        Kakeya.realRpowENN rho.1 3)
    (hkappa : 0 < kappa)
    (hkappaOne : kappa ≤ 1)
    (hkappaRho : rho.1 ≤ kappa)
    (hkappaProperty : Real.rpow rho.1 epsilon₃ ≤ kappa)
    (hcloseAbsorb :
      Kakeya.realRpowENN rho.1 (-targetLoss) *
          ENNReal.ofReal (10000 * kappa ^ 2) *
          reentry.normalization.croppedFamily.enncard <
        Kakeya.realRpowENN rho.1 densityLoss *
          reentry.normalization.croppedFamily.enncard)
    (hrhoOne : rho.1 < 1)
    (hmassSlack : proposition63DependentPropertyThreeMassLoss
        rho.1 innerLogExponent * Kakeya.realRpowENN rho.1 targetLoss ≤
      Kakeya.realRpowENN rho.1 reentryLoss)
    (htauSmall : tau.1 ≤ 1 / 12)
    (hrhoSmall : rho.1 ≤ 1 / 1000)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * rho.1) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          (((5832 * Real.rpow rho.1 (sigma - outerLoss) *
              Real.rpow tau.1 (3 - sigma - 2 * innerLoss)) /
              (Real.rpow rho.1 (1 + 7 * epsilon₁ + epsilon₃) *
                tau.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth rho.1 tau.1 incidenceBound
              coefficient / rho.1 + 2)) ≤
        C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)) :
    ∃ input : Proposition63DependentHighPointCoverInput
        (targetLoss := targetLoss) data planeMap coefficient,
      input.C = C := by
  rcases data.propertyP_of_cwa_eq hreentryTarget hretention hdensityLoss
      htargetLoss hsmall hrhoSmall24 hrhoSmall10000 hpackingAbsorb
      hepsilon₁ hepsilon₃ hepsilonSum htau hrhoTau htauLarge htauSq
      htauOne hcell hkappa hkappaOne hkappaRho hkappaProperty
      hcloseAbsorb with ⟨propP, hpropertyEq⟩
  refine ⟨{
    epsilon₁ := epsilon₁
    epsilon₃ := epsilon₃
    propP := propP
    incidenceBound := incidenceBound
    plane_unit := ?_
    plane_lipschitz := hplaneLipschitz
    plane_incidence := ?_
    reentry_target := hreentryTarget
    target_loss_pos := htargetLoss
    rho_lt_one := hrhoOne
    mass_slack := hmassSlack
    tau_small := htauSmall
    rho_small := hrhoSmall
    rho_le_tau := hrhoTau
    tau_sq := htauSq
    tau_le_one := htauOne
    sigma_pos := hsigma
    sigma_lt_one := hsigmaOne
    epsilon₁_pos := hepsilon₁
    epsilon₃_pos := hepsilon₃
    epsilon_sum := hepsilonSum
    logScale := logScale
    rho_le_logScale := hrhoLog
    logarithmic_bound := hlog
    propertyThree_full := ?_
    axis_budget := haxis
    C := C
    covering_arithmetic := harithmetic
  }, rfl⟩
  · intro point hpoint
    apply hplaneUnit point
    rcases hpoint with ⟨index, hindex⟩
    exact ⟨index, propP.propertyOne_sub index
      (propP.propertyThree_sub index hindex)⟩
  · intro index point hpoint
    exact hplaneIncidence index point
      (propP.propertyOne_sub index hpoint)
  · rw [hpropertyEq]
    exact propP.propertyOne_full

/-- Execute the packaged HIGH call and retain source multiplicity, its exact
mass factor, and the point-centered projection estimate. -/
theorem run
    {delta sigma outerLoss reentryLoss innerLoss targetLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    {data : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau}
    {planeMap : Point3 → Point3} {coefficient : NNReal}
    (input : Proposition63DependentHighPointCoverInput
      (targetLoss := targetLoss) data planeMap coefficient) :
    ∃ state : Proposition63ExtremalShadingData
        (sigma := sigma) (outputLoss := targetLoss)
        reentry.normalization.croppedRefined,
      state.shading = data.commonPropertyThree input.propP ∧
      (∀ point ∈ state.shading.union,
        state.shading.pointMultiplicity point =
          reentry.normalization.croppedRefined.pointMultiplicity point) ∧
      (proposition63DependentPropertyThreeMassLoss
          rho.1 innerLogExponent)⁻¹ *
          reentry.normalization.croppedRefined.mass ≤ state.shading.mass ∧
      PureWZ2PointCenteredCoveringAt state.shading planeMap
        (Real.toNNReal rho.1) tau.1
        (input.C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)) := by
  exact data.currentPointCover input.propP planeMap input.incidenceBound
    input.plane_unit input.plane_lipschitz input.plane_incidence
    input.reentry_target input.target_loss_pos input.rho_lt_one
    input.mass_slack input.tau_small input.rho_small input.rho_le_tau
    input.tau_sq input.tau_le_one input.sigma_pos input.sigma_lt_one
    input.epsilon₁_pos input.epsilon₃_pos input.epsilon_sum input.logScale
    input.rho_le_logScale input.logarithmic_bound input.propertyThree_full
    input.axis_budget input.C input.covering_arithmetic

end Proposition63DependentHighPointCoverInput

/-- A point cover lifted through an actual current-shading re-entry.  The
retention factor is normalized to a one-sided inequality so that it composes
directly with the later nested-cover ledger. -/
structure Proposition63LiftedPointCoverData
    {delta sigma inputLoss normalizationLoss outputLoss queryScale
      spatialRadius : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent)
    (current : WZ1PaperTubeShading initialNormalized.croppedFamily)
    (planeMap : Point3 → Point3) (constant : ENNReal) where
  state : Proposition63ExtremalShadingData
    (sigma := sigma) (outputLoss := outputLoss) current
  multiplicity : ∀ point ∈ state.shading.union,
    state.shading.pointMultiplicity point = current.pointMultiplicity point
  retainedFactor : ENNReal
  retained : retainedFactor * current.mass ≤ state.shading.mass
  retained_factor_pos : 0 < retainedFactor
  retained_factor_ne_top : retainedFactor ≠ ⊤
  cover : PureWZ2PointCenteredCoveringAt state.shading planeMap
    (Real.toNNReal queryScale) spatialRadius constant

/-- Restore a point-cover candidate inside an already-extremal parent on the
same tube family.  The common-spatial hull preserves the candidate union and
restores the parent's full pointwise multiplicity; only the displayed local
mass factor is charged. -/
theorem proposition63_point_cover_on_extremal_parent
    {delta sigma inputLoss normalizationLoss parentLoss outputLoss queryScale
      spatialRadius : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent)
    (parent : WZ1PaperTubeShading initialNormalized.croppedFamily)
    (parentExtremal : WZ2PaperCroppedIsExtremal sigma parentLoss
      initialNormalized.croppedFamily parent)
    (parentCWA : WZ2PaperConvexWolffBound
      initialNormalized.croppedFamily
      (Kakeya.realRpowENN delta (-parentLoss)))
    (candidate : WZ1PaperTubeShading initialNormalized.croppedFamily)
    (candidateSub : PaperIsSubshading candidate parent)
    (candidateCubical : WZ1PaperIsCubicalShading candidate)
    (planeMap : Point3 → Point3) (constant : ENNReal)
    (candidateCover : PureWZ2PointCenteredCoveringAt candidate planeMap
      (Real.toNNReal queryScale) spatialRadius constant)
    (retainedFactor : ENNReal)
    (retained : retainedFactor * parent.mass ≤ candidate.mass)
    (retainedPos : 0 < retainedFactor)
    (retainedTop : retainedFactor ≠ ⊤)
    (hparentOutput : parentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss retainedFactor 1 *
        Kakeya.realRpowENN delta outputLoss ≤
      Kakeya.realRpowENN delta parentLoss) :
    ∃ result : Proposition63LiftedPointCoverData
        (outputLoss := outputLoss) (queryScale := queryScale)
        (spatialRadius := spatialRadius) initialNormalized parent planeMap
        constant,
      result.state.shading.union = candidate.union ∧
        result.retainedFactor = retainedFactor := by
  let nextShading := paperCommonSpatialHull parent candidate
  have nextSub : PaperIsSubshading nextShading parent :=
    paperCommonSpatialHull_subshading _ _
  have nextCubical : WZ1PaperIsCubicalShading nextShading :=
    paperCommonSpatialHull_cubical parentExtremal.cubical candidateCubical
  have nextUnion : nextShading.union = candidate.union :=
    paperCommonSpatialHull_union candidateSub
  have nextMass : retainedFactor * parent.mass ≤ nextShading.mass :=
    retained.trans (paperCommonSpatialHull_mass_lower candidateSub)
  let massLoss := proposition63Lemma43MassLoss retainedFactor 1
  have nextMassInv : massLoss⁻¹ * parent.mass ≤ nextShading.mass :=
    proposition63Lemma43MassLoss_inv_mul_le retainedPos retainedTop
      (by norm_num) (by simpa only [one_mul] using nextMass)
  have nextExtremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      initialNormalized.croppedFamily nextShading := by
    apply transfer_cropped_extremal_to_subshading massLoss
      (proposition63Lemma43MassLoss_pos _ _)
      (proposition63Lemma43MassLoss_ne_top retainedPos (by norm_num))
      parentExtremal nextSub nextMassInv nextCubical hparentOutput
    · simpa only [massLoss] using hrestore
    · exact parentExtremal.delta_pos
    · exact parentExtremal.delta_le_one
    · exact houtputLoss
  have nextCWA : WZ2PaperConvexWolffBound
      initialNormalized.croppedFamily
      (Kakeya.realRpowENN delta (-outputLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := parent) (_shading2 := nextShading)
      parentCWA hparentOutput
      parentExtremal.delta_pos parentExtremal.delta_le_one
  let state : Proposition63ExtremalShadingData
      (sigma := sigma) (outputLoss := outputLoss) parent :=
    { shading := nextShading
      subshading := nextSub
      extremal := nextExtremal
      cwa := nextCWA }
  have nextCover : PureWZ2PointCenteredCoveringAt state.shading planeMap
      (Real.toNNReal queryScale) spatialRadius constant := by
    intro point
    have pointCandidate : (point : Point3) ∈ candidate.union := by
      rw [← nextUnion]
      exact point.property
    simpa only [state, nextUnion] using candidateCover ⟨point, pointCandidate⟩
  exact ⟨{
    state := state
    multiplicity := paperCommonSpatialHull_pointMultiplicity_eq
      parent candidate
    retainedFactor := retainedFactor
    retained := nextMass
    retained_factor_pos := retainedPos
    retained_factor_ne_top := retainedTop
    cover := nextCover
  }, nextUnion, rfl⟩

/-- Keep a dependent HIGH point-cover output on its actual normalized coarse
family.  This is the paper-faithful intermediate state between the two
applications of Lemma 17: no zero-extension to the root family and no
extremality restoration are performed here. -/
theorem Proposition63DependentHighPointCoverInput.directPointCover
    {delta sigma outerLoss reentryLoss innerLoss targetLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    {dependent : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau}
    {planeMap : Point3 → Point3} {coefficient : NNReal}
    (input : Proposition63DependentHighPointCoverInput
      (targetLoss := targetLoss) dependent planeMap coefficient) :
    ∃ result : Proposition63LiftedPointCoverData
        (outputLoss := targetLoss) (queryScale := rho.1)
        (spatialRadius := tau.1) reentry.normalization
        reentry.normalization.croppedRefined planeMap
        (input.C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)),
      result.retainedFactor =
        (proposition63DependentPropertyThreeMassLoss
          rho.1 innerLogExponent)⁻¹ := by
  rcases input.run with ⟨state, _hstate, hmultiplicity, hmass, hcover⟩
  let retainedFactor :=
    (proposition63DependentPropertyThreeMassLoss
      rho.1 innerLogExponent)⁻¹
  have hfactor := proposition63DependentPropertyThreeMassLoss_pos_ne_top
    reentry.normalization.final_extremal.delta_pos input.rho_lt_one
    innerLogExponent
  refine ⟨{
    state := state
    multiplicity := hmultiplicity
    retainedFactor := retainedFactor
    retained := by simpa only [retainedFactor] using hmass
    retained_factor_pos := ENNReal.inv_pos.mpr hfactor.2
    retained_factor_ne_top := ENNReal.inv_ne_top.mpr hfactor.1.ne'
    cover := hcover
  }, rfl⟩

/-- Compose the retained mass of a lifted point cover with the ancestry of
its incoming current shading.  The returned factor is positive and finite
and is oriented exactly as `proposition63DependentCoarseReentryOfCurrent`
expects for the next Node-3 call. -/
theorem Proposition63LiftedPointCoverData.composeAncestorRetention
    {delta sigma inputLoss normalizationLoss outputLoss queryScale
      spatialRadius : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    {planeMap : Point3 → Point3} {constant : ENNReal}
    (data : Proposition63LiftedPointCoverData
      (outputLoss := outputLoss) (queryScale := queryScale)
      (spatialRadius := spatialRadius) initialNormalized current planeMap
      constant)
    (ancestorFactor : ENNReal)
    (hancestorPos : 0 < ancestorFactor)
    (hancestorTop : ancestorFactor ≠ ⊤)
    {ancestorMass : ENNReal}
    (hcurrent : ancestorFactor⁻¹ * ancestorMass ≤ current.mass) :
    ∃ nextAncestorFactor : ENNReal,
      0 < nextAncestorFactor ∧
      nextAncestorFactor ≠ ⊤ ∧
      nextAncestorFactor⁻¹ * ancestorMass ≤ data.state.shading.mass := by
  let retainedCoefficient := data.retainedFactor * ancestorFactor⁻¹
  have hcoefficientPos : 0 < retainedCoefficient := by
    apply ENNReal.mul_pos data.retained_factor_pos.ne'
    exact ENNReal.inv_ne_zero.mpr hancestorTop
  have hcoefficientTop : retainedCoefficient ≠ ⊤ := by
    apply ENNReal.mul_ne_top data.retained_factor_ne_top
    exact ENNReal.inv_ne_top.mpr hancestorPos.ne'
  let nextAncestorFactor := retainedCoefficient⁻¹
  refine ⟨nextAncestorFactor, ENNReal.inv_pos.mpr hcoefficientTop,
    ENNReal.inv_ne_top.mpr hcoefficientPos.ne', ?_⟩
  change nextAncestorFactor⁻¹ * ancestorMass ≤ data.state.shading.mass
  rw [show nextAncestorFactor⁻¹ = retainedCoefficient by
    simp [nextAncestorFactor]]
  calc
    retainedCoefficient * ancestorMass =
        data.retainedFactor * (ancestorFactor⁻¹ * ancestorMass) := by
      simp only [retainedCoefficient]
      ring
    _ ≤ data.retainedFactor * current.mass := by gcongr
    _ ≤ data.state.shading.mass := data.retained

/-- Rebase a lifted point-cover state from a retained current shading to a
larger parent shading on the same tube family.  The common-spatial hull keeps
the covered union, restores the parent's complete tube membership at every
surviving point, and composes the two explicit mass-retention factors. -/
theorem Proposition63LiftedPointCoverData.rebaseByCommonHull
    {delta sigma inputLoss normalizationLoss outputLoss queryScale
      spatialRadius : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {current parent : WZ1PaperTubeShading
      initialNormalized.croppedFamily}
    {planeMap : Point3 → Point3} {constant : ENNReal}
    (data : Proposition63LiftedPointCoverData
      (outputLoss := outputLoss) (queryScale := queryScale)
      (spatialRadius := spatialRadius) initialNormalized current planeMap
      constant)
    (hcurrentSub : PaperIsSubshading current parent)
    (hparentCubical : WZ1PaperIsCubicalShading parent)
    (ancestorFactor : ENNReal)
    (hancestorMass : ancestorFactor * parent.mass ≤ current.mass)
    (hancestorPos : 0 < ancestorFactor)
    (hancestorTop : ancestorFactor ≠ ⊤) :
    ∃ result : Proposition63LiftedPointCoverData
        (outputLoss := outputLoss) (queryScale := queryScale)
        (spatialRadius := spatialRadius) initialNormalized parent planeMap
        constant,
      result.retainedFactor = data.retainedFactor * ancestorFactor ∧
      result.state.shading.union = data.state.shading.union := by
  have hstateSubParent : PaperIsSubshading data.state.shading parent :=
    fun index point hpoint => hcurrentSub index
      (data.state.subshading index hpoint)
  let shading := paperCommonSpatialHull parent data.state.shading
  have shadingSub : PaperIsSubshading shading parent :=
    paperCommonSpatialHull_subshading _ _
  have shadingCubical : WZ1PaperIsCubicalShading shading :=
    paperCommonSpatialHull_cubical hparentCubical data.state.extremal.cubical
  have shadingUnion : shading.union = data.state.shading.union :=
    paperCommonSpatialHull_union hstateSubParent
  have shadingMass : data.state.shading.mass ≤ shading.mass :=
    paperCommonSpatialHull_mass_lower hstateSubParent
  have shadingExtremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      initialNormalized.croppedFamily shading := by
    refine {
      delta_pos := data.state.extremal.delta_pos
      delta_le_one := data.state.extremal.delta_le_one
      nonempty := data.state.extremal.nonempty
      cwa_nearby_scales := data.state.extremal.cwa_nearby_scales
      cubical := shadingCubical
      dense := data.state.extremal.dense.trans shadingMass
      volume_upper := ?_
    }
    rw [shadingUnion]
    exact data.state.extremal.volume_upper
  let state : Proposition63ExtremalShadingData
      (sigma := sigma) (outputLoss := outputLoss) parent :=
    { shading := shading
      subshading := shadingSub
      extremal := shadingExtremal
      cwa := data.state.cwa }
  let retainedFactor := data.retainedFactor * ancestorFactor
  have retained : retainedFactor * parent.mass ≤ state.shading.mass := by
    calc
      retainedFactor * parent.mass =
          data.retainedFactor * (ancestorFactor * parent.mass) := by
        simp only [retainedFactor]
        ring
      _ ≤ data.retainedFactor * current.mass := by gcongr
      _ ≤ data.state.shading.mass := data.retained
      _ ≤ state.shading.mass := shadingMass
  have retainedPos : 0 < retainedFactor :=
    ENNReal.mul_pos data.retained_factor_pos.ne' hancestorPos.ne'
  have retainedTop : retainedFactor ≠ ⊤ :=
    ENNReal.mul_ne_top data.retained_factor_ne_top hancestorTop
  have stateCover : PureWZ2PointCenteredCoveringAt state.shading planeMap
      (Real.toNNReal queryScale) spatialRadius constant := by
    intro point
    have pointOld : (point : Point3) ∈ data.state.shading.union := by
      rw [← shadingUnion]
      exact point.property
    simpa only [state, shadingUnion] using data.cover ⟨point, pointOld⟩
  refine ⟨{
    state := state
    multiplicity := paperCommonSpatialHull_pointMultiplicity_eq
      parent data.state.shading
    retainedFactor := retainedFactor
    retained := retained
    retained_factor_pos := retainedPos
    retained_factor_ne_top := retainedTop
    cover := stateCover
  }, rfl, ?_⟩
  exact shadingUnion

/-- Re-enter the exact state of a lifted point cover on its fixed current
family.  The construction deliberately forgets how the point cover was
produced: after the preceding step has restored extremality, the next
Proposition 6.2 call needs only the root ordinary provenance, the actual
subshading, and the next one-scale scalar receipts. -/
theorem Proposition63LiftedPointCoverData.nextCurrentShadingReentry
    {delta sigma inputLoss normalizationLoss firstLoss queryScale
      spatialRadius densityLoss reentryLoss reentryNormalizationLoss
      weightLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
      densityLoss)
    {current : WZ1PaperTubeShading root.normalization.croppedFamily}
    {planeMap : Point3 → Point3} {constant : ENNReal}
    (first : Proposition63LiftedPointCoverData
      (outputLoss := firstLoss) (queryScale := queryScale)
      (spatialRadius := spatialRadius) root.normalization current planeMap
      constant)
    (hfirstSub : PaperIsSubshading first.state.shading
      root.normalization.croppedRefined)
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := root.normalization.croppedFamily)
      (Kakeya.realRpowENN delta (-normalizationLoss))
      (Kakeya.realRpowENN delta (-reentryLoss))
      (proposition63CanonicalNearbyLevelCount normalizationLoss))
    (ambient_two : (2 : ENNReal) <
      Kakeya.realRpowENN delta (-normalizationLoss))
    (hfirstReentry : firstLoss ≤ reentryLoss)
    (hfirstLoss : 0 < firstLoss)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2)
    (canonical_weight_absorb :
      proposition63CanonicalReentryWeight delta weightLoss ≤
        (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta (firstLoss + 2))
    (trace_fixed_absorb :
      (96 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta (reentryLoss - weightLoss) ≤ 1)
    (paper_fixed_absorb :
      ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta (reentryLoss - weightLoss) ≤
        (73 / 100 : ENNReal))
    (regularization_absorb :
      let degreeConstant :=
        16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * root.normalization.croppedFamily.card) + 1 :
            ENNReal) ^ schedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * root.normalization.croppedFamily.card) + 1 :
            ENNReal) ^ (schedule.scaleCount + 1)
      max degreeConstant
          (((proposition63CanonicalReentryWeight delta weightLoss)⁻¹ *
              (Kakeya.realRpowENN delta (-normalizationLoss) *
                (regularizationLoss *
                  ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
                    Kakeya.realRpowENN delta 2)) *
                degreeConstant)) *
            Kakeya.realRpowENN delta (-normalizationLoss)) ≤
        Kakeya.realRpowENN delta (-reentryLoss))
    (hdeltaSmall : delta ≤ 1 / 24) :
    ∃ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) root.normalization first.state.shading,
      reentry.normalizationWeight =
          proposition63CanonicalReentryWeight delta weightLoss ∧
        reentry.weightUpper =
          (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2 ∧
        reentry.levelCount =
          proposition63CanonicalNearbyLevelCount normalizationLoss ∧
        reentry.reentryNormalizationLoss = reentryNormalizationLoss := by
  exact root.currentShadingReentryFromExtremal first.state.shading schedule
    ambient_two first.state.extremal hfirstReentry hfirstLoss
    reentryNormalizationLoss hreentryNormalizationLoss hreentryHalf
    canonical_weight_absorb trace_fixed_absorb paper_fixed_absorb
    regularization_absorb hfirstSub first.state.extremal.cubical hdeltaSmall

/-- Re-enter a restored first point cover and immediately execute the
preselected third rich call at the square-root scale.  This is the exact
middle edge between the two robust localizations: neither the outer rich
call nor an ancestry embedding is part of the interface. -/
theorem Proposition63LiftedPointCoverData.nextReentryAndThirdRich
    {delta sigma inputLoss normalizationLoss firstLoss queryScale
      spatialRadius densityLoss reentryLoss reentryNormalizationLoss
      weightLoss sqrtStickyLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
      densityLoss)
    {current : WZ1PaperTubeShading root.normalization.croppedFamily}
    {planeMap : Point3 → Point3} {constant : ENNReal}
    (first : Proposition63LiftedPointCoverData
      (outputLoss := firstLoss) (queryScale := queryScale)
      (spatialRadius := spatialRadius) root.normalization current planeMap
      constant)
    (hfirstSub : PaperIsSubshading first.state.shading
      root.normalization.croppedRefined)
    (nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := root.normalization.croppedFamily)
      (Kakeya.realRpowENN delta (-normalizationLoss))
      (Kakeya.realRpowENN delta (-reentryLoss))
      (proposition63CanonicalNearbyLevelCount normalizationLoss))
    (ambient_two : (2 : ENNReal) <
      Kakeya.realRpowENN delta (-normalizationLoss))
    (hfirstReentry : firstLoss ≤ reentryLoss)
    (hfirstLoss : 0 < firstLoss)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2)
    (canonical_weight_absorb :
      proposition63CanonicalReentryWeight delta weightLoss ≤
        (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta (firstLoss + 2))
    (trace_fixed_absorb :
      (96 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta (reentryLoss - weightLoss) ≤ 1)
    (paper_fixed_absorb :
      ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta (reentryLoss - weightLoss) ≤
        (73 / 100 : ENNReal))
    (regularization_absorb :
      let degreeConstant :=
        16 * (nearbySchedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * root.normalization.croppedFamily.card) + 1 :
            ENNReal) ^ nearbySchedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * root.normalization.croppedFamily.card) + 1 :
            ENNReal) ^ (nearbySchedule.scaleCount + 1)
      max degreeConstant
          (((proposition63CanonicalReentryWeight delta weightLoss)⁻¹ *
              (Kakeya.realRpowENN delta (-normalizationLoss) *
                (regularizationLoss *
                  ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
                    Kakeya.realRpowENN delta 2)) *
                degreeConstant)) *
            Kakeya.realRpowENN delta (-normalizationLoss)) ≤
        Kakeya.realRpowENN delta (-reentryLoss))
    (hdeltaSmall : delta ≤ 1 / 24)
    (richSchedule : Proposition63RichThreeCallScheduleData
      sigma sqrtStickyLoss)
    (hreentryLoss : reentryLoss = richSchedule.third.sourceLoss)
    (hthirdNormalization :
      reentryNormalizationLoss = richSchedule.third.normalizationLoss)
    (hdeltaThird : delta ≤ richSchedule.third.delta₀)
    (sqrtRequested : WZ2PaperRequestedScale delta)
    (hsqrtLower : Real.rpow delta (1 - sqrtStickyLoss) ≤ sqrtRequested.1)
    (hsqrtUpper : sqrtRequested.1 ≤
      Real.rpow delta sqrtStickyLoss) :
    ∃ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) root.normalization first.state.shading,
      Nonempty (Proposition63RichTerminalStickyData
        (sigma := sigma) (outputLoss := sqrtStickyLoss)
        reentry.normalization.croppedRefined
        (reentry.normalization.toPropStickyReentryData
          (by rw [hreentryLoss]; exact richSchedule.third.sourceLoss_pos)
          reentry.reentry_normalization_loss_pos) sqrtRequested) ∧
      reentry.normalizationWeight =
          proposition63CanonicalReentryWeight delta weightLoss ∧
      reentry.weightUpper =
          (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2 ∧
      reentry.levelCount =
          proposition63CanonicalNearbyLevelCount normalizationLoss ∧
      reentry.reentryNormalizationLoss = reentryNormalizationLoss := by
  rcases first.nextCurrentShadingReentry root hfirstSub nearbySchedule
      ambient_two hfirstReentry hfirstLoss hreentryNormalizationLoss
      hreentryHalf canonical_weight_absorb trace_fixed_absorb
      paper_fixed_absorb regularization_absorb hdeltaSmall with
    ⟨reentry, hweight, hweightUpper, hlevel, hnormalization⟩
  have hthirdRaw := proposition63CurrentShadingReentry_richTerminalSticky
    (initialSource := source)
    (normalizationExponent := normalizationExponent)
    (initialNormalized := root.normalization)
    (current := first.state.shading) reentry richSchedule.third hreentryLoss
      (hnormalization.trans hthirdNormalization) hdeltaThird sqrtRequested
      hsqrtLower hsqrtUpper
  have hthird : Nonempty (Proposition63RichTerminalStickyData
      (sigma := sigma) (outputLoss := sqrtStickyLoss)
      reentry.normalization.croppedRefined
      (reentry.normalization.toPropStickyReentryData
        (by rw [hreentryLoss]; exact richSchedule.third.sourceLoss_pos)
        reentry.reentry_normalization_loss_pos) sqrtRequested) := by
    simpa only using hthirdRaw
  exact ⟨reentry, hthird, hweight, hweightUpper, hlevel, hnormalization⟩

/-- The first lifted point cover together with the exact current-shading
re-entry and outer-coarse ancestry consumed by the third Node-3 call. -/
structure Proposition63LiftedPointCoverReentryData
    {fineDelta sigma outerLoss queryInputLoss queryNormalizationLoss firstLoss
      tauScale reentryLoss reentryNormalizationLoss weightLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily fineDelta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale fineDelta}
    {outerLogExponent queryNormalizationExponent : ℕ}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent)
    {querySource : PureWZ2ExtremalConfiguration
      sigma queryInputLoss rho.1}
    (queryNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := queryNormalizationLoss) querySource
      queryNormalizationExponent)
    (current : WZ1PaperTubeShading queryNormalized.croppedFamily)
    (planeMap : Point3 → Point3) (tauConstant : ENNReal)
    (first : Proposition63LiftedPointCoverData
      (outputLoss := firstLoss) (queryScale := rho.1)
      (spatialRadius := tauScale) queryNormalized current planeMap tauConstant)
    (ancestorEmbedding :
      Fin queryNormalized.croppedFamily.card ↪ Fin outer.coarse.card) where
  reentry : Proposition63CurrentShadingReentryData
    (reentryLoss := reentryLoss) queryNormalized first.state.shading
  current_sub_outer : ∀ index, first.state.shading.carrier index ⊆
    outer.croppedCoarseShading.carrier (ancestorEmbedding index)
  ancestorRetentionFactor : ENNReal
  ancestor_retention_factor_pos : 0 < ancestorRetentionFactor
  ancestor_retention_factor_ne_top : ancestorRetentionFactor ≠ ⊤
  current_retained_mass :
    ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
      first.state.shading.mass
  normalization_weight_eq : reentry.normalizationWeight =
    proposition63CanonicalReentryWeight rho.1 weightLoss
  weight_upper_eq : reentry.weightUpper =
    (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
      Kakeya.realRpowENN rho.1 2
  level_count_eq : reentry.levelCount =
    proposition63CanonicalNearbyLevelCount queryNormalizationLoss
  reentry_normalization_loss_eq :
    reentry.reentryNormalizationLoss = reentryNormalizationLoss

/-- Re-enter the exact shading returned by the first lifted point cover.
The new ancestry factor is composed from the old outer ancestry and the
first cover's own retained factor, while the re-entry itself is built from
the restored extremality of that first cover. -/
theorem Proposition63LiftedPointCoverData.nextReentry
    {fineDelta sigma outerLoss queryInputLoss queryNormalizationLoss
      firstLoss tauScale reentryLoss
      reentryNormalizationLoss rootDensityLoss weightLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily fineDelta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale fineDelta}
    {outerLogExponent queryNormalizationExponent : ℕ}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent)
    {querySource : PureWZ2ExtremalConfiguration
      sigma queryInputLoss rho.1}
    (queryNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := queryNormalizationLoss) querySource
      queryNormalizationExponent)
    (current : WZ1PaperTubeShading queryNormalized.croppedFamily)
    (planeMap : Point3 → Point3) (tauConstant : ENNReal)
    (first : Proposition63LiftedPointCoverData
      (outputLoss := firstLoss) (queryScale := rho.1)
      (spatialRadius := tauScale) queryNormalized current planeMap tauConstant)
    (hfirstSub : PaperIsSubshading first.state.shading
      queryNormalized.croppedRefined)
    (ancestorEmbedding :
      Fin queryNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      queryNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index))
    (current_sub_outer : ∀ index, current.carrier index ⊆
      outer.croppedCoarseShading.carrier (ancestorEmbedding index))
    (ancestorRetentionFactor : ENNReal)
    (ancestorRetentionFactor_pos : 0 < ancestorRetentionFactor)
    (ancestorRetentionFactor_ne_top : ancestorRetentionFactor ≠ ⊤)
    (current_retained_mass :
      ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
        current.mass)
    (density_absorb :
      Kakeya.realRpowENN rho.1 rootDensityLoss ≤
        Kakeya.realRpowENN rho.1 queryInputLoss / 2)
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := queryNormalized.croppedFamily)
      (Kakeya.realRpowENN rho.1 (-queryNormalizationLoss))
      (Kakeya.realRpowENN rho.1 (-reentryLoss))
      (proposition63CanonicalNearbyLevelCount queryNormalizationLoss))
    (ambient_two : (2 : ENNReal) <
      Kakeya.realRpowENN rho.1 (-queryNormalizationLoss))
    (hfirstReentry : firstLoss ≤ reentryLoss)
    (hfirstLoss : 0 < firstLoss)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2)
    (canonical_weight_absorb :
      proposition63CanonicalReentryWeight rho.1 weightLoss ≤
        (100 : ENNReal)⁻¹ * Kakeya.realRpowENN rho.1 rootDensityLoss *
          Kakeya.realRpowENN rho.1 (firstLoss + 2))
    (trace_fixed_absorb :
      (96 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN rho.1 (reentryLoss - weightLoss) ≤ 1)
    (paper_fixed_absorb :
      ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN rho.1 (reentryLoss - weightLoss) ≤
        (73 / 100 : ENNReal))
    (regularization_absorb :
      let degreeConstant :=
        16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * queryNormalized.croppedFamily.card) + 1 :
            ENNReal) ^ schedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * queryNormalized.croppedFamily.card) + 1 :
            ENNReal) ^ (schedule.scaleCount + 1)
      max degreeConstant
          (((proposition63CanonicalReentryWeight rho.1 weightLoss)⁻¹ *
              (Kakeya.realRpowENN rho.1 (-queryNormalizationLoss) *
                (regularizationLoss *
                  ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
                    Kakeya.realRpowENN rho.1 2)) *
                degreeConstant)) *
            Kakeya.realRpowENN rho.1 (-queryNormalizationLoss)) ≤
        Kakeya.realRpowENN rho.1 (-reentryLoss))
    (hrhoSmall : rho.1 ≤ 1 / 24) :
    Nonempty (Proposition63LiftedPointCoverReentryData outer
      queryNormalized current planeMap tauConstant first ancestorEmbedding
      (reentryLoss := reentryLoss)
      (reentryNormalizationLoss := reentryNormalizationLoss)
      (weightLoss := weightLoss)) := by
  let root : Proposition63RootNormalizationData
      (outputLoss := queryNormalizationLoss) querySource
      queryNormalizationExponent rootDensityLoss :=
    Proposition63RootNormalizationData.ofNormalization queryNormalized
      density_absorb
  rcases root.currentShadingReentryFromExtremal first.state.shading schedule
      ambient_two first.state.extremal hfirstReentry hfirstLoss
      reentryNormalizationLoss hreentryNormalizationLoss hreentryHalf
      canonical_weight_absorb trace_fixed_absorb paper_fixed_absorb
      regularization_absorb hfirstSub first.state.extremal.cubical hrhoSmall with
    ⟨reentry, hweight, hweightUpper, hlevel, hnormalization⟩
  rcases first.composeAncestorRetention ancestorRetentionFactor
      ancestorRetentionFactor_pos ancestorRetentionFactor_ne_top
      current_retained_mass with
    ⟨nextAncestorFactor, hnextPos, hnextTop, hnextRetained⟩
  refine ⟨{
    reentry := reentry
    current_sub_outer := ?_
    ancestorRetentionFactor := nextAncestorFactor
    ancestor_retention_factor_pos := hnextPos
    ancestor_retention_factor_ne_top := hnextTop
    current_retained_mass := hnextRetained
    normalization_weight_eq := hweight
    weight_upper_eq := hweightUpper
    level_count_eq := hlevel
    reentry_normalization_loss_eq := hnormalization
  }⟩
  intro index point hpoint
  exact current_sub_outer index (first.state.subshading index hpoint)

/-- Lift a point-centered covering output from a freshly normalized
current-shading subfamily back to the fixed ambient family.  The displayed
left/right factors are the complete one-step mass ledger; the caller pays
their loss immediately before using the result as the next iterator state. -/
theorem Proposition63CurrentShadingReentryData.liftPointCover
    {delta sigma inputLoss normalizationLoss reentryLoss
      outputLoss queryScale spatialRadius : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (candidate : WZ1PaperTubeShading data.normalization.croppedFamily)
    (hcandidateSub : PaperIsSubshading candidate
      data.normalization.croppedRefined)
    (hcandidateCubical : WZ1PaperIsCubicalShading candidate)
    (planeMap : Point3 → Point3)
    (constant stateLeft stateRight : ENNReal)
    (hcover : PureWZ2PointCenteredCoveringAt candidate planeMap
      (Real.toNNReal queryScale) spatialRadius constant)
    (hstateMass : stateLeft * data.normalization.croppedRefined.mass ≤
      stateRight * candidate.mass)
    (hstateLeftPos : 0 < stateLeft) (hstateLeftTop : stateLeft ≠ ⊤)
    (hstateRightTop : stateRight ≠ ⊤)
    (hcurrentCWA : WZ2PaperConvexWolffBound
      initialNormalized.croppedFamily
      (Kakeya.realRpowENN delta (-reentryLoss)))
    (hreentryOutput : reentryLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss
        (stateLeft *
          ((73 / 100 : ENNReal) * data.normalizationWeight))
        (data.regularized.regularizationLoss * stateRight) *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta reentryLoss) :
    ∃ next : Proposition63ExtremalShadingData
        (sigma := sigma) (outputLoss := outputLoss) current,
      (∀ point ∈ next.shading.union,
        next.shading.pointMultiplicity point = current.pointMultiplicity point) ∧
      (stateLeft *
          ((73 / 100 : ENNReal) * data.normalizationWeight)) * current.mass ≤
        (data.regularized.regularizationLoss * stateRight) *
          next.shading.mass ∧
      PureWZ2PointCenteredCoveringAt next.shading planeMap
        (Real.toNNReal queryScale) spatialRadius constant ∧
      next.shading.union = candidate.union := by
  let ambient := data.extendCandidate candidate
  have hambientSub : PaperIsSubshading ambient current :=
    data.extendCandidate_subshading hcandidateSub
  let nextShading := paperCommonSpatialHull current ambient
  have hnextSub : PaperIsSubshading nextShading current :=
    paperCommonSpatialHull_subshading _ _
  have hnextCubical : WZ1PaperIsCubicalShading nextShading :=
    paperCommonSpatialHull_cubical data.current_cubical
      (extendShading_cubical data.regularized.selected hcandidateCubical)
  have hnextUnion : nextShading.union = candidate.union := by
    calc
      nextShading.union = ambient.union :=
        paperCommonSpatialHull_union hambientSub
      _ = candidate.union := data.extendCandidate_union _
  have hambientMass : ambient.mass = candidate.mass := by
    change (data.extendCandidate candidate).mass = candidate.mass
    exact data.extendCandidate_mass candidate
  have hmass :
      (stateLeft *
          ((73 / 100 : ENNReal) * data.normalizationWeight)) * current.mass ≤
        (data.regularized.regularizationLoss * stateRight) *
          nextShading.mass := by
    calc
      (stateLeft *
            ((73 / 100 : ENNReal) * data.normalizationWeight)) * current.mass =
          stateLeft *
            (((73 / 100 : ENNReal) * data.normalizationWeight) *
              current.mass) := by ring
      _ ≤ stateLeft *
          (data.regularized.regularizationLoss *
            data.normalization.croppedRefined.mass) :=
        mul_le_mul_left' data.reentryMassRetention _
      _ = data.regularized.regularizationLoss *
          (stateLeft * data.normalization.croppedRefined.mass) := by ring
      _ ≤ data.regularized.regularizationLoss *
          (stateRight * candidate.mass) :=
        mul_le_mul_left' hstateMass _
      _ = (data.regularized.regularizationLoss * stateRight) *
          candidate.mass := by ring
      _ = (data.regularized.regularizationLoss * stateRight) *
          ambient.mass := by
        rw [hambientMass]
      _ ≤ (data.regularized.regularizationLoss * stateRight) *
          nextShading.mass :=
        mul_le_mul_left' (paperCommonSpatialHull_mass_lower hambientSub) _
  have hleftPos : 0 < stateLeft *
      ((73 / 100 : ENNReal) * data.normalizationWeight) :=
    ENNReal.mul_pos hstateLeftPos.ne' <|
      ENNReal.mul_pos (by norm_num : (73 / 100 : ENNReal) ≠ 0)
        data.normalization_weight_ne_zero |>.ne'
  have hleftTop : stateLeft *
      ((73 / 100 : ENNReal) * data.normalizationWeight) ≠ ⊤ :=
    ENNReal.mul_ne_top hstateLeftTop <|
      ENNReal.mul_ne_top (ENNReal.div_ne_top (by norm_num) (by norm_num))
        data.normalization_weight_ne_top
  have hregularizationTop :
      data.regularized.regularizationLoss ≠ ⊤ := by
    rw [data.regularized.regularizationLoss_eq]
    exact ENNReal.mul_ne_top (by norm_num) (by simp)
  have hrightTop :
      data.regularized.regularizationLoss * stateRight ≠ ⊤ :=
    ENNReal.mul_ne_top hregularizationTop hstateRightTop
  let massLoss := proposition63Lemma43MassLoss
    (stateLeft * ((73 / 100 : ENNReal) * data.normalizationWeight))
    (data.regularized.regularizationLoss * stateRight)
  have hmassInv : massLoss⁻¹ * current.mass ≤ nextShading.mass :=
    proposition63Lemma43MassLoss_inv_mul_le
      hleftPos hleftTop hrightTop hmass
  have hnextExtremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      initialNormalized.croppedFamily nextShading := by
    apply transfer_cropped_extremal_to_subshading massLoss
      (proposition63Lemma43MassLoss_pos _ _)
      (proposition63Lemma43MassLoss_ne_top hleftPos hrightTop)
      data.reentry_extremal hnextSub hmassInv hnextCubical hreentryOutput
    · simpa only [massLoss] using hrestore
    · exact data.reentry_extremal.delta_pos
    · exact data.reentry_extremal.delta_le_one
    · exact houtputLoss
  have hnextCWA : WZ2PaperConvexWolffBound
      initialNormalized.croppedFamily
      (Kakeya.realRpowENN delta (-outputLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := current) (_shading2 := nextShading)
      hcurrentCWA hreentryOutput
      data.reentry_extremal.delta_pos data.reentry_extremal.delta_le_one
  let next : Proposition63ExtremalShadingData
      (sigma := sigma) (outputLoss := outputLoss) current :=
    { shading := nextShading
      subshading := hnextSub
      extremal := hnextExtremal
      cwa := hnextCWA }
  refine ⟨next, ?_, ?_, ?_, hnextUnion⟩
  · exact paperCommonSpatialHull_pointMultiplicity_eq current ambient
  · exact hmass
  · intro point
    have hpointState : (point : Point3) ∈ candidate.union := by
      rw [← hnextUnion]
      exact point.property
    have hpointCover := hcover ⟨point, hpointState⟩
    simpa only [next, hnextUnion] using hpointCover

/-- Execute a dependent HIGH point-cover certificate and immediately lift it
back through the current-shading re-entry.  Both analytic loss factors remain
visible; division by the positive finite regularization loss merely converts
the two-sided ledger into the one-sided form used by the nested producer. -/
theorem Proposition63CurrentShadingReentryData.liftHighPointCover
    {fineDelta sigma outerLoss queryInputLoss queryNormalizationLoss
      currentReentryLoss innerLoss targetLoss outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily fineDelta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale fineDelta}
    {outerLogExponent queryNormalizationExponent
      innerLogExponent : ℕ}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent)
    {querySource : PureWZ2ExtremalConfiguration
      sigma queryInputLoss rho.1}
    (queryNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := queryNormalizationLoss) querySource
      queryNormalizationExponent)
    (current : WZ1PaperTubeShading queryNormalized.croppedFamily)
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := currentReentryLoss) queryNormalized current)
    (ancestorEmbedding :
      Fin queryNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      queryNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index))
    (current_sub_outer : ∀ index, current.carrier index ⊆
      outer.croppedCoarseShading.carrier (ancestorEmbedding index))
    (ancestorRetentionFactor : ENNReal)
    (ancestorRetentionFactor_pos : 0 < ancestorRetentionFactor)
    (ancestorRetentionFactor_ne_top : ancestorRetentionFactor ≠ ⊤)
    (current_retained_mass :
      ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
        current.mass)
    {tau : WZ2PaperRequestedScale rho.1}
    {dependent : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      (proposition63DependentCoarseReentryOfCurrent outer queryNormalized
        current data ancestorEmbedding ancestor_tube_eq current_sub_outer
        ancestorRetentionFactor ancestorRetentionFactor_pos
        ancestorRetentionFactor_ne_top current_retained_mass) tau}
    {planeMap : Point3 → Point3} {coefficient : NNReal}
    (input : Proposition63DependentHighPointCoverInput
      (targetLoss := targetLoss) dependent planeMap coefficient)
    (hcurrentCWA : WZ2PaperConvexWolffBound
      queryNormalized.croppedFamily
      (Kakeya.realRpowENN rho.1 (-currentReentryLoss)))
    (hreentryOutput : currentReentryLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss
        ((proposition63DependentPropertyThreeMassLoss
            rho.1 innerLogExponent)⁻¹ *
          ((73 / 100 : ENNReal) * data.normalizationWeight))
        data.regularized.regularizationLoss *
          Kakeya.realRpowENN rho.1 outputLoss ≤
        Kakeya.realRpowENN rho.1 currentReentryLoss) :
    Nonempty (Proposition63LiftedPointCoverData
      (outputLoss := outputLoss) (queryScale := rho.1)
      (spatialRadius := tau.1) queryNormalized current planeMap
      (input.C *
        Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma))) := by
  rcases input.run with ⟨state, _hstate, _hmultiplicity, hstateMass, hcover⟩
  let stateLeft :=
    (proposition63DependentPropertyThreeMassLoss
      rho.1 innerLogExponent)⁻¹
  have hstateLeftPos : 0 < stateLeft := by
    dsimp only [stateLeft]
    exact ENNReal.inv_pos.mpr <|
      (proposition63DependentPropertyThreeMassLoss_pos_ne_top
        data.reentry_extremal.delta_pos
        input.rho_lt_one innerLogExponent).2
  have hstateLeftTop : stateLeft ≠ ⊤ := by
    dsimp only [stateLeft]
    exact ENNReal.inv_ne_top.mpr <|
      (proposition63DependentPropertyThreeMassLoss_pos_ne_top
        data.reentry_extremal.delta_pos
        input.rho_lt_one innerLogExponent).1.ne'
  rcases data.liftPointCover state.shading state.subshading
      state.extremal.cubical planeMap
      (input.C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma))
      stateLeft 1
      hcover
      (by
        change stateLeft * data.normalization.croppedRefined.mass ≤
          state.shading.mass at hstateMass
        simpa only [proposition63DependentCoarseReentryOfCurrent, one_mul]
          using hstateMass)
      hstateLeftPos hstateLeftTop (by norm_num) hcurrentCWA hreentryOutput
      houtputLoss
      (hrestore := by simpa only [stateLeft, mul_one] using hrestore) with
    ⟨next, hmultiplicity, hmass, hnextCover, _hnextUnion⟩
  have hregularizationPos : 0 < data.regularized.regularizationLoss := by
    rw [data.regularized.regularizationLoss_eq]
    positivity
  have hregularizationTop : data.regularized.regularizationLoss ≠ ⊤ := by
    rw [data.regularized.regularizationLoss_eq]
    exact ENNReal.mul_ne_top (by norm_num) (by simp)
  let retainedFactor : ENNReal :=
    (stateLeft * ((73 / 100 : ENNReal) * data.normalizationWeight)) /
      data.regularized.regularizationLoss
  have hretained : retainedFactor * current.mass ≤ next.shading.mass := by
    have hdiv :
        (stateLeft * ((73 / 100 : ENNReal) * data.normalizationWeight) *
            current.mass) / data.regularized.regularizationLoss ≤
          next.shading.mass := by
      apply (ENNReal.div_le_iff hregularizationPos.ne'
        hregularizationTop).2
      simpa [mul_assoc, mul_comm, mul_left_comm] using hmass
    simpa only [retainedFactor, div_eq_mul_inv, mul_assoc, mul_comm,
      mul_left_comm] using hdiv
  have hretainedPos : 0 < retainedFactor := by
    dsimp only [retainedFactor]
    exact ENNReal.div_pos
      (ENNReal.mul_pos hstateLeftPos.ne'
        (ENNReal.mul_pos (by norm_num : (73 / 100 : ENNReal) ≠ 0)
          data.normalization_weight_ne_zero).ne').ne'
      hregularizationTop
  have hretainedTop : retainedFactor ≠ ⊤ := by
    dsimp only [retainedFactor]
    exact ENNReal.div_ne_top
      (ENNReal.mul_ne_top hstateLeftTop <|
        ENNReal.mul_ne_top
          (ENNReal.div_ne_top (by norm_num) (by norm_num))
          data.normalization_weight_ne_top) hregularizationPos.ne'
  exact ⟨{
    state := next
    multiplicity := hmultiplicity
    retainedFactor := retainedFactor
    retained := hretained
    retained_factor_pos := hretainedPos
    retained_factor_ne_top := hretainedTop
    cover := hnextCover
  }⟩

/-- Run the second preselected Node-3 kernel at an arbitrary legal `tau` and
keep its HIGH point-cover output on the actual normalized coarse family.
This is the intermediate state used by the paper before the square-root
call; it deliberately performs no lift and no premature extremality
restoration on the root family. -/
theorem Proposition63CurrentShadingReentryData.directSecondCWA
    {fineDelta sigma outerLoss queryInputLoss queryNormalizationLoss
      currentReentryLoss highTargetLoss densityLoss epsilon₁ epsilon₃ kappa
      finalStickyLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily fineDelta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale fineDelta}
    {outerLogExponent queryNormalizationExponent : ℕ}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent)
    {querySource : PureWZ2ExtremalConfiguration
      sigma queryInputLoss rho.1}
    (queryNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := queryNormalizationLoss) querySource
      queryNormalizationExponent)
    (current : WZ1PaperTubeShading queryNormalized.croppedFamily)
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := currentReentryLoss) queryNormalized current)
    (ancestorEmbedding :
      Fin queryNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      queryNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index))
    (current_sub_outer : ∀ index, current.carrier index ⊆
      outer.croppedCoarseShading.carrier (ancestorEmbedding index))
    (ancestorRetentionFactor : ENNReal)
    (ancestorRetentionFactor_pos : 0 < ancestorRetentionFactor)
    (ancestorRetentionFactor_ne_top : ancestorRetentionFactor ≠ ⊤)
    (current_retained_mass :
      ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
        current.mass)
    (schedule : Proposition63RichThreeCallScheduleData sigma finalStickyLoss)
    (hreentryLoss : currentReentryLoss = schedule.second.sourceLoss)
    (hnormalizationLoss :
      data.reentryNormalizationLoss = schedule.second.normalizationLoss)
    (hrhoSchedule : rho.1 ≤ schedule.second.delta₀)
    (tau : WZ2PaperRequestedScale rho.1)
    (htauLower : Real.rpow rho.1 (1 - schedule.secondOutputLoss) ≤ tau.1)
    (htauUpper : tau.1 ≤ Real.rpow rho.1 schedule.secondOutputLoss)
    (planeMap : Point3 → Point3)
    (coefficient : NNReal)
    (incidenceBound : ℝ)
    (hplaneUnit : ∀ point ∈ current.union, ‖planeMap point‖ = 1)
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneIncidence : ∀ index point,
      point ∈ current.carrier index →
        |@Inner.inner ℝ Point3 _
          (queryNormalized.croppedFamily.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (hreentryTarget : data.reentryNormalizationLoss ≤ highTargetLoss)
    (hretention : Kakeya.realRpowENN rho.1 highTargetLoss ≤
      wz2PaperPureRefinementFraction rho.1 61 *
        Kakeya.realRpowENN rho.1 data.reentryNormalizationLoss)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * highTargetLoss)
    (hhighTargetLoss : 0 < highTargetLoss)
    (hsmall : Kakeya.realRpowENN rho.1 highTargetLoss < 1 / 4)
    (hrhoSmall24 : rho.1 ≤ 1 / 24)
    (hrhoSmall10000 : rho.1 ≤ 1 / 10000)
    (hpackingAbsorb :
      (12 * ((2 * 4 * 601 ^ 3 * 12001 ^ 3 + 1 : ℕ) : ENNReal)) *
          ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN rho.1 (-sigma + 4 * highTargetLoss))
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (htau : 0 < tau.1) (hrhoTau : rho.1 ≤ tau.1)
    (htauLarge : rho.1 * Real.sqrt 3 ≤ tau.1)
    (htauSq : tau.1 ^ 2 ≤ 4 * rho.1) (htauOne : tau.1 ≤ 1)
    (hcell : Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
        ENNReal.ofReal tau.1 ≤ Kakeya.realRpowENN rho.1 3)
    (hkappa : 0 < kappa) (hkappaOne : kappa ≤ 1)
    (hkappaRho : rho.1 ≤ kappa)
    (hkappaProperty : Real.rpow rho.1 epsilon₃ ≤ kappa)
    (hcloseAbsorb :
      Kakeya.realRpowENN rho.1 (-highTargetLoss) *
          ENNReal.ofReal (10000 * kappa ^ 2) <
        Kakeya.realRpowENN rho.1 densityLoss)
    (hrhoOne : rho.1 < 1)
    (hmassSlack : proposition63DependentPropertyThreeMassLoss rho.1 61 *
        Kakeya.realRpowENN rho.1 highTargetLoss ≤
      Kakeya.realRpowENN rho.1 data.reentryNormalizationLoss)
    (htauSmall : tau.1 ≤ 1 / 12) (hrhoSmall : rho.1 ≤ 1 / 1000)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * rho.1) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          (((5832 * Real.rpow rho.1 (sigma - outerLoss) *
              Real.rpow tau.1
                (3 - sigma - 2 * schedule.secondOutputLoss)) /
              (Real.rpow rho.1 (1 + 7 * epsilon₁ + epsilon₃) *
                tau.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth rho.1 tau.1 incidenceBound
              coefficient / rho.1 + 2)) ≤
        C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)) :
    ∃ result : Proposition63LiftedPointCoverData
        (outputLoss := highTargetLoss) (queryScale := rho.1)
        (spatialRadius := tau.1) data.normalization
        data.normalization.croppedRefined planeMap
        (C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)),
      result.retainedFactor =
        (proposition63DependentPropertyThreeMassLoss rho.1 61)⁻¹ := by
  have hsourceLoss : 0 < currentReentryLoss := by
    rw [hreentryLoss]
    exact schedule.second.sourceLoss_pos
  have run := schedule.second.runPlain rho.1 data.reentry_extremal.delta_pos
    hrhoSchedule
  rw [← hreentryLoss, ← hnormalizationLoss] at run
  rcases run data.normalization.croppedFamily
      data.normalization.croppedRefined
      (data.normalization.toPropStickyReentryData hsourceLoss
        data.reentry_normalization_loss_pos)
      tau htauLower htauUpper with ⟨inner⟩
  let dependentReentry := proposition63DependentCoarseReentryOfCurrent outer
    queryNormalized current data ancestorEmbedding ancestor_tube_eq
    current_sub_outer ancestorRetentionFactor ancestorRetentionFactor_pos
    ancestorRetentionFactor_ne_top current_retained_mass
  let dependent : Proposition63DependentTwoLevelCoverData
      (innerLoss := schedule.secondOutputLoss) (innerLogExponent := 61)
      dependentReentry tau := { inner := inner }
  have hnormalizedUnit :
      ∀ point ∈ data.normalization.croppedRefined.union,
        ‖planeMap point‖ = 1 := by
    intro point hpoint
    rcases hpoint with ⟨index, hindex⟩
    exact hplaneUnit point ⟨data.regularized.selected.embedding index,
      data.denseSubshading index hindex⟩
  have hnormalizedIncidence : ∀ index point,
      point ∈ data.normalization.croppedRefined.carrier index →
        |@Inner.inner ℝ Point3 _
          (data.normalization.croppedFamily.tube index).direction
          (planeMap point)| ≤ incidenceBound := by
    intro index point hpoint
    have hambient := hplaneIncidence
      (data.regularized.selected.embedding index) point
      (data.denseSubshading index hpoint)
    change |@Inner.inner ℝ Point3 _
      (data.regularized.selected.family.tube index).direction
      (planeMap point)| ≤ incidenceBound
    rw [data.regularized.selected.tube_eq index]
    exact hambient
  have hambientUnit : ∀ point ∈ dependent.ambientRefined.union,
      ‖planeMap point‖ = 1 := by
    intro point hpoint
    exact hnormalizedUnit point
      (paperSubshading_union dependent.ambientRefined_sub_normalized hpoint)
  have hambientIncidence : ∀ index point,
      point ∈ dependent.ambientRefined.carrier index →
        |@Inner.inner ℝ Point3 _
          (data.normalization.croppedFamily.tube index).direction
          (planeMap point)| ≤ incidenceBound := by
    intro index point hpoint
    exact hnormalizedIncidence index point
      (dependent.ambientRefined_sub_normalized index hpoint)
  have hfamilyCardPos : 0 < data.normalization.croppedFamily.enncard := by
    change (0 : ENNReal) <
      (data.normalization.croppedFamily.card : ENNReal)
    exact_mod_cast data.normalization.final_extremal.nonempty
  have hcloseAbsorbWithCard :
      Kakeya.realRpowENN rho.1 (-highTargetLoss) *
          ENNReal.ofReal (10000 * kappa ^ 2) *
          data.normalization.croppedFamily.enncard <
        Kakeya.realRpowENN rho.1 densityLoss *
          data.normalization.croppedFamily.enncard := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      ENNReal.mul_lt_mul_right hfamilyCardPos.ne' ENNReal.coe_ne_top
        hcloseAbsorb
  rcases Proposition63DependentHighPointCoverInput.of_cwa dependent
      planeMap coefficient incidenceBound hambientUnit hplaneLipschitz
      hambientIncidence hreentryTarget hretention hdensityLoss
      hhighTargetLoss hsmall hrhoSmall24 hrhoSmall10000 hpackingAbsorb
      hepsilon₁ hepsilon₃ hepsilonSum htau hrhoTau htauLarge htauSq
      htauOne hcell hkappa hkappaOne hkappaRho hkappaProperty
      hcloseAbsorbWithCard
      hrhoOne hmassSlack htauSmall hrhoSmall hsigma hsigmaOne logScale
      hrhoLog hlog haxis C harithmetic with ⟨input, hinputC⟩
  subst C
  have direct := input.directPointCover
  simpa only [dependentReentry, proposition63DependentCoarseReentryOfCurrent]
    using direct

/-- Backwards-compatible lifted form of `directSecondCWA`.  New nested-pair
code should stay on the direct normalized coarse family until the final
whole-cell pullback. -/
theorem Proposition63CurrentShadingReentryData.liftSecondCWA
    {fineDelta sigma outerLoss queryInputLoss queryNormalizationLoss
      currentReentryLoss highTargetLoss outputLoss densityLoss epsilon₁
      epsilon₃ kappa finalStickyLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily fineDelta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale fineDelta}
    {outerLogExponent queryNormalizationExponent : ℕ}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent)
    {querySource : PureWZ2ExtremalConfiguration
      sigma queryInputLoss rho.1}
    (queryNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := queryNormalizationLoss) querySource
      queryNormalizationExponent)
    (current : WZ1PaperTubeShading queryNormalized.croppedFamily)
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := currentReentryLoss) queryNormalized current)
    (ancestorEmbedding :
      Fin queryNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      queryNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index))
    (current_sub_outer : ∀ index, current.carrier index ⊆
      outer.croppedCoarseShading.carrier (ancestorEmbedding index))
    (ancestorRetentionFactor : ENNReal)
    (ancestorRetentionFactor_pos : 0 < ancestorRetentionFactor)
    (ancestorRetentionFactor_ne_top : ancestorRetentionFactor ≠ ⊤)
    (current_retained_mass :
      ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
        current.mass)
    (schedule : Proposition63RichThreeCallScheduleData sigma finalStickyLoss)
    (hreentryLoss : currentReentryLoss = schedule.second.sourceLoss)
    (hnormalizationLoss :
      data.reentryNormalizationLoss = schedule.second.normalizationLoss)
    (hrhoSchedule : rho.1 ≤ schedule.second.delta₀)
    (tau : WZ2PaperRequestedScale rho.1)
    (htauLower : Real.rpow rho.1 (1 - schedule.secondOutputLoss) ≤ tau.1)
    (htauUpper : tau.1 ≤ Real.rpow rho.1 schedule.secondOutputLoss)
    (planeMap : Point3 → Point3)
    (coefficient : NNReal)
    (incidenceBound : ℝ)
    (hplaneUnit : ∀ point ∈ current.union,
      ‖planeMap point‖ = 1)
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneIncidence : ∀ index point,
      point ∈ current.carrier index →
        |@Inner.inner ℝ Point3 _
          (queryNormalized.croppedFamily.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (hreentryTarget : data.reentryNormalizationLoss ≤ highTargetLoss)
    (hretention : Kakeya.realRpowENN rho.1 highTargetLoss ≤
      wz2PaperPureRefinementFraction rho.1 61 *
        Kakeya.realRpowENN rho.1 data.reentryNormalizationLoss)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * highTargetLoss)
    (hhighTargetLoss : 0 < highTargetLoss)
    (hsmall : Kakeya.realRpowENN rho.1 highTargetLoss < 1 / 4)
    (hrhoSmall24 : rho.1 ≤ 1 / 24)
    (hrhoSmall10000 : rho.1 ≤ 1 / 10000)
    (hpackingAbsorb :
      (12 * ((2 * 4 * 601 ^ 3 * 12001 ^ 3 + 1 : ℕ) : ENNReal)) *
          ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN rho.1 (-sigma + 4 * highTargetLoss))
    (hepsilon₁ : 0 < epsilon₁)
    (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (htau : 0 < tau.1)
    (hrhoTau : rho.1 ≤ tau.1)
    (htauLarge : rho.1 * Real.sqrt 3 ≤ tau.1)
    (htauSq : tau.1 ^ 2 ≤ 4 * rho.1)
    (htauOne : tau.1 ≤ 1)
    (hcell :
      Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
          ENNReal.ofReal tau.1 ≤
        Kakeya.realRpowENN rho.1 3)
    (hkappa : 0 < kappa)
    (hkappaOne : kappa ≤ 1)
    (hkappaRho : rho.1 ≤ kappa)
    (hkappaProperty : Real.rpow rho.1 epsilon₃ ≤ kappa)
    (hcloseAbsorb :
      Kakeya.realRpowENN rho.1 (-highTargetLoss) *
          ENNReal.ofReal (10000 * kappa ^ 2) *
          data.normalization.croppedFamily.enncard <
        Kakeya.realRpowENN rho.1 densityLoss *
          data.normalization.croppedFamily.enncard)
    (hrhoOne : rho.1 < 1)
    (hmassSlack : proposition63DependentPropertyThreeMassLoss rho.1 61 *
        Kakeya.realRpowENN rho.1 highTargetLoss ≤
      Kakeya.realRpowENN rho.1 data.reentryNormalizationLoss)
    (htauSmall : tau.1 ≤ 1 / 12)
    (hrhoSmall : rho.1 ≤ 1 / 1000)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * rho.1) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          (((5832 * Real.rpow rho.1 (sigma - outerLoss) *
              Real.rpow tau.1
                (3 - sigma - 2 * schedule.secondOutputLoss)) /
              (Real.rpow rho.1 (1 + 7 * epsilon₁ + epsilon₃) *
                tau.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth rho.1 tau.1 incidenceBound
              coefficient / rho.1 + 2)) ≤
        C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma))
    (hcurrentCWA : WZ2PaperConvexWolffBound
      queryNormalized.croppedFamily
      (Kakeya.realRpowENN rho.1 (-currentReentryLoss)))
    (hreentryOutput : currentReentryLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss
        ((proposition63DependentPropertyThreeMassLoss rho.1 61)⁻¹ *
          ((73 / 100 : ENNReal) * data.normalizationWeight))
        data.regularized.regularizationLoss *
          Kakeya.realRpowENN rho.1 outputLoss ≤
        Kakeya.realRpowENN rho.1 currentReentryLoss) :
    Nonempty (Proposition63LiftedPointCoverData
      (outputLoss := outputLoss) (queryScale := rho.1)
      (spatialRadius := tau.1) queryNormalized current planeMap
      (C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma))) := by
  have hsourceLoss : 0 < currentReentryLoss := by
    rw [hreentryLoss]
    exact schedule.second.sourceLoss_pos
  have run := schedule.second.runPlain rho.1 data.reentry_extremal.delta_pos
    hrhoSchedule
  rw [← hreentryLoss, ← hnormalizationLoss] at run
  rcases run data.normalization.croppedFamily
      data.normalization.croppedRefined
      (data.normalization.toPropStickyReentryData hsourceLoss
        data.reentry_normalization_loss_pos)
      tau htauLower htauUpper with ⟨inner⟩
  let dependentReentry := proposition63DependentCoarseReentryOfCurrent outer
    queryNormalized current data ancestorEmbedding ancestor_tube_eq
    current_sub_outer ancestorRetentionFactor ancestorRetentionFactor_pos
    ancestorRetentionFactor_ne_top current_retained_mass
  let dependent : Proposition63DependentTwoLevelCoverData
      (innerLoss := schedule.secondOutputLoss) (innerLogExponent := 61)
      dependentReentry tau :=
    { inner := inner }
  have hnormalizedUnit :
      ∀ point ∈ data.normalization.croppedRefined.union,
        ‖planeMap point‖ = 1 := by
    intro point hpoint
    rcases hpoint with ⟨index, hindex⟩
    exact hplaneUnit point ⟨data.regularized.selected.embedding index,
      data.denseSubshading index hindex⟩
  have hnormalizedIncidence : ∀ index point,
      point ∈ data.normalization.croppedRefined.carrier index →
        |@Inner.inner ℝ Point3 _
          (data.normalization.croppedFamily.tube index).direction
          (planeMap point)| ≤ incidenceBound := by
    intro index point hpoint
    have hambient := hplaneIncidence
      (data.regularized.selected.embedding index) point
      (data.denseSubshading index hpoint)
    change |@Inner.inner ℝ Point3 _
      (data.regularized.selected.family.tube index).direction
      (planeMap point)| ≤ incidenceBound
    rw [data.regularized.selected.tube_eq index]
    exact hambient
  have hambientUnit : ∀ point ∈ dependent.ambientRefined.union,
      ‖planeMap point‖ = 1 := by
    intro point hpoint
    apply hnormalizedUnit point
    exact paperSubshading_union
      dependent.ambientRefined_sub_normalized hpoint
  have hambientIncidence : ∀ index point,
      point ∈ dependent.ambientRefined.carrier index →
        |@Inner.inner ℝ Point3 _
          (data.normalization.croppedFamily.tube index).direction
          (planeMap point)| ≤ incidenceBound := by
    intro index point hpoint
    exact hnormalizedIncidence index point
      (dependent.ambientRefined_sub_normalized index hpoint)
  rcases Proposition63DependentHighPointCoverInput.of_cwa dependent
      planeMap coefficient incidenceBound hambientUnit hplaneLipschitz
      hambientIncidence hreentryTarget hretention hdensityLoss
      hhighTargetLoss hsmall hrhoSmall24 hrhoSmall10000 hpackingAbsorb
      hepsilon₁ hepsilon₃ hepsilonSum htau hrhoTau htauLarge htauSq
      htauOne hcell hkappa hkappaOne hkappaRho hkappaProperty hcloseAbsorb
      hrhoOne hmassSlack htauSmall hrhoSmall hsigma hsigmaOne logScale
      hrhoLog hlog haxis C harithmetic with ⟨input, hinputC⟩
  have lifted := data.liftHighPointCover outer queryNormalized current
    ancestorEmbedding ancestor_tube_eq current_sub_outer
    ancestorRetentionFactor ancestorRetentionFactor_pos
    ancestorRetentionFactor_ne_top current_retained_mass input hcurrentCWA
    hreentryOutput houtputLoss hrestore
  simpa only [hinputC] using lifted

/-- Two dependent point-centered covering estimates on one nested chain.
The second estimate and the balanced square-root cells are attached to the
same final constant-multiplicity shading. -/
structure Proposition63NestedPointCoverData
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent)
    (planeMap : Point3 → Point3)
    (tauConstant sqrtConstant : ENNReal) where
  current : WZ1PaperTubeShading initialNormalized.croppedFamily
  first : Proposition63ExtremalShadingData
    (sigma := sigma) (outputLoss := firstLoss)
    current
  first_multiplicity : ∀ point ∈ first.shading.union,
    first.shading.pointMultiplicity point = current.pointMultiplicity point
  firstCover : PureWZ2PointCenteredCoveringAt first.shading planeMap
    (Real.toNNReal queryScale) tauScale tauConstant
  firstRetainedFactor : ENNReal
  first_retained : firstRetainedFactor *
      current.mass ≤ first.shading.mass
  first_retained_factor_pos : 0 < firstRetainedFactor
  first_retained_factor_ne_top : firstRetainedFactor ≠ ⊤
  reentry : Proposition63CurrentShadingReentryData
    (reentryLoss := reentryLoss) initialNormalized first.shading
  sqrtRequested : WZ2PaperRequestedScale delta
  sqrt_requested_eq : sqrtRequested.1 = sqrtScale
  sqrtSticky : PureWZ2PropStickyData
    (sigma := sigma) (outputLoss := sqrtStickyLoss)
    reentry.normalization.croppedRefined sqrtRequested 61
  second : Proposition63ExtremalShadingData
    (sigma := sigma) (outputLoss := secondLoss)
    reentry.normalization.croppedRefined
  secondCover : PureWZ2PointCenteredCoveringAt second.shading planeMap
    (Real.toNNReal queryScale) sqrtScale sqrtConstant
  second_union_subset_sqrt_sticky : second.shading.union ⊆
    (extendShading sqrtSticky.selected sqrtSticky.refined).union
  secondRetainedFactor : ENNReal
  second_retained : secondRetainedFactor *
      reentry.normalization.croppedRefined.mass ≤ second.shading.mass
  second_retained_factor_pos : 0 < secondRetainedFactor
  second_retained_factor_ne_top : secondRetainedFactor ≠ ⊤
  prepared : Proposition63ConstantMultiplicityShadingData
    (secondLoss := finalLoss) second
  cells : Proposition63BalancedCellData (scale := sqrtScale)
    prepared.refined.shading

/-- The two analytic point-cover outputs before multiplicity preparation and
fresh whole-cell balancing.  Keeping this package separate makes the
non-circular boundary explicit: it contains extremality, CWA, covering, and
mass data, but no one-scale AD conclusion. -/
structure Proposition63NestedPointCoverAnalyticData
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent)
    (planeMap : Point3 → Point3)
    (tauConstant sqrtConstant : ENNReal) where
  current : WZ1PaperTubeShading initialNormalized.croppedFamily
  first : Proposition63ExtremalShadingData
    (sigma := sigma) (outputLoss := firstLoss) current
  first_multiplicity : ∀ point ∈ first.shading.union,
    first.shading.pointMultiplicity point = current.pointMultiplicity point
  firstCover : PureWZ2PointCenteredCoveringAt first.shading planeMap
    (Real.toNNReal queryScale) tauScale tauConstant
  firstRetainedFactor : ENNReal
  first_retained : firstRetainedFactor * current.mass ≤ first.shading.mass
  first_retained_factor_pos : 0 < firstRetainedFactor
  first_retained_factor_ne_top : firstRetainedFactor ≠ ⊤
  reentry : Proposition63CurrentShadingReentryData
    (reentryLoss := reentryLoss) initialNormalized first.shading
  sqrtRequested : WZ2PaperRequestedScale delta
  sqrt_requested_eq : sqrtRequested.1 = sqrtScale
  sqrtSticky : PureWZ2PropStickyData
    (sigma := sigma) (outputLoss := sqrtStickyLoss)
    reentry.normalization.croppedRefined sqrtRequested 61
  second : Proposition63ExtremalShadingData
    (sigma := sigma) (outputLoss := secondLoss)
    reentry.normalization.croppedRefined
  secondCover : PureWZ2PointCenteredCoveringAt second.shading planeMap
    (Real.toNNReal queryScale) sqrtScale sqrtConstant
  second_union_subset_sqrt_sticky : second.shading.union ⊆
    (extendShading sqrtSticky.selected sqrtSticky.refined).union
  secondRetainedFactor : ENNReal
  second_retained : secondRetainedFactor *
      reentry.normalization.croppedRefined.mass ≤ second.shading.mass
  second_retained_factor_pos : 0 < secondRetainedFactor
  second_retained_factor_ne_top : secondRetainedFactor ≠ ⊤

namespace Proposition63NestedPointCoverAnalyticData

/-- Assemble the analytic two-cover state from two already-restored point
covers on the exact dependent family chain.  This constructor contains no
outer-family ancestry: the first cover is re-entered directly, and the second
cover already lives on that re-entry normalization. -/
theorem ofLiftedPointCovers
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent)
    (current : WZ1PaperTubeShading initialNormalized.croppedFamily)
    (planeMap : Point3 → Point3) (tauConstant sqrtConstant : ENNReal)
    (first : Proposition63LiftedPointCoverData
      (outputLoss := firstLoss) (queryScale := queryScale)
      (spatialRadius := tauScale) initialNormalized current planeMap
      tauConstant)
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized first.state.shading)
    (sqrtRequested : WZ2PaperRequestedScale delta)
    (hsqrtRequested : sqrtRequested.1 = sqrtScale)
    (sqrtSticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := sqrtStickyLoss)
      reentry.normalization.croppedRefined sqrtRequested 61)
    (second : Proposition63LiftedPointCoverData
      (outputLoss := secondLoss) (queryScale := queryScale)
      (spatialRadius := sqrtScale) reentry.normalization
      reentry.normalization.croppedRefined planeMap sqrtConstant)
    (hsecondSubset : second.state.shading.union ⊆
      (extendShading sqrtSticky.selected sqrtSticky.refined).union) :
    Nonempty (Proposition63NestedPointCoverAnalyticData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap tauConstant
      sqrtConstant) := by
  exact ⟨{
    current := current
    first := first.state
    first_multiplicity := first.multiplicity
    firstCover := first.cover
    firstRetainedFactor := first.retainedFactor
    first_retained := first.retained
    first_retained_factor_pos := first.retained_factor_pos
    first_retained_factor_ne_top := first.retained_factor_ne_top
    reentry := reentry
    sqrtRequested := sqrtRequested
    sqrt_requested_eq := hsqrtRequested
    sqrtSticky := sqrtSticky
    second := second.state
    secondCover := second.cover
    second_union_subset_sqrt_sticky := hsecondSubset
    secondRetainedFactor := second.retainedFactor
    second_retained := second.retained
    second_retained_factor_pos := second.retained_factor_pos
    second_retained_factor_ne_top := second.retained_factor_ne_top
  }⟩

/-- Attach the third, square-root-scale Node-3 call to an already lifted
arbitrary-radius point cover.  The same outer coarse ancestry is reused, so
the second HIGH call is genuinely nested inside the first output rather than
chosen on an unrelated family. -/
theorem ofLiftedFirstAndSqrtHigh
    {fineDelta sigma outerLoss queryInputLoss
      queryNormalizationLoss firstLoss reentryLoss sqrtStickyLoss secondLoss
      tauScale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily fineDelta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale fineDelta}
    {outerLogExponent queryNormalizationExponent : ℕ}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent)
    {querySource : PureWZ2ExtremalConfiguration
      sigma queryInputLoss rho.1}
    (queryNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := queryNormalizationLoss) querySource
      queryNormalizationExponent)
    (current : WZ1PaperTubeShading queryNormalized.croppedFamily)
    (planeMap : Point3 → Point3) (tauConstant : ENNReal)
    (first : Proposition63LiftedPointCoverData
      (outputLoss := firstLoss) (queryScale := rho.1)
      (spatialRadius := tauScale) queryNormalized current planeMap tauConstant)
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) queryNormalized first.state.shading)
    (ancestorEmbedding :
      Fin queryNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      queryNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index))
    (current_sub_outer : ∀ index, first.state.shading.carrier index ⊆
      outer.croppedCoarseShading.carrier (ancestorEmbedding index))
    (ancestorRetentionFactor : ENNReal)
    (ancestorRetentionFactor_pos : 0 < ancestorRetentionFactor)
    (ancestorRetentionFactor_ne_top : ancestorRetentionFactor ≠ ⊤)
    (current_retained_mass :
      ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
        first.state.shading.mass)
    (sqrtRequested : WZ2PaperRequestedScale rho.1)
    (sqrtSticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := sqrtStickyLoss)
      reentry.normalization.croppedRefined sqrtRequested 61)
    (coefficient : NNReal)
    (sqrtInput : Proposition63DependentHighPointCoverInput
      (targetLoss := secondLoss)
      ({ inner := sqrtSticky } : Proposition63DependentTwoLevelCoverData
        (innerLoss := sqrtStickyLoss) (innerLogExponent := 61)
        (proposition63DependentCoarseReentryOfCurrent outer queryNormalized
          first.state.shading reentry ancestorEmbedding ancestor_tube_eq
          current_sub_outer ancestorRetentionFactor
          ancestorRetentionFactor_pos ancestorRetentionFactor_ne_top
          current_retained_mass) sqrtRequested) planeMap coefficient) :
    ∃ result : Proposition63NestedPointCoverAnalyticData
        (firstLoss := firstLoss) (reentryLoss := reentryLoss)
        (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
        (queryScale := rho.1) (tauScale := tauScale)
        (sqrtScale := sqrtRequested.1) queryNormalized planeMap tauConstant
        (sqrtInput.C * Kakeya.realRpowENN
          (sqrtRequested.1 / rho.1) (1 - sigma)),
      result.current = current ∧
      result.firstRetainedFactor = first.retainedFactor ∧
      result.reentry.normalizationWeight = reentry.normalizationWeight ∧
      result.reentry.levelCount = reentry.levelCount ∧
      result.secondRetainedFactor =
        (proposition63DependentPropertyThreeMassLoss rho.1 61)⁻¹ := by
  let sqrtDependent : Proposition63DependentTwoLevelCoverData
      (innerLoss := sqrtStickyLoss) (innerLogExponent := 61)
      (proposition63DependentCoarseReentryOfCurrent outer queryNormalized
        first.state.shading reentry ancestorEmbedding ancestor_tube_eq
        current_sub_outer ancestorRetentionFactor
        ancestorRetentionFactor_pos ancestorRetentionFactor_ne_top
        current_retained_mass) sqrtRequested :=
    { inner := sqrtSticky }
  rcases sqrtInput.run with
    ⟨second, hsecond, _hsecondMultiplicity, hsecondMass, hsecondCover⟩
  let secondFactor :=
    (proposition63DependentPropertyThreeMassLoss rho.1 61)⁻¹
  have hsecondFactor := proposition63DependentPropertyThreeMassLoss_pos_ne_top
    reentry.reentry_extremal.delta_pos sqrtInput.rho_lt_one 61
  have hsecondFactorPos : 0 < secondFactor := by
    exact ENNReal.inv_pos.mpr hsecondFactor.2
  have hsecondFactorTop : secondFactor ≠ ⊤ := by
    exact ENNReal.inv_ne_top.mpr hsecondFactor.1.ne'
  have hsecondMass' : secondFactor *
      reentry.normalization.croppedRefined.mass ≤ second.shading.mass := by
    change secondFactor * reentry.normalization.croppedRefined.mass ≤
      second.shading.mass at hsecondMass
    simpa only [sqrtDependent, secondFactor,
      proposition63DependentCoarseReentryOfCurrent] using hsecondMass
  have hsecondSubset : second.shading.union ⊆
      (extendShading sqrtSticky.selected sqrtSticky.refined).union := by
    intro point hpoint
    have hproperty : point ∈ sqrtInput.propP.propertyThree.union := by
      rw [hsecond] at hpoint
      rw [sqrtDependent.commonPropertyThree_union sqrtInput.propP] at hpoint
      exact hpoint
    have hambient : point ∈ sqrtDependent.ambientRefined.union := by
      rcases hproperty with ⟨index, hindex⟩
      exact ⟨index, sqrtInput.propP.propertyOne_sub index
        (sqrtInput.propP.propertyThree_sub index hindex)⟩
    rw [extendShading_union]
    simpa only [sqrtDependent,
      Proposition63DependentTwoLevelCoverData.ambientRefined_union] using
      hambient
  refine ⟨{
    current := current
    first := first.state
    first_multiplicity := first.multiplicity
    firstCover := first.cover
    firstRetainedFactor := first.retainedFactor
    first_retained := first.retained
    first_retained_factor_pos := first.retained_factor_pos
    first_retained_factor_ne_top := first.retained_factor_ne_top
    reentry := reentry
    sqrtRequested := sqrtRequested
    sqrt_requested_eq := rfl
    sqrtSticky := sqrtSticky
    second := second
    secondCover := by
      change PureWZ2PointCenteredCoveringAt second.shading planeMap
        (Real.toNNReal rho.1) sqrtRequested.1
        (sqrtInput.C * Kakeya.realRpowENN
          (sqrtRequested.1 / rho.1) (1 - sigma)) at hsecondCover
      exact hsecondCover
    second_union_subset_sqrt_sticky := hsecondSubset
    secondRetainedFactor := secondFactor
    second_retained := hsecondMass'
    second_retained_factor_pos := hsecondFactorPos
    second_retained_factor_ne_top := hsecondFactorTop
  }, rfl, rfl, rfl, rfl, rfl⟩

/-- Execute the preselected third Node-3 call at the square-root radius and
construct its dependent HIGH point cover directly from CWA.  In particular,
neither the third sticky output nor its Property-(P) refinement is supplied
as an external geometric callback. -/
theorem ofLiftedFirstAndThirdCWA
    {fineDelta sigma outerLoss queryInputLoss queryNormalizationLoss firstLoss
      reentryLoss sqrtStickyLoss secondLoss sqrtDensityLoss epsilon₁ epsilon₃
      kappa tauScale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily fineDelta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale fineDelta}
    {outerLogExponent queryNormalizationExponent : ℕ}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent)
    {querySource : PureWZ2ExtremalConfiguration
      sigma queryInputLoss rho.1}
    (queryNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := queryNormalizationLoss) querySource
      queryNormalizationExponent)
    (current : WZ1PaperTubeShading queryNormalized.croppedFamily)
    (planeMap : Point3 → Point3) (tauConstant : ENNReal)
    (first : Proposition63LiftedPointCoverData
      (outputLoss := firstLoss) (queryScale := rho.1)
      (spatialRadius := tauScale) queryNormalized current planeMap tauConstant)
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) queryNormalized first.state.shading)
    (ancestorEmbedding :
      Fin queryNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      queryNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index))
    (current_sub_outer : ∀ index, first.state.shading.carrier index ⊆
      outer.croppedCoarseShading.carrier (ancestorEmbedding index))
    (ancestorRetentionFactor : ENNReal)
    (ancestorRetentionFactor_pos : 0 < ancestorRetentionFactor)
    (ancestorRetentionFactor_ne_top : ancestorRetentionFactor ≠ ⊤)
    (current_retained_mass :
      ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
        first.state.shading.mass)
    (schedule : Proposition63RichThreeCallScheduleData sigma sqrtStickyLoss)
    (hreentryLoss : reentryLoss = schedule.third.sourceLoss)
    (hnormalizationLoss :
      reentry.reentryNormalizationLoss = schedule.third.normalizationLoss)
    (hrhoSchedule : rho.1 ≤ schedule.third.delta₀)
    (sqrtRequested : WZ2PaperRequestedScale rho.1)
    (hsqrtLower : Real.rpow rho.1 (1 - sqrtStickyLoss) ≤
      sqrtRequested.1)
    (hsqrtUpper : sqrtRequested.1 ≤
      Real.rpow rho.1 sqrtStickyLoss)
    (coefficient : NNReal)
    (incidenceBound : ℝ)
    (hplaneUnit : ∀ point ∈ reentry.normalization.croppedRefined.union,
      ‖planeMap point‖ = 1)
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneIncidence : ∀ index point,
      point ∈ reentry.normalization.croppedRefined.carrier index →
        |@Inner.inner ℝ Point3 _
          (reentry.normalization.croppedFamily.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (hreentrySecond : reentry.reentryNormalizationLoss ≤ secondLoss)
    (hretention : Kakeya.realRpowENN rho.1 secondLoss ≤
      wz2PaperPureRefinementFraction rho.1 61 *
        Kakeya.realRpowENN rho.1 reentry.reentryNormalizationLoss)
    (hdensityLoss : sqrtDensityLoss = 2 - sigma + 3 * secondLoss)
    (hsecondLoss : 0 < secondLoss)
    (hsmall : Kakeya.realRpowENN rho.1 secondLoss < 1 / 4)
    (hrhoSmall24 : rho.1 ≤ 1 / 24)
    (hrhoSmall10000 : rho.1 ≤ 1 / 10000)
    (hpackingAbsorb :
      (12 * ((2 * 4 * 601 ^ 3 * 12001 ^ 3 + 1 : ℕ) : ENNReal)) *
          ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN rho.1 (-sigma + 4 * secondLoss))
    (hepsilon₁ : 0 < epsilon₁)
    (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (hsqrtPos : 0 < sqrtRequested.1)
    (hrhoSqrt : rho.1 ≤ sqrtRequested.1)
    (hsqrtLarge : rho.1 * Real.sqrt 3 ≤ sqrtRequested.1)
    (hsqrtSq : sqrtRequested.1 ^ 2 ≤ 4 * rho.1)
    (hsqrtOne : sqrtRequested.1 ≤ 1)
    (hcell :
      Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
          ENNReal.ofReal sqrtRequested.1 ≤
        Kakeya.realRpowENN rho.1 3)
    (hkappa : 0 < kappa)
    (hkappaOne : kappa ≤ 1)
    (hkappaRho : rho.1 ≤ kappa)
    (hkappaProperty : Real.rpow rho.1 epsilon₃ ≤ kappa)
    (hcloseAbsorb :
      Kakeya.realRpowENN rho.1 (-secondLoss) *
          ENNReal.ofReal (10000 * kappa ^ 2) <
        Kakeya.realRpowENN rho.1 sqrtDensityLoss)
    (hrhoOne : rho.1 < 1)
    (hmassSlack : proposition63DependentPropertyThreeMassLoss rho.1 61 *
        Kakeya.realRpowENN rho.1 secondLoss ≤
      Kakeya.realRpowENN rho.1 reentry.reentryNormalizationLoss)
    (hsqrtSmall : sqrtRequested.1 ≤ 1 / 12)
    (hrhoSmall : rho.1 ≤ 1 / 1000)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * rho.1) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          (((5832 * Real.rpow rho.1 (sigma - outerLoss) *
              Real.rpow sqrtRequested.1 (3 - sigma - 2 * sqrtStickyLoss)) /
              (Real.rpow rho.1 (1 + 7 * epsilon₁ + epsilon₃) *
                sqrtRequested.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth rho.1 sqrtRequested.1
              incidenceBound coefficient / rho.1 + 2)) ≤
        C * Kakeya.realRpowENN
          (sqrtRequested.1 / rho.1) (1 - sigma)) :
    ∃ result : Proposition63NestedPointCoverAnalyticData
        (firstLoss := firstLoss) (reentryLoss := reentryLoss)
        (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
        (queryScale := rho.1) (tauScale := tauScale)
        (sqrtScale := sqrtRequested.1) queryNormalized planeMap tauConstant
        (C * Kakeya.realRpowENN
          (sqrtRequested.1 / rho.1) (1 - sigma)),
      result.current = current ∧
      result.firstRetainedFactor = first.retainedFactor ∧
      result.reentry.normalizationWeight = reentry.normalizationWeight ∧
      result.reentry.levelCount = reentry.levelCount ∧
      result.secondRetainedFactor =
        (proposition63DependentPropertyThreeMassLoss rho.1 61)⁻¹ := by
  rcases proposition63CurrentShadingReentry_thirdSticky reentry schedule
      hreentryLoss hnormalizationLoss hrhoSchedule sqrtRequested
      hsqrtLower hsqrtUpper with ⟨sqrtSticky⟩
  let sqrtReentry := proposition63DependentCoarseReentryOfCurrent outer
    queryNormalized first.state.shading reentry ancestorEmbedding
    ancestor_tube_eq current_sub_outer ancestorRetentionFactor
    ancestorRetentionFactor_pos ancestorRetentionFactor_ne_top
    current_retained_mass
  let sqrtDependent : Proposition63DependentTwoLevelCoverData
      (innerLoss := sqrtStickyLoss) (innerLogExponent := 61)
      sqrtReentry sqrtRequested :=
    { inner := sqrtSticky }
  have hambientUnit : ∀ point ∈ sqrtDependent.ambientRefined.union,
      ‖planeMap point‖ = 1 := by
    intro point hpoint
    apply hplaneUnit point
    exact paperSubshading_union
      sqrtDependent.ambientRefined_sub_normalized hpoint
  have hambientIncidence : ∀ index point,
      point ∈ sqrtDependent.ambientRefined.carrier index →
        |@Inner.inner ℝ Point3 _
          (reentry.normalization.croppedFamily.tube index).direction
          (planeMap point)| ≤ incidenceBound := by
    intro index point hpoint
    exact hplaneIncidence index point
      (sqrtDependent.ambientRefined_sub_normalized index hpoint)
  have hfamilyCardPos : 0 < reentry.normalization.croppedFamily.enncard := by
    change (0 : ENNReal) <
      (reentry.normalization.croppedFamily.card : ENNReal)
    exact_mod_cast reentry.normalization.final_extremal.nonempty
  have hcloseAbsorbWithCard :
      Kakeya.realRpowENN rho.1 (-secondLoss) *
          ENNReal.ofReal (10000 * kappa ^ 2) *
          reentry.normalization.croppedFamily.enncard <
        Kakeya.realRpowENN rho.1 sqrtDensityLoss *
          reentry.normalization.croppedFamily.enncard := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      ENNReal.mul_lt_mul_right hfamilyCardPos.ne' ENNReal.coe_ne_top
        hcloseAbsorb
  rcases Proposition63DependentHighPointCoverInput.of_cwa sqrtDependent
      planeMap coefficient incidenceBound hambientUnit hplaneLipschitz
      hambientIncidence hreentrySecond hretention hdensityLoss hsecondLoss
      hsmall hrhoSmall24 hrhoSmall10000 hpackingAbsorb hepsilon₁ hepsilon₃
      hepsilonSum hsqrtPos hrhoSqrt hsqrtLarge hsqrtSq hsqrtOne hcell
      hkappa hkappaOne hkappaRho hkappaProperty hcloseAbsorbWithCard hrhoOne
      hmassSlack hsqrtSmall hrhoSmall hsigma hsigmaOne logScale hrhoLog
      hlog haxis C harithmetic with ⟨sqrtInput, hsqrtInputC⟩
  subst C
  have result := ofLiftedFirstAndSqrtHigh outer queryNormalized current planeMap
    tauConstant first reentry ancestorEmbedding ancestor_tube_eq
    current_sub_outer ancestorRetentionFactor ancestorRetentionFactor_pos
    ancestorRetentionFactor_ne_top current_retained_mass sqrtRequested
    sqrtSticky coefficient sqrtInput
  exact result

/-- Finish the analytic two-cover chain by genuine constant-multiplicity
selection and fresh square-root whole-cell balancing.  In particular, this
constructor never assumes the one-query AD estimate that the later interval
iteration is meant to prove. -/
theorem withFreshBalancedCells
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss middleLoss finalLoss queryScale tauScale
      sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    (data : Proposition63NestedPointCoverAnalyticData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant)
    (prepared : Proposition63ConstantMultiplicityShadingData
      (secondLoss := middleLoss) data.second)
    (fresh : Proposition63FreshBalancedExtremalCellsData
      (sqrtScale := sqrtScale) data.second prepared
      data.second.extremal.delta_pos)
    (hmiddleFinal : middleLoss ≤ finalLoss)
    (hfinalLoss : 0 < finalLoss)
    (hbalancingSlack : fresh.freshLoss *
        Kakeya.realRpowENN delta finalLoss ≤
      Kakeya.realRpowENN delta middleLoss) :
    ∃ result : Proposition63NestedPointCoverData
        (firstLoss := firstLoss) (reentryLoss := reentryLoss)
        (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
        (finalLoss := finalLoss) (queryScale := queryScale)
        (tauScale := tauScale) (sqrtScale := sqrtScale)
        initialNormalized planeMap tauConstant sqrtConstant,
      result.current = data.current ∧
      result.firstRetainedFactor = data.firstRetainedFactor ∧
      result.reentry.normalizationWeight = data.reentry.normalizationWeight ∧
      result.reentry.levelCount = data.reentry.levelCount ∧
      result.secondRetainedFactor = data.secondRetainedFactor ∧
      result.prepared.preparationLoss =
        prepared.preparationLoss * fresh.freshLoss := by
  let finalPrepared := fresh.toConstantMultiplicity hmiddleFinal hfinalLoss
    hbalancingSlack
  refine ⟨{
    current := data.current
    first := data.first
    first_multiplicity := data.first_multiplicity
    firstCover := data.firstCover
    firstRetainedFactor := data.firstRetainedFactor
    first_retained := data.first_retained
    first_retained_factor_pos := data.first_retained_factor_pos
    first_retained_factor_ne_top := data.first_retained_factor_ne_top
    reentry := data.reentry
    sqrtRequested := data.sqrtRequested
    sqrt_requested_eq := data.sqrt_requested_eq
    sqrtSticky := data.sqrtSticky
    second := data.second
    secondCover := data.secondCover
    second_union_subset_sqrt_sticky :=
      data.second_union_subset_sqrt_sticky
    secondRetainedFactor := data.secondRetainedFactor
    second_retained := data.second_retained
    second_retained_factor_pos := data.second_retained_factor_pos
    second_retained_factor_ne_top := data.second_retained_factor_ne_top
    prepared := finalPrepared
    cells := ?_
  }, rfl, rfl, rfl, rfl, rfl, ?_⟩
  change Proposition63BalancedCellData (scale := sqrtScale)
    fresh.balancing.refined
  exact fresh.cells
  simpa only [finalPrepared,
    Proposition63FreshBalancedExtremalCellsData.toConstantMultiplicity]
    using fresh.preparedLoss_eq

/-- Fully construct the non-circular cell preparation from the two analytic
point covers.  Both dyadic multiplicity and fresh whole-cell balancing are
run here; the caller supplies only their explicit loss absorptions and legal
square-root scale window. -/
theorem prepareFreshBalancedCells
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss middleLoss finalLoss queryScale tauScale
      sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    (data : Proposition63NestedPointCoverAnalyticData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant)
    (hsecondMiddle : secondLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (hmultiplicitySlack :
      (((Nat.log 2 data.reentry.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal) * Kakeya.realRpowENN delta middleLoss) ≤
        Kakeya.realRpowENN delta secondLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hperiodicScale : 50 * delta ≤ sqrtScale)
    (hsqrtPos : 0 < sqrtScale)
    (hsqrtOne : sqrtScale ≤ 1)
    (hboundaryScalar :
      2 * 24000000 *
          (Kakeya.realRpowENN delta (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (delta / sqrtScale)) <
        Kakeya.realRpowENN delta middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss)
    (hfinalLoss : 0 < finalLoss)
    (hbalancingSlack : proposition63FreshBalancingEnvelope delta *
        Kakeya.realRpowENN delta finalLoss ≤
      Kakeya.realRpowENN delta middleLoss) :
    ∃ result : Proposition63NestedPointCoverData
        (firstLoss := firstLoss) (reentryLoss := reentryLoss)
        (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
        (finalLoss := finalLoss) (queryScale := queryScale)
        (tauScale := tauScale) (sqrtScale := sqrtScale)
        initialNormalized planeMap tauConstant sqrtConstant,
      result.current = data.current ∧
      result.firstRetainedFactor = data.firstRetainedFactor ∧
      result.reentry.normalizationWeight = data.reentry.normalizationWeight ∧
      result.reentry.levelCount = data.reentry.levelCount ∧
      result.secondRetainedFactor = data.secondRetainedFactor ∧
      result.prepared.preparationLoss ≤
        proposition63UniformPreparationLoss
          initialNormalized.croppedFamily := by
  rcases proposition63_prepare_extremalShading_constantMultiplicity_with_loss
      data.second hsecondMiddle hmiddleLoss hmultiplicitySlack with
    ⟨prepared, hpreparedLoss⟩
  rcases proposition63_fresh_balancedExtremalCells_of_cwa_scalar data.second
      prepared data.reentry.normalization.line_class hdeltaSmall
      hperiodicScale hsqrtPos hsqrtOne hboundaryScalar with
    ⟨fresh⟩
  rcases data.withFreshBalancedCells prepared fresh hmiddleFinal hfinalLoss
      ((mul_le_mul_right' fresh.freshLoss_le_envelope
        (Kakeya.realRpowENN delta finalLoss)).trans hbalancingSlack) with
    ⟨result, hresultCurrent, hresultFirst, hresultWeight, hresultLevel,
      hresultSecond, hresultPreparation⟩
  refine ⟨result, hresultCurrent, hresultFirst, hresultWeight, hresultLevel,
    hresultSecond, ?_⟩
  rw [hresultPreparation, hpreparedLoss]
  have hcard : data.reentry.normalization.croppedFamily.card ≤
      initialNormalized.croppedFamily.card := by
    rw [data.reentry.normalization_croppedFamily]
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      data.reentry.regularized.selected.embedding
      data.reentry.regularized.selected.embedding.injective
  have hlog :
      ((Nat.log 2 data.reentry.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal) ≤
        ((Nat.log 2 initialNormalized.croppedFamily.card + 1 : ℕ) :
          ENNReal) := by
    exact_mod_cast Nat.add_le_add_right (Nat.log_mono_right hcard) 1
  unfold proposition63UniformPreparationLoss
  exact mul_le_mul hlog fresh.freshLoss_le_envelope bot_le bot_le

end Proposition63NestedPointCoverAnalyticData

namespace Proposition63NestedPointCoverData

variable
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3}
    {tauConstant sqrtConstant : ENNReal}

/-- The final balanced shading remains inside the current shading on which
the nested pair started. -/
theorem prepared_union_subset_current
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant) :
    data.prepared.refined.shading.union ⊆ data.current.union := by
  intro point hpoint
  have hsecond : point ∈ data.second.shading.union :=
    paperSubshading_union data.prepared.subshading_original hpoint
  have hnormalized : point ∈ data.reentry.normalization.croppedRefined.union :=
    paperSubshading_union data.second.subshading hsecond
  have hfirst : point ∈ data.first.shading.union :=
    data.reentry.normalization_croppedRefined_union_subset_current hnormalized
  exact paperSubshading_union data.first.subshading hfirst

/-- The first, arbitrary-radius covering estimate survives the exact
ordinary-trace re-entry, the second analytic refinement, and the final
constant-multiplicity refinement. -/
theorem firstCoverOnPrepared
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant) :
    PureWZ2PointCenteredCoveringAt data.prepared.refined.shading planeMap
      (Real.toNNReal queryScale) tauScale tauConstant := by
  apply pureWZ2PointCenteredCoveringAt_mono
    data.prepared.subshading_original
  apply pureWZ2PointCenteredCoveringAt_mono data.second.subshading
  exact data.reentry.pointCenteredCovering data.firstCover

/-- The square-root covering estimate survives the final
constant-multiplicity refinement. -/
theorem secondCoverOnPrepared
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant) :
    PureWZ2PointCenteredCoveringAt data.prepared.refined.shading planeMap
      (Real.toNNReal queryScale) sqrtScale sqrtConstant :=
  pureWZ2PointCenteredCoveringAt_mono
    data.prepared.subshading_original data.secondCover

/-- Exact multiplicative mass ledger through the first cover, its re-entry,
the second cover, and constant-multiplicity preparation. -/
theorem prepared_mass_ledger
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant) :
    (data.secondRetainedFactor *
        ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
        data.firstRetainedFactor) *
        data.current.mass ≤
      (data.reentry.regularized.regularizationLoss *
        data.prepared.preparationLoss) * data.prepared.refined.shading.mass := by
  calc
    (data.secondRetainedFactor *
          ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
          data.firstRetainedFactor) *
          data.current.mass =
        data.secondRetainedFactor *
          ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
          (data.firstRetainedFactor *
            data.current.mass) := by ring
    _ ≤ data.secondRetainedFactor *
          ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
          data.first.shading.mass := by
      gcongr
      exact data.first_retained
    _ ≤ data.secondRetainedFactor *
          (data.reentry.regularized.regularizationLoss *
            data.reentry.normalization.croppedRefined.mass) := by
      calc
        data.secondRetainedFactor *
            ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
            data.first.shading.mass =
          data.secondRetainedFactor *
            (((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
              data.first.shading.mass) := by ring
        _ ≤ data.secondRetainedFactor *
            (data.reentry.regularized.regularizationLoss *
              data.reentry.normalization.croppedRefined.mass) :=
          mul_le_mul_left' data.reentry.reentryMassRetention _
    _ = data.reentry.regularized.regularizationLoss *
          (data.secondRetainedFactor *
            data.reentry.normalization.croppedRefined.mass) := by ring
    _ ≤ data.reentry.regularized.regularizationLoss *
          data.second.shading.mass := by
      gcongr
      exact data.second_retained
    _ ≤ data.reentry.regularized.regularizationLoss *
          (data.prepared.preparationLoss *
            data.prepared.refined.shading.mass) := by
      exact mul_le_mul_left' data.prepared.mass_retention _
    _ = (data.reentry.regularized.regularizationLoss *
          data.prepared.preparationLoss) *
        data.prepared.refined.shading.mass := by ring

/-- Every active square-root cell of the final balanced shading is one of
the active cells supplied by the actual third sticky call.  This is the
cardinality bridge used in the paper; it avoids counting the entire ambient
three-dimensional grid window. -/
theorem activeCells_subset_sqrtSticky
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant) :
    data.cells.activeCells ⊆ data.sqrtSticky.balanced.activeCells := by
  intro cell hcell
  let point := data.cells.cellRep cell hcell
  have hpointPrepared : point ∈ data.prepared.refined.shading.union :=
    data.cells.cellRep_in_union cell hcell
  have hpointSecond : point ∈ data.second.shading.union :=
    paperSubshading_union data.prepared.subshading_original hpointPrepared
  have hpointExtended : point ∈
      (extendShading data.sqrtSticky.selected data.sqrtSticky.refined).union :=
    data.second_union_subset_sqrt_sticky hpointSecond
  have hpointSticky : point ∈ data.sqrtSticky.refined.union := by
    rw [← extendShading_union data.sqrtSticky.selected
      data.sqrtSticky.refined]
    exact hpointExtended
  have hpointCoarse : point ∈ data.sqrtSticky.croppedCoarseShading.union := by
    rcases hpointSticky with ⟨sourceIndex, hsourcePoint⟩
    let parent := data.sqrtSticky.cover.toPaperTubeCover.parent sourceIndex
    exact ⟨parent, data.sqrtSticky.balanced.point_compatibility sourceIndex
      parent (data.sqrtSticky.cover.toPaperTubeCover.parent_covers sourceIndex)
      point hsourcePoint⟩
  rw [data.sqrtSticky.balanced.coarse_union_eq] at hpointCoarse
  rcases Set.mem_iUnion₂.mp hpointCoarse with
    ⟨stickyCell, hstickyCell, hpointStickyCell⟩
  have hcurrentIndex : wz1PaperGridIndex sqrtScale point = cell :=
    (mem_wz1PaperGridCube sqrtScale cell point).mp
      (data.cells.cellRep_in_cell cell hcell)
  have hstickyIndex : wz1PaperGridIndex sqrtScale point = stickyCell := by
    rw [← data.sqrt_requested_eq]
    exact (mem_wz1PaperGridCube data.sqrtRequested.1 stickyCell point).mp
      hpointStickyCell
  rw [← hcurrentIndex, hstickyIndex]
  exact hstickyCell

/-- The active square-root cells of the nested candidate obey the sharp
cardinality bound coming from the third sticky cover's coarse volume upper
bound.  The denominator is the volume of one actual square-root cell. -/
theorem activeCells_mul_sqrtCubeVolume_le
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant) :
    (data.cells.activeCells.card : ENNReal) *
        Kakeya.realRpowENN sqrtScale 3 ≤
      Kakeya.realRpowENN sqrtScale (sigma - sqrtStickyLoss) := by
  have hcard : data.cells.activeCells.card ≤
      data.sqrtSticky.balanced.activeCells.card :=
    Finset.card_le_card data.activeCells_subset_sqrtSticky
  have hcardENN : (data.cells.activeCells.card : ENNReal) ≤
      (data.sqrtSticky.balanced.activeCells.card : ENNReal) := by
    exact_mod_cast hcard
  have hcube : Kakeya.realRpowENN sqrtScale 3 =
      volume (wz1PaperGridCube data.sqrtRequested.1 (0, 0, 0)) := by
    calc
      Kakeya.realRpowENN sqrtScale 3 =
          Kakeya.realRpowENN data.sqrtRequested.1 3 :=
        congrArg (fun scale => Kakeya.realRpowENN scale 3)
          data.sqrt_requested_eq.symm
      _ = ENNReal.ofReal (data.sqrtRequested.1 ^ 3) := by
        simp [Kakeya.realRpowENN, Real.rpow_natCast]
      _ = volume
          (wz1PaperGridCube data.sqrtRequested.1 (0, 0, 0)) :=
        (wz1PaperGridCube_volume_exact
          data.sqrtSticky.coarse_extremal.delta_pos).symm
  calc
    (data.cells.activeCells.card : ENNReal) *
          Kakeya.realRpowENN sqrtScale 3 ≤
        (data.sqrtSticky.balanced.activeCells.card : ENNReal) *
          Kakeya.realRpowENN sqrtScale 3 := by gcongr
    _ = volume data.sqrtSticky.croppedCoarseShading.union := by
      rw [hcube]
      exact (balanced_cover_coarse_volume data.sqrtSticky.balanced
        data.sqrtSticky.coarse_extremal.delta_pos).symm
    _ ≤ Kakeya.realRpowENN data.sqrtRequested.1
          (sigma - sqrtStickyLoss) :=
      data.sqrtSticky.coarse_extremal.volume_upper
    _ = Kakeya.realRpowENN sqrtScale (sigma - sqrtStickyLoss) := by
      rw [data.sqrt_requested_eq]

/-- Apply the global critical-volume floor only to the final extremal
coarse shading, and divide it by the sharp third-sticky active-cell count.
The scalar hypothesis is the exact power comparison; crucially, it contains
no full ambient grid-window cardinality. -/
theorem critical_cellMass_lower
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant)
    {floorLoss structuralBudget cellVolumeFloor : ℝ}
    (critical : PureWZ2CroppedCriticalFloorSelectionData
      sigma floorLoss structuralBudget)
    (hdeltaCritical : delta ≤ critical.delta₀)
    (hfinalStructural : finalLoss = critical.structuralLoss)
    (hcellVolumeFloor : 0 ≤ cellVolumeFloor)
    (hcellBudget :
      ENNReal.ofReal cellVolumeFloor *
          Kakeya.realRpowENN sqrtScale (sigma - sqrtStickyLoss) ≤
        Kakeya.realRpowENN delta (sigma + floorLoss) *
          Kakeya.realRpowENN sqrtScale 3) :
    ENNReal.ofReal cellVolumeFloor ≤ data.cells.cellMass := by
  have hdelta : 0 < delta :=
    data.prepared.refined.extremal.delta_pos
  have hcwa : WZ2PaperPureCWAAtNearbyScales
      data.reentry.normalization.croppedFamily
      (Kakeya.realRpowENN delta (-critical.structuralLoss)) := by
    rw [← hfinalStructural]
    exact data.prepared.refined.extremal.cwa_nearby_scales
  have hdense : data.prepared.refined.shading.IsLambdaDense
      (Kakeya.realRpowENN delta critical.structuralLoss) := by
    rw [← hfinalStructural]
    exact data.prepared.refined.extremal.dense
  have hunionFloor :
      Kakeya.realRpowENN delta (sigma + floorLoss) ≤
        volume data.prepared.refined.shading.union :=
    critical.volume_floor delta hdelta hdeltaCritical
      data.reentry.normalization.croppedFamily
      data.prepared.refined.extremal.nonempty
      data.prepared.refined.shading hcwa
      data.prepared.refined.extremal.cubical hdense
  let active : ENNReal := data.cells.activeCells.card
  let cubeVolume : ENNReal := Kakeya.realRpowENN sqrtScale 3
  let activeUpper : ENNReal :=
    Kakeya.realRpowENN sqrtScale (sigma - sqrtStickyLoss)
  have hactiveCube : active * cubeVolume ≤ activeUpper := by
    simpa only [active, cubeVolume, activeUpper] using
      data.activeCells_mul_sqrtCubeVolume_le
  have hcubePos : 0 < cubeVolume := by
    dsimp only [cubeVolume, Kakeya.realRpowENN]
    exact ENNReal.ofReal_pos.mpr <|
      Real.rpow_pos_of_pos data.cells.scale_pos _
  have hcubeTop : cubeVolume ≠ ⊤ := by
    simp [cubeVolume, Kakeya.realRpowENN]
  have hcellActive : ENNReal.ofReal cellVolumeFloor * active ≤
      Kakeya.realRpowENN delta (sigma + floorLoss) := by
    apply (ENNReal.mul_le_mul_iff_right hcubePos.ne' hcubeTop).mp
    calc
      cubeVolume * (ENNReal.ofReal cellVolumeFloor * active) =
          ENNReal.ofReal cellVolumeFloor * (active * cubeVolume) := by ring
      _ ≤ ENNReal.ofReal cellVolumeFloor * activeUpper := by gcongr
      _ ≤ cubeVolume * Kakeya.realRpowENN delta (sigma + floorLoss) := by
        simpa only [activeUpper, cubeVolume, mul_comm] using hcellBudget
  have hactiveMass : ENNReal.ofReal cellVolumeFloor * active ≤
      active * data.cells.cellMass := by
    calc
      ENNReal.ofReal cellVolumeFloor * active ≤
          Kakeya.realRpowENN delta (sigma + floorLoss) :=
        hcellActive
      _ ≤ volume data.prepared.refined.shading.union := hunionFloor
      _ = active * data.cells.cellMass := by
        simpa only [active] using data.cells.fine_union_volume
  have hfloorPos : 0 < Kakeya.realRpowENN delta
      (sigma + floorLoss) := by
    simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hdelta]
  have hunionPos : 0 < volume data.prepared.refined.shading.union :=
    hfloorPos.trans_le hunionFloor
  have hactiveZero : active ≠ 0 := by
    intro hzero
    rw [data.cells.fine_union_volume] at hunionPos
    simp only [active, hzero, zero_mul] at hunionPos
    exact (lt_irrefl 0) hunionPos
  have hactiveTop : active ≠ ⊤ := by
    simp [active]
  apply (ENNReal.mul_le_mul_iff_right hactiveZero hactiveTop).mp
  simpa [mul_comm] using hactiveMass

theorem critical_cellMass_lower_of_pure_critical_trace
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant)
    {floorLoss structuralBudget cellVolumeFloor : ℝ}
    (critical : PureWZ2CriticalFloorSelectionData
      sigma floorLoss structuralBudget)
    (hdeltaCritical : delta ≤ critical.delta₀)
    (hfinalStructural : finalLoss ≤ critical.structuralLoss)
    (traceAbsorption : Proposition63PureCriticalTailTraceAbsorption delta
      critical.structuralLoss reentryLoss finalLoss)
    (hcellVolumeFloor : 0 ≤ cellVolumeFloor)
    (hcellBudget :
      ENNReal.ofReal cellVolumeFloor *
          Kakeya.realRpowENN sqrtScale (sigma - sqrtStickyLoss) ≤
        Kakeya.realRpowENN delta (sigma + floorLoss) *
          Kakeya.realRpowENN sqrtScale 3) :
    ENNReal.ofReal cellVolumeFloor ≤ data.cells.cellMass := by
  have hdelta : 0 < delta :=
    data.prepared.refined.extremal.delta_pos
  have hcwa : WZ2PaperPureCWAAtNearbyScales
      data.reentry.normalization.croppedFamily
      (Kakeya.realRpowENN delta (-critical.structuralLoss)) :=
    data.prepared.refined.extremal.cwa_nearby_scales.mono_loss
      hdelta data.prepared.refined.extremal.delta_le_one hfinalStructural
  let trace := data.reentry.normalization.criticalTailOrdinaryTrace_identity
    data.prepared.refined.shading data.prepared.refined.extremal.cubical
    data.prepared.refined.subshading data.reentry.normalizationOrdinaryPerTube
    data.prepared.refined.extremal hcwa
    (data.reentry.delta_small.trans (by norm_num)) traceAbsorption
  have hunionFloor :
      Kakeya.realRpowENN delta (sigma + floorLoss) ≤
        volume data.prepared.refined.shading.union :=
    critical.cropped_union_floor_of_trace hdelta hdeltaCritical trace
  let active : ENNReal := data.cells.activeCells.card
  let cubeVolume : ENNReal := Kakeya.realRpowENN sqrtScale 3
  let activeUpper : ENNReal :=
    Kakeya.realRpowENN sqrtScale (sigma - sqrtStickyLoss)
  have hactiveCube : active * cubeVolume ≤ activeUpper := by
    simpa only [active, cubeVolume, activeUpper] using
      data.activeCells_mul_sqrtCubeVolume_le
  have hcubePos : 0 < cubeVolume := by
    dsimp only [cubeVolume, Kakeya.realRpowENN]
    exact ENNReal.ofReal_pos.mpr <|
      Real.rpow_pos_of_pos data.cells.scale_pos _
  have hcubeTop : cubeVolume ≠ ⊤ := by
    simp [cubeVolume, Kakeya.realRpowENN]
  have hcellActive : ENNReal.ofReal cellVolumeFloor * active ≤
      Kakeya.realRpowENN delta (sigma + floorLoss) := by
    apply (ENNReal.mul_le_mul_iff_right hcubePos.ne' hcubeTop).mp
    calc
      cubeVolume * (ENNReal.ofReal cellVolumeFloor * active) =
          ENNReal.ofReal cellVolumeFloor * (active * cubeVolume) := by ring
      _ ≤ ENNReal.ofReal cellVolumeFloor * activeUpper := by gcongr
      _ ≤ cubeVolume * Kakeya.realRpowENN delta (sigma + floorLoss) := by
        simpa only [activeUpper, cubeVolume, mul_comm] using hcellBudget
  have hactiveMass : ENNReal.ofReal cellVolumeFloor * active ≤
      active * data.cells.cellMass := by
    calc
      ENNReal.ofReal cellVolumeFloor * active ≤
          Kakeya.realRpowENN delta (sigma + floorLoss) :=
        hcellActive
      _ ≤ volume data.prepared.refined.shading.union := hunionFloor
      _ = active * data.cells.cellMass := by
        simpa only [active] using data.cells.fine_union_volume
  have hfloorPos : 0 < Kakeya.realRpowENN delta
      (sigma + floorLoss) := by
    simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hdelta]
  have hunionPos : 0 < volume data.prepared.refined.shading.union :=
    hfloorPos.trans_le hunionFloor
  have hactiveZero : active ≠ 0 := by
    intro hzero
    rw [data.cells.fine_union_volume] at hunionPos
    simp only [active, hzero, zero_mul] at hunionPos
    exact (lt_irrefl 0) hunionPos
  have hactiveTop : active ≠ ⊤ := by
    simp [active]
  apply (ENNReal.mul_le_mul_iff_right hactiveZero hactiveTop).mp
  simpa [mul_comm] using hactiveMass

/-- The full-grain/Fubini certificate in every active square-root cell.
Unlike the historical constructor, this consumes only the second
point-centered covering estimate, not a completed one-scale AD theorem. -/
structure FullGrainCells
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant)
    (lineVolume : ℝ) (coverBudget : ℕ) where
  cellData : ∀ cell : {cell // cell ∈ data.cells.activeCells},
    Proposition63FullGrainFubiniCellData
      (data.prepared.refined.shading.union ∩
        wz1PaperGridCube sqrtScale cell.1)
      (planeMap (data.cells.cellRep cell.1 cell.2))
      queryScale (2 * sqrtScale) lineVolume
      (data.cells.cellMass / 2)
      ((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal)))
  lineHits : ∀ cell : {cell // cell ∈ data.cells.activeCells},
    (cellData cell).LineHitData

namespace FullGrainCells

def nestedCellIntervalBound
    (queryScale K : ℝ) (tauConstant : ENNReal) : ENNReal :=
  4 * (9 *
    ((2 * Nat.ceil ((2 * K * queryScale) / queryScale) + 2 : ENNReal) *
      tauConstant))

def nestedRegionIntervalBound
    (queryScale normalError K : ℝ) (neighborBudget : ℕ)
    (tauConstant : ENNReal) : ENNReal :=
  (2 * Nat.ceil (normalError / queryScale) + 2 : ENNReal) *
    ((neighborBudget : ENNReal) *
      (5 * nestedCellIntervalBound queryScale K tauConstant))

def nestedCandidateIntervalBound
    (delta queryScale normalError K : ℝ) (neighborBudget : ℕ)
    (tauConstant : ENNReal) : ENNReal :=
  (2 * Nat.ceil ((delta * Real.sqrt 3) / queryScale) + 2 : ENNReal) *
    (5 * nestedRegionIntervalBound queryScale normalError K neighborBudget
      tauConstant)

@[simp] lemma nestedCellIntervalBound_eq
    (queryScale K : ℝ) (tauConstant : ENNReal) :
    nestedCellIntervalBound queryScale K tauConstant =
      4 * (9 *
        ((2 * Nat.ceil ((2 * K * queryScale) / queryScale) + 2 : ENNReal) *
          tauConstant)) := rfl

@[simp] lemma nestedRegionIntervalBound_eq
    (queryScale normalError K : ℝ) (neighborBudget : ℕ)
    (tauConstant : ENNReal) :
    nestedRegionIntervalBound queryScale normalError K neighborBudget
        tauConstant =
      (2 * Nat.ceil (normalError / queryScale) + 2 : ENNReal) *
        ((neighborBudget : ENNReal) *
          (5 * nestedCellIntervalBound queryScale K tauConstant)) := rfl

@[simp] lemma nestedCandidateIntervalBound_eq
    (delta queryScale normalError K : ℝ) (neighborBudget : ℕ)
    (tauConstant : ENNReal) :
    nestedCandidateIntervalBound delta queryScale normalError K
        neighborBudget tauConstant =
      (2 * Nat.ceil ((delta * Real.sqrt 3) / queryScale) + 2 : ENNReal) *
        (5 * nestedRegionIntervalBound queryScale normalError K
          neighborBudget tauConstant) := rfl

/-- The line-hit region in one active square-root cell. -/
def cellLineHitRegion
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (cell : ℤ × ℤ × ℤ) : Set Point3 :=
  if hcell : cell ∈ data.cells.activeCells then
    (full.lineHits ⟨cell, hcell⟩).region
  else ∅

lemma cellLineHitRegion_eq
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ data.cells.activeCells) :
    full.cellLineHitRegion cell =
      (full.lineHits ⟨cell, hcell⟩).region := by
  simp [cellLineHitRegion, hcell]

/-- Union of the selected line-hit full grains in all active square-root
cells. -/
def lineHitRegion
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget) : Set Point3 :=
  ⋃ cell ∈ data.cells.activeCells, full.cellLineHitRegion cell

/-- Active square-root cells whose line-hit region meets a specified spatial
ball. -/
def lineHitRelevantCells
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (center : Point3) (radius : ℝ) : Finset (ℤ × ℤ × ℤ) :=
  data.cells.activeCells.filter fun cell =>
    (full.cellLineHitRegion cell ∩ Metric.closedBall center radius).Nonempty

lemma gridCell_sqrtThree_eq_paperGridCube
    (scale : ℝ) (cell : ℤ × ℤ × ℤ) :
    gridCell (scale * Real.sqrt 3) cell =
      wz1PaperGridCube scale cell := by
  have hsqrt : Real.sqrt 3 ≠ 0 :=
    (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hside : gridSide (scale * Real.sqrt 3 / 2) = scale := by
    dsimp only [gridSide]
    field_simp [hsqrt]
  ext point
  simp only [gridCell, rhoGridIndex, wz1PaperGridCube,
    wz1PaperGridIndex, hside]

theorem cellLineHitRegion_subset_cell
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ data.cells.activeCells) :
    full.cellLineHitRegion cell ⊆ wz1PaperGridCube sqrtScale cell := by
  rw [full.cellLineHitRegion_eq cell hcell]
  exact (full.lineHits ⟨cell, hcell⟩).region_subset_good.trans
    ((full.cellData ⟨cell, hcell⟩).good_subset.trans Set.inter_subset_right)

/-- A ball whose radius is at most three literal cell side lengths meets at
most `13^3` active cells.  This is a local constant bound and is independent
of the total number of square-root cells. -/
theorem lineHitRelevantCells_card_le_fixed
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hsqrtPos : 0 < sqrtScale) (center : Point3) {radius : ℝ}
    (hradius : radius ≤ 3 * (sqrtScale * Real.sqrt 3)) :
    (full.lineHitRelevantCells center radius).card ≤ 13 ^ 3 := by
  have hgridScale : 0 < sqrtScale * Real.sqrt 3 := by positivity
  have hbound := gridCellsIntersecting_ball_bound hgridScale center hradius
  have hsubset :
      (↑(full.lineHitRelevantCells center radius) :
          Set (ℤ × ℤ × ℤ)) ⊆
        gridCellsIntersecting (sqrtScale * Real.sqrt 3)
          (Metric.closedBall center radius) := by
    intro cell hcell
    rcases Finset.mem_filter.mp hcell with
      ⟨hcellActive, point, hpointRegion, hpointBall⟩
    refine ⟨point, ?_, hpointBall⟩
    rw [gridCell_sqrtThree_eq_paperGridCube]
    exact full.cellLineHitRegion_subset_cell cell hcellActive hpointRegion
  have hncard := Set.ncard_le_ncard hsubset hbound.1
  simpa using hncard.trans hbound.2

theorem lineHitRegion_measurable
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget) :
    MeasurableSet full.lineHitRegion := by
  apply MeasurableSet.biUnion
    (Finset.finite_toSet data.cells.activeCells).countable
  intro cell hcell
  rw [full.cellLineHitRegion_eq cell hcell]
  exact (full.lineHits ⟨cell, hcell⟩).region_measurable

theorem lineHitRegion_subset
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget) :
    full.lineHitRegion ⊆ data.prepared.refined.shading.union := by
  intro point hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointRegion⟩
  rw [full.cellLineHitRegion_eq cell hcell] at hpointRegion
  exact (full.cellData ⟨cell, hcell⟩).good_subset
    (Proposition63FullGrainFubiniCellData.LineHitData.region_subset_good
      (full.cellData ⟨cell, hcell⟩)
      (full.lineHits ⟨cell, hcell⟩) hpointRegion) |>.1

/-- Cubical hull of the genuine line-hit region at the ambient tube scale. -/
def lineHitCandidate
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    WZ1PaperTubeShading data.reentry.normalization.croppedFamily :=
  wz2RefinedShading data.prepared.refined.shading <|
    (wz1PaperGridIndicesInWindow delta hdelta).filter fun cell =>
      (full.lineHitRegion ∩ wz1PaperGridCube delta cell).Nonempty

theorem lineHitCandidate_subshading
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    PaperIsSubshading (full.lineHitCandidate hdelta)
      data.prepared.refined.shading :=
  wz2RefinedShading_subshading

theorem lineHitCandidate_cubical
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    WZ1PaperIsCubicalShading (full.lineHitCandidate hdelta) :=
  wz2RefinedShading_cubical data.prepared.refined.extremal.cubical

theorem lineHitRegion_subset_candidate_union
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    full.lineHitRegion ⊆ (full.lineHitCandidate hdelta).union := by
  intro point hpoint
  have hpointPrepared : point ∈ data.prepared.refined.shading.union :=
    full.lineHitRegion_subset hpoint
  have hpointBox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
    rcases hpointPrepared with ⟨index, hindex⟩
    exact (data.prepared.refined.shading.subset_body index hindex).2
  have hwindow : wz1PaperGridIndex delta point ∈
      wz1PaperGridIndicesInWindow delta hdelta :=
    Kakeya.Assouad.paper_point_gridIndex_in_window hdelta hpointBox
  have hpointCell : point ∈
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) := by
    rw [mem_wz1PaperGridCube]
  have hselected : wz1PaperGridIndex delta point ∈
      (wz1PaperGridIndicesInWindow delta hdelta).filter fun cell =>
        (full.lineHitRegion ∩ wz1PaperGridCube delta cell).Nonempty := by
    rw [Finset.mem_filter]
    exact ⟨hwindow, ⟨point, hpoint, hpointCell⟩⟩
  rw [lineHitCandidate, wz2RefinedShading_union_inter]
  exact ⟨hpointPrepared, Set.mem_iUnion₂.mpr
    ⟨wz1PaperGridIndex delta point, hselected, hpointCell⟩⟩

/-- Every point of the cubical hull lies in one ambient `delta`-cell meeting
the genuine line-hit region. -/
theorem lineHitCandidate_close_to_lineHitRegion
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    ∀ point ∈ (full.lineHitCandidate hdelta).union,
      ∃ sourcePoint ∈ full.lineHitRegion,
        dist point sourcePoint ≤ delta * Real.sqrt 3 := by
  intro point hpoint
  have hpointHull := hpoint
  rw [lineHitCandidate, wz2RefinedShading_union_inter] at hpointHull
  rcases Set.mem_iUnion₂.mp hpointHull.2 with
    ⟨cell, hcellSelected, hpointCell⟩
  have hcellHit :
      (full.lineHitRegion ∩ wz1PaperGridCube delta cell).Nonempty :=
    (Finset.mem_filter.mp hcellSelected).2
  rcases hcellHit with ⟨sourcePoint, hsourceRegion, hsourceCell⟩
  exact ⟨sourcePoint, hsourceRegion,
    wz1PaperGridCube_diameter hdelta cell hpointCell hsourceCell⟩

/-- The nested line-hit region retains the same cell-mass-cancelled fraction
as the historical one-scale construction.  The analytic input is now the
explicit square-root point-centered estimate. -/
theorem lineHitRegion_mass_ledger
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hquery : 0 < queryScale) :
    (data.cells.activeCells.card : ENNReal) *
        (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          ((data.cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal)))) ≤
      ENNReal.ofReal (4 * queryScale) * volume full.lineHitRegion := by
  have hdisjoint : Set.PairwiseDisjoint (↑data.cells.activeCells)
      full.cellLineHitRegion := by
    intro first hfirst second hsecond hne
    exact (wz1PaperGridCube_disjoint hne).mono
      (full.cellLineHitRegion_subset_cell first hfirst)
      (full.cellLineHitRegion_subset_cell second hsecond)
  have hmeasurable : ∀ cell ∈ data.cells.activeCells,
      MeasurableSet (full.cellLineHitRegion cell) := by
    intro cell hcell
    rw [full.cellLineHitRegion_eq cell hcell]
    exact (full.lineHits ⟨cell, hcell⟩).region_measurable
  have hsum :
      ∑ _cell ∈ data.cells.activeCells,
          ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
            ((data.cells.cellMass / 2) /
              (2 * (coverBudget : ENNReal))) ≤
        ∑ cell ∈ data.cells.activeCells,
          ENNReal.ofReal (4 * queryScale) *
            volume (full.cellLineHitRegion cell) := by
    apply Finset.sum_le_sum
    intro cell hcell
    rw [full.cellLineHitRegion_eq cell hcell]
    exact (full.lineHits ⟨cell, hcell⟩).line_volume_mul_threshold_le
      (full.cellData ⟨cell, hcell⟩) hquery
  have hunion : volume full.lineHitRegion =
      ∑ cell ∈ data.cells.activeCells,
        volume (full.cellLineHitRegion cell) :=
    measure_biUnion_finset hdisjoint hmeasurable
  rw [hunion]
  simpa only [full.cellLineHitRegion_eq, Finset.sum_const, Finset.mul_sum,
    nsmul_eq_mul] using hsum

/-- The line-hit selection ledger relative to the already prepared source.
This isolates the geometric line and inverse-cover factors: no earlier sticky
retention factor or preparation-loss receipt is used. -/
theorem prepared_lineHitCandidate_mass_ledger
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) (hquery : 0 < queryScale) :
    let lineFactor :=
      ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2))
    let inverseCoverFactor :=
      ((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))
    (lineFactor * inverseCoverFactor) * data.prepared.refined.shading.mass ≤
      (2 * ENNReal.ofReal (4 * queryScale)) *
        (full.lineHitCandidate hdelta).mass := by
  dsimp only
  have hsourceVolume : data.prepared.refined.shading.mass ≤
      (2 * (2 ^ data.prepared.level : ENNReal)) *
        ((data.cells.activeCells.card : ENNReal) *
          data.cells.cellMass) := by
    calc
      data.prepared.refined.shading.mass ≤
          (2 * (2 ^ data.prepared.level : ENNReal)) *
            volume data.prepared.refined.shading.union :=
        Kakeya.Assouad.mass_le_multiplicity_vol
          (ENNReal.mul_ne_top (by norm_num) (by simp))
          data.prepared.multiplicity_upper
      _ = (2 * (2 ^ data.prepared.level : ENNReal)) *
          ((data.cells.activeCells.card : ENNReal) *
            data.cells.cellMass) := by rw [data.cells.fine_union_volume]
  have hregion := full.lineHitRegion_mass_ledger hquery
  have hexactMassLower :
      (2 ^ data.prepared.level : ENNReal) *
          volume full.lineHitRegion ≤
        (full.lineHitCandidate hdelta).mass := by
    let exactLineHit := paperRestrictShadingToSet
      data.prepared.refined.shading full.lineHitRegion
        full.lineHitRegion_measurable
    have hexactUnion : exactLineHit.union = full.lineHitRegion := by
      ext point
      constructor
      · rintro ⟨index, hpoint⟩
        exact hpoint.2
      · intro hpoint
        rcases full.lineHitRegion_subset hpoint with ⟨index, hindex⟩
        exact ⟨index, hindex, hpoint⟩
    have hlower :
        (2 ^ data.prepared.level : ENNReal) *
            volume full.lineHitRegion ≤ exactLineHit.mass := by
      rw [← hexactUnion]
      apply Kakeya.Assouad.multiplicity_floor_le_mass
      intro point hpoint
      have hpointRegion : point ∈ full.lineHitRegion := by
        rw [← hexactUnion]
        exact hpoint
      change (2 ^ data.prepared.level : ENNReal) ≤
        (paperRestrictShadingToSet data.prepared.refined.shading
          full.lineHitRegion full.lineHitRegion_measurable
            ).pointMultiplicity point
      rw [paperPmRestrictShadingToSet full.lineHitRegion_measurable
        hpointRegion]
      exact data.prepared.multiplicity_lower point
        (full.lineHitRegion_subset hpointRegion)
    exact hlower.trans <| by
      apply Finset.sum_le_sum
      intro index _
      apply measure_mono
      rintro point ⟨hpointPrepared, hpointRegion⟩
      refine ⟨hpointPrepared, ?_⟩
      have hpointCandidate :=
        full.lineHitRegion_subset_candidate_union hdelta hpointRegion
      rw [lineHitCandidate, wz2RefinedShading_union_inter] at hpointCandidate
      exact hpointCandidate.2
  apply (ENNReal.mul_le_mul_iff_left data.cells.cellMass_pos.ne'
    data.cells.cellMass_ne_top).mp
  calc
    (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) *
          data.prepared.refined.shading.mass) * data.cells.cellMass =
        (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          ((data.cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal)))) *
          data.prepared.refined.shading.mass := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          ((data.cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal)))) *
          ((2 * (2 ^ data.prepared.level : ENNReal)) *
            ((data.cells.activeCells.card : ENNReal) *
              data.cells.cellMass)) :=
      mul_le_mul_left' hsourceVolume _
    _ = (2 * data.cells.cellMass *
          (2 ^ data.prepared.level : ENNReal)) *
        ((data.cells.activeCells.card : ENNReal) *
          (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
            ((data.cells.cellMass / 2) /
              (2 * (coverBudget : ENNReal))))) := by ring
    _ ≤ (2 * data.cells.cellMass *
          (2 ^ data.prepared.level : ENNReal)) *
        (ENNReal.ofReal (4 * queryScale) *
          volume full.lineHitRegion) :=
      mul_le_mul_left' hregion _
    _ = (2 * ENNReal.ofReal (4 * queryScale)) *
        (((2 ^ data.prepared.level : ENNReal) *
          volume full.lineHitRegion) * data.cells.cellMass) := by ring
    _ ≤ (2 * ENNReal.ofReal (4 * queryScale)) *
        ((full.lineHitCandidate hdelta).mass * data.cells.cellMass) :=
      mul_le_mul_left' (mul_le_mul_right' hexactMassLower _) _
    _ = ((2 * ENNReal.ofReal (4 * queryScale)) *
        (full.lineHitCandidate hdelta).mass) * data.cells.cellMass := by ring

/-- Restore a local interval-grain state immediately after the prepared-source
line-hit selection.  The mass loss contains only the geometric line factor
and inverse cover factor on the left, and the one-dimensional line-hit cost
on the right. -/
theorem prepared_lineHitCandidate_intervalLocalGrain
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss outputCandidateLoss queryScale
      tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) (hquery : 0 < queryScale)
    (hlineVolume : 0 < lineVolume) (hcoverBudget : 0 < coverBudget)
    {constant : ENNReal}
    (hcover : PureWZ2IntervalCoveringAt (full.lineHitCandidate hdelta)
      planeMap queryScale (Real.toNNReal queryScale)
      (Real.toNNReal tauScale) constant)
    (hfinalOutput : finalLoss ≤ outputCandidateLoss)
    (houtputCandidateLoss : 0 < outputCandidateLoss)
    (hrestore :
      proposition63Lemma43MassLoss
          (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
            (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))))
          (2 * ENNReal.ofReal (4 * queryScale)) *
        Kakeya.realRpowENN delta outputCandidateLoss ≤
          Kakeya.realRpowENN delta finalLoss) :
    ∃ restored : PureWZ2IntervalLocalGrainData
        (sigma := sigma) (outputLoss := outputCandidateLoss)
        (source := data.prepared.refined.shading) planeMap queryScale
        (Real.toNNReal queryScale) (Real.toNNReal tauScale) constant,
      restored.shading = full.lineHitCandidate hdelta := by
  let lineFactor :=
    ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2))
  let inverseCoverFactor :=
    ((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))
  let leftFactor := lineFactor * inverseCoverFactor
  let rightFactor := 2 * ENNReal.ofReal (4 * queryScale)
  have hlineFactorPos : 0 < lineFactor := by
    dsimp only [lineFactor]
    exact ENNReal.ofReal_pos.mpr <| div_pos hlineVolume <| by
      exact mul_pos (by norm_num) <| sq_pos_of_pos <|
        mul_pos (by norm_num) data.cells.scale_pos
  have hlineFactorTop : lineFactor ≠ ⊤ := by
    dsimp only [lineFactor]
    exact ENNReal.ofReal_ne_top
  have hinverseCoverPos : 0 < inverseCoverFactor := by
    dsimp only [inverseCoverFactor]
    exact ENNReal.div_pos (by norm_num) <|
      ENNReal.mul_ne_top (by norm_num) <| ENNReal.natCast_ne_top _
  have hinverseCoverTop : inverseCoverFactor ≠ ⊤ := by
    dsimp only [inverseCoverFactor]
    exact ENNReal.div_ne_top (by norm_num) <|
      (ENNReal.mul_pos (by norm_num) <|
        (by exact_mod_cast (Nat.ne_of_gt hcoverBudget))).ne'
  have hleftPos : 0 < leftFactor := by
    exact ENNReal.mul_pos hlineFactorPos.ne' hinverseCoverPos.ne'
  have hleftTop : leftFactor ≠ ⊤ :=
    ENNReal.mul_ne_top hlineFactorTop hinverseCoverTop
  have hrightTop : rightFactor ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hmass : leftFactor * data.prepared.refined.shading.mass ≤
      rightFactor * (full.lineHitCandidate hdelta).mass := by
    simpa only [leftFactor, lineFactor, inverseCoverFactor, rightFactor] using
      full.prepared_lineHitCandidate_mass_ledger hdelta hquery
  let massLoss := proposition63Lemma43MassLoss leftFactor rightFactor
  have hmassRetention : massLoss⁻¹ *
      data.prepared.refined.shading.mass ≤
        (full.lineHitCandidate hdelta).mass :=
    proposition63Lemma43MassLoss_inv_mul_le
      hleftPos hleftTop hrightTop hmass
  exact intervalLocalGrain_of_mass_ledger planeMap
    data.prepared.refined.extremal data.prepared.refined.cwa
    (full.lineHitCandidate_subshading hdelta)
    (full.lineHitCandidate_cubical hdelta) hcover massLoss
    (proposition63Lemma43MassLoss_pos _ _)
    (proposition63Lemma43MassLoss_ne_top hleftPos hrightTop)
    hmassRetention hfinalOutput houtputCandidateLoss
    (by simpa only [massLoss, leftFactor, lineFactor, inverseCoverFactor,
      rightFactor] using hrestore)

/-- Full multiplicative mass ledger for the cubical line-hit candidate.
The common balanced-cell mass cancels, leaving only the two sticky/re-entry
retention factors, one multiplicity-preparation loss, and the one-dimensional
line-hit factors. -/
theorem lineHitCandidate_mass_ledger
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) (hquery : 0 < queryScale) :
    let lineFactor :=
      ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2))
    let inverseCoverFactor :=
      ((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))
    let retainedFactor := data.secondRetainedFactor *
      ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
      data.firstRetainedFactor
    let lossFactor := data.reentry.regularized.regularizationLoss *
      data.prepared.preparationLoss
    (lineFactor * inverseCoverFactor * retainedFactor) *
        data.current.mass ≤
      (lossFactor * (2 * ENNReal.ofReal (4 * queryScale))) *
        (full.lineHitCandidate hdelta).mass := by
  dsimp only
  have hsourceMass := data.prepared_mass_ledger
  have hsourceVolume : data.prepared.refined.shading.mass ≤
      (2 * (2 ^ data.prepared.level : ENNReal)) *
        ((data.cells.activeCells.card : ENNReal) *
          data.cells.cellMass) := by
    calc
      data.prepared.refined.shading.mass ≤
          (2 * (2 ^ data.prepared.level : ENNReal)) *
            volume data.prepared.refined.shading.union :=
        Kakeya.Assouad.mass_le_multiplicity_vol
          (ENNReal.mul_ne_top (by norm_num) (by simp))
          data.prepared.multiplicity_upper
      _ = (2 * (2 ^ data.prepared.level : ENNReal)) *
          ((data.cells.activeCells.card : ENNReal) *
            data.cells.cellMass) := by rw [data.cells.fine_union_volume]
  have hregion := full.lineHitRegion_mass_ledger hquery
  have hexactMassLower :
      (2 ^ data.prepared.level : ENNReal) *
          volume full.lineHitRegion ≤
        (full.lineHitCandidate hdelta).mass := by
    let exactLineHit := paperRestrictShadingToSet
      data.prepared.refined.shading full.lineHitRegion
        full.lineHitRegion_measurable
    have hexactUnion : exactLineHit.union = full.lineHitRegion := by
      ext point
      constructor
      · rintro ⟨index, hpoint⟩
        exact hpoint.2
      · intro hpoint
        rcases full.lineHitRegion_subset hpoint with ⟨index, hindex⟩
        exact ⟨index, hindex, hpoint⟩
    have hlower :
        (2 ^ data.prepared.level : ENNReal) *
            volume full.lineHitRegion ≤ exactLineHit.mass := by
      rw [← hexactUnion]
      apply Kakeya.Assouad.multiplicity_floor_le_mass
      intro point hpoint
      have hpointRegion : point ∈ full.lineHitRegion := by
        rw [← hexactUnion]
        exact hpoint
      change (2 ^ data.prepared.level : ENNReal) ≤
        (paperRestrictShadingToSet data.prepared.refined.shading
          full.lineHitRegion full.lineHitRegion_measurable
            ).pointMultiplicity point
      rw [paperPmRestrictShadingToSet full.lineHitRegion_measurable
        hpointRegion]
      exact data.prepared.multiplicity_lower point
        (full.lineHitRegion_subset hpointRegion)
    exact hlower.trans <| by
      apply Finset.sum_le_sum
      intro index _
      apply measure_mono
      rintro point ⟨hpointPrepared, hpointRegion⟩
      refine ⟨hpointPrepared, ?_⟩
      have hpointCandidate :=
        full.lineHitRegion_subset_candidate_union hdelta hpointRegion
      rw [lineHitCandidate, wz2RefinedShading_union_inter] at hpointCandidate
      exact hpointCandidate.2
  apply (ENNReal.mul_le_mul_iff_left data.cells.cellMass_pos.ne'
    data.cells.cellMass_ne_top).mp
  calc
    ((ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) *
          (data.secondRetainedFactor *
            ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
            data.firstRetainedFactor)) *
          data.current.mass) * data.cells.cellMass =
        (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          ((data.cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal)))) *
          ((data.secondRetainedFactor *
            ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
            data.firstRetainedFactor) *
            data.current.mass) := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          ((data.cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal)))) *
          ((data.reentry.regularized.regularizationLoss *
            data.prepared.preparationLoss) *
            data.prepared.refined.shading.mass) :=
      mul_le_mul_left' hsourceMass _
    _ = (data.reentry.regularized.regularizationLoss *
          data.prepared.preparationLoss) *
        (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          ((data.cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal))) *
          data.prepared.refined.shading.mass) := by ring
    _ ≤ (data.reentry.regularized.regularizationLoss *
          data.prepared.preparationLoss) *
        (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          ((data.cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal))) *
          ((2 * (2 ^ data.prepared.level : ENNReal)) *
            ((data.cells.activeCells.card : ENNReal) *
              data.cells.cellMass))) :=
      mul_le_mul_left' (mul_le_mul_left' hsourceVolume _) _
    _ = (data.reentry.regularized.regularizationLoss *
          data.prepared.preparationLoss) *
        ((2 * data.cells.cellMass *
            (2 ^ data.prepared.level : ENNReal)) *
          ((data.cells.activeCells.card : ENNReal) *
            (ENNReal.ofReal
              (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
              ((data.cells.cellMass / 2) /
                (2 * (coverBudget : ENNReal)))))) := by ring
    _ ≤ (data.reentry.regularized.regularizationLoss *
          data.prepared.preparationLoss) *
        ((2 * data.cells.cellMass *
            (2 ^ data.prepared.level : ENNReal)) *
          (ENNReal.ofReal (4 * queryScale) *
            volume full.lineHitRegion)) :=
      mul_le_mul_left' (mul_le_mul_left' hregion _) _
    _ = (data.reentry.regularized.regularizationLoss *
          data.prepared.preparationLoss *
          (2 * ENNReal.ofReal (4 * queryScale))) *
        (((2 ^ data.prepared.level : ENNReal) *
          volume full.lineHitRegion) * data.cells.cellMass) := by ring
    _ ≤ (data.reentry.regularized.regularizationLoss *
          data.prepared.preparationLoss *
          (2 * ENNReal.ofReal (4 * queryScale))) *
        ((full.lineHitCandidate hdelta).mass * data.cells.cellMass) :=
      mul_le_mul_left' (mul_le_mul_right' hexactMassLower _) _
    _ = (((data.reentry.regularized.regularizationLoss *
            data.prepared.preparationLoss) *
          (2 * ENNReal.ofReal (4 * queryScale))) *
        (full.lineHitCandidate hdelta).mass) * data.cells.cellMass := by ring

/-- Zero-extend the selected-family line-hit candidate and restore all tube
memberships of the first point-cover shading at its geometric union. -/
def finalCandidate
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    WZ1PaperTubeShading initialNormalized.croppedFamily :=
  paperCommonSpatialHull data.first.shading <|
    data.reentry.extendCandidate (full.lineHitCandidate hdelta)

theorem finalCandidate_subshading
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    PaperIsSubshading (full.finalCandidate hdelta) data.current := by
  intro index point hpoint
  exact data.first.subshading index
    (paperCommonSpatialHull_subshading _ _ index hpoint)

theorem finalCandidate_cubical
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    WZ1PaperIsCubicalShading (full.finalCandidate hdelta) := by
  apply paperCommonSpatialHull_cubical data.first.extremal.cubical
  exact extendShading_cubical data.reentry.regularized.selected
    (full.lineHitCandidate_cubical hdelta)

theorem finalCandidate_union
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    (full.finalCandidate hdelta).union =
      (full.lineHitCandidate hdelta).union := by
  let selectedCandidate := full.lineHitCandidate hdelta
  have hselectedSub : PaperIsSubshading selectedCandidate
      data.reentry.normalization.croppedRefined := fun index =>
    (full.lineHitCandidate_subshading hdelta index).trans
      (data.prepared.refined.subshading index)
  have hambientSub : PaperIsSubshading
      (data.reentry.extendCandidate selectedCandidate) data.first.shading :=
    data.reentry.extendCandidate_subshading hselectedSub
  calc
    (full.finalCandidate hdelta).union =
        (data.reentry.extendCandidate selectedCandidate).union :=
      paperCommonSpatialHull_union hambientSub
    _ = selectedCandidate.union := data.reentry.extendCandidate_union _

theorem finalCandidate_mass_ledger
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) (hquery : 0 < queryScale) :
    let lineFactor :=
      ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2))
    let inverseCoverFactor :=
      ((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))
    let retainedFactor := data.secondRetainedFactor *
      ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
      data.firstRetainedFactor
    let lossFactor := data.reentry.regularized.regularizationLoss *
      data.prepared.preparationLoss
    (lineFactor * inverseCoverFactor * retainedFactor) *
        data.current.mass ≤
      (lossFactor * (2 * ENNReal.ofReal (4 * queryScale))) *
        (full.finalCandidate hdelta).mass := by
  dsimp only
  have hselected := full.lineHitCandidate_mass_ledger hdelta hquery
  have hmass : (full.lineHitCandidate hdelta).mass ≤
      (full.finalCandidate hdelta).mass := by
    let selectedCandidate := full.lineHitCandidate hdelta
    have hselectedSub : PaperIsSubshading selectedCandidate
        data.reentry.normalization.croppedRefined := fun index =>
      (full.lineHitCandidate_subshading hdelta index).trans
        (data.prepared.refined.subshading index)
    have hambientSub : PaperIsSubshading
        (data.reentry.extendCandidate selectedCandidate) data.first.shading :=
      data.reentry.extendCandidate_subshading hselectedSub
    calc
      (full.lineHitCandidate hdelta).mass =
          (data.reentry.extendCandidate selectedCandidate).mass :=
        (data.reentry.extendCandidate_mass selectedCandidate).symm
      _ ≤ (full.finalCandidate hdelta).mass :=
        paperCommonSpatialHull_mass_lower hambientSub
  exact hselected.trans <| mul_le_mul_left' hmass _

/-- Restore extremality and CWA immediately on the final nested interval
candidate.  This is the exact result type consumed by the finite interval
iterator. -/
theorem finalCandidate_intervalLocalGrain
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss outputLoss queryScale tauScale
      sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) (hquery : 0 < queryScale)
    (currentLoss : ℝ)
    (hcurrentExtremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      initialNormalized.croppedFamily data.current)
    (hcurrentCWA : WZ2PaperConvexWolffBound
      initialNormalized.croppedFamily
      (Kakeya.realRpowENN delta (-currentLoss)))
    (constant : ENNReal)
    (hcover : PureWZ2IntervalCoveringAt (full.finalCandidate hdelta)
      planeMap queryScale (Real.toNNReal queryScale)
      (Real.toNNReal tauScale) constant)
    (leftFactor rightFactor : ENNReal)
    (hleft : leftFactor ≤
      ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
        (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) *
        (data.secondRetainedFactor *
          ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
          data.firstRetainedFactor))
    (hright :
      (data.reentry.regularized.regularizationLoss *
        data.prepared.preparationLoss) *
          (2 * ENNReal.ofReal (4 * queryScale)) ≤ rightFactor)
    (hleftPos : 0 < leftFactor)
    (hleftTop : leftFactor ≠ ⊤)
    (hrightTop : rightFactor ≠ ⊤)
    (hcurrentOutput : currentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss leftFactor rightFactor *
      Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta currentLoss) :
    ∃ restored : PureWZ2IntervalLocalGrainData
        (sigma := sigma) (outputLoss := outputLoss)
        (source := data.current) planeMap queryScale
        (Real.toNNReal queryScale) (Real.toNNReal tauScale) constant,
      restored.shading = full.finalCandidate hdelta := by
  have hmass : leftFactor * data.current.mass ≤
      rightFactor * (full.finalCandidate hdelta).mass := by
    calc
      leftFactor * data.current.mass ≤
          (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
            (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) *
            (data.secondRetainedFactor *
              ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
              data.firstRetainedFactor)) *
            data.current.mass :=
        mul_le_mul_right' hleft _
      _ ≤ ((data.reentry.regularized.regularizationLoss *
              data.prepared.preparationLoss) *
            (2 * ENNReal.ofReal (4 * queryScale))) *
          (full.finalCandidate hdelta).mass :=
        full.finalCandidate_mass_ledger hdelta hquery
      _ ≤ rightFactor * (full.finalCandidate hdelta).mass :=
        mul_le_mul_right' hright _
  let massLoss := proposition63Lemma43MassLoss leftFactor rightFactor
  have hmassRetention : massLoss⁻¹ *
      data.current.mass ≤
        (full.finalCandidate hdelta).mass :=
    proposition63Lemma43MassLoss_inv_mul_le
      hleftPos hleftTop hrightTop hmass
  exact intervalLocalGrain_of_mass_ledger planeMap
    hcurrentExtremal hcurrentCWA
    (full.finalCandidate_subshading hdelta)
    (full.finalCandidate_cubical hdelta) hcover massLoss
    (proposition63Lemma43MassLoss_pos _ _)
    (proposition63Lemma43MassLoss_ne_top hleftPos hrightTop)
    hmassRetention hcurrentOutput houtputLoss
    (by simpa only [massLoss] using hrestore)

/-- Iterator-facing form of the nested pair step.  It exposes precisely the
subshading, cubicality, restored extremality/CWA, interval estimate, and mass
ledger expected by `finite_interval_covering_iteration_of_mass_pos`. -/
theorem finalCandidate_for_interval_iteration
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss outputLoss queryScale tauScale
      sqrtScale spatialScale variationScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) (hquery : 0 < queryScale)
    (currentLoss : ℝ)
    (hcurrentExtremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      initialNormalized.croppedFamily data.current)
    (hcurrentCWA : WZ2PaperConvexWolffBound
      initialNormalized.croppedFamily
      (Kakeya.realRpowENN delta (-currentLoss)))
    (exactConstant targetConstant : ENNReal)
    (hcover : PureWZ2IntervalCoveringAt (full.finalCandidate hdelta)
      planeMap queryScale (Real.toNNReal queryScale)
      (Real.toNNReal tauScale) exactConstant)
    (hconstant : exactConstant ≤ targetConstant)
    (leftFactor rightFactor : ENNReal)
    (hleft : leftFactor ≤
      ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
        (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) *
        (data.secondRetainedFactor *
          ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
          data.firstRetainedFactor))
    (hright :
      (data.reentry.regularized.regularizationLoss *
        data.prepared.preparationLoss) *
          (2 * ENNReal.ofReal (4 * queryScale)) ≤ rightFactor)
    (hleftPos : 0 < leftFactor)
    (hleftTop : leftFactor ≠ ⊤)
    (hrightTop : rightFactor ≠ ⊤)
    (hcurrentOutput : currentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss leftFactor rightFactor *
      Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta currentLoss)
    (coefficient : NNReal)
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hvariation : (coefficient : ℝ) * spatialScale ≤ variationScale) :
    ∃ next : WZ1PaperTubeShading initialNormalized.croppedFamily,
      PaperIsSubshading next data.current ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union,
        next.pointMultiplicity point = data.current.pointMultiplicity point) ∧
      WZ2PaperCroppedIsExtremal sigma outputLoss
        initialNormalized.croppedFamily next ∧
      WZ2PaperConvexWolffBound initialNormalized.croppedFamily
        (Kakeya.realRpowENN delta (-outputLoss)) ∧
      PureWZ2IntervalCoveringAt next planeMap queryScale
        (Real.toNNReal queryScale) (Real.toNNReal tauScale) targetConstant ∧
      leftFactor * data.current.mass ≤ rightFactor * next.mass ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) := by
  rcases full.finalCandidate_intervalLocalGrain hdelta hquery currentLoss
      hcurrentExtremal hcurrentCWA exactConstant hcover leftFactor
      rightFactor hleft hright hleftPos hleftTop hrightTop hcurrentOutput
      houtputLoss hrestore with ⟨restored, hrestored⟩
  have hsub : PaperIsSubshading restored.shading data.current := by
    rw [hrestored]
    exact full.finalCandidate_subshading hdelta
  have hcubical : WZ1PaperIsCubicalShading restored.shading := by
    rw [hrestored]
    exact full.finalCandidate_cubical hdelta
  refine ⟨restored.shading, hsub, hcubical, ?_, restored.extremal,
    restored.cwa, ?_, ?_, ?_⟩
  · intro point hpoint
    rw [hrestored] at hpoint ⊢
    exact (paperCommonSpatialHull_pointMultiplicity_eq data.first.shading
      (data.reentry.extendCandidate (full.lineHitCandidate hdelta)) point
      hpoint).trans (data.first_multiplicity point <| by
        exact paperSubshading_union
          (paperCommonSpatialHull_subshading _ _) hpoint)
  · exact pureWZ2IntervalCoveringAt_mono_constant hconstant
      restored.interval_covering
  · calc
      leftFactor * data.current.mass ≤
          rightFactor * (full.finalCandidate hdelta).mass := by
        exact_mod_cast (by
          have hmassLoss := full.finalCandidate_mass_ledger hdelta hquery
          exact (mul_le_mul_right' hleft data.current.mass).trans <|
            hmassLoss.trans (mul_le_mul_right' hright _))
      _ = rightFactor * restored.shading.mass := by rw [hrestored]
  · intro first hfirst second hsecond hdistance
    exact (hplaneLipschitz.dist_le_mul first second).trans <|
      (mul_le_mul_of_nonneg_left hdistance coefficient.coe_nonneg).trans
        hvariation

/-- The first arbitrary-`tauScale` estimate applies at every actual good-line
point in every active cell.  This is the exact input to the existing
`LineHitData.region_interval_covering` theorem. -/
theorem tauCoverAtLineParameters
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hquery : 0 < queryScale)
    (htau : 0 ≤ tauScale)
    (htauSqrt : tauScale ≤ Real.sqrt queryScale)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (K : ℝ) (hK : 1 ≤ K)
    (hplaneLipschitz : ∀ first ∈ data.prepared.refined.shading.union,
      ∀ second ∈ data.prepared.refined.shading.union,
        dist (planeMap first) (planeMap second) ≤ K * dist first second) :
    ∀ cell, ∀ hcell : cell ∈ data.cells.activeCells,
      ∀ parameter ∈ (full.cellData ⟨cell, hcell⟩).lineParameters,
        (Metric.externalCoveringNumber (Real.toNNReal queryScale)
          (scalarProjection
            (planeMap (data.cells.cellRep cell hcell))
            ((data.prepared.refined.shading.union ∩
                wz1PaperGridCube sqrtScale cell) ∩
              Metric.closedBall
                ((full.cellData ⟨cell, hcell⟩).anchor +
                  parameter • planeMap (data.cells.cellRep cell hcell))
                tauScale)) : ENNReal) ≤
          (2 * Nat.ceil ((2 * K * queryScale) / queryScale) + 2 : ENNReal) *
            tauConstant := by
  intro cell hcell parameter hparameter
  let center := (full.cellData ⟨cell, hcell⟩).anchor +
    parameter • planeMap (data.cells.cellRep cell hcell)
  have hcenterPrepared : center ∈ data.prepared.refined.shading.union :=
    (full.cellData ⟨cell, hcell⟩).good_subset hparameter |>.1
  have hcellCenterPrepared := data.cells.cellRep_in_union cell hcell
  have hcenterCell : center ∈ wz1PaperGridCube sqrtScale cell :=
    (full.cellData ⟨cell, hcell⟩).good_subset hparameter |>.2
  have hdistance : dist center (data.cells.cellRep cell hcell) ≤
      2 * Real.sqrt queryScale := by
    have hdiameter := wz1_paper_grid_cube_diameter_lt_two_rho
      data.cells.scale_pos hcenterCell (data.cells.cellRep_in_cell cell hcell)
    calc
      dist center (data.cells.cellRep cell hcell) ≤ 2 * sqrtScale :=
        hdiameter.le
      _ = 2 * Real.sqrt queryScale := by rw [hsqrtScale]
  let E := data.prepared.refined.shading.union ∩
    wz1PaperGridCube sqrtScale cell
  have hlocalSubset :
      scalarProjection (planeMap center)
          (E ∩ Metric.closedBall center tauScale) ⊆
        scalarProjection (planeMap center)
          (data.prepared.refined.shading.union ∩
            Metric.closedBall center tauScale) :=
    Set.image_mono <| Set.inter_subset_inter_left _ Set.inter_subset_left
  have hlocalMono :
      (Metric.externalCoveringNumber (Real.toNNReal queryScale)
          (scalarProjection (planeMap center)
            (E ∩ Metric.closedBall center tauScale)) : ENNReal) ≤
        (Metric.externalCoveringNumber (Real.toNNReal queryScale)
          (scalarProjection (planeMap center)
            (data.prepared.refined.shading.union ∩
              Metric.closedBall center tauScale)) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set hlocalSubset
  have hlocal :
      (Metric.externalCoveringNumber (Real.toNNReal queryScale)
          (scalarProjection (planeMap center)
            (E ∩ Metric.closedBall center tauScale)) : ENNReal) ≤
        tauConstant :=
    hlocalMono.trans <|
      data.firstCoverOnPrepared ⟨center, hcenterPrepared⟩
  have htransfer :=
    Kakeya.Assouad.wz1_lemma18_cell_normal_projection_transfer
      queryScale tauScale K hquery htau htauSqrt hK E planeMap center
      (data.cells.cellRep cell hcell) hdistance
      (hplaneLipschitz center hcenterPrepared
        (data.cells.cellRep cell hcell) hcellCenterPrepared)
  exact htransfer.2.trans <| mul_le_mul_left' hlocal _

/-- Assemble the interval estimate on the genuine line-hit region.  The
first point-centered cover is used only at the at-most-nine actual line
points selected in each relevant square-root cell. -/
theorem lineHitRegion_interval_covering
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hquery : 0 < queryScale)
    (htau : 0 < tauScale)
    (hqueryTau : queryScale ≤ tauScale)
    (htauSqrt : tauScale ≤ Real.sqrt queryScale)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (K : ℝ) (hK : 1 ≤ K)
    (hplaneLipschitz : ∀ first ∈ data.prepared.refined.shading.union,
      ∀ second ∈ data.prepared.refined.shading.union,
        dist (planeMap first) (planeMap second) ≤ K * dist first second)
    (spatialRadius normalError : ℝ)
    (hnormalError : 0 < normalError)
    (hnormalErrorTau : normalError ≤ tauScale)
    (neighborBudget : ℕ)
    (hneighbor : ∀ center,
      (full.lineHitRelevantCells center spatialRadius).card ≤ neighborBudget)
    (hcentered : ∀ center,
      ∀ cell, ∀ hcellRelevant :
          cell ∈ full.lineHitRelevantCells center spatialRadius,
        ∀ point ∈
          full.cellLineHitRegion cell ∩
            Metric.closedBall center spatialRadius,
          dist
              (inner ℝ (point - center) (planeMap center))
              (inner ℝ (point - center)
                (planeMap (data.cells.cellRep cell
                  ((Finset.mem_filter.mp hcellRelevant).1)))) ≤
            normalError) :
    ∀ center : Point3, ∀ intervalCenter : ℝ,
      (Metric.externalCoveringNumber (Real.toNNReal queryScale)
        (scalarProjection (planeMap center)
            (full.lineHitRegion ∩ Metric.closedBall center spatialRadius) ∩
          Metric.closedBall intervalCenter tauScale) : ENNReal) ≤
        nestedRegionIntervalBound queryScale normalError K neighborBudget
          tauConstant := by
  intro center intervalCenter
  let relevant := full.lineHitRelevantCells center spatialRadius
  let piece : (ℤ × ℤ × ℤ) → Set Point3 := fun cell =>
    full.cellLineHitRegion cell ∩ Metric.closedBall center spatialRadius
  let normal : (ℤ × ℤ × ℤ) → Point3 := fun cell =>
    if hcell : cell ∈ data.cells.activeCells then
      planeMap (data.cells.cellRep cell hcell)
    else planeMap center
  let targetSet := full.lineHitRegion ∩
    Metric.closedBall center spatialRadius
  have hdecompose : ∀ point ∈ targetSet,
      ∃ cell ∈ relevant, point ∈ piece cell := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint.1 with
      ⟨cell, hcellActive, hpointCell⟩
    have hcellRelevant : cell ∈ relevant :=
      Finset.mem_filter.mpr
        ⟨hcellActive, ⟨point, hpointCell, hpoint.2⟩⟩
    exact ⟨cell, hcellRelevant, hpointCell, hpoint.2⟩
  have hlocal : ∀ cell ∈ relevant, ∀ sourceCenter : ℝ,
      (Metric.externalCoveringNumber (Real.toNNReal queryScale)
        (scalarProjection (normal cell) (piece cell) ∩
          Metric.closedBall sourceCenter tauScale) : ENNReal) ≤
        nestedCellIntervalBound queryScale K tauConstant := by
    intro cell hcellRelevant sourceCenter
    have hcellActive : cell ∈ data.cells.activeCells :=
      (Finset.mem_filter.mp hcellRelevant).1
    have hpiece : piece cell ⊆ full.cellLineHitRegion cell :=
      Set.inter_subset_left
    have hmono :
        (Metric.externalCoveringNumber (Real.toNNReal queryScale)
          (scalarProjection (normal cell) (piece cell) ∩
            Metric.closedBall sourceCenter tauScale) : ENNReal) ≤
          (Metric.externalCoveringNumber (Real.toNNReal queryScale)
            (scalarProjection
                (planeMap (data.cells.cellRep cell hcellActive))
                (full.cellLineHitRegion cell) ∩
              Metric.closedBall sourceCenter tauScale) : ENNReal) := by
      have hnormal : normal cell =
          planeMap (data.cells.cellRep cell hcellActive) := by
        simp [normal, hcellActive]
      rw [hnormal]
      exact_mod_cast Metric.externalCoveringNumber_mono_set
        (Set.inter_subset_inter (Set.image_mono hpiece) Set.Subset.rfl)
    have hcellBound := (full.lineHits ⟨cell, hcellActive⟩).region_interval_covering
      (full.cellData ⟨cell, hcellActive⟩) hquery htau hqueryTau
      ((2 * Nat.ceil ((2 * K * queryScale) / queryScale) + 2 : ENNReal) *
        tauConstant)
      (full.tauCoverAtLineParameters hquery htau.le htauSqrt hsqrtScale K
        hK hplaneLipschitz cell hcellActive) sourceCenter
    have hmono' :
        (Metric.externalCoveringNumber (Real.toNNReal queryScale)
          (scalarProjection
              (planeMap (data.cells.cellRep cell hcellActive))
              (piece cell) ∩ Metric.closedBall sourceCenter tauScale) :
            ENNReal) ≤
          (Metric.externalCoveringNumber (Real.toNNReal queryScale)
            (scalarProjection
                (planeMap (data.cells.cellRep cell hcellActive))
                (full.cellLineHitRegion cell) ∩
              Metric.closedBall sourceCenter tauScale) : ENNReal) := by
      simpa only [normal, dif_pos hcellActive] using hmono
    have hcellBound' :
        (Metric.externalCoveringNumber (Real.toNNReal queryScale)
          (scalarProjection
              (planeMap (data.cells.cellRep cell hcellActive))
              (full.cellLineHitRegion cell) ∩
            Metric.closedBall sourceCenter tauScale) : ENNReal) ≤
          nestedCellIntervalBound queryScale K tauConstant := by
      rw [nestedCellIntervalBound_eq]
      simpa only [full.cellLineHitRegion_eq cell hcellActive] using hcellBound
    have hresult := hmono'.trans hcellBound'
    simpa only [normal, dif_pos hcellActive] using hresult
  have hraw := Kakeya.Assouad.wz1_lemma18_centered_finite_cell_interval_transfer
    relevant piece normal targetSet center (planeMap center) queryScale
    tauScale normalError
    (nestedCellIntervalBound queryScale K tauConstant)
    hquery htau hnormalError hnormalErrorTau hdecompose
    (by
      intro cell hcellRelevant point hpoint
      have hcellActive : cell ∈ data.cells.activeCells :=
        (Finset.mem_filter.mp hcellRelevant).1
      have hnormal : normal cell =
          planeMap (data.cells.cellRep cell hcellActive) := by
        simp [normal, hcellActive]
      rw [hnormal]
      exact hcentered center cell hcellRelevant point hpoint)
    hlocal intervalCenter
  exact hraw.trans <| by
    rw [nestedRegionIntervalBound_eq]
    gcongr
    exact_mod_cast hneighbor center

/-- Transfer the interval estimate from the genuine line-hit region to its
ambient-scale cubical hull. -/
theorem lineHitCandidate_interval_covering
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta)
    (hquery : 0 < queryScale)
    (htau : 0 < tauScale)
    (hqueryTau : queryScale ≤ tauScale)
    (htauSqrt : tauScale ≤ Real.sqrt queryScale)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (K : ℝ) (hK : 1 ≤ K)
    (hplaneLipschitz : ∀ first ∈ data.prepared.refined.shading.union,
      ∀ second ∈ data.prepared.refined.shading.union,
        dist (planeMap first) (planeMap second) ≤ K * dist first second)
    (hplaneUnit : ∀ point ∈ data.prepared.refined.shading.union,
      ‖planeMap point‖ = 1)
    (spatialRadius normalError : ℝ)
    (hspatialRadius : Real.sqrt queryScale + delta * Real.sqrt 3 ≤
      spatialRadius)
    (hnormalError : 0 < normalError)
    (hnormalErrorTau : normalError ≤ tauScale)
    (hhullTau : delta * Real.sqrt 3 ≤ tauScale)
    (neighborBudget : ℕ)
    (hneighbor : ∀ center,
      (full.lineHitRelevantCells center spatialRadius).card ≤ neighborBudget)
    (hcentered : ∀ center,
      ∀ cell, ∀ hcellRelevant :
          cell ∈ full.lineHitRelevantCells center spatialRadius,
        ∀ point ∈
          full.cellLineHitRegion cell ∩
            Metric.closedBall center spatialRadius,
          dist
              (inner ℝ (point - center) (planeMap center))
              (inner ℝ (point - center)
                (planeMap (data.cells.cellRep cell
                  ((Finset.mem_filter.mp hcellRelevant).1)))) ≤
            normalError) :
    PureWZ2IntervalCoveringAt (full.lineHitCandidate hdelta) planeMap
      queryScale (Real.toNNReal queryScale) (Real.toNNReal tauScale)
      (nestedCandidateIntervalBound delta queryScale normalError K
        neighborBudget tauConstant) := by
  let regionBound : ENNReal := nestedRegionIntervalBound
    queryScale normalError K neighborBudget tauConstant
  have hregion : ∀ center : Point3, ∀ intervalCenter : ℝ,
      (Metric.externalCoveringNumber (Real.toNNReal queryScale)
        (scalarProjection (planeMap center)
            (full.lineHitRegion ∩ Metric.closedBall center spatialRadius) ∩
          Metric.closedBall intervalCenter tauScale) : ENNReal) ≤
        regionBound := by
    intro center intervalCenter
    exact full.lineHitRegion_interval_covering hquery htau hqueryTau
      htauSqrt hsqrtScale K hK hplaneLipschitz spatialRadius normalError
      hnormalError hnormalErrorTau neighborBudget hneighbor hcentered center
      intervalCenter
  intro center intervalCenter
  let target := scalarProjection (planeMap center)
    ((full.lineHitCandidate hdelta).union ∩
      Metric.closedBall (center : Point3) (Real.sqrt queryScale))
  let sourceSet := scalarProjection (planeMap center)
    (full.lineHitRegion ∩ Metric.closedBall (center : Point3) spatialRadius)
  have hcenterPrepared : (center : Point3) ∈
      data.prepared.refined.shading.union := by
    rcases center.property with ⟨index, hindex⟩
    exact ⟨index, full.lineHitCandidate_subshading hdelta index hindex⟩
  have hclose : ∀ value ∈ target,
      ∃ sourceValue ∈ sourceSet,
        dist value sourceValue ≤ delta * Real.sqrt 3 := by
    intro value hvalue
    rcases hvalue with ⟨point, hpoint, rfl⟩
    rcases full.lineHitCandidate_close_to_lineHitRegion hdelta point
        hpoint.1 with ⟨sourcePoint, hsourcePoint, hdistance⟩
    let sourceValue := inner ℝ sourcePoint (planeMap center)
    have hsourceBall : sourcePoint ∈
        Metric.closedBall (center : Point3) spatialRadius := by
      rw [Metric.mem_closedBall]
      calc
        dist sourcePoint center ≤ dist sourcePoint point + dist point center :=
          dist_triangle _ _ _
        _ ≤ delta * Real.sqrt 3 + Real.sqrt queryScale := by
          exact add_le_add (by simpa [dist_comm] using hdistance) hpoint.2
        _ = Real.sqrt queryScale + delta * Real.sqrt 3 := by ring
        _ ≤ spatialRadius := hspatialRadius
    have hsourceValue : sourceValue ∈ sourceSet :=
      ⟨sourcePoint, ⟨hsourcePoint, hsourceBall⟩, rfl⟩
    have hprojectionDistance :
        dist (inner ℝ point (planeMap center)) sourceValue ≤
          delta * Real.sqrt 3 := by
      rw [Real.dist_eq]
      have hinner := abs_real_inner_le_norm
        (point - sourcePoint) (planeMap center)
      have hidentity :
          inner ℝ point (planeMap center) - sourceValue =
            inner ℝ (point - sourcePoint) (planeMap center) := by
        simp [sourceValue, inner_sub_left]
      rw [hidentity]
      calc
        |inner ℝ (point - sourcePoint) (planeMap center)| ≤
            ‖point - sourcePoint‖ * ‖planeMap center‖ := hinner
        _ = dist point sourcePoint := by
          rw [hplaneUnit center hcenterPrepared, mul_one, dist_eq_norm]
        _ ≤ delta * Real.sqrt 3 := hdistance
    exact ⟨sourceValue, hsourceValue, hprojectionDistance⟩
  have hsource : ∀ sourceCenter : ℝ,
      (Metric.externalCoveringNumber (Real.toNNReal queryScale)
        (sourceSet ∩ Metric.closedBall sourceCenter tauScale) : ENNReal) ≤
        regionBound := hregion center
  have hfinal :=
    Kakeya.Assouad.wz1_lemma18_close_projection_interval_transfer
      target sourceSet queryScale tauScale (delta * Real.sqrt 3) regionBound
      hquery htau (mul_pos hdelta (Real.sqrt_pos.mpr (by norm_num)))
      hhullTau hclose hsource intervalCenter
  have hqueryCoe : (Real.toNNReal queryScale : ℝ) = queryScale :=
    Real.coe_toNNReal _ hquery.le
  have htauCoe : (Real.toNNReal tauScale : ℝ) = tauScale :=
    Real.coe_toNNReal _ htau.le
  simpa only [target, sourceSet, regionBound, hqueryCoe, htauCoe,
    nestedCandidateIntervalBound_eq] using hfinal

/-- The literal square-root grid gives the full candidate a uniform local
neighbor budget.  The bound is the fixed constant `13^3`; it is not a cover
of a square-root cell by `tauScale` balls. -/
theorem lineHitCandidate_neighbor_bound
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hquery : 0 < queryScale)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale) :
    ∀ center,
      (full.lineHitRelevantCells center
        (2 * Real.sqrt queryScale)).card ≤ 13 ^ 3 := by
  intro center
  have hsqrtPos : 0 < sqrtScale := by
    rw [hsqrtScale]
    exact Real.sqrt_pos.mpr hquery
  apply full.lineHitRelevantCells_card_le_fixed hsqrtPos center
  rw [hsqrtScale]
  have hsqrtOne : 1 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg 3]
  have hsqrtQuery : 0 ≤ Real.sqrt queryScale := Real.sqrt_nonneg _
  nlinarith

/-- Centering the scalar projections converts Lipschitz variation on a
square-root cell into an `O(K * queryScale)` error. -/
theorem lineHitCandidate_centered_error
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hquery : 0 < queryScale)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (coefficient : NNReal)
    (hplaneLipschitz : LipschitzWith coefficient planeMap) :
    ∀ center, ∀ cell, ∀ hcellRelevant :
        cell ∈ full.lineHitRelevantCells center
          (2 * Real.sqrt queryScale),
      ∀ point ∈ full.cellLineHitRegion cell ∩
          Metric.closedBall center (2 * Real.sqrt queryScale),
        dist
            (inner ℝ (point - center) (planeMap center))
            (inner ℝ (point - center)
              (planeMap (data.cells.cellRep cell
                ((Finset.mem_filter.mp hcellRelevant).1)))) ≤
          8 * (coefficient : ℝ) * queryScale := by
  intro center cell hcellRelevant point hpoint
  have hcellActive : cell ∈ data.cells.activeCells :=
    (Finset.mem_filter.mp hcellRelevant).1
  have hpointCell : point ∈ wz1PaperGridCube sqrtScale cell :=
    full.cellLineHitRegion_subset_cell cell hcellActive hpoint.1
  have hpointRep : dist point (data.cells.cellRep cell hcellActive) ≤
      sqrtScale * Real.sqrt 3 :=
    wz1PaperGridCube_diameter
      (hsqrtScale.symm ▸ Real.sqrt_pos.mpr hquery) cell hpointCell
      (data.cells.cellRep_in_cell cell hcellActive)
  have hcenterRep : dist center (data.cells.cellRep cell hcellActive) ≤
      4 * Real.sqrt queryScale := by
    have hpointCenter : dist point center ≤ 2 * Real.sqrt queryScale :=
      Metric.mem_closedBall.mp hpoint.2
    have hsqrtThree : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    calc
      dist center (data.cells.cellRep cell hcellActive) ≤
          dist center point + dist point
            (data.cells.cellRep cell hcellActive) := dist_triangle _ _ _
      _ ≤ 2 * Real.sqrt queryScale + sqrtScale * Real.sqrt 3 := by
        gcongr
        simpa [dist_comm] using hpointCenter
      _ ≤ 4 * Real.sqrt queryScale := by
        rw [hsqrtScale]
        have hsqrtNonneg : 0 ≤ Real.sqrt queryScale := Real.sqrt_nonneg _
        nlinarith
  have hnormalDistance :
      dist (planeMap center)
          (planeMap (data.cells.cellRep cell hcellActive)) ≤
        4 * (coefficient : ℝ) * Real.sqrt queryScale := by
    exact (hplaneLipschitz.dist_le_mul center
      (data.cells.cellRep cell hcellActive)).trans <| by
        nlinarith [coefficient.coe_nonneg, hcenterRep,
          (dist_nonneg : 0 ≤ dist center
            (data.cells.cellRep cell hcellActive))]
  rw [Real.dist_eq]
  have hinner := abs_real_inner_le_norm (point - center)
    (planeMap center - planeMap (data.cells.cellRep cell hcellActive))
  have hidentity :
      inner ℝ (point - center) (planeMap center) -
          inner ℝ (point - center)
            (planeMap (data.cells.cellRep cell hcellActive)) =
        inner ℝ (point - center)
          (planeMap center - planeMap
            (data.cells.cellRep cell hcellActive)) := by
    rw [inner_sub_right]
  rw [hidentity]
  calc
    |inner ℝ (point - center)
        (planeMap center - planeMap
          (data.cells.cellRep cell hcellActive))| ≤
        ‖point - center‖ *
          ‖planeMap center -
            planeMap (data.cells.cellRep cell hcellActive)‖ := hinner
    _ = dist point center *
        dist (planeMap center)
          (planeMap (data.cells.cellRep cell hcellActive)) := by
      rw [dist_eq_norm, dist_eq_norm]
    _ ≤ (2 * Real.sqrt queryScale) *
        (4 * (coefficient : ℝ) * Real.sqrt queryScale) := by
      exact mul_le_mul (Metric.mem_closedBall.mp hpoint.2) hnormalDistance
        dist_nonneg (by positivity)
    _ = 8 * (coefficient : ℝ) * queryScale := by
      calc
        (2 * Real.sqrt queryScale) *
            (4 * (coefficient : ℝ) * Real.sqrt queryScale) =
          8 * (coefficient : ℝ) *
            (Real.sqrt queryScale * Real.sqrt queryScale) := by ring
        _ = 8 * (coefficient : ℝ) * queryScale := by
          rw [Real.mul_self_sqrt hquery.le]

/-- Interval covering with both local-cell bookkeeping obligations discharged
by the literal grid and the same global Lipschitz plane map. -/
theorem lineHitCandidate_interval_covering_of_lipschitz
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) (hquery : 0 < queryScale) (htau : 0 < tauScale)
    (hqueryTau : queryScale ≤ tauScale)
    (htauSqrt : tauScale ≤ Real.sqrt queryScale)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (coefficient : NNReal) (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneUnit : ∀ point ∈ data.prepared.refined.shading.union,
      ‖planeMap point‖ = 1)
    (hnormalErrorTau : 8 * (coefficient : ℝ) * queryScale ≤ tauScale)
    (hhullTau : delta * Real.sqrt 3 ≤ tauScale) :
    PureWZ2IntervalCoveringAt (full.lineHitCandidate hdelta) planeMap
      queryScale (Real.toNNReal queryScale) (Real.toNNReal tauScale)
      (nestedCandidateIntervalBound delta queryScale
        (8 * (coefficient : ℝ) * queryScale) (coefficient : ℝ)
        (13 ^ 3) tauConstant) := by
  apply full.lineHitCandidate_interval_covering hdelta hquery htau hqueryTau
    htauSqrt hsqrtScale (coefficient : ℝ) hcoefficientOne
    (fun first _ second _ => hplaneLipschitz.dist_le_mul first second)
    hplaneUnit (2 * Real.sqrt queryScale)
    (8 * (coefficient : ℝ) * queryScale)
  · have hhullSqrt : delta * Real.sqrt 3 ≤ Real.sqrt queryScale :=
      hhullTau.trans htauSqrt
    linarith
  · positivity
  · exact hnormalErrorTau
  · exact hhullTau
  · exact fun center => full.lineHitCandidate_neighbor_bound hquery
      hsqrtScale center
  · exact full.lineHitCandidate_centered_error hquery hsqrtScale coefficient
      hplaneLipschitz

/-- Run the interval tail on the actual coarse `rho` family, pull its
whole-cell candidate back through the outer sticky cover exactly once, and
only then restore extremality and CWA on the fixed fine/current family.
This is the iterator-facing endpoint of the paper-faithful two-HIGH chain. -/
theorem finalCandidate_for_fine_interval_iteration_of_lipschitz
    {fineDelta sigma fineInputLoss fineNormalizationLoss fineReentryLoss
      outerLoss coarseInputLoss coarseNormalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss tauScale sqrtScale outputLoss
      spatialScale variationScale : ℝ}
    {fineSource : PureWZ2ExtremalConfiguration
      sigma fineInputLoss fineDelta}
    {fineNormalizationExponent outerLogExponent
      coarseNormalizationExponent : ℕ}
    {fineNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := fineNormalizationLoss) fineSource
      fineNormalizationExponent}
    {fineCurrent : WZ1PaperTubeShading fineNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) fineNormalized fineCurrent)
    {rho : WZ2PaperRequestedScale fineDelta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    {coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      coarseNormalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := rho.1)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      coarseNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      coarseNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index))
    (current_sub_outer : ∀ index, data.current.carrier index ⊆
      outer.croppedCoarseShading.carrier (ancestorEmbedding index))
    (ancestorRetentionFactor : ENNReal)
    (current_retained_mass :
      ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
        data.current.mass)
    (hquery : 0 < rho.1)
    (htau : 0 < tauScale) (hqueryTau : rho.1 ≤ tauScale)
    (htauSqrt : tauScale ≤ Real.sqrt rho.1)
    (hsqrtScale : sqrtScale = Real.sqrt rho.1)
    (coefficient : NNReal) (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneUnit : ∀ point ∈ data.prepared.refined.shading.union,
      ‖planeMap point‖ = 1)
    (hnormalErrorTau : 8 * (coefficient : ℝ) * rho.1 ≤ tauScale)
    (hhullTau : rho.1 * Real.sqrt 3 ≤ tauScale)
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * fineDelta)
    (fineCurrentLoss : ℝ)
    (hcurrentExtremal : WZ2PaperCroppedIsExtremal sigma fineCurrentLoss
      fineNormalized.croppedFamily fineCurrent)
    (hcurrentCWA : WZ2PaperConvexWolffBound
      fineNormalized.croppedFamily
      (Kakeya.realRpowENN fineDelta (-fineCurrentLoss)))
    (targetConstant targetLeft targetRight : ENNReal)
    (hconstant : nestedCandidateIntervalBound rho.1 rho.1
      (8 * (coefficient : ℝ) * rho.1) (coefficient : ℝ)
      (13 ^ 3) tauConstant ≤ targetConstant)
    (hleft : targetLeft ≤
      proposition63DependentFinePullbackLeft fineReentry outer
        ancestorRetentionFactor
        (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) *
          (data.secondRetainedFactor *
            ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
            data.firstRetainedFactor)))
    (hright : proposition63DependentFinePullbackRight fineReentry
        ((data.reentry.regularized.regularizationLoss *
            data.prepared.preparationLoss) *
          (2 * ENNReal.ofReal (4 * rho.1))) ≤ targetRight)
    (hleftPos : 0 < targetLeft) (hleftTop : targetLeft ≠ ⊤)
    (hrightTop : targetRight ≠ ⊤)
    (hcurrentOutput : fineCurrentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss targetLeft targetRight *
        Kakeya.realRpowENN fineDelta outputLoss ≤
      Kakeya.realRpowENN fineDelta fineCurrentLoss)
    (hvariation : (coefficient : ℝ) * spatialScale ≤ variationScale) :
    ∃ next : WZ1PaperTubeShading fineNormalized.croppedFamily,
      PaperIsSubshading next fineCurrent ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union,
        next.pointMultiplicity point = fineCurrent.pointMultiplicity point) ∧
      WZ2PaperCroppedIsExtremal sigma outputLoss
        fineNormalized.croppedFamily next ∧
      WZ2PaperConvexWolffBound fineNormalized.croppedFamily
        (Kakeya.realRpowENN fineDelta (-outputLoss)) ∧
      PureWZ2IntervalCoveringAt next planeMap rho.1
        (Real.toNNReal rho.1) (Real.toNNReal tauScale) targetConstant ∧
      targetLeft * fineCurrent.mass ≤ targetRight * next.mass ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) := by
  let exactConstant := nestedCandidateIntervalBound rho.1 rho.1
    (8 * (coefficient : ℝ) * rho.1) (coefficient : ℝ)
    (13 ^ 3) tauConstant
  let coarseLeft :=
    ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
      (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) *
      (data.secondRetainedFactor *
        ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
        data.firstRetainedFactor)
  let coarseRight :=
    (data.reentry.regularized.regularizationLoss *
      data.prepared.preparationLoss) *
    (2 * ENNReal.ofReal (4 * rho.1))
  have hselectedCover :=
    full.lineHitCandidate_interval_covering_of_lipschitz hquery hquery htau
      hqueryTau htauSqrt hsqrtScale coefficient hcoefficientOne
      hplaneLipschitz hplaneUnit hnormalErrorTau hhullTau
  have hcoarseCover : PureWZ2IntervalCoveringAt
      (full.finalCandidate hquery) planeMap rho.1
      (Real.toNNReal rho.1) (Real.toNNReal tauScale) exactConstant := by
    intro point center
    have hpointSelected : (point : Point3) ∈
        (full.lineHitCandidate hquery).union := by
      rw [← full.finalCandidate_union hquery]
      exact point.property
    have hcover := hselectedCover ⟨point, hpointSelected⟩ center
    simpa only [exactConstant, full.finalCandidate_union hquery] using hcover
  have hcoarseVariation : ∀ first ∈ (full.finalCandidate hquery).union,
      ∀ second ∈ (full.finalCandidate hquery).union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale := by
    intro first _ second _ hdistance
    exact (hplaneLipschitz.dist_le_mul first second).trans <|
      (mul_le_mul_of_nonneg_left hdistance coefficient.coe_nonneg).trans
        hvariation
  have hcoarseMass : coarseLeft * data.current.mass ≤
      coarseRight * (full.finalCandidate hquery).mass := by
    simpa only [coarseLeft, coarseRight] using
      full.finalCandidate_mass_ledger hquery hquery
  rcases fineReentry.candidate_joint_interval_of_outer_coarse
      (outer := outer) (coarseNormalized := coarseNormalized)
      (coarseCurrent := data.current)
      (coarseCandidate := full.finalCandidate hquery)
      (ancestorEmbedding := ancestorEmbedding)
      (ancestor_tube_eq := ancestor_tube_eq)
      (current_sub_outer := current_sub_outer)
      (ancestorRetentionFactor := ancestorRetentionFactor)
      (current_retained_mass := current_retained_mass)
      (planeMap := planeMap) (resolutionScale := Real.toNNReal rho.1)
      (windowScale := Real.toNNReal tauScale) (constant := exactConstant)
      (coarseLeft := coarseLeft) (coarseRight := coarseRight)
      (hcoarseSub := full.finalCandidate_subshading hquery)
      (hcoarseCubical := full.finalCandidate_cubical hquery)
      (hcoarseVariation := hcoarseVariation)
      (hcoarseInterval := hcoarseCover) (hcoarseMass := hcoarseMass)
      (scaleFactor := scaleFactor) (hscaleFactor := hscaleFactor)
      (hrhoAligned := hrhoAligned) with
    ⟨pulled, hpulledSub, hpulledCubical, hpulledMultiplicity,
      hpulledVariation, hpulledCover, hpulledMass⟩
  have htargetMass : targetLeft * fineCurrent.mass ≤
      targetRight * pulled.mass := by
    calc
      targetLeft * fineCurrent.mass ≤
          proposition63DependentFinePullbackLeft fineReentry outer
              ancestorRetentionFactor coarseLeft * fineCurrent.mass :=
        mul_le_mul_right' (by simpa only [coarseLeft] using hleft) _
      _ ≤ proposition63DependentFinePullbackRight fineReentry coarseRight *
          pulled.mass := hpulledMass
      _ ≤ targetRight * pulled.mass :=
        mul_le_mul_right' (by simpa only [coarseRight] using hright) _
  let massLoss := proposition63Lemma43MassLoss targetLeft targetRight
  have hmassRetention : massLoss⁻¹ * fineCurrent.mass ≤ pulled.mass :=
    proposition63Lemma43MassLoss_inv_mul_le hleftPos hleftTop hrightTop
      htargetMass
  rcases intervalLocalGrain_of_mass_ledger planeMap hcurrentExtremal
      hcurrentCWA hpulledSub hpulledCubical
      (pureWZ2IntervalCoveringAt_mono_constant hconstant hpulledCover)
      massLoss (proposition63Lemma43MassLoss_pos _ _)
      (proposition63Lemma43MassLoss_ne_top hleftPos hrightTop)
      hmassRetention hcurrentOutput houtputLoss
      (by simpa only [massLoss] using hrestore) with ⟨restored, hrestored⟩
  refine ⟨restored.shading, restored.subshading, ?_, ?_, restored.extremal,
    restored.cwa, restored.interval_covering, ?_, ?_⟩
  · rw [hrestored]
    exact hpulledCubical
  · intro point hpoint
    rw [hrestored] at hpoint ⊢
    exact hpulledMultiplicity point hpoint
  · rw [hrestored]
    exact htargetMass
  · intro first hfirst second hsecond hdistance
    rw [hrestored] at hfirst hsecond
    exact hpulledVariation first hfirst second hsecond hdistance

end FullGrainCells

/-- Construct all square-root-cell full-grain certificates from the second
point-centered covering.  The only spatial covering cost is the fixed `512`
for a ball by half-radius balls; no `(sqrt queryScale / tauScale)^3` term
appears. -/
theorem fullGrainCells
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant)
    (hqueryPos : 0 < queryScale)
    (hqueryOne : queryScale ≤ 1)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (hplaneUnit : ∀ point ∈ data.prepared.refined.shading.union,
      ‖planeMap point‖ = 1)
    (K : ℝ) (hK : 1 ≤ K)
    (hplaneLipschitz : ∀ first ∈ data.prepared.refined.shading.union,
      ∀ second ∈ data.prepared.refined.shading.union,
        dist (planeMap first) (planeMap second) ≤ K * dist first second)
    (lineVolume : ℝ)
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * K) + 2 : ENNReal) * sqrtConstant) ≤
        (coverBudget : ENNReal))
    (hsqrtConstantFinite : sqrtConstant ≠ ⊤)
    (hlineVolume : 0 < lineVolume)
    (hlineFloor : ENNReal.ofReal lineVolume ≤ data.cells.cellMass / 2) :
    Nonempty (data.FullGrainCells lineVolume coverBudget) := by
  have hsqrtPos : 0 < sqrtScale := by
    rw [hsqrtScale]
    exact Real.sqrt_pos.mpr hqueryPos
  have hcellData : ∀ cell : {cell // cell ∈ data.cells.activeCells},
      Nonempty (Proposition63FullGrainFubiniCellData
        (data.prepared.refined.shading.union ∩
          wz1PaperGridCube sqrtScale cell.1)
        (planeMap (data.cells.cellRep cell.1 cell.2))
        queryScale (2 * sqrtScale) lineVolume
        (data.cells.cellMass / 2)
        ((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal)))) := by
    intro cell
    let E := data.prepared.refined.shading.union ∩
      wz1PaperGridCube sqrtScale cell.1
    let center := data.cells.cellRep cell.1 cell.2
    have hEMeasurable : MeasurableSet E :=
      data.prepared.refined.shading.union_measurable.inter
        (wz1PaperGridCube_measurable cell.1)
    have hEVolume : volume E = data.cells.cellMass :=
      data.cells.fine_cell_mass cell.1 cell.2
    have hEFinite : volume E ≠ ⊤ := by
      rw [hEVolume]
      exact data.cells.cellMass_ne_top
    have hcenterE : center ∈ E :=
      ⟨data.cells.cellRep_in_union cell.1 cell.2,
        data.cells.cellRep_in_cell cell.1 cell.2⟩
    have hEball : E ⊆ Metric.closedBall center (2 * sqrtScale) := by
      intro point hpoint
      exact (wz1_paper_grid_cube_diameter_lt_two_rho hsqrtPos
        hpoint.2 hcenterE.2).le
    have hlocal : ∀ point ∈ E,
        (Metric.externalCoveringNumber (Real.toNNReal queryScale)
          (scalarProjection (planeMap point)
            (E ∩ Metric.closedBall point sqrtScale)) : ENNReal) ≤
          sqrtConstant := by
      intro point hpoint
      have hraw := data.secondCoverOnPrepared
        ⟨point, hpoint.1⟩
      have hset :
          scalarProjection (planeMap point)
              (E ∩ Metric.closedBall point sqrtScale) ⊆
            scalarProjection (planeMap point)
              (data.prepared.refined.shading.union ∩
                Metric.closedBall point sqrtScale) :=
        Set.image_mono <| Set.inter_subset_inter_left _ Set.inter_subset_left
      have hmono :
          (Metric.externalCoveringNumber (Real.toNNReal queryScale)
              (scalarProjection (planeMap point)
                (E ∩ Metric.closedBall point sqrtScale)) : ENNReal) ≤
            (Metric.externalCoveringNumber (Real.toNNReal queryScale)
              (scalarProjection (planeMap point)
                (data.prepared.refined.shading.union ∩
                  Metric.closedBall point sqrtScale)) : ENNReal) := by
        exact_mod_cast Metric.externalCoveringNumber_mono_set hset
      exact hmono.trans hraw
    have htwice : 2 * (data.cells.cellMass / 2) ≤ volume E := by
      rw [hEVolume]
      exact (ENNReal.mul_div_cancel (by norm_num) (by norm_num)).le
    exact proposition63_fullGrainFubiniCell_of_planeMap
      hEMeasurable hEFinite hqueryPos hsqrtPos hsqrtScale center hcenterE
      hEball planeMap (hplaneUnit center hcenterE.1) hK
      (fun first hfirst second hsecond =>
        hplaneLipschitz first hfirst.1 second hsecond.1)
      sqrtConstant hsqrtConstantFinite
      hlocal (data.cells.cellMass / 2)
      ((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal)))
      (ENNReal.div_ne_top data.cells.cellMass_ne_top (by norm_num)) htwice
      hlineVolume hlineFloor coverBudget hcoverBudgetPos hcoverBudget rfl
  let selected := fun cell : {cell // cell ∈ data.cells.activeCells} =>
    Classical.choice (hcellData cell)
  have hlineHits : ∀ cell : {cell // cell ∈ data.cells.activeCells},
      Nonempty (selected cell).LineHitData := by
    intro cell
    exact (selected cell).exists_lineHitData
      (hplaneUnit (data.cells.cellRep cell.1 cell.2)
        (data.cells.cellRep_in_union cell.1 cell.2))
      hqueryPos (by positivity)
  exact ⟨{
    cellData := selected
    lineHits := fun cell => Classical.choice (hlineHits cell)
  }⟩

/-- Construct the full-grain cells with the paper-scale line threshold
coming from the cropped critical floor and the actual third-sticky active-cell
count.  This replaces the weaker ambient-grid average used by the temporary
canonical wrapper. -/
theorem fullGrainCells_of_critical_floor
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant)
    {floorLoss structuralBudget cellVolumeFloor : ℝ}
    (critical : PureWZ2CroppedCriticalFloorSelectionData
      sigma floorLoss structuralBudget)
    (hdeltaCritical : delta ≤ critical.delta₀)
    (hfinalStructural : finalLoss = critical.structuralLoss)
    (hcellVolumeFloor : 0 < cellVolumeFloor)
    (hcellBudget :
      ENNReal.ofReal cellVolumeFloor *
          Kakeya.realRpowENN sqrtScale (sigma - sqrtStickyLoss) ≤
        Kakeya.realRpowENN delta (sigma + floorLoss) *
          Kakeya.realRpowENN sqrtScale 3)
    (hqueryPos : 0 < queryScale) (hqueryOne : queryScale ≤ 1)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (hplaneUnit : ∀ point ∈ data.prepared.refined.shading.union,
      ‖planeMap point‖ = 1)
    (coefficient : NNReal) (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            sqrtConstant) ≤ (coverBudget : ENNReal))
    (hsqrtConstantFinite : sqrtConstant ≠ ⊤) :
    Nonempty (data.FullGrainCells (cellVolumeFloor / 2) coverBudget) := by
  have hcellLower : ENNReal.ofReal cellVolumeFloor ≤ data.cells.cellMass :=
    data.critical_cellMass_lower critical hdeltaCritical hfinalStructural
      hcellVolumeFloor.le hcellBudget
  have hlineFloor : ENNReal.ofReal (cellVolumeFloor / 2) ≤
      data.cells.cellMass / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    simpa using ENNReal.div_le_div_right hcellLower (2 : ENNReal)
  exact data.fullGrainCells hqueryPos hqueryOne hsqrtScale hplaneUnit
    (coefficient : ℝ) hcoefficientOne
    (fun first _ second _ => hplaneLipschitz.dist_le_mul first second)
    (cellVolumeFloor / 2) coverBudget hcoverBudgetPos hcoverBudget
    hsqrtConstantFinite (by positivity) hlineFloor

theorem fullGrainCells_of_pure_critical_trace
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant)
    {floorLoss structuralBudget cellVolumeFloor : ℝ}
    (critical : PureWZ2CriticalFloorSelectionData
      sigma floorLoss structuralBudget)
    (hdeltaCritical : delta ≤ critical.delta₀)
    (hfinalStructural : finalLoss ≤ critical.structuralLoss)
    (traceAbsorption : Proposition63PureCriticalTailTraceAbsorption delta
      critical.structuralLoss reentryLoss finalLoss)
    (hcellVolumeFloor : 0 < cellVolumeFloor)
    (hcellBudget :
      ENNReal.ofReal cellVolumeFloor *
          Kakeya.realRpowENN sqrtScale (sigma - sqrtStickyLoss) ≤
        Kakeya.realRpowENN delta (sigma + floorLoss) *
          Kakeya.realRpowENN sqrtScale 3)
    (hqueryPos : 0 < queryScale) (hqueryOne : queryScale ≤ 1)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (hplaneUnit : ∀ point ∈ data.prepared.refined.shading.union,
      ‖planeMap point‖ = 1)
    (coefficient : NNReal) (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            sqrtConstant) ≤ (coverBudget : ENNReal))
    (hsqrtConstantFinite : sqrtConstant ≠ ⊤) :
    Nonempty (data.FullGrainCells (cellVolumeFloor / 2) coverBudget) := by
  have hcellLower : ENNReal.ofReal cellVolumeFloor ≤ data.cells.cellMass :=
    data.critical_cellMass_lower_of_pure_critical_trace critical hdeltaCritical hfinalStructural
      traceAbsorption hcellVolumeFloor.le hcellBudget
  have hlineFloor : ENNReal.ofReal (cellVolumeFloor / 2) ≤
      data.cells.cellMass / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    simpa using ENNReal.div_le_div_right hcellLower (2 : ENNReal)
  exact data.fullGrainCells hqueryPos hqueryOne hsqrtScale hplaneUnit
    (coefficient : ℝ) hcoefficientOne
    (fun first _ second _ => hplaneLipschitz.dist_le_mul first second)
    (cellVolumeFloor / 2) coverBudget hcoverBudgetPos hcoverBudget
    hsqrtConstantFinite (by positivity) hlineFloor

/-- Direct paper-scale tail for one concrete nested pair.  It constructs the
full-grain witness from the cropped critical floor and immediately performs
the unique whole-cell pullback and final extremality/CWA restoration. -/
theorem finalCandidate_for_fine_interval_iteration_of_critical_floor
    {fineDelta sigma fineInputLoss fineNormalizationLoss fineReentryLoss
      outerLoss coarseInputLoss coarseNormalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss tauScale sqrtScale outputLoss
      spatialScale variationScale floorLoss structuralBudget cellVolumeFloor : ℝ}
    {fineSource : PureWZ2ExtremalConfiguration
      sigma fineInputLoss fineDelta}
    {fineNormalizationExponent outerLogExponent
      coarseNormalizationExponent : ℕ}
    {fineNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := fineNormalizationLoss) fineSource
      fineNormalizationExponent}
    {fineCurrent : WZ1PaperTubeShading fineNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) fineNormalized fineCurrent)
    {rho : WZ2PaperRequestedScale fineDelta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      coarseNormalizationExponent)
    (planeMap : Point3 → Point3) (tauConstant sqrtConstant : ENNReal)
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := rho.1)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      coarseNormalized planeMap tauConstant sqrtConstant)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      coarseNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index))
    (current_sub_outer : ∀ index, data.current.carrier index ⊆
      outer.croppedCoarseShading.carrier (ancestorEmbedding index))
    (ancestorRetentionFactor : ENNReal)
    (current_retained_mass :
      ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
        data.current.mass)
    (critical : PureWZ2CroppedCriticalFloorSelectionData
      sigma floorLoss structuralBudget)
    (hcoarseCritical : rho.1 ≤ critical.delta₀)
    (hfinalStructural : finalLoss = critical.structuralLoss)
    (hcellVolumeFloor : 0 < cellVolumeFloor)
    (hcellBudget :
      ENNReal.ofReal cellVolumeFloor *
          Kakeya.realRpowENN sqrtScale (sigma - sqrtStickyLoss) ≤
        Kakeya.realRpowENN rho.1 (sigma + floorLoss) *
          Kakeya.realRpowENN sqrtScale 3)
    (hquery : 0 < rho.1) (hqueryOne : rho.1 ≤ 1)
    (htau : 0 < tauScale) (hqueryTau : rho.1 ≤ tauScale)
    (htauSqrt : tauScale ≤ Real.sqrt rho.1)
    (hsqrtScale : sqrtScale = Real.sqrt rho.1)
    (hplaneUnit : ∀ point ∈ data.prepared.refined.shading.union,
      ‖planeMap point‖ = 1)
    (coefficient : NNReal) (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            sqrtConstant) ≤ (coverBudget : ENNReal))
    (hsqrtConstantFinite : sqrtConstant ≠ ⊤)
    (hnormalErrorTau : 8 * (coefficient : ℝ) * rho.1 ≤ tauScale)
    (hhullTau : rho.1 * Real.sqrt 3 ≤ tauScale)
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * fineDelta)
    (fineCurrentLoss : ℝ)
    (hcurrentExtremal : WZ2PaperCroppedIsExtremal sigma fineCurrentLoss
      fineNormalized.croppedFamily fineCurrent)
    (hcurrentCWA : WZ2PaperConvexWolffBound
      fineNormalized.croppedFamily
      (Kakeya.realRpowENN fineDelta (-fineCurrentLoss)))
    (targetConstant targetLeft targetRight : ENNReal)
    (hconstant : FullGrainCells.nestedCandidateIntervalBound rho.1 rho.1
      (8 * (coefficient : ℝ) * rho.1) (coefficient : ℝ)
      (13 ^ 3) tauConstant ≤ targetConstant)
    (hleft : targetLeft ≤
      proposition63DependentFinePullbackLeft fineReentry outer
        ancestorRetentionFactor
        (ENNReal.ofReal
            ((cellVolumeFloor / 2) / (4 * (2 * sqrtScale) ^ 2)) *
          (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) *
          (data.secondRetainedFactor *
            ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
            data.firstRetainedFactor)))
    (hright : proposition63DependentFinePullbackRight fineReentry
        ((data.reentry.regularized.regularizationLoss *
            data.prepared.preparationLoss) *
          (2 * ENNReal.ofReal (4 * rho.1))) ≤ targetRight)
    (hleftPos : 0 < targetLeft) (hleftTop : targetLeft ≠ ⊤)
    (hrightTop : targetRight ≠ ⊤)
    (hcurrentOutput : fineCurrentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss targetLeft targetRight *
        Kakeya.realRpowENN fineDelta outputLoss ≤
      Kakeya.realRpowENN fineDelta fineCurrentLoss)
    (hvariation : (coefficient : ℝ) * spatialScale ≤ variationScale) :
    ∃ next : WZ1PaperTubeShading fineNormalized.croppedFamily,
      PaperIsSubshading next fineCurrent ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union,
        next.pointMultiplicity point = fineCurrent.pointMultiplicity point) ∧
      WZ2PaperCroppedIsExtremal sigma outputLoss
        fineNormalized.croppedFamily next ∧
      WZ2PaperConvexWolffBound fineNormalized.croppedFamily
        (Kakeya.realRpowENN fineDelta (-outputLoss)) ∧
      PureWZ2IntervalCoveringAt next planeMap rho.1
        (Real.toNNReal rho.1) (Real.toNNReal tauScale) targetConstant ∧
      targetLeft * fineCurrent.mass ≤ targetRight * next.mass ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) := by
  let coarseLeft : ENNReal :=
    ENNReal.ofReal
        ((cellVolumeFloor / 2) / (4 * (2 * sqrtScale) ^ 2)) *
      (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) *
      (data.secondRetainedFactor *
        ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
        data.firstRetainedFactor)
  let coarseRight : ENNReal :=
    (data.reentry.regularized.regularizationLoss *
      data.prepared.preparationLoss) *
    (2 * ENNReal.ofReal (4 * rho.1))
  rcases data.fullGrainCells_of_critical_floor critical hcoarseCritical
      hfinalStructural hcellVolumeFloor hcellBudget hquery hqueryOne
      hsqrtScale hplaneUnit coefficient hcoefficientOne hplaneLipschitz
      coverBudget hcoverBudgetPos hcoverBudget hsqrtConstantFinite with
    ⟨full⟩
  have hconstant' : FullGrainCells.nestedCandidateIntervalBound rho.1 rho.1
        (8 * (coefficient : ℝ) * rho.1) (coefficient : ℝ)
        (13 ^ 3) tauConstant ≤ targetConstant :=
    hconstant
  have hleft' : targetLeft ≤
      proposition63DependentFinePullbackLeft fineReentry outer
        ancestorRetentionFactor coarseLeft := by
    simpa only [coarseLeft] using hleft
  have hright' : proposition63DependentFinePullbackRight fineReentry
      coarseRight ≤ targetRight := by
    simpa only [coarseRight] using hright
  exact FullGrainCells.finalCandidate_for_fine_interval_iteration_of_lipschitz
    (data := data) full
    (fineReentry := fineReentry) (outer := outer)
    (coarseNormalized := coarseNormalized)
    (ancestorEmbedding := ancestorEmbedding)
    (ancestor_tube_eq := ancestor_tube_eq)
    (current_sub_outer := current_sub_outer)
    (ancestorRetentionFactor := ancestorRetentionFactor)
    (current_retained_mass := current_retained_mass)
    (hquery := hquery) (htau := htau) (hqueryTau := hqueryTau)
    (htauSqrt := htauSqrt) (hsqrtScale := hsqrtScale)
    (coefficient := coefficient) (hcoefficientOne := hcoefficientOne)
    (hplaneLipschitz := hplaneLipschitz) (hplaneUnit := hplaneUnit)
    (hnormalErrorTau := hnormalErrorTau) (hhullTau := hhullTau)
    (scaleFactor := scaleFactor) (hscaleFactor := hscaleFactor)
    (hrhoAligned := hrhoAligned) (fineCurrentLoss := fineCurrentLoss)
    (hcurrentExtremal := hcurrentExtremal) (hcurrentCWA := hcurrentCWA)
    (targetConstant := targetConstant) (targetLeft := targetLeft)
    (targetRight := targetRight) (hconstant := hconstant') (hleft := hleft')
    (hright := hright') (hleftPos := hleftPos) (hleftTop := hleftTop)
    (hrightTop := hrightTop) (hcurrentOutput := hcurrentOutput)
    (houtputLoss := houtputLoss) (hrestore := hrestore)
    (hvariation := hvariation)

theorem finalCandidate_for_fine_interval_iteration_of_pure_critical_trace
    {fineDelta sigma fineInputLoss fineNormalizationLoss fineReentryLoss
      outerLoss coarseInputLoss coarseNormalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss tauScale sqrtScale outputLoss
      spatialScale variationScale floorLoss structuralBudget cellVolumeFloor : ℝ}
    {fineSource : PureWZ2ExtremalConfiguration
      sigma fineInputLoss fineDelta}
    {fineNormalizationExponent outerLogExponent
      coarseNormalizationExponent : ℕ}
    {fineNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := fineNormalizationLoss) fineSource
      fineNormalizationExponent}
    {fineCurrent : WZ1PaperTubeShading fineNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) fineNormalized fineCurrent)
    {rho : WZ2PaperRequestedScale fineDelta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      coarseNormalizationExponent)
    (planeMap : Point3 → Point3) (tauConstant sqrtConstant : ENNReal)
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := rho.1)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      coarseNormalized planeMap tauConstant sqrtConstant)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      coarseNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index))
    (current_sub_outer : ∀ index, data.current.carrier index ⊆
      outer.croppedCoarseShading.carrier (ancestorEmbedding index))
    (ancestorRetentionFactor : ENNReal)
    (current_retained_mass :
      ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
        data.current.mass)
    (critical : PureWZ2CriticalFloorSelectionData
      sigma floorLoss structuralBudget)
    (hcoarseCritical : rho.1 ≤ critical.delta₀)
    (hfinalStructural : finalLoss ≤ critical.structuralLoss)
    (traceAbsorption : Proposition63PureCriticalTailTraceAbsorption rho.1
      critical.structuralLoss reentryLoss finalLoss)
    (hcellVolumeFloor : 0 < cellVolumeFloor)
    (hcellBudget :
      ENNReal.ofReal cellVolumeFloor *
          Kakeya.realRpowENN sqrtScale (sigma - sqrtStickyLoss) ≤
        Kakeya.realRpowENN rho.1 (sigma + floorLoss) *
          Kakeya.realRpowENN sqrtScale 3)
    (hquery : 0 < rho.1) (hqueryOne : rho.1 ≤ 1)
    (htau : 0 < tauScale) (hqueryTau : rho.1 ≤ tauScale)
    (htauSqrt : tauScale ≤ Real.sqrt rho.1)
    (hsqrtScale : sqrtScale = Real.sqrt rho.1)
    (hplaneUnit : ∀ point ∈ data.prepared.refined.shading.union,
      ‖planeMap point‖ = 1)
    (coefficient : NNReal) (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            sqrtConstant) ≤ (coverBudget : ENNReal))
    (hsqrtConstantFinite : sqrtConstant ≠ ⊤)
    (hnormalErrorTau : 8 * (coefficient : ℝ) * rho.1 ≤ tauScale)
    (hhullTau : rho.1 * Real.sqrt 3 ≤ tauScale)
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * fineDelta)
    (fineCurrentLoss : ℝ)
    (hcurrentExtremal : WZ2PaperCroppedIsExtremal sigma fineCurrentLoss
      fineNormalized.croppedFamily fineCurrent)
    (hcurrentCWA : WZ2PaperConvexWolffBound
      fineNormalized.croppedFamily
      (Kakeya.realRpowENN fineDelta (-fineCurrentLoss)))
    (targetConstant targetLeft targetRight : ENNReal)
    (hconstant : FullGrainCells.nestedCandidateIntervalBound rho.1 rho.1
      (8 * (coefficient : ℝ) * rho.1) (coefficient : ℝ)
      (13 ^ 3) tauConstant ≤ targetConstant)
    (hleft : targetLeft ≤
      proposition63DependentFinePullbackLeft fineReentry outer
        ancestorRetentionFactor
        (ENNReal.ofReal
            ((cellVolumeFloor / 2) / (4 * (2 * sqrtScale) ^ 2)) *
          (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) *
          (data.secondRetainedFactor *
            ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
            data.firstRetainedFactor)))
    (hright : proposition63DependentFinePullbackRight fineReentry
        ((data.reentry.regularized.regularizationLoss *
            data.prepared.preparationLoss) *
          (2 * ENNReal.ofReal (4 * rho.1))) ≤ targetRight)
    (hleftPos : 0 < targetLeft) (hleftTop : targetLeft ≠ ⊤)
    (hrightTop : targetRight ≠ ⊤)
    (hcurrentOutput : fineCurrentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss targetLeft targetRight *
        Kakeya.realRpowENN fineDelta outputLoss ≤
      Kakeya.realRpowENN fineDelta fineCurrentLoss)
    (hvariation : (coefficient : ℝ) * spatialScale ≤ variationScale) :
    ∃ next : WZ1PaperTubeShading fineNormalized.croppedFamily,
      PaperIsSubshading next fineCurrent ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union,
        next.pointMultiplicity point = fineCurrent.pointMultiplicity point) ∧
      WZ2PaperCroppedIsExtremal sigma outputLoss
        fineNormalized.croppedFamily next ∧
      WZ2PaperConvexWolffBound fineNormalized.croppedFamily
        (Kakeya.realRpowENN fineDelta (-outputLoss)) ∧
      PureWZ2IntervalCoveringAt next planeMap rho.1
        (Real.toNNReal rho.1) (Real.toNNReal tauScale) targetConstant ∧
      targetLeft * fineCurrent.mass ≤ targetRight * next.mass ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) := by
  let coarseLeft : ENNReal :=
    ENNReal.ofReal
        ((cellVolumeFloor / 2) / (4 * (2 * sqrtScale) ^ 2)) *
      (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) *
      (data.secondRetainedFactor *
        ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
        data.firstRetainedFactor)
  let coarseRight : ENNReal :=
    (data.reentry.regularized.regularizationLoss *
      data.prepared.preparationLoss) *
    (2 * ENNReal.ofReal (4 * rho.1))
  rcases data.fullGrainCells_of_pure_critical_trace critical hcoarseCritical
      hfinalStructural traceAbsorption hcellVolumeFloor hcellBudget
      hquery hqueryOne
      hsqrtScale hplaneUnit coefficient hcoefficientOne hplaneLipschitz
      coverBudget hcoverBudgetPos hcoverBudget hsqrtConstantFinite with
    ⟨full⟩
  have hconstant' : FullGrainCells.nestedCandidateIntervalBound rho.1 rho.1
        (8 * (coefficient : ℝ) * rho.1) (coefficient : ℝ)
        (13 ^ 3) tauConstant ≤ targetConstant :=
    hconstant
  have hleft' : targetLeft ≤
      proposition63DependentFinePullbackLeft fineReentry outer
        ancestorRetentionFactor coarseLeft := by
    simpa only [coarseLeft] using hleft
  have hright' : proposition63DependentFinePullbackRight fineReentry
      coarseRight ≤ targetRight := by
    simpa only [coarseRight] using hright
  exact FullGrainCells.finalCandidate_for_fine_interval_iteration_of_lipschitz
    (data := data) full
    (fineReentry := fineReentry) (outer := outer)
    (coarseNormalized := coarseNormalized)
    (ancestorEmbedding := ancestorEmbedding)
    (ancestor_tube_eq := ancestor_tube_eq)
    (current_sub_outer := current_sub_outer)
    (ancestorRetentionFactor := ancestorRetentionFactor)
    (current_retained_mass := current_retained_mass)
    (hquery := hquery) (htau := htau) (hqueryTau := hqueryTau)
    (htauSqrt := htauSqrt) (hsqrtScale := hsqrtScale)
    (coefficient := coefficient) (hcoefficientOne := hcoefficientOne)
    (hplaneLipschitz := hplaneLipschitz) (hplaneUnit := hplaneUnit)
    (hnormalErrorTau := hnormalErrorTau) (hhullTau := hhullTau)
    (scaleFactor := scaleFactor) (hscaleFactor := hscaleFactor)
    (hrhoAligned := hrhoAligned) (fineCurrentLoss := fineCurrentLoss)
    (hcurrentExtremal := hcurrentExtremal) (hcurrentCWA := hcurrentCWA)
    (targetConstant := targetConstant) (targetLeft := targetLeft)
    (targetRight := targetRight) (hconstant := hconstant') (hleft := hleft')
    (hright := hright') (hleftPos := hleftPos) (hleftTop := hleftTop)
    (hrightTop := hrightTop) (hcurrentOutput := hcurrentOutput)
    (houtputLoss := houtputLoss) (hrestore := hrestore)
    (hvariation := hvariation)

/-- The canonical total-volume floor supplied by the final extremal shading
in a nested point-cover chain. -/
def canonicalVolumeFloor
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant) : ENNReal :=
  Kakeya.realRpowENN delta (finalLoss + 2)

/-- The canonical line threshold obtained from extremality and the finite
literal square-root grid. -/
def canonicalLineVolume
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant) : ℝ :=
  proposition63UniformLineVolume data.canonicalVolumeFloor sqrtScale
    data.cells.scale_pos

/-- The finite cover budget needed by the Fubini selection inside one
square-root cell.  It depends on the square-root covering constant, but not
on the arbitrary interval radius `tauScale`. -/
def canonicalCoverRequirement
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant)
    (coefficient : NNReal) : ENNReal :=
  512 * ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
    sqrtConstant)

/-- A deterministic natural budget dominating the finite square-root cover
requirement.  Making this a definition, rather than an existential runtime
choice, lets the finite iterator preselect its exact mass factors. -/
def canonicalCoverBudget
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant)
    (coefficient : NNReal) : ℕ :=
  Nat.ceil (data.canonicalCoverRequirement coefficient).toNNReal + 1

theorem canonicalCoverBudget_pos
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant)
    (coefficient : NNReal) :
    0 < data.canonicalCoverBudget coefficient := by
  unfold canonicalCoverBudget
  omega

theorem canonicalCoverBudget_bound
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant)
    (coefficient : NNReal)
    (hfinite : data.canonicalCoverRequirement coefficient ≠ ⊤) :
    data.canonicalCoverRequirement coefficient ≤
      (data.canonicalCoverBudget coefficient : ENNReal) := by
  have hceil : (data.canonicalCoverRequirement coefficient).toNNReal ≤
      ((Nat.ceil (data.canonicalCoverRequirement coefficient).toNNReal : ℕ) :
        NNReal) := Nat.le_ceil _
  have hceil' : (data.canonicalCoverRequirement coefficient).toNNReal ≤
      ((Nat.ceil (data.canonicalCoverRequirement coefficient).toNNReal + 1 :
        ℕ) : NNReal) := by
    have hsucc : Nat.ceil
        (data.canonicalCoverRequirement coefficient).toNNReal ≤
        Nat.ceil (data.canonicalCoverRequirement coefficient).toNNReal + 1 :=
      Nat.le_succ _
    exact hceil.trans (by exact_mod_cast hsucc)
  rw [← ENNReal.coe_toNNReal hfinite]
  exact_mod_cast hceil'

/-- A nested point-cover chain with the canonical line threshold and an
internally chosen finite full-grain cover budget. -/
structure CanonicalFullGrainCells
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant)
    (coefficient : NNReal) where
  full : data.FullGrainCells data.canonicalLineVolume
    (data.canonicalCoverBudget coefficient)

/-- Construct the canonical full-grain/Fubini cells directly from nested
extremality.  The only cover-cardinality payment is the finite
square-root-scale requirement; no cover of a square-root cell by
`tauScale`-balls is used. -/
theorem canonicalFullGrainCells
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap
      tauConstant sqrtConstant)
    (hqueryPos : 0 < queryScale)
    (hqueryOne : queryScale ≤ 1)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (hplaneUnit : ∀ point ∈ data.prepared.refined.shading.union,
      ‖planeMap point‖ = 1)
    (coefficient : NNReal) (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hsqrtConstantFinite : sqrtConstant ≠ ⊤)
    (hdeltaSmall : delta ≤ 1 / 12) :
    Nonempty (data.CanonicalFullGrainCells coefficient) := by
  have hvolumeFloorPos : 0 < data.canonicalVolumeFloor := by
    simp [canonicalVolumeFloor, Kakeya.realRpowENN,
      Real.rpow_pos_of_pos data.prepared.refined.extremal.delta_pos]
  have hvolumeFloorTop : data.canonicalVolumeFloor ≠ ⊤ := by
    simp [canonicalVolumeFloor, Kakeya.realRpowENN]
  have hvolumeFloor : data.canonicalVolumeFloor ≤
      volume data.prepared.refined.shading.union :=
    data.prepared.refined.union_volume_lower
      data.reentry.normalization.line_class hdeltaSmall
  have hrequirementTop : data.canonicalCoverRequirement coefficient ≠ ⊤ := by
    unfold canonicalCoverRequirement
    exact ENNReal.mul_ne_top (by norm_num) <| ENNReal.mul_ne_top
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _),
          by norm_num⟩)
      hsqrtConstantFinite
  have hcoverBudget := data.canonicalCoverBudget_bound coefficient
    hrequirementTop
  have hlineVolumePos : 0 < data.canonicalLineVolume := by
    exact proposition63UniformLineVolume_pos hvolumeFloorPos
      hvolumeFloorTop sqrtScale data.cells.scale_pos
  have hlineFloor : ENNReal.ofReal data.canonicalLineVolume ≤
      data.cells.cellMass / 2 :=
    data.cells.uniformLineVolume_le_half_cellMass data.canonicalVolumeFloor
      hvolumeFloorTop hvolumeFloor
  rcases data.fullGrainCells hqueryPos hqueryOne hsqrtScale hplaneUnit
      (coefficient : ℝ) hcoefficientOne
      (fun first _ second _ => hplaneLipschitz.dist_le_mul first second)
      data.canonicalLineVolume (data.canonicalCoverBudget coefficient)
      (data.canonicalCoverBudget_pos coefficient) hcoverBudget
      hsqrtConstantFinite hlineVolumePos hlineFloor with ⟨full⟩
  exact ⟨{ full := full }⟩

namespace CanonicalFullGrainCells

/-- The exact favorable factor in the nested full-grain mass ledger. -/
def leftFactor
    {coefficient : NNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    (canonical : data.CanonicalFullGrainCells coefficient) :
    ENNReal :=
  proposition63UniformLineFactor
      (Kakeya.realRpowENN delta (finalLoss + 2)) sqrtScale
      data.cells.scale_pos *
    (((1 : ENNReal) / 2) /
      (2 * (data.canonicalCoverBudget coefficient : ENNReal))) *
    (data.secondRetainedFactor *
      ((73 / 100 : ENNReal) *
        data.reentry.normalizationWeight) *
      data.firstRetainedFactor)

/-- The exact unfavorable factor in the nested full-grain mass ledger. -/
def rightFactor
    {coefficient : NNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    (canonical : data.CanonicalFullGrainCells coefficient) :
    ENNReal :=
  (data.reentry.regularized.regularizationLoss *
    data.prepared.preparationLoss) *
    (2 * ENNReal.ofReal (4 * queryScale))

/-- Direct iterator-facing output of the canonical nested full-grain
construction.  The interval estimate is derived from the two point-centered
covers and the Lipschitz plane map; the caller supplies only the numerical
comparison with its preselected target constant and the one-step loss
absorption used to restore extremality/CWA. -/
theorem finalCandidate_for_interval_iteration_of_lipschitz
    {outputLoss spatialScale variationScale : ℝ}
    {coefficient : NNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    (canonical : data.CanonicalFullGrainCells coefficient)
    (hdelta : 0 < delta) (hquery : 0 < queryScale)
    (htau : 0 < tauScale) (hqueryTau : queryScale ≤ tauScale)
    (htauSqrt : tauScale ≤ Real.sqrt queryScale)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneUnit : ∀ point ∈ data.prepared.refined.shading.union,
      ‖planeMap point‖ = 1)
    (hnormalErrorTau : 8 * (coefficient : ℝ) * queryScale ≤ tauScale)
    (hhullTau : delta * Real.sqrt 3 ≤ tauScale)
    (currentLoss : ℝ)
    (hcurrentExtremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      initialNormalized.croppedFamily data.current)
    (hcurrentCWA : WZ2PaperConvexWolffBound
      initialNormalized.croppedFamily
      (Kakeya.realRpowENN delta (-currentLoss)))
    (targetConstant : ENNReal)
    (hconstant : FullGrainCells.nestedCandidateIntervalBound delta queryScale
      (8 * (coefficient : ℝ) * queryScale) (coefficient : ℝ)
      (13 ^ 3) tauConstant ≤ targetConstant)
    (hcurrentOutput : currentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss canonical.leftFactor
        canonical.rightFactor * Kakeya.realRpowENN delta outputLoss ≤
      Kakeya.realRpowENN delta currentLoss)
    (hvariation : (coefficient : ℝ) * spatialScale ≤ variationScale) :
    ∃ next : WZ1PaperTubeShading initialNormalized.croppedFamily,
      PaperIsSubshading next data.current ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union,
        next.pointMultiplicity point = data.current.pointMultiplicity point) ∧
      WZ2PaperCroppedIsExtremal sigma outputLoss
        initialNormalized.croppedFamily next ∧
      WZ2PaperConvexWolffBound initialNormalized.croppedFamily
        (Kakeya.realRpowENN delta (-outputLoss)) ∧
      PureWZ2IntervalCoveringAt next planeMap queryScale
        (Real.toNNReal queryScale) (Real.toNNReal tauScale) targetConstant ∧
      canonical.leftFactor * data.current.mass ≤
        canonical.rightFactor * next.mass ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) := by
  let exactConstant := FullGrainCells.nestedCandidateIntervalBound delta queryScale
    (8 * (coefficient : ℝ) * queryScale) (coefficient : ℝ)
    (13 ^ 3) tauConstant
  have hselectedCover :=
    canonical.full.lineHitCandidate_interval_covering_of_lipschitz
      hdelta hquery htau hqueryTau htauSqrt hsqrtScale coefficient
      hcoefficientOne hplaneLipschitz hplaneUnit hnormalErrorTau hhullTau
  have hfinalCover : PureWZ2IntervalCoveringAt
      (canonical.full.finalCandidate hdelta) planeMap queryScale
      (Real.toNNReal queryScale) (Real.toNNReal tauScale) exactConstant := by
    intro point intervalCenter
    let selectedPoint : {point : Point3 // point ∈
        (canonical.full.lineHitCandidate hdelta).union} :=
      ⟨point, by
        rw [← canonical.full.finalCandidate_union hdelta]
        exact point.property⟩
    have hcover := hselectedCover selectedPoint intervalCenter
    simpa only [selectedPoint, canonical.full.finalCandidate_union hdelta]
      using hcover
  have hvolumeFloorPos : 0 < data.canonicalVolumeFloor := by
    simp [Proposition63NestedPointCoverData.canonicalVolumeFloor,
      Kakeya.realRpowENN,
      Real.rpow_pos_of_pos data.prepared.refined.extremal.delta_pos]
  have hvolumeFloorTop : data.canonicalVolumeFloor ≠ ⊤ := by
    simp [Proposition63NestedPointCoverData.canonicalVolumeFloor,
      Kakeya.realRpowENN]
  have hlineFactorPos : 0 < proposition63UniformLineFactor
      data.canonicalVolumeFloor sqrtScale data.cells.scale_pos :=
    proposition63UniformLineFactor_pos hvolumeFloorPos hvolumeFloorTop
      sqrtScale data.cells.scale_pos
  have hinverseCoverPos : 0 <
      (((1 : ENNReal) / 2) /
        (2 * (data.canonicalCoverBudget coefficient : ENNReal))) := by
    apply ENNReal.div_pos
    · norm_num
    · exact ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)
  have hretainedPos : 0 < data.secondRetainedFactor *
      ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
      data.firstRetainedFactor := by
    exact ENNReal.mul_pos
      (ENNReal.mul_pos data.second_retained_factor_pos.ne'
        (ENNReal.mul_pos (by norm_num)
          data.reentry.normalization_weight_ne_zero).ne').ne'
      data.first_retained_factor_pos.ne'
  have hleftPos : 0 < canonical.leftFactor := by
    unfold leftFactor
    exact ENNReal.mul_pos
      (ENNReal.mul_pos hlineFactorPos.ne' hinverseCoverPos.ne').ne'
      hretainedPos.ne'
  have hleftTop : canonical.leftFactor ≠ ⊤ := by
    unfold leftFactor proposition63UniformLineFactor
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.div_ne_top
          (ENNReal.div_ne_top (by norm_num) (by norm_num))
          (mul_ne_zero (by norm_num) <| by
            exact_mod_cast (data.canonicalCoverBudget_pos coefficient).ne')))
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top data.second_retained_factor_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.div_ne_top (by norm_num) (by norm_num))
            data.reentry.normalization_weight_ne_top))
        data.first_retained_factor_ne_top)
  have hrightTop : canonical.rightFactor ≠ ⊤ := by
    unfold rightFactor
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (by
          rw [data.reentry.regularized.regularizationLoss_eq]
          exact ENNReal.mul_ne_top (by norm_num) (by simp))
        data.prepared.preparationLoss_ne_top)
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
  apply canonical.full.finalCandidate_for_interval_iteration hdelta hquery
    currentLoss hcurrentExtremal hcurrentCWA exactConstant targetConstant
    hfinalCover hconstant canonical.leftFactor canonical.rightFactor
  · exact le_rfl
  · exact le_rfl
  · exact hleftPos
  · exact hleftTop
  · exact hrightTop
  · exact hcurrentOutput
  · exact houtputLoss
  · exact hrestore
  · exact hplaneLipschitz
  · exact hvariation

end CanonicalFullGrainCells

end Proposition63NestedPointCoverData

end Kakeya.Assouad.PureWZ2

end
