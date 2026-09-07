import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentHighCovering
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeOneScaleOutput
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LowCaseTrivialAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.OneScaleLocalGrain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.NormalizedCardinalityFloor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63UniformFullGrainStepProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.StickyZeroExtensionExtremal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CWAPropertyP
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteIntervalGridOneScaleLocalAD

/-!
# Dependent one-scale analytic output for Proposition 6.3

The second Proposition 6.2 call lives on the actual normalized outer coarse
family.  Its Property-(P) refinement therefore has the correct geometric
union for Lemma 4.11, but it does not by itself preserve all tube memberships
of the normalized source.  We first take the common-spatial hull relative to
that source.  This keeps the Property-(P) union exactly, restores the source
multiplicity on every retained point, and loses no shaded mass.

The LOW producer below uses the ball-diameter estimate.  The HIGH producer
uses the dependent local-volume/Cordoba estimate on the same Property-(P)
shading.  In the HIGH theorem the second requested scale is explicitly
`sqrt rho`, so the ball in the dependent estimate is definitionally the ball
required by `PureWZ2OneScaleLocalGrainData`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

attribute [local instance] Classical.propDecidable

/-- Common-spatial ambient lift of the dependent Property-(P) shading. -/
def Proposition63DependentTwoLevelCoverData.commonPropertyThree
    {delta sigma outerLoss reentryLoss innerLoss epsilon₁ epsilon₃ : ℝ}
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
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := data.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃) :
    WZ1PaperTubeShading reentry.normalization.croppedFamily :=
  paperCommonSpatialHull reentry.normalization.croppedRefined
    propP.propertyThree

/-- The zero-extended inner refinement remains below the exact normalization
used for the dependent second Proposition 6.2 call. -/
lemma Proposition63DependentTwoLevelCoverData.ambientRefined_sub_normalized
    {delta sigma outerLoss reentryLoss innerLoss : ℝ}
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
      reentry tau) :
    PaperIsSubshading data.ambientRefined
      reentry.normalization.croppedRefined := by
  intro ambientIndex point hpoint
  by_cases himage : ∃ selectedIndex,
      data.inner.selected.embedding selectedIndex = ambientIndex
  · rcases himage with ⟨selectedIndex, rfl⟩
    rw [Proposition63DependentTwoLevelCoverData.ambientRefined,
      extendShading_carrier_mem] at hpoint
    exact data.inner.subshading selectedIndex hpoint
  · have hempty : data.ambientRefined.carrier ambientIndex = ∅ := by
      exact extendShading_carrier_empty himage
    rw [hempty] at hpoint
    exact False.elim hpoint

/-- Property Three, and hence its common-spatial hull, is a genuine
subshading of the normalized source used by the dependent call. -/
lemma Proposition63DependentTwoLevelCoverData.propertyThree_sub_normalized
    {delta sigma outerLoss reentryLoss innerLoss epsilon₁ epsilon₃ : ℝ}
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
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := data.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃) :
    PaperIsSubshading propP.propertyThree
      reentry.normalization.croppedRefined := fun index point hpoint =>
  data.ambientRefined_sub_normalized index <|
    propP.propertyOne_sub index <| propP.propertyThree_sub index hpoint

lemma Proposition63DependentTwoLevelCoverData.commonPropertyThree_subshading
    {delta sigma outerLoss reentryLoss innerLoss epsilon₁ epsilon₃ : ℝ}
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
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := data.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃) :
    PaperIsSubshading (data.commonPropertyThree propP)
      reentry.normalization.croppedRefined :=
  paperCommonSpatialHull_subshading _ _

@[simp] lemma Proposition63DependentTwoLevelCoverData.commonPropertyThree_union
    {delta sigma outerLoss reentryLoss innerLoss epsilon₁ epsilon₃ : ℝ}
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
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := data.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃) :
    (data.commonPropertyThree propP).union = propP.propertyThree.union :=
  paperCommonSpatialHull_union (data.propertyThree_sub_normalized propP)

lemma Proposition63DependentTwoLevelCoverData.commonPropertyThree_cubical
    {delta sigma outerLoss reentryLoss innerLoss epsilon₁ epsilon₃ : ℝ}
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
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := data.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃) :
    WZ1PaperIsCubicalShading (data.commonPropertyThree propP) :=
  paperCommonSpatialHull_cubical reentry.normalization.cropped_cubical
    propP.propertyThree_cubical

/-- The zero-extension of the inner sticky refinement is a genuine extremal
shading on the exact outer-coarse normalization after paying only the inner
sticky retention factor. -/
theorem Proposition63DependentTwoLevelCoverData.ambientRefined_extremal
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
    (hreentryTarget : reentryLoss ≤ targetLoss)
    (hretention : Kakeya.realRpowENN rho.1 targetLoss ≤
      wz2PaperPureRefinementFraction rho.1 innerLogExponent *
        Kakeya.realRpowENN rho.1 reentryLoss) :
    WZ2PaperCroppedIsExtremal sigma targetLoss
      reentry.normalization.croppedFamily data.ambientRefined := by
  simpa only [Proposition63DependentTwoLevelCoverData.ambientRefined] using
    sticky_zero_extension_extremal reentry.normalization.final_extremal
      data.inner hreentryTarget hretention

/-- The same ambient refinement uses the unchanged top-level CWA of the
exact outer-coarse normalization, weakened only through the displayed loss
ordering. -/
theorem Proposition63DependentTwoLevelCoverData.ambientRefined_cwa
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
    (hreentryTarget : reentryLoss ≤ targetLoss) :
    WZ2PaperConvexWolffBound reentry.normalization.croppedFamily
      (Kakeya.realRpowENN rho.1 (-targetLoss)) := by
  apply transfer_cwa_to_subshading
    (_shading1 := reentry.normalization.croppedRefined)
    (_shading2 := data.ambientRefined)
    reentry.normalization.cropped_top_level_cwa hreentryTarget
    reentry.normalization.final_extremal.delta_pos
    reentry.normalization.final_extremal.delta_le_one

/-- Construct Property-(P) on the actual zero-extended inner refinement.
The first two hypotheses are precisely the loss payment needed to make that
refinement extremal; all remaining hypotheses are the scalar inputs of the
closed CWA Property-(P) theorem. -/
theorem Proposition63DependentTwoLevelCoverData.propertyP_of_cwa
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
          reentry.normalization.croppedFamily.enncard) :
    Nonempty (PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := data.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃) := by
  exact propertyP_refinement_of_cwa
    (data.ambientRefined_extremal hreentryTarget hretention)
    reentry.normalization.line_class
    (data.ambientRefined_cwa hreentryTarget) hdensityLoss htargetLoss
    hsmall hrhoSmall24 hrhoSmall10000 hpackingAbsorb hepsilon₁ hepsilon₃
    hepsilonSum htau hrhoTau htauLarge htauSq htauOne hcell hkappa
    hkappaOne hkappaRho hkappaProperty hcloseAbsorb

/-- Strengthened dependent Property-(P) construction exposing that the CWA
producer uses the same whole-cell shading for Properties One and Three.
This equality is the certificate needed to obtain the HIGH-call fullness
input from `propertyOne_full` rather than from an external callback. -/
theorem Proposition63DependentTwoLevelCoverData.propertyP_of_cwa_eq
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
          reentry.normalization.croppedFamily.enncard) :
    ∃ propP : PureWZ2PropertyPData
        (sigma := sigma) (coarseShading := data.ambientRefined)
        (tau := tau.1) epsilon₁ epsilon₃,
      propP.propertyThree = propP.propertyOne := by
  exact propertyP_refinement_of_cwa_eq
    (data.ambientRefined_extremal hreentryTarget hretention)
    reentry.normalization.line_class
    (data.ambientRefined_cwa hreentryTarget) hdensityLoss htargetLoss
    hsmall hrhoSmall24 hrhoSmall10000 hpackingAbsorb hepsilon₁ hepsilon₃
    hepsilonSum htau hrhoTau htauLarge htauSq htauOne hcell hkappa
    hkappaOne hkappaRho hkappaProperty hcloseAbsorb

/-- Exact mass-loss factor of the dependent second cover followed by the
half-mass Property-(P) refinement. -/
def proposition63DependentPropertyThreeMassLoss
    (rho : ℝ) (innerLogExponent : ℕ) : ENNReal :=
  ((1 / 2 : ENNReal) *
    wz2PaperPureRefinementFraction rho innerLogExponent)⁻¹

lemma proposition63DependentPropertyThreeMassLoss_pos_ne_top
    {rho : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (innerLogExponent : ℕ) :
    0 < proposition63DependentPropertyThreeMassLoss rho innerLogExponent ∧
      proposition63DependentPropertyThreeMassLoss rho innerLogExponent ≠ ⊤ := by
  rcases pure_refinement_fraction_pos_ne_top hrho hrhoOne innerLogExponent with
    ⟨hfractionPos, hfractionTop⟩
  have hproductPos : 0 < (1 / 2 : ENNReal) *
      wz2PaperPureRefinementFraction rho innerLogExponent := by
    exact ENNReal.mul_pos (by norm_num) hfractionPos.ne'
  have hproductTop : (1 / 2 : ENNReal) *
      wz2PaperPureRefinementFraction rho innerLogExponent ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hfractionTop
  exact ⟨ENNReal.inv_pos.mpr hproductTop,
    ENNReal.inv_ne_top.mpr hproductPos.ne'⟩

/-- The common-spatial Property-Three lift retains the exact product of the
inner Proposition 6.2 fraction and the Property-(P) half-mass fraction. -/
theorem Proposition63DependentTwoLevelCoverData.commonPropertyThree_mass
    {delta sigma outerLoss reentryLoss innerLoss epsilon₁ epsilon₃ : ℝ}
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
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := data.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃) :
    (proposition63DependentPropertyThreeMassLoss
        rho.1 innerLogExponent)⁻¹ *
        reentry.normalization.croppedRefined.mass ≤
      (data.commonPropertyThree propP).mass := by
  calc
    (proposition63DependentPropertyThreeMassLoss
          rho.1 innerLogExponent)⁻¹ *
          reentry.normalization.croppedRefined.mass =
        (1 / 2 : ENNReal) *
          (wz2PaperPureRefinementFraction rho.1 innerLogExponent *
            reentry.normalization.croppedRefined.mass) := by
      simp [proposition63DependentPropertyThreeMassLoss]
      ring
    _ ≤ (1 / 2 : ENNReal) * data.inner.refined.mass := by
      gcongr
      exact data.inner.retained_mass
    _ ≤ propP.propertyThree.mass :=
      data.propertyThree_mass_from_inner propP
    _ ≤ (data.commonPropertyThree propP).mass :=
      paperCommonSpatialHull_mass_lower
        (data.propertyThree_sub_normalized propP)

/-- Restore the exact extremal/CWA state on the dependent common-spatial
Property-Three shading without assuming any local AD conclusion.  This is
the correct entry point for the inner Lemma 4.11 interval producer. -/
theorem Proposition63DependentTwoLevelCoverData.extremalShadingData
    {delta sigma outerLoss reentryLoss innerLoss targetLoss epsilon₁ epsilon₃ : ℝ}
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
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := data.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃)
    (hreentryTarget : reentryLoss ≤ targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hrhoOne : rho.1 < 1)
    (hmassSlack : proposition63DependentPropertyThreeMassLoss
        rho.1 innerLogExponent *
          Kakeya.realRpowENN rho.1 targetLoss ≤
        Kakeya.realRpowENN rho.1 reentryLoss) :
    ∃ state : Proposition63ExtremalShadingData
        (sigma := sigma) (outputLoss := targetLoss)
        reentry.normalization.croppedRefined,
      state.shading = data.commonPropertyThree propP ∧
      (proposition63DependentPropertyThreeMassLoss
          rho.1 innerLogExponent)⁻¹ *
          reentry.normalization.croppedRefined.mass ≤ state.shading.mass := by
  let massLoss := proposition63DependentPropertyThreeMassLoss
    rho.1 innerLogExponent
  have hmassLoss := proposition63DependentPropertyThreeMassLoss_pos_ne_top
    reentry.normalization.final_extremal.delta_pos hrhoOne innerLogExponent
  let target := data.commonPropertyThree propP
  have htargetExtremal : WZ2PaperCroppedIsExtremal
      sigma targetLoss reentry.normalization.croppedFamily target :=
    transfer_cropped_extremal_to_subshading massLoss
      hmassLoss.1 hmassLoss.2 reentry.normalization.final_extremal
      (data.commonPropertyThree_subshading propP)
      (data.commonPropertyThree_mass propP)
      (data.commonPropertyThree_cubical propP) hreentryTarget hmassSlack
      reentry.normalization.final_extremal.delta_pos
      reentry.normalization.final_extremal.delta_le_one htargetLoss
  have htargetCWA : WZ2PaperConvexWolffBound
      reentry.normalization.croppedFamily
      (Kakeya.realRpowENN rho.1 (-targetLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := reentry.normalization.croppedRefined)
      (_shading2 := target)
      reentry.normalization.cropped_top_level_cwa hreentryTarget
      reentry.normalization.final_extremal.delta_pos
      reentry.normalization.final_extremal.delta_le_one
  let state : Proposition63ExtremalShadingData
      (sigma := sigma) (outputLoss := targetLoss)
      reentry.normalization.croppedRefined :=
    { shading := target
      subshading := data.commonPropertyThree_subshading propP
      extremal := htargetExtremal
      cwa := htargetCWA }
  exact ⟨state, rfl, data.commonPropertyThree_mass propP⟩

/-- The arbitrary-`tau` HIGH output before Lemma 4.11's separate
square-root-scale full-grain call.  Unlike `commonPropertyThree_high_localAD`,
this theorem does not assume `tau = sqrt rho` and does not claim AD. -/
theorem Proposition63DependentTwoLevelCoverData.pointCenteredCoveringData
    {delta sigma outerLoss reentryLoss innerLoss targetLoss epsilon₁ epsilon₃ : ℝ}
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
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := data.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃)
    (planeMap : Point3 → Point3)
    (incidenceBound : ℝ)
    (hplaneUnit : ∀ point ∈ propP.propertyThree.union,
      ‖planeMap point‖ = 1)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneIncidence : ∀ index point,
      ∀ hpoint : point ∈ propP.propertyOne.carrier index,
        |@Inner.inner ℝ Point3 _
          (reentry.normalization.croppedFamily.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (hreentryTarget : reentryLoss ≤ targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hrhoOne : rho.1 < 1)
    (hmassSlack : proposition63DependentPropertyThreeMassLoss
        rho.1 innerLogExponent * Kakeya.realRpowENN rho.1 targetLoss ≤
      Kakeya.realRpowENN rho.1 reentryLoss)
    (htauSmall : tau.1 ≤ 1 / 12)
    (hrhoSmall : rho.1 ≤ 1 / 1000)
    (hrhoTau : rho.1 ≤ tau.1)
    (htauSq : tau.1 ^ 2 ≤ 4 * rho.1)
    (htauOne : tau.1 ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hpropertyThreeFull :
      ∀ index point, point ∈ propP.propertyThree.carrier index →
        Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
            ENNReal.ofReal tau.1 ≤
          volume (propP.propertyThree.carrier index ∩
            Metric.closedBall point tau.1))
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
    ∃ state : Proposition63ExtremalShadingData
        (sigma := sigma) (outputLoss := targetLoss)
        reentry.normalization.croppedRefined,
      state.shading = data.commonPropertyThree propP ∧
      (proposition63DependentPropertyThreeMassLoss
          rho.1 innerLogExponent)⁻¹ *
          reentry.normalization.croppedRefined.mass ≤ state.shading.mass ∧
      PureWZ2PointCenteredCoveringAt state.shading planeMap
        (Real.toNNReal rho.1) tau.1
        (C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)) := by
  rcases data.extremalShadingData propP hreentryTarget htargetLoss hrhoOne
      hmassSlack with ⟨state, hstate, hmass⟩
  refine ⟨state, hstate, hmass, ?_⟩
  intro point
  have hpointCommon : (point : Point3) ∈
      (data.commonPropertyThree propP).union := by
    rw [← hstate]
    exact point.property
  have hpointProperty : (point : Point3) ∈ propP.propertyThree.union := by
    rw [← data.commonPropertyThree_union propP]
    exact hpointCommon
  have hcover := data.inner_propertyThree_projection_covering_of_arithmetic
    propP.toCordoba planeMap incidenceBound hplaneUnit hplaneLipschitz
    hplaneIncidence
    point hpointProperty htauSmall hrhoSmall hrhoTau htauSq htauOne
    hsigma hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale hrhoLog hlog
    hpropertyThreeFull haxis C harithmetic
  simpa only [PureWZ2PropertyPData.toCordoba, hstate,
    data.commonPropertyThree_union propP] using hcover

/-- Package the arbitrary-radius dependent HIGH output together with the
exact normalized-source multiplicity needed before lifting it back through
the current-shading re-entry. -/
theorem Proposition63DependentTwoLevelCoverData.currentPointCover
    {delta sigma outerLoss reentryLoss innerLoss targetLoss epsilon₁ epsilon₃ : ℝ}
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
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := data.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃)
    (planeMap : Point3 → Point3)
    (incidenceBound : ℝ)
    (hplaneUnit : ∀ point ∈ propP.propertyThree.union,
      ‖planeMap point‖ = 1)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneIncidence : ∀ index point,
      ∀ hpoint : point ∈ propP.propertyOne.carrier index,
        |@Inner.inner ℝ Point3 _
          (reentry.normalization.croppedFamily.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (hreentryTarget : reentryLoss ≤ targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hrhoOne : rho.1 < 1)
    (hmassSlack : proposition63DependentPropertyThreeMassLoss
        rho.1 innerLogExponent * Kakeya.realRpowENN rho.1 targetLoss ≤
      Kakeya.realRpowENN rho.1 reentryLoss)
    (htauSmall : tau.1 ≤ 1 / 12)
    (hrhoSmall : rho.1 ≤ 1 / 1000)
    (hrhoTau : rho.1 ≤ tau.1)
    (htauSq : tau.1 ^ 2 ≤ 4 * rho.1)
    (htauOne : tau.1 ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hpropertyThreeFull :
      ∀ index point, point ∈ propP.propertyThree.carrier index →
        Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
            ENNReal.ofReal tau.1 ≤
          volume (propP.propertyThree.carrier index ∩
            Metric.closedBall point tau.1))
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
    ∃ state : Proposition63ExtremalShadingData
        (sigma := sigma) (outputLoss := targetLoss)
        reentry.normalization.croppedRefined,
      state.shading = data.commonPropertyThree propP ∧
      (∀ point ∈ state.shading.union,
        state.shading.pointMultiplicity point =
          reentry.normalization.croppedRefined.pointMultiplicity point) ∧
      (proposition63DependentPropertyThreeMassLoss
          rho.1 innerLogExponent)⁻¹ *
          reentry.normalization.croppedRefined.mass ≤ state.shading.mass ∧
      PureWZ2PointCenteredCoveringAt state.shading planeMap
        (Real.toNNReal rho.1) tau.1
        (C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)) := by
  rcases data.pointCenteredCoveringData propP planeMap incidenceBound
      hplaneUnit hplaneLipschitz hplaneIncidence hreentryTarget htargetLoss
      hrhoOne hmassSlack htauSmall hrhoSmall hrhoTau htauSq htauOne hsigma
      hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale hrhoLog hlog
      hpropertyThreeFull haxis C harithmetic with
    ⟨state, hstate, hmass, hcover⟩
  refine ⟨state, hstate, ?_, hmass, hcover⟩
  intro point hpoint
  rw [hstate] at hpoint ⊢
  exact paperCommonSpatialHull_pointMultiplicity_eq
    reentry.normalization.croppedRefined propP.propertyThree point hpoint

/-- Structural one-scale assembler on the dependent common-spatial shading. -/
theorem Proposition63DependentTwoLevelCoverData.oneScale_of_localAD
    {delta sigma outerLoss reentryLoss innerLoss targetLoss epsilon₁ epsilon₃ : ℝ}
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
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := data.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃)
    (planeMap : Point3 → Point3)
    (hreentryTarget : reentryLoss ≤ targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hrhoOne : rho.1 < 1)
    (hmassSlack : proposition63DependentPropertyThreeMassLoss
        rho.1 innerLogExponent *
          Kakeya.realRpowENN rho.1 targetLoss ≤
        Kakeya.realRpowENN rho.1 reentryLoss)
    (hlocalAD : ∀ point : Point3,
      ∀ hpoint : point ∈ (data.commonPropertyThree propP).union,
        IsADSet1
          (scalarProjection (planeMap point)
            ((data.commonPropertyThree propP).union ∩
              Metric.closedBall point (Real.sqrt rho.1)))
          rho.1 (1 - sigma)
          (Kakeya.realRpowENN rho.1 (-targetLoss))) :
    ∃ oneScale : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := targetLoss)
        (rho := rho.1) (Y := reentry.normalization.croppedRefined)
        (fun point => planeMap point),
      oneScale.shading = data.commonPropertyThree propP ∧
      (proposition63DependentPropertyThreeMassLoss
          rho.1 innerLogExponent)⁻¹ *
          reentry.normalization.croppedRefined.mass ≤
        oneScale.shading.mass := by
  let massLoss := proposition63DependentPropertyThreeMassLoss
    rho.1 innerLogExponent
  have hmassLoss := proposition63DependentPropertyThreeMassLoss_pos_ne_top
    reentry.normalization.final_extremal.delta_pos hrhoOne innerLogExponent
  let target := data.commonPropertyThree propP
  have htargetExtremal : WZ2PaperCroppedIsExtremal
      sigma targetLoss reentry.normalization.croppedFamily target :=
    transfer_cropped_extremal_to_subshading massLoss
      hmassLoss.1 hmassLoss.2 reentry.normalization.final_extremal
      (data.commonPropertyThree_subshading propP)
      (data.commonPropertyThree_mass propP)
      (data.commonPropertyThree_cubical propP) hreentryTarget hmassSlack
      reentry.normalization.final_extremal.delta_pos
      reentry.normalization.final_extremal.delta_le_one htargetLoss
  have htargetCWA : WZ2PaperConvexWolffBound
      reentry.normalization.croppedFamily
      (Kakeya.realRpowENN rho.1 (-targetLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := reentry.normalization.croppedRefined)
      (_shading2 := target)
      reentry.normalization.cropped_top_level_cwa hreentryTarget
      reentry.normalization.final_extremal.delta_pos
      reentry.normalization.final_extremal.delta_le_one
  let oneScale : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := targetLoss)
      (rho := rho.1) (Y := reentry.normalization.croppedRefined)
      (fun point => planeMap point) :=
    { shading := target
      subshading := data.commonPropertyThree_subshading propP
      extremal := htargetExtremal
      cwa := htargetCWA
      local_ad := by
        intro point hpoint
        simpa only [target] using hlocalAD point hpoint }
  refine ⟨oneScale, rfl, ?_⟩
  exact data.commonPropertyThree_mass propP

/-- LOW part of the dependent one-scale estimate.  The conclusion is stated
on the same common-spatial Property-Three shading used by the HIGH part. -/
theorem Proposition63DependentTwoLevelCoverData.commonPropertyThree_low_localAD
    {delta sigma outerLoss reentryLoss innerLoss epsilon₁ epsilon₃
      lowScale targetLoss : ℝ}
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
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := data.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃)
    (planeMap : Point3 → Point3)
    (hplaneUnit : ∀ point ∈ (data.commonPropertyThree propP).union,
      ‖planeMap point‖ = 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hlowScale : 0 < lowScale) (hlowScaleSmall : lowScale ≤ 1 / 10000)
    (hlow : 5 * lowScale ^ 2 ≤ rho.1)
    (hconstant : Kakeya.realRpowENN lowScale (-1) ≤
      Kakeya.realRpowENN rho.1 (-targetLoss)) :
    ∀ point : Point3,
      ∀ hpoint : point ∈ (data.commonPropertyThree propP).union,
        IsADSet1
          (scalarProjection (planeMap point)
            ((data.commonPropertyThree propP).union ∩
              Metric.closedBall point (Real.sqrt rho.1)))
          rho.1 (1 - sigma)
          (Kakeya.realRpowENN rho.1 (-targetLoss)) := by
  intro point hpoint
  let E : Set ℝ := scalarProjection (planeMap point)
    ((data.commonPropertyThree propP).union ∩
      Metric.closedBall point (Real.sqrt rho.1))
  have hbounded : E ⊆ Set.Icc (-4 : ℝ) 4 := by
    apply scalarProjection_bounded (hplaneUnit point hpoint) E
    rintro value ⟨other, hother, rfl⟩
    exact ⟨other, hother.1, rfl⟩
  have hcenter : ∃ center : ℝ,
      E ⊆ Set.Icc (center - Real.sqrt rho.1)
        (center + Real.sqrt rho.1) := by
    let center : ℝ := @Inner.inner ℝ Point3 _ point (planeMap point)
    refine ⟨center, ?_⟩
    rintro value ⟨other, hother, rfl⟩
    have hdistance : ‖other - point‖ ≤ Real.sqrt rho.1 := by
      simpa [dist_eq_norm] using hother.2
    have hinner :
        |@Inner.inner ℝ Point3 _ other (planeMap point) - center| ≤
          Real.sqrt rho.1 := by
      have hrewrite : @Inner.inner ℝ Point3 _ other (planeMap point) - center =
          @Inner.inner ℝ Point3 _ (other - point) (planeMap point) := by
        simp [center, inner_sub_left]
      rw [hrewrite]
      calc
        |@Inner.inner ℝ Point3 _ (other - point) (planeMap point)| ≤
            ‖other - point‖ * ‖planeMap point‖ :=
          abs_real_inner_le_norm _ _
        _ = ‖other - point‖ := by rw [hplaneUnit point hpoint]; ring
        _ ≤ Real.sqrt rho.1 := hdistance
    rcases abs_le.mp hinner with ⟨hleft, hright⟩
    exact ⟨by linarith, by linarith⟩
  exact (low_case_trivial_ad_v2 hsigma hsigmaOne hlowScale
    hlowScaleSmall reentry.normalization.final_extremal.delta_pos hlow
    E hbounded hcenter).mono_constant hconstant

/-- HIGH part of the dependent one-scale estimate.  The second cover radius
is exactly the square root of the first cover radius, so its local ball and
the `PureWZ2OneScaleLocalGrainData` query ball are the same set. -/
theorem Proposition63DependentTwoLevelCoverData.commonPropertyThree_high_localAD
    {delta sigma outerLoss reentryLoss innerLoss targetLoss epsilon₁ epsilon₃ : ℝ}
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
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := data.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃)
    (planeMap : Point3 → Point3)
    (coefficient : NNReal)
    (incidenceBound : ℝ)
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneUnit : ∀ point ∈ (data.commonPropertyThree propP).union,
      ‖planeMap point‖ = 1)
    (hplaneIncidence : ∀ index point,
      ∀ hpoint : point ∈ propP.propertyOne.carrier index,
        |@Inner.inner ℝ Point3 _
          (reentry.normalization.croppedFamily.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (htauSqrt : tau.1 = Real.sqrt rho.1)
    (htauSmall : tau.1 ≤ 1 / 12)
    (hrhoSmall : rho.1 ≤ 1 / 1000)
    (hrhoTau : rho.1 ≤ tau.1)
    (htauSq : tau.1 ^ 2 ≤ 4 * rho.1)
    (htauOne : tau.1 ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hpropertyThreeFull :
      ∀ index point, point ∈ propP.propertyThree.carrier index →
        Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
            ENNReal.ofReal tau.1 ≤
          volume (propP.propertyThree.carrier index ∩
            Metric.closedBall point tau.1))
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
              coefficient /
              rho.1 + 2)) ≤
        C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma))
    (heffectiveOne : (1 : ENNReal) ≤
      C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma))
    (heffectiveTop : C *
      Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma) ≠ ⊤)
    (hconstant : 10 *
        (C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)) ≤
      Kakeya.realRpowENN rho.1 (-targetLoss)) :
    ∀ point : Point3,
      ∀ hpoint : point ∈ (data.commonPropertyThree propP).union,
        IsADSet1
          (scalarProjection (planeMap point)
            ((data.commonPropertyThree propP).union ∩
              Metric.closedBall point (Real.sqrt rho.1)))
          rho.1 (1 - sigma)
          (Kakeya.realRpowENN rho.1 (-targetLoss)) := by
  intro point hpoint
  have hpointProperty : point ∈ propP.propertyThree.union := by
    rw [← data.commonPropertyThree_union propP]
    exact hpoint
  have hplaneUnitProperty : ∀ other ∈ propP.propertyThree.union,
      ‖planeMap other‖ = 1 := by
    intro other hother
    apply hplaneUnit other
    rw [data.commonPropertyThree_union propP]
    exact hother
  have hcover :=
    data.inner_propertyThree_projection_covering_of_arithmetic propP.toCordoba
      planeMap incidenceBound hplaneUnitProperty hplaneLipschitz
      hplaneIncidence
      point hpointProperty htauSmall hrhoSmall hrhoTau htauSq htauOne hsigma
      hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale hrhoLog hlog
      hpropertyThreeFull haxis C harithmetic
  let targetSet : Set ℝ := scalarProjection (planeMap point)
    ((data.commonPropertyThree propP).union ∩
      Metric.closedBall point (Real.sqrt rho.1))
  have hcoverTarget :
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho.1) targetSet) :
          ENNReal) ≤
        C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma) := by
    have hset : targetSet = scalarProjection (planeMap point)
        (propP.propertyThree.union ∩ Metric.closedBall point tau.1) := by
      simp only [targetSet, data.commonPropertyThree_union propP, htauSqrt]
    simpa only [PureWZ2PropertyPData.toCordoba, hset] using hcover
  have hpaper : PureWZ2PaperADSet1 targetSet rho.1 (1 - sigma)
      (C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)) :=
    slab_to_ad_wz1 (hplaneUnit point hpoint)
      reentry.normalization.final_extremal.delta_pos hsigma hsigmaOne
      heffectiveOne heffectiveTop hcoverTarget
  have hbounded : targetSet ⊆ Set.Icc (-4 : ℝ) 4 := by
    apply scalarProjection_bounded (hplaneUnit point hpoint) targetSet
    rintro value ⟨other, hother, rfl⟩
    exact ⟨other, hother.1, rfl⟩
  have hinternal : IsADSet1 targetSet rho.1 (1 - sigma)
      (10 * (C * Kakeya.realRpowENN
        (tau.1 / rho.1) (1 - sigma))) :=
    pure_wz2_paper_ad_bridge.1 targetSet rho.1 (1 - sigma)
      (C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma))
      hbounded hpaper
  exact hinternal.mono_constant hconstant

/-- Choose the paper's LOW or HIGH estimate on one fixed dependent
Property-(P) shading, then assemble the complete one-scale output. -/
theorem Proposition63DependentTwoLevelCoverData.oneScale_low_high
    {delta sigma outerLoss reentryLoss innerLoss targetLoss epsilon₁ epsilon₃
      lowScale : ℝ}
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
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := data.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃)
    (planeMap : Point3 → Point3)
    (coefficient : NNReal)
    (incidenceBound : ℝ)
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneUnit : ∀ point ∈ (data.commonPropertyThree propP).union,
      ‖planeMap point‖ = 1)
    (hplaneIncidence : ∀ index point,
      ∀ hpoint : point ∈ propP.propertyOne.carrier index,
        |@Inner.inner ℝ Point3 _
          (reentry.normalization.croppedFamily.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (hreentryTarget : reentryLoss ≤ targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hrhoOne : rho.1 < 1)
    (hmassSlack : proposition63DependentPropertyThreeMassLoss
        rho.1 innerLogExponent * Kakeya.realRpowENN rho.1 targetLoss ≤
        Kakeya.realRpowENN rho.1 reentryLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hlowScale : 0 < lowScale) (hlowScaleSmall : lowScale ≤ 1 / 10000)
    (hlowConstant : Kakeya.realRpowENN lowScale (-1) ≤
      Kakeya.realRpowENN rho.1 (-targetLoss))
    (htauSqrt : tau.1 = Real.sqrt rho.1)
    (htauSmall : tau.1 ≤ 1 / 12)
    (hrhoSmall : rho.1 ≤ 1 / 1000)
    (hrhoTau : rho.1 ≤ tau.1)
    (htauSq : tau.1 ^ 2 ≤ 4 * rho.1)
    (htauOne : tau.1 ≤ 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hpropertyThreeFull :
      ∀ index point, point ∈ propP.propertyThree.carrier index →
        Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
            ENNReal.ofReal tau.1 ≤
          volume (propP.propertyThree.carrier index ∩
            Metric.closedBall point tau.1))
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
              coefficient /
              rho.1 + 2)) ≤
        C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma))
    (heffectiveOne : (1 : ENNReal) ≤
      C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma))
    (heffectiveTop : C *
      Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma) ≠ ⊤)
    (hhighConstant : 10 *
        (C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)) ≤
      Kakeya.realRpowENN rho.1 (-targetLoss)) :
    ∃ oneScale : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := targetLoss)
        (rho := rho.1) (Y := reentry.normalization.croppedRefined)
        (fun point => planeMap point),
      oneScale.shading = data.commonPropertyThree propP ∧
      (proposition63DependentPropertyThreeMassLoss
          rho.1 innerLogExponent)⁻¹ *
          reentry.normalization.croppedRefined.mass ≤
        oneScale.shading.mass := by
  apply data.oneScale_of_localAD propP planeMap hreentryTarget htargetLoss
    hrhoOne hmassSlack
  by_cases hlow : 5 * lowScale ^ 2 ≤ rho.1
  · exact data.commonPropertyThree_low_localAD propP planeMap hplaneUnit
      hsigma hsigmaOne hlowScale hlowScaleSmall hlow hlowConstant
  · exact data.commonPropertyThree_high_localAD propP planeMap coefficient
      incidenceBound hplaneLipschitz hplaneUnit hplaneIncidence htauSqrt htauSmall
      hrhoSmall hrhoTau htauSq htauOne
      hsigma hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale hrhoLog
      hlog hpropertyThreeFull haxis C harithmetic heffectiveOne heffectiveTop
      hhighConstant

/-- Feed a completed dependent one-scale analytic output into the concrete
full-grain step.
The left mass factor is the product of the current re-entry retention and the
dependent second-cover/Property-(P) retention; the regularization loss stays
on the right. -/
theorem proposition63_uniformFullGrainStep_of_dependentOneScale
    {fineDelta sigma outerLoss coarseInputLoss coarseNormalizationLoss
      reentryLoss innerLoss targetLoss middleLoss finalLoss epsilon₁ epsilon₃ : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily fineDelta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale fineDelta}
    {outerLogExponent normalizationExponent innerLogExponent : ℕ}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      normalizationExponent)
    (current : WZ1PaperTubeShading coarseNormalized.croppedFamily)
    (currentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) coarseNormalized current)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      coarseNormalized.croppedFamily.tube index =
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
    (dependent : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      (proposition63DependentCoarseReentryOfCurrent outer coarseNormalized
        current currentReentry ancestorEmbedding ancestor_tube_eq
        current_sub_outer ancestorRetentionFactor
        ancestorRetentionFactor_pos ancestorRetentionFactor_ne_top
        current_retained_mass) tau)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := dependent.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃)
    (planeMap : Point3 → Point3)
    (coefficient : NNReal) (uniformPreparationLoss : ENNReal)
    (uniformCoverBudget : ℕ)
    (analytic : ∃ original : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := targetLoss)
        (rho := rho.1)
        (Y := currentReentry.normalization.croppedRefined)
        (fun point => planeMap point),
      original.shading = dependent.commonPropertyThree propP ∧
      (proposition63DependentPropertyThreeMassLoss
          rho.1 innerLogExponent)⁻¹ *
          currentReentry.normalization.croppedRefined.mass ≤
        original.shading.mass)
    (hfirstMiddle : targetLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (hmultiplicitySlack :
      (((Nat.log 2 currentReentry.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal) * Kakeya.realRpowENN rho.1 middleLoss) ≤
        Kakeya.realRpowENN rho.1 targetLoss)
    (hrhoSmall24 : rho.1 ≤ 1 / 24)
    (hperiodicScale : 50 * rho.1 ≤ tau.1)
    (htauPos : 0 < tau.1)
    (htauOne : tau.1 ≤ 1)
    (hboundaryScalar :
      2 * 24000000 *
          (Kakeya.realRpowENN rho.1 (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (rho.1 / tau.1)) <
        Kakeya.realRpowENN rho.1 middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss)
    (hfinalLoss : 0 < finalLoss)
    (hbalancingSlack : ∀ original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := targetLoss)
      (rho := rho.1) (Y := currentReentry.normalization.croppedRefined)
      (fun point => planeMap point),
      ∀ prepared : Proposition63OneScaleConstantMultiplicityData
        (secondLoss := middleLoss) planeMap original,
      ∀ fresh : Proposition63FreshBalancedCellsData
        (sqrtScale := tau.1) planeMap original prepared
          original.extremal.delta_pos,
        fresh.freshLoss * Kakeya.realRpowENN rho.1 finalLoss ≤
          Kakeya.realRpowENN rho.1 middleLoss)
    (hpreparationBudget : ∀ original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := targetLoss)
      (rho := rho.1) (Y := currentReentry.normalization.croppedRefined)
      (fun point => planeMap point),
      ∀ prepared : Proposition63OneScaleConstantMultiplicityData
        (secondLoss := middleLoss) planeMap original,
      ∀ fresh : Proposition63FreshBalancedCellsData
        (sqrtScale := tau.1) planeMap original prepared
          original.extremal.delta_pos,
        fresh.preparedLoss ≤ uniformPreparationLoss)
    (plane_unit : ∀ point ∈ (dependent.commonPropertyThree propP).union,
      ‖planeMap point‖ = 1)
    (cover_budget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN rho.1 (-finalLoss) *
              Kakeya.realRpowENN (1 / rho.1) (1 - sigma))) ≤
        (uniformCoverBudget : ENNReal)) :
    Nonempty (Proposition63UniformFullGrainStepData
      (firstLoss := targetLoss) (secondLoss := finalLoss)
      (queryScale := rho.1) (sqrtScale := tau.1) currentReentry planeMap
      ((proposition63DependentPropertyThreeMassLoss
          rho.1 innerLogExponent)⁻¹ *
        ((73 / 100 : ENNReal) * currentReentry.normalizationWeight))
      currentReentry.regularized.regularizationLoss coefficient
      uniformPreparationLoss uniformCoverBudget) := by
  rcases analytic with ⟨original, horiginal, hnormalizedMass⟩
  have hscaledReentry := mul_le_mul_left' currentReentry.reentryMassRetention
    (proposition63DependentPropertyThreeMassLoss
      rho.1 innerLogExponent)⁻¹
  have hincoming :
      ((proposition63DependentPropertyThreeMassLoss
            rho.1 innerLogExponent)⁻¹ *
          ((73 / 100 : ENNReal) * currentReentry.normalizationWeight)) *
          current.mass ≤
        currentReentry.regularized.regularizationLoss *
          original.shading.mass := by
    calc
      ((proposition63DependentPropertyThreeMassLoss
              rho.1 innerLogExponent)⁻¹ *
            ((73 / 100 : ENNReal) * currentReentry.normalizationWeight)) *
            current.mass =
          (proposition63DependentPropertyThreeMassLoss
              rho.1 innerLogExponent)⁻¹ *
            (((73 / 100 : ENNReal) *
              currentReentry.normalizationWeight) * current.mass) := by ring
      _ ≤ (proposition63DependentPropertyThreeMassLoss
              rho.1 innerLogExponent)⁻¹ *
            (currentReentry.regularized.regularizationLoss *
              currentReentry.normalization.croppedRefined.mass) :=
        hscaledReentry
      _ = currentReentry.regularized.regularizationLoss *
          ((proposition63DependentPropertyThreeMassLoss
              rho.1 innerLogExponent)⁻¹ *
            currentReentry.normalization.croppedRefined.mass) := by ring
      _ ≤ currentReentry.regularized.regularizationLoss *
          original.shading.mass := by gcongr
  apply proposition63_uniformFullGrainStep_of_freshBalancingCWA currentReentry
    planeMap
    ((proposition63DependentPropertyThreeMassLoss
        rho.1 innerLogExponent)⁻¹ *
      ((73 / 100 : ENNReal) * currentReentry.normalizationWeight))
    currentReentry.regularized.regularizationLoss coefficient
    uniformPreparationLoss uniformCoverBudget original hincoming
    hfirstMiddle hmiddleLoss hmultiplicitySlack hrhoSmall24 hperiodicScale
    htauPos htauOne hboundaryScalar hmiddleFinal hfinalLoss
    (hbalancingSlack original) (hpreparationBudget original)
  · intro point hpoint
    rw [horiginal] at hpoint
    exact plane_unit point hpoint
  · exact cover_budget

/-- Canonical-budget version of the dependent full-grain step.  The
multiplicity and fresh-balancing losses are produced internally and bounded
by the fixed physical logarithmic envelope. -/
theorem proposition63_uniformFullGrainStep_of_dependentOneScale_uniform
    {fineDelta sigma outerLoss coarseInputLoss coarseNormalizationLoss
      reentryLoss innerLoss targetLoss middleLoss finalLoss epsilon₁ epsilon₃ : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily fineDelta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale fineDelta}
    {outerLogExponent normalizationExponent innerLogExponent : ℕ}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      normalizationExponent)
    (current : WZ1PaperTubeShading coarseNormalized.croppedFamily)
    (currentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) coarseNormalized current)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      coarseNormalized.croppedFamily.tube index =
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
    (dependent : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      (proposition63DependentCoarseReentryOfCurrent outer coarseNormalized
        current currentReentry ancestorEmbedding ancestor_tube_eq
        current_sub_outer ancestorRetentionFactor
        ancestorRetentionFactor_pos ancestorRetentionFactor_ne_top
        current_retained_mass) tau)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := dependent.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃)
    (planeMap : Point3 → Point3)
    (coefficient : NNReal) (uniformCoverBudget : ℕ)
    (analytic : ∃ original : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := targetLoss)
        (rho := rho.1)
        (Y := currentReentry.normalization.croppedRefined)
        (fun point => planeMap point),
      original.shading = dependent.commonPropertyThree propP ∧
      (proposition63DependentPropertyThreeMassLoss
          rho.1 innerLogExponent)⁻¹ *
          currentReentry.normalization.croppedRefined.mass ≤
        original.shading.mass)
    (hfirstMiddle : targetLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (hmultiplicitySlack :
      (((Nat.log 2 currentReentry.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal) * Kakeya.realRpowENN rho.1 middleLoss) ≤
        Kakeya.realRpowENN rho.1 targetLoss)
    (hrhoSmall24 : rho.1 ≤ 1 / 24)
    (hperiodicScale : 50 * rho.1 ≤ tau.1)
    (htauPos : 0 < tau.1)
    (htauOne : tau.1 ≤ 1)
    (hboundaryScalar :
      2 * 24000000 *
          (Kakeya.realRpowENN rho.1 (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (rho.1 / tau.1)) <
        Kakeya.realRpowENN rho.1 middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss)
    (hfinalLoss : 0 < finalLoss)
    (hbalancingSlack : proposition63FreshBalancingEnvelope rho.1 *
        Kakeya.realRpowENN rho.1 finalLoss ≤
      Kakeya.realRpowENN rho.1 middleLoss)
    (plane_unit : ∀ point ∈ (dependent.commonPropertyThree propP).union,
      ‖planeMap point‖ = 1)
    (cover_budget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN rho.1 (-finalLoss) *
              Kakeya.realRpowENN (1 / rho.1) (1 - sigma))) ≤
        (uniformCoverBudget : ENNReal)) :
    Nonempty (Proposition63UniformFullGrainStepData
      (firstLoss := targetLoss) (secondLoss := finalLoss)
      (queryScale := rho.1) (sqrtScale := tau.1) currentReentry planeMap
      ((proposition63DependentPropertyThreeMassLoss
          rho.1 innerLogExponent)⁻¹ *
        ((73 / 100 : ENNReal) * currentReentry.normalizationWeight))
      currentReentry.regularized.regularizationLoss coefficient
      (proposition63UniformPreparationLoss
        currentReentry.normalization.croppedFamily)
      uniformCoverBudget) := by
  rcases analytic with ⟨original, horiginal, hnormalizedMass⟩
  have hscaledReentry := mul_le_mul_left' currentReentry.reentryMassRetention
    (proposition63DependentPropertyThreeMassLoss
      rho.1 innerLogExponent)⁻¹
  have hincoming :
      ((proposition63DependentPropertyThreeMassLoss
            rho.1 innerLogExponent)⁻¹ *
          ((73 / 100 : ENNReal) * currentReentry.normalizationWeight)) *
          current.mass ≤
        currentReentry.regularized.regularizationLoss *
          original.shading.mass := by
    calc
      ((proposition63DependentPropertyThreeMassLoss
              rho.1 innerLogExponent)⁻¹ *
            ((73 / 100 : ENNReal) * currentReentry.normalizationWeight)) *
            current.mass =
          (proposition63DependentPropertyThreeMassLoss
              rho.1 innerLogExponent)⁻¹ *
            (((73 / 100 : ENNReal) *
              currentReentry.normalizationWeight) * current.mass) := by ring
      _ ≤ (proposition63DependentPropertyThreeMassLoss
              rho.1 innerLogExponent)⁻¹ *
            (currentReentry.regularized.regularizationLoss *
              currentReentry.normalization.croppedRefined.mass) :=
        hscaledReentry
      _ = currentReentry.regularized.regularizationLoss *
          ((proposition63DependentPropertyThreeMassLoss
              rho.1 innerLogExponent)⁻¹ *
            currentReentry.normalization.croppedRefined.mass) := by ring
      _ ≤ currentReentry.regularized.regularizationLoss *
          original.shading.mass := by gcongr
  apply proposition63_uniformFullGrainStep_of_freshBalancingCWA_uniform
    currentReentry planeMap
    ((proposition63DependentPropertyThreeMassLoss
        rho.1 innerLogExponent)⁻¹ *
      ((73 / 100 : ENNReal) * currentReentry.normalizationWeight))
    currentReentry.regularized.regularizationLoss coefficient
    uniformCoverBudget original hincoming hfirstMiddle hmiddleLoss
    hmultiplicitySlack hrhoSmall24 hperiodicScale htauPos htauOne
    hboundaryScalar hmiddleFinal hfinalLoss hbalancingSlack
  · intro point hpoint
    rw [horiginal] at hpoint
    exact plane_unit point hpoint
  · exact cover_budget

/-- Paper-order composition of the dependent LOW/HIGH dichotomy with the
CWA boundary-layer preparation and its canonical uniform loss budget. -/
theorem proposition63_uniformFullGrainStep_of_dependentLowHigh
    {fineDelta sigma outerLoss coarseInputLoss coarseNormalizationLoss
      reentryLoss innerLoss targetLoss middleLoss finalLoss epsilon₁ epsilon₃
      lowScale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily fineDelta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale fineDelta}
    {outerLogExponent normalizationExponent innerLogExponent : ℕ}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      normalizationExponent)
    (current : WZ1PaperTubeShading coarseNormalized.croppedFamily)
    (currentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) coarseNormalized current)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      coarseNormalized.croppedFamily.tube index =
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
    (dependent : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      (proposition63DependentCoarseReentryOfCurrent outer coarseNormalized
        current currentReentry ancestorEmbedding ancestor_tube_eq
        current_sub_outer ancestorRetentionFactor
        ancestorRetentionFactor_pos ancestorRetentionFactor_ne_top
        current_retained_mass) tau)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := dependent.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃)
    (planeMap : Point3 → Point3)
    (coefficient : NNReal) (incidenceBound : ℝ)
    (uniformCoverBudget : ℕ)
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneUnit : ∀ point ∈ (dependent.commonPropertyThree propP).union,
      ‖planeMap point‖ = 1)
    (hplaneIncidence : ∀ index point,
      ∀ hpoint : point ∈ propP.propertyOne.carrier index,
        |@Inner.inner ℝ Point3 _
          (currentReentry.normalization.croppedFamily.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (hreentryTarget : currentReentry.reentryNormalizationLoss ≤ targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hrhoOne : rho.1 < 1)
    (hmassSlack : proposition63DependentPropertyThreeMassLoss
        rho.1 innerLogExponent * Kakeya.realRpowENN rho.1 targetLoss ≤
      Kakeya.realRpowENN rho.1 currentReentry.reentryNormalizationLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hlowScale : 0 < lowScale) (hlowScaleSmall : lowScale ≤ 1 / 10000)
    (hlowConstant : Kakeya.realRpowENN lowScale (-1) ≤
      Kakeya.realRpowENN rho.1 (-targetLoss))
    (htauSqrt : tau.1 = Real.sqrt rho.1)
    (htauSmall : tau.1 ≤ 1 / 12)
    (hrhoSmall : rho.1 ≤ 1 / 1000)
    (hrhoTau : rho.1 ≤ tau.1)
    (htauSq : tau.1 ^ 2 ≤ 4 * rho.1)
    (htauOne : tau.1 ≤ 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hpropertyThreeFull :
      ∀ index point, point ∈ propP.propertyThree.carrier index →
        Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
            ENNReal.ofReal tau.1 ≤
          volume (propP.propertyThree.carrier index ∩
            Metric.closedBall point tau.1))
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
              coefficient /
              rho.1 + 2)) ≤
        C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma))
    (heffectiveOne : (1 : ENNReal) ≤
      C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma))
    (heffectiveTop : C *
      Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma) ≠ ⊤)
    (hhighConstant : 10 *
        (C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)) ≤
      Kakeya.realRpowENN rho.1 (-targetLoss))
    (hfirstMiddle : targetLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (hmultiplicitySlack :
      (((Nat.log 2 currentReentry.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal) * Kakeya.realRpowENN rho.1 middleLoss) ≤
        Kakeya.realRpowENN rho.1 targetLoss)
    (hrhoSmall24 : rho.1 ≤ 1 / 24)
    (hperiodicScale : 50 * rho.1 ≤ tau.1)
    (htauPos : 0 < tau.1)
    (hboundaryScalar :
      2 * 24000000 *
          (Kakeya.realRpowENN rho.1 (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (rho.1 / tau.1)) <
        Kakeya.realRpowENN rho.1 middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss)
    (hfinalLoss : 0 < finalLoss)
    (hbalancingSlack : proposition63FreshBalancingEnvelope rho.1 *
        Kakeya.realRpowENN rho.1 finalLoss ≤
      Kakeya.realRpowENN rho.1 middleLoss)
    (cover_budget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN rho.1 (-finalLoss) *
              Kakeya.realRpowENN (1 / rho.1) (1 - sigma))) ≤
        (uniformCoverBudget : ENNReal)) :
    Nonempty (Proposition63UniformFullGrainStepData
      (firstLoss := targetLoss) (secondLoss := finalLoss)
      (queryScale := rho.1) (sqrtScale := tau.1) currentReentry planeMap
      ((proposition63DependentPropertyThreeMassLoss
          rho.1 innerLogExponent)⁻¹ *
        ((73 / 100 : ENNReal) * currentReentry.normalizationWeight))
      currentReentry.regularized.regularizationLoss coefficient
      (proposition63UniformPreparationLoss
        currentReentry.normalization.croppedFamily)
      uniformCoverBudget) := by
  apply proposition63_uniformFullGrainStep_of_dependentOneScale_uniform
    outer coarseNormalized current currentReentry ancestorEmbedding
    ancestor_tube_eq current_sub_outer ancestorRetentionFactor
    ancestorRetentionFactor_pos ancestorRetentionFactor_ne_top
    current_retained_mass dependent propP planeMap coefficient
    uniformCoverBudget
    (dependent.oneScale_low_high propP planeMap coefficient incidenceBound
      hplaneLipschitz
      hplaneUnit hplaneIncidence hreentryTarget
      htargetLoss hrhoOne hmassSlack hsigma hsigmaOne hlowScale
      hlowScaleSmall hlowConstant htauSqrt htauSmall hrhoSmall
      hrhoTau htauSq htauOne hepsilon₁ hepsilon₃ hepsilonSum logScale
      hrhoLog hlog hpropertyThreeFull haxis C harithmetic heffectiveOne
      heffectiveTop hhighConstant)
    hfirstMiddle hmiddleLoss hmultiplicitySlack hrhoSmall24 hperiodicScale
    htauPos htauOne hboundaryScalar hmiddleFinal hfinalLoss hbalancingSlack
    hplaneUnit cover_budget

end Kakeya.Assouad.PureWZ2

end
