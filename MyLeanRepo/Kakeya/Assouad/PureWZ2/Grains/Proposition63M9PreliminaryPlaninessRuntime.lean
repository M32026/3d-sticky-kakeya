import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PreliminaryFiniteGridProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RootPlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ExtremalOneScalePlaneMap

/-!
# M9 preliminary planiness runtime boundary

The preliminary paper stage first constructs one genuine finite-planiness
refinement and only then runs the finite rich Lemma-4.12 iteration on the same
plane map.  This record preserves the map and its fine-cell constancy across
that boundary.  In particular, the later iteration does not reconstruct a
map from the every-scale local-AD compatibility interface.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- The selected preliminary planiness shading, with exactly the data needed
to re-enter it and keep its plane map fixed through the rich finite iteration. -/
structure Proposition63M9PreliminaryPlaninessRuntimeData
    {delta sigma initialInputLoss normalizationLoss producerLoss coefficient
      incidence : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (source : WZ1PaperTubeShading initialNormalized.croppedFamily) where
  planiness : BoundedBalancedFinitePlaninessData
    (coefficient := coefficient) source incidence
  subshading : PaperIsSubshading planiness.data.refinement.shading
    initialNormalized.croppedRefined
  extremal : WZ2PaperCroppedIsExtremal sigma producerLoss
    initialNormalized.croppedFamily planiness.data.refinement.shading
  topLevelCWA : WZ2PaperConvexWolffBound initialNormalized.croppedFamily
    (Kakeya.realRpowENN delta (-producerLoss))
  incidence_nonnegative : 0 ≤ incidence

/-- Run only the genuine preliminary finite-planiness selection.  Unlike the
legacy finite-grid wrapper, this boundary does not ask one fixed coarse
sticky output to prove all later HIGH-scale local-AD estimates. -/
theorem proposition63_m9_preliminary_planiness_runtime
    {delta sigma initialInputLoss normalizationLoss preliminaryStickyLoss
      planinessLoss producerLoss tau epsilon₁ epsilon₃ coefficient incidence
      densityLoss kappa eta : ℝ}
    {rho : WZ2PaperRequestedScale delta}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent logExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := preliminaryStickyLoss)
      initialNormalized.croppedRefined rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (commonExtremal : WZ2PaperCroppedIsExtremal sigma planinessLoss
      initialNormalized.croppedFamily
      (ambientPropertyThreeCommonHull sticky propP.propertyThree))
    (hline : WZ1PaperIsLineClass initialNormalized.croppedFamily)
    (planinessSchedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * planinessLoss)
    (hplaninessLoss : 0 < planinessLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hplaninessSmall : Kakeya.realRpowENN delta planinessLoss < 1 / 4)
    (hfixedAbsorb : (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
      Kakeya.realRpowENN delta (-sigma + 4 * planinessLoss))
    (hsparsePackage : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa)
      (ambientPropertyThreeCommonHull sticky propP.propertyThree)
      (Kakeya.realRpowENN delta (2 - sigma + 3 * planinessLoss)),
        Nonempty (SparseRelativeBandCVPackage
          (ambientPropertyThreeCommonHull sticky propP.propertyThree)
          prepared))
    (hdenseIncidence : eta ≤ incidence)
    (hsparseIncidence : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa)
      (ambientPropertyThreeCommonHull sticky propP.propertyThree)
      (Kakeya.realRpowENN delta (2 - sigma + 3 * planinessLoss)),
      ∀ package : SparseRelativeBandCVPackage
        (ambientPropertyThreeCommonHull sticky propP.propertyThree) prepared,
          package.tau / kappa ≤ incidence)
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaPositive : 0 < kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (hetaPositive : 0 < eta)
    (hetaHalf : eta ≤ 1 / 2)
    (hcoefficient : 0 < coefficient)
    (hactualSmall : ∀ coordinate, coordinate < 1 →
      (commonExtremal.cwa_nearby_scales.chosenNearby
        (planinessSchedule.requested coordinate)).rho < 1 / 8)
    (hnearbyGap : ∀ coordinate, coordinate < 1 →
      16 * (commonExtremal.cwa_nearby_scales.chosenNearby
        (planinessSchedule.requested coordinate)).rho ≤ kappa)
    (hnormalizationSticky : normalizationLoss ≤ preliminaryStickyLoss)
    (hstickyProducer : preliminaryStickyLoss ≤ producerLoss)
    (hmassEnvelopeSlack :
      (propertyThreeCommonHullMassLoss sticky *
          proposition63PreliminaryPlaninessMassEnvelope planinessSchedule
            sigma planinessLoss incidence kappa eta) *
          Kakeya.realRpowENN delta producerLoss ≤
        Kakeya.realRpowENN delta preliminaryStickyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hproducerLoss : 0 < producerLoss)
    (hsigmaOne : sigma < 1) :
    Nonempty (Proposition63M9PreliminaryPlaninessRuntimeData
      (producerLoss := producerLoss) (coefficient := coefficient)
      (incidence := incidence) initialNormalized
      (ambientPropertyThreeCommonHull sticky propP.propertyThree)) := by
  have hparentKappa : ∀ coordinate, coordinate < 1 →
      8 * (commonExtremal.cwa_nearby_scales.chosenNearby
        (planinessSchedule.requested coordinate)).rho < kappa := by
    intro coordinate hcoordinate
    have hrho := (commonExtremal.cwa_nearby_scales.chosenNearby
      (planinessSchedule.requested coordinate)).scaleData.rho_pos
    linarith [hnearbyGap coordinate hcoordinate]
  rcases high_multiplicity_balanced_direction_dichotomy commonExtremal hline
      hdeltaSmall hdensityLoss hplaninessLoss hplaninessSmall hfixedAbsorb with
    ⟨dichotomy⟩
  rcases high_multiplicity_balanced_weak_finite_lipschitz_coefficient
      commonExtremal.cwa_nearby_scales commonExtremal.nonempty hline
      (by simpa [hdensityLoss] using dichotomy) hsparsePackage
      1 planinessSchedule.requested planinessSchedule.spatialScale
      planinessSchedule.variationScale planinessSchedule.K
      hkappaNonnegative hkappaPositive hkappaHalf hdelta hetaPositive
      hetaHalf hcoefficient hactualSmall hparentKappa
      planinessSchedule.spatial_pos planinessSchedule.variation_pos
      planinessSchedule.K_pos planinessSchedule.spatial_aligned
      planinessSchedule.covers with
    ⟨finite⟩
  have hboundedIncidence : finite.incidence ≤ incidence := by
    rcases finite.branch_formula with hdense | hsparse
    · rw [hdense.1]
      exact hdenseIncidence
    · rcases hsparse with
        ⟨prepared, package, hincidence, _hleft, _hright⟩
      rw [hincidence]
      exact hsparseIncidence prepared package
  let bounded : BoundedBalancedFinitePlaninessData
      (coefficient := coefficient)
      (ambientPropertyThreeCommonHull sticky propP.propertyThree) incidence :=
    { data := finite.toPlaniness hdelta
      incidence_le := hboundedIncidence }
  have hmassSlack :
      (propertyThreeCommonHullMassLoss sticky * bounded.data.massLoss) *
          Kakeya.realRpowENN delta producerLoss ≤
        Kakeya.realRpowENN delta preliminaryStickyLoss := by
    have hdensityExponent : 0 ≤ 2 - sigma + 3 * planinessLoss := by
      linarith
    have henvelope :=
      proposition63PreliminaryPlaninessMassLoss_le_envelope
        (eta := eta) (incidence := incidence) commonExtremal
        planinessSchedule (hnearbyGap 0 (by norm_num)) hkappaPositive
        hdelta hdeltaOne.le hdensityExponent
    rcases finite.branch_formula with hdense | hsparse
    · have hbranch : bounded.data.massLoss ≤
          proposition63PreliminaryPlaninessMassEnvelope planinessSchedule
            sigma planinessLoss incidence kappa eta := by
        simpa only [bounded,
          HighMultiplicityBalancedFiniteLipschitzOutput.toPlaniness,
          BalancedFinitePlaninessData.massLoss,
          proposition63PreliminaryDensePlaninessMassLoss, hdense.2.1,
          hdense.2.2] using henvelope.1
      exact (mul_le_mul_right'
        (mul_le_mul_left' hbranch (propertyThreeCommonHullMassLoss sticky))
        (Kakeya.realRpowENN delta producerLoss)).trans hmassEnvelopeSlack
    · rcases hsparse with
        ⟨prepared, package, _hincidence, hleft, hright⟩
      have hbranch : bounded.data.massLoss ≤
          proposition63PreliminaryPlaninessMassEnvelope planinessSchedule
            sigma planinessLoss incidence kappa eta := by
        simpa only [bounded,
          HighMultiplicityBalancedFiniteLipschitzOutput.toPlaniness,
          BalancedFinitePlaninessData.massLoss,
          proposition63PreliminarySparsePlaninessMassLoss, hleft, hright] using
          henvelope.2 prepared package (hsparseIncidence prepared package)
      exact (mul_le_mul_right'
        (mul_le_mul_left' hbranch (propertyThreeCommonHullMassLoss sticky))
        (Kakeya.realRpowENN delta producerLoss)).trans hmassEnvelopeSlack
  have hcommonMass :
      (propertyThreeCommonHullMassLoss sticky)⁻¹ *
          initialNormalized.croppedRefined.mass ≤
        (ambientPropertyThreeCommonHull sticky propP.propertyThree).mass :=
    propertyThreeCommonHullMassLoss_inv_mul_source_mass_le
      sticky propP hdelta
  let totalMassLoss :=
    propertyThreeCommonHullMassLoss sticky * bounded.data.massLoss
  have htotalPos : 0 < totalMassLoss :=
    ENNReal.mul_pos (propertyThreeCommonHullMassLoss_pos sticky).ne'
      bounded.data.massLoss_pos.ne'
  have htotalTop : totalMassLoss ≠ ⊤ :=
    ENNReal.mul_ne_top
      (propertyThreeCommonHullMassLoss_ne_top sticky hdelta hdeltaOne)
      bounded.data.massLoss_ne_top
  have htotalMass : totalMassLoss⁻¹ *
        initialNormalized.croppedRefined.mass ≤
      bounded.data.refinement.shading.mass := by
    calc
      totalMassLoss⁻¹ * initialNormalized.croppedRefined.mass =
          bounded.data.massLoss⁻¹ *
            ((propertyThreeCommonHullMassLoss sticky)⁻¹ *
              initialNormalized.croppedRefined.mass) := by
        dsimp only [totalMassLoss]
        rw [ENNReal.mul_inv
          (Or.inl (propertyThreeCommonHullMassLoss_pos sticky).ne')
          (Or.inl (propertyThreeCommonHullMassLoss_ne_top
            sticky hdelta hdeltaOne))]
        ring
      _ ≤ bounded.data.massLoss⁻¹ *
          (ambientPropertyThreeCommonHull sticky propP.propertyThree).mass :=
        mul_le_mul_left' hcommonMass _
      _ ≤ bounded.data.refinement.shading.mass :=
        bounded.data.massLoss_inv_mul_source_mass_le
  have hfinalSub : PaperIsSubshading bounded.data.refinement.shading
      initialNormalized.croppedRefined := fun index =>
    (bounded.data.refinement.subshading index).trans
      (ambientPropertyThreeCommonHull_subshading
        sticky propP.propertyThree index)
  have hsourceExtremal : WZ2PaperCroppedIsExtremal
      sigma preliminaryStickyLoss initialNormalized.croppedFamily
        initialNormalized.croppedRefined :=
    initialNormalized.final_extremal.mono_loss hnormalizationSticky
  have hproducerExtremal : WZ2PaperCroppedIsExtremal
      sigma producerLoss initialNormalized.croppedFamily
        bounded.data.refinement.shading :=
    transfer_cropped_extremal_to_subshading totalMassLoss htotalPos
      htotalTop hsourceExtremal hfinalSub htotalMass
      bounded.data.refinement.cubical hstickyProducer
      (by simpa [totalMassLoss] using hmassSlack) hdelta hdeltaOne.le
      hproducerLoss
  have hsourceCWA : WZ2PaperConvexWolffBound
      initialNormalized.croppedFamily
      (Kakeya.realRpowENN delta (-preliminaryStickyLoss)) := by
    apply weaken_convex_wolff_bound initialNormalized.cropped_top_level_cwa
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne.le
      (by linarith)
  exact ⟨{
    planiness := bounded
    subshading := hfinalSub
    extremal := hproducerExtremal
    topLevelCWA := by
      apply weaken_convex_wolff_bound hsourceCWA
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne.le
        (by linarith)
    incidence_nonnegative := hetaPositive.le.trans hdenseIncidence
  }⟩

namespace Proposition63M9PreliminaryPlaninessRuntimeData

variable
    {delta sigma initialInputLoss normalizationLoss producerLoss coefficient
      incidence : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {source : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63M9PreliminaryPlaninessRuntimeData
      (producerLoss := producerLoss) (coefficient := coefficient)
      (incidence := incidence) initialNormalized source)

/-- The planiness map with its actual incidence weakened to the single
runtime budget used by the subsequent re-entry. -/
noncomputable def currentMap : PaperWZ1WeakPlaneMapData
    data.planiness.data.refinement.shading incidence where
  planeMap := data.planiness.data.refinement.planeMap.planeMap
  measurable := data.planiness.data.refinement.planeMap.measurable
  unit := data.planiness.data.refinement.planeMap.unit
  incidence := by
    intro index point point_mem
    exact (data.planiness.data.refinement.planeMap.incidence
      index point point_mem).trans data.planiness.incidence_le

/-- Fine-cell constancy is preserved by the incidence weakening. -/
theorem currentMap_cellwise : ∀ first second,
    wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
      data.currentMap.planeMap first = data.currentMap.planeMap second :=
  data.planiness.data.refinement.planeMap_cellwise

/-- The runtime planiness shading is a genuine extremal input to the same
current-shading re-entry machinery used by the rest of M9. -/
theorem prepareReentry
    {densityLoss weightLoss reentryLoss : ℝ}
    (absorption : Proposition63CurrentReentryAbsorptionData
      initialInputLoss normalizationLoss densityLoss producerLoss weightLoss
      reentryLoss
      (proposition63CanonicalNearbyLevelCount normalizationLoss))
    (hdelta : 0 < delta) (hdeltaLe : delta ≤ absorption.delta₀)
    (hnormalizationLoss : 0 < normalizationLoss)
    (hproducerReentry : producerLoss ≤ reentryLoss)
    (hproducerLoss : 0 < producerLoss)
    (reentryNormalizationLoss : ℝ)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (htwoNormalization : 2 * normalizationLoss ≤ reentryLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2) :
    ∃ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) initialNormalized
          data.planiness.data.refinement.shading,
      reentry.normalizationWeight =
          proposition63CanonicalReentryWeight delta weightLoss ∧
        reentry.levelCount =
          proposition63CanonicalNearbyLevelCount normalizationLoss ∧
        reentry.reentryNormalizationLoss = reentryNormalizationLoss := by
  let root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent
      densityLoss :=
    Proposition63RootNormalizationData.ofNormalization initialNormalized
      (absorption.density_absorb hdelta hdeltaLe)
  have ambientTwo := absorption.ambient_two hdelta hdeltaLe
  rcases root.finiteNearbySchedule
      (reentryLoss := reentryLoss) hnormalizationLoss
      ambientTwo htwoNormalization with
    ⟨schedule⟩
  have regularizationAbsorb := absorption.regularization_absorb
    root.normalization rfl schedule rfl rfl hdelta hdeltaLe
  rcases root.currentShadingReentryFromExtremal
      data.planiness.data.refinement.shading schedule ambientTwo
      data.extremal hproducerReentry hproducerLoss reentryNormalizationLoss
      hreentryNormalizationLoss hreentryHalf
      (absorption.canonical_weight_absorb hdelta hdeltaLe)
      (absorption.trace_fixed_absorb hdelta hdeltaLe)
      (absorption.paper_fixed_absorb hdelta hdeltaLe)
      regularizationAbsorb data.subshading
      data.planiness.data.refinement.cubical
      (hdeltaLe.trans absorption.delta₀_le_tiny |>.trans (by norm_num)) with
    ⟨reentry, weight, _weightUpper, levelCount, normalization⟩
  exact ⟨reentry, weight, levelCount, normalization⟩

/-- Prepare the preliminary re-entry and, without changing its selected map,
package the exact root consumed by the subsequent rich finite iteration. -/
theorem prepareRootPlaneMap
    {densityLoss weightLoss reentryLoss gridLoss : ℝ}
    (absorption : Proposition63CurrentReentryAbsorptionData
      initialInputLoss normalizationLoss densityLoss producerLoss weightLoss
      reentryLoss
      (proposition63CanonicalNearbyLevelCount normalizationLoss))
    (hdelta : 0 < delta) (hdeltaLe : delta ≤ absorption.delta₀)
    (hnormalizationLoss : 0 < normalizationLoss)
    (hproducerReentry : producerLoss ≤ reentryLoss)
    (hproducerLoss : 0 < producerLoss)
    (reentryNormalizationLoss : ℝ)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (htwoNormalization : 2 * normalizationLoss ≤ reentryLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2)
    (grid_density_absorb :
      Kakeya.realRpowENN delta gridLoss ≤
        Kakeya.realRpowENN delta reentryLoss / 2) :
    ∃ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) initialNormalized
          data.planiness.data.refinement.shading,
      reentry.normalizationWeight =
          proposition63CanonicalReentryWeight delta weightLoss ∧
        reentry.levelCount =
          proposition63CanonicalNearbyLevelCount normalizationLoss ∧
        reentry.reentryNormalizationLoss = reentryNormalizationLoss ∧
        Nonempty (Proposition63RootPlaneMapData
          (densityLoss := gridLoss) (incidence := incidence)
          reentry (Real.toNNReal coefficient)) := by
  rcases data.prepareReentry absorption hdelta hdeltaLe hnormalizationLoss
      hproducerReentry hproducerLoss reentryNormalizationLoss
      hreentryNormalizationLoss htwoNormalization hreentryHalf with
    ⟨reentry, weight, levelCount, normalization⟩
  exact ⟨reentry, weight, levelCount, normalization,
    proposition63_root_plane_map_of_current_reentry reentry data.currentMap
      (Real.toNNReal coefficient) data.planiness.data.refinement.lipschitz
      data.currentMap_cellwise grid_density_absorb⟩

/-- Re-enter the actual planiness shading and restrict its exact plane map to
the normalization selected by that re-entry. -/
theorem rootPlaneMap
    {reentryLoss gridLoss : ℝ}
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized
        data.planiness.data.refinement.shading)
    (density_absorb :
      Kakeya.realRpowENN delta gridLoss ≤
        Kakeya.realRpowENN delta reentryLoss / 2) :
    Nonempty (Proposition63RootPlaneMapData
      (densityLoss := gridLoss) (incidence := incidence)
      reentry (Real.toNNReal coefficient)) :=
  proposition63_root_plane_map_of_current_reentry reentry data.currentMap
    (Real.toNNReal coefficient) data.planiness.data.refinement.lipschitz
    data.currentMap_cellwise density_absorb

end Proposition63M9PreliminaryPlaninessRuntimeData

end Kakeya.Assouad.PureWZ2

end
