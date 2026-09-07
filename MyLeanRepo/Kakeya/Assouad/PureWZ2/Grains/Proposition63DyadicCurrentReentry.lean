import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RootNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ConstantMultiplicityRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiplicityPreservingVariation

/-!
# Dyadic current-shading re-entry for Proposition 6.3

Before each Phase-1 call in the Lemma 4.12 iteration, select a genuine
dyadic point-multiplicity band of the actual current shading.  Its single
logarithmic loss is absorbed immediately into a fresh cropped-extremality
loss, and the ordinary-trace re-entry is then run on that exact band.

The record keeps the fixed root-family embedding and the unchanged ambient
plane map.  No prefix product of losses from earlier spatial scales enters
this construction.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

/-- One current shading after pre-Phase-1 dyadic selection, immediate
extremality restoration, and ordinary-trace re-entry. -/
structure Proposition63DyadicCurrentReentryData
    {delta sigma initialInputLoss normalizationLoss densityLoss incidence
      currentLoss dyadicLoss weightLoss reentryLoss
      reentryNormalizationLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent
        densityLoss)
    (current : WZ1PaperTubeShading root.normalization.croppedFamily)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence) where
  level : ℕ
  shading : WZ1PaperTubeShading root.normalization.croppedFamily
  subshading : PaperIsSubshading shading current
  root_subshading : PaperIsSubshading shading
    root.normalization.croppedRefined
  cubical : WZ1PaperIsCubicalShading shading
  multiplicity_lower : ∀ point ∈ shading.union,
    (2 ^ level : ENNReal) ≤ (shading.pointMultiplicity point : ENNReal)
  multiplicity_upper : ∀ point ∈ shading.union,
    (shading.pointMultiplicity point : ENNReal) <
      2 * (2 ^ level : ENNReal)
  massLoss : ENNReal
  massLoss_eq : massLoss =
    ((Nat.log 2 root.normalization.croppedFamily.card + 1 : ℕ) : ENNReal)
  massLoss_pos : 0 < massLoss
  massLoss_ne_top : massLoss ≠ ⊤
  mass_retention : massLoss⁻¹ * current.mass ≤ shading.mass
  extremal : WZ2PaperCroppedIsExtremal sigma dyadicLoss
    root.normalization.croppedFamily shading
  dyadic_loss_le_reentry : dyadicLoss ≤ reentryLoss
  planeMap : PaperWZ1WeakPlaneMapData shading incidence
  same_plane_map : planeMap.planeMap = currentMap.planeMap
  reentry : Proposition63CurrentShadingReentryData
    (reentryLoss := reentryLoss) root.normalization shading
  reentry_normalization_weight : reentry.normalizationWeight =
    proposition63CanonicalReentryWeight delta weightLoss
  reentry_weight_upper : reentry.weightUpper =
    (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
      Kakeya.realRpowENN delta 2
  reentry_level_count : reentry.levelCount =
    proposition63CanonicalNearbyLevelCount normalizationLoss
  reentry_normalization_loss :
    reentry.reentryNormalizationLoss = reentryNormalizationLoss

/-- Select the dyadic band of the actual current shading, pay exactly its
one logarithmic loss, restore extremality, and run the next ordinary re-entry
on that restored band. -/
theorem Proposition63RootNormalizationData.currentDyadicShadingReentry
    {sigma inputLoss normalizationLoss densityLoss incidence currentLoss
      dyadicLoss weightLoss reentryLoss reentryNormalizationLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss)
    (current : WZ1PaperTubeShading root.normalization.croppedFamily)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (currentExtremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      root.normalization.croppedFamily current)
    (current_sub_normalized : PaperIsSubshading current
      root.normalization.croppedRefined)
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := root.normalization.croppedFamily)
      (Kakeya.realRpowENN delta (-normalizationLoss))
      (Kakeya.realRpowENN delta (-reentryLoss))
      (proposition63CanonicalNearbyLevelCount normalizationLoss))
    (ambient_two : (2 : ENNReal) <
      Kakeya.realRpowENN delta (-normalizationLoss))
    (currentLoss_le_dyadic : currentLoss ≤ dyadicLoss)
    (dyadicLoss_pos : 0 < dyadicLoss)
    (dyadic_slack :
      ((Nat.log 2 root.normalization.croppedFamily.card + 1 : ℕ) : ENNReal) *
          Kakeya.realRpowENN delta dyadicLoss ≤
        Kakeya.realRpowENN delta currentLoss)
    (dyadicLoss_le_reentry : dyadicLoss ≤ reentryLoss)
    (reentryNormalizationLoss_pos : 0 < reentryNormalizationLoss)
    (reentryLoss_le_half : reentryLoss ≤ reentryNormalizationLoss / 2)
    (canonical_weight_absorb :
      proposition63CanonicalReentryWeight delta weightLoss ≤
        (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta (dyadicLoss + 2))
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
    (delta_small : delta ≤ 1 / 24) :
    Nonempty (Proposition63DyadicCurrentReentryData
      (currentLoss := currentLoss) (dyadicLoss := dyadicLoss)
      (weightLoss := weightLoss) (reentryLoss := reentryLoss)
      (reentryNormalizationLoss := reentryNormalizationLoss)
      root current currentMap) := by
  rcases Kakeya.Assouad.constant_multiplicity_refinement
      currentExtremal.cubical with
    ⟨level, dyadic, hsub, hcubical, hlower, hupper, hmass⟩
  let massLoss : ENNReal :=
    ((Nat.log 2 root.normalization.croppedFamily.card + 1 : ℕ) : ENNReal)
  have hmassLossPos : 0 < massLoss := by
    simp [massLoss]
  have hmassLossTop : massLoss ≠ ⊤ := by
    simp [massLoss]
  have hmassInverse : massLoss⁻¹ * current.mass ≤ dyadic.mass := by
    simpa [massLoss, div_eq_mul_inv, mul_comm] using hmass
  have dyadicExtremal : WZ2PaperCroppedIsExtremal sigma dyadicLoss
      root.normalization.croppedFamily dyadic := by
    apply transfer_cropped_extremal_to_subshading massLoss hmassLossPos
      hmassLossTop currentExtremal hsub hmassInverse hcubical
      currentLoss_le_dyadic
    · simpa only [massLoss] using dyadic_slack
    · exact currentExtremal.delta_pos
    · exact currentExtremal.delta_le_one
    · exact dyadicLoss_pos
  have hsubRoot : PaperIsSubshading dyadic
      root.normalization.croppedRefined :=
    fun index point hpoint => current_sub_normalized index (hsub index hpoint)
  rcases root.currentShadingReentryFromExtremal dyadic schedule ambient_two
      dyadicExtremal dyadicLoss_le_reentry dyadicLoss_pos
      reentryNormalizationLoss reentryNormalizationLoss_pos
      reentryLoss_le_half canonical_weight_absorb trace_fixed_absorb
      paper_fixed_absorb regularization_absorb hsubRoot hcubical delta_small
    with ⟨reentry, hweight, hweightUpper, hlevelCount, hnormalizationLoss⟩
  let dyadicMap := paperWeakPlaneMapRestrict currentMap hsub
  exact ⟨{
    level := level
    shading := dyadic
    subshading := hsub
    root_subshading := hsubRoot
    cubical := hcubical
    multiplicity_lower := hlower
    multiplicity_upper := hupper
    massLoss := massLoss
    massLoss_eq := rfl
    massLoss_pos := hmassLossPos
    massLoss_ne_top := hmassLossTop
    mass_retention := hmassInverse
    extremal := dyadicExtremal
    dyadic_loss_le_reentry := dyadicLoss_le_reentry
    planeMap := dyadicMap
    same_plane_map := rfl
    reentry := reentry
    reentry_normalization_weight := hweight
    reentry_weight_upper := hweightUpper
    reentry_level_count := hlevelCount
    reentry_normalization_loss := hnormalizationLoss
  }⟩

end Kakeya.Assouad.PureWZ2

end
