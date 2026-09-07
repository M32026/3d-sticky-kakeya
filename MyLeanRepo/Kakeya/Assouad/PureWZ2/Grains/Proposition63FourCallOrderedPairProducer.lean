import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RootNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalGrainAmbientPlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ExtremalOneScalePlaneMap

/-!
# Producers used by one four-call ordered-pair step

The first adapter performs a fresh re-entry from the extremality restored by
the preceding iteration step.  The second restricts one fixed ambient plane
map extension to that current shading without choosing a new extension.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- Prepare a fresh re-entry from the actual extremality of the callback's
current shading, exporting both canonical normalization constants needed by
the ordered-pair consumer.  No prefix mass ledger is used. -/
theorem proposition63_four_call_ordered_pair_prepare_fresh_reentry
    {sigma inputLoss normalizationLoss densityLoss currentLoss weightLoss
      reentryLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss)
    (current : WZ1PaperTubeShading root.normalization.croppedFamily)
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := root.normalization.croppedFamily)
      (Kakeya.realRpowENN delta (-normalizationLoss))
      (Kakeya.realRpowENN delta (-reentryLoss))
      (proposition63CanonicalNearbyLevelCount normalizationLoss))
    (ambient_two : (2 : ENNReal) <
      Kakeya.realRpowENN delta (-normalizationLoss))
    (current_sub : PaperIsSubshading current
      root.normalization.croppedRefined)
    (current_cubical : WZ1PaperIsCubicalShading current)
    (current_extremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      root.normalization.croppedFamily current)
    (currentLoss_le_reentry : currentLoss ≤ reentryLoss)
    (currentLoss_pos : 0 < currentLoss)
    (reentryNormalizationLoss : ℝ)
    (reentryNormalizationLoss_pos : 0 < reentryNormalizationLoss)
    (reentryLoss_le_half : reentryLoss ≤ reentryNormalizationLoss / 2)
    (canonical_weight_absorb :
      proposition63CanonicalReentryWeight delta weightLoss ≤
        (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta (currentLoss + 2))
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
    ∃ data : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) root.normalization current,
      data.normalizationWeight =
          proposition63CanonicalReentryWeight delta weightLoss ∧
        data.weightUpper =
          (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2 ∧
        data.levelCount =
          proposition63CanonicalNearbyLevelCount normalizationLoss ∧
        data.reentryNormalizationLoss = reentryNormalizationLoss := by
  rcases root.currentShadingReentryFromExtremal current schedule ambient_two
      current_extremal currentLoss_le_reentry currentLoss_pos
      reentryNormalizationLoss reentryNormalizationLoss_pos
      reentryLoss_le_half canonical_weight_absorb trace_fixed_absorb
      paper_fixed_absorb regularization_absorb current_sub current_cubical
      delta_small with
    ⟨data, hweight, hweightUpper, hlevelCount, hnormalizationLoss⟩
  exact ⟨data, hweight, hweightUpper, hlevelCount, hnormalizationLoss⟩

/-- Restrict a fixed unit ambient extension to a subshading.  Both the raw
ambient function and the clipped ambient function are definitionally the same
functions as in the source extension; only their shading-indexed certificates
are restricted. -/
noncomputable def PureWZ2UnitAmbientWeakPlaneMapExtension.restrict
    {delta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source current : WZ1PaperTubeShading family}
    (sourceMap : PaperWZ1WeakPlaneMapData source incidence)
    (coefficient : NNReal)
    (extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap coefficient)
    (current_sub : PaperIsSubshading current source) :
    PureWZ2UnitAmbientWeakPlaneMapExtension
      (paperWeakPlaneMapRestrict sourceMap current_sub) coefficient where
  raw :=
    { ambient := paperWeakPlaneMapRestrict extension.raw.ambient current_sub
      lipschitz := extension.raw.lipschitz
      agrees := fun point => extension.raw.agrees
        ⟨point, by
          rcases point.property with ⟨index, hpoint⟩
          exact ⟨index, current_sub index hpoint⟩⟩ }
  ambient := paperWeakPlaneMapRestrict extension.ambient current_sub
  ambient_eq := extension.ambient_eq
  lipschitz := extension.lipschitz
  agrees := fun point => extension.agrees
    ⟨point, by
      rcases point.property with ⟨index, hpoint⟩
      exact ⟨index, current_sub index hpoint⟩⟩

/-- Restrict the fixed current-shading ambient extension through both family
and shading restrictions selected by a fresh re-entry.  No new extension is
chosen: the raw and clipped ambient point functions are inherited unchanged. -/
noncomputable def PureWZ2UnitAmbientWeakPlaneMapExtension.restrictToReentry
    {delta sigma inputLoss normalizationLoss reentryLoss incidence : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {current : WZ1PaperTubeShading normalized.croppedFamily}
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (coefficient : NNReal)
    (extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      currentMap coefficient)
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) normalized current) :
    PureWZ2UnitAmbientWeakPlaneMapExtension
      (data.normalizedPlaneMap currentMap) coefficient where
  raw :=
    { ambient := paperWeakPlaneMapRestrict
        (PaperWZ1WeakPlaneMapData.restrictSubfamily
          extension.raw.ambient data.regularized.selected)
        data.denseSubshading
      lipschitz := extension.raw.lipschitz
      agrees := fun point => extension.raw.agrees
        ⟨point, data.normalization_croppedRefined_union_subset_current
          point.property⟩ }
  ambient := paperWeakPlaneMapRestrict
    (PaperWZ1WeakPlaneMapData.restrictSubfamily
      extension.ambient data.regularized.selected)
    data.denseSubshading
  ambient_eq := extension.ambient_eq
  lipschitz := extension.lipschitz
  agrees := fun point => extension.agrees
    ⟨point, data.normalization_croppedRefined_union_subset_current
      point.property⟩

/-- Transport a fixed `1 / 8` axial-window certificate through the exact
ordinary ancestry of a fresh re-entry, in the form required by the M4 runtime. -/
theorem Proposition63CurrentShadingReentryData.rootAxialWindow
    {delta sigma inputLoss normalizationLoss densityLoss reentryLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss}
    {current : WZ1PaperTubeShading root.normalization.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) root.normalization current)
    (rootAxialWindow : ∀ index point,
      point ∈ root.normalization.frame ''
          root.normalization.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (hreentryLoss : 0 < reentryLoss) :
    ∀ index point,
      point ∈ (data.normalization.toPropStickyReentryData
          hreentryLoss data.reentry_normalization_loss_pos).geometry.frame ''
          (data.normalization.toPropStickyReentryData
            hreentryLoss
            data.reentry_normalization_loss_pos).geometry.ordinaryRefined.carrier
              index →
        |point (2 : Fin 3)| ≤ 1 / 8 := by
  intro index point point_mem
  have point_mem' : point ∈ data.normalization.frame ''
      data.normalization.ordinaryRefined.carrier index := by
    simpa [PureWZ2CroppedCriticalNormalizationData.toPropStickyReentryData]
      using point_mem
  dsimp [Proposition63CurrentShadingReentryData.normalization,
    proposition63IdentityFullOrdinaryNormalization] at point_mem'
  exact data.ordinaryAxialWindowOf rootAxialWindow index point <| by
    simpa using point_mem'

end Kakeya.Assouad.PureWZ2
