import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RegularizedAlignedSampledPlaniness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SubfamilyExtensionExtremal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RootPlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ExtremalOneScalePlaneMap

/-!
# M9 sampled coarse plane-map boundary

This is the scale-changing boundary corresponding to the paper's
`existenceOfPlaneMap` step.  A finite weak map on the synchronized fine
fibres has already been rebalanced and sampled on a genuine coarse
subfamily.  Here that sampled shading and map are represented inside the
original coarse family so that its existing ordinary re-entry provenance can
be reused by the subsequent stateful grain-structure iteration.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory

namespace RegularizedAlignedSampledPlaninessData

variable
    {delta rho sigma stickyLoss coefficient : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {requested : WZ2PaperRequestedScale delta}
    {normalizationExponent logExponent : ℕ}
    {sticky : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading requested normalizationExponent logExponent}
    {outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    {nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sticky.data.coarse)
      (Kakeya.realRpowENN requested.1 (-stickyLoss))
      outputConstant levelCount}
    (regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) sticky.data nearbySchedule)
    (hdelta : 0 < delta)
    {K : ℕ}
    (data : RegularizedAlignedSampledPlaninessData
      (coefficient := coefficient)
      (regularizedCompleteFiberCompatibleCover regularized)
      hdelta K)

/-- The sampled coarse shading, represented on the original coarse family by
empty carriers outside the genuinely selected parent set. -/
noncomputable def ambientShading :
    WZ1PaperTubeShading sticky.data.coarse :=
  extendShading regularized.restriction.selectedCoarse
    data.coarseMap.sampled.selected

/-- The sampled coarse plane map on the ambient coarse-family representation.
The point function and its incidence scale are unchanged. -/
noncomputable def ambientPlaneMap :
    PaperWZ1WeakPlaneMapData data.ambientShading requested.1 :=
  PaperWZ1WeakPlaneMapData.extendSubfamily
    regularized.restriction.selectedCoarse data.coarseMap.sampled.planeMap

/-- The ambient representation is a genuine subshading of the coarse shading
carried by the same auxiliary sticky output. -/
theorem sampledShading_sub_sticky : ∀ parent,
    data.coarseMap.sampled.selected.carrier parent ⊆
      sticky.data.croppedCoarseShading.carrier
        (regularized.restriction.selectedCoarse.embedding parent) := by
  intro parent point point_mem
  exact (data.coarseMap.sampled.subshading parent).trans
    ((data.coarseMap.sourceWitness.subshading parent).trans
      (data.coarseMap.residue.coarse_subshading parent)) point_mem

/-- The ambient representation is a genuine subshading of the coarse shading
carried by the same auxiliary sticky output. -/
theorem ambientShading_sub_sticky :
    PaperIsSubshading data.ambientShading
      sticky.data.croppedCoarseShading := by
  apply extendShading_subshading
  exact data.sampledShading_sub_sticky

/-- The sampled map remains one-Lipschitz after its empty-carrier extension. -/
theorem ambientPlaneMap_lipschitz :
    LipschitzWith 1
      (fun point : {point : Point3 // point ∈ data.ambientShading.union} =>
        data.ambientPlaneMap.planeMap point) :=
  paperWeakPlaneMap_extendSubfamily_lipschitz
    regularized.restriction.selectedCoarse data.coarseMap.sampled.planeMap
      data.coarseMap.sampled.lipschitz

/-- The exact coarse-cell constancy from source-witness sampling survives the
ambient representation. -/
theorem ambientPlaneMap_cellwise : ∀ first second,
    wz1PaperGridIndex requested.1 first =
        wz1PaperGridIndex requested.1 second →
      data.ambientPlaneMap.planeMap first =
        data.ambientPlaneMap.planeMap second :=
  paperWeakPlaneMap_extendSubfamily_cellwise
    regularized.restriction.selectedCoarse data.coarseMap.sampled.planeMap
      data.coarseMap.sampled.planeMap_cellwise

/-- Restore extremality of the sampled shading in the ambient coarse family.
The indexed-cardinality selection cost is converted to paper body mass using
the explicit cropped-carrier geometry constant. -/
theorem ambientShading_extremal
    {selectedLoss targetLoss : ℝ}
    (selectedExtremal : WZ2PaperCroppedIsExtremal sigma selectedLoss
      regularized.restriction.selectedCoarse.family
      data.coarseMap.sampled.selected)
    (hstickyTarget : stickyLoss ≤ targetLoss)
    (hnormalizationWeightZero : normalizationWeight ≠ 0)
    (hnormalizationWeightTop : normalizationWeight ≠ ⊤)
    (habsorb :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (regularized.regularized.regularizationLoss * weightUpper) *
            Kakeya.realRpowENN requested.1 targetLoss ≤
        normalizationWeight *
          Kakeya.realRpowENN requested.1 selectedLoss)
    (htargetLoss : 0 < targetLoss)
    (hscaleSmall : requested.1 ≤ 1 / 24) :
    WZ2PaperCroppedIsExtremal sigma targetLoss sticky.data.coarse
      data.ambientShading := by
  have hcardinality :
      normalizationWeight * sticky.data.coarse.enncard ≤
        (regularized.regularized.regularizationLoss * weightUpper) *
          regularized.restriction.selectedCoarse.family.enncard := by
    simpa only [regularized.restriction_coarse_eq] using
      regularized.regularized.cardinality_retention
  exact subfamily_extension_cropped_extremal_of_cardinality
    regularized.restriction.selectedCoarse sticky.data.coarse_extremal
      selectedExtremal data.sampledShading_sub_sticky hstickyTarget
      normalizationWeight
      (regularized.regularized.regularizationLoss * weightUpper)
      hnormalizationWeightZero hnormalizationWeightTop hcardinality habsorb
      htargetLoss hscaleSmall sticky.data.cover.coarse_line_class

/-- Re-enter the sampled coarse shading from an explicitly retargeted copy of
the sticky coarse re-entry.  The plane map still comes from the same sampled
coarse family; only the loss indices of the ordinary provenance may have been
weakened before this call. -/
theorem prepareGrainStructureRootOfAmbientReentryWithAxial
    {ambientSourceLoss ambientNormalizationLoss selectedLoss currentLoss
      densityLoss weightLoss reentryLoss reentryNormalizationLoss gridLoss : ℝ}
    (ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sticky.data.croppedCoarseShading normalizationExponent
      ambientSourceLoss ambientNormalizationLoss)
    (selectedExtremal : WZ2PaperCroppedIsExtremal sigma selectedLoss
      regularized.restriction.selectedCoarse.family
      data.coarseMap.sampled.selected)
    (hstickyCurrent : stickyLoss ≤ currentLoss)
    (hnormalizationWeightZero : normalizationWeight ≠ 0)
    (hnormalizationWeightTop : normalizationWeight ≠ ⊤)
    (hextensionAbsorb :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (regularized.regularized.regularizationLoss * weightUpper) *
            Kakeya.realRpowENN requested.1 currentLoss ≤
        normalizationWeight *
          Kakeya.realRpowENN requested.1 selectedLoss)
    (absorption : Proposition63CurrentReentryAbsorptionData
      ambientSourceLoss ambientNormalizationLoss densityLoss currentLoss
      weightLoss reentryLoss
      (proposition63CanonicalNearbyLevelCount ambientNormalizationLoss))
    (hscaleLe : requested.1 ≤ absorption.delta₀)
    (hcurrentReentry : currentLoss ≤ reentryLoss)
    (hcurrentLoss : 0 < currentLoss)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (htwoNormalization : 2 * ambientNormalizationLoss ≤ reentryLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2)
    (hgridDensity :
      Kakeya.realRpowENN requested.1 gridLoss ≤
        Kakeya.realRpowENN requested.1 reentryLoss / 2)
    (ambientAxialEighth : ∀ tube point,
      point ∈ ambientReentry.geometry.frame ''
          ambientReentry.geometry.ordinaryRefined.carrier tube →
        |point (2 : Fin 3)| ≤ 1 / 8) :
    ∃ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss)
        ambientReentry.toNormalizationData data.ambientShading,
      reentry.normalizationWeight =
          proposition63CanonicalReentryWeight requested.1 weightLoss ∧
        reentry.levelCount = proposition63CanonicalNearbyLevelCount
          ambientNormalizationLoss ∧
        reentry.reentryNormalizationLoss = reentryNormalizationLoss ∧
        ∃ rootMap : Proposition63RootPlaneMapData
            (densityLoss := gridLoss) (incidence := requested.1) reentry 1,
          ∀ tube point,
            point ∈ rootMap.root.normalization.frame ''
                rootMap.root.normalization.ordinaryRefined.carrier tube →
              |point (2 : Fin 3)| ≤ 1 / 8 := by
  have hscalePos : 0 < requested.1 := sticky.data.coarse_extremal.delta_pos
  have hscaleSmall : requested.1 ≤ 1 / 24 :=
    hscaleLe.trans absorption.delta₀_le_tiny |>.trans (by norm_num)
  have currentExtremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      sticky.data.coarse data.ambientShading :=
    ambientShading_extremal regularized hdelta data selectedExtremal
      hstickyCurrent hnormalizationWeightZero hnormalizationWeightTop
      hextensionAbsorb hcurrentLoss hscaleSmall
  let root : Proposition63RootNormalizationData
      (outputLoss := ambientNormalizationLoss) ambientReentry.ordinarySource
      normalizationExponent densityLoss :=
    Proposition63RootNormalizationData.ofPropStickyReentry ambientReentry
      (absorption.density_absorb hscalePos hscaleLe)
  have ambientTwo := absorption.ambient_two hscalePos hscaleLe
  rcases root.finiteNearbySchedule
      ambientReentry.normalizationLoss_pos ambientTwo htwoNormalization with
    ⟨schedule⟩
  have regularizationAbsorb := absorption.regularization_absorb
    root.normalization rfl schedule rfl rfl hscalePos hscaleLe
  have currentSub : PaperIsSubshading data.ambientShading
      root.normalization.croppedRefined := by
    simpa only [root, Proposition63RootNormalizationData.ofPropStickyReentry,
      Proposition63RootNormalizationData.ofNormalization,
      PureWZ2PropStickyReentryData.toNormalizationData] using
        data.ambientShading_sub_sticky
  rcases root.currentShadingReentryFromExtremal data.ambientShading schedule
      ambientTwo currentExtremal hcurrentReentry hcurrentLoss
      reentryNormalizationLoss hreentryNormalizationLoss hreentryHalf
      (absorption.canonical_weight_absorb hscalePos hscaleLe)
      (absorption.trace_fixed_absorb hscalePos hscaleLe)
      (absorption.paper_fixed_absorb hscalePos hscaleLe)
      regularizationAbsorb currentSub
      (extendShading_cubical regularized.restriction.selectedCoarse
        data.coarseMap.sampled.cubical) hscaleSmall with
    ⟨reentry, weight, _weightUpper, levelCount, normalization⟩
  let rootMap := Proposition63RootPlaneMapData.ofCurrentReentry reentry
    data.ambientPlaneMap 1 data.ambientPlaneMap_lipschitz
    data.ambientPlaneMap_cellwise hgridDensity
  refine ⟨reentry, weight, levelCount, normalization, rootMap, ?_⟩
  exact Proposition63RootPlaneMapData.ofCurrentReentry_axialWindow reentry
    data.ambientPlaneMap 1 data.ambientPlaneMap_lipschitz
    data.ambientPlaneMap_cellwise hgridDensity
    (by simpa only [root,
      Proposition63RootNormalizationData.ofPropStickyReentry,
      Proposition63RootNormalizationData.ofNormalization,
      PureWZ2PropStickyReentryData.toNormalizationData] using
        ambientAxialEighth)

/-- Re-enter the sampled coarse shading through the exact ordinary provenance
of the auxiliary sticky output, then attach the same sampled plane map to the
resulting grain-structure root.  Every loss and cutoff remains an explicit
pre-runtime receipt. -/
theorem prepareGrainStructureRoot
    {selectedLoss currentLoss densityLoss weightLoss reentryLoss
      reentryNormalizationLoss gridLoss : ℝ}
    (selectedExtremal : WZ2PaperCroppedIsExtremal sigma selectedLoss
      regularized.restriction.selectedCoarse.family
      data.coarseMap.sampled.selected)
    (hstickyCurrent : stickyLoss ≤ currentLoss)
    (hnormalizationWeightZero : normalizationWeight ≠ 0)
    (hnormalizationWeightTop : normalizationWeight ≠ ⊤)
    (hextensionAbsorb :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (regularized.regularized.regularizationLoss * weightUpper) *
            Kakeya.realRpowENN requested.1 currentLoss ≤
        normalizationWeight *
          Kakeya.realRpowENN requested.1 selectedLoss)
    (absorption : Proposition63CurrentReentryAbsorptionData
      sticky.coarseSourceLoss sticky.coarseNormalizationLoss densityLoss
      currentLoss weightLoss reentryLoss
      (proposition63CanonicalNearbyLevelCount
        sticky.coarseNormalizationLoss))
    (hscaleLe : requested.1 ≤ absorption.delta₀)
    (hcurrentReentry : currentLoss ≤ reentryLoss)
    (hcurrentLoss : 0 < currentLoss)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (htwoNormalization :
      2 * sticky.coarseNormalizationLoss ≤ reentryLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2)
    (hgridDensity :
      Kakeya.realRpowENN requested.1 gridLoss ≤
        Kakeya.realRpowENN requested.1 reentryLoss / 2) :
    ∃ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss)
        sticky.coarseReentry.toNormalizationData data.ambientShading,
      reentry.normalizationWeight =
          proposition63CanonicalReentryWeight requested.1 weightLoss ∧
        reentry.levelCount = proposition63CanonicalNearbyLevelCount
          sticky.coarseNormalizationLoss ∧
        reentry.reentryNormalizationLoss = reentryNormalizationLoss ∧
        Nonempty (Proposition63RootPlaneMapData
          (densityLoss := gridLoss) (incidence := requested.1) reentry 1) := by
  have hscalePos : 0 < requested.1 := sticky.data.coarse_extremal.delta_pos
  have hscaleSmall : requested.1 ≤ 1 / 24 :=
    hscaleLe.trans absorption.delta₀_le_tiny |>.trans (by norm_num)
  have currentExtremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      sticky.data.coarse data.ambientShading :=
    ambientShading_extremal regularized hdelta data selectedExtremal
      hstickyCurrent
      hnormalizationWeightZero hnormalizationWeightTop hextensionAbsorb
      hcurrentLoss hscaleSmall
  let root : Proposition63RootNormalizationData
      (outputLoss := sticky.coarseNormalizationLoss)
      sticky.coarseReentry.ordinarySource normalizationExponent densityLoss :=
    Proposition63RootNormalizationData.ofPropStickyReentry
      sticky.coarseReentry
      (absorption.density_absorb hscalePos hscaleLe)
  have ambientTwo := absorption.ambient_two hscalePos hscaleLe
  rcases root.finiteNearbySchedule
      sticky.coarseNormalizationLoss_pos ambientTwo htwoNormalization with
    ⟨schedule⟩
  have regularizationAbsorb := absorption.regularization_absorb
    root.normalization rfl schedule rfl rfl hscalePos hscaleLe
  have currentSub : PaperIsSubshading data.ambientShading
      root.normalization.croppedRefined := by
    simpa only [root, Proposition63RootNormalizationData.ofPropStickyReentry,
      Proposition63RootNormalizationData.ofNormalization,
      PureWZ2PropStickyReentryData.toNormalizationData] using
        data.ambientShading_sub_sticky
  rcases root.currentShadingReentryFromExtremal data.ambientShading schedule
      ambientTwo currentExtremal hcurrentReentry hcurrentLoss
      reentryNormalizationLoss hreentryNormalizationLoss hreentryHalf
      (absorption.canonical_weight_absorb hscalePos hscaleLe)
      (absorption.trace_fixed_absorb hscalePos hscaleLe)
      (absorption.paper_fixed_absorb hscalePos hscaleLe)
      regularizationAbsorb currentSub
      (extendShading_cubical regularized.restriction.selectedCoarse
        data.coarseMap.sampled.cubical) hscaleSmall with
    ⟨reentry, weight, _weightUpper, levelCount, normalization⟩
  refine ⟨reentry, weight, levelCount, normalization, ?_⟩
  exact ⟨Proposition63RootPlaneMapData.ofCurrentReentry reentry
    data.ambientPlaneMap 1 data.ambientPlaneMap_lipschitz
    data.ambientPlaneMap_cellwise hgridDensity⟩

/-- Axial-provenance specialization of `prepareGrainStructureRoot`.  The
returned certificate is indexed by the exact canonical root-map witness, so a
later M7/M8 caller never has to identify an opaque existential root with the
current-reentry normalization. -/
theorem prepareGrainStructureRootWithAxial
    {selectedLoss currentLoss densityLoss weightLoss reentryLoss
      reentryNormalizationLoss gridLoss : ℝ}
    (selectedExtremal : WZ2PaperCroppedIsExtremal sigma selectedLoss
      regularized.restriction.selectedCoarse.family
      data.coarseMap.sampled.selected)
    (hstickyCurrent : stickyLoss ≤ currentLoss)
    (hnormalizationWeightZero : normalizationWeight ≠ 0)
    (hnormalizationWeightTop : normalizationWeight ≠ ⊤)
    (hextensionAbsorb :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (regularized.regularized.regularizationLoss * weightUpper) *
            Kakeya.realRpowENN requested.1 currentLoss ≤
        normalizationWeight *
          Kakeya.realRpowENN requested.1 selectedLoss)
    (absorption : Proposition63CurrentReentryAbsorptionData
      sticky.coarseSourceLoss sticky.coarseNormalizationLoss densityLoss
      currentLoss weightLoss reentryLoss
      (proposition63CanonicalNearbyLevelCount
        sticky.coarseNormalizationLoss))
    (hscaleLe : requested.1 ≤ absorption.delta₀)
    (hcurrentReentry : currentLoss ≤ reentryLoss)
    (hcurrentLoss : 0 < currentLoss)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (htwoNormalization :
      2 * sticky.coarseNormalizationLoss ≤ reentryLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2)
    (hgridDensity :
      Kakeya.realRpowENN requested.1 gridLoss ≤
        Kakeya.realRpowENN requested.1 reentryLoss / 2)
    (coarseAxialEighth : ∀ tube point,
      point ∈ sticky.coarseReentry.geometry.frame ''
          sticky.coarseReentry.geometry.ordinaryRefined.carrier tube →
        |point (2 : Fin 3)| ≤ 1 / 8) :
    ∃ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss)
        sticky.coarseReentry.toNormalizationData data.ambientShading,
      reentry.normalizationWeight =
          proposition63CanonicalReentryWeight requested.1 weightLoss ∧
        reentry.levelCount = proposition63CanonicalNearbyLevelCount
          sticky.coarseNormalizationLoss ∧
        reentry.reentryNormalizationLoss = reentryNormalizationLoss ∧
        ∃ rootMap : Proposition63RootPlaneMapData
            (densityLoss := gridLoss) (incidence := requested.1) reentry 1,
          ∀ tube point,
            point ∈ rootMap.root.normalization.frame ''
                rootMap.root.normalization.ordinaryRefined.carrier tube →
              |point (2 : Fin 3)| ≤ 1 / 8 := by
  rcases data.prepareGrainStructureRoot regularized hdelta selectedExtremal
      hstickyCurrent hnormalizationWeightZero hnormalizationWeightTop
      hextensionAbsorb absorption hscaleLe hcurrentReentry hcurrentLoss
      hreentryNormalizationLoss htwoNormalization
      hreentryHalf hgridDensity with
    ⟨reentry, weight, level, normalization, _rootMap⟩
  let rootMap := Proposition63RootPlaneMapData.ofCurrentReentry reentry
    data.ambientPlaneMap 1 data.ambientPlaneMap_lipschitz
    data.ambientPlaneMap_cellwise hgridDensity
  refine ⟨reentry, weight, level, normalization, rootMap, ?_⟩
  exact Proposition63RootPlaneMapData.ofCurrentReentry_axialWindow reentry
    data.ambientPlaneMap 1 data.ambientPlaneMap_lipschitz
    data.ambientPlaneMap_cellwise hgridDensity coarseAxialEighth

end RegularizedAlignedSampledPlaninessData

end Kakeya.Assouad.PureWZ2

end
