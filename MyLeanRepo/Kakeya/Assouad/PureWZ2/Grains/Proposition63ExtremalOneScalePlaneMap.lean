import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RobustTransversality
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63CrossDegreeAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureAmplifiedOneScaleVariation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63TwoRichCloseCount
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CanonicalMassBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RootNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63SequentialReentry
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLinePackingCardinality
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PreparedScaleRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureHitParentRestriction

/-!
# Extremality-restored one-scale plane-map step for WZ2 Proposition 6.3

This is the current pure/cropped replacement for the retired WZ1 one-scale
interface.  A robust rich Proposition 6.2 output supplies exact packet
multiplicity and fiber caps.  A separate literal nearby-CWA cover supplies the
target spatial scale and is restricted to the selected terminal fine family.
The plane map is always a restriction of the caller's fixed ambient function.

The geometric theorem below records one scale only.  Its mass inequality is
consumed immediately by the extremality-restoration wrapper; it is never
multiplied across the finite Lemma 4.7 iteration.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

namespace Proposition63RichTerminalStickyData

variable
    {delta sigma outputLoss sourceLoss normalizationLoss incidence : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)

/-- Restrict the caller's fixed map first to the Node 3 selected family and
then to its exact terminal fine shading. -/
noncomputable def terminalPlaneMap
    (planeMap : PaperWZ1WeakPlaneMapData croppedShading incidence) :
    PaperWZ1WeakPlaneMapData rich.data.refined incidence :=
  paperWeakPlaneMapRestrict
    (PaperWZ1WeakPlaneMapData.restrictSubfamily
      planeMap rich.data.selected)
    rich.data.subshading

@[simp] theorem terminalPlaneMap_apply
    (planeMap : PaperWZ1WeakPlaneMapData croppedShading incidence)
    (point : Point3) :
    (rich.terminalPlaneMap planeMap).planeMap point = planeMap.planeMap point :=
  rfl

/-- Regard the same total point function as a weak plane map on the terminal
zero-extension.  No function is changed: unit norm follows from the union
identity, while incidence is vacuous off the selected subfamily. -/
noncomputable def ambientTerminalPlaneMap
    (planeMap : PaperWZ1WeakPlaneMapData rich.data.refined incidence) :
    PaperWZ1WeakPlaneMapData
      (extendShading rich.data.selected rich.data.refined) incidence where
  planeMap := planeMap.planeMap
  measurable := planeMap.measurable
  unit := by
    intro point hpoint
    exact planeMap.unit point <| by
      simpa only [extendShading_union rich.data.selected rich.data.refined]
        using hpoint
  incidence := by
    intro index point hpoint
    by_cases himage : ∃ selected, rich.data.selected.embedding selected = index
    · rcases himage with ⟨selected, rfl⟩
      rw [extendShading_carrier_mem] at hpoint
      simpa only [rich.data.selected.tube_eq] using
        planeMap.incidence selected point hpoint
    · rw [extendShading_carrier_empty himage] at hpoint
      exact False.elim hpoint

@[simp] theorem ambientTerminalPlaneMap_apply
    (planeMap : PaperWZ1WeakPlaneMapData rich.data.refined incidence)
    (point : Point3) :
    (rich.ambientTerminalPlaneMap planeMap).planeMap point =
      planeMap.planeMap point := rfl

/-- One target-scale variation step on the exact terminal fine family.

The target cover is the literal pure nearby-CWA cover of the ambient current
family, restricted to the parents hit by the rich terminal fine subfamily.
The robust threshold is the independent Node 3 scale `rho`; thus no target
cover is asked to supply a second multiplicity certificate. -/
theorem oneScaleVariation
    (planeMap : PaperWZ1WeakPlaneMapData croppedShading incidence)
    (hplaneCell : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        planeMap.planeMap first = planeMap.planeMap second)
    {requested : WZ2PaperRequestedScale delta}
    {C densityPower : ENNReal}
    {spatialScale variationScale : ℝ}
    (nearby : WZ2PaperPureNearbyScaleCoverData croppedFamily requested C)
    (houtputLoss : 0 ≤ outputLoss)
    (hrhoSmall : rho.1 ≤ 1 / 10000)
    (hdegreeAbsorb :
      (12 * (2 * stickyCoarseCloseCount)) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN rho.1 (-sigma + 4 * outputLoss))
    (hdensityScalar :
      densityPower *
          ((rich.terminal.regularity : ENNReal) *
            Kakeya.realRpowENN delta (sigma - normalizationLoss)) ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta (normalizationLoss + 2))
    (hincidence : 0 ≤ incidence)
    (hparentSmall : nearby.rho < 1 / 8)
    (hparentRobust : 8 * nearby.rho < rho.1)
    (hspatial : 0 < spatialScale)
    (hvariation : 0 < variationScale)
    (K : ℕ) (hK : 0 < K)
    (hspatialAligned : spatialScale = (K : ℝ) * delta) :
    ∃ selected : WZ1PaperTubeShading rich.data.selected.family,
      PaperIsSubshading selected rich.data.refined ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ point ∈ selected.union, ∀ other ∈ selected.union,
        dist point other ≤ spatialScale →
          dist (planeMap.planeMap point) (planeMap.planeMap other) ≤
            variationScale) ∧
      (∀ point ∈ selected.union,
        selected.pointMultiplicity point =
          rich.data.refined.pointMultiplicity point) ∧
      densityPower ^ 2 * rich.data.refined.mass ≤
        27 * (2 *
          (wz1OrientationCapCount
            (10 * (incidence + 4 * nearby.rho) /
              (rho.1 - 8 * nearby.rho)) variationScale : ENNReal)) *
          selected.mass := by
  let selectedPure : WZ2PaperPureTubeSubfamily croppedFamily :=
    WZ2PaperPureTubeSubfamily.ofTubeSubfamily rich.data.selected
  let targetCover :=
    nearby.scaleData.cover.restrictToHitParents selectedPure
  have hterminalCell : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        (rich.terminalPlaneMap planeMap).planeMap first =
          (rich.terminalPlaneMap planeMap).planeMap second := by
    intro first second sameCell
    exact hplaneCell first second sameCell
  have hdensity : densityPower * rich.data.selected.family.enncard ≤
      (rich.terminal.fineDegreeFloor * rich.terminal.muFine : ℕ) :=
    rich.fineMultiplicity_density_of_scalar densityPower
      (rho.2.1.trans (hrhoSmall.trans (by norm_num)))
      hdensityScalar
  exact paper_pure_amplified_one_scale_nearby_variation_cancel_cardinality
    targetCover rich.data.selected_nonempty rich.data.cover.fine_line_class
    rich.terminal.fine_cubical (rich.terminalPlaneMap planeMap)
    hterminalCell
    (rich.terminal.fineDegreeFloor * rich.terminal.muFine)
    (fun point point_mem =>
      rich.terminal.fine_pointMultiplicity_floor_on_union point_mem)
    (rich.robust_close_count_absorbed_of_cwa houtputLoss hrhoSmall
      hdegreeAbsorb)
    densityPower hdensity hincidence nearby.scaleData.rho_pos hparentSmall
    hspatial hvariation hparentRobust K hK hspatialAligned

end Proposition63RichTerminalStickyData

/-- The output of one Lemma 4.7 scale after it has already been returned to
the current ambient family and made extremal at the requested output loss. -/
structure Proposition63ExtremalOneScalePlaneMapData
    {delta sigma initialInputLoss normalizationLoss incidence : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    (current : WZ1PaperTubeShading initialNormalized.croppedFamily)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (outputLoss spatialScale variationScale : ℝ) where
  shading : WZ1PaperTubeShading initialNormalized.croppedFamily
  subshading : PaperIsSubshading shading current
  cubical : WZ1PaperIsCubicalShading shading
  planeMap : PaperWZ1WeakPlaneMapData shading incidence
  same_plane_map : planeMap.planeMap = currentMap.planeMap
  variation : ∀ point ∈ shading.union, ∀ other ∈ shading.union,
    dist point other ≤ spatialScale →
      dist (planeMap.planeMap point) (planeMap.planeMap other) ≤
        variationScale
  massLoss : ENNReal
  massLoss_pos : 0 < massLoss
  massLoss_ne_top : massLoss ≠ ⊤
  mass_retention : massLoss⁻¹ * current.mass ≤ shading.mass
  extremal : WZ2PaperCroppedIsExtremal
    sigma outputLoss initialNormalized.croppedFamily shading

namespace Proposition63CurrentShadingReentryData

variable
    {delta sigma initialInputLoss normalizationLoss reentryLoss incidence : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)

/-- Restrict the fixed current plane map through the exact family and shading
selected by ordinary re-entry. -/
noncomputable def normalizedPlaneMap
    (currentMap : PaperWZ1WeakPlaneMapData current incidence) :
    PaperWZ1WeakPlaneMapData data.normalization.croppedRefined incidence :=
  paperWeakPlaneMapRestrict
    (PaperWZ1WeakPlaneMapData.restrictSubfamily
      currentMap data.regularized.selected)
    data.denseSubshading

@[simp] theorem normalizedPlaneMap_apply
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (point : Point3) :
    (data.normalizedPlaneMap currentMap).planeMap point =
      currentMap.planeMap point := rfl

end Proposition63CurrentShadingReentryData

/-- Lift an extremal shading from a current re-entry's selected normalization
family back to the caller family using the regularizer's cardinality ledger.
The common tube-volume factor is cancelled before the density estimate, so
the canonical weight's geometric `delta ^ 2` factor is not charged as a raw
mass loss. -/
theorem Proposition63CurrentShadingReentryData.extendCandidate_extremal
    {delta sigma initialInputLoss normalizationLoss reentryLoss currentLoss
      innerLoss outputLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (currentExtremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      initialNormalized.croppedFamily current)
    {candidate : WZ1PaperTubeShading data.normalization.croppedFamily}
    (candidateSub : PaperIsSubshading candidate
      data.normalization.croppedRefined)
    (candidateCubical : WZ1PaperIsCubicalShading candidate)
    (candidateExtremal : WZ2PaperCroppedIsExtremal sigma innerLoss
      data.normalization.croppedFamily candidate)
    (hcurrentOutput : currentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hdensityLift :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (data.regularized.regularizationLoss * data.weightUpper) *
          Kakeya.realRpowENN delta outputLoss ≤
        data.normalizationWeight *
          Kakeya.realRpowENN delta innerLoss) :
    WZ2PaperCroppedIsExtremal sigma outputLoss
      initialNormalized.croppedFamily (data.extendCandidate candidate) := by
  let ambient := data.extendCandidate candidate
  have ambientSub : PaperIsSubshading ambient current :=
    data.extendCandidate_subshading candidateSub
  have ambientCubical : WZ1PaperIsCubicalShading ambient :=
    extendShading_cubical data.regularized.selected candidateCubical
  have ambientMass : ambient.mass = candidate.mass :=
    data.extendCandidate_mass candidate
  have cardinality :
      data.normalizationWeight *
          initialNormalized.croppedFamily.enncard ≤
        (data.regularized.regularizationLoss * data.weightUpper) *
          data.normalization.croppedFamily.enncard := by
    simpa only [data.normalization_croppedFamily] using
      data.regularized.cardinality_retention
  have ambientBodyUpper :
      (wz1PaperBodyFamily initialNormalized.croppedFamily).mass ≤
        ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta 2 *
          initialNormalized.croppedFamily.enncard :=
    by
      let fullShading : WZ1PaperTubeShading
          initialNormalized.croppedFamily :=
        { carrier := fun index => wz1PaperTubeCarrier
            (initialNormalized.croppedFamily.tube index)
          measurable_carrier := fun index =>
            wz1PaperTubeCarrier_measurable
              (initialNormalized.croppedFamily.tube index)
          subset_body := fun _ => Set.Subset.rfl }
      have upper := wz2_paper_shading_mass_upper
        currentExtremal.delta_pos data.delta_small data.line_class fullShading
      change (wz1PaperBodyFamily initialNormalized.croppedFamily).mass ≤
        ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta 2 *
          initialNormalized.croppedFamily.enncard at upper
      exact upper
  have selectedBodyLower :
      Kakeya.realRpowENN delta 2 *
          data.normalization.croppedFamily.enncard ≤
        (wz1PaperBodyFamily data.normalization.croppedFamily).mass :=
    paperBodyFamily_mass_lower_rpow_two currentExtremal.delta_pos
      (data.delta_small.trans (by norm_num)) data.normalization.line_class
  have scaledDensity :
      data.normalizationWeight *
          (Kakeya.realRpowENN delta outputLoss *
            (wz1PaperBodyFamily initialNormalized.croppedFamily).mass) ≤
        data.normalizationWeight * candidate.mass := by
    calc
      data.normalizationWeight *
            (Kakeya.realRpowENN delta outputLoss *
              (wz1PaperBodyFamily initialNormalized.croppedFamily).mass) ≤
          data.normalizationWeight *
            (Kakeya.realRpowENN delta outputLoss *
              (((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
                Kakeya.realRpowENN delta 2 *
                initialNormalized.croppedFamily.enncard)) := by gcongr
      _ = ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta outputLoss *
          (data.normalizationWeight *
            initialNormalized.croppedFamily.enncard) *
          Kakeya.realRpowENN delta 2 := by ring
      _ ≤ ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta outputLoss *
            ((data.regularized.regularizationLoss * data.weightUpper) *
              data.normalization.croppedFamily.enncard) *
            Kakeya.realRpowENN delta 2 := by gcongr
      _ = (((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
            (data.regularized.regularizationLoss * data.weightUpper) *
            Kakeya.realRpowENN delta outputLoss) *
          (Kakeya.realRpowENN delta 2 *
            data.normalization.croppedFamily.enncard) := by ring
      _ ≤ (data.normalizationWeight *
            Kakeya.realRpowENN delta innerLoss) *
          (wz1PaperBodyFamily data.normalization.croppedFamily).mass := by
        exact mul_le_mul hdensityLift selectedBodyLower bot_le bot_le
      _ = data.normalizationWeight *
          (Kakeya.realRpowENN delta innerLoss *
            (wz1PaperBodyFamily data.normalization.croppedFamily).mass) := by
        ring
      _ ≤ data.normalizationWeight * candidate.mass := by
        gcongr
        exact candidateExtremal.dense
  have ambientDense : ambient.IsLambdaDense
      (Kakeya.realRpowENN delta outputLoss) := by
    rw [Kakeya.Streamlined.Shading.IsLambdaDense, ambientMass]
    exact (ENNReal.mul_le_mul_iff_right
      data.normalization_weight_ne_zero
      data.normalization_weight_ne_top).mp <| by
        simpa [mul_comm, mul_left_comm, mul_assoc] using scaledDensity
  have weakened := currentExtremal.mono_loss hcurrentOutput
  exact {
    delta_pos := weakened.delta_pos
    delta_le_one := weakened.delta_le_one
    nonempty := weakened.nonempty
    cwa_nearby_scales := weakened.cwa_nearby_scales
    cubical := ambientCubical
    dense := ambientDense
    volume_upper := by
      apply (measure_mono ?_).trans weakened.volume_upper
      rintro point ⟨index, pointMem⟩
      exact ⟨index, ambientSub index pointMem⟩
  }

/-- Lift an extremality-restored one-scale output from the exact family
selected by a current-shading re-entry back to the caller's ambient family.
Only the mass lost inside this single re-entry is paid here; no loss from an
earlier spatial scale appears in the statement. -/
theorem Proposition63CurrentShadingReentryData.liftExtremalOneScalePlaneMap
    {delta sigma initialInputLoss normalizationLoss reentryLoss currentLoss
      innerOutputLoss outputLoss incidence spatialScale variationScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (currentExtremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      initialNormalized.croppedFamily current)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    {normalizedCurrent : WZ1PaperTubeShading
      data.normalization.croppedFamily}
    (normalizedCurrentSub : PaperIsSubshading normalizedCurrent
      data.normalization.croppedRefined)
    (normalizedCurrentMap : PaperWZ1WeakPlaneMapData normalizedCurrent incidence)
    (normalizedMap_eq : normalizedCurrentMap.planeMap = currentMap.planeMap)
    (inner : Proposition63ExtremalOneScalePlaneMapData
      (initialNormalized := data.normalization) normalizedCurrent
      normalizedCurrentMap innerOutputLoss spatialScale variationScale)
    (preFactor : ENNReal)
    (preFactor_pos : 0 < preFactor)
    (preFactor_ne_top : preFactor ≠ ⊤)
    (preRetention :
      preFactor * data.normalization.croppedRefined.mass ≤
        normalizedCurrent.mass)
    (hcurrentOutput : currentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hdensityLift :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (data.regularized.regularizationLoss * data.weightUpper) *
          Kakeya.realRpowENN delta outputLoss ≤
        data.normalizationWeight *
          Kakeya.realRpowENN delta innerOutputLoss) :
    Nonempty (Proposition63ExtremalOneScalePlaneMapData
      current currentMap outputLoss spatialScale variationScale) := by
  have innerSubNormalized : PaperIsSubshading inner.shading
      data.normalization.croppedRefined := by
    intro index point pointMem
    exact normalizedCurrentSub index (inner.subshading index pointMem)
  let ambient := data.extendCandidate inner.shading
  have ambientSub : PaperIsSubshading ambient current :=
    data.extendCandidate_subshading innerSubNormalized
  have ambientCubical : WZ1PaperIsCubicalShading ambient :=
    extendShading_cubical data.regularized.selected inner.cubical
  let ambientMap := paperWeakPlaneMapRestrict currentMap ambientSub
  let leftFactor : ENNReal :=
    ((73 / 100 : ENNReal) * data.normalizationWeight) *
      (preFactor * inner.massLoss⁻¹)
  let rightFactor : ENNReal := data.regularized.regularizationLoss
  let massLoss := proposition63Lemma43MassLoss leftFactor rightFactor
  have innerInvPos : 0 < inner.massLoss⁻¹ :=
    ENNReal.inv_pos.mpr inner.massLoss_ne_top
  have innerInvTop : inner.massLoss⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr inner.massLoss_pos.ne'
  have retentionConstantPos : 0 < (73 / 100 : ENNReal) := by norm_num
  have retentionConstantTop : (73 / 100 : ENNReal) ≠ ⊤ :=
    ENNReal.div_ne_top (by norm_num) (by norm_num)
  have leftPos : 0 < leftFactor := by
    dsimp only [leftFactor]
    exact ENNReal.mul_pos
      (ENNReal.mul_pos retentionConstantPos.ne'
        data.normalization_weight_ne_zero).ne'
      (ENNReal.mul_pos preFactor_pos.ne' innerInvPos.ne').ne'
  have leftTop : leftFactor ≠ ⊤ := by
    dsimp only [leftFactor]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top retentionConstantTop
        data.normalization_weight_ne_top)
      (ENNReal.mul_ne_top preFactor_ne_top innerInvTop)
  have rightTop : rightFactor ≠ ⊤ := by
    dsimp only [rightFactor]
    rw [data.regularized.regularizationLoss_eq]
    exact ENNReal.mul_ne_top (by norm_num) (by simp)
  have combinedMass : leftFactor * current.mass ≤
      rightFactor * inner.shading.mass := by
    calc
      leftFactor * current.mass =
          (preFactor * inner.massLoss⁻¹) *
            (((73 / 100 : ENNReal) * data.normalizationWeight) *
              current.mass) := by
        dsimp only [leftFactor]
        ring
      _ ≤ (preFactor * inner.massLoss⁻¹) *
          (data.regularized.regularizationLoss *
            data.normalization.croppedRefined.mass) := by
        exact mul_le_mul_left' data.reentryMassRetention _
      _ = data.regularized.regularizationLoss *
          (inner.massLoss⁻¹ *
            (preFactor * data.normalization.croppedRefined.mass)) := by ring
      _ ≤ data.regularized.regularizationLoss *
          (inner.massLoss⁻¹ * normalizedCurrent.mass) := by gcongr
      _ ≤ data.regularized.regularizationLoss * inner.shading.mass := by
        exact mul_le_mul_left' inner.mass_retention _
      _ = rightFactor * inner.shading.mass := by
        rfl
  have ambientMass : massLoss⁻¹ * current.mass ≤ ambient.mass := by
    rw [data.extendCandidate_mass]
    exact proposition63Lemma43MassLoss_inv_mul_le
      leftPos leftTop rightTop combinedMass
  have ambientExtremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      initialNormalized.croppedFamily ambient :=
    data.extendCandidate_extremal currentExtremal innerSubNormalized
      inner.cubical inner.extremal hcurrentOutput houtputLoss hdensityLift
  refine ⟨{
    shading := ambient
    subshading := ambientSub
    cubical := ambientCubical
    planeMap := ambientMap
    same_plane_map := rfl
    variation := ?_
    massLoss := massLoss
    massLoss_pos := proposition63Lemma43MassLoss_pos _ _
    massLoss_ne_top := proposition63Lemma43MassLoss_ne_top leftPos rightTop
    mass_retention := ambientMass
    extremal := ambientExtremal
  }⟩
  intro point pointMem other otherMem distanceBound
  have ambientUnion : ambient.union = inner.shading.union :=
    data.extendCandidate_union inner.shading
  have innerPoint : point ∈ inner.shading.union := by
    rw [← ambientUnion]
    exact pointMem
  have innerOther : other ∈ inner.shading.union := by
    rw [← ambientUnion]
    exact otherMem
  change dist (currentMap.planeMap point) (currentMap.planeMap other) ≤
    variationScale
  rw [← normalizedMap_eq, ← inner.same_plane_map]
  exact inner.variation point innerPoint other innerOther distanceBound

/-- Restore the outer terminal fine shading on its source family and prepare
the exact ordinary re-entry used by the dependent target-scale rich call. -/
theorem Proposition63RootNormalizationData.reenterOuterTerminal
    {delta sigma sourceLoss normalizationLoss densityLoss outerLoss
      outerExtremalLoss weightLoss targetReentryLoss
      targetReentryNormalizationLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {normalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading normalizationExponent
      sourceLoss normalizationLoss}
    (density_absorb :
      Kakeya.realRpowENN delta densityLoss ≤
        Kakeya.realRpowENN delta sourceLoss / 2)
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFamily)
      (Kakeya.realRpowENN delta (-normalizationLoss))
      (Kakeya.realRpowENN delta (-targetReentryLoss))
      (proposition63CanonicalNearbyLevelCount normalizationLoss))
    (ambient_two :
      (2 : ENNReal) < Kakeya.realRpowENN delta (-normalizationLoss))
    (hsourceOuter : normalizationLoss ≤ outerExtremalLoss)
    (houterExtremalLoss : 0 < outerExtremalLoss)
    (houterRetention :
      Kakeya.realRpowENN delta outerExtremalLoss ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta normalizationLoss)
    (houterTargetReentry : outerExtremalLoss ≤ targetReentryLoss)
    (htargetReentryNormalizationLoss :
      0 < targetReentryNormalizationLoss)
    (htargetReentryHalf :
      targetReentryLoss ≤ targetReentryNormalizationLoss / 2)
    (canonical_weight_absorb :
      proposition63CanonicalReentryWeight delta weightLoss ≤
        (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta (outerExtremalLoss + 2))
    (trace_fixed_absorb :
      (96 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta (targetReentryLoss - weightLoss) ≤ 1)
    (paper_fixed_absorb :
      ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta (targetReentryLoss - weightLoss) ≤
        (73 / 100 : ENNReal))
    (regularization_absorb :
      let degreeConstant :=
        16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
            schedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
            (schedule.scaleCount + 1)
      max degreeConstant
          (((proposition63CanonicalReentryWeight delta weightLoss)⁻¹ *
              (Kakeya.realRpowENN delta (-normalizationLoss) *
                (regularizationLoss *
                  ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
                    Kakeya.realRpowENN delta 2)) *
                degreeConstant)) *
            Kakeya.realRpowENN delta (-normalizationLoss)) ≤
        Kakeya.realRpowENN delta (-targetReentryLoss))
    (hdeltaSmall : delta ≤ 1 / 24) :
    ∃ targetReentry : Proposition63CurrentShadingReentryData
        (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
        (extendShading outer.data.selected outer.data.refined),
      targetReentry.normalizationWeight =
          proposition63CanonicalReentryWeight delta weightLoss ∧
        targetReentry.weightUpper =
          (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2 ∧
        targetReentry.levelCount =
          proposition63CanonicalNearbyLevelCount normalizationLoss ∧
        targetReentry.reentryNormalizationLoss =
          targetReentryNormalizationLoss := by
  let root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) outerReentry.ordinarySource
      normalizationExponent densityLoss :=
    Proposition63RootNormalizationData.ofPropStickyReentry
      outerReentry density_absorb
  have outerAmbientExtremal : WZ2PaperCroppedIsExtremal sigma
      outerExtremalLoss sourceFamily
      (extendShading outer.data.selected outer.data.refined) :=
    sticky_zero_extension_extremal outerReentry.cropped_extremal outer.data
      hsourceOuter houterRetention
  have outerAmbientSub : PaperIsSubshading
      (extendShading outer.data.selected outer.data.refined) sourceShading :=
    extendShading_subshading outer.data.selected outer.data.subshading
  have outerAmbientCubical : WZ1PaperIsCubicalShading
      (extendShading outer.data.selected outer.data.refined) :=
    extendShading_cubical outer.data.selected outer.data.refined_cubical
  exact root.currentShadingReentryFromExtremal
    (extendShading outer.data.selected outer.data.refined) schedule
    ambient_two outerAmbientExtremal houterTargetReentry
    houterExtremalLoss targetReentryNormalizationLoss
    htargetReentryNormalizationLoss htargetReentryHalf
    canonical_weight_absorb trace_fixed_absorb paper_fixed_absorb
    regularization_absorb outerAmbientSub outerAmbientCubical hdeltaSmall

/-- Execute the two rich Node 3 calls in the paper order on the actual
dependent family selected by the first call.  All schedules are fixed before
the runtime family; the result retains the canonical target re-entry receipts
needed by the scalar part of the one-scale theorem. -/
theorem proposition63_nested_two_rich_runtime
    {delta sigma initialInputLoss normalizationLoss firstReentryLoss
      densityLoss weightLoss outerExtremalLoss outerLoss targetLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource 0}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (firstReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := firstReentryLoss) initialNormalized current)
    (firstSchedule : Proposition63RichStickyKernelScheduleData sigma outerLoss)
    (hfirstReentryLoss : firstReentryLoss = firstSchedule.sourceLoss)
    (hfirstNormalizationLoss :
      firstReentry.reentryNormalizationLoss =
        firstSchedule.normalizationLoss)
    (hdeltaFirst : delta ≤ firstSchedule.delta₀)
    {robustScale : WZ2PaperRequestedScale delta}
    (hrobustLower : Real.rpow delta (1 - outerLoss) ≤ robustScale.1)
    (hrobustUpper : robustScale.1 ≤ Real.rpow delta outerLoss)
    (secondSchedule : Proposition63RichStickyKernelScheduleData sigma targetLoss)
    (hdeltaSecond : delta ≤ secondSchedule.delta₀)
    (density_absorb :
      Kakeya.realRpowENN delta densityLoss ≤
        Kakeya.realRpowENN delta firstReentryLoss / 2)
    (targetNearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := firstReentry.normalization.croppedFamily)
      (Kakeya.realRpowENN delta
        (-firstReentry.reentryNormalizationLoss))
      (Kakeya.realRpowENN delta (-secondSchedule.sourceLoss))
      (proposition63CanonicalNearbyLevelCount
        firstReentry.reentryNormalizationLoss))
    (ambient_two : (2 : ENNReal) < Kakeya.realRpowENN delta
      (-firstReentry.reentryNormalizationLoss))
    (hsourceOuter :
      firstReentry.reentryNormalizationLoss ≤ outerExtremalLoss)
    (houterExtremalLoss : 0 < outerExtremalLoss)
    (houterRetention :
      Kakeya.realRpowENN delta outerExtremalLoss ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            firstReentry.reentryNormalizationLoss)
    (houterTargetReentry :
      outerExtremalLoss ≤ secondSchedule.sourceLoss)
    (canonical_weight_absorb :
      proposition63CanonicalReentryWeight delta weightLoss ≤
        (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta (outerExtremalLoss + 2))
    (trace_fixed_absorb :
      (96 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta
            (secondSchedule.sourceLoss - weightLoss) ≤ 1)
    (paper_fixed_absorb :
      ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta
            (secondSchedule.sourceLoss - weightLoss) ≤
        (73 / 100 : ENNReal))
    (regularization_absorb :
      let degreeConstant :=
        16 * (targetNearbySchedule.scaleCount : ENNReal) *
          (Nat.log 2
            (2 * firstReentry.normalization.croppedFamily.card) + 1 :
              ENNReal) ^ targetNearbySchedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2
            (2 * firstReentry.normalization.croppedFamily.card) + 1 :
              ENNReal) ^ (targetNearbySchedule.scaleCount + 1)
      max degreeConstant
          (((proposition63CanonicalReentryWeight delta weightLoss)⁻¹ *
              (Kakeya.realRpowENN delta
                  (-firstReentry.reentryNormalizationLoss) *
                (regularizationLoss *
                  ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
                    Kakeya.realRpowENN delta 2)) *
                degreeConstant)) *
            Kakeya.realRpowENN delta
              (-firstReentry.reentryNormalizationLoss)) ≤
        Kakeya.realRpowENN delta (-secondSchedule.sourceLoss))
    (hdeltaSmall : delta ≤ 1 / 24)
    {targetScale : WZ2PaperRequestedScale delta}
    (htargetLower : Real.rpow delta (1 - targetLoss) ≤ targetScale.1)
    (htargetUpper : targetScale.1 ≤ Real.rpow delta targetLoss) :
    ∃ outer : Proposition63RichTerminalStickyData
        (outputLoss := outerLoss) firstReentry.normalization.croppedRefined
        (firstReentry.normalization.toPropStickyReentryData
          (by rw [hfirstReentryLoss]; exact firstSchedule.sourceLoss_pos)
          firstReentry.reentry_normalization_loss_pos) robustScale,
      ∃ targetReentry : Proposition63CurrentShadingReentryData
          (reentryLoss := secondSchedule.sourceLoss)
          firstReentry.normalization
          (extendShading outer.data.selected outer.data.refined),
        targetReentry.normalizationWeight =
            proposition63CanonicalReentryWeight delta weightLoss ∧
          targetReentry.weightUpper =
            (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2 ∧
          targetReentry.levelCount = proposition63CanonicalNearbyLevelCount
            firstReentry.reentryNormalizationLoss ∧
          targetReentry.reentryNormalizationLoss =
            secondSchedule.normalizationLoss ∧
          Nonempty (Proposition63RichTerminalStickyData
            (outputLoss := targetLoss)
            targetReentry.normalization.croppedRefined
            (targetReentry.normalization.toPropStickyReentryData
              secondSchedule.sourceLoss_pos
              targetReentry.reentry_normalization_loss_pos) targetScale) := by
  rcases proposition63CurrentShadingReentry_richTerminalSticky firstReentry
      firstSchedule hfirstReentryLoss hfirstNormalizationLoss hdeltaFirst
      robustScale hrobustLower hrobustUpper with ⟨outer⟩
  let outerReentry :=
    firstReentry.normalization.toPropStickyReentryData
      (by rw [hfirstReentryLoss]; exact firstSchedule.sourceLoss_pos)
      firstReentry.reentry_normalization_loss_pos
  have targetReentryExists :=
    Proposition63RootNormalizationData.reenterOuterTerminal
      (outerReentry := outerReentry) density_absorb outer
      targetNearbySchedule ambient_two hsourceOuter
      houterExtremalLoss houterRetention houterTargetReentry
      secondSchedule.normalizationLoss_pos
      secondSchedule.sourceLoss_le_half canonical_weight_absorb
      trace_fixed_absorb paper_fixed_absorb regularization_absorb hdeltaSmall
  let targetReentry := Classical.choose targetReentryExists
  have targetReentrySpec := Classical.choose_spec targetReentryExists
  have weightEq := targetReentrySpec.1
  have weightUpperEq := targetReentrySpec.2.1
  have levelEq := targetReentrySpec.2.2.1
  have normalizationEq := targetReentrySpec.2.2.2
  have target := proposition63CurrentShadingReentry_richTerminalSticky
    targetReentry secondSchedule rfl normalizationEq hdeltaSecond
      targetScale htargetLower htargetUpper
  exact ⟨outer, targetReentry, weightEq, weightUpperEq, levelEq,
    normalizationEq, target⟩

/-- Family-level envelope for the external-weight regularization used by the
second rich call in one Lemma 4.7 step. -/
def proposition63OneScaleReentryRegularizationEnvelope
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta)
    (levelCount : ℕ) : ENNReal :=
  (8 : ENNReal) *
    (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^ (levelCount + 2)

/-- One fixed coefficient dominates both logarithmic quantities occurring in
the two-rich scalar ledger. -/
def proposition63OneScaleLogCoefficient : ℝ :=
  max 2 pureWZ2Prop62OrdinaryCardLogConstant

def proposition63OneScaleLogEnvelope (delta : ℝ) : ENNReal :=
  ENNReal.ofReal
    (proposition63OneScaleLogCoefficient * (1 + Real.log delta⁻¹))

theorem proposition63OneScaleLogCoefficient_nonneg :
    0 ≤ proposition63OneScaleLogCoefficient :=
  (by norm_num : (0 : ℝ) ≤ 2).trans (le_max_left _ _)

/-- Replace the target re-entry's data-dependent regularization loss by the
fixed envelope determined by its ambient family and canonical level count. -/
theorem Proposition63CurrentShadingReentryData.regularizationLoss_le_oneScaleEnvelope
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent levelCount : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (hlevelCount : data.levelCount = levelCount) :
    data.regularized.regularizationLoss ≤
      proposition63OneScaleReentryRegularizationEnvelope
        initialNormalized.croppedFamily levelCount := by
  have logOne : (1 : ENNReal) ≤
      (Nat.log 2 (2 * initialNormalized.croppedFamily.card) + 1 :
        ENNReal) := by
    exact_mod_cast Nat.succ_le_succ
      (Nat.zero_le (Nat.log 2 (2 * initialNormalized.croppedFamily.card)))
  have exponentBound : data.schedule.scaleCount + 1 ≤ levelCount + 2 := by
    have scaleCountBound := data.schedule.scaleCount_le
    omega
  rw [data.regularized.regularizationLoss_eq]
  unfold proposition63OneScaleReentryRegularizationEnvelope
  exact mul_le_mul_left'
    (pow_le_pow_right' logOne exponentBound) 8

/-- Every cropped normalization has a family-independent logarithmic
cardinality bound.  Pure nearby CWA supplies ordinary centered-containment
distinctness, and bounded basepoints place all tube midpoints in the fixed
six-parameter packing window. -/
theorem proposition63_cropped_cardLog_le_fixedEnvelope
    {delta sigma inputLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent)
    (_hdeltaSmall : delta ≤ 1 / 100000) :
    (Nat.log 2 (2 * normalized.croppedFamily.card) + 1 : ENNReal) ≤
      ENNReal.ofReal
        (proposition63OneScaleLogCoefficient *
          (1 + Real.log delta⁻¹)) := by
  let scaleCount := Nat.ceil (320 / delta)
  have midpointNormLeFive : ∀ index,
      ‖wz2PaperTubeMidpoint (normalized.croppedFamily.tube index)‖ ≤ 5 := by
    intro index
    let tube := normalized.croppedFamily.tube index
    dsimp only [wz2PaperTubeMidpoint]
    calc
      ‖tube.base + (1 / 2 : ℝ) • tube.direction‖ ≤
          ‖tube.base‖ + ‖(1 / 2 : ℝ) • tube.direction‖ :=
        norm_add_le _ _
      _ = ‖tube.base‖ + 1 / 2 := by
        rw [norm_smul, tube.direction_unit]
        norm_num
      _ ≤ 5 := by
        change ‖(normalized.croppedFamily.tube index).base‖ + 1 / 2 ≤ 5
        linarith [normalized.ordinary_bounded_base index]
  have rawCard : normalized.croppedFamily.card ≤
      (2 * scaleCount + 1) ^ 6 := by
    have raw := wz2PaperOrdinary_local_six_grid_card_bound
      normalized.final_extremal.delta_pos
      (show (0 : ℝ) ≤ 5 by norm_num)
      normalized.final_extremal.cwa_nearby_scales.2.2.1
      Finset.univ (0 : Point3) <| by
        intro index _
        simpa [dist_zero_right] using
          midpointNormLeFive index
    have firstArgument : 5 / (delta / 64) = 320 / delta := by
      field_simp [normalized.final_extremal.delta_pos.ne']
      norm_num
    have secondArgument : 1 / (delta / 64) ≤ 320 / delta := by
      have identity : 1 / (delta / 64) = 64 / delta := by
        field_simp [normalized.final_extremal.delta_pos.ne']
      rw [identity]
      exact div_le_div_of_nonneg_right (by norm_num)
        normalized.final_extremal.delta_pos.le
    have firstCeil : Nat.ceil (5 / (delta / 64)) = scaleCount := by
      rw [firstArgument]
    have secondCeil : Nat.ceil (1 / (delta / 64)) ≤ scaleCount :=
      Nat.ceil_mono secondArgument
    simpa only [Finset.card_univ, Fintype.card_fin] using raw.trans (by
      rw [firstCeil]
      calc
        (2 * scaleCount + 1) ^ 3 *
              (2 * Nat.ceil (1 / (delta / 64)) + 1) ^ 3 ≤
            (2 * scaleCount + 1) ^ 3 *
              (2 * scaleCount + 1) ^ 3 := by gcongr
        _ = (2 * scaleCount + 1) ^ 6 := by ring)
  have realBound := pureWZ2Prop62_ordinary_card_log_bound
    normalized.final_extremal.delta_pos
    normalized.final_extremal.delta_le_one
    normalized.final_extremal.nonempty rawCard
  calc
    (Nat.log 2 (2 * normalized.croppedFamily.card) + 1 : ENNReal) =
        ENNReal.ofReal
          (Nat.log 2 (2 * normalized.croppedFamily.card) + 1 : ℝ) := by
      simpa using
        (ENNReal.ofReal_natCast
          (Nat.log 2 (2 * normalized.croppedFamily.card) + 1)).symm
    _ ≤ ENNReal.ofReal
        (proposition63OneScaleLogCoefficient *
          (1 + Real.log delta⁻¹)) := by
      apply ENNReal.ofReal_mono
      apply realBound.trans
      unfold proposition63OneScaleLogCoefficient
      have logNonnegative : 0 ≤ 1 + Real.log delta⁻¹ := by
        have inverseOne : (1 : ℝ) ≤ delta⁻¹ := by
          apply (one_le_inv₀ normalized.final_extremal.delta_pos).mpr
          exact normalized.final_extremal.delta_le_one
        linarith [Real.log_nonneg inverseOne]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) logNonnegative

theorem proposition63_cropped_cardLog_le_oneScaleEnvelope
    {delta sigma inputLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent)
    (hdeltaSmall : delta ≤ 1 / 100000) :
    (Nat.log 2 (2 * normalized.croppedFamily.card) + 1 : ENNReal) ≤
      proposition63OneScaleLogEnvelope delta := by
  unfold proposition63OneScaleLogEnvelope
  exact proposition63_cropped_cardLog_le_fixedEnvelope normalized hdeltaSmall

theorem proposition63_logarithmicLoss_le_oneScaleEnvelope
    {delta : ℝ} (hdeltaPos : 0 < delta) (hdeltaOne : delta ≤ 1) :
    Prop62PaperAudit.V4.logarithmicLoss delta ≤
      proposition63OneScaleLogEnvelope delta := by
  have raw := proposition63_logarithmicLoss_le_two_logEnvelope
    hdeltaPos hdeltaOne
  apply raw.trans
  unfold proposition63OneScaleLogEnvelope
  have logNonnegative : 0 ≤ 1 + Real.log delta⁻¹ := by
    have inverseOne : (1 : ℝ) ≤ delta⁻¹ := by
      apply (one_le_inv₀ hdeltaPos).mpr hdeltaOne
    linarith [Real.log_nonneg inverseOne]
  have twoAsOfReal : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
  rw [twoAsOfReal, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_mono
    (mul_le_mul_of_nonneg_right (le_max_left _ _) logNonnegative)

theorem proposition63OneScaleReentryRegularizationEnvelope_le_logEnvelope
    {delta sigma inputLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent levelCount : ℕ}
    (normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent)
    (hdeltaSmall : delta ≤ 1 / 100000) :
    proposition63OneScaleReentryRegularizationEnvelope
        normalized.croppedFamily levelCount ≤
      8 * proposition63OneScaleLogEnvelope delta ^ (levelCount + 2) := by
  unfold proposition63OneScaleReentryRegularizationEnvelope
  exact mul_le_mul_left'
    (pow_le_pow_left'
      (proposition63_cropped_cardLog_le_oneScaleEnvelope normalized hdeltaSmall) _) 8

/-- A family-free small-scale receipt for the external-weight regularization
used when an already-extremal current shading re-enters Node 3.  Both the
degree and mass costs are bounded by the fixed logarithmic envelope before
the runtime normalization is known. -/
structure Proposition63ReentryRegularizationAbsorptionData
    (normalizationLoss weightLoss reentryLoss : ℝ) (levelCount : ℕ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_tiny : delta₀ ≤ 1 / 100000
  absorb :
    ∀ {delta sigma inputLoss actualNormalizationLoss actualReentryLoss : ℝ}
      {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
      {normalizationExponent actualLevelCount : ℕ},
      ∀ (normalized : PureWZ2CroppedCriticalNormalizationData
          (outputLoss := actualNormalizationLoss) source normalizationExponent),
        actualNormalizationLoss = normalizationLoss →
        ∀ schedule : WZ2PaperPureFiniteNearbyScheduleData
          (fine := normalized.croppedFamily)
          (Kakeya.realRpowENN delta (-actualNormalizationLoss))
          (Kakeya.realRpowENN delta (-actualReentryLoss)) actualLevelCount,
          actualReentryLoss = reentryLoss → actualLevelCount = levelCount →
          0 < delta → delta ≤ delta₀ →
            let degreeConstant :=
              16 * (schedule.scaleCount : ENNReal) *
                (Nat.log 2 (2 * normalized.croppedFamily.card) + 1 :
                  ENNReal) ^ schedule.scaleCount
            let regularizationLoss :=
              (8 : ENNReal) *
                (Nat.log 2 (2 * normalized.croppedFamily.card) + 1 :
                  ENNReal) ^ (schedule.scaleCount + 1)
            max degreeConstant
                (((proposition63CanonicalReentryWeight delta weightLoss)⁻¹ *
                    (Kakeya.realRpowENN delta (-actualNormalizationLoss) *
                      (regularizationLoss *
                        ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
                          Kakeya.realRpowENN delta 2)) *
                      degreeConstant)) *
                  Kakeya.realRpowENN delta (-actualNormalizationLoss)) ≤
              Kakeya.realRpowENN delta (-actualReentryLoss)

/-- Choose the current-reentry regularization threshold before the runtime
family.  The strict power gap is exactly the cost of two nearby-scale
ambient constants and the canonical external weight. -/
theorem proposition63_reentry_regularization_absorption
    (normalizationLoss weightLoss reentryLoss : ℝ) (levelCount : ℕ)
    (hlevelCount : 0 < levelCount)
    (hreentryLoss : 0 < reentryLoss)
    (hgap : 0 < reentryLoss - weightLoss - 2 * normalizationLoss) :
    Nonempty (Proposition63ReentryRegularizationAbsorptionData
      normalizationLoss weightLoss reentryLoss levelCount) := by
  let gap : ℝ := reentryLoss - weightLoss - 2 * normalizationLoss
  have gapPos : 0 < gap := by simpa [gap] using hgap
  let degreeFixed : ENNReal := 16 * ((levelCount + 1 : ℕ) : ENNReal)
  have degreeFixedTop : degreeFixed ≠ ⊤ := by
    dsimp only [degreeFixed]
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
  rcases exists_delta_C_pow_log_absorbed_ennreal degreeFixed degreeFixedTop
      proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg hreentryLoss
      (show 0 < levelCount + 1 by omega) with
    ⟨degreeDelta, degreeDeltaPos, degreeDeltaOne, degreeAbsorb⟩
  let geometry : ENNReal :=
    (55296 : ENNReal) * Kakeya.deltaTubeVolume 1
  let massFixed : ENNReal :=
    (8 : ENNReal) * geometry * degreeFixed
  have geometryTop : geometry ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top
  have massFixedTop : massFixed ≠ ⊤ := by
    dsimp only [massFixed]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) geometryTop) degreeFixedTop
  have massExponentPos : 0 < 2 * levelCount + 3 := by omega
  rcases exists_delta_C_pow_log_absorbed_ennreal massFixed massFixedTop
      proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg gapPos massExponentPos with
    ⟨massDelta, massDeltaPos, massDeltaOne, massAbsorb⟩
  let delta₀ : ℝ := min degreeDelta (min massDelta (1 / 100000))
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := by dsimp only [delta₀]; positivity
    delta₀_le_one := (min_le_left _ _).trans degreeDeltaOne
    delta₀_le_tiny :=
      (min_le_right _ _).trans (min_le_right _ _)
    absorb := ?_
  }⟩
  intro delta sigma inputLoss actualNormalizationLoss actualReentryLoss source
    normalizationExponent actualLevelCount normalized normalizationEq schedule
    reentryEq levelCountEq deltaPos deltaLe
  subst actualNormalizationLoss
  subst actualReentryLoss
  subst actualLevelCount
  dsimp only
  have deltaLeDegree : delta ≤ degreeDelta :=
    deltaLe.trans (min_le_left _ _)
  have deltaLeMass : delta ≤ massDelta :=
    deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have deltaTiny : delta ≤ 1 / 100000 :=
    deltaLe.trans <| (min_le_right _ _).trans (min_le_right _ _)
  have deltaOne : delta ≤ 1 := deltaLeDegree.trans degreeDeltaOne
  let envelope : ENNReal := proposition63OneScaleLogEnvelope delta
  have envelopeOne : (1 : ENNReal) ≤ envelope := by
    dsimp only [envelope, proposition63OneScaleLogEnvelope]
    have inverseOne : (1 : ℝ) ≤ delta⁻¹ :=
      (one_le_inv₀ deltaPos).mpr deltaOne
    have logNonnegative : 0 ≤ Real.log delta⁻¹ :=
      Real.log_nonneg inverseOne
    have coefficientOne : 1 ≤ proposition63OneScaleLogCoefficient :=
      (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
    rw [show (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) by norm_num]
    apply ENNReal.ofReal_mono
    nlinarith [mul_nonneg (sub_nonneg.mpr coefficientOne)
      (show 0 ≤ 1 + Real.log delta⁻¹ by linarith)]
  have logBound :
      (Nat.log 2 (2 * normalized.croppedFamily.card) + 1 : ENNReal) ≤
        envelope := by
    exact proposition63_cropped_cardLog_le_oneScaleEnvelope normalized
      deltaTiny
  have scaleCountLe : schedule.scaleCount ≤ levelCount + 1 :=
    schedule.scaleCount_le
  have scaleCountCastLe :
      (schedule.scaleCount : ENNReal) ≤ ((levelCount + 1 : ℕ) : ENNReal) := by
    exact_mod_cast scaleCountLe
  let degreeConstant : ENNReal :=
    16 * (schedule.scaleCount : ENNReal) *
      (Nat.log 2 (2 * normalized.croppedFamily.card) + 1 : ENNReal) ^
        schedule.scaleCount
  let regularizationLoss : ENNReal :=
    (8 : ENNReal) *
      (Nat.log 2 (2 * normalized.croppedFamily.card) + 1 : ENNReal) ^
        (schedule.scaleCount + 1)
  have degreeBound :
      degreeConstant ≤ degreeFixed * envelope ^ (levelCount + 1) := by
    calc
      degreeConstant ≤
          16 * ((levelCount + 1 : ℕ) : ENNReal) *
            envelope ^ schedule.scaleCount := by
        dsimp only [degreeConstant]
        gcongr
      _ ≤ 16 * ((levelCount + 1 : ℕ) : ENNReal) *
          envelope ^ (levelCount + 1) := by
        gcongr
      _ = degreeFixed * envelope ^ (levelCount + 1) := by rfl
  have regularizationBound :
      regularizationLoss ≤ 8 * envelope ^ (levelCount + 2) := by
    dsimp only [regularizationLoss]
    calc
      (8 : ENNReal) *
            (Nat.log 2 (2 * normalized.croppedFamily.card) + 1 :
              ENNReal) ^ (schedule.scaleCount + 1) ≤
          8 * envelope ^ (schedule.scaleCount + 1) := by gcongr
      _ ≤ 8 * envelope ^ (levelCount + 2) := by
        apply mul_le_mul_left'
        apply pow_le_pow_right' envelopeOne
        omega
  have degreeAbsorption :
      degreeFixed * envelope ^ (levelCount + 1) ≤
        Kakeya.realRpowENN delta (-reentryLoss) := by
    simpa [envelope, proposition63OneScaleLogEnvelope] using
      degreeAbsorb delta deltaPos deltaLeDegree
  have massAbsorption :
      massFixed * envelope ^ (2 * levelCount + 3) ≤
        Kakeya.realRpowENN delta (-gap) := by
    simpa [envelope, proposition63OneScaleLogEnvelope] using
      massAbsorb delta deltaPos deltaLeMass
  have powerIdentity :
      (proposition63CanonicalReentryWeight delta weightLoss)⁻¹ *
          Kakeya.realRpowENN delta (-normalizationLoss) *
          Kakeya.realRpowENN delta 2 *
          Kakeya.realRpowENN delta (-normalizationLoss) =
        Kakeya.realRpowENN delta (-weightLoss - 2 * normalizationLoss) := by
    unfold proposition63CanonicalReentryWeight
    rw [pure_wz2_realRpowENN_inv deltaPos]
    rw [← realRpowENN_add deltaPos]
    rw [← realRpowENN_add deltaPos]
    rw [← realRpowENN_add deltaPos]
    congr 1
    ring
  have massEnvelope :
      (((proposition63CanonicalReentryWeight delta weightLoss)⁻¹ *
            (Kakeya.realRpowENN delta (-normalizationLoss) *
              ((8 * envelope ^ (levelCount + 2)) *
                (geometry * Kakeya.realRpowENN delta 2)) *
              (degreeFixed * envelope ^ (levelCount + 1)))) *
          Kakeya.realRpowENN delta (-normalizationLoss)) ≤
        Kakeya.realRpowENN delta (-reentryLoss) := by
    have logCombine :
        envelope ^ (levelCount + 2) * envelope ^ (levelCount + 1) =
          envelope ^ (2 * levelCount + 3) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      (((proposition63CanonicalReentryWeight delta weightLoss)⁻¹ *
            (Kakeya.realRpowENN delta (-normalizationLoss) *
              ((8 * envelope ^ (levelCount + 2)) *
                (geometry * Kakeya.realRpowENN delta 2)) *
              (degreeFixed * envelope ^ (levelCount + 1)))) *
          Kakeya.realRpowENN delta (-normalizationLoss)) =
        (massFixed * envelope ^ (2 * levelCount + 3)) *
          Kakeya.realRpowENN delta
            (-weightLoss - 2 * normalizationLoss) := by
              rw [← powerIdentity, ← logCombine]
              dsimp only [massFixed]
              ring
      _ ≤ Kakeya.realRpowENN delta (-gap) *
          Kakeya.realRpowENN delta
            (-weightLoss - 2 * normalizationLoss) := by gcongr
      _ = Kakeya.realRpowENN delta (-reentryLoss) := by
        rw [← realRpowENN_add deltaPos]
        congr 1
        dsimp only [gap]
        ring
  apply max_le
  · exact degreeBound.trans degreeAbsorption
  · apply (show
        (((proposition63CanonicalReentryWeight delta weightLoss)⁻¹ *
              (Kakeya.realRpowENN delta (-normalizationLoss) *
                (regularizationLoss *
                  ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
                    Kakeya.realRpowENN delta 2)) *
                degreeConstant)) *
            Kakeya.realRpowENN delta (-normalizationLoss)) ≤
          (((proposition63CanonicalReentryWeight delta weightLoss)⁻¹ *
              (Kakeya.realRpowENN delta (-normalizationLoss) *
                ((8 * envelope ^ (levelCount + 2)) *
                  (geometry * Kakeya.realRpowENN delta 2)) *
                (degreeFixed * envelope ^ (levelCount + 1)))) *
            Kakeya.realRpowENN delta (-normalizationLoss)) by
              dsimp only [geometry]
              gcongr).trans
    exact massEnvelope

/-- Uniform absorption of one pure logarithmic refinement into a strict
extremality-loss gap. -/
structure Proposition63RefinementRetentionAbsorptionData
    (sourceLoss outputLoss : ℝ) (logExponent : ℕ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    Kakeya.realRpowENN delta outputLoss ≤
      wz2PaperPureRefinementFraction delta logExponent *
        Kakeya.realRpowENN delta sourceLoss

theorem proposition63_refinement_retention_absorption
    (sourceLoss outputLoss : ℝ) (logExponent : ℕ)
    (hgap : sourceLoss < outputLoss)
    (hlogExponent : 0 < logExponent) :
    Nonempty (Proposition63RefinementRetentionAbsorptionData
      sourceLoss outputLoss logExponent) := by
  let gap : ℝ := outputLoss - sourceLoss
  have gapPos : 0 < gap := by dsimp only [gap]; linarith
  rcases exists_delta_log_absorbed_ennreal (1 : ENNReal) (by norm_num)
      gapPos hlogExponent with
    ⟨logDelta, logDeltaPos, logDeltaOne, logAbsorb⟩
  let delta₀ : ℝ := min logDelta (Real.exp (-1))
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := by dsimp only [delta₀]; positivity
    delta₀_le_one := (min_le_left _ _).trans logDeltaOne
    absorb := ?_
  }⟩
  intro delta deltaPos deltaLe
  have deltaLeLog : delta ≤ logDelta := deltaLe.trans (min_le_left _ _)
  have deltaLtOne : delta < 1 :=
    deltaLe.trans_lt <| (min_le_right _ _).trans_lt
      (Real.exp_lt_one_iff.mpr (by norm_num))
  let logTerm : ENNReal := ENNReal.ofReal (Real.log (1 / delta))
  have logTermPos : 0 < logTerm := by
    exact ENNReal.ofReal_pos.mpr <|
      Real.log_pos (one_lt_one_div deltaPos deltaLtOne)
  have logTermTop : logTerm ≠ ⊤ := by simp [logTerm]
  have logPowerPos : 0 < logTerm ^ logExponent := by positivity
  have logPowerTop : logTerm ^ logExponent ≠ ⊤ :=
    ENNReal.pow_ne_top logTermTop
  have logTermLe : logTerm ≤ ENNReal.ofReal (1 + Real.log delta⁻¹) := by
    dsimp only [logTerm]
    apply ENNReal.ofReal_mono
    rw [show 1 / delta = delta⁻¹ by simp]
    linarith
  have logarithmicAbsorption :
      logTerm ^ logExponent ≤ Kakeya.realRpowENN delta (-gap) := by
    calc
      logTerm ^ logExponent ≤
          ENNReal.ofReal (1 + Real.log delta⁻¹) ^ logExponent := by gcongr
      _ = 1 * ENNReal.ofReal
          (1 + Real.log delta⁻¹) ^ logExponent := by simp
      _ ≤ Kakeya.realRpowENN delta (-gap) :=
        logAbsorb delta deltaPos deltaLeLog
  have multiplied :
      Kakeya.realRpowENN delta outputLoss * logTerm ^ logExponent ≤
        Kakeya.realRpowENN delta sourceLoss := by
    calc
      Kakeya.realRpowENN delta outputLoss * logTerm ^ logExponent ≤
          Kakeya.realRpowENN delta outputLoss *
            Kakeya.realRpowENN delta (-gap) := by gcongr
      _ = Kakeya.realRpowENN delta sourceLoss := by
        rw [← realRpowENN_add deltaPos]
        congr 1
        dsimp only [gap]
        ring
  rw [wz2PaperPureRefinementFraction, ← ENNReal.inv_pow]
  change Kakeya.realRpowENN delta outputLoss ≤
    (logTerm ^ logExponent)⁻¹ *
      Kakeya.realRpowENN delta sourceLoss
  rw [show (logTerm ^ logExponent)⁻¹ *
      Kakeya.realRpowENN delta sourceLoss =
      Kakeya.realRpowENN delta sourceLoss / logTerm ^ logExponent by
        rw [ENNReal.div_eq_inv_mul]]
  exact (ENNReal.le_div_iff_mul_le
    (Or.inl logPowerPos.ne') (Or.inl logPowerTop)).2 multiplied

/-- All scalar receipts required to prepare one current shading for a fresh
rich Node 3 call, with one threshold fixed before the runtime family. -/
structure Proposition63CurrentReentryAbsorptionData
    (sourceLoss normalizationLoss densityLoss currentLoss weightLoss
      reentryLoss : ℝ) (levelCount : ℕ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_tiny : delta₀ ≤ 1 / 100000
  density_absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    Kakeya.realRpowENN delta densityLoss ≤
      Kakeya.realRpowENN delta sourceLoss / 2
  ambient_two : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    (2 : ENNReal) < Kakeya.realRpowENN delta (-normalizationLoss)
  canonical_weight_absorb :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      proposition63CanonicalReentryWeight delta weightLoss ≤
        (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta (currentLoss + 2)
  trace_fixed_absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    (96 * Kakeya.deltaTubeVolume 1) *
      Kakeya.realRpowENN delta (reentryLoss - weightLoss) ≤ 1
  paper_fixed_absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
      Kakeya.realRpowENN delta (reentryLoss - weightLoss) ≤
        (73 / 100 : ENNReal)
  regularization_absorb :
    ∀ {delta sigma inputLoss actualNormalizationLoss actualReentryLoss : ℝ}
      {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
      {normalizationExponent actualLevelCount : ℕ},
      ∀ (normalized : PureWZ2CroppedCriticalNormalizationData
          (outputLoss := actualNormalizationLoss) source normalizationExponent),
        actualNormalizationLoss = normalizationLoss →
        ∀ schedule : WZ2PaperPureFiniteNearbyScheduleData
          (fine := normalized.croppedFamily)
          (Kakeya.realRpowENN delta (-actualNormalizationLoss))
          (Kakeya.realRpowENN delta (-actualReentryLoss)) actualLevelCount,
          actualReentryLoss = reentryLoss → actualLevelCount = levelCount →
          0 < delta → delta ≤ delta₀ →
            let degreeConstant :=
              16 * (schedule.scaleCount : ENNReal) *
                (Nat.log 2 (2 * normalized.croppedFamily.card) + 1 :
                  ENNReal) ^ schedule.scaleCount
            let regularizationLoss :=
              (8 : ENNReal) *
                (Nat.log 2 (2 * normalized.croppedFamily.card) + 1 :
                  ENNReal) ^ (schedule.scaleCount + 1)
            max degreeConstant
                (((proposition63CanonicalReentryWeight delta weightLoss)⁻¹ *
                    (Kakeya.realRpowENN delta (-actualNormalizationLoss) *
                      (regularizationLoss *
                        ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
                          Kakeya.realRpowENN delta 2)) *
                      degreeConstant)) *
                  Kakeya.realRpowENN delta (-actualNormalizationLoss)) ≤
              Kakeya.realRpowENN delta (-actualReentryLoss)

theorem proposition63_current_reentry_absorption
    (sourceLoss normalizationLoss densityLoss currentLoss weightLoss
      reentryLoss : ℝ) (levelCount : ℕ)
    (hsourceDensity : sourceLoss < densityLoss)
    (hnormalizationLoss : 0 < normalizationLoss)
    (hdensityWeight : densityLoss + currentLoss < weightLoss)
    (hweightReentry : weightLoss < reentryLoss)
    (hlevelCount : 0 < levelCount)
    (hreentryLoss : 0 < reentryLoss)
    (hregularizationGap :
      0 < reentryLoss - weightLoss - 2 * normalizationLoss) :
    Nonempty (Proposition63CurrentReentryAbsorptionData
      sourceLoss normalizationLoss densityLoss currentLoss weightLoss
      reentryLoss levelCount) := by
  rcases exists_delta_mul_rpow_le_rpow (2 : ℝ) (by norm_num)
      hsourceDensity with
    ⟨densityDelta, densityDeltaPos, densityDeltaOne, densityAbsorbReal⟩
  rcases exists_delta_proposition63CanonicalNearbyAmbient_gt_two
      hnormalizationLoss with
    ⟨ambientDelta, ambientDeltaPos, ambientDeltaOne, ambientTwo⟩
  rcases exists_delta_proposition63CanonicalReentryWeight_le
      hdensityWeight with
    ⟨weightDelta, weightDeltaPos, weightDeltaOne, weightAbsorb⟩
  rcases exists_delta_proposition63CanonicalReentryWeight_scale_bounds
      hweightReentry with
    ⟨scaleDelta, scaleDeltaPos, scaleDeltaOne, scaleAbsorb⟩
  rcases proposition63_reentry_regularization_absorption
      normalizationLoss weightLoss reentryLoss levelCount hlevelCount
      hreentryLoss hregularizationGap with
    ⟨regularization⟩
  let delta₀ := min densityDelta <| min ambientDelta <| min weightDelta <|
    min scaleDelta regularization.delta₀
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := by
      dsimp only [delta₀]
      exact lt_min densityDeltaPos <| lt_min ambientDeltaPos <|
        lt_min weightDeltaPos <| lt_min scaleDeltaPos
          regularization.delta₀_pos
    delta₀_le_one := (min_le_left _ _).trans densityDeltaOne
    delta₀_le_tiny :=
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans
          regularization.delta₀_le_tiny
    density_absorb := ?_
    ambient_two := ?_
    canonical_weight_absorb := ?_
    trace_fixed_absorb := ?_
    paper_fixed_absorb := ?_
    regularization_absorb := ?_
  }⟩
  · intro delta deltaPos deltaLe
    have absorbReal :
        2 * Real.rpow delta densityLoss ≤
          Real.rpow delta sourceLoss :=
      densityAbsorbReal delta deltaPos
        (deltaLe.trans (min_le_left _ _))
    apply (ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).2
    calc
      Kakeya.realRpowENN delta densityLoss * 2 =
          ENNReal.ofReal
            (Real.rpow delta densityLoss * 2) := by
        rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num]
        exact (ENNReal.ofReal_mul
          (Real.rpow_nonneg deltaPos.le densityLoss)).symm
      _ ≤ ENNReal.ofReal (Real.rpow delta sourceLoss) :=
        ENNReal.ofReal_mono (by simpa [mul_comm] using absorbReal)
      _ = Kakeya.realRpowENN delta sourceLoss := rfl
  · intro delta deltaPos deltaLe
    exact ambientTwo delta deltaPos <|
      deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
  · intro delta deltaPos deltaLe
    exact weightAbsorb delta deltaPos <|
      deltaLe.trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  · intro delta deltaPos deltaLe
    exact (scaleAbsorb delta deltaPos <|
      deltaLe.trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)).1
  · intro delta deltaPos deltaLe
    exact (scaleAbsorb delta deltaPos <|
      deltaLe.trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)).2
  · intro delta sigma inputLoss actualNormalizationLoss actualReentryLoss
      source normalizationExponent actualLevelCount normalized normalizationEq
      schedule reentryEq levelCountEq deltaPos deltaLe
    exact regularization.absorb normalized normalizationEq schedule reentryEq
      levelCountEq deltaPos <|
      deltaLe.trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _)

/-- Family-free small-scale receipt for lifting an already-extremal candidate
through one current-shading re-entry. -/
structure Proposition63ReentryDensityLiftAbsorptionData
    (weightLoss innerLoss outputLoss : ℝ) (levelCount : ℕ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_tiny : delta₀ ≤ 1 / 100000
  absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
        ((8 : ENNReal) * proposition63OneScaleLogEnvelope delta ^
          (levelCount + 2) *
          ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2)) *
        Kakeya.realRpowENN delta outputLoss ≤
      proposition63CanonicalReentryWeight delta weightLoss *
        Kakeya.realRpowENN delta innerLoss

/-- Choose the density-lift threshold before the runtime family. -/
theorem proposition63_reentry_density_lift_absorption
    (weightLoss innerLoss outputLoss : ℝ) (levelCount : ℕ)
    (hgap : 0 < outputLoss - innerLoss - weightLoss) :
    Nonempty (Proposition63ReentryDensityLiftAbsorptionData
      weightLoss innerLoss outputLoss levelCount) := by
  let gap : ℝ := outputLoss - innerLoss - weightLoss
  have gapPos : 0 < gap := by simpa [gap] using hgap
  let geometry : ENNReal :=
    (55296 : ENNReal) * Kakeya.deltaTubeVolume 1
  let fixed : ENNReal := geometry * 8 * geometry
  have geometryTop : geometry ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top
  have fixedTop : fixed ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top geometryTop (by norm_num))
      geometryTop
  have exponentPos : 0 < levelCount + 2 := by omega
  rcases exists_delta_C_pow_log_absorbed_ennreal
      fixed fixedTop proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg gapPos exponentPos with
    ⟨logDelta, logDeltaPos, logDeltaOne, logAbsorb⟩
  let delta₀ : ℝ := min logDelta (1 / 100000)
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min logDeltaPos (by norm_num)
    delta₀_le_one := (min_le_left _ _).trans logDeltaOne
    delta₀_le_tiny := min_le_right _ _
    absorb := ?_
  }⟩
  intro delta deltaPos deltaLe
  have deltaLeLog : delta ≤ logDelta := deltaLe.trans (min_le_left _ _)
  have logarithmicAbsorption :
      fixed * proposition63OneScaleLogEnvelope delta ^ (levelCount + 2) ≤
        Kakeya.realRpowENN delta (-gap) := by
    simpa [proposition63OneScaleLogEnvelope] using
      logAbsorb delta deltaPos deltaLeLog
  have powerIdentity :
      Kakeya.realRpowENN delta (-gap) *
          (Kakeya.realRpowENN delta 2 *
            Kakeya.realRpowENN delta outputLoss) =
        proposition63CanonicalReentryWeight delta weightLoss *
          Kakeya.realRpowENN delta innerLoss := by
    unfold proposition63CanonicalReentryWeight
    rw [← realRpowENN_add deltaPos]
    rw [← realRpowENN_add deltaPos]
    rw [← realRpowENN_add deltaPos]
    congr 1
    dsimp only [gap]
    ring
  calc
    ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          ((8 : ENNReal) * proposition63OneScaleLogEnvelope delta ^
            (levelCount + 2) *
            ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2)) *
          Kakeya.realRpowENN delta outputLoss =
        (fixed * proposition63OneScaleLogEnvelope delta ^
          (levelCount + 2)) *
          (Kakeya.realRpowENN delta 2 *
            Kakeya.realRpowENN delta outputLoss) := by
      dsimp only [fixed, geometry]
      ring
    _ ≤ Kakeya.realRpowENN delta (-gap) *
          (Kakeya.realRpowENN delta 2 *
            Kakeya.realRpowENN delta outputLoss) := by gcongr
    _ = proposition63CanonicalReentryWeight delta weightLoss *
          Kakeya.realRpowENN delta innerLoss := powerIdentity

/-- Specialize the family-free density-lift receipt to an actual canonical
current-shading re-entry. -/
theorem Proposition63CurrentShadingReentryData.densityLift_of_absorption
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      weightLoss innerLoss outputLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent levelCount : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (absorption : Proposition63ReentryDensityLiftAbsorptionData
      weightLoss innerLoss outputLoss levelCount)
    (hdelta : delta ≤ absorption.delta₀)
    (hweight : data.normalizationWeight =
      proposition63CanonicalReentryWeight delta weightLoss)
    (hweightUpper : data.weightUpper =
      (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2)
    (hlevelCount : data.levelCount = levelCount) :
    ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
        (data.regularized.regularizationLoss * data.weightUpper) *
        Kakeya.realRpowENN delta outputLoss ≤
      data.normalizationWeight * Kakeya.realRpowENN delta innerLoss := by
  calc
    _ ≤ ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (((8 : ENNReal) * proposition63OneScaleLogEnvelope delta ^
            (levelCount + 2)) *
            ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2)) *
          Kakeya.realRpowENN delta outputLoss := by
      gcongr
      · exact
          (data.regularizationLoss_le_oneScaleEnvelope hlevelCount).trans
            (proposition63OneScaleReentryRegularizationEnvelope_le_logEnvelope
              initialNormalized (hdelta.trans absorption.delta₀_le_tiny))
      · exact hweightUpper.le
    _ ≤ proposition63CanonicalReentryWeight delta weightLoss *
          Kakeya.realRpowENN delta innerLoss :=
      absorption.absorb data.reentry_extremal.delta_pos hdelta
    _ = data.normalizationWeight * Kakeya.realRpowENN delta innerLoss := by
      rw [hweight]

/-- Split the additive `1 + left⁻¹ * right` mass loss into two equal
half-budgets. -/
theorem proposition63Lemma43MassLoss_slack_of_two_bounds
    {left right outputPower inputPower : ENNReal}
    (leftPos : 0 < left) (leftTop : left ≠ ⊤)
    (oneBound : 2 * outputPower ≤ inputPower)
    (ratioBound : 2 * right * outputPower ≤ left * inputPower) :
    proposition63Lemma43MassLoss left right * outputPower ≤ inputPower := by
  apply (ENNReal.mul_le_mul_iff_right
    (show (2 : ENNReal) ≠ 0 by norm_num)
    (show (2 : ENNReal) ≠ ⊤ by norm_num)).mp
  calc
    2 * (proposition63Lemma43MassLoss left right * outputPower) =
        2 * outputPower + left⁻¹ * (2 * right * outputPower) := by
      unfold proposition63Lemma43MassLoss
      ring
    _ ≤ inputPower + left⁻¹ * (left * inputPower) := by
      exact add_le_add oneBound (mul_le_mul_left' ratioBound _)
    _ = 2 * inputPower := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel leftPos.ne' leftTop]
      ring

/-- The orientation refinement in the terminal-balanced target step is
dominated by the standard WZ1 one-scale cap count. -/
theorem proposition63_target_orientation_cap_le_power
    {delta targetLoss robustExponent incidence variationScale : ℝ}
    (targetScale : WZ2PaperRequestedScale delta)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (htargetLoss : 0 < targetLoss)
    (hrobustExponent : 0 < robustExponent)
    (robustScale : ℝ)
    (hrobustEq : robustScale = Real.rpow delta robustExponent)
    (hincidenceNonnegative : 0 ≤ incidence)
    (hincidence : incidence ≤ targetScale.1)
    (htargetUpper : targetScale.1 ≤ Real.rpow delta targetLoss)
    (hseparation : 16 * targetScale.1 ≤ robustScale)
    (hvariation : variationScale = targetScale.1) :
    (wz1OrientationCapCount
        (10 * (incidence + targetScale.1 / 2) /
          (robustScale - targetScale.1)) variationScale : ENNReal) ≤
      (100000000 : ENNReal) *
        Kakeya.realRpowENN delta (-3 * robustExponent) := by
  subst variationScale
  have targetPos : 0 < targetScale.1 := hdelta.trans_le targetScale.2.1
  have robustPos : 0 < robustScale := by
    rw [hrobustEq]
    exact Real.rpow_pos_of_pos hdelta _
  have robustOne : robustScale ≤ 1 := by
    rw [hrobustEq]
    exact Real.rpow_le_one hdelta.le hdeltaOne.le hrobustExponent.le
  have eightStrict : 8 * targetScale.1 < robustScale := by
    nlinarith
  have halfGap : robustScale - 8 * targetScale.1 ≥ robustScale / 2 := by
    nlinarith
  have radiusLe :
      10 * (incidence + targetScale.1 / 2) /
          (robustScale - targetScale.1) ≤
        10 * (5 * targetScale.1) /
          (robustScale - 8 * targetScale.1) := by
    have smallDenominatorPos :
        0 < robustScale - 8 * targetScale.1 := by linarith
    have largeDenominator :
        robustScale - 8 * targetScale.1 ≤
          robustScale - targetScale.1 := by linarith
    have numeratorNonnegative : 0 ≤
        10 * (incidence + targetScale.1 / 2) := by
      exact mul_nonneg (by norm_num)
        (add_nonneg hincidenceNonnegative (by positivity))
    have numeratorLe :
        10 * (incidence + targetScale.1 / 2) ≤
          10 * (5 * targetScale.1) := by
      nlinarith
    exact div_le_div₀ (by positivity) numeratorLe
      smallDenominatorPos largeDenominator
  have capMono :
      wz1OrientationCapCount
          (10 * (incidence + targetScale.1 / 2) /
            (robustScale - targetScale.1)) targetScale.1 ≤
        wz1OrientationCapCount
          (10 * (5 * targetScale.1) /
            (robustScale - 8 * targetScale.1)) targetScale.1 := by
    unfold wz1OrientationCapCount
    gcongr
  have sqrtThree : Real.sqrt 3 < 7 / 4 := by
    have squareBound : (3 : ℝ) < (7 / 4 : ℝ) ^ 2 := by norm_num
    exact (Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 3)
      (by norm_num : (0 : ℝ) ≤ 7 / 4)).2 squareBound
  let x : ℝ := 2 * Real.sqrt 3 *
    (10 * (5 * targetScale.1) /
      (robustScale - 8 * targetScale.1)) / targetScale.1
  have xNonnegative : 0 ≤ x := by
    dsimp only [x]
    positivity
  have xLe : x ≤ 350 / robustScale := by
    have ratioLe :
        10 * (5 * targetScale.1) /
            (robustScale - 8 * targetScale.1) ≤
          100 * targetScale.1 / robustScale := by
      calc
        10 * (5 * targetScale.1) /
              (robustScale - 8 * targetScale.1) ≤
            10 * (5 * targetScale.1) / (robustScale / 2) := by gcongr
        _ = 100 * targetScale.1 / robustScale := by
          field_simp [robustPos.ne']
          ring
    calc
      x ≤ 2 * Real.sqrt 3 *
          (100 * targetScale.1 / robustScale) / targetScale.1 := by
        dsimp only [x]
        gcongr
      _ = 200 * Real.sqrt 3 / robustScale := by
        field_simp [targetPos.ne', robustPos.ne']
        ring
      _ ≤ 350 / robustScale := by
        apply div_le_div_of_nonneg_right _ robustPos.le
        nlinarith
  let n := Nat.ceil x
  have ceilLe : (n : ℝ) ≤ x + 1 := by
    dsimp only [n]
    exact (Nat.ceil_lt_add_one xNonnegative).le
  have twoLeTwoDiv : (2 : ℝ) ≤ 2 / robustScale := by
    calc
      (2 : ℝ) = 2 / 1 := by norm_num
      _ ≤ 2 / robustScale := by gcongr
  have nPlusOneLe : (n : ℝ) + 1 ≤ 352 / robustScale := by
    calc
      (n : ℝ) + 1 ≤ x + 2 := by linarith
      _ ≤ 350 / robustScale + 2 / robustScale := by
        exact add_le_add xLe twoLeTwoDiv
      _ = 352 / robustScale := by ring
  have realCapBound :
      (2 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 3 ≤
        100000000 * Real.rpow delta (-3 * robustExponent) := by
    have castSucc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
    have robustCube : robustScale ^ 3 =
        Real.rpow delta (3 * robustExponent) := by
      rw [hrobustEq]
      calc
        (Real.rpow delta robustExponent) ^ 3 =
            Real.rpow (Real.rpow delta robustExponent) (3 : ℝ) :=
          (Real.rpow_natCast _ 3).symm
        _ = Real.rpow delta (robustExponent * 3) :=
          (Real.rpow_mul hdelta.le _ _).symm
        _ = Real.rpow delta (3 * robustExponent) := by ring_nf
    have inverseCube : robustScale⁻¹ ^ 3 =
        Real.rpow delta (-3 * robustExponent) := by
      rw [inv_pow, robustCube]
      rw [show -3 * robustExponent = -(3 * robustExponent) by ring]
      exact (Real.rpow_neg hdelta.le _).symm
    calc
      (2 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 3 =
          2 * ((n : ℝ) + 1) ^ 3 := by rw [castSucc]
      _ ≤ 2 * (352 / robustScale) ^ 3 := by gcongr
      _ = (2 * 352 ^ 3) * robustScale⁻¹ ^ 3 := by
        field_simp [robustPos.ne']
      _ = (2 * 352 ^ 3) *
          Real.rpow delta (-3 * robustExponent) := by rw [inverseCube]
      _ ≤ 100000000 * Real.rpow delta (-3 * robustExponent) := by
        exact mul_le_mul_of_nonneg_right (by norm_num)
          (Real.rpow_nonneg hdelta.le _)
  have capBound :
      (wz1OrientationCapCount
          (10 * (5 * targetScale.1) /
            (robustScale - 8 * targetScale.1)) targetScale.1 : ENNReal) ≤
        ENNReal.ofReal
          (100000000 * Real.rpow delta (-3 * robustExponent)) := by
    have capEq :
        wz1OrientationCapCount
          (10 * (5 * targetScale.1) /
            (robustScale - 8 * targetScale.1)) targetScale.1 =
          2 * (n + 1) ^ 3 := by
      unfold wz1OrientationCapCount
      dsimp only [n, x]
    rw [capEq]
    exact_mod_cast ENNReal.ofReal_mono realCapBound
  have capMonoENN :
      (wz1OrientationCapCount
          (10 * (incidence + targetScale.1 / 2) /
            (robustScale - targetScale.1)) targetScale.1 : ENNReal) ≤
        (wz1OrientationCapCount
          (10 * (5 * targetScale.1) /
            (robustScale - 8 * targetScale.1)) targetScale.1 : ENNReal) := by
    exact_mod_cast capMono
  exact capMonoENN.trans <| by
    calc
      (wz1OrientationCapCount
          (10 * (5 * targetScale.1) /
            (robustScale - 8 * targetScale.1)) targetScale.1 : ENNReal) ≤
          ENNReal.ofReal
            (100000000 * Real.rpow delta (-3 * robustExponent)) := by
        exact capBound
      _ = (100000000 : ENNReal) *
          Kakeya.realRpowENN delta (-3 * robustExponent) := by
        rw [show (100000000 : ENNReal) =
            ENNReal.ofReal (100000000 : ℝ) by norm_num]
        change ENNReal.ofReal
            (100000000 * Real.rpow delta (-3 * robustExponent)) =
          ENNReal.ofReal (100000000 : ℝ) *
            ENNReal.ofReal (Real.rpow delta (-3 * robustExponent))
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 100000000 by norm_num)]

/-- A pre-runtime receipt for restoring extremality after one target-rich
variation on the target normalization family. -/
structure Proposition63TargetStepAbsorptionData
    (sourceLoss targetLoss robustExponent outputLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  source_lt_output : sourceLoss < outputLoss
  absorb :
    ∀ {delta incidence variationScale robustScale : ℝ}
      (targetScale : WZ2PaperRequestedScale delta),
      0 < delta → delta ≤ delta₀ →
      robustScale = Real.rpow delta robustExponent →
      0 ≤ incidence → incidence ≤ targetScale.1 →
      Real.rpow delta (1 - targetLoss) ≤ targetScale.1 →
      targetScale.1 ≤ Real.rpow delta targetLoss →
      16 * targetScale.1 ≤ robustScale →
      variationScale = targetScale.1 →
      proposition63Lemma43MassLoss
          (wz2PaperPureRefinementFraction delta 61 *
            Kakeya.realRpowENN targetScale.1 (2 * targetLoss))
          (27 * (2 *
            (wz1OrientationCapCount
              (10 * (incidence + targetScale.1 / 2) /
                (robustScale - targetScale.1)) variationScale : ENNReal))) *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta sourceLoss

/-- Choose the target-step threshold from the exact spatial and robust power
losses. -/
theorem proposition63_target_step_absorption
    (sourceLoss targetLoss robustExponent outputLoss : ℝ)
    (htargetLoss : 0 < targetLoss)
    (htargetLossLeOne : targetLoss ≤ 1)
    (hrobustExponent : 0 < robustExponent)
    (hgap : 0 < outputLoss - sourceLoss - 3 * robustExponent -
      (1 - targetLoss) * (2 * targetLoss)) :
    Nonempty (Proposition63TargetStepAbsorptionData
      sourceLoss targetLoss robustExponent outputLoss) := by
  let gap : ℝ := outputLoss - sourceLoss - 3 * robustExponent -
    (1 - targetLoss) * (2 * targetLoss)
  have gapPos : 0 < gap := by simpa [gap] using hgap
  have outputGapPos : 0 < outputLoss - sourceLoss := by
    have costsNonnegative :
        0 ≤ 3 * robustExponent +
          (1 - targetLoss) * (2 * targetLoss) := by
      positivity
    linarith
  let fixed : ENNReal :=
    (2 : ENNReal) * (27 * 2 * 100000000)
  have fixedTop : fixed ≠ ⊤ := by
    dsimp only [fixed]
    norm_num
  rcases exists_delta_log_absorbed_ennreal fixed fixedTop gapPos
      (show 0 < (61 : ℕ) by norm_num) with
    ⟨logDelta, logDeltaPos, logDeltaOne, logAbsorb⟩
  rcases exists_delta_realRpowENN_bound (2 : ENNReal) (by norm_num)
      outputGapPos with
    ⟨oneDelta, oneDeltaPos, oneDeltaOne, oneAbsorb⟩
  let delta₀ : ℝ := min logDelta (min oneDelta (Real.exp (-1)))
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := by dsimp only [delta₀]; positivity
    delta₀_le_one := (min_le_left _ _).trans logDeltaOne
    source_lt_output := by linarith
    absorb := ?_
  }⟩
  intro delta incidence variationScale robustScale targetScale deltaPos
    deltaLe robustEq incidenceNonneg incidenceLe targetLower targetUpper
      separation variationEq
  have deltaLeLog : delta ≤ logDelta := deltaLe.trans (min_le_left _ _)
  have deltaLeOneThreshold : delta ≤ oneDelta :=
    deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeOne : delta ≤ 1 := deltaLeLog.trans logDeltaOne
  have deltaLtOne : delta < 1 := by
    exact deltaLe.trans_lt <|
      (min_le_right _ _).trans_lt <|
        (min_le_right _ _).trans_lt
          (Real.exp_lt_one_iff.mpr (by norm_num))
  have capBound := proposition63_target_orientation_cap_le_power
    targetScale deltaPos deltaLtOne htargetLoss hrobustExponent robustScale
    robustEq incidenceNonneg incidenceLe targetUpper separation variationEq
  let logTerm : ENNReal := ENNReal.ofReal (Real.log (1 / delta))
  let logEnvelope : ENNReal :=
    ENNReal.ofReal (1 + Real.log delta⁻¹)
  have logTermPos : 0 < logTerm := by
    dsimp only [logTerm]
    exact ENNReal.ofReal_pos.mpr <|
      Real.log_pos (one_lt_one_div deltaPos deltaLtOne)
  have logTermLe : logTerm ≤ logEnvelope := by
    dsimp only [logTerm, logEnvelope]
    apply ENNReal.ofReal_mono
    rw [show 1 / delta = delta⁻¹ by simp]
    linarith
  have logarithmicAbsorption :
      fixed * logTerm ^ 61 ≤ Kakeya.realRpowENN delta (-gap) := by
    calc
      fixed * logTerm ^ 61 ≤ fixed * logEnvelope ^ 61 := by gcongr
      _ ≤ Kakeya.realRpowENN delta (-gap) := by
        simpa only [logEnvelope] using
          logAbsorb delta deltaPos deltaLeLog
  have targetPowerLower :
      Kakeya.realRpowENN delta
          ((1 - targetLoss) * (2 * targetLoss)) ≤
        Kakeya.realRpowENN targetScale.1 (2 * targetLoss) := by
    apply ENNReal.ofReal_mono
    calc
      Real.rpow delta ((1 - targetLoss) * (2 * targetLoss)) =
          Real.rpow (Real.rpow delta (1 - targetLoss))
            (2 * targetLoss) :=
        Real.rpow_mul deltaPos.le _ _
      _ ≤ Real.rpow targetScale.1 (2 * targetLoss) :=
        Real.rpow_le_rpow (Real.rpow_nonneg deltaPos.le _) targetLower
          (by positivity)
  let left : ENNReal :=
    wz2PaperPureRefinementFraction delta 61 *
      Kakeya.realRpowENN targetScale.1 (2 * targetLoss)
  let right : ENNReal :=
    27 * (2 *
      (wz1OrientationCapCount
        (10 * (incidence + targetScale.1 / 2) /
          (robustScale - targetScale.1)) variationScale : ENNReal))
  have leftPos : 0 < left := by
    dsimp only [left]
    apply ENNReal.mul_pos
    · unfold wz2PaperPureRefinementFraction
      exact (ENNReal.pow_pos
        (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top) 61).ne'
    · exact (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos (deltaPos.trans_le targetScale.2.1) _)).ne'
  have leftTop : left ≠ ⊤ := by
    dsimp only [left]
    exact ENNReal.mul_ne_top (by
      unfold wz2PaperPureRefinementFraction
      apply ENNReal.pow_ne_top
      apply ENNReal.inv_ne_top.mpr
      exact (ENNReal.ofReal_pos.mpr <| Real.log_pos <|
        one_lt_one_div deltaPos deltaLtOne).ne')
      (by simp [Kakeya.realRpowENN])
  have oneBound :
      2 * Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta sourceLoss := by
    have constantBound := oneAbsorb delta deltaPos deltaLeOneThreshold
    calc
      2 * Kakeya.realRpowENN delta outputLoss ≤
          Kakeya.realRpowENN delta (-(outputLoss - sourceLoss)) *
            Kakeya.realRpowENN delta outputLoss := by gcongr
      _ = Kakeya.realRpowENN delta sourceLoss := by
        rw [← realRpowENN_add deltaPos]
        congr 1
        ring
  have ratioMultiplied :
      (2 * right * Kakeya.realRpowENN delta outputLoss) * logTerm ^ 61 ≤
        Kakeya.realRpowENN targetScale.1 (2 * targetLoss) *
          Kakeya.realRpowENN delta sourceLoss := by
    have exponentIdentity :
        Kakeya.realRpowENN delta (-gap) *
            (Kakeya.realRpowENN delta (-3 * robustExponent) *
              Kakeya.realRpowENN delta outputLoss) =
          Kakeya.realRpowENN delta
            ((1 - targetLoss) * (2 * targetLoss)) *
            Kakeya.realRpowENN delta sourceLoss := by
      rw [← realRpowENN_add deltaPos]
      rw [← realRpowENN_add deltaPos]
      rw [← realRpowENN_add deltaPos]
      congr 1
      dsimp only [gap]
      ring
    calc
      (2 * right * Kakeya.realRpowENN delta outputLoss) * logTerm ^ 61 ≤
          ((2 * 27 * 2 : ENNReal) *
              ((100000000 : ENNReal) *
                Kakeya.realRpowENN delta (-3 * robustExponent)) *
            Kakeya.realRpowENN delta outputLoss) * logTerm ^ 61 := by
        dsimp only [right]
        have lifted := mul_le_mul_right'
          (mul_le_mul_right'
            (mul_le_mul_left' capBound (2 * 27 * 2))
            (Kakeya.realRpowENN delta outputLoss))
          (logTerm ^ 61)
        simpa only [mul_assoc] using lifted
      _ = (fixed * logTerm ^ 61) *
          (Kakeya.realRpowENN delta (-3 * robustExponent) *
            Kakeya.realRpowENN delta outputLoss) := by
        dsimp only [fixed]
        ring
      _ ≤ Kakeya.realRpowENN delta (-gap) *
          (Kakeya.realRpowENN delta (-3 * robustExponent) *
            Kakeya.realRpowENN delta outputLoss) := by gcongr
      _ = Kakeya.realRpowENN delta
            ((1 - targetLoss) * (2 * targetLoss)) *
          Kakeya.realRpowENN delta sourceLoss := exponentIdentity
      _ ≤ Kakeya.realRpowENN targetScale.1 (2 * targetLoss) *
          Kakeya.realRpowENN delta sourceLoss := by gcongr
  have ratioBound :
      2 * right * Kakeya.realRpowENN delta outputLoss ≤
        left * Kakeya.realRpowENN delta sourceLoss := by
    have rightRewrite :
        left * Kakeya.realRpowENN delta sourceLoss =
          (logTerm ^ 61)⁻¹ *
            (Kakeya.realRpowENN targetScale.1 (2 * targetLoss) *
              Kakeya.realRpowENN delta sourceLoss) := by
      dsimp only [left, logTerm]
      rw [wz2PaperPureRefinementFraction, ← ENNReal.inv_pow]
      ring
    rw [rightRewrite]
    rw [← ENNReal.div_eq_inv_mul]
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (pow_ne_zero 61 logTermPos.ne'))
      (Or.inl (ENNReal.pow_ne_top (by simp [logTerm])))).mpr
    simpa [mul_comm, mul_left_comm, mul_assoc] using ratioMultiplied
  exact proposition63Lemma43MassLoss_slack_of_two_bounds
    leftPos leftTop oneBound ratioBound

/-- At an exact power scale, the quotient-scale and ambient-scale powers
collapse to a single power of the fine scale. -/
theorem proposition63_ratio_power_mul_power_at_power_scale
    {delta robustExponent firstExponent secondExponent : ℝ}
    (hdelta : 0 < delta) :
    Kakeya.realRpowENN
          (delta / Real.rpow delta robustExponent) firstExponent *
        Kakeya.realRpowENN
          (Real.rpow delta robustExponent) secondExponent =
      Kakeya.realRpowENN delta
        (firstExponent + robustExponent *
          (secondExponent - firstExponent)) := by
  have robustPos : 0 < Real.rpow delta robustExponent :=
    Real.rpow_pos_of_pos hdelta _
  have split :
      Kakeya.realRpowENN (Real.rpow delta robustExponent) firstExponent *
          Kakeya.realRpowENN (Real.rpow delta robustExponent)
            (secondExponent - firstExponent) =
        Kakeya.realRpowENN (Real.rpow delta robustExponent) secondExponent := by
    rw [← realRpowENN_add robustPos]
    congr 1
    ring
  have nested :
      Kakeya.realRpowENN (Real.rpow delta robustExponent)
          (secondExponent - firstExponent) =
        Kakeya.realRpowENN delta
          (robustExponent * (secondExponent - firstExponent)) := by
    apply congrArg ENNReal.ofReal
    exact (Real.rpow_mul hdelta.le _ _).symm
  calc
    Kakeya.realRpowENN
          (delta / Real.rpow delta robustExponent) firstExponent *
        Kakeya.realRpowENN
          (Real.rpow delta robustExponent) secondExponent =
      (Kakeya.realRpowENN
          (delta / Real.rpow delta robustExponent) firstExponent *
        Kakeya.realRpowENN
          (Real.rpow delta robustExponent) firstExponent) *
        Kakeya.realRpowENN
          (Real.rpow delta robustExponent)
            (secondExponent - firstExponent) := by
      rw [← split]
      ring
    _ = Kakeya.realRpowENN delta firstExponent *
        Kakeya.realRpowENN
          (Real.rpow delta robustExponent)
            (secondExponent - firstExponent) := by
      have cancel :
          Kakeya.realRpowENN
                (delta / Real.rpow delta robustExponent) firstExponent *
              Kakeya.realRpowENN
                (Real.rpow delta robustExponent) firstExponent =
            Kakeya.realRpowENN delta firstExponent := by
        rw [← Kakeya.Assouad.realRpowENN_mul
          (div_pos hdelta robustPos) robustPos]
        congr 1
        field_simp [robustPos.ne']
      rw [cancel]
    _ = Kakeya.realRpowENN delta firstExponent *
        Kakeya.realRpowENN delta
          (robustExponent * (secondExponent - firstExponent)) := by
      rw [nested]
    _ = Kakeya.realRpowENN delta
        (firstExponent + robustExponent *
          (secondExponent - firstExponent)) :=
      (realRpowENN_add hdelta _ _).symm

/-- A family-free small-scale receipt for the terminal scalar in one scaled
two-rich step. -/
structure Proposition63ScaledTwoRichTerminalScalarAbsorptionData
    (sigma robustExponent outerLoss targetNormalizationLoss weightLoss : ℝ)
    (factor levelCount : ℕ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_tiny : delta₀ ≤ 1 / 100000
  absorb :
    ∀ {delta robustScale terminalLoss : ℝ},
      0 < delta → delta ≤ delta₀ →
      robustScale = Real.rpow delta robustExponent →
      0 < terminalLoss → terminalLoss ≤ outerLoss →
      ((((factor : ENNReal) * stickyCoarseCloseCount) *
          Kakeya.realRpowENN (delta / robustScale)
            (2 - sigma - terminalLoss) *
          ((8 * proposition63OneScaleLogEnvelope delta ^
                (levelCount + 2)) *
            ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2))) *
          ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
          Kakeya.realRpowENN robustScale (2 - outerLoss)) *
          (proposition63OneScaleLogEnvelope delta ^ 10 *
            Kakeya.realRpowENN delta
              (sigma - targetNormalizationLoss)) ≤
        proposition63CanonicalReentryWeight delta weightLoss *
          (wz2PaperPureRefinementFraction delta 61 *
            Kakeya.realRpowENN delta
              (targetNormalizationLoss + 2))

/-- Compatibility name for the factor-two plane-map receipt. -/
abbrev Proposition63TwoRichTerminalScalarAbsorptionData
    (sigma robustExponent outerLoss targetNormalizationLoss weightLoss : ℝ)
    (levelCount : ℕ) :=
  Proposition63ScaledTwoRichTerminalScalarAbsorptionData
    sigma robustExponent outerLoss targetNormalizationLoss weightLoss 2
    levelCount

/-- Choose the terminal-scalar threshold before the runtime family and the
two rich calls.  The strict gap is exactly the robust-scale power left after
the two normalization losses and the canonical external weight are paid. -/
theorem proposition63_scaled_two_rich_terminal_scalar_absorption
    (sigma robustExponent outerLoss targetNormalizationLoss weightLoss : ℝ)
    (factor levelCount : ℕ)
    (_hrobustNonneg : 0 ≤ robustExponent)
    (hrobustLeOne : robustExponent ≤ 1)
    (hgap : 0 < robustExponent * sigma - outerLoss -
      2 * targetNormalizationLoss - weightLoss) :
    Nonempty (Proposition63ScaledTwoRichTerminalScalarAbsorptionData
      sigma robustExponent outerLoss targetNormalizationLoss weightLoss
      factor levelCount) := by
  let gap : ℝ := robustExponent * sigma - outerLoss -
    2 * targetNormalizationLoss - weightLoss
  have gapPos : 0 < gap := by simpa [gap] using hgap
  let fixed : ENNReal :=
    (((factor : ENNReal) * stickyCoarseCloseCount) * 8 *
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1)) *
      ((12 : ENNReal) * ENNReal.ofReal Real.pi)
  have fixedTop : fixed ≠ ⊤ := by
    dsimp only [fixed]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top ENNReal.coe_ne_top
            (by norm_num [stickyCoarseCloseCount])) (by norm_num))
        (ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top))
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
  let logExponent : ℕ := levelCount + 73
  have logExponentPos : 0 < logExponent := by
    dsimp only [logExponent]
    omega
  rcases exists_delta_C_pow_log_absorbed_ennreal
      fixed fixedTop proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg gapPos logExponentPos with
    ⟨logDelta, logDeltaPos, logDeltaOne, logAbsorb⟩
  let delta₀ : ℝ := min logDelta (min (1 / 100000) (Real.exp (-1)))
  have delta₀Pos : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := delta₀Pos
    delta₀_le_one := (min_le_left _ _).trans logDeltaOne
    delta₀_le_tiny :=
      (min_le_right _ _).trans (min_le_left _ _)
    absorb := ?_
  }⟩
  intro delta robustScale terminalLoss deltaPos deltaLe robustEq
    terminalLossPos terminalLossLe
  subst robustScale
  have deltaLeLog : delta ≤ logDelta :=
    deltaLe.trans (min_le_left _ _)
  have deltaLeOne : delta ≤ 1 :=
    deltaLeLog.trans logDeltaOne
  have deltaLtOne : delta < 1 := by
    exact deltaLe.trans_lt <|
      (min_le_right _ _).trans_lt <|
        (min_le_right _ _).trans_lt
          (Real.exp_lt_one_iff.mpr (by norm_num))
  let logTerm : ENNReal := ENNReal.ofReal (Real.log (1 / delta))
  have logTermLe : logTerm ≤ proposition63OneScaleLogEnvelope delta := by
    unfold proposition63OneScaleLogEnvelope
    dsimp only [logTerm]
    apply ENNReal.ofReal_mono
    have logNonnegative : 0 ≤ Real.log delta⁻¹ :=
      Real.log_nonneg ((one_le_inv₀ deltaPos).mpr deltaLeOne)
    rw [show 1 / delta = delta⁻¹ by simp]
    have coefficientOne : 1 ≤ proposition63OneScaleLogCoefficient :=
      (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
    calc
      Real.log delta⁻¹ ≤ 1 + Real.log delta⁻¹ := by linarith
      _ ≤ proposition63OneScaleLogCoefficient *
          (1 + Real.log delta⁻¹) := by
        nlinarith [mul_nonneg
          (sub_nonneg.mpr coefficientOne)
          (show 0 ≤ 1 + Real.log delta⁻¹ by linarith)]
  have logsCombined :
      proposition63OneScaleLogEnvelope delta ^ (levelCount + 12) *
          logTerm ^ 61 ≤
        proposition63OneScaleLogEnvelope delta ^ logExponent := by
    calc
      proposition63OneScaleLogEnvelope delta ^ (levelCount + 12) *
            logTerm ^ 61 ≤
          proposition63OneScaleLogEnvelope delta ^ (levelCount + 12) *
            proposition63OneScaleLogEnvelope delta ^ 61 := by gcongr
      _ = proposition63OneScaleLogEnvelope delta ^ logExponent := by
        rw [← pow_add]
  have logarithmicAbsorption :
      fixed * proposition63OneScaleLogEnvelope delta ^ logExponent ≤
        Kakeya.realRpowENN delta (-gap) := by
    simpa [proposition63OneScaleLogEnvelope] using
      logAbsorb delta deltaPos deltaLeLog
  let firstExponent : ℝ := 2 - sigma - terminalLoss
  let secondExponent : ℝ := 2 - outerLoss
  let actualExponent : ℝ :=
    firstExponent + robustExponent * (secondExponent - firstExponent) +
      2 + (sigma - targetNormalizationLoss)
  let rightExponent : ℝ := weightLoss + targetNormalizationLoss + 4
  have exponentBound : rightExponent + gap ≤ actualExponent := by
    have productNonnegative :
        0 ≤ (1 - robustExponent) * (outerLoss - terminalLoss) :=
      mul_nonneg (sub_nonneg.mpr hrobustLeOne)
        (sub_nonneg.mpr terminalLossLe)
    dsimp only [actualExponent, rightExponent, firstExponent, secondExponent, gap]
    nlinarith
  have actualPowerLe :
      Kakeya.realRpowENN delta actualExponent ≤
        Kakeya.realRpowENN delta (rightExponent + gap) := by
    exact ENNReal.ofReal_mono <|
      Real.rpow_le_rpow_of_exponent_ge deltaPos deltaLeOne exponentBound
  have scalePowers :
      Kakeya.realRpowENN
            (delta / Real.rpow delta robustExponent) firstExponent *
          Kakeya.realRpowENN
            (Real.rpow delta robustExponent) secondExponent *
          Kakeya.realRpowENN delta 2 *
          Kakeya.realRpowENN delta
            (sigma - targetNormalizationLoss) =
        Kakeya.realRpowENN delta actualExponent := by
    rw [proposition63_ratio_power_mul_power_at_power_scale deltaPos]
    rw [← realRpowENN_add deltaPos]
    rw [← realRpowENN_add deltaPos]
  have multiplied :
      (fixed * proposition63OneScaleLogEnvelope delta ^
          (levelCount + 12) *
        Kakeya.realRpowENN delta actualExponent) * logTerm ^ 61 ≤
        Kakeya.realRpowENN delta rightExponent := by
    calc
      (fixed * proposition63OneScaleLogEnvelope delta ^
            (levelCount + 12) *
          Kakeya.realRpowENN delta actualExponent) * logTerm ^ 61 =
          (fixed *
            (proposition63OneScaleLogEnvelope delta ^
              (levelCount + 12) * logTerm ^ 61)) *
            Kakeya.realRpowENN delta actualExponent := by ring
      _ ≤ (fixed * proposition63OneScaleLogEnvelope delta ^ logExponent) *
            Kakeya.realRpowENN delta actualExponent := by gcongr
      _ ≤ Kakeya.realRpowENN delta (-gap) *
            Kakeya.realRpowENN delta actualExponent := by gcongr
      _ ≤ Kakeya.realRpowENN delta (-gap) *
            Kakeya.realRpowENN delta (rightExponent + gap) := by gcongr
      _ = Kakeya.realRpowENN delta rightExponent := by
        rw [← realRpowENN_add deltaPos]
        congr 1
        ring
  have leftRewrite :
      ((((factor : ENNReal) * stickyCoarseCloseCount) *
          Kakeya.realRpowENN
            (delta / Real.rpow delta robustExponent)
              (2 - sigma - terminalLoss) *
          ((8 * proposition63OneScaleLogEnvelope delta ^
                (levelCount + 2)) *
            ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2))) *
          ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
          Kakeya.realRpowENN (Real.rpow delta robustExponent)
            (2 - outerLoss)) *
          (proposition63OneScaleLogEnvelope delta ^ 10 *
            Kakeya.realRpowENN delta
              (sigma - targetNormalizationLoss)) =
        fixed * proposition63OneScaleLogEnvelope delta ^
            (levelCount + 12) *
          Kakeya.realRpowENN delta actualExponent := by
    rw [show 2 - sigma - terminalLoss = firstExponent by rfl]
    rw [show 2 - outerLoss = secondExponent by rfl]
    rw [← scalePowers]
    dsimp only [fixed]
    rw [show proposition63OneScaleLogEnvelope delta ^ (levelCount + 12) =
        proposition63OneScaleLogEnvelope delta ^ (levelCount + 2) *
          proposition63OneScaleLogEnvelope delta ^ 10 by
      rw [← pow_add]
      ]
    ring
  rw [leftRewrite]
  rw [wz2PaperPureRefinementFraction, ← ENNReal.inv_pow]
  have logTermPos : 0 < logTerm := by
    apply ENNReal.ofReal_pos.mpr
    exact Real.log_pos (one_lt_one_div deltaPos deltaLtOne)
  have logTermTop : logTerm ≠ ⊤ := by simp [logTerm]
  have logPowerPos : 0 < logTerm ^ 61 := by positivity
  have logPowerTop : logTerm ^ 61 ≠ ⊤ :=
    ENNReal.pow_ne_top logTermTop
  have rightPower :
      proposition63CanonicalReentryWeight delta weightLoss *
          Kakeya.realRpowENN delta (targetNormalizationLoss + 2) =
        Kakeya.realRpowENN delta rightExponent := by
    unfold proposition63CanonicalReentryWeight
    rw [← realRpowENN_add deltaPos]
    congr 1
    dsimp only [rightExponent]
    ring
  rw [show ENNReal.ofReal (Real.log (1 / delta)) = logTerm by rfl]
  change fixed * proposition63OneScaleLogEnvelope delta ^
      (levelCount + 12) * Kakeya.realRpowENN delta actualExponent ≤
    proposition63CanonicalReentryWeight delta weightLoss *
      ((logTerm ^ 61)⁻¹ *
        Kakeya.realRpowENN delta (targetNormalizationLoss + 2))
  rw [show proposition63CanonicalReentryWeight delta weightLoss *
      ((logTerm ^ 61)⁻¹ *
        Kakeya.realRpowENN delta (targetNormalizationLoss + 2)) =
      (proposition63CanonicalReentryWeight delta weightLoss *
        Kakeya.realRpowENN delta (targetNormalizationLoss + 2)) *
          (logTerm ^ 61)⁻¹ by ring]
  rw [rightPower]
  change _ ≤ Kakeya.realRpowENN delta rightExponent / logTerm ^ 61
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl logPowerPos.ne') (Or.inl logPowerTop)).mpr
  simpa [mul_comm, mul_left_comm, mul_assoc] using multiplied

/-- Choose the historical factor-two terminal scalar receipt. -/
theorem proposition63_two_rich_terminal_scalar_absorption
    (sigma robustExponent outerLoss targetNormalizationLoss weightLoss : ℝ)
    (levelCount : ℕ)
    (hrobustNonneg : 0 ≤ robustExponent)
    (hrobustLeOne : robustExponent ≤ 1)
    (hgap : 0 < robustExponent * sigma - outerLoss -
      2 * targetNormalizationLoss - weightLoss) :
    Nonempty (Proposition63TwoRichTerminalScalarAbsorptionData
      sigma robustExponent outerLoss targetNormalizationLoss weightLoss
      levelCount) :=
  proposition63_scaled_two_rich_terminal_scalar_absorption
    sigma robustExponent outerLoss targetNormalizationLoss weightLoss 2
    levelCount hrobustNonneg hrobustLeOne hgap

/-- The family-uniform scalar envelope implies the exact terminal scalar
needed by the two-rich cross-degree cancellation.  This is the boundary at
which all data-dependent log factors are replaced by their frozen bounds. -/
theorem proposition63_scaled_two_rich_terminal_scalar_of_uniform_envelope
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss weightLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent levelCount : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (hweight : targetReentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta weightLoss)
    (hweightUpper : targetReentry.weightUpper =
      (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2)
    (hlevelCount : targetReentry.levelCount = levelCount)
    (hdeltaTiny : delta ≤ 1 / 100000)
    (factor : ℕ)
    (huniform :
      ((((factor : ENNReal) * stickyCoarseCloseCount) *
          Kakeya.realRpowENN (delta / robustScale.1)
            (2 - sigma - outer.terminalLoss) *
          ((8 * proposition63OneScaleLogEnvelope delta ^
                (levelCount + 2)) *
            ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2))) *
          ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
          Kakeya.realRpowENN robustScale.1 (2 - outerLoss)) *
          (proposition63OneScaleLogEnvelope delta ^ 10 *
            Kakeya.realRpowENN delta
              (sigma - targetReentry.reentryNormalizationLoss)) ≤
        proposition63CanonicalReentryWeight delta weightLoss *
          (wz2PaperPureRefinementFraction delta 61 *
            Kakeya.realRpowENN delta
              (targetReentry.reentryNormalizationLoss + 2))) :
    ((((factor : ENNReal) * stickyCoarseCloseCount) *
        Kakeya.realRpowENN (delta / robustScale.1)
          (2 - sigma - outer.terminalLoss) *
        (targetReentry.regularized.regularizationLoss *
          targetReentry.weightUpper)) *
        ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
        Kakeya.realRpowENN robustScale.1 (2 - outerLoss)) *
        ((target.terminal.regularity : ENNReal) *
          Kakeya.realRpowENN delta
            (sigma - targetReentry.reentryNormalizationLoss)) ≤
      targetReentry.normalizationWeight *
        (wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            (targetReentry.reentryNormalizationLoss + 2)) := by
  calc
    _ ≤ ((((factor : ENNReal) * stickyCoarseCloseCount) *
          Kakeya.realRpowENN (delta / robustScale.1)
            (2 - sigma - outer.terminalLoss) *
          ((8 * proposition63OneScaleLogEnvelope delta ^
                (levelCount + 2)) *
            ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2))) *
          ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
          Kakeya.realRpowENN robustScale.1 (2 - outerLoss)) *
          (proposition63OneScaleLogEnvelope delta ^ 10 *
            Kakeya.realRpowENN delta
              (sigma - targetReentry.reentryNormalizationLoss)) := by
      gcongr
      · exact
          (targetReentry.regularizationLoss_le_oneScaleEnvelope hlevelCount).trans
            (proposition63OneScaleReentryRegularizationEnvelope_le_logEnvelope
              outerReentry.toNormalizationData hdeltaTiny)
      · exact hweightUpper.le
      · exact target.terminal_regularity_bound.trans <| by
          gcongr
          exact proposition63_logarithmicLoss_le_oneScaleEnvelope
            targetReentry.reentry_extremal.delta_pos
            targetReentry.reentry_extremal.delta_le_one
    _ ≤ proposition63CanonicalReentryWeight delta weightLoss *
          (wz2PaperPureRefinementFraction delta 61 *
            Kakeya.realRpowENN delta
              (targetReentry.reentryNormalizationLoss + 2)) := huniform
    _ = targetReentry.normalizationWeight *
          (wz2PaperPureRefinementFraction delta 61 *
            Kakeya.realRpowENN delta
              (targetReentry.reentryNormalizationLoss + 2)) := by
      rw [hweight]

/-- Factor-two compatibility specialization of the uniform terminal scalar
bound. -/
theorem proposition63_two_rich_terminal_scalar_of_uniform_envelope
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss weightLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent levelCount : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (hweight : targetReentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta weightLoss)
    (hweightUpper : targetReentry.weightUpper =
      (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2)
    (hlevelCount : targetReentry.levelCount = levelCount)
    (hdeltaTiny : delta ≤ 1 / 100000)
    (huniform :
      (((2 * stickyCoarseCloseCount) *
          Kakeya.realRpowENN (delta / robustScale.1)
            (2 - sigma - outer.terminalLoss) *
          ((8 * proposition63OneScaleLogEnvelope delta ^
                (levelCount + 2)) *
            ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2))) *
          ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
          Kakeya.realRpowENN robustScale.1 (2 - outerLoss)) *
          (proposition63OneScaleLogEnvelope delta ^ 10 *
            Kakeya.realRpowENN delta
              (sigma - targetReentry.reentryNormalizationLoss)) ≤
        proposition63CanonicalReentryWeight delta weightLoss *
          (wz2PaperPureRefinementFraction delta 61 *
            Kakeya.realRpowENN delta
              (targetReentry.reentryNormalizationLoss + 2))) :
    (((2 * stickyCoarseCloseCount) *
        Kakeya.realRpowENN (delta / robustScale.1)
          (2 - sigma - outer.terminalLoss) *
        (targetReentry.regularized.regularizationLoss *
          targetReentry.weightUpper)) *
        ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
        Kakeya.realRpowENN robustScale.1 (2 - outerLoss)) *
        ((target.terminal.regularity : ENNReal) *
          Kakeya.realRpowENN delta
            (sigma - targetReentry.reentryNormalizationLoss)) ≤
      targetReentry.normalizationWeight *
        (wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            (targetReentry.reentryNormalizationLoss + 2)) := by
  exact proposition63_scaled_two_rich_terminal_scalar_of_uniform_envelope
    outer targetReentry htargetReentryLoss target hweight hweightUpper
    hlevelCount hdeltaTiny 2 huniform

/-- Specialize the pre-runtime terminal-scalar receipt to the actual nested
two-rich output.  Only canonical equalities returned by the genuine second
re-entry are used. -/
theorem proposition63_scaled_two_rich_terminal_scalar_of_absorption
    {delta sigma robustExponent outerLoss outerSourceLoss
      outerNormalizationLoss targetReentryLoss targetLoss weightLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent levelCount : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    {factor : ℕ}
    (absorption : Proposition63ScaledTwoRichTerminalScalarAbsorptionData
      sigma robustExponent outerLoss targetReentry.reentryNormalizationLoss
      weightLoss factor levelCount)
    (hdelta : delta ≤ absorption.delta₀)
    (hrobustScale : robustScale.1 = Real.rpow delta robustExponent)
    (hweight : targetReentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta weightLoss)
    (hweightUpper : targetReentry.weightUpper =
      (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2)
    (hlevelCount : targetReentry.levelCount = levelCount) :
    ((((factor : ENNReal) * stickyCoarseCloseCount) *
        Kakeya.realRpowENN (delta / robustScale.1)
          (2 - sigma - outer.terminalLoss) *
        (targetReentry.regularized.regularizationLoss *
          targetReentry.weightUpper)) *
        ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
        Kakeya.realRpowENN robustScale.1 (2 - outerLoss)) *
        ((target.terminal.regularity : ENNReal) *
          Kakeya.realRpowENN delta
            (sigma - targetReentry.reentryNormalizationLoss)) ≤
      targetReentry.normalizationWeight *
        (wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            (targetReentry.reentryNormalizationLoss + 2)) := by
  apply proposition63_scaled_two_rich_terminal_scalar_of_uniform_envelope
    outer targetReentry htargetReentryLoss target hweight hweightUpper
      hlevelCount (hdelta.trans absorption.delta₀_le_tiny) factor
  exact absorption.absorb targetReentry.reentry_extremal.delta_pos hdelta
    hrobustScale outer.terminalLoss_pos outer.terminalLoss_le_output

/-- Factor-two compatibility specialization of the pre-runtime terminal
scalar receipt. -/
theorem proposition63_two_rich_terminal_scalar_of_absorption
    {delta sigma robustExponent outerLoss outerSourceLoss
      outerNormalizationLoss targetReentryLoss targetLoss weightLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent levelCount : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (absorption : Proposition63TwoRichTerminalScalarAbsorptionData
      sigma robustExponent outerLoss targetReentry.reentryNormalizationLoss
      weightLoss levelCount)
    (hdelta : delta ≤ absorption.delta₀)
    (hrobustScale : robustScale.1 = Real.rpow delta robustExponent)
    (hweight : targetReentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta weightLoss)
    (hweightUpper : targetReentry.weightUpper =
      (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2)
    (hlevelCount : targetReentry.levelCount = levelCount) :
    (((2 * stickyCoarseCloseCount) *
        Kakeya.realRpowENN (delta / robustScale.1)
          (2 - sigma - outer.terminalLoss) *
        (targetReentry.regularized.regularizationLoss *
          targetReentry.weightUpper)) *
        ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
        Kakeya.realRpowENN robustScale.1 (2 - outerLoss)) *
        ((target.terminal.regularity : ENNReal) *
          Kakeya.realRpowENN delta
            (sigma - targetReentry.reentryNormalizationLoss)) ≤
      targetReentry.normalizationWeight *
        (wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            (targetReentry.reentryNormalizationLoss + 2)) := by
  exact proposition63_scaled_two_rich_terminal_scalar_of_absorption
    outer targetReentry htargetReentryLoss target absorption hdelta
    hrobustScale hweight hweightUpper hlevelCount

/-- Produce the requested scaled cross-call degree comparison directly from
the pre-runtime scalar absorption.  The robust localization uses `factor = 4`;
no runtime cardinality or multiplicity hypothesis remains. -/
theorem proposition63_two_rich_cross_degree_scaled_of_absorption
    {delta sigma robustExponent outerLoss outerSourceLoss
      outerNormalizationLoss targetReentryLoss targetLoss weightLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent factor levelCount : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (absorption : Proposition63ScaledTwoRichTerminalScalarAbsorptionData
      sigma robustExponent outerLoss targetReentry.reentryNormalizationLoss
      weightLoss factor levelCount)
    (hdelta : delta ≤ absorption.delta₀)
    (hrobustScale : robustScale.1 = Real.rpow delta robustExponent)
    (hweight : targetReentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta weightLoss)
    (hweightUpper : targetReentry.weightUpper =
      (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2)
    (hlevelCount : targetReentry.levelCount = levelCount)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000) :
    (factor : ENNReal) *
        (stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal)) ≤
      ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
        ENNReal) := by
  have terminalScalar :=
    proposition63_scaled_two_rich_terminal_scalar_of_absorption outer
      targetReentry htargetReentryLoss target absorption hdelta hrobustScale
      hweight hweightUpper hlevelCount
  simpa only [mul_assoc] using
    proposition63_two_rich_cross_degree_of_terminal_scalar_scaled outer
      targetReentry htargetReentryLoss target
      (hdelta.trans absorption.delta₀_le_tiny |>.trans (by norm_num))
      hrobustSmall factor terminalScalar

/-- Restore one target-rich variation on the target normalization's own
family.  This is the dependent-family step used by Lemma 4.7: its mass loss
contains only the current sticky refinement and the current orientation
selection, never the ordinary re-entry weight. -/
theorem proposition63_extremal_one_scale_plane_map_on_normalized_source
    {delta sigma inputLoss sourceLoss targetLoss outputLoss incidence
      variationScale kappa : ℝ}
    {sourceConfiguration :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := sourceLoss) sourceConfiguration normalizationExponent)
    (hinputLoss : 0 < inputLoss)
    (hsourceLoss : 0 < sourceLoss)
    (sourceMap : PaperWZ1WeakPlaneMapData
      normalized.croppedRefined incidence)
    (sourceCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        sourceMap.planeMap first = sourceMap.planeMap second)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) normalized.croppedRefined
      (normalized.toPropStickyReentryData hinputLoss hsourceLoss) targetScale)
    (hclose : ∀ point ∈ target.data.refined.union, ∀ index,
      point ∈ target.data.refined.carrier index →
        2 * paperCloseDirectionCount target.data.refined point index kappa ≤
          target.terminal.fineDegreeFloor * target.terminal.muFine)
    (hincidence : 0 ≤ incidence)
    (hvariation : 0 < variationScale)
    (hkappa : targetScale.1 < kappa)
    (K : ℕ) (hK : 0 < K)
    (htargetAligned : targetScale.1 = (K : ℝ) * delta)
    (hsourceOutput : sourceLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hdeltaStrict : delta < 1)
    (hslack :
      proposition63Lemma43MassLoss
          (wz2PaperPureRefinementFraction delta 61 *
            Kakeya.realRpowENN targetScale.1 (2 * targetLoss))
          (27 * (2 *
            (wz1OrientationCapCount
              (10 * (incidence + targetScale.1 / 2) /
                (kappa - targetScale.1)) variationScale : ENNReal))) *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta sourceLoss) :
    ∃ result : Proposition63ExtremalOneScalePlaneMapData
        (initialNormalized := normalized) normalized.croppedRefined sourceMap
        outputLoss targetScale.1 variationScale,
      result.massLoss = proposition63Lemma43MassLoss
        (wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN targetScale.1 (2 * targetLoss))
        (27 * (2 *
          (wz1OrientationCapCount
            (10 * (incidence + targetScale.1 / 2) /
              (kappa - targetScale.1)) variationScale : ENNReal))) := by
  have terminalCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        (target.terminalPlaneMap sourceMap).planeMap first =
          (target.terminalPlaneMap sourceMap).planeMap second := by
    intro first second sameCell
    exact sourceCellwise first second sameCell
  rcases target.asymmetric_variation
      (fun _ => Set.Subset.rfl) target.terminal.fine_cubical
      (target.terminalPlaneMap sourceMap) terminalCellwise
      (fun point pointMem =>
        target.terminal.fine_pointMultiplicity_floor_on_union pointMem)
      hclose hincidence hvariation hkappa K hK htargetAligned with
    ⟨selected, selectedSub, selectedCubical, selectedVariation,
      _selectedMultiplicity, selectedMass⟩
  let ambient : WZ1PaperTubeShading normalized.croppedFamily :=
    extendShading target.data.selected selected
  have ambientSub : PaperIsSubshading ambient normalized.croppedRefined := by
    intro ambientIndex point pointMem
    by_cases imageMem : ∃ selectedIndex,
        target.data.selected.embedding selectedIndex = ambientIndex
    · rcases imageMem with ⟨selectedIndex, rfl⟩
      change point ∈ (extendShading target.data.selected selected).carrier
        (target.data.selected.embedding selectedIndex) at pointMem
      rw [extendShading_carrier_mem] at pointMem
      exact target.data.subshading selectedIndex
        (selectedSub selectedIndex pointMem)
    · change point ∈ (extendShading target.data.selected selected).carrier
        ambientIndex at pointMem
      rw [extendShading_carrier_empty imageMem] at pointMem
      exact False.elim pointMem
  have ambientCubical : WZ1PaperIsCubicalShading ambient :=
    extendShading_cubical target.data.selected selectedCubical
  let ambientMap := paperWeakPlaneMapRestrict sourceMap ambientSub
  let leftFactor : ENNReal :=
    wz2PaperPureRefinementFraction delta 61 *
      Kakeya.realRpowENN targetScale.1 (2 * targetLoss)
  let rightFactor : ENNReal :=
    27 * (2 *
      (wz1OrientationCapCount
        (10 * (incidence + targetScale.1 / 2) /
          (kappa - targetScale.1)) variationScale : ENNReal))
  let massLoss := proposition63Lemma43MassLoss leftFactor rightFactor
  have refinementPos :
      0 < wz2PaperPureRefinementFraction delta 61 := by
    unfold wz2PaperPureRefinementFraction
    exact ENNReal.pow_pos
      (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top) 61
  have refinementTop :
      wz2PaperPureRefinementFraction delta 61 ≠ ⊤ := by
    unfold wz2PaperPureRefinementFraction
    apply ENNReal.pow_ne_top
    apply ENNReal.inv_ne_top.mpr
    exact (ENNReal.ofReal_pos.mpr <| Real.log_pos <|
      one_lt_one_div normalized.final_extremal.delta_pos hdeltaStrict).ne'
  have targetPowerPos :
      0 < Kakeya.realRpowENN targetScale.1 (2 * targetLoss) :=
    ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos target.data.coarse_extremal.delta_pos _)
  have leftPos : 0 < leftFactor := by
    dsimp only [leftFactor]
    exact ENNReal.mul_pos refinementPos.ne' targetPowerPos.ne'
  have leftTop : leftFactor ≠ ⊤ := by
    dsimp only [leftFactor]
    exact ENNReal.mul_ne_top refinementTop (by simp [Kakeya.realRpowENN])
  have rightTop : rightFactor ≠ ⊤ := by
    dsimp only [rightFactor]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top (by norm_num) (by simp))
  have combinedMass : leftFactor * normalized.croppedRefined.mass ≤
      rightFactor * selected.mass := by
    calc
      leftFactor * normalized.croppedRefined.mass =
          Kakeya.realRpowENN targetScale.1 (2 * targetLoss) *
            (wz2PaperPureRefinementFraction delta 61 *
              normalized.croppedRefined.mass) := by
        dsimp only [leftFactor]
        ring
      _ ≤ Kakeya.realRpowENN targetScale.1 (2 * targetLoss) *
          target.data.refined.mass :=
        mul_le_mul_left' target.total_mass_retention _
      _ ≤ rightFactor * selected.mass := by
        simpa only [rightFactor] using selectedMass
  have ambientMass : massLoss⁻¹ * normalized.croppedRefined.mass ≤
      ambient.mass := by
    rw [show ambient.mass = selected.mass by
      dsimp only [ambient]
      exact extendShading_mass target.data.selected selected]
    exact proposition63Lemma43MassLoss_inv_mul_le
      leftPos leftTop rightTop combinedMass
  have ambientExtremal : WZ2PaperCroppedIsExtremal
      sigma outputLoss normalized.croppedFamily ambient := by
    apply transfer_cropped_extremal_to_subshading massLoss
      (proposition63Lemma43MassLoss_pos _ _)
      (proposition63Lemma43MassLoss_ne_top leftPos rightTop)
      normalized.final_extremal ambientSub ambientMass ambientCubical
      hsourceOutput hslack normalized.final_extremal.delta_pos
      normalized.final_extremal.delta_le_one houtputLoss
  refine ⟨{
    shading := ambient
    subshading := ambientSub
    cubical := ambientCubical
    planeMap := ambientMap
    same_plane_map := rfl
    variation := ?_
    massLoss := massLoss
    massLoss_pos := proposition63Lemma43MassLoss_pos _ _
    massLoss_ne_top := proposition63Lemma43MassLoss_ne_top leftPos rightTop
    mass_retention := ambientMass
    extremal := ambientExtremal
  }, rfl⟩
  intro point pointMem other otherMem distanceBound
  have ambientUnion : ambient.union = selected.union :=
    extendShading_union target.data.selected selected
  have selectedPoint : point ∈ selected.union := by
    rw [← ambientUnion]
    exact pointMem
  have selectedOther : other ∈ selected.union := by
    rw [← ambientUnion]
    exact otherMem
  change dist (sourceMap.planeMap point) (sourceMap.planeMap other) ≤
    variationScale
  simpa only [Proposition63RichTerminalStickyData.terminalPlaneMap_apply] using
    selectedVariation point selectedPoint other selectedOther distanceBound

/-- Execute one already-prepared rich/nearby geometric step, zero-extend its
result through both genuine subfamily selections, and immediately restore
cropped extremality.  This theorem contains no product over spatial scales. -/
theorem proposition63_extremal_one_scale_plane_map_of_rich
    {delta sigma initialInputLoss normalizationLoss reentryLoss robustLoss
      currentLoss outputLoss incidence spatialScale variationScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource 0}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (currentExtremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      initialNormalized.croppedFamily current)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (currentCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        currentMap.planeMap first = currentMap.planeMap second)
    (reentryData : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (reentryLoss_pos : 0 < reentryLoss)
    {robustScale : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (sigma := sigma) (outputLoss := robustLoss)
      reentryData.normalization.croppedRefined
      (reentryData.normalization.toPropStickyReentryData
        reentryLoss_pos reentryData.reentry_normalization_loss_pos)
      robustScale)
    {requested : WZ2PaperRequestedScale delta}
    {C densityPower : ENNReal}
    (nearby : WZ2PaperPureNearbyScaleCoverData
      reentryData.normalization.croppedFamily requested C)
    (hdensityPowerPos : 0 < densityPower)
    (hdensityPowerTop : densityPower ≠ ⊤)
    (hrobustLoss : 0 ≤ robustLoss)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hdegreeAbsorb :
      (12 * (2 * stickyCoarseCloseCount)) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN robustScale.1 (-sigma + 4 * robustLoss))
    (hdensityScalar :
      densityPower *
          ((rich.terminal.regularity : ENNReal) *
            Kakeya.realRpowENN delta
              (sigma - reentryData.reentryNormalizationLoss)) ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            (reentryData.reentryNormalizationLoss + 2))
    (hincidence : 0 ≤ incidence)
    (hparentSmall : nearby.rho < 1 / 8)
    (hparentRobust : 8 * nearby.rho < robustScale.1)
    (hspatial : 0 < spatialScale)
    (hvariation : 0 < variationScale)
    (K : ℕ) (hK : 0 < K)
    (hspatialAligned : spatialScale = (K : ℝ) * delta)
    (hcurrentOutput : currentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hslack :
      proposition63Lemma43MassLoss
          (((73 / 100 : ENNReal) * reentryData.normalizationWeight) *
            (wz2PaperPureRefinementFraction delta 61 *
              densityPower ^ 2))
          (reentryData.regularized.regularizationLoss *
            (27 * (2 *
              (wz1OrientationCapCount
                (10 * (incidence + 4 * nearby.rho) /
                  (robustScale.1 - 8 * nearby.rho)) variationScale :
                    ENNReal)))) *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta currentLoss) :
    Nonempty (Proposition63ExtremalOneScalePlaneMapData
      current currentMap outputLoss spatialScale variationScale) := by
  let normalizedMap := reentryData.normalizedPlaneMap currentMap
  have normalizedCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        normalizedMap.planeMap first = normalizedMap.planeMap second := by
    intro first second sameCell
    exact currentCellwise first second sameCell
  rcases rich.oneScaleVariation normalizedMap normalizedCellwise nearby
      hrobustLoss hrobustSmall hdegreeAbsorb hdensityScalar hincidence
      hparentSmall hparentRobust hspatial hvariation K hK hspatialAligned with
    ⟨selected, selectedSub, selectedCubical, selectedVariation,
      _selectedMultiplicity, selectedMass⟩
  let terminalAmbient : WZ1PaperTubeShading
      reentryData.normalization.croppedFamily :=
    extendShading rich.data.selected selected
  have terminalAmbientSub : PaperIsSubshading terminalAmbient
      reentryData.normalization.croppedRefined := by
    intro ambientIndex point pointMem
    by_cases imageMem : ∃ selectedIndex,
        rich.data.selected.embedding selectedIndex = ambientIndex
    · rcases imageMem with ⟨selectedIndex, rfl⟩
      change point ∈ (extendShading rich.data.selected selected).carrier
        (rich.data.selected.embedding selectedIndex) at pointMem
      rw [extendShading_carrier_mem] at pointMem
      exact rich.data.subshading selectedIndex
        (selectedSub selectedIndex pointMem)
    · change point ∈ (extendShading rich.data.selected selected).carrier
        ambientIndex at pointMem
      rw [extendShading_carrier_empty imageMem] at pointMem
      exact False.elim pointMem
  let ambient := reentryData.extendCandidate terminalAmbient
  have ambientSub : PaperIsSubshading ambient current :=
    reentryData.extendCandidate_subshading terminalAmbientSub
  have ambientCubical : WZ1PaperIsCubicalShading ambient := by
    exact extendShading_cubical reentryData.regularized.selected
      (extendShading_cubical rich.data.selected selectedCubical)
  let ambientMap := paperWeakPlaneMapRestrict currentMap ambientSub
  let leftFactor : ENNReal :=
    ((73 / 100 : ENNReal) * reentryData.normalizationWeight) *
      (wz2PaperPureRefinementFraction delta 61 * densityPower ^ 2)
  let orientationFactor : ENNReal :=
    27 * (2 *
      (wz1OrientationCapCount
        (10 * (incidence + 4 * nearby.rho) /
          (robustScale.1 - 8 * nearby.rho)) variationScale : ENNReal))
  let rightFactor : ENNReal :=
    reentryData.regularized.regularizationLoss * orientationFactor
  let massLoss := proposition63Lemma43MassLoss leftFactor rightFactor
  have deltaLtOne : delta < 1 := by
    exact (robustScale.2.1.trans hrobustSmall).trans_lt (by norm_num)
  have logPos :
      0 < ENNReal.ofReal (Real.log (1 / delta)) := by
    apply ENNReal.ofReal_pos.mpr
    exact Real.log_pos
      (one_lt_one_div currentExtremal.delta_pos deltaLtOne)
  have refinementPos :
      0 < wz2PaperPureRefinementFraction delta 61 := by
    unfold wz2PaperPureRefinementFraction
    exact ENNReal.pow_pos
      (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top) 61
  have refinementTop :
      wz2PaperPureRefinementFraction delta 61 ≠ ⊤ := by
    unfold wz2PaperPureRefinementFraction
    exact ENNReal.pow_ne_top
      (ENNReal.inv_ne_top.mpr logPos.ne')
  have leftPos : 0 < leftFactor := by
    dsimp only [leftFactor]
    apply ENNReal.mul_pos
    · exact (ENNReal.mul_pos (by norm_num)
        reentryData.normalization_weight_ne_zero).ne'
    · exact (ENNReal.mul_pos refinementPos.ne'
        (ENNReal.pow_pos hdensityPowerPos 2).ne').ne'
  have leftTop : leftFactor ≠ ⊤ := by
    dsimp only [leftFactor]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.div_ne_top (by norm_num) (by norm_num))
        reentryData.normalization_weight_ne_top)
      (ENNReal.mul_ne_top refinementTop
        (ENNReal.pow_ne_top hdensityPowerTop))
  have rightTop : rightFactor ≠ ⊤ := by
    dsimp only [rightFactor, orientationFactor]
    exact ENNReal.mul_ne_top
      (by
        rw [reentryData.regularized.regularizationLoss_eq]
        exact ENNReal.mul_ne_top (by norm_num) (by simp))
      (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top (by norm_num) (by simp)))
  have combinedMass : leftFactor * current.mass ≤
      rightFactor * selected.mass := by
    calc
      leftFactor * current.mass =
          (wz2PaperPureRefinementFraction delta 61 * densityPower ^ 2) *
            (((73 / 100 : ENNReal) *
              reentryData.normalizationWeight) * current.mass) := by
        simp only [leftFactor]
        ring
      _ ≤ (wz2PaperPureRefinementFraction delta 61 * densityPower ^ 2) *
          (reentryData.regularized.regularizationLoss *
            reentryData.normalization.croppedRefined.mass) := by
        exact mul_le_mul_left' reentryData.reentryMassRetention _
      _ = reentryData.regularized.regularizationLoss *
          (densityPower ^ 2 *
            (wz2PaperPureRefinementFraction delta 61 *
              reentryData.normalization.croppedRefined.mass)) := by ring
      _ ≤ reentryData.regularized.regularizationLoss *
          (densityPower ^ 2 * rich.data.refined.mass) := by
        gcongr
        exact rich.total_mass_retention
      _ ≤ reentryData.regularized.regularizationLoss *
          (orientationFactor * selected.mass) := by
        exact mul_le_mul_left'
          (by simpa only [orientationFactor] using selectedMass) _
      _ = rightFactor * selected.mass := by
        simp only [rightFactor]
        ring
  have ambientMass : massLoss⁻¹ * current.mass ≤ ambient.mass := by
    rw [reentryData.extendCandidate_mass]
    rw [show terminalAmbient.mass = selected.mass by
      dsimp only [terminalAmbient]
      exact extendShading_mass rich.data.selected selected]
    exact proposition63Lemma43MassLoss_inv_mul_le
      leftPos leftTop rightTop combinedMass
  have ambientExtremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      initialNormalized.croppedFamily ambient := by
    apply transfer_cropped_extremal_to_subshading massLoss
      (proposition63Lemma43MassLoss_pos _ _)
      (proposition63Lemma43MassLoss_ne_top leftPos rightTop)
      currentExtremal ambientSub ambientMass ambientCubical
      hcurrentOutput hslack currentExtremal.delta_pos
      currentExtremal.delta_le_one houtputLoss
  refine ⟨{
    shading := ambient
    subshading := ambientSub
    cubical := ambientCubical
    planeMap := ambientMap
    same_plane_map := rfl
    variation := ?_
    massLoss := massLoss
    massLoss_pos := proposition63Lemma43MassLoss_pos _ _
    massLoss_ne_top := proposition63Lemma43MassLoss_ne_top leftPos rightTop
    mass_retention := ambientMass
    extremal := ambientExtremal
  }⟩
  intro point pointMem other otherMem distanceBound
  have ambientUnion : ambient.union = selected.union := by
    calc
      ambient.union = terminalAmbient.union := reentryData.extendCandidate_union _
      _ = selected.union := extendShading_union rich.data.selected selected
  have selectedPoint : point ∈ selected.union := by
    rw [← ambientUnion]
    exact pointMem
  have selectedOther : other ∈ selected.union := by
    rw [← ambientUnion]
    exact otherMem
  exact selectedVariation point selectedPoint other selectedOther distanceBound

/-- Execute the corrected target-scale rich step and immediately restore
cropped extremality.  Unlike `proposition63_extremal_one_scale_plane_map_of_rich`,
the geometric mass bound here uses the terminal balanced parent and fiber
multiplicities, so no square of the global fine-family cardinality occurs.
The close-count premise is deliberately separated: it is supplied by the
outer robust rich call in the two-call Lemma 4.7 producer. -/
theorem proposition63_extremal_one_scale_plane_map_of_target_rich
    {delta sigma initialInputLoss normalizationLoss reentryLoss targetLoss
      currentLoss outputLoss incidence variationScale kappa : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {initialNormalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource
        initialNormalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (currentExtremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      initialNormalized.croppedFamily current)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (currentCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        currentMap.planeMap first = currentMap.planeMap second)
    (reentryData : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (hreentryLoss : 0 < reentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (sigma := sigma) (outputLoss := targetLoss)
      reentryData.normalization.croppedRefined
      (reentryData.normalization.toPropStickyReentryData
        hreentryLoss
        reentryData.reentry_normalization_loss_pos)
      targetScale)
    (hclose : ∀ point ∈ target.data.refined.union, ∀ index,
      point ∈ target.data.refined.carrier index →
        2 * paperCloseDirectionCount target.data.refined point index kappa ≤
          target.terminal.fineDegreeFloor * target.terminal.muFine)
    (hincidence : 0 ≤ incidence)
    (hvariation : 0 < variationScale)
    (hkappa : targetScale.1 < kappa)
    (K : ℕ) (hK : 0 < K)
    (htargetAligned : targetScale.1 = (K : ℝ) * delta)
    (hcurrentOutput : currentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hdeltaStrict : delta < 1)
    (hslack :
      proposition63Lemma43MassLoss
          (((73 / 100 : ENNReal) * reentryData.normalizationWeight) *
            (wz2PaperPureRefinementFraction delta 61 *
              Kakeya.realRpowENN targetScale.1 (2 * targetLoss)))
          (reentryData.regularized.regularizationLoss *
            (27 * (2 *
              (wz1OrientationCapCount
                (10 * (incidence + targetScale.1 / 2) /
                  (kappa - targetScale.1)) variationScale : ENNReal)))) *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta currentLoss) :
    ∃ result : Proposition63ExtremalOneScalePlaneMapData
        current currentMap outputLoss targetScale.1 variationScale,
      result.massLoss = proposition63Lemma43MassLoss
        (((73 / 100 : ENNReal) * reentryData.normalizationWeight) *
          (wz2PaperPureRefinementFraction delta 61 *
            Kakeya.realRpowENN targetScale.1 (2 * targetLoss)))
        (reentryData.regularized.regularizationLoss *
          (27 * (2 *
            (wz1OrientationCapCount
              (10 * (incidence + targetScale.1 / 2) /
                (kappa - targetScale.1)) variationScale : ENNReal)))) := by
  let normalizedMap := reentryData.normalizedPlaneMap currentMap
  have normalizedCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        normalizedMap.planeMap first = normalizedMap.planeMap second := by
    intro first second sameCell
    exact currentCellwise first second sameCell
  have terminalCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        (target.terminalPlaneMap normalizedMap).planeMap first =
          (target.terminalPlaneMap normalizedMap).planeMap second := by
    intro first second sameCell
    exact normalizedCellwise first second sameCell
  rcases target.asymmetric_variation
      (fun _ => Set.Subset.rfl) target.terminal.fine_cubical
      (target.terminalPlaneMap normalizedMap) terminalCellwise
      (fun point pointMem =>
        target.terminal.fine_pointMultiplicity_floor_on_union pointMem)
      hclose hincidence hvariation hkappa K hK htargetAligned with
    ⟨selected, selectedSub, selectedCubical, selectedVariation,
      _selectedMultiplicity, selectedMass⟩
  let terminalAmbient : WZ1PaperTubeShading
      reentryData.normalization.croppedFamily :=
    extendShading target.data.selected selected
  have terminalAmbientSub : PaperIsSubshading terminalAmbient
      reentryData.normalization.croppedRefined := by
    intro ambientIndex point pointMem
    by_cases imageMem : ∃ selectedIndex,
        target.data.selected.embedding selectedIndex = ambientIndex
    · rcases imageMem with ⟨selectedIndex, rfl⟩
      change point ∈ (extendShading target.data.selected selected).carrier
        (target.data.selected.embedding selectedIndex) at pointMem
      rw [extendShading_carrier_mem] at pointMem
      exact target.data.subshading selectedIndex
        (selectedSub selectedIndex pointMem)
    · change point ∈ (extendShading target.data.selected selected).carrier
        ambientIndex at pointMem
      rw [extendShading_carrier_empty imageMem] at pointMem
      exact False.elim pointMem
  let ambient := reentryData.extendCandidate terminalAmbient
  have ambientSub : PaperIsSubshading ambient current :=
    reentryData.extendCandidate_subshading terminalAmbientSub
  have ambientCubical : WZ1PaperIsCubicalShading ambient := by
    exact extendShading_cubical reentryData.regularized.selected
      (extendShading_cubical target.data.selected selectedCubical)
  let ambientMap := paperWeakPlaneMapRestrict currentMap ambientSub
  let leftFactor : ENNReal :=
    ((73 / 100 : ENNReal) * reentryData.normalizationWeight) *
      (wz2PaperPureRefinementFraction delta 61 *
        Kakeya.realRpowENN targetScale.1 (2 * targetLoss))
  let orientationFactor : ENNReal :=
    27 * (2 *
      (wz1OrientationCapCount
        (10 * (incidence + targetScale.1 / 2) /
          (kappa - targetScale.1)) variationScale : ENNReal))
  let rightFactor : ENNReal :=
    reentryData.regularized.regularizationLoss * orientationFactor
  let massLoss := proposition63Lemma43MassLoss leftFactor rightFactor
  have refinementPos :
      0 < wz2PaperPureRefinementFraction delta 61 := by
    unfold wz2PaperPureRefinementFraction
    exact ENNReal.pow_pos
      (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top) 61
  have refinementTop :
      wz2PaperPureRefinementFraction delta 61 ≠ ⊤ := by
    unfold wz2PaperPureRefinementFraction
    apply ENNReal.pow_ne_top
    apply ENNReal.inv_ne_top.mpr
    exact (ENNReal.ofReal_pos.mpr <| Real.log_pos <|
      one_lt_one_div currentExtremal.delta_pos hdeltaStrict).ne'
  have targetPowerPos :
      0 < Kakeya.realRpowENN targetScale.1 (2 * targetLoss) := by
    exact ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos target.data.coarse_extremal.delta_pos _)
  have targetPowerTop :
      Kakeya.realRpowENN targetScale.1 (2 * targetLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have leftPos : 0 < leftFactor := by
    dsimp only [leftFactor]
    apply ENNReal.mul_pos
    · exact (ENNReal.mul_pos (by norm_num)
        reentryData.normalization_weight_ne_zero).ne'
    · exact (ENNReal.mul_pos refinementPos.ne' targetPowerPos.ne').ne'
  have leftTop : leftFactor ≠ ⊤ := by
    dsimp only [leftFactor]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.div_ne_top (by norm_num) (by norm_num))
        reentryData.normalization_weight_ne_top)
      (ENNReal.mul_ne_top refinementTop targetPowerTop)
  have rightTop : rightFactor ≠ ⊤ := by
    dsimp only [rightFactor, orientationFactor]
    exact ENNReal.mul_ne_top
      (by
        rw [reentryData.regularized.regularizationLoss_eq]
        exact ENNReal.mul_ne_top (by norm_num) (by simp))
      (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top (by norm_num) (by simp)))
  have combinedMass : leftFactor * current.mass ≤
      rightFactor * selected.mass := by
    calc
      leftFactor * current.mass =
          (wz2PaperPureRefinementFraction delta 61 *
            Kakeya.realRpowENN targetScale.1 (2 * targetLoss)) *
            (((73 / 100 : ENNReal) *
              reentryData.normalizationWeight) * current.mass) := by
        simp only [leftFactor]
        ring
      _ ≤ (wz2PaperPureRefinementFraction delta 61 *
            Kakeya.realRpowENN targetScale.1 (2 * targetLoss)) *
          (reentryData.regularized.regularizationLoss *
            reentryData.normalization.croppedRefined.mass) := by
        exact mul_le_mul_left' reentryData.reentryMassRetention _
      _ = reentryData.regularized.regularizationLoss *
          (Kakeya.realRpowENN targetScale.1 (2 * targetLoss) *
            (wz2PaperPureRefinementFraction delta 61 *
              reentryData.normalization.croppedRefined.mass)) := by ring
      _ ≤ reentryData.regularized.regularizationLoss *
          (Kakeya.realRpowENN targetScale.1 (2 * targetLoss) *
            target.data.refined.mass) := by
        gcongr
        exact target.total_mass_retention
      _ ≤ reentryData.regularized.regularizationLoss *
          (orientationFactor * selected.mass) := by
        exact mul_le_mul_left'
          (by simpa only [orientationFactor] using selectedMass) _
      _ = rightFactor * selected.mass := by
        simp only [rightFactor]
        ring
  have ambientMass : massLoss⁻¹ * current.mass ≤ ambient.mass := by
    rw [reentryData.extendCandidate_mass]
    rw [show terminalAmbient.mass = selected.mass by
      dsimp only [terminalAmbient]
      exact extendShading_mass target.data.selected selected]
    exact proposition63Lemma43MassLoss_inv_mul_le
      leftPos leftTop rightTop combinedMass
  have ambientExtremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      initialNormalized.croppedFamily ambient := by
    apply transfer_cropped_extremal_to_subshading massLoss
      (proposition63Lemma43MassLoss_pos _ _)
      (proposition63Lemma43MassLoss_ne_top leftPos rightTop)
      currentExtremal ambientSub ambientMass ambientCubical
      hcurrentOutput hslack currentExtremal.delta_pos
      currentExtremal.delta_le_one houtputLoss
  refine ⟨{
    shading := ambient
    subshading := ambientSub
    cubical := ambientCubical
    planeMap := ambientMap
    same_plane_map := rfl
    variation := ?_
    massLoss := massLoss
    massLoss_pos := proposition63Lemma43MassLoss_pos _ _
    massLoss_ne_top := proposition63Lemma43MassLoss_ne_top leftPos rightTop
    mass_retention := ambientMass
    extremal := ambientExtremal
  }, rfl⟩
  intro point pointMem other otherMem distanceBound
  have ambientUnion : ambient.union = selected.union := by
    calc
      ambient.union = terminalAmbient.union :=
        reentryData.extendCandidate_union _
      _ = selected.union := extendShading_union target.data.selected selected
  have selectedPoint : point ∈ selected.union := by
    rw [← ambientUnion]
    exact pointMem
  have selectedOther : other ∈ selected.union := by
    rw [← ambientUnion]
    exact otherMem
  change dist (currentMap.planeMap point) (currentMap.planeMap other) ≤
    variationScale
  simpa only [normalizedMap,
    Proposition63RichTerminalStickyData.terminalPlaneMap_apply,
    Proposition63CurrentShadingReentryData.normalizedPlaneMap_apply] using
    selectedVariation point selectedPoint other selectedOther distanceBound

/-- Complete runtime two-rich-call one-scale step.  The outer terminal gives
the robust close-direction bound, the target terminal gives the balanced
parent-pair selection, and the exact cross-call scalar ledger compares the
two multiplicity scales before extremality is restored. -/
theorem proposition63_extremal_one_scale_plane_map_of_two_rich
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss targetStepOutputLoss outputLoss incidence
      variationScale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (currentMap : PaperWZ1WeakPlaneMapData
      (extendShading outer.data.selected outer.data.refined) incidence)
    (currentCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        currentMap.planeMap first = currentMap.planeMap second)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hterminalScalar :
      (((2 * stickyCoarseCloseCount) *
          Kakeya.realRpowENN (delta / robustScale.1)
            (2 - sigma - outer.terminalLoss) *
          (targetReentry.regularized.regularizationLoss *
            targetReentry.weightUpper)) *
          ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
          Kakeya.realRpowENN robustScale.1 (2 - outerLoss)) *
          ((target.terminal.regularity : ENNReal) *
            Kakeya.realRpowENN delta
              (sigma - targetReentry.reentryNormalizationLoss)) ≤
        targetReentry.normalizationWeight *
          (wz2PaperPureRefinementFraction delta 61 *
            Kakeya.realRpowENN delta
              (targetReentry.reentryNormalizationLoss + 2)))
    (hincidence : 0 ≤ incidence)
    (hvariation : 0 < variationScale)
    (htargetRobust : targetScale.1 < robustScale.1)
    (K : ℕ) (hK : 0 < K)
    (htargetAligned : targetScale.1 = (K : ℝ) * delta)
    (htargetNormalizationOutput :
      targetReentry.reentryNormalizationLoss ≤ targetStepOutputLoss)
    (htargetStepOutputLoss : 0 < targetStepOutputLoss)
    (htargetReentryOutput : targetReentryLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hdeltaStrict : delta < 1)
    (hslack :
      proposition63Lemma43MassLoss
          (wz2PaperPureRefinementFraction delta 61 *
            Kakeya.realRpowENN targetScale.1 (2 * targetLoss))
          (27 * (2 *
            (wz1OrientationCapCount
              (10 * (incidence + targetScale.1 / 2) /
                (robustScale.1 - targetScale.1)) variationScale :
                  ENNReal))) *
          Kakeya.realRpowENN delta targetStepOutputLoss ≤
        Kakeya.realRpowENN delta
          targetReentry.reentryNormalizationLoss)
    (htargetDensityLift :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (targetReentry.regularized.regularizationLoss *
            targetReentry.weightUpper) *
          Kakeya.realRpowENN delta outputLoss ≤
        targetReentry.normalizationWeight *
          Kakeya.realRpowENN delta targetStepOutputLoss) :
    Nonempty (Proposition63ExtremalOneScalePlaneMapData
        (initialNormalized := outerReentry.toNormalizationData)
        (extendShading outer.data.selected outer.data.refined) currentMap
        outputLoss targetScale.1 variationScale) := by
  have crossCall :
      2 * stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal) ≤
        ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
          ENNReal) :=
    proposition63_two_rich_cross_degree_of_terminal_scalar outer
      targetReentry htargetReentryLoss target hdeltaSmall hrobustSmall
      hterminalScalar
  have closeAbsorbed : ∀ point ∈ target.data.refined.union, ∀ index,
      point ∈ target.data.refined.carrier index →
        2 * paperCloseDirectionCount target.data.refined point index
            robustScale.1 ≤
          target.terminal.fineDegreeFloor * target.terminal.muFine :=
    proposition63_two_rich_close_count_absorbed outer targetReentry
      htargetReentryLoss target (kappa := robustScale.1) hrobustSmall <| by
        simpa only [mul_assoc] using crossCall
  let normalizedMap := targetReentry.normalizedPlaneMap currentMap
  have normalizedCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        normalizedMap.planeMap first = normalizedMap.planeMap second := by
    intro first second sameCell
    exact currentCellwise first second sameCell
  rcases proposition63_extremal_one_scale_plane_map_on_normalized_source
      targetReentry.normalization htargetReentryLoss
      targetReentry.reentry_normalization_loss_pos normalizedMap
      normalizedCellwise target closeAbsorbed hincidence hvariation
      htargetRobust K hK htargetAligned htargetNormalizationOutput
      htargetStepOutputLoss hdeltaStrict hslack with ⟨inner, _⟩
  apply targetReentry.liftExtremalOneScalePlaneMap
    targetReentry.reentry_extremal currentMap
    (normalizedCurrent := targetReentry.normalization.croppedRefined)
    (fun _ => Set.Subset.rfl) normalizedMap rfl inner 1
    (by norm_num) (by norm_num) (by simp)
    htargetReentryOutput houtputLoss htargetDensityLift

/-- Run the complete two-rich target step from family-free scalar receipts.
No scalar premise below depends on either runtime tube family. -/
theorem proposition63_extremal_one_scale_plane_map_of_two_rich_absorbed
    {delta sigma robustExponent outerLoss outerSourceLoss
      outerNormalizationLoss targetReentryLoss targetLoss
      targetStepOutputLoss outputLoss targetWeightLoss incidence
      variationScale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent levelCount : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (terminalAbsorption : Proposition63TwoRichTerminalScalarAbsorptionData
      sigma robustExponent outerLoss targetReentry.reentryNormalizationLoss
      targetWeightLoss levelCount)
    (targetStepAbsorption : Proposition63TargetStepAbsorptionData
      targetReentry.reentryNormalizationLoss targetLoss robustExponent
      targetStepOutputLoss)
    (targetLiftAbsorption : Proposition63ReentryDensityLiftAbsorptionData
      targetWeightLoss targetStepOutputLoss outputLoss levelCount)
    (hdeltaTerminal : delta ≤ terminalAbsorption.delta₀)
    (hdeltaStep : delta ≤ targetStepAbsorption.delta₀)
    (hdeltaLift : delta ≤ targetLiftAbsorption.delta₀)
    (hrobustScale : robustScale.1 = Real.rpow delta robustExponent)
    (hweight : targetReentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta targetWeightLoss)
    (hweightUpper : targetReentry.weightUpper =
      (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2)
    (hlevelCount : targetReentry.levelCount = levelCount)
    (currentMap : PaperWZ1WeakPlaneMapData
      (extendShading outer.data.selected outer.data.refined) incidence)
    (currentCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        currentMap.planeMap first = currentMap.planeMap second)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hincidence : 0 ≤ incidence)
    (hincidenceTarget : incidence ≤ targetScale.1)
    (hvariation : 0 < variationScale)
    (hvariationEq : variationScale = targetScale.1)
    (htargetLower : Real.rpow delta (1 - targetLoss) ≤ targetScale.1)
    (htargetUpper : targetScale.1 ≤ Real.rpow delta targetLoss)
    (htargetSeparation : 16 * targetScale.1 ≤ robustScale.1)
    (K : ℕ) (hK : 0 < K)
    (htargetAligned : targetScale.1 = (K : ℝ) * delta)
    (htargetReentryOutput : targetReentryLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss) :
    Nonempty (Proposition63ExtremalOneScalePlaneMapData
      (initialNormalized := outerReentry.toNormalizationData)
      (extendShading outer.data.selected outer.data.refined) currentMap
      outputLoss targetScale.1 variationScale) := by
  have deltaPos := targetReentry.reentry_extremal.delta_pos
  have deltaStrict : delta < 1 :=
    (hdeltaTerminal.trans terminalAbsorption.delta₀_le_tiny).trans_lt
      (by norm_num)
  have terminalScalar :=
    proposition63_two_rich_terminal_scalar_of_absorption outer targetReentry
      htargetReentryLoss target terminalAbsorption hdeltaTerminal
      hrobustScale hweight hweightUpper hlevelCount
  have targetStepSlack := targetStepAbsorption.absorb targetScale deltaPos
    hdeltaStep hrobustScale hincidence hincidenceTarget htargetLower
      htargetUpper htargetSeparation hvariationEq
  have targetDensityLift := targetReentry.densityLift_of_absorption
    targetLiftAbsorption hdeltaLift hweight hweightUpper hlevelCount
  exact proposition63_extremal_one_scale_plane_map_of_two_rich
    outer targetReentry htargetReentryLoss target currentMap currentCellwise
    (hdeltaTerminal.trans terminalAbsorption.delta₀_le_tiny |>.trans
      (by norm_num)) hrobustSmall terminalScalar hincidence hvariation
    (by linarith) K hK htargetAligned
    targetStepAbsorption.source_lt_output.le
    (targetReentry.reentry_normalization_loss_pos.trans
      targetStepAbsorption.source_lt_output)
    htargetReentryOutput
    houtputLoss deltaStrict targetStepSlack targetDensityLift

/-- Hide both dependent selected families behind a one-scale result on the
caller's current family.  The first re-entry and the target-rich step are each
paid immediately, so the returned object is ready to be used as the next
finite-iteration state. -/
theorem proposition63_extremal_one_scale_plane_map_of_nested_two_rich
    {delta sigma initialInputLoss normalizationLoss firstReentryLoss
      currentLoss outerLoss targetReentryLoss targetLoss targetStepOutputLoss
      innerOutputLoss outputLoss incidence variationScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (currentExtremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      initialNormalized.croppedFamily current)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (currentCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        currentMap.planeMap first = currentMap.planeMap second)
    (firstReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := firstReentryLoss) initialNormalized current)
    (hfirstReentryLoss : 0 < firstReentryLoss)
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) firstReentry.normalization.croppedRefined
      (firstReentry.normalization.toPropStickyReentryData
        hfirstReentryLoss firstReentry.reentry_normalization_loss_pos)
      robustScale)
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss)
      firstReentry.normalization
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hterminalScalar :
      (((2 * stickyCoarseCloseCount) *
          Kakeya.realRpowENN (delta / robustScale.1)
            (2 - sigma - outer.terminalLoss) *
          (targetReentry.regularized.regularizationLoss *
            targetReentry.weightUpper)) *
          ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
          Kakeya.realRpowENN robustScale.1 (2 - outerLoss)) *
          ((target.terminal.regularity : ENNReal) *
            Kakeya.realRpowENN delta
              (sigma - targetReentry.reentryNormalizationLoss)) ≤
        targetReentry.normalizationWeight *
          (wz2PaperPureRefinementFraction delta 61 *
            Kakeya.realRpowENN delta
              (targetReentry.reentryNormalizationLoss + 2)))
    (hincidence : 0 ≤ incidence)
    (hvariation : 0 < variationScale)
    (htargetRobust : targetScale.1 < robustScale.1)
    (K : ℕ) (hK : 0 < K)
    (htargetAligned : targetScale.1 = (K : ℝ) * delta)
    (htargetNormalizationStep :
      targetReentry.reentryNormalizationLoss ≤ targetStepOutputLoss)
    (htargetStepOutputLoss : 0 < targetStepOutputLoss)
    (htargetReentryInnerOutput : targetReentryLoss ≤ innerOutputLoss)
    (hinnerOutputLoss : 0 < innerOutputLoss)
    (hdeltaStrict : delta < 1)
    (hinnerSlack :
      proposition63Lemma43MassLoss
          (wz2PaperPureRefinementFraction delta 61 *
            Kakeya.realRpowENN targetScale.1 (2 * targetLoss))
          (27 * (2 *
            (wz1OrientationCapCount
              (10 * (incidence + targetScale.1 / 2) /
                (robustScale.1 - targetScale.1)) variationScale :
                  ENNReal))) *
          Kakeya.realRpowENN delta targetStepOutputLoss ≤
        Kakeya.realRpowENN delta
          targetReentry.reentryNormalizationLoss)
    (htargetDensityLift :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (targetReentry.regularized.regularizationLoss *
            targetReentry.weightUpper) *
          Kakeya.realRpowENN delta innerOutputLoss ≤
        targetReentry.normalizationWeight *
          Kakeya.realRpowENN delta targetStepOutputLoss)
    (hcurrentOutput : currentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (houterSlack :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (firstReentry.regularized.regularizationLoss *
            firstReentry.weightUpper) *
          Kakeya.realRpowENN delta outputLoss ≤
        firstReentry.normalizationWeight *
          Kakeya.realRpowENN delta innerOutputLoss) :
    Nonempty (Proposition63ExtremalOneScalePlaneMapData
      current currentMap outputLoss targetScale.1 variationScale) := by
  let normalizedMap := firstReentry.normalizedPlaneMap currentMap
  let outerAmbient : WZ1PaperTubeShading
      firstReentry.normalization.croppedFamily :=
    extendShading outer.data.selected outer.data.refined
  have outerAmbientSub : PaperIsSubshading outerAmbient
      firstReentry.normalization.croppedRefined :=
    extendShading_subshading outer.data.selected outer.data.subshading
  let outerMap := paperWeakPlaneMapRestrict normalizedMap outerAmbientSub
  have outerCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        outerMap.planeMap first = outerMap.planeMap second := by
    intro first second sameCell
    exact currentCellwise first second sameCell
  rcases proposition63_extremal_one_scale_plane_map_of_two_rich
      outer targetReentry htargetReentryLoss target outerMap outerCellwise
      hdeltaSmall hrobustSmall hterminalScalar hincidence hvariation
      htargetRobust K hK htargetAligned htargetNormalizationStep
      htargetStepOutputLoss htargetReentryInnerOutput hinnerOutputLoss
      hdeltaStrict hinnerSlack htargetDensityLift with
    ⟨inner⟩
  apply firstReentry.liftExtremalOneScalePlaneMap currentExtremal currentMap
    outerAmbientSub outerMap rfl inner
    (wz2PaperPureRefinementFraction delta 61)
  · unfold wz2PaperPureRefinementFraction
    exact ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top) 61
  · unfold wz2PaperPureRefinementFraction
    apply ENNReal.pow_ne_top
    apply ENNReal.inv_ne_top.mpr
    exact (ENNReal.ofReal_pos.mpr <| Real.log_pos <|
      one_lt_one_div currentExtremal.delta_pos hdeltaStrict).ne'
  · rw [extendShading_mass]
    exact outer.total_mass_retention
  · exact hcurrentOutput
  · exact houtputLoss
  · exact houterSlack

/-- The complete nested two-rich step after all three extremality restorations
have been reduced to family-free pre-runtime receipts. -/
theorem proposition63_extremal_one_scale_plane_map_of_nested_two_rich_absorbed
    {delta sigma initialInputLoss normalizationLoss firstReentryLoss
      currentLoss robustExponent outerLoss targetReentryLoss targetLoss
      targetStepOutputLoss innerOutputLoss outputLoss firstWeightLoss
      targetWeightLoss incidence variationScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent firstLevelCount targetLevelCount : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (currentExtremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      initialNormalized.croppedFamily current)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (currentCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        currentMap.planeMap first = currentMap.planeMap second)
    (firstReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := firstReentryLoss) initialNormalized current)
    (hfirstReentryLoss : 0 < firstReentryLoss)
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) firstReentry.normalization.croppedRefined
      (firstReentry.normalization.toPropStickyReentryData
        hfirstReentryLoss firstReentry.reentry_normalization_loss_pos)
      robustScale)
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) firstReentry.normalization
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (terminalAbsorption : Proposition63TwoRichTerminalScalarAbsorptionData
      sigma robustExponent outerLoss targetReentry.reentryNormalizationLoss
      targetWeightLoss targetLevelCount)
    (targetStepAbsorption : Proposition63TargetStepAbsorptionData
      targetReentry.reentryNormalizationLoss targetLoss robustExponent
      targetStepOutputLoss)
    (targetLiftAbsorption : Proposition63ReentryDensityLiftAbsorptionData
      targetWeightLoss targetStepOutputLoss innerOutputLoss targetLevelCount)
    (firstLiftAbsorption : Proposition63ReentryDensityLiftAbsorptionData
      firstWeightLoss innerOutputLoss outputLoss firstLevelCount)
    (hdeltaTerminal : delta ≤ terminalAbsorption.delta₀)
    (hdeltaStep : delta ≤ targetStepAbsorption.delta₀)
    (hdeltaTargetLift : delta ≤ targetLiftAbsorption.delta₀)
    (hdeltaFirstLift : delta ≤ firstLiftAbsorption.delta₀)
    (hrobustScale : robustScale.1 = Real.rpow delta robustExponent)
    (hfirstWeight : firstReentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta firstWeightLoss)
    (hfirstWeightUpper : firstReentry.weightUpper =
      (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2)
    (hfirstLevelCount : firstReentry.levelCount = firstLevelCount)
    (htargetWeight : targetReentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta targetWeightLoss)
    (htargetWeightUpper : targetReentry.weightUpper =
      (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2)
    (htargetLevelCount : targetReentry.levelCount = targetLevelCount)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hincidence : 0 ≤ incidence)
    (hincidenceTarget : incidence ≤ targetScale.1)
    (hvariation : 0 < variationScale)
    (hvariationEq : variationScale = targetScale.1)
    (htargetLower : Real.rpow delta (1 - targetLoss) ≤ targetScale.1)
    (htargetUpper : targetScale.1 ≤ Real.rpow delta targetLoss)
    (htargetSeparation : 16 * targetScale.1 ≤ robustScale.1)
    (K : ℕ) (hK : 0 < K)
    (htargetAligned : targetScale.1 = (K : ℝ) * delta)
    (htargetReentryInnerOutput : targetReentryLoss ≤ innerOutputLoss)
    (hinnerOutputLoss : 0 < innerOutputLoss)
    (hcurrentOutput : currentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss) :
    Nonempty (Proposition63ExtremalOneScalePlaneMapData
      current currentMap outputLoss targetScale.1 variationScale) := by
  have terminalScalar :=
    proposition63_two_rich_terminal_scalar_of_absorption outer targetReentry
      htargetReentryLoss target terminalAbsorption hdeltaTerminal
      hrobustScale htargetWeight htargetWeightUpper htargetLevelCount
  have targetStepSlack := targetStepAbsorption.absorb targetScale
    targetReentry.reentry_extremal.delta_pos hdeltaStep hrobustScale
    hincidence hincidenceTarget htargetLower htargetUpper
    htargetSeparation hvariationEq
  have targetDensityLift := targetReentry.densityLift_of_absorption
    targetLiftAbsorption hdeltaTargetLift htargetWeight
      htargetWeightUpper htargetLevelCount
  have firstDensityLift := firstReentry.densityLift_of_absorption
    firstLiftAbsorption hdeltaFirstLift hfirstWeight hfirstWeightUpper
      hfirstLevelCount
  exact proposition63_extremal_one_scale_plane_map_of_nested_two_rich
    currentExtremal currentMap currentCellwise firstReentry hfirstReentryLoss
    outer targetReentry htargetReentryLoss target
    (hdeltaTerminal.trans terminalAbsorption.delta₀_le_tiny |>.trans
      (by norm_num))
    hrobustSmall terminalScalar hincidence hvariation
    (by linarith) K hK htargetAligned
    targetStepAbsorption.source_lt_output.le
    (targetReentry.reentry_normalization_loss_pos.trans
      targetStepAbsorption.source_lt_output)
    htargetReentryInnerOutput
    hinnerOutputLoss
    (hdeltaTerminal.trans terminalAbsorption.delta₀_le_tiny |>.trans_lt
      (by norm_num))
    targetStepSlack targetDensityLift hcurrentOutput houtputLoss
      firstDensityLift

/-- Public one-scale schedule with the paper quantifier order.  The complete
loss hierarchy and every scalar threshold are fixed before the runtime root,
current shading, plane map, and aligned target scale. -/
structure Proposition63ExtremalOneScalePlaneMapScheduleData
    (sigma outputLoss : ℝ) where
  rootSourceLoss : ℝ
  rootNormalizationLoss : ℝ
  rootDensityLoss : ℝ
  inputLoss : ℝ
  delta₀ : ℝ
  rootSourceLoss_pos : 0 < rootSourceLoss
  rootNormalizationLoss_pos : 0 < rootNormalizationLoss
  rootSourceLoss_le_half : rootSourceLoss ≤ rootNormalizationLoss / 2
  rootDensityLoss_pos : 0 < rootDensityLoss
  inputLoss_pos : 0 < inputLoss
  inputLoss_le_output : inputLoss ≤ outputLoss
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  run :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {ambientSourceLoss ambientNormalizationLoss : ℝ}
        {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
        {ambientShading : WZ1PaperTubeShading ambientFamily},
        ∀ (ambientReentry : PureWZ2PropStickyReentryData
          (sigma := sigma) ambientShading 0 ambientSourceLoss
            ambientNormalizationLoss),
          ∀ (hambientSource : ambientSourceLoss ≤ rootSourceLoss)
            (hambientNormalization :
              ambientNormalizationLoss ≤ rootNormalizationLoss),
          ∀ (current : WZ1PaperTubeShading ambientFamily),
            WZ2PaperCroppedIsExtremal sigma inputLoss
              ambientFamily current →
            PaperIsSubshading current ambientShading →
            ∀ {incidence : ℝ},
              ∀ (currentMap : PaperWZ1WeakPlaneMapData current incidence),
                (∀ first second,
                  wz1PaperGridIndex delta first =
                      wz1PaperGridIndex delta second →
                    currentMap.planeMap first = currentMap.planeMap second) →
                0 ≤ incidence →
                ∀ targetScale : WZ2PaperRequestedScale delta,
                  Real.rpow delta (1 - outputLoss) ≤ targetScale.1 →
                  targetScale.1 ≤ Real.rpow delta outputLoss →
                  incidence ≤ targetScale.1 →
                  ∀ K : ℕ, 0 < K →
                    targetScale.1 = (K : ℝ) * delta →
                    Nonempty (Proposition63ExtremalOneScalePlaneMapData
                      (initialNormalized :=
                        (ambientReentry.mono_losses
                          hambientSource hambientNormalization rootSourceLoss_pos
                            rootNormalizationLoss_pos
                            rootSourceLoss_le_half).toNormalizationData)
                      current currentMap outputLoss targetScale.1 targetScale.1)

/-- Construct the full one-scale producer for losses at most one.  The
returned `inputLoss` is selected only after both rich Node 3 schedules have
been fixed, and every subsequent threshold is folded into one `delta₀`. -/
theorem proposition63_extremal_one_scale_plane_map_schedule
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ) (houtputLoss : 0 < outputLoss)
    (houtputLossOne : outputLoss ≤ 1) :
    Nonempty (Proposition63ExtremalOneScalePlaneMapScheduleData
      sigma outputLoss) := by
  let robustExponent : ℝ := outputLoss / 32
  let targetLoss : ℝ := outputLoss * sigma / 1024
  have robustExponentPos : 0 < robustExponent := by positivity
  have robustExponentOne : robustExponent ≤ 1 := by
    dsimp only [robustExponent]
    linarith
  have targetLossPos : 0 < targetLoss := by
    dsimp only [targetLoss]
    exact div_pos (mul_pos houtputLoss critical.sigma_pos) (by norm_num)
  have targetLossOne : targetLoss ≤ 1 := by
    dsimp only [targetLoss]
    nlinarith [critical.sigma_pos, critical.sigma_lt_one]
  have targetLossLeOutput : targetLoss ≤ outputLoss := by
    dsimp only [targetLoss]
    have sigmaLe : sigma ≤ 1024 := by
      linarith [critical.sigma_lt_one]
    calc
      outputLoss * sigma / 1024 ≤ outputLoss * 1024 / 1024 := by
        gcongr
      _ = outputLoss := by ring
  rcases proposition63_rich_two_call_schedule sigma critical targetLoss
      targetLossPos targetLossOne with ⟨richSchedule⟩
  let secondSource : ℝ := richSchedule.second.sourceLoss
  let firstSource : ℝ := richSchedule.first.sourceLoss
  let firstNormalization : ℝ := richSchedule.first.normalizationLoss
  let rootNormalizationLoss : ℝ := firstSource / 16
  let rootSourceLoss : ℝ := rootNormalizationLoss / 4
  let rootDensityLoss : ℝ := rootNormalizationLoss / 2
  let inputLoss : ℝ := rootNormalizationLoss
  let firstWeightLoss : ℝ := 2 * rootNormalizationLoss
  let outerExtremalLoss : ℝ := secondSource / 8
  let targetDensityLoss : ℝ := secondSource / 4
  let targetWeightLoss : ℝ := secondSource / 2
  let targetStepOutputLoss : ℝ := outputLoss / 4
  let innerOutputLoss : ℝ := outputLoss / 2
  let firstLevelCount :=
    proposition63CanonicalNearbyLevelCount rootNormalizationLoss
  let targetLevelCount :=
    proposition63CanonicalNearbyLevelCount firstNormalization
  have secondSourcePos : 0 < secondSource :=
    richSchedule.second.sourceLoss_pos
  have firstSourcePos : 0 < firstSource :=
    richSchedule.first.sourceLoss_pos
  have firstNormalizationPos : 0 < firstNormalization :=
    richSchedule.first.normalizationLoss_pos
  have rootNormalizationLossPos : 0 < rootNormalizationLoss := by
    dsimp only [rootNormalizationLoss]
    positivity
  have rootSourceLossPos : 0 < rootSourceLoss := by
    dsimp only [rootSourceLoss]
    positivity
  have rootDensityLossPos : 0 < rootDensityLoss := by
    dsimp only [rootDensityLoss]
    positivity
  have inputLossPos : 0 < inputLoss := by
    dsimp only [inputLoss]
    exact rootNormalizationLossPos
  have firstLevelCountPos : 0 < firstLevelCount :=
    proposition63CanonicalNearbyLevelCount_pos rootNormalizationLossPos
  have targetLevelCountPos : 0 < targetLevelCount :=
    proposition63CanonicalNearbyLevelCount_pos firstNormalizationPos
  have firstOutputEq :
      richSchedule.firstOutputLoss = secondSource / 16 := by
    simpa only [secondSource] using richSchedule.firstOutputLoss_eq
  have secondSourceLeTarget : secondSource ≤ targetLoss / 2 := by
    have sourceLe := richSchedule.second.sourceLoss_le_half
    have normalizationLt := richSchedule.second.normalizationLoss_lt_output
    dsimp only [secondSource]
    linarith
  have firstSourceLtSecond : firstSource < secondSource := by
    have firstNormalizationLt :
        firstNormalization < richSchedule.firstOutputLoss :=
      richSchedule.first.normalizationLoss_lt_output
    have firstSourceLe : firstSource ≤ firstNormalization / 2 :=
      richSchedule.first.sourceLoss_le_half
    dsimp only [firstSource, firstNormalization, secondSource] at *
    linarith [firstOutputEq]
  have rootSourceDensity : rootSourceLoss < rootDensityLoss := by
    dsimp only [rootSourceLoss, rootDensityLoss]
    linarith
  have firstDensityWeight :
      rootDensityLoss + inputLoss < firstWeightLoss := by
    dsimp only [rootDensityLoss, inputLoss, firstWeightLoss]
    linarith
  have firstWeightReentry : firstWeightLoss < firstSource := by
    dsimp only [firstWeightLoss, rootNormalizationLoss]
    linarith [firstSourcePos]
  have firstRegularizationGap :
      0 < firstSource - firstWeightLoss - 2 * rootNormalizationLoss := by
    dsimp only [firstWeightLoss, rootNormalizationLoss]
    linarith [firstSourcePos]
  rcases proposition63_current_reentry_absorption
      rootSourceLoss rootNormalizationLoss rootDensityLoss inputLoss
      firstWeightLoss firstSource firstLevelCount rootSourceDensity
      rootNormalizationLossPos firstDensityWeight firstWeightReentry
      firstLevelCountPos firstSourcePos firstRegularizationGap with
    ⟨firstReentryAbsorption⟩
  have targetSourceDensity : firstSource < targetDensityLoss := by
    have firstNormalizationLt :
        firstNormalization < richSchedule.firstOutputLoss :=
      richSchedule.first.normalizationLoss_lt_output
    have firstSourceLe : firstSource ≤ firstNormalization / 2 :=
      richSchedule.first.sourceLoss_le_half
    dsimp only [targetDensityLoss, secondSource, firstSource,
      firstNormalization] at *
    linarith [firstOutputEq]
  have targetDensityWeight :
      targetDensityLoss + outerExtremalLoss < targetWeightLoss := by
    dsimp only [targetDensityLoss, outerExtremalLoss, targetWeightLoss]
    linarith
  have targetWeightReentry : targetWeightLoss < secondSource := by
    dsimp only [targetWeightLoss]
    linarith
  have targetRegularizationGap :
      0 < secondSource - targetWeightLoss - 2 * firstNormalization := by
    have firstNormalizationLt :
        firstNormalization < richSchedule.firstOutputLoss :=
      richSchedule.first.normalizationLoss_lt_output
    dsimp only [targetWeightLoss, secondSource, firstNormalization] at *
    linarith [firstOutputEq]
  rcases proposition63_current_reentry_absorption
      firstSource firstNormalization targetDensityLoss outerExtremalLoss
      targetWeightLoss secondSource targetLevelCount targetSourceDensity
      firstNormalizationPos targetDensityWeight targetWeightReentry
      targetLevelCountPos secondSourcePos targetRegularizationGap with
    ⟨targetReentryAbsorption⟩
  have outerRetentionGap : firstNormalization < outerExtremalLoss := by
    have firstNormalizationLt :
        firstNormalization < richSchedule.firstOutputLoss :=
      richSchedule.first.normalizationLoss_lt_output
    dsimp only [outerExtremalLoss, secondSource, firstNormalization] at *
    linarith [firstOutputEq]
  rcases proposition63_refinement_retention_absorption firstNormalization
      outerExtremalLoss 61 outerRetentionGap (by norm_num) with
    ⟨outerRetentionAbsorption⟩
  have terminalGap : 0 < robustExponent * sigma -
      richSchedule.firstOutputLoss -
      2 * richSchedule.second.normalizationLoss - targetWeightLoss := by
    have secondNormalizationLt :=
      richSchedule.second.normalizationLoss_lt_output
    have secondSourceLe := richSchedule.second.sourceLoss_le_half
    dsimp only [robustExponent, targetLoss, targetWeightLoss, secondSource] at *
    nlinarith [critical.sigma_pos, critical.sigma_lt_one, firstOutputEq]
  rcases proposition63_two_rich_terminal_scalar_absorption sigma
      robustExponent richSchedule.firstOutputLoss
      richSchedule.second.normalizationLoss targetWeightLoss
      targetLevelCount robustExponentPos.le robustExponentOne terminalGap with
    ⟨terminalAbsorption⟩
  have targetStepGap : 0 < targetStepOutputLoss -
      richSchedule.second.normalizationLoss - 3 * robustExponent -
      (1 - targetLoss) * (2 * targetLoss) := by
    have secondNormalizationLt :=
      richSchedule.second.normalizationLoss_lt_output
    dsimp only [targetStepOutputLoss, robustExponent, targetLoss] at *
    nlinarith [critical.sigma_pos, critical.sigma_lt_one]
  rcases proposition63_target_step_absorption
      richSchedule.second.normalizationLoss targetLoss robustExponent
      targetStepOutputLoss targetLossPos targetLossOne robustExponentPos
      targetStepGap with ⟨targetStepAbsorption⟩
  have targetLiftGap :
      0 < innerOutputLoss - targetStepOutputLoss - targetWeightLoss := by
    have secondNormalizationLt :=
      richSchedule.second.normalizationLoss_lt_output
    have secondSourceLe := richSchedule.second.sourceLoss_le_half
    dsimp only [innerOutputLoss, targetStepOutputLoss, targetWeightLoss,
      secondSource, targetLoss] at *
    nlinarith [critical.sigma_pos, critical.sigma_lt_one]
  rcases proposition63_reentry_density_lift_absorption targetWeightLoss
      targetStepOutputLoss innerOutputLoss targetLevelCount targetLiftGap with
    ⟨targetLiftAbsorption⟩
  have firstLiftGap :
      0 < outputLoss - innerOutputLoss - firstWeightLoss := by
    have firstNormalizationLt :
        firstNormalization < richSchedule.firstOutputLoss :=
      richSchedule.first.normalizationLoss_lt_output
    have firstSourceLe : firstSource ≤ firstNormalization / 2 :=
      richSchedule.first.sourceLoss_le_half
    have secondNormalizationLt :=
      richSchedule.second.normalizationLoss_lt_output
    have secondSourceLe := richSchedule.second.sourceLoss_le_half
    dsimp only [innerOutputLoss, firstWeightLoss, rootNormalizationLoss,
      firstSource, firstNormalization, secondSource, targetLoss] at *
    nlinarith [critical.sigma_pos, critical.sigma_lt_one, firstOutputEq]
  rcases proposition63_reentry_density_lift_absorption firstWeightLoss
      innerOutputLoss outputLoss firstLevelCount firstLiftGap with
    ⟨firstLiftAbsorption⟩
  rcases pure_wz2_exists_delta₀_rpow_le (threshold := 1 / 10000)
      (s := robustExponent) (by norm_num) robustExponentPos with
    ⟨robustSmallDelta, robustSmallDeltaPos, robustSmallDeltaOne,
      robustSmall⟩
  have robustOutput : robustExponent < outputLoss := by
    dsimp only [robustExponent]
    linarith
  rcases exists_delta_mul_rpow_le_rpow (16 : ℝ) (by norm_num)
      robustOutput with
    ⟨separationDelta, separationDeltaPos, separationDeltaOne, separation⟩
  have inputLossLeOutput : inputLoss ≤ outputLoss := by
    have firstNormalizationLt :
        firstNormalization < richSchedule.firstOutputLoss :=
      richSchedule.first.normalizationLoss_lt_output
    have firstSourceLe : firstSource ≤ firstNormalization / 2 :=
      richSchedule.first.sourceLoss_le_half
    dsimp only [inputLoss, rootNormalizationLoss, firstSource,
      firstNormalization] at *
    linarith [firstOutputEq, secondSourceLeTarget, targetLossLeOutput]
  let delta₀ := min richSchedule.first.delta₀ <|
    min richSchedule.second.delta₀ <|
    min firstReentryAbsorption.delta₀ <|
    min targetReentryAbsorption.delta₀ <|
    min outerRetentionAbsorption.delta₀ <|
    min terminalAbsorption.delta₀ <|
    min targetStepAbsorption.delta₀ <|
    min targetLiftAbsorption.delta₀ <|
    min firstLiftAbsorption.delta₀ <|
    min robustSmallDelta separationDelta
  refine ⟨{
    rootSourceLoss := rootSourceLoss
    rootNormalizationLoss := rootNormalizationLoss
    rootDensityLoss := rootDensityLoss
    inputLoss := inputLoss
    delta₀ := delta₀
    rootSourceLoss_pos := rootSourceLossPos
    rootNormalizationLoss_pos := rootNormalizationLossPos
    rootSourceLoss_le_half := by
      dsimp only [rootSourceLoss, rootNormalizationLoss]
      linarith [rootNormalizationLossPos]
    rootDensityLoss_pos := rootDensityLossPos
    inputLoss_pos := inputLossPos
    inputLoss_le_output := inputLossLeOutput
    delta₀_pos := by
      dsimp only [delta₀]
      exact lt_min richSchedule.first.delta₀_pos <|
        lt_min richSchedule.second.delta₀_pos <|
        lt_min firstReentryAbsorption.delta₀_pos <|
        lt_min targetReentryAbsorption.delta₀_pos <|
        lt_min outerRetentionAbsorption.delta₀_pos <|
        lt_min terminalAbsorption.delta₀_pos <|
        lt_min targetStepAbsorption.delta₀_pos <|
        lt_min targetLiftAbsorption.delta₀_pos <|
        lt_min firstLiftAbsorption.delta₀_pos <|
        lt_min robustSmallDeltaPos separationDeltaPos
    delta₀_le_one := (min_le_left _ _).trans richSchedule.first.delta₀_le_one
    run := ?_
  }⟩
  intro delta deltaPos deltaLe ambientSourceLoss ambientNormalizationLoss
    ambientFamily ambientShading ambientReentry ambientSourceLe
    ambientNormalizationLe current currentExtremal currentSub incidence
    currentMap currentCellwise incidenceNonnegative targetScale
    targetLower targetUpper incidenceTarget K KPos targetAligned
  have deltaLeFirstSchedule : delta ≤ richSchedule.first.delta₀ :=
    deltaLe.trans <| by dsimp only [delta₀]; exact min_le_left _ _
  have deltaLeSecondSchedule : delta ≤ richSchedule.second.delta₀ :=
    deltaLe.trans <| by
      dsimp only [delta₀]
      exact (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeFirstReentry : delta ≤ firstReentryAbsorption.delta₀ :=
    deltaLe.trans <| by
      dsimp only [delta₀]
      exact (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeTargetReentry : delta ≤ targetReentryAbsorption.delta₀ :=
    deltaLe.trans <| by
      dsimp only [delta₀]
      exact (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeOuterRetention : delta ≤ outerRetentionAbsorption.delta₀ :=
    deltaLe.trans <| by
      dsimp only [delta₀]
      exact (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeTerminal : delta ≤ terminalAbsorption.delta₀ :=
    deltaLe.trans <| by
      dsimp only [delta₀]
      exact (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeTargetStep : delta ≤ targetStepAbsorption.delta₀ :=
    deltaLe.trans <| by
      dsimp only [delta₀]
      exact (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeTargetLift : delta ≤ targetLiftAbsorption.delta₀ :=
    deltaLe.trans <| by
      dsimp only [delta₀]
      exact (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans <|
            (min_le_right _ _).trans <|
              (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeFirstLift : delta ≤ firstLiftAbsorption.delta₀ :=
    deltaLe.trans <| by
      dsimp only [delta₀]
      exact (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans <|
            (min_le_right _ _).trans <| (min_le_right _ _).trans <|
              (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeRobustSmall : delta ≤ robustSmallDelta :=
    deltaLe.trans <| by
      dsimp only [delta₀]
      exact (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans <|
            (min_le_right _ _).trans <| (min_le_right _ _).trans <|
              (min_le_right _ _).trans <| (min_le_right _ _).trans <|
                (min_le_left _ _)
  have deltaLeSeparation : delta ≤ separationDelta :=
    deltaLe.trans <| by
      dsimp only [delta₀]
      exact (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans <|
            (min_le_right _ _).trans <| (min_le_right _ _).trans <|
              (min_le_right _ _).trans <| (min_le_right _ _).trans <|
                (min_le_right _ _)
  have deltaOne : delta ≤ 1 :=
    deltaLeFirstSchedule.trans richSchedule.first.delta₀_le_one
  have deltaStrict : delta < 1 :=
    deltaLeTerminal.trans_lt <|
      terminalAbsorption.delta₀_le_tiny.trans_lt (by norm_num)
  let scheduledReentry := ambientReentry.mono_losses ambientSourceLe
    ambientNormalizationLe rootSourceLossPos rootNormalizationLossPos
      (show rootSourceLoss ≤ rootNormalizationLoss / 2 by
        dsimp only [rootSourceLoss, rootNormalizationLoss]
        linarith [rootNormalizationLossPos])
  let root : Proposition63RootNormalizationData
      (outputLoss := rootNormalizationLoss) scheduledReentry.ordinarySource 0
      rootDensityLoss :=
    Proposition63RootNormalizationData.ofPropStickyReentry scheduledReentry
      (firstReentryAbsorption.density_absorb deltaPos
        deltaLeFirstReentry)
  have firstAmbientTwo := firstReentryAbsorption.ambient_two deltaPos
    deltaLeFirstReentry
  rcases root.finiteNearbySchedule rootNormalizationLossPos firstAmbientTwo
      (show 2 * rootNormalizationLoss ≤ firstSource by
        dsimp only [rootNormalizationLoss]
        linarith [firstSourcePos]) with ⟨firstNearbySchedule⟩
  have firstRegularization :=
    firstReentryAbsorption.regularization_absorb root.normalization
      rfl firstNearbySchedule rfl rfl deltaPos deltaLeFirstReentry
  rcases root.currentShadingReentryFromExtremal current firstNearbySchedule
      firstAmbientTwo currentExtremal
      (show inputLoss ≤ firstSource by
        dsimp only [inputLoss, rootNormalizationLoss]
        linarith [firstSourcePos]) inputLossPos firstNormalization
      firstNormalizationPos richSchedule.first.sourceLoss_le_half
      (firstReentryAbsorption.canonical_weight_absorb deltaPos
        deltaLeFirstReentry)
      (firstReentryAbsorption.trace_fixed_absorb deltaPos
        deltaLeFirstReentry)
      (firstReentryAbsorption.paper_fixed_absorb deltaPos
        deltaLeFirstReentry)
      firstRegularization currentSub currentExtremal.cubical
      (deltaLeFirstReentry.trans firstReentryAbsorption.delta₀_le_tiny |>.trans
        (by norm_num)) with
    ⟨firstReentry, firstWeightEq, firstWeightUpper, firstLevelEq,
      firstNormalizationEq⟩
  subst firstNormalization
  have targetDensityAbsorb :=
    targetReentryAbsorption.density_absorb deltaPos deltaLeTargetReentry
  let targetRoot : Proposition63RootNormalizationData
      (outputLoss := firstReentry.reentryNormalizationLoss)
      firstReentry.ordinarySource 0
      targetDensityLoss :=
    Proposition63RootNormalizationData.ofNormalization
      firstReentry.normalization targetDensityAbsorb
  have targetAmbientTwo :=
    targetReentryAbsorption.ambient_two deltaPos deltaLeTargetReentry
  have targetActualNormalizationPos :
      0 < firstReentry.reentryNormalizationLoss :=
    firstReentry.reentry_normalization_loss_pos
  have targetAmbientTwoActual : (2 : ENNReal) <
      Kakeya.realRpowENN delta
        (-firstReentry.reentryNormalizationLoss) := by
    simpa only [firstNormalizationEq] using targetAmbientTwo
  have targetWindowReach :
      2 * firstReentry.reentryNormalizationLoss ≤ secondSource := by
    have firstNormalizationLt :
        richSchedule.first.normalizationLoss <
          richSchedule.firstOutputLoss :=
      richSchedule.first.normalizationLoss_lt_output
    dsimp only [secondSource]
    linarith [firstOutputEq]
  rcases targetRoot.finiteNearbySchedule targetActualNormalizationPos
      targetAmbientTwoActual targetWindowReach with
    ⟨targetNearbyScheduleRaw⟩
  have targetRootFamilyEq :
      targetRoot.normalization.croppedFamily =
        firstReentry.normalization.croppedFamily := rfl
  have targetNearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := firstReentry.normalization.croppedFamily)
      (Kakeya.realRpowENN delta
        (-firstReentry.reentryNormalizationLoss))
      (Kakeya.realRpowENN delta (-richSchedule.second.sourceLoss))
      (proposition63CanonicalNearbyLevelCount
        firstReentry.reentryNormalizationLoss) := by
    simpa only [secondSource, firstNormalizationEq, targetRootFamilyEq]
      using targetNearbyScheduleRaw
  let robustScale : WZ2PaperRequestedScale delta :=
    ⟨Real.rpow delta robustExponent,
      by
        have := Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne
          robustExponentOne
        simpa using this,
      Real.rpow_le_one deltaPos.le deltaOne robustExponentPos.le⟩
  have firstOutputLeRobustExponent :
      richSchedule.firstOutputLoss ≤ robustExponent := by
    dsimp only [robustExponent]
    linarith [firstOutputEq, secondSourceLeTarget, targetLossLeOutput]
  have robustExponentLeOneSubFirstOutput :
      robustExponent ≤ 1 - richSchedule.firstOutputLoss := by
    have robustExponentLeHalf : robustExponent ≤ 1 / 2 := by
      dsimp only [robustExponent]
      linarith
    linarith [firstOutputLeRobustExponent]
  have robustLower :
      Real.rpow delta (1 - richSchedule.firstOutputLoss) ≤ robustScale.1 := by
    apply Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne
    exact robustExponentLeOneSubFirstOutput
  have robustUpper : robustScale.1 ≤
      Real.rpow delta richSchedule.firstOutputLoss := by
    apply Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne
    exact firstOutputLeRobustExponent
  have targetWindowLower :
      Real.rpow delta (1 - targetLoss) ≤ targetScale.1 := by
    apply (Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne ?_).trans
      targetLower
    linarith [targetLossLeOutput]
  have targetWindowUpper : targetScale.1 ≤
      Real.rpow delta targetLoss := by
    apply targetUpper.trans
    apply Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne
    exact targetLossLeOutput
  have outerRetention := outerRetentionAbsorption.absorb deltaPos
    deltaLeOuterRetention
  have targetRegularization :=
    targetReentryAbsorption.regularization_absorb firstReentry.normalization
      firstNormalizationEq targetNearbySchedule rfl (by
        dsimp only [targetLevelCount]
        rw [firstNormalizationEq]) deltaPos deltaLeTargetReentry
  rcases proposition63_nested_two_rich_runtime
      (densityLoss := targetDensityLoss) (weightLoss := targetWeightLoss)
      (outerExtremalLoss := outerExtremalLoss) firstReentry
      richSchedule.first rfl firstNormalizationEq deltaLeFirstSchedule
      (robustScale := robustScale) robustLower robustUpper richSchedule.second
      deltaLeSecondSchedule targetDensityAbsorb targetNearbySchedule
      targetAmbientTwoActual
      (show firstReentry.reentryNormalizationLoss ≤ outerExtremalLoss by
        rw [firstNormalizationEq]
        exact outerRetentionGap.le)
      (show 0 < outerExtremalLoss by
        dsimp only [outerExtremalLoss]
        positivity) (by
          simpa only [firstNormalizationEq] using outerRetention)
      (show outerExtremalLoss ≤ secondSource by
        dsimp only [outerExtremalLoss]
        linarith [secondSourcePos])
      (targetReentryAbsorption.canonical_weight_absorb deltaPos
        deltaLeTargetReentry)
      (targetReentryAbsorption.trace_fixed_absorb deltaPos
        deltaLeTargetReentry)
      (targetReentryAbsorption.paper_fixed_absorb deltaPos
        deltaLeTargetReentry) targetRegularization
      (deltaLeTargetReentry.trans targetReentryAbsorption.delta₀_le_tiny |>.trans
        (by norm_num)) (targetScale := targetScale) targetWindowLower
      targetWindowUpper with
    ⟨outer, targetReentry, targetWeightEq, targetWeightUpper, targetLevelEq,
      targetNormalizationEq, ⟨target⟩⟩
  have terminalAbsorptionExists :
      ∃ absorption : Proposition63TwoRichTerminalScalarAbsorptionData
          sigma robustExponent richSchedule.firstOutputLoss
          targetReentry.reentryNormalizationLoss targetWeightLoss
          targetLevelCount,
        delta ≤ absorption.delta₀ := by
    rw [targetNormalizationEq]
    exact ⟨terminalAbsorption, deltaLeTerminal⟩
  rcases terminalAbsorptionExists with
    ⟨terminalAbsorption', deltaLeTerminal'⟩
  have targetStepAbsorptionExists :
      ∃ absorption : Proposition63TargetStepAbsorptionData
          targetReentry.reentryNormalizationLoss targetLoss robustExponent
          targetStepOutputLoss,
        delta ≤ absorption.delta₀ := by
    rw [targetNormalizationEq]
    exact ⟨targetStepAbsorption, deltaLeTargetStep⟩
  rcases targetStepAbsorptionExists with
    ⟨targetStepAbsorption', deltaLeTargetStep'⟩
  have targetLevelEq' : targetReentry.levelCount = targetLevelCount := by
    rw [targetLevelEq]
    dsimp only [targetLevelCount]
    rw [firstNormalizationEq]
  have robustSmallBound : robustScale.1 ≤ 1 / 10000 := by
    exact robustSmall delta deltaPos deltaLeRobustSmall
  have targetSeparation : 16 * targetScale.1 ≤ robustScale.1 := by
    calc
      16 * targetScale.1 ≤ 16 * Real.rpow delta outputLoss := by gcongr
      _ ≤ Real.rpow delta robustExponent :=
        separation delta deltaPos deltaLeSeparation
      _ = robustScale.1 := rfl
  apply proposition63_extremal_one_scale_plane_map_of_nested_two_rich_absorbed
    currentExtremal currentMap currentCellwise firstReentry firstSourcePos
    outer targetReentry secondSourcePos target terminalAbsorption'
    targetStepAbsorption' targetLiftAbsorption firstLiftAbsorption
    deltaLeTerminal' deltaLeTargetStep' deltaLeTargetLift deltaLeFirstLift rfl
    firstWeightEq firstWeightUpper firstLevelEq targetWeightEq
    targetWeightUpper targetLevelEq' robustSmallBound incidenceNonnegative
    incidenceTarget (deltaPos.trans_le targetScale.2.1) rfl targetWindowLower
    targetWindowUpper targetSeparation K KPos targetAligned
  · dsimp only [innerOutputLoss, secondSource]
    dsimp only [secondSource] at secondSourceLeTarget
    linarith [secondSourceLeTarget, targetLossLeOutput]
  · dsimp only [innerOutputLoss]
    positivity
  · exact inputLossLeOutput
  · exact houtputLoss

end Kakeya.Assouad.PureWZ2

end
