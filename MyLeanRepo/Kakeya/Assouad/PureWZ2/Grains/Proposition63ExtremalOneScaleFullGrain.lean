import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63UniformFullGrainStepProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63Lemma43
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63AlignedPhase1Candidate
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentStepArithmetic
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ExtremalOneScalePlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63NestedPointCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RobustTauLocalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalGrainAmbientPlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SourceWitnessCoarseMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentPlaneIncidence
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FullGrainSchedule

/-!
# Extremality-restored one-scale full-grain output

This is the one-scale state transition needed by the paper Lemma 4.12
iteration.  A genuine line-hit full-grain step is first constructed on the
fresh ordinary re-entry family, then zero-extended to the current ambient
family.  Its exact one-step mass ledger is immediately converted into
cropped extremality.  No product over earlier spatial scales occurs here.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

/-- The terminal source-witness shading is itself a cropped extremal input at
any loss which is weaker than both its terminal density loss and the ambient
coarse extremality loss.  The union identity is used only for the volume
upper bound; the indexed density is the genuine terminal certificate. -/
theorem Proposition63RichTerminalStickyData.sourceWitness_extremal
    {delta sigma outputLoss sourceLoss normalizationLoss targetLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (hterminalTarget : rich.terminalLoss ≤ targetLoss)
    (houtputTarget : outputLoss ≤ targetLoss) :
    WZ2PaperCroppedIsExtremal sigma targetLoss rich.data.coarse
      rich.terminal.sourceWitness.shading := by
  let ambient := rich.data.coarse_extremal.mono_loss houtputTarget
  have hdensityPower : Kakeya.realRpowENN rho.1 targetLoss ≤
      Kakeya.realRpowENN rho.1 rich.terminalLoss := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge ambient.delta_pos
      ambient.delta_le_one hterminalTarget
  refine {
    delta_pos := ambient.delta_pos
    delta_le_one := ambient.delta_le_one
    nonempty := ambient.nonempty
    cwa_nearby_scales := ambient.cwa_nearby_scales
    cubical := rich.terminal.sourceWitness.balanced.coarse_cubical
    dense := ?_
    volume_upper := ?_
  }
  · exact (mul_le_mul_right' hdensityPower
      (wz1PaperBodyFamily rich.data.coarse).mass).trans
        rich.terminal.sourceWitness_dense
  · rw [source_witness_coarse_shading_union_eq
      rich.terminal.sourceWitness]
    exact ambient.volume_upper

/-- A point which lies in the same `rho`-cell as a source point inherits a
`1/2` lower bound for the raw extension whenever the Lipschitz error across
one coarse cell is at most `1/2`. -/
theorem PureWZ2UnitAmbientWeakPlaneMapExtension.raw_norm_half_of_same_grid_cell
    {delta incidence rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {planeMap : PaperWZ1WeakPlaneMapData shading incidence}
    {coefficient : NNReal}
    (extension : PureWZ2UnitAmbientWeakPlaneMapExtension planeMap coefficient)
    (hrho : 0 < rho)
    (hcellError :
      ((lipschitzExtensionConstant Point3 * coefficient : NNReal) : ℝ) *
        (rho * Real.sqrt 3) ≤ 1 / 2)
    {source point : Point3}
    (hsource : source ∈ shading.union)
    (hsame : wz1PaperGridIndex rho source =
      wz1PaperGridIndex rho point) :
    (1 / 2 : ℝ) ≤ ‖extension.raw.ambient.planeMap point‖ := by
  have hsourceCell : source ∈
      wz1PaperGridCube rho (wz1PaperGridIndex rho source) :=
    (mem_wz1PaperGridCube rho _ source).mpr rfl
  have hpointCell : point ∈
      wz1PaperGridCube rho (wz1PaperGridIndex rho source) :=
    (mem_wz1PaperGridCube rho _ point).mpr hsame.symm
  have hdistance : dist source point ≤ rho * Real.sqrt 3 :=
    wz1PaperGridCube_diameter hrho _ hsourceCell hpointCell
  have hmapDistance : dist (extension.raw.ambient.planeMap source)
      (extension.raw.ambient.planeMap point) ≤ 1 / 2 := by
    exact (extension.raw.lipschitz.dist_le_mul source point).trans <|
      (mul_le_mul_of_nonneg_left hdistance
        (lipschitzExtensionConstant Point3 * coefficient).coe_nonneg).trans
        hcellError
  have hsourceUnit : ‖extension.raw.ambient.planeMap source‖ = 1 := by
    rw [extension.raw.agrees ⟨source, hsource⟩]
    exact planeMap.unit source hsource
  have hreverse : ‖extension.raw.ambient.planeMap source‖ -
      ‖extension.raw.ambient.planeMap point‖ ≤
        dist (extension.raw.ambient.planeMap source)
          (extension.raw.ambient.planeMap point) := by
    simpa [dist_eq_norm] using norm_sub_norm_le
      (extension.raw.ambient.planeMap source)
      (extension.raw.ambient.planeMap point)
  rw [hsourceUnit] at hreverse
  linarith

/-- The fixed clipped extension is unit on a source-witness coarse shading
once its raw Lipschitz error across one coarse cell is at most `1/2`. -/
theorem PureWZ2UnitAmbientWeakPlaneMapExtension.unit_on_sourceWitness
    {sourceDelta rho incidence : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {planeMap : PaperWZ1WeakPlaneMapData sourceShading incidence}
    {coefficient : NNReal}
    (extension : PureWZ2UnitAmbientWeakPlaneMapExtension planeMap coefficient)
    {fine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced : PureWZ2BalancedCoverData cover fineShading coarseShading}
    (sourceWitness : PureWZ2SourceWitnessCoarseShadingData balanced)
    (hfineUnion : fineShading.union ⊆ sourceShading.union)
    (hrho : 0 < rho)
    (hcellError :
      ((lipschitzExtensionConstant Point3 * coefficient : NNReal) : ℝ) *
        (rho * Real.sqrt 3) ≤ 1 / 2) :
    ∀ point ∈ sourceWitness.shading.union,
      ‖extension.ambient.planeMap point‖ = 1 := by
  intro point hpoint
  rcases hpoint with ⟨parent, hpointParent⟩
  rw [sourceWitness.shading_carrier_eq parent] at hpointParent
  rcases Set.mem_iUnion₂.mp hpointParent with
    ⟨cell, hcell, hpointCell⟩
  rcases sourceWitness.source_witness parent cell hcell with
    ⟨source, sourcePoint, _hparent, hsourceFine, hsourceCell⟩
  have hsame : wz1PaperGridIndex rho sourcePoint =
      wz1PaperGridIndex rho point :=
    ((mem_wz1PaperGridCube rho cell sourcePoint).mp hsourceCell).trans
      ((mem_wz1PaperGridCube rho cell point).mp hpointCell).symm
  apply extension.unitOn_of_raw_norm_half sourceWitness.shading.union
    (fun query queryMem => ?_) point ⟨parent, by
      rw [sourceWitness.shading_carrier_eq parent]
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCell⟩⟩
  rcases queryMem with ⟨queryParent, hqueryParent⟩
  rw [sourceWitness.shading_carrier_eq queryParent] at hqueryParent
  rcases Set.mem_iUnion₂.mp hqueryParent with
    ⟨queryCell, hqueryCell, hqueryPointCell⟩
  rcases sourceWitness.source_witness queryParent queryCell hqueryCell with
    ⟨querySource, querySourcePoint, _hqueryParent, hqueryFine,
      hquerySourceCell⟩
  have hquerySame : wz1PaperGridIndex rho querySourcePoint =
      wz1PaperGridIndex rho query :=
    ((mem_wz1PaperGridCube rho queryCell querySourcePoint).mp
      hquerySourceCell).trans
      ((mem_wz1PaperGridCube rho queryCell query).mp
        hqueryPointCell).symm
  exact extension.raw_norm_half_of_same_grid_cell hrho hcellError
    (hfineUnion ⟨querySource, hqueryFine⟩) hquerySame

/-- Named payload for the source-witness re-entry produced after one rich
terminal.  Keeping the canonical scalar equalities beside their producer
avoids rebuilding a deeply nested dependent existential downstream. -/
structure Proposition63SourceWitnessCurrentReentryResult
    {scale sigma coarseInputLoss coarseNormalizationLoss nextSourceLoss
      nextNormalizationLoss incidence weightLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma coarseInputLoss scale}
    {normalizationExponent : ℕ}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) source normalizationExponent)
    (current : WZ1PaperTubeShading coarseNormalized.croppedFamily)
    (sourceCoefficient : NNReal) (ambientPlaneMap : Point3 → Point3) where
  currentMap : PaperWZ1WeakPlaneMapData current
    (proposition63DependentCoarseIncidence scale incidence
      (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)))
  currentReentry : Proposition63CurrentShadingReentryData
    (reentryLoss := nextSourceLoss) coarseNormalized current
  currentNormalization : currentReentry.reentryNormalizationLoss =
    nextNormalizationLoss
  currentCanonicalWeight : currentReentry.normalizationWeight =
    proposition63CanonicalReentryWeight scale weightLoss
  currentCanonicalWeightUpper : currentReentry.weightUpper =
    (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
      Kakeya.realRpowENN scale 2
  currentCanonicalLevel : currentReentry.levelCount =
    proposition63CanonicalNearbyLevelCount coarseNormalizationLoss
  currentMap_eq : currentMap.planeMap = ambientPlaneMap
  currentLipschitz : LipschitzWith
    (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient))
    currentMap.planeMap

/-- Repackage one rich terminal's exact coarse source-witness pair as the
current state used by the next inner call.  The normalization is exactly the
coarse re-entry generated by that rich call, the ancestry is identity, and
the plane map is the restriction of one fixed ambient function. -/
theorem Proposition63RichTerminalStickyData.currentReentry_on_sourceWitness
    {delta sigma outputLoss sourceLoss normalizationLoss currentLoss
      coarseRootSourceLoss coarseRootNormalizationLoss densityLoss weightLoss
      nextSourceLoss nextNormalizationLoss incidence : ℝ}
    {croppedFamily ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (rootAxialWindow : ∀ index point,
      point ∈ reentry.geometry.frame ''
          reentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8)
    {sourceMap : PaperWZ1WeakPlaneMapData ambientShading incidence}
    {sourceCoefficient : NNReal}
    (extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient)
    (hfineAmbient : rich.data.refined.union ⊆ ambientShading.union)
    (hfineIncidence : ∀ index point,
      point ∈ rich.data.refined.carrier index →
        |@Inner.inner ℝ Point3 _
          (rich.data.selected.family.tube index).direction
          (extension.ambient.planeMap point)| ≤ incidence)
    (hcellError :
      ((lipschitzExtensionConstant Point3 * sourceCoefficient : NNReal) : ℝ) *
        (rho.1 * Real.sqrt 3) ≤ 1 / 2)
    (hterminalCurrent : rich.terminalLoss ≤ currentLoss)
    (houtputCurrent : outputLoss ≤ currentLoss)
    (hcoarseSource : rich.coarseSourceLoss ≤ coarseRootSourceLoss)
    (hcoarseNormalization :
      rich.coarseNormalizationLoss ≤ coarseRootNormalizationLoss)
    (hcoarseRootSource : 0 < coarseRootSourceLoss)
    (hcoarseRootNormalization : 0 < coarseRootNormalizationLoss)
    (hcoarseRootHalf :
      coarseRootSourceLoss ≤ coarseRootNormalizationLoss / 2)
    (rootDensityAbsorb : Kakeya.realRpowENN rho.1 densityLoss ≤
      Kakeya.realRpowENN rho.1 coarseRootSourceLoss / 2)
    (nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := rich.data.coarse)
      (Kakeya.realRpowENN rho.1 (-coarseRootNormalizationLoss))
      (Kakeya.realRpowENN rho.1 (-nextSourceLoss))
      (proposition63CanonicalNearbyLevelCount coarseRootNormalizationLoss))
    (ambientTwo : (2 : ENNReal) <
      Kakeya.realRpowENN rho.1 (-coarseRootNormalizationLoss))
    (hcurrentNext : currentLoss ≤ nextSourceLoss)
    (hnextSource : 0 < nextSourceLoss)
    (hnextNormalization : 0 < nextNormalizationLoss)
    (hnextHalf : nextSourceLoss ≤ nextNormalizationLoss / 2)
    (canonicalWeightAbsorb : proposition63CanonicalReentryWeight
      rho.1 weightLoss ≤
        (100 : ENNReal)⁻¹ * Kakeya.realRpowENN rho.1 densityLoss *
          Kakeya.realRpowENN rho.1 (currentLoss + 2))
    (traceFixedAbsorb :
      (96 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN rho.1 (nextSourceLoss - weightLoss) ≤ 1)
    (paperFixedAbsorb :
      ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN rho.1 (nextSourceLoss - weightLoss) ≤
        (73 / 100 : ENNReal))
    (regularizationAbsorb :
      let degreeConstant :=
        16 * (nearbySchedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * rich.data.coarse.card) + 1 : ENNReal) ^
            nearbySchedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * rich.data.coarse.card) + 1 : ENNReal) ^
            (nearbySchedule.scaleCount + 1)
      max degreeConstant
          (((proposition63CanonicalReentryWeight rho.1 weightLoss)⁻¹ *
              (Kakeya.realRpowENN rho.1 (-coarseRootNormalizationLoss) *
                (regularizationLoss *
                  ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
                    Kakeya.realRpowENN rho.1 2)) *
                degreeConstant)) *
            Kakeya.realRpowENN rho.1 (-coarseRootNormalizationLoss)) ≤
        Kakeya.realRpowENN rho.1 (-nextSourceLoss))
    (hrhoSmall : rho.1 ≤ 1 / 24) :
    let coarseReentry := (rich.coarseReentry rootAxialWindow).mono_losses
      hcoarseSource hcoarseNormalization hcoarseRootSource
      hcoarseRootNormalization hcoarseRootHalf
    let coarseNormalized := coarseReentry.toNormalizationData
    let current := rich.terminal.sourceWitness.shading
    Nonempty (Proposition63SourceWitnessCurrentReentryResult
      (nextSourceLoss := nextSourceLoss)
      (nextNormalizationLoss := nextNormalizationLoss)
      (incidence := incidence) (weightLoss := weightLoss) coarseNormalized
      current sourceCoefficient extension.ambient.planeMap) := by
  dsimp only
  let coarseReentry := (rich.coarseReentry rootAxialWindow).mono_losses
    hcoarseSource hcoarseNormalization hcoarseRootSource
    hcoarseRootNormalization hcoarseRootHalf
  let coarseNormalized := coarseReentry.toNormalizationData
  let current := rich.terminal.sourceWitness.shading
  let coefficient : NNReal :=
    4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)
  have hunit : ∀ point ∈ current.union,
      ‖extension.ambient.planeMap point‖ = 1 :=
    extension.unit_on_sourceWitness rich.terminal.sourceWitness hfineAmbient
      rich.data.coarse_extremal.delta_pos hcellError
  let currentMap : PaperWZ1WeakPlaneMapData current
      (proposition63DependentCoarseIncidence rho.1 incidence coefficient) :=
    source_witness_coarse_weak_plane_map rich.terminal.sourceWitness
      extension.ambient.planeMap coefficient extension.lipschitz hunit
      hfineIncidence
      rich.data.coarse_extremal.delta_pos
  have currentExtremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      rich.data.coarse current :=
    rich.sourceWitness_extremal hterminalCurrent houtputCurrent
  let root : Proposition63RootNormalizationData
      (outputLoss := coarseRootNormalizationLoss)
      coarseReentry.ordinarySource 0 densityLoss :=
    Proposition63RootNormalizationData.ofPropStickyReentry coarseReentry
      rootDensityAbsorb
  have currentSub : PaperIsSubshading current
      root.normalization.croppedRefined := by
    simpa only [root, coarseNormalized, coarseReentry, current,
      Proposition63RootNormalizationData.ofPropStickyReentry,
      Proposition63RootNormalizationData.ofNormalization,
      PureWZ2PropStickyReentryData.toNormalizationData] using
        rich.terminal.sourceWitness.subshading
  rcases root.currentShadingReentryFromExtremal current nearbySchedule
      ambientTwo currentExtremal hcurrentNext
      (rich.terminalLoss_pos.trans_le hterminalCurrent)
      nextNormalizationLoss hnextNormalization hnextHalf
      canonicalWeightAbsorb traceFixedAbsorb paperFixedAbsorb
      regularizationAbsorb currentSub
      rich.terminal.sourceWitness.balanced.coarse_cubical hrhoSmall with
    ⟨currentReentry, hweight, hweightUpper, hlevel, hnormalization⟩
  exact ⟨{
    currentMap := currentMap
    currentReentry := currentReentry
    currentNormalization := hnormalization
    currentCanonicalWeight := hweight
    currentCanonicalWeightUpper := hweightUpper
    currentCanonicalLevel := hlevel
    currentMap_eq := rfl
    currentLipschitz := extension.lipschitz }⟩

/-- Concrete form of the first-cover re-entry on its actual normalized
`rho`-family.  A family-free absorption package constructs the
family-dependent nearby schedule at runtime and then invokes the low-level
ancestry-preserving re-entry theorem.  The explicit subshading premise makes
this usable by the direct first HIGH output, without lifting that output back
to an earlier root family. -/
theorem Proposition63LiftedPointCoverData.nextReentryOfAbsorption
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
    (absorption : Proposition63CurrentReentryAbsorptionData
      queryInputLoss queryNormalizationLoss rootDensityLoss firstLoss
      weightLoss reentryLoss
      (proposition63CanonicalNearbyLevelCount queryNormalizationLoss))
    (hrhoAbsorption : rho.1 ≤ absorption.delta₀)
    (hqueryNormalizationLoss : 0 < queryNormalizationLoss)
    (htwoNormalization : 2 * queryNormalizationLoss ≤ reentryLoss)
    (hfirstReentry : firstLoss ≤ reentryLoss)
    (hfirstLoss : 0 < firstLoss)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2) :
    Nonempty (Proposition63LiftedPointCoverReentryData outer
      queryNormalized current planeMap tauConstant first ancestorEmbedding
      (reentryLoss := reentryLoss)
      (reentryNormalizationLoss := reentryNormalizationLoss)
      (weightLoss := weightLoss)) := by
  let root : Proposition63RootNormalizationData
      (outputLoss := queryNormalizationLoss) querySource
      queryNormalizationExponent rootDensityLoss :=
    Proposition63RootNormalizationData.ofNormalization queryNormalized
      (absorption.density_absorb queryNormalized.final_extremal.delta_pos
        hrhoAbsorption)
  have hambientTwo := absorption.ambient_two
    queryNormalized.final_extremal.delta_pos hrhoAbsorption
  rcases root.finiteNearbySchedule hqueryNormalizationLoss hambientTwo
      htwoNormalization with ⟨nearbySchedule⟩
  have hregularization := absorption.regularization_absorb queryNormalized rfl
    nearbySchedule rfl rfl queryNormalized.final_extremal.delta_pos
    hrhoAbsorption
  exact first.nextReentry outer queryNormalized current planeMap tauConstant
    hfirstSub
    ancestorEmbedding ancestor_tube_eq current_sub_outer
    ancestorRetentionFactor ancestorRetentionFactor_pos
    ancestorRetentionFactor_ne_top current_retained_mass
    (absorption.density_absorb queryNormalized.final_extremal.delta_pos
      hrhoAbsorption) nearbySchedule hambientTwo hfirstReentry hfirstLoss
    hreentryNormalizationLoss hreentryHalf
    (absorption.canonical_weight_absorb
      queryNormalized.final_extremal.delta_pos hrhoAbsorption)
    (absorption.trace_fixed_absorb
      queryNormalized.final_extremal.delta_pos hrhoAbsorption)
    (absorption.paper_fixed_absorb
      queryNormalized.final_extremal.delta_pos hrhoAbsorption)
    hregularization
    (hrhoAbsorption.trans absorption.delta₀_le_tiny |>.trans (by norm_num))

/-- Re-enter a restored first point cover from a pre-runtime absorption
receipt and immediately run the preselected third rich terminal.  This is the
ancestry-free runtime bridge used between the two robust localizations. -/
theorem Proposition63LiftedPointCoverData.nextReentryAndThirdRichOfAbsorption
    {delta sigma inputLoss normalizationLoss firstLoss queryScale
      spatialRadius densityLoss reentryLoss reentryNormalizationLoss
      weightLoss sqrtStickyLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent)
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    {planeMap : Point3 → Point3} {constant : ENNReal}
    (first : Proposition63LiftedPointCoverData
      (outputLoss := firstLoss) (queryScale := queryScale)
      (spatialRadius := spatialRadius) initialNormalized current planeMap
      constant)
    (hfirstSub : PaperIsSubshading first.state.shading
      initialNormalized.croppedRefined)
    (absorption : Proposition63CurrentReentryAbsorptionData
      inputLoss normalizationLoss densityLoss firstLoss weightLoss reentryLoss
      (proposition63CanonicalNearbyLevelCount normalizationLoss))
    (hdeltaAbsorption : delta ≤ absorption.delta₀)
    (hnormalizationLoss : 0 < normalizationLoss)
    (htwoNormalization : 2 * normalizationLoss ≤ reentryLoss)
    (hfirstReentry : firstLoss ≤ reentryLoss)
    (hfirstLoss : 0 < firstLoss)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2)
    (richSchedule : Proposition63RichThreeCallScheduleData
      sigma sqrtStickyLoss)
    (hreentryLoss : reentryLoss = richSchedule.third.sourceLoss)
    (hthirdNormalization :
      reentryNormalizationLoss = richSchedule.third.normalizationLoss)
    (hdeltaThird : delta ≤ richSchedule.third.delta₀)
    (sqrtRequested : WZ2PaperRequestedScale delta)
    (hsqrtLower : Real.rpow delta (1 - sqrtStickyLoss) ≤ sqrtRequested.1)
    (hsqrtUpper : sqrtRequested.1 ≤ Real.rpow delta sqrtStickyLoss) :
    ∃ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) initialNormalized first.state.shading,
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
  let root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
      densityLoss :=
    Proposition63RootNormalizationData.ofNormalization initialNormalized
      (absorption.density_absorb initialNormalized.final_extremal.delta_pos
        hdeltaAbsorption)
  have ambientTwo := absorption.ambient_two
    initialNormalized.final_extremal.delta_pos hdeltaAbsorption
  rcases root.finiteNearbySchedule hnormalizationLoss ambientTwo
      htwoNormalization with ⟨nearbySchedule⟩
  have regularizationAbsorb := absorption.regularization_absorb
    initialNormalized rfl nearbySchedule rfl rfl
    initialNormalized.final_extremal.delta_pos hdeltaAbsorption
  exact first.nextReentryAndThirdRich root hfirstSub nearbySchedule ambientTwo
    hfirstReentry hfirstLoss hreentryNormalizationLoss hreentryHalf
    (absorption.canonical_weight_absorb
      initialNormalized.final_extremal.delta_pos hdeltaAbsorption)
    (absorption.trace_fixed_absorb
      initialNormalized.final_extremal.delta_pos hdeltaAbsorption)
    (absorption.paper_fixed_absorb
      initialNormalized.final_extremal.delta_pos hdeltaAbsorption)
    regularizationAbsorb
    (hdeltaAbsorption.trans absorption.delta₀_le_tiny |>.trans (by norm_num))
    richSchedule hreentryLoss hthirdNormalization hdeltaThird sqrtRequested
    hsqrtLower hsqrtUpper

/-- Complete the second robust localization from the already-restored first
point cover.  The re-entry absorption and the third rich schedule are fixed
before runtime; the remaining assumptions are the explicit scalar receipts of
the square-root Lemma 17 call. -/
theorem Proposition63LiftedPointCoverData.toNestedAnalyticViaThirdRobust
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss firstLoss
      tauScale densityLoss reentryLoss reentryNormalizationLoss weightLoss
      sqrtStickyLoss secondLoss epsilon₁ epsilon₃ : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {incidenceBound : ℝ}
    (currentMap : PaperWZ1WeakPlaneMapData
      (extendShading outer.data.selected outer.data.refined) incidenceBound)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient currentMap.planeMap)
    (tauConstant : ENNReal)
    (first : Proposition63LiftedPointCoverData
      (outputLoss := firstLoss) (queryScale := delta)
      (spatialRadius := tauScale) outerReentry.toNormalizationData
      (extendShading outer.data.selected outer.data.refined)
      currentMap.planeMap tauConstant)
    (absorption : Proposition63CurrentReentryAbsorptionData
      outerSourceLoss outerNormalizationLoss densityLoss firstLoss weightLoss
      reentryLoss
      (proposition63CanonicalNearbyLevelCount outerNormalizationLoss))
    (hdeltaAbsorption : delta ≤ absorption.delta₀)
    (houterNormalizationLoss : 0 < outerNormalizationLoss)
    (htwoNormalization : 2 * outerNormalizationLoss ≤ reentryLoss)
    (hfirstReentry : firstLoss ≤ reentryLoss)
    (hfirstLoss : 0 < firstLoss)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2)
    (richSchedule : Proposition63RichThreeCallScheduleData
      sigma sqrtStickyLoss)
    (hreentryLoss : reentryLoss = richSchedule.third.sourceLoss)
    (hthirdNormalization :
      reentryNormalizationLoss = richSchedule.third.normalizationLoss)
    (hdeltaThird : delta ≤ richSchedule.third.delta₀)
    (sqrtRequested : WZ2PaperRequestedScale delta)
    (hsqrtLower : Real.rpow delta (1 - sqrtStickyLoss) ≤ sqrtRequested.1)
    (hsqrtUpper : sqrtRequested.1 ≤ Real.rpow delta sqrtStickyLoss)
    (hdeltaGrid : delta ≤ gridSide (sqrtRequested.1 / 2))
    (hsqrtOne : sqrtRequested.1 ≤ 1)
    (hboundary : ∀ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) outerReentry.toNormalizationData
        first.state.shading,
      ∀ target : Proposition63RichTerminalStickyData
        (outputLoss := sqrtStickyLoss) reentry.normalization.croppedRefined
        (reentry.normalization.toPropStickyReentryData
          (by rw [hreentryLoss]; exact richSchedule.third.sourceLoss_pos)
          reentry.reentry_normalization_loss_pos) sqrtRequested,
      ((target.terminal.regularity * target.terminal.fineDegreeFloor : ℕ) :
          ENNReal) * (target.terminal.muFine : ENNReal) *
          ENNReal.ofReal
            (1000 * delta / gridSide (sqrtRequested.1 / 2)) <
        target.data.refined.mass)
    (hboundaryError : ∀ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) outerReentry.toNormalizationData
        first.state.shading,
      ∀ target : Proposition63RichTerminalStickyData
        (outputLoss := sqrtStickyLoss) reentry.normalization.croppedRefined
        (reentry.normalization.toPropStickyReentryData
          (by rw [hreentryLoss]; exact richSchedule.third.sourceLoss_pos)
          reentry.reentry_normalization_loss_pos) sqrtRequested,
      ((target.terminal.regularity * target.terminal.fineDegreeFloor : ℕ) :
          ENNReal) * (target.terminal.muFine : ENNReal) *
          ENNReal.ofReal
            (1000 * delta / gridSide (sqrtRequested.1 / 2)) ≤
        (1 / 10 : ENNReal) * target.data.refined.mass)
    (hgridError : ∀ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) outerReentry.toNormalizationData
        first.state.shading,
      ∀ target : Proposition63RichTerminalStickyData
        (outputLoss := sqrtStickyLoss) reentry.normalization.croppedRefined
        (reentry.normalization.toPropStickyReentryData
          (by rw [hreentryLoss]; exact richSchedule.third.sourceLoss_pos)
          reentry.reentry_normalization_loss_pos) sqrtRequested,
      proposition63TauGridPruningError target.data.selected.family
          sqrtRequested.1 epsilon₁ ≤
        (9 / 400 : ENNReal) *
          (target.data.refined.mass /
            ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
              ENNReal)))
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hcrossCall : ∀ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) outerReentry.toNormalizationData
        first.state.shading,
      ∀ target : Proposition63RichTerminalStickyData
        (outputLoss := sqrtStickyLoss) reentry.normalization.croppedRefined
        (reentry.normalization.toPropStickyReentryData
          (by rw [hreentryLoss]; exact richSchedule.third.sourceLoss_pos)
          reentry.reentry_normalization_loss_pos) sqrtRequested,
      4 * (stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal)) ≤
        ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
          ENNReal))
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : sqrtRequested.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (hsqrtSq : sqrtRequested.1 ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic : ∀ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) outerReentry.toNormalizationData
        first.state.shading,
      ∀ target : Proposition63RichTerminalStickyData
        (outputLoss := sqrtStickyLoss) reentry.normalization.croppedRefined
        (reentry.normalization.toPropStickyReentryData
          (by rw [hreentryLoss]; exact richSchedule.third.sourceLoss_pos)
          reentry.reentry_normalization_loss_pos) sqrtRequested,
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              reentry.reentryNormalizationLoss sqrtStickyLoss
              sqrtRequested.1 sqrtRequested.1 /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                sqrtRequested.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta sqrtRequested.1
              incidenceBound coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN
          (sqrtRequested.1 / delta) (1 - sigma))
    (hnormalizationSecond : reentryNormalizationLoss ≤ secondLoss)
    (hsecondLoss : 0 < secondLoss)
    (hrestore : ∀ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) outerReentry.toNormalizationData
        first.state.shading,
      ∀ target : Proposition63RichTerminalStickyData
        (outputLoss := sqrtStickyLoss) reentry.normalization.croppedRefined
        (reentry.normalization.toPropStickyReentryData
          (by rw [hreentryLoss]; exact richSchedule.third.sourceLoss_pos)
          reentry.reentry_normalization_loss_pos) sqrtRequested,
      proposition63Lemma43MassLoss
          ((81 / 400 : ENNReal) *
            (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
              ENNReal))⁻¹ *
            wz2PaperPureRefinementFraction delta 61) 1 *
            Kakeya.realRpowENN delta secondLoss ≤
          Kakeya.realRpowENN delta reentry.reentryNormalizationLoss) :
    Nonempty (Proposition63NestedPointCoverAnalyticData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (queryScale := delta) (tauScale := tauScale)
      (sqrtScale := sqrtRequested.1) outerReentry.toNormalizationData
      currentMap.planeMap tauConstant
      (C * Kakeya.realRpowENN
        (sqrtRequested.1 / delta) (1 - sigma))) := by
  have firstSubNormalized : PaperIsSubshading first.state.shading
      outerReentry.toNormalizationData.croppedRefined := by
    exact fun index point hpoint =>
      extendShading_subshading outer.data.selected outer.data.subshading index <|
        first.state.subshading index hpoint
  rcases first.nextReentryAndThirdRichOfAbsorption
      outerReentry.toNormalizationData firstSubNormalized absorption
      hdeltaAbsorption houterNormalizationLoss htwoNormalization
      hfirstReentry hfirstLoss hreentryNormalizationLoss hreentryHalf
      richSchedule hreentryLoss hthirdNormalization hdeltaThird sqrtRequested
      hsqrtLower hsqrtUpper with
    ⟨reentry, ⟨target⟩, _hweight, _hweightUpper, _hlevel, hnormalization⟩
  let firstMap : PaperWZ1WeakPlaneMapData first.state.shading incidenceBound :=
    paperWeakPlaneMapRestrict currentMap first.state.subshading
  let normalizedMap : PaperWZ1WeakPlaneMapData
      reentry.normalization.croppedRefined incidenceBound :=
    reentry.normalizedPlaneMap firstMap
  let targetMap : PaperWZ1WeakPlaneMapData
      target.data.refined incidenceBound :=
    target.terminalPlaneMap normalizedMap
  have gridFirst := hgridError reentry target
  have gridFirstWeak : proposition63TauGridPruningError
      target.data.selected.family sqrtRequested.1 epsilon₁ ≤
      (9 / 100 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
            ENNReal)) :=
    gridFirst.trans <| by gcongr <;> norm_num
  have htargetReentryLoss : 0 < reentryLoss := by
    rw [hreentryLoss]
    exact richSchedule.third.sourceLoss_pos
  exact Proposition63NestedPointCoverAnalyticData.ofLiftedFirstAndThirdRobust
    outer currentMap.planeMap tauConstant first reentry htargetReentryLoss
    target incidenceBound targetMap.unit hplaneLipschitz targetMap.incidence
    hdeltaGrid hsqrtOne (hboundary reentry target)
    (hboundaryError reentry target) gridFirstWeak gridFirst hrobustSmall
    (hcrossCall reentry target) hkappa htargetSmall hdeltaSmall hsqrtSq hsigma
    hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale hdeltaLog hlog haxis C
    (harithmetic reentry target)
    (hdeltaSmall.trans_lt (by norm_num))
    (hnormalization.trans_le hnormalizationSecond) hsecondLoss
    (hrestore reentry target)

/-- Re-enter a direct first-HIGH output without ever lifting it out of the
actual normalized coarse `rho`-family.  The ancestry and retained-mass data
are read from the exact dependent re-entry that produced the first HIGH
call, so the third call continues on the same `rho` family. -/
theorem Proposition63LiftedPointCoverData.nextReentryOfDirectCoarseAbsorption
    {fineDelta sigma outerLoss queryInputLoss queryNormalizationLoss
      currentReentryLoss firstLoss tauScale reentryLoss
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
    (currentReentry : Proposition63CurrentShadingReentryData
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
    (planeMap : Point3 → Point3) (tauConstant : ENNReal)
    (first : Proposition63LiftedPointCoverData
      (outputLoss := firstLoss) (queryScale := rho.1)
      (spatialRadius := tauScale) currentReentry.normalization
      currentReentry.normalization.croppedRefined planeMap tauConstant)
    (absorption : Proposition63CurrentReentryAbsorptionData
      currentReentryLoss currentReentry.reentryNormalizationLoss
      rootDensityLoss firstLoss weightLoss reentryLoss
      (proposition63CanonicalNearbyLevelCount
        currentReentry.reentryNormalizationLoss))
    (hrhoAbsorption : rho.1 ≤ absorption.delta₀)
    (hqueryNormalizationLoss :
      0 < currentReentry.reentryNormalizationLoss)
    (htwoNormalization :
      2 * currentReentry.reentryNormalizationLoss ≤ reentryLoss)
    (hfirstReentry : firstLoss ≤ reentryLoss)
    (hfirstLoss : 0 < firstLoss)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2) :
    let directCoarse := proposition63DependentCoarseReentryOfCurrent outer
      queryNormalized current currentReentry ancestorEmbedding
      ancestor_tube_eq current_sub_outer ancestorRetentionFactor
      ancestorRetentionFactor_pos ancestorRetentionFactor_ne_top
      current_retained_mass
    Nonempty (Proposition63LiftedPointCoverReentryData outer
      currentReentry.normalization
      currentReentry.normalization.croppedRefined planeMap tauConstant first
      directCoarse.coarseEmbedding (reentryLoss := reentryLoss)
      (reentryNormalizationLoss := reentryNormalizationLoss)
      (weightLoss := weightLoss)) := by
  dsimp only
  let directCoarse := proposition63DependentCoarseReentryOfCurrent outer
    queryNormalized current currentReentry ancestorEmbedding ancestor_tube_eq
    current_sub_outer ancestorRetentionFactor ancestorRetentionFactor_pos
    ancestorRetentionFactor_ne_top current_retained_mass
  exact first.nextReentryOfAbsorption outer currentReentry.normalization
    currentReentry.normalization.croppedRefined planeMap tauConstant
    first.state.subshading directCoarse.coarseEmbedding
    directCoarse.coarse_tube_eq directCoarse.normalized_subshading
    directCoarse.retentionFactor directCoarse.retentionFactor_pos
    directCoarse.retentionFactor_ne_top directCoarse.retained_mass absorption
    hrhoAbsorption hqueryNormalizationLoss htwoNormalization hfirstReentry
    hfirstLoss hreentryNormalizationLoss hreentryHalf

/-- All fixed scalar receipts for one paper-order nested pair.  The first and
third HIGH calls use the same actual normalized `rho` family.  In particular,
the package contains no intermediate root-family lift, no completed one-scale
AD estimate, and no proof quantified over a runtime-produced family. -/
structure Proposition63ConcreteNestedPairParameters
    {fineDelta sigma fineInputLoss fineNormalizationLoss fineReentryLoss
      outerLoss coarseInputLoss coarseNormalizationLoss currentReentryLoss
      firstLoss reentryLoss reentryNormalizationLoss rootDensityLoss weightLoss
      sqrtStickyLoss secondLoss firstDensityLoss sqrtDensityLoss
      firstEpsilon₁ firstEpsilon₃ firstKappa sqrtEpsilon₁ sqrtEpsilon₃
      sqrtKappa middleLoss finalLoss : ℝ}
    {fineSource : PureWZ2ExtremalConfiguration sigma fineInputLoss fineDelta}
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
    (current : WZ1PaperTubeShading coarseNormalized.croppedFamily)
    (currentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := currentReentryLoss) coarseNormalized current)
    (schedule : Proposition63RichThreeCallScheduleData sigma sqrtStickyLoss)
    (tau sqrtRequested : WZ2PaperRequestedScale rho.1)
    (incidenceBound : ℝ)
    (currentMap : PaperWZ1WeakPlaneMapData current incidenceBound)
    (coefficient : NNReal) (firstC sqrtC : ENNReal) where
  ancestorEmbedding :
    Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card
  ancestor_tube_eq : ∀ index,
    coarseNormalized.croppedFamily.tube index =
      outer.coarse.tube (ancestorEmbedding index)
  current_sub_outer : ∀ index, current.carrier index ⊆
    outer.croppedCoarseShading.carrier (ancestorEmbedding index)
  ancestorRetentionFactor : ENNReal
  ancestor_retention_factor_pos : 0 < ancestorRetentionFactor
  ancestor_retention_factor_ne_top : ancestorRetentionFactor ≠ ⊤
  current_retained_mass :
    ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤ current.mass
  plane_lipschitz : LipschitzWith coefficient currentMap.planeMap
  coefficient_one : 1 ≤ (coefficient : ℝ)
  first_reentry_loss : currentReentryLoss = schedule.second.sourceLoss
  first_normalization_loss :
    currentReentry.reentryNormalizationLoss =
      schedule.second.normalizationLoss
  first_schedule_scale : rho.1 ≤ schedule.second.delta₀
  tau_lower : Real.rpow rho.1 (1 - schedule.secondOutputLoss) ≤ tau.1
  tau_upper : tau.1 ≤ Real.rpow rho.1 schedule.secondOutputLoss
  first_reentry_target : currentReentry.reentryNormalizationLoss ≤ firstLoss
  first_retention : Kakeya.realRpowENN rho.1 firstLoss ≤
    wz2PaperPureRefinementFraction rho.1 61 *
      Kakeya.realRpowENN rho.1 currentReentry.reentryNormalizationLoss
  first_density_loss : firstDensityLoss = 2 - sigma + 3 * firstLoss
  first_loss_pos : 0 < firstLoss
  first_small : Kakeya.realRpowENN rho.1 firstLoss < 1 / 4
  rho_small_24 : rho.1 ≤ 1 / 24
  rho_small_10000 : rho.1 ≤ 1 / 10000
  first_packing_absorb :
    (12 * ((2 * 4 * 601 ^ 3 * 12001 ^ 3 + 1 : ℕ) : ENNReal)) *
        ENNReal.ofReal Real.pi ≤
      Kakeya.realRpowENN rho.1 (-sigma + 4 * firstLoss)
  first_epsilon₁_pos : 0 < firstEpsilon₁
  first_epsilon₃_pos : 0 < firstEpsilon₃
  first_epsilon_sum : firstEpsilon₁ + firstEpsilon₃ < 1
  tau_pos : 0 < tau.1
  rho_le_tau : rho.1 ≤ tau.1
  tau_le_sqrt : tau.1 ≤ Real.sqrt rho.1
  tau_large : rho.1 * Real.sqrt 3 ≤ tau.1
  tau_sq : tau.1 ^ 2 ≤ 4 * rho.1
  tau_one : tau.1 ≤ 1
  first_cell :
    Kakeya.realRpowENN rho.1 (2 + 2 * firstEpsilon₁) *
        ENNReal.ofReal tau.1 ≤ Kakeya.realRpowENN rho.1 3
  first_kappa_pos : 0 < firstKappa
  first_kappa_one : firstKappa ≤ 1
  first_kappa_rho : rho.1 ≤ firstKappa
  first_kappa_property : Real.rpow rho.1 firstEpsilon₃ ≤ firstKappa
  first_close_absorb :
    Kakeya.realRpowENN rho.1 (-firstLoss) *
        ENNReal.ofReal (10000 * firstKappa ^ 2) <
      Kakeya.realRpowENN rho.1 firstDensityLoss
  rho_lt_one : rho.1 < 1
  first_mass_slack : proposition63DependentPropertyThreeMassLoss rho.1 61 *
      Kakeya.realRpowENN rho.1 firstLoss ≤
    Kakeya.realRpowENN rho.1 currentReentry.reentryNormalizationLoss
  tau_small : tau.1 ≤ 1 / 12
  rho_small_1000 : rho.1 ≤ 1 / 1000
  sigma_pos : 0 < sigma
  sigma_lt_one : sigma < 1
  firstLogScale : ℝ
  rho_le_firstLogScale : rho.1 ≤ firstLogScale
  first_logarithmic_bound : 0 < firstEpsilon₁ →
    ∀ scale : ℝ, 0 < scale → scale ≤ firstLogScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale firstEpsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108
  first_axis_budget : 4 * (6 * rho.1) ^ 2 ≤
    (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - firstEpsilon₃)) ^ 2
  first_covering_arithmetic :
    ENNReal.ofReal
        (((5832 * Real.rpow rho.1 (sigma - outerLoss) *
            Real.rpow tau.1
              (3 - sigma - 2 * schedule.secondOutputLoss)) /
            (Real.rpow rho.1 (1 + 7 * firstEpsilon₁ + firstEpsilon₃) *
              tau.1 ^ 2 / 200)) *
          (2 * proposition63DependentSlabWidth rho.1 tau.1 incidenceBound
            coefficient / rho.1 + 2)) ≤
      firstC * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)
  reentry_absorption : Proposition63CurrentReentryAbsorptionData
    currentReentryLoss currentReentry.reentryNormalizationLoss
    rootDensityLoss firstLoss weightLoss reentryLoss
    (proposition63CanonicalNearbyLevelCount
      currentReentry.reentryNormalizationLoss)
  reentry_scale : rho.1 ≤ reentry_absorption.delta₀
  twice_normalization_le_reentry :
    2 * currentReentry.reentryNormalizationLoss ≤ reentryLoss
  first_le_reentry : firstLoss ≤ reentryLoss
  reentry_normalization_loss_pos : 0 < reentryNormalizationLoss
  reentry_half : reentryLoss ≤ reentryNormalizationLoss / 2
  third_reentry_loss : reentryLoss = schedule.third.sourceLoss
  third_normalization_loss :
    reentryNormalizationLoss = schedule.third.normalizationLoss
  third_schedule_scale : rho.1 ≤ schedule.third.delta₀
  sqrt_eq : sqrtRequested.1 = Real.sqrt rho.1
  sqrt_lower : Real.rpow rho.1 (1 - sqrtStickyLoss) ≤ sqrtRequested.1
  sqrt_upper : sqrtRequested.1 ≤ Real.rpow rho.1 sqrtStickyLoss
  third_reentry_target : reentryNormalizationLoss ≤ secondLoss
  third_retention : Kakeya.realRpowENN rho.1 secondLoss ≤
    wz2PaperPureRefinementFraction rho.1 61 *
      Kakeya.realRpowENN rho.1 reentryNormalizationLoss
  sqrt_density_loss : sqrtDensityLoss = 2 - sigma + 3 * secondLoss
  second_loss_pos : 0 < secondLoss
  second_small : Kakeya.realRpowENN rho.1 secondLoss < 1 / 4
  second_packing_absorb :
    (12 * ((2 * 4 * 601 ^ 3 * 12001 ^ 3 + 1 : ℕ) : ENNReal)) *
        ENNReal.ofReal Real.pi ≤
      Kakeya.realRpowENN rho.1 (-sigma + 4 * secondLoss)
  sqrt_epsilon₁_pos : 0 < sqrtEpsilon₁
  sqrt_epsilon₃_pos : 0 < sqrtEpsilon₃
  sqrt_epsilon_sum : sqrtEpsilon₁ + sqrtEpsilon₃ < 1
  sqrt_pos : 0 < sqrtRequested.1
  rho_le_sqrt : rho.1 ≤ sqrtRequested.1
  sqrt_large : rho.1 * Real.sqrt 3 ≤ sqrtRequested.1
  sqrt_sq : sqrtRequested.1 ^ 2 ≤ 4 * rho.1
  sqrt_one : sqrtRequested.1 ≤ 1
  sqrt_cell :
    Kakeya.realRpowENN rho.1 (2 + 2 * sqrtEpsilon₁) *
        ENNReal.ofReal sqrtRequested.1 ≤ Kakeya.realRpowENN rho.1 3
  sqrt_kappa_pos : 0 < sqrtKappa
  sqrt_kappa_one : sqrtKappa ≤ 1
  sqrt_kappa_rho : rho.1 ≤ sqrtKappa
  sqrt_kappa_property : Real.rpow rho.1 sqrtEpsilon₃ ≤ sqrtKappa
  sqrt_close_absorb :
    Kakeya.realRpowENN rho.1 (-secondLoss) *
        ENNReal.ofReal (10000 * sqrtKappa ^ 2) <
      Kakeya.realRpowENN rho.1 sqrtDensityLoss
  second_mass_slack : proposition63DependentPropertyThreeMassLoss rho.1 61 *
      Kakeya.realRpowENN rho.1 secondLoss ≤
    Kakeya.realRpowENN rho.1 reentryNormalizationLoss
  sqrt_small : sqrtRequested.1 ≤ 1 / 12
  sqrtLogScale : ℝ
  rho_le_sqrtLogScale : rho.1 ≤ sqrtLogScale
  sqrt_logarithmic_bound : 0 < sqrtEpsilon₁ →
    ∀ scale : ℝ, 0 < scale → scale ≤ sqrtLogScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale sqrtEpsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108
  sqrt_axis_budget : 4 * (6 * rho.1) ^ 2 ≤
    (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - sqrtEpsilon₃)) ^ 2
  sqrt_covering_arithmetic :
    ENNReal.ofReal
        (((5832 * Real.rpow rho.1 (sigma - outerLoss) *
            Real.rpow sqrtRequested.1
              (3 - sigma - 2 * sqrtStickyLoss)) /
            (Real.rpow rho.1 (1 + 7 * sqrtEpsilon₁ + sqrtEpsilon₃) *
              sqrtRequested.1 ^ 2 / 200)) *
          (2 * proposition63DependentSlabWidth rho.1 sqrtRequested.1
            incidenceBound coefficient / rho.1 + 2)) ≤
      sqrtC * Kakeya.realRpowENN
        (sqrtRequested.1 / rho.1) (1 - sigma)
  sqrt_C_ne_top : sqrtC ≠ ⊤
  normal_error_le_tau : 8 * (coefficient : ℝ) * rho.1 ≤ tau.1
  second_le_middle : secondLoss ≤ middleLoss
  middle_loss_pos : 0 < middleLoss
  multiplicity_slack :
    (((Nat.log 2 coarseNormalized.croppedFamily.card + 1 : ℕ) : ENNReal) *
        Kakeya.realRpowENN rho.1 middleLoss) ≤
      Kakeya.realRpowENN rho.1 secondLoss
  periodic_scale : 50 * rho.1 ≤ sqrtRequested.1
  boundary_scalar :
    2 * 24000000 *
        (Kakeya.realRpowENN rho.1 (-middleLoss) *
            wz2PaperBoundaryGeometryConstant + 1) *
        ENNReal.ofReal (Real.sqrt (rho.1 / sqrtRequested.1)) <
      Kakeya.realRpowENN rho.1 middleLoss
  middle_le_final : middleLoss ≤ finalLoss
  final_loss_pos : 0 < finalLoss
  balancing_slack : proposition63FreshBalancingEnvelope rho.1 *
      Kakeya.realRpowENN rho.1 finalLoss ≤
    Kakeya.realRpowENN rho.1 middleLoss

namespace Proposition63ConcreteNestedPairParameters

/-- The fixed favorable factor for the critical-floor line-hit tail. -/
def coarseLeftFactor
    (rho sqrtScale cellVolumeFloor weightLoss : ℝ)
    (coverBudget : ℕ) : ENNReal :=
  ENNReal.ofReal
      ((cellVolumeFloor / 2) / (4 * (2 * sqrtScale) ^ 2)) *
    (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) *
    ((proposition63DependentPropertyThreeMassLoss rho 61)⁻¹ *
      ((73 / 100 : ENNReal) *
        proposition63CanonicalReentryWeight rho weightLoss) *
      (proposition63DependentPropertyThreeMassLoss rho 61)⁻¹)

/-- A fixed upper envelope for the unfavorable coarse-tail factor. -/
def coarseRightFactor
    {rho : ℝ} (family : Kakeya.Streamlined.TubeFamily rho)
    (normalizationLoss rhoScale : ℝ) : ENNReal :=
  (proposition63UniformReentryRegularizationLoss family
      (proposition63CanonicalNearbyLevelCount normalizationLoss) *
    proposition63UniformPreparationLoss family) *
  (2 * ENNReal.ofReal (4 * rhoScale))

/-- Execute both HIGH calls on one actual `rho` family, then perform the
constant-multiplicity and fresh whole-cell refinements. -/
theorem nestedPointCover
    {fineDelta sigma fineInputLoss fineNormalizationLoss fineReentryLoss
      outerLoss coarseInputLoss coarseNormalizationLoss currentReentryLoss
      firstLoss reentryLoss reentryNormalizationLoss rootDensityLoss weightLoss
      sqrtStickyLoss secondLoss firstDensityLoss sqrtDensityLoss
      firstEpsilon₁ firstEpsilon₃ firstKappa sqrtEpsilon₁ sqrtEpsilon₃
      sqrtKappa middleLoss finalLoss : ℝ}
    {fineSource : PureWZ2ExtremalConfiguration sigma fineInputLoss fineDelta}
    {fineNormalizationExponent outerLogExponent
      coarseNormalizationExponent : ℕ}
    {fineNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := fineNormalizationLoss) fineSource
      fineNormalizationExponent}
    {fineCurrent : WZ1PaperTubeShading fineNormalized.croppedFamily}
    {fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) fineNormalized fineCurrent}
    {rho : WZ2PaperRequestedScale fineDelta}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent}
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    {coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      coarseNormalizationExponent}
    {current : WZ1PaperTubeShading coarseNormalized.croppedFamily}
    {currentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := currentReentryLoss) coarseNormalized current}
    {schedule : Proposition63RichThreeCallScheduleData sigma sqrtStickyLoss}
    {tau sqrtRequested : WZ2PaperRequestedScale rho.1}
    {incidenceBound : ℝ}
    {currentMap : PaperWZ1WeakPlaneMapData current incidenceBound}
    {coefficient : NNReal} {firstC sqrtC : ENNReal}
    (parameters : Proposition63ConcreteNestedPairParameters
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (reentryNormalizationLoss := reentryNormalizationLoss)
      (rootDensityLoss := rootDensityLoss) (weightLoss := weightLoss)
      (secondLoss := secondLoss) (firstDensityLoss := firstDensityLoss)
      (sqrtDensityLoss := sqrtDensityLoss)
      (firstEpsilon₁ := firstEpsilon₁) (firstEpsilon₃ := firstEpsilon₃)
      (firstKappa := firstKappa)
      (sqrtEpsilon₁ := sqrtEpsilon₁) (sqrtEpsilon₃ := sqrtEpsilon₃)
      (sqrtKappa := sqrtKappa) (middleLoss := middleLoss)
      (finalLoss := finalLoss) fineReentry outer coarseNormalized current
      currentReentry schedule tau sqrtRequested incidenceBound currentMap
      coefficient firstC sqrtC) :
    ∃ result : Proposition63NestedPointCoverData
        (firstLoss := firstLoss) (reentryLoss := reentryLoss)
        (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
        (finalLoss := finalLoss) (queryScale := rho.1)
        (tauScale := tau.1) (sqrtScale := sqrtRequested.1)
        currentReentry.normalization currentMap.planeMap
        (firstC * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma))
        (sqrtC * Kakeya.realRpowENN
          (sqrtRequested.1 / rho.1) (1 - sigma)),
      result.current = currentReentry.normalization.croppedRefined ∧
      result.firstRetainedFactor =
        (proposition63DependentPropertyThreeMassLoss rho.1 61)⁻¹ ∧
      result.secondRetainedFactor =
        (proposition63DependentPropertyThreeMassLoss rho.1 61)⁻¹ ∧
      result.reentry.normalizationWeight =
        proposition63CanonicalReentryWeight rho.1 weightLoss ∧
      result.reentry.levelCount =
        proposition63CanonicalNearbyLevelCount
          currentReentry.reentryNormalizationLoss ∧
      result.prepared.preparationLoss ≤
        proposition63UniformPreparationLoss
          currentReentry.normalization.croppedFamily := by
  rcases currentReentry.directSecondCWA outer coarseNormalized current
      parameters.ancestorEmbedding parameters.ancestor_tube_eq
      parameters.current_sub_outer parameters.ancestorRetentionFactor
      parameters.ancestor_retention_factor_pos
      parameters.ancestor_retention_factor_ne_top
      parameters.current_retained_mass schedule parameters.first_reentry_loss
      parameters.first_normalization_loss parameters.first_schedule_scale tau
      parameters.tau_lower parameters.tau_upper currentMap.planeMap coefficient
      incidenceBound currentMap.unit parameters.plane_lipschitz
      currentMap.incidence
      parameters.first_reentry_target parameters.first_retention
      parameters.first_density_loss parameters.first_loss_pos
      parameters.first_small parameters.rho_small_24
      parameters.rho_small_10000 parameters.first_packing_absorb
      parameters.first_epsilon₁_pos parameters.first_epsilon₃_pos
      parameters.first_epsilon_sum parameters.tau_pos parameters.rho_le_tau
      parameters.tau_large parameters.tau_sq parameters.tau_one
      parameters.first_cell parameters.first_kappa_pos
      parameters.first_kappa_one parameters.first_kappa_rho
      parameters.first_kappa_property parameters.first_close_absorb
      parameters.rho_lt_one parameters.first_mass_slack parameters.tau_small
      parameters.rho_small_1000 parameters.sigma_pos parameters.sigma_lt_one
      parameters.firstLogScale parameters.rho_le_firstLogScale
      parameters.first_logarithmic_bound parameters.first_axis_budget firstC
      parameters.first_covering_arithmetic with ⟨first, hfirstFactor⟩
  let directCoarse := proposition63DependentCoarseReentryOfCurrent outer
    coarseNormalized current currentReentry parameters.ancestorEmbedding
    parameters.ancestor_tube_eq parameters.current_sub_outer
    parameters.ancestorRetentionFactor
    parameters.ancestor_retention_factor_pos
    parameters.ancestor_retention_factor_ne_top
    parameters.current_retained_mass
  rcases first.nextReentryOfDirectCoarseAbsorption outer coarseNormalized
      current currentReentry parameters.ancestorEmbedding
      parameters.ancestor_tube_eq parameters.current_sub_outer
      parameters.ancestorRetentionFactor
      parameters.ancestor_retention_factor_pos
      parameters.ancestor_retention_factor_ne_top
      parameters.current_retained_mass currentMap.planeMap
      (firstC * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma))
      parameters.reentry_absorption parameters.reentry_scale
      currentReentry.reentry_normalization_loss_pos
      parameters.twice_normalization_le_reentry parameters.first_le_reentry
      parameters.first_loss_pos parameters.reentry_normalization_loss_pos
      parameters.reentry_half with ⟨nextReentry⟩
  let firstSelectedMap : PaperWZ1WeakPlaneMapData
      (restrictPaperShading currentReentry.regularized.selected current)
      incidenceBound :=
    PaperWZ1WeakPlaneMapData.restrictSubfamily currentMap
      currentReentry.regularized.selected
  let firstNormalizedMap : PaperWZ1WeakPlaneMapData
      currentReentry.normalization.croppedRefined incidenceBound :=
    paperWeakPlaneMapRestrict firstSelectedMap currentReentry.denseSubshading
  let firstMap : PaperWZ1WeakPlaneMapData first.state.shading incidenceBound :=
    paperWeakPlaneMapRestrict firstNormalizedMap first.state.subshading
  let secondSelectedMap : PaperWZ1WeakPlaneMapData
      (restrictPaperShading nextReentry.reentry.regularized.selected
        first.state.shading) incidenceBound :=
    PaperWZ1WeakPlaneMapData.restrictSubfamily firstMap
      nextReentry.reentry.regularized.selected
  let secondNormalizedMap : PaperWZ1WeakPlaneMapData
      nextReentry.reentry.normalization.croppedRefined incidenceBound :=
    paperWeakPlaneMapRestrict secondSelectedMap
      nextReentry.reentry.denseSubshading
  have hthirdNormalization :
      nextReentry.reentry.reentryNormalizationLoss =
        schedule.third.normalizationLoss :=
    nextReentry.reentry_normalization_loss_eq.trans
      parameters.third_normalization_loss
  have hthirdTarget :
      nextReentry.reentry.reentryNormalizationLoss ≤ secondLoss := by
    rw [nextReentry.reentry_normalization_loss_eq]
    exact parameters.third_reentry_target
  have hthirdRetention : Kakeya.realRpowENN rho.1 secondLoss ≤
      wz2PaperPureRefinementFraction rho.1 61 *
        Kakeya.realRpowENN rho.1
          nextReentry.reentry.reentryNormalizationLoss := by
    rw [nextReentry.reentry_normalization_loss_eq]
    exact parameters.third_retention
  have hthirdMassSlack :
      proposition63DependentPropertyThreeMassLoss rho.1 61 *
          Kakeya.realRpowENN rho.1 secondLoss ≤
        Kakeya.realRpowENN rho.1
          nextReentry.reentry.reentryNormalizationLoss := by
    rw [nextReentry.reentry_normalization_loss_eq]
    exact parameters.second_mass_slack
  rcases Proposition63NestedPointCoverAnalyticData.ofLiftedFirstAndThirdCWA
      outer currentReentry.normalization
      currentReentry.normalization.croppedRefined currentMap.planeMap
      (firstC * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)) first
      nextReentry.reentry directCoarse.coarseEmbedding
      directCoarse.coarse_tube_eq nextReentry.current_sub_outer
      nextReentry.ancestorRetentionFactor
      nextReentry.ancestor_retention_factor_pos
      nextReentry.ancestor_retention_factor_ne_top
      nextReentry.current_retained_mass schedule parameters.third_reentry_loss
      hthirdNormalization parameters.third_schedule_scale sqrtRequested
      parameters.sqrt_lower parameters.sqrt_upper coefficient incidenceBound
      secondNormalizedMap.unit parameters.plane_lipschitz
      secondNormalizedMap.incidence hthirdTarget hthirdRetention
      parameters.sqrt_density_loss
      parameters.second_loss_pos parameters.second_small
      parameters.rho_small_24 parameters.rho_small_10000
      parameters.second_packing_absorb parameters.sqrt_epsilon₁_pos
      parameters.sqrt_epsilon₃_pos parameters.sqrt_epsilon_sum
      parameters.sqrt_pos parameters.rho_le_sqrt parameters.sqrt_large
      parameters.sqrt_sq parameters.sqrt_one parameters.sqrt_cell
      parameters.sqrt_kappa_pos parameters.sqrt_kappa_one
      parameters.sqrt_kappa_rho parameters.sqrt_kappa_property
      parameters.sqrt_close_absorb parameters.rho_lt_one
      hthirdMassSlack parameters.sqrt_small
      parameters.rho_small_1000 parameters.sigma_pos parameters.sigma_lt_one
      parameters.sqrtLogScale parameters.rho_le_sqrtLogScale
      parameters.sqrt_logarithmic_bound parameters.sqrt_axis_budget sqrtC
      parameters.sqrt_covering_arithmetic with
    ⟨analytic, hanalyticCurrent, hanalyticFirst, hanalyticWeight,
      hanalyticLevel, hanalyticSecond⟩
  have hfirstCard : currentReentry.normalization.croppedFamily.card ≤
      coarseNormalized.croppedFamily.card := by
    rw [currentReentry.normalization_croppedFamily]
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      currentReentry.regularized.selected.embedding
      currentReentry.regularized.selected.embedding.injective
  have hsecondCard : analytic.reentry.normalization.croppedFamily.card ≤
      currentReentry.normalization.croppedFamily.card := by
    rw [analytic.reentry.normalization_croppedFamily]
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      analytic.reentry.regularized.selected.embedding
      analytic.reentry.regularized.selected.embedding.injective
  have hlogNat :
      Nat.log 2 analytic.reentry.normalization.croppedFamily.card + 1 ≤
        Nat.log 2 coarseNormalized.croppedFamily.card + 1 :=
    Nat.add_le_add_right
      (Nat.log_mono_right (hsecondCard.trans hfirstCard)) 1
  have hlog :
      ((Nat.log 2 analytic.reentry.normalization.croppedFamily.card + 1 :
          ℕ) : ENNReal) ≤
        ((Nat.log 2 coarseNormalized.croppedFamily.card + 1 : ℕ) :
          ENNReal) := by
    exact_mod_cast hlogNat
  have hmultiplicitySlack :
      (((Nat.log 2 analytic.reentry.normalization.croppedFamily.card + 1 :
          ℕ) : ENNReal) * Kakeya.realRpowENN rho.1 middleLoss) ≤
        Kakeya.realRpowENN rho.1 secondLoss :=
    (mul_le_mul_right' hlog _).trans parameters.multiplicity_slack
  rcases analytic.prepareFreshBalancedCells parameters.second_le_middle
      parameters.middle_loss_pos hmultiplicitySlack parameters.rho_small_24
      parameters.periodic_scale parameters.sqrt_pos parameters.sqrt_one
      parameters.boundary_scalar parameters.middle_le_final
      parameters.final_loss_pos parameters.balancing_slack with
    ⟨result, hresultCurrent, hresultFirst, hresultWeight, hresultLevel,
      hresultSecond, hpreparation⟩
  refine ⟨result, hresultCurrent.trans hanalyticCurrent, ?_, ?_, ?_, ?_,
    hpreparation⟩
  · exact hresultFirst.trans <| hanalyticFirst.trans hfirstFactor
  · exact hresultSecond.trans hanalyticSecond
  · exact hresultWeight.trans <|
      hanalyticWeight.trans nextReentry.normalization_weight_eq
  · exact hresultLevel.trans <|
      hanalyticLevel.trans nextReentry.level_count_eq

/-- Single entry point for one concrete nested pair.  It runs both dependent
HIGH calls on the same actual normalized `rho` family, constructs the fresh
square-root cells, applies the cropped critical floor, and performs exactly
one whole-cell pullback to the fixed fine/current family. -/
theorem finalCandidate_for_interval_iteration
    {fineDelta sigma fineInputLoss fineNormalizationLoss fineReentryLoss
      outerLoss coarseInputLoss coarseNormalizationLoss currentReentryLoss
      firstLoss reentryLoss reentryNormalizationLoss rootDensityLoss weightLoss
      sqrtStickyLoss secondLoss firstDensityLoss sqrtDensityLoss
      firstEpsilon₁ firstEpsilon₃ firstKappa sqrtEpsilon₁ sqrtEpsilon₃
      sqrtKappa middleLoss finalLoss floorLoss structuralBudget cellVolumeFloor
      outputLoss spatialScale variationScale : ℝ}
    {fineSource : PureWZ2ExtremalConfiguration sigma fineInputLoss fineDelta}
    {fineNormalizationExponent outerLogExponent
      coarseNormalizationExponent : ℕ}
    {fineNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := fineNormalizationLoss) fineSource
      fineNormalizationExponent}
    {fineCurrent : WZ1PaperTubeShading fineNormalized.croppedFamily}
    {fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) fineNormalized fineCurrent}
    {rho : WZ2PaperRequestedScale fineDelta}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent}
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    {coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      coarseNormalizationExponent}
    {current : WZ1PaperTubeShading coarseNormalized.croppedFamily}
    {currentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := currentReentryLoss) coarseNormalized current}
    {schedule : Proposition63RichThreeCallScheduleData sigma sqrtStickyLoss}
    {tau sqrtRequested : WZ2PaperRequestedScale rho.1}
    {incidenceBound : ℝ}
    {currentMap : PaperWZ1WeakPlaneMapData current incidenceBound}
    {coefficient : NNReal} {firstC sqrtC : ENNReal}
    (parameters : Proposition63ConcreteNestedPairParameters
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (reentryNormalizationLoss := reentryNormalizationLoss)
      (rootDensityLoss := rootDensityLoss) (weightLoss := weightLoss)
      (secondLoss := secondLoss) (firstDensityLoss := firstDensityLoss)
      (sqrtDensityLoss := sqrtDensityLoss)
      (firstEpsilon₁ := firstEpsilon₁) (firstEpsilon₃ := firstEpsilon₃)
      (firstKappa := firstKappa)
      (sqrtEpsilon₁ := sqrtEpsilon₁) (sqrtEpsilon₃ := sqrtEpsilon₃)
      (sqrtKappa := sqrtKappa) (middleLoss := middleLoss)
      (finalLoss := finalLoss) fineReentry outer coarseNormalized current
      currentReentry schedule tau sqrtRequested incidenceBound currentMap
      coefficient firstC sqrtC)
    (critical : PureWZ2CroppedCriticalFloorSelectionData
      sigma floorLoss structuralBudget)
    (hcoarseCritical : rho.1 ≤ critical.delta₀)
    (hfinalStructural : finalLoss = critical.structuralLoss)
    (hcellVolumeFloor : 0 < cellVolumeFloor)
    (hcellBudget :
      ENNReal.ofReal cellVolumeFloor *
          Kakeya.realRpowENN sqrtRequested.1
            (sigma - sqrtStickyLoss) ≤
        Kakeya.realRpowENN rho.1 (sigma + floorLoss) *
          Kakeya.realRpowENN sqrtRequested.1 3)
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            (sqrtC * Kakeya.realRpowENN
              (sqrtRequested.1 / rho.1) (1 - sigma))) ≤
        (coverBudget : ENNReal))
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * fineDelta)
    (hcurrentCWA : WZ2PaperConvexWolffBound
      fineNormalized.croppedFamily
      (Kakeya.realRpowENN fineDelta (-fineReentryLoss)))
    (targetConstant targetLeft targetRight : ENNReal)
    (hconstant :
      Proposition63NestedPointCoverData.FullGrainCells.nestedCandidateIntervalBound
            rho.1 rho.1
            (8 * (coefficient : ℝ) * rho.1) (coefficient : ℝ) (13 ^ 3)
            (firstC * Kakeya.realRpowENN
              (tau.1 / rho.1) (1 - sigma)) ≤
        targetConstant)
    (hleft : targetLeft ≤
      proposition63DependentFinePullbackLeft fineReentry outer
        (proposition63DependentCoarseReentryOfCurrent outer coarseNormalized
          current currentReentry parameters.ancestorEmbedding
          parameters.ancestor_tube_eq parameters.current_sub_outer
          parameters.ancestorRetentionFactor
          parameters.ancestor_retention_factor_pos
          parameters.ancestor_retention_factor_ne_top
          parameters.current_retained_mass).retentionFactor
        (coarseLeftFactor rho.1 sqrtRequested.1 cellVolumeFloor weightLoss
          coverBudget))
    (hright : proposition63DependentFinePullbackRight fineReentry
        (coarseRightFactor currentReentry.normalization.croppedFamily
          currentReentry.reentryNormalizationLoss rho.1) ≤ targetRight)
    (hleftPos : 0 < targetLeft) (hleftTop : targetLeft ≠ ⊤)
    (hrightTop : targetRight ≠ ⊤)
    (hcurrentOutput : fineReentryLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss targetLeft targetRight *
        Kakeya.realRpowENN fineDelta outputLoss ≤
      Kakeya.realRpowENN fineDelta fineReentryLoss)
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
      PureWZ2IntervalCoveringAt next currentMap.planeMap rho.1
        (Real.toNNReal rho.1) (Real.toNNReal tau.1) targetConstant ∧
      targetLeft * fineCurrent.mass ≤ targetRight * next.mass ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ spatialScale →
          dist (currentMap.planeMap first)
            (currentMap.planeMap second) ≤ variationScale) := by
  rcases parameters.nestedPointCover with
    ⟨data, hdataCurrent, hfirstFactor, hsecondFactor, hweight, hlevel,
      hpreparation⟩
  let directCoarse := proposition63DependentCoarseReentryOfCurrent outer
    coarseNormalized current currentReentry parameters.ancestorEmbedding
    parameters.ancestor_tube_eq parameters.current_sub_outer
    parameters.ancestorRetentionFactor
    parameters.ancestor_retention_factor_pos
    parameters.ancestor_retention_factor_ne_top
    parameters.current_retained_mass
  have hdataSub : ∀ index, data.current.carrier index ⊆
      outer.croppedCoarseShading.carrier (directCoarse.coarseEmbedding index) :=
    by
      intro index point hpoint
      rw [hdataCurrent] at hpoint
      exact directCoarse.normalized_subshading index hpoint
  have hdataRetained :
      directCoarse.retentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
        data.current.mass := by
    rw [hdataCurrent]
    exact directCoarse.retained_mass
  have hplaneUnit : ∀ point ∈ data.prepared.refined.shading.union,
      ‖currentMap.planeMap point‖ = 1 := by
    intro point hpoint
    apply currentMap.unit point
    apply currentReentry.normalization_croppedRefined_union_subset_current
    rw [← hdataCurrent]
    exact data.prepared_union_subset_current hpoint
  have hsqrtConstantFinite :
      sqrtC * Kakeya.realRpowENN
          (sqrtRequested.1 / rho.1) (1 - sigma) ≠ ⊤ :=
    ENNReal.mul_ne_top parameters.sqrt_C_ne_top ENNReal.ofReal_ne_top
  have hcoarseLeft : targetLeft ≤
      proposition63DependentFinePullbackLeft fineReentry outer
        directCoarse.retentionFactor
        (ENNReal.ofReal
            ((cellVolumeFloor / 2) /
              (4 * (2 * sqrtRequested.1) ^ 2)) *
          (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) *
          (data.secondRetainedFactor *
            ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
            data.firstRetainedFactor)) := by
    simpa only [coarseLeftFactor, hfirstFactor, hsecondFactor, hweight] using
      hleft
  have hreentryRegularization : data.reentry.regularized.regularizationLoss ≤
      proposition63UniformReentryRegularizationLoss
        currentReentry.normalization.croppedFamily
        (proposition63CanonicalNearbyLevelCount
          currentReentry.reentryNormalizationLoss) := by
    exact proposition63_reentry_regularizationLoss_le_uniform data.reentry
      currentReentry.normalization.croppedFamily
      (proposition63CanonicalNearbyLevelCount
        currentReentry.reentryNormalizationLoss) le_rfl (by rw [hlevel])
  have hcoarseRight :
      (data.reentry.regularized.regularizationLoss *
          data.prepared.preparationLoss) *
          (2 * ENNReal.ofReal (4 * rho.1)) ≤
        coarseRightFactor currentReentry.normalization.croppedFamily
          currentReentry.reentryNormalizationLoss rho.1 := by
    unfold coarseRightFactor
    gcongr
  have hdataRight : proposition63DependentFinePullbackRight fineReentry
        ((data.reentry.regularized.regularizationLoss *
            data.prepared.preparationLoss) *
          (2 * ENNReal.ofReal (4 * rho.1))) ≤ targetRight :=
    (by
      unfold proposition63DependentFinePullbackRight
      exact (mul_le_mul_right' hcoarseRight
        fineReentry.regularized.regularizationLoss).trans hright)
  exact Proposition63NestedPointCoverData.finalCandidate_for_fine_interval_iteration_of_critical_floor
      fineReentry outer currentReentry.normalization currentMap.planeMap
      (firstC * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma))
      (sqrtC * Kakeya.realRpowENN
        (sqrtRequested.1 / rho.1) (1 - sigma)) data
      directCoarse.coarseEmbedding directCoarse.coarse_tube_eq hdataSub
      directCoarse.retentionFactor hdataRetained critical hcoarseCritical
      hfinalStructural hcellVolumeFloor hcellBudget
      currentReentry.reentry_extremal.delta_pos
      currentReentry.reentry_extremal.delta_le_one parameters.tau_pos
      parameters.rho_le_tau parameters.tau_le_sqrt parameters.sqrt_eq
      hplaneUnit coefficient parameters.coefficient_one
      parameters.plane_lipschitz coverBudget hcoverBudgetPos hcoverBudget
      hsqrtConstantFinite parameters.normal_error_le_tau parameters.tau_large
      scaleFactor hscaleFactor hrhoAligned fineReentryLoss
      fineReentry.reentry_extremal hcurrentCWA targetConstant targetLeft
      targetRight hconstant hcoarseLeft hdataRight hleftPos hleftTop hrightTop
      hcurrentOutput houtputLoss hrestore hvariation

/-- Exact one-ordered-pair callback consumed by the inner Lemma 4.11
iteration.  The resolution is the lower grid scale `rho`, the interval window
is `tau`, and the covering constant has the literal paper interpolation form.
All geometric data are constructed by `finalCandidate_for_interval_iteration`;
this wrapper only fixes the callback interface. -/
theorem orderedPairStep
    {fineDelta sigma fineInputLoss fineNormalizationLoss fineReentryLoss
      outerLoss coarseInputLoss coarseNormalizationLoss currentReentryLoss
      firstLoss reentryLoss reentryNormalizationLoss rootDensityLoss weightLoss
      sqrtStickyLoss secondLoss firstDensityLoss sqrtDensityLoss
      firstEpsilon₁ firstEpsilon₃ firstKappa sqrtEpsilon₁ sqrtEpsilon₃
      sqrtKappa middleLoss finalLoss floorLoss structuralBudget cellVolumeFloor
      discreteLoss outputLoss : ℝ}
    {fineSource : PureWZ2ExtremalConfiguration sigma fineInputLoss fineDelta}
    {fineNormalizationExponent outerLogExponent
      coarseNormalizationExponent : ℕ}
    {fineNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := fineNormalizationLoss) fineSource
      fineNormalizationExponent}
    {fineCurrent : WZ1PaperTubeShading fineNormalized.croppedFamily}
    {fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) fineNormalized fineCurrent}
    {rho : WZ2PaperRequestedScale fineDelta}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent}
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    {coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      coarseNormalizationExponent}
    {current : WZ1PaperTubeShading coarseNormalized.croppedFamily}
    {currentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := currentReentryLoss) coarseNormalized current}
    {schedule : Proposition63RichThreeCallScheduleData sigma sqrtStickyLoss}
    {tau sqrtRequested : WZ2PaperRequestedScale rho.1}
    {incidenceBound : ℝ}
    {currentMap : PaperWZ1WeakPlaneMapData current incidenceBound}
    {coefficient : NNReal} {firstC sqrtC : ENNReal}
    (parameters : Proposition63ConcreteNestedPairParameters
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (reentryNormalizationLoss := reentryNormalizationLoss)
      (rootDensityLoss := rootDensityLoss) (weightLoss := weightLoss)
      (secondLoss := secondLoss) (firstDensityLoss := firstDensityLoss)
      (sqrtDensityLoss := sqrtDensityLoss)
      (firstEpsilon₁ := firstEpsilon₁) (firstEpsilon₃ := firstEpsilon₃)
      (firstKappa := firstKappa)
      (sqrtEpsilon₁ := sqrtEpsilon₁) (sqrtEpsilon₃ := sqrtEpsilon₃)
      (sqrtKappa := sqrtKappa) (middleLoss := middleLoss)
      (finalLoss := finalLoss) fineReentry outer coarseNormalized current
      currentReentry schedule tau sqrtRequested incidenceBound currentMap
      coefficient firstC sqrtC)
    (critical : PureWZ2CroppedCriticalFloorSelectionData
      sigma floorLoss structuralBudget)
    (hcoarseCritical : rho.1 ≤ critical.delta₀)
    (hfinalStructural : finalLoss = critical.structuralLoss)
    (hcellVolumeFloor : 0 < cellVolumeFloor)
    (hcellBudget :
      ENNReal.ofReal cellVolumeFloor *
          Kakeya.realRpowENN sqrtRequested.1
            (sigma - sqrtStickyLoss) ≤
        Kakeya.realRpowENN rho.1 (sigma + floorLoss) *
          Kakeya.realRpowENN sqrtRequested.1 3)
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            (sqrtC * Kakeya.realRpowENN
              (sqrtRequested.1 / rho.1) (1 - sigma))) ≤
        (coverBudget : ENNReal))
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * fineDelta)
    (hcurrentCWA : WZ2PaperConvexWolffBound
      fineNormalized.croppedFamily
      (Kakeya.realRpowENN fineDelta (-fineReentryLoss)))
    (targetLeft targetRight : ENNReal)
    (hconstant :
      Proposition63NestedPointCoverData.FullGrainCells.nestedCandidateIntervalBound
            rho.1 rho.1 (8 * (coefficient : ℝ) * rho.1)
            (coefficient : ℝ) (13 ^ 3)
            (firstC * Kakeya.realRpowENN
              (tau.1 / rho.1) (1 - sigma)) ≤
        ENNReal.ofReal (Real.rpow fineDelta (-discreteLoss) *
          Real.rpow (tau.1 / rho.1) (1 - sigma)))
    (hleft : targetLeft ≤
      proposition63DependentFinePullbackLeft fineReentry outer
        (proposition63DependentCoarseReentryOfCurrent outer coarseNormalized
          current currentReentry parameters.ancestorEmbedding
          parameters.ancestor_tube_eq parameters.current_sub_outer
          parameters.ancestorRetentionFactor
          parameters.ancestor_retention_factor_pos
          parameters.ancestor_retention_factor_ne_top
          parameters.current_retained_mass).retentionFactor
        (coarseLeftFactor rho.1 sqrtRequested.1 cellVolumeFloor weightLoss
          coverBudget))
    (hright : proposition63DependentFinePullbackRight fineReentry
        (coarseRightFactor currentReentry.normalization.croppedFamily
          currentReentry.reentryNormalizationLoss rho.1) ≤ targetRight)
    (hleftPos : 0 < targetLeft) (hleftTop : targetLeft ≠ ⊤)
    (hrightTop : targetRight ≠ ⊤)
    (hcurrentOutput : fineReentryLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss targetLeft targetRight *
        Kakeya.realRpowENN fineDelta outputLoss ≤
      Kakeya.realRpowENN fineDelta fineReentryLoss) :
    ∃ next : WZ1PaperTubeShading fineNormalized.croppedFamily,
      PaperIsSubshading next fineCurrent ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union,
        next.pointMultiplicity point = fineCurrent.pointMultiplicity point) ∧
      WZ2PaperCroppedIsExtremal sigma outputLoss
        fineNormalized.croppedFamily next ∧
      WZ2PaperConvexWolffBound fineNormalized.croppedFamily
        (Kakeya.realRpowENN fineDelta (-outputLoss)) ∧
      PureWZ2IntervalCoveringAt next currentMap.planeMap rho.1
        (Real.toNNReal rho.1) (Real.toNNReal tau.1)
        (ENNReal.ofReal (Real.rpow fineDelta (-discreteLoss) *
          Real.rpow (tau.1 / rho.1) (1 - sigma))) ∧
      targetLeft * fineCurrent.mass ≤ targetRight * next.mass := by
  rcases parameters.finalCandidate_for_interval_iteration critical
      hcoarseCritical hfinalStructural hcellVolumeFloor hcellBudget
      coverBudget hcoverBudgetPos hcoverBudget scaleFactor hscaleFactor
      hrhoAligned hcurrentCWA
      (ENNReal.ofReal (Real.rpow fineDelta (-discreteLoss) *
        Real.rpow (tau.1 / rho.1) (1 - sigma))) targetLeft targetRight
      hconstant hleft hright hleftPos hleftTop hrightTop hcurrentOutput
      houtputLoss hrestore (spatialScale := 0) (variationScale := 0)
      (by simp) with
    ⟨next, hsub, hcubical, hmultiplicity, hextremal, hcwa, hcover, hmass, _⟩
  exact ⟨next, hsub, hcubical, hmultiplicity, hextremal, hcwa, hcover, hmass⟩

end Proposition63ConcreteNestedPairParameters

/-- Family-free small-scale budget for both grid prunings in one robust
Lemma 17 localization.  The strict gap records the actual power condition:
the restored source density must dominate `delta^(2 * epsilon₁)`, while the
single dyadic logarithm is absorbed before the runtime family is known. -/
structure Proposition63RobustGridPruningAbsorptionData
    (normalizationLoss epsilon₁ : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_tiny : delta₀ ≤ 1 / 100000
  absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    (((6 * 103 ^ 3 : ℕ) : ENNReal) *
        Kakeya.realRpowENN delta (2 * epsilon₁ - normalizationLoss)) *
        proposition63OneScaleLogEnvelope delta ≤
      (9 / 400 : ENNReal) * wz2PaperPureRefinementFraction delta 61

/-- Choose the robust grid-pruning threshold before the runtime tube family.
Only one `O(log(1/delta))` factor and the fixed 61-log refinement loss remain
after the tube-axis count and selected-cardinality cancellations. -/
theorem proposition63_robust_grid_pruning_absorption
    (normalizationLoss epsilon₁ : ℝ)
    (hgap : normalizationLoss < 2 * epsilon₁) :
    Nonempty (Proposition63RobustGridPruningAbsorptionData
      normalizationLoss epsilon₁) := by
  let gap : ℝ := 2 * epsilon₁ - normalizationLoss
  have gapPos : 0 < gap := by simpa only [gap] using sub_pos.mpr hgap
  let fixed : ENNReal :=
    45 * ((6 * 103 ^ 3 : ℕ) : ENNReal)
  have fixedTop : fixed ≠ ⊤ := by
    dsimp only [fixed]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have logExponentPos : 0 < (62 : ℕ) := by norm_num
  rcases exists_delta_C_pow_log_absorbed_ennreal
      fixed fixedTop proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg gapPos logExponentPos with
    ⟨logDelta, logDeltaPos, logDeltaOne, logAbsorb⟩
  let delta₀ : ℝ := min logDelta (min (1 / 100000) (Real.exp (-1)))
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := by dsimp only [delta₀]; positivity
    delta₀_le_one := (min_le_left _ _).trans logDeltaOne
    delta₀_le_tiny :=
      (min_le_right _ _).trans (min_le_left _ _)
    absorb := ?_
  }⟩
  intro delta deltaPos deltaLe
  have deltaLeLog : delta ≤ logDelta := deltaLe.trans (min_le_left _ _)
  have deltaLeOne : delta ≤ 1 := deltaLeLog.trans logDeltaOne
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
        nlinarith [mul_nonneg (sub_nonneg.mpr coefficientOne)
          (show 0 ≤ 1 + Real.log delta⁻¹ by linarith)]
  have logTermPos : 0 < logTerm :=
    ENNReal.ofReal_pos.mpr <|
      Real.log_pos (one_lt_one_div deltaPos deltaLtOne)
  have logTermTop : logTerm ≠ ⊤ := by simp [logTerm]
  have logPowerPos : 0 < logTerm ^ 61 := by positivity
  have logPowerTop : logTerm ^ 61 ≠ ⊤ :=
    ENNReal.pow_ne_top logTermTop
  have logsCombined :
      proposition63OneScaleLogEnvelope delta * logTerm ^ 61 ≤
        proposition63OneScaleLogEnvelope delta ^ 62 := by
    calc
      proposition63OneScaleLogEnvelope delta * logTerm ^ 61 ≤
          proposition63OneScaleLogEnvelope delta *
            proposition63OneScaleLogEnvelope delta ^ 61 := by gcongr
      _ = proposition63OneScaleLogEnvelope delta ^ 62 := by
        rw [show (62 : ℕ) = 1 + 61 by norm_num, pow_add, pow_one]
  have logarithmicAbsorption :
      fixed * proposition63OneScaleLogEnvelope delta ^ 62 ≤
        Kakeya.realRpowENN delta (-gap) := by
    simpa [proposition63OneScaleLogEnvelope] using
      logAbsorb delta deltaPos deltaLeLog
  have multiplied :
      (((6 * 103 ^ 3 : ℕ) : ENNReal) *
          Kakeya.realRpowENN delta gap *
          proposition63OneScaleLogEnvelope delta) * logTerm ^ 61 ≤
        (9 / 400 : ENNReal) := by
    have fixedDomination :
        ((6 * 103 ^ 3 : ℕ) : ENNReal) ≤
          (9 / 400 : ENNReal) * fixed := by
      dsimp only [fixed]
      calc
        ((6 * 103 ^ 3 : ℕ) : ENNReal) =
            1 * ((6 * 103 ^ 3 : ℕ) : ENNReal) := by simp
        _ ≤ ((9 / 400 : ENNReal) * 45) *
            ((6 * 103 ^ 3 : ℕ) : ENNReal) := by
          apply mul_le_mul_right'
          rw [← ENNReal.toReal_le_toReal (by norm_num)
            (ENNReal.mul_ne_top
              (ENNReal.div_ne_top (by norm_num) (by norm_num))
              (by norm_num))]
          norm_num
        _ = (9 / 400 : ENNReal) *
            (45 * ((6 * 103 ^ 3 : ℕ) : ENNReal)) := by ring
    have powerIdentity : Kakeya.realRpowENN delta (-gap) *
        Kakeya.realRpowENN delta gap = 1 := by
      rw [← realRpowENN_add deltaPos]
      have exponentZero : -gap + gap = 0 := by ring
      rw [exponentZero]
      change ENNReal.ofReal (Real.rpow delta 0) = 1
      simp
    calc
      (((6 * 103 ^ 3 : ℕ) : ENNReal) *
            Kakeya.realRpowENN delta gap *
            proposition63OneScaleLogEnvelope delta) * logTerm ^ 61 =
          ((6 * 103 ^ 3 : ℕ) : ENNReal) *
            (proposition63OneScaleLogEnvelope delta * logTerm ^ 61) *
            Kakeya.realRpowENN delta gap := by ring
      _ ≤ ((9 / 400 : ENNReal) * fixed) *
            (proposition63OneScaleLogEnvelope delta * logTerm ^ 61) *
            Kakeya.realRpowENN delta gap := by gcongr
      _ = (9 / 400 : ENNReal) *
            (fixed *
              (proposition63OneScaleLogEnvelope delta * logTerm ^ 61)) *
            Kakeya.realRpowENN delta gap := by ring
      _ ≤ (9 / 400 : ENNReal) *
            (fixed * proposition63OneScaleLogEnvelope delta ^ 62) *
            Kakeya.realRpowENN delta gap := by gcongr
      _ ≤ (9 / 400 : ENNReal) * Kakeya.realRpowENN delta (-gap) *
            Kakeya.realRpowENN delta gap := by gcongr
      _ = 9 / 400 := by
        rw [show (9 / 400 : ENNReal) * Kakeya.realRpowENN delta (-gap) *
            Kakeya.realRpowENN delta gap =
          (9 / 400 : ENNReal) *
            (Kakeya.realRpowENN delta (-gap) *
              Kakeya.realRpowENN delta gap) by ring]
        rw [powerIdentity, mul_one]
  rw [wz2PaperPureRefinementFraction, ← ENNReal.inv_pow]
  change (((6 * 103 ^ 3 : ℕ) : ENNReal) *
      Kakeya.realRpowENN delta gap) *
      proposition63OneScaleLogEnvelope delta ≤
    (9 / 400 : ENNReal) * (logTerm ^ 61)⁻¹
  rw [show (9 / 400 : ENNReal) * (logTerm ^ 61)⁻¹ =
      (9 / 400 : ENNReal) / logTerm ^ 61 by
        simp only [div_eq_mul_inv]]
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl logPowerPos.ne') (Or.inl logPowerTop)).2
  simpa only [mul_assoc, mul_comm, mul_left_comm] using multiplied

/-- Apply the family-free grid-pruning budget to the exact selected family
generated by the runtime target rich call. -/
theorem Proposition63RichTerminalStickyData.tauGridPruningError_of_absorption
    {delta sigma outerSourceLoss outerNormalizationLoss targetReentryLoss
      targetLoss tau epsilon₁ : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    {targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current}
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (absorption : Proposition63RobustGridPruningAbsorptionData
      targetReentry.reentryNormalizationLoss epsilon₁)
    (hdelta : delta ≤ absorption.delta₀)
    (htau : 0 < tau) (htauOne : tau ≤ 1) :
    proposition63TauGridPruningError target.data.selected.family tau epsilon₁ ≤
      (9 / 400 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
            ENNReal)) := by
  apply target.tauGridPruningError_le htargetReentryLoss htau htauOne
    (hdelta.trans absorption.delta₀_le_tiny |>.trans (by norm_num))
  have selectedLog :
      ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal) ≤
        proposition63OneScaleLogEnvelope delta := by
    have selectedCard : target.data.selected.family.card ≤
        targetReentry.normalization.croppedFamily.card :=
      by
        simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
          target.data.selected.embedding
          target.data.selected.embedding.injective
    have logNat : Nat.log 2 target.data.selected.family.card + 1 ≤
        Nat.log 2 (2 * targetReentry.normalization.croppedFamily.card) + 1 :=
      Nat.add_le_add_right (Nat.log_mono_right <|
        selectedCard.trans <| Nat.le_mul_of_pos_left _ (by norm_num)) 1
    have logENN :
        ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal) ≤
          ((Nat.log 2
              (2 * targetReentry.normalization.croppedFamily.card) + 1 : ℕ) :
            ENNReal) := by
      exact_mod_cast logNat
    exact logENN.trans <|
      (by
        simpa only [Nat.cast_add, Nat.cast_one] using
          proposition63_cropped_cardLog_le_oneScaleEnvelope
            targetReentry.normalization
            (hdelta.trans absorption.delta₀_le_tiny))
  exact (mul_le_mul_left' selectedLog
    (((6 * 103 ^ 3 : ℕ) : ENNReal) *
      Kakeya.realRpowENN delta
        (2 * epsilon₁ - targetReentry.reentryNormalizationLoss))).trans <|
    absorption.absorb targetReentry.reentry_extremal.delta_pos hdelta

/-- Specialize the two family-free receipts used by a robust localization to
the actual runtime target.  The selected-family cardinality and both terminal
multiplicities are eliminated here, after the rich calls have been run. -/
theorem Proposition63RichTerminalStickyData.robustTauRuntimeReceipts_of_absorptions
    {delta sigma robustExponent outerLoss outerSourceLoss
      outerNormalizationLoss targetReentryLoss targetNormalizationLoss
      targetLoss tau epsilon₁ weightLoss : ℝ}
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
    (hnormalization : targetReentry.reentryNormalizationLoss =
      targetNormalizationLoss)
    (gridAbsorption : Proposition63RobustGridPruningAbsorptionData
      targetNormalizationLoss epsilon₁)
    (crossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        robustExponent outerLoss targetNormalizationLoss weightLoss 4
        levelCount)
    (hdeltaGrid : delta ≤ gridAbsorption.delta₀)
    (hdeltaCross : delta ≤ crossAbsorption.delta₀)
    (hrobustScale : robustScale.1 = Real.rpow delta robustExponent)
    (hweight : targetReentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta weightLoss)
    (hweightUpper : targetReentry.weightUpper =
      (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2)
    (hlevelCount : targetReentry.levelCount = levelCount)
    (htau : 0 < tau) (htauOne : tau ≤ 1)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000) :
    proposition63TauGridPruningError target.data.selected.family tau
        epsilon₁ ≤
          (9 / 400 : ENNReal) *
            (target.data.refined.mass /
              ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
                ENNReal)) ∧
      4 * (stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal)) ≤
        ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
          ENNReal) := by
  subst targetNormalizationLoss
  constructor
  · exact target.tauGridPruningError_of_absorption htargetReentryLoss
      gridAbsorption hdeltaGrid htau htauOne
  · exact proposition63_two_rich_cross_degree_scaled_of_absorption outer
      targetReentry htargetReentryLoss target crossAbsorption hdeltaCross
      hrobustScale hweight hweightUpper hlevelCount hrobustSmall


/-- Runtime payload for the middle two rich calls of the four-call schedule.
It records the first robust cover on the target terminal's exact ambient
zero-extension, so that `target` is definitionally the outer witness for the
next robust localization. -/
structure Proposition63FirstRobustTargetAmbientData
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetNormalizationLoss targetLoss tau firstLoss
      weightLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    (robustScale : WZ2PaperRequestedScale delta)
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    (targetScale : WZ2PaperRequestedScale delta)
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (levelCount : ℕ) (planeMap : Point3 → Point3)
    (constant : ENNReal) where
  first : Proposition63LiftedPointCoverData
    (outputLoss := firstLoss) (queryScale := delta)
    (spatialRadius := tau) targetReentry.normalization
    (extendShading target.data.selected target.data.refined) planeMap constant
  firstRetainedFactor : first.retainedFactor =
    (81 / 400 : ENNReal) *
      (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
        ENNReal))⁻¹
  target_normalization_loss :
    targetReentry.reentryNormalizationLoss = targetNormalizationLoss
  targetCanonicalWeight : targetReentry.normalizationWeight =
    proposition63CanonicalReentryWeight delta weightLoss
  targetCanonicalLevel : targetReentry.levelCount = levelCount


/-- Run the first robust localization after the actual outer/target rich pair
has been generated, using only pre-runtime grid and factor-four absorption
records.  The restored cover lives on the target terminal's zero-extension,
which is the precise current family for the next rich call. -/
theorem Proposition63RichTerminalStickyData.targetAmbientPointCoverOfAbsorptions
    {delta sigma robustExponent outerLoss outerSourceLoss
      outerNormalizationLoss targetReentryLoss targetNormalizationLoss
      targetLoss tau epsilon₁ epsilon₃ weightLoss parentLoss outputLoss : ℝ}
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
    (hcurrentSubOuter : PaperIsSubshading current
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (hnormalization : targetReentry.reentryNormalizationLoss =
      targetNormalizationLoss)
    (gridAbsorption : Proposition63RobustGridPruningAbsorptionData
      targetNormalizationLoss epsilon₁)
    (crossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        robustExponent outerLoss targetNormalizationLoss weightLoss 4
        levelCount)
    (hdeltaGridAbsorption : delta ≤ gridAbsorption.delta₀)
    (hdeltaCrossAbsorption : delta ≤ crossAbsorption.delta₀)
    (hrobustScale : robustScale.1 = Real.rpow delta robustExponent)
    (hweight : targetReentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta weightLoss)
    (hweightUpper : targetReentry.weightUpper =
      (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2)
    (hlevelCount : targetReentry.levelCount = levelCount)
    (planeMap : Point3 → Point3) (incidenceBound : ℝ)
    (hplaneUnit : ∀ point ∈ target.data.refined.union,
      ‖planeMap point‖ = 1)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneIncidence : ∀ index point,
      point ∈ target.data.refined.carrier index →
        |@Inner.inner ℝ Point3 _
          (target.data.selected.family.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (hdeltaTau : delta ≤ tau)
    (hdeltaGrid : delta ≤ gridSide (tau / 2))
    (htau : 0 < tau) (htauOne : tau ≤ 1)
    (hperiodic : 50 * delta ≤ gridSide (tau / 2))
    (hboundaryCWA :
      let side := gridSide (tau / 2)
      targetReentry.normalization.croppedFamily.enncard *
          ((24000000 : ENNReal) *
            (Kakeya.realRpowENN delta
                (-targetReentry.reentryNormalizationLoss) *
                wz2PaperBoundaryGeometryConstant + 1) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (Real.sqrt (delta / side))) ≤
        (1 / 10 : ENNReal) * target.data.refined.mass)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : targetScale.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (htargetTau : targetScale.1 ≤ 3 * tau)
    (htauSq : tau ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              targetReentry.reentryNormalizationLoss targetLoss
              targetScale.1 tau /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                tau ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta tau incidenceBound
              coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN (tau / delta) (1 - sigma))
    (hnormalizationParent :
      targetReentry.reentryNormalizationLoss ≤ parentLoss)
    (hparentRetention :
      Kakeya.realRpowENN delta parentLoss ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            targetReentry.reentryNormalizationLoss)
    (hparentOutput : parentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss
        ((81 / 400 : ENNReal) *
          (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
            ENNReal))⁻¹) 1 *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta parentLoss) :
    ∃ result : Proposition63LiftedPointCoverData
      (outputLoss := outputLoss) (queryScale := delta)
      (spatialRadius := tau) targetReentry.normalization
      (extendShading target.data.selected target.data.refined) planeMap
      (C * Kakeya.realRpowENN (tau / delta) (1 - sigma)),
      result.retainedFactor =
        (81 / 400 : ENNReal) *
          (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
            ENNReal))⁻¹ := by
  rcases Proposition63RichTerminalStickyData.robustTauRuntimeReceipts_of_absorptions
      (outer := outer) (targetReentry := targetReentry)
      (target := target) htargetReentryLoss hnormalization gridAbsorption
      crossAbsorption hdeltaGridAbsorption hdeltaCrossAbsorption
      hrobustScale hweight hweightUpper hlevelCount htau htauOne
      hrobustSmall with
    ⟨hgridError, hcrossCall⟩
  exact proposition63_robust_tau_target_ambient_point_cover_data_of_cwa outer
    targetReentry hcurrentSubOuter htargetReentryLoss target planeMap
    incidenceBound hplaneUnit hplaneLipschitz hplaneIncidence hdeltaTau
    hdeltaGrid htau htauOne hperiodic hboundaryCWA hgridError hrobustSmall
    hcrossCall hkappa htargetSmall hdeltaSmall htargetTau htauSq hsigma
    hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale hdeltaLog hlog
    haxis C harithmetic hnormalizationParent hparentRetention hparentOutput
    houtputLoss hrestore

/-- Construct the first restored robust cover from an already-generated
outer/target rich pair.  Both runtime combinatorial estimates are discharged
by preselected family-free absorption records, and the boundary estimate is
reduced to one scalar inequality. -/
theorem proposition63_first_robust_target_ambient_of_absorptions
    {delta sigma robustExponent outerLoss outerSourceLoss
      outerNormalizationLoss targetReentryLoss targetNormalizationLoss
      targetLoss tau epsilon₁ epsilon₃ weightLoss parentLoss firstLoss : ℝ}
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
    (hnormalization : targetReentry.reentryNormalizationLoss =
      targetNormalizationLoss)
    (gridAbsorption : Proposition63RobustGridPruningAbsorptionData
      targetNormalizationLoss epsilon₁)
    (crossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        robustExponent outerLoss targetNormalizationLoss weightLoss 4
        levelCount)
    (hdeltaGridAbsorption : delta ≤ gridAbsorption.delta₀)
    (hdeltaCrossAbsorption : delta ≤ crossAbsorption.delta₀)
    (hrobustScale : robustScale.1 = Real.rpow delta robustExponent)
    (hweight : targetReentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta weightLoss)
    (hweightUpper : targetReentry.weightUpper =
      (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2)
    (hlevelCount : targetReentry.levelCount = levelCount)
    {incidenceBound : ℝ}
    (targetMap : PaperWZ1WeakPlaneMapData target.data.refined
      incidenceBound)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient targetMap.planeMap)
    (hdeltaTau : delta ≤ tau)
    (hdeltaGrid : delta ≤ gridSide (tau / 2))
    (htau : 0 < tau) (htauOne : tau ≤ 1)
    (hperiodic : 50 * delta ≤ gridSide (tau / 2))
    (hboundaryScalar :
      (24000000 : ENNReal) *
          (Kakeya.realRpowENN delta
              (-targetReentry.reentryNormalizationLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          Kakeya.realRpowENN delta 2 *
          ENNReal.ofReal (Real.sqrt (delta / gridSide (tau / 2))) ≤
        (1 / 10 : ENNReal) * wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            (targetReentry.reentryNormalizationLoss + 2))
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : targetScale.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (htargetTau : targetScale.1 ≤ 3 * tau)
    (htauSq : tau ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              targetReentry.reentryNormalizationLoss targetLoss
              targetScale.1 tau /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                tau ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta tau incidenceBound
              coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN (tau / delta) (1 - sigma))
    (hnormalizationParent :
      targetReentry.reentryNormalizationLoss ≤ parentLoss)
    (hparentRetention :
      Kakeya.realRpowENN delta parentLoss ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            targetReentry.reentryNormalizationLoss)
    (hparentOutput : parentLoss ≤ firstLoss)
    (hfirstLoss : 0 < firstLoss)
    (hrestore : proposition63Lemma43MassLoss
        ((81 / 400 : ENNReal) *
          (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
            ENNReal))⁻¹) 1 *
          Kakeya.realRpowENN delta firstLoss ≤
        Kakeya.realRpowENN delta parentLoss) :
    Nonempty (Proposition63FirstRobustTargetAmbientData
      (targetNormalizationLoss := targetNormalizationLoss)
      (tau := tau) (firstLoss := firstLoss) (weightLoss := weightLoss)
      robustScale outer targetReentry htargetReentryLoss targetScale target
      levelCount targetMap.planeMap
      (C * Kakeya.realRpowENN (tau / delta) (1 - sigma))) := by
  have hboundaryCWA := target.boundaryCWA_of_scalar htargetReentryLoss
    (hdeltaSmall.trans (by norm_num)) hboundaryScalar
  rcases outer.targetAmbientPointCoverOfAbsorptions targetReentry
      (fun _ _ hpoint => hpoint) htargetReentryLoss target hnormalization
      gridAbsorption crossAbsorption hdeltaGridAbsorption
      hdeltaCrossAbsorption hrobustScale hweight hweightUpper hlevelCount
      targetMap.planeMap incidenceBound targetMap.unit hplaneLipschitz
      targetMap.incidence hdeltaTau hdeltaGrid htau htauOne hperiodic
      hboundaryCWA hrobustSmall hkappa htargetSmall hdeltaSmall htargetTau
      htauSq hsigma hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale
      hdeltaLog hlog haxis C harithmetic hnormalizationParent
      hparentRetention hparentOutput hfirstLoss hrestore with
    ⟨first, hfactor⟩
  exact ⟨{
    first := first
    firstRetainedFactor := hfactor
    target_normalization_loss := hnormalization
    targetCanonicalWeight := hweight
    targetCanonicalLevel := hlevelCount
  }⟩


/-- Complete the second robust localization with its grid and factor-four
cross-degree receipts fixed before the runtime rich target is generated.  The
remaining CWA boundary, Cordoba, and restoration inequalities are kept
explicit for the next family-free absorption layer. -/
theorem Proposition63LiftedPointCoverData.toNestedAnalyticViaThirdRobustOfAbsorptions
    {delta sigma robustExponent outerLoss outerSourceLoss
      outerNormalizationLoss firstLoss tauScale densityLoss reentryLoss
      reentryNormalizationLoss weightLoss sqrtStickyLoss secondLoss epsilon₁
      epsilon₃ : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {incidenceBound : ℝ}
    (currentMap : PaperWZ1WeakPlaneMapData
      (extendShading outer.data.selected outer.data.refined) incidenceBound)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient currentMap.planeMap)
    (tauConstant : ENNReal)
    (first : Proposition63LiftedPointCoverData
      (outputLoss := firstLoss) (queryScale := delta)
      (spatialRadius := tauScale) outerReentry.toNormalizationData
      (extendShading outer.data.selected outer.data.refined)
      currentMap.planeMap tauConstant)
    (absorption : Proposition63CurrentReentryAbsorptionData
      outerSourceLoss outerNormalizationLoss densityLoss firstLoss weightLoss
      reentryLoss
      (proposition63CanonicalNearbyLevelCount outerNormalizationLoss))
    (hdeltaAbsorption : delta ≤ absorption.delta₀)
    (houterNormalizationLoss : 0 < outerNormalizationLoss)
    (htwoNormalization : 2 * outerNormalizationLoss ≤ reentryLoss)
    (hfirstReentry : firstLoss ≤ reentryLoss)
    (hfirstLoss : 0 < firstLoss)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2)
    (richSchedule : Proposition63RichThreeCallScheduleData
      sigma sqrtStickyLoss)
    (hreentryLoss : reentryLoss = richSchedule.third.sourceLoss)
    (hthirdNormalization :
      reentryNormalizationLoss = richSchedule.third.normalizationLoss)
    (hdeltaThird : delta ≤ richSchedule.third.delta₀)
    (sqrtRequested : WZ2PaperRequestedScale delta)
    (hsqrtLower : Real.rpow delta (1 - sqrtStickyLoss) ≤ sqrtRequested.1)
    (hsqrtUpper : sqrtRequested.1 ≤ Real.rpow delta sqrtStickyLoss)
    (hdeltaGrid : delta ≤ gridSide (sqrtRequested.1 / 2))
    (hsqrtOne : sqrtRequested.1 ≤ 1)
    (hperiodic : 50 * delta ≤ gridSide (sqrtRequested.1 / 2))
    (hboundaryCWA : ∀ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) outerReentry.toNormalizationData
        first.state.shading,
      ∀ target : Proposition63RichTerminalStickyData
        (outputLoss := sqrtStickyLoss) reentry.normalization.croppedRefined
        (reentry.normalization.toPropStickyReentryData
          (by rw [hreentryLoss]; exact richSchedule.third.sourceLoss_pos)
          reentry.reentry_normalization_loss_pos) sqrtRequested,
      let side := gridSide (sqrtRequested.1 / 2)
      reentry.normalization.croppedFamily.enncard *
          ((24000000 : ENNReal) *
            (Kakeya.realRpowENN delta
                (-reentry.reentryNormalizationLoss) *
                wz2PaperBoundaryGeometryConstant + 1) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (Real.sqrt (delta / side))) ≤
        (1 / 10 : ENNReal) * target.data.refined.mass)
    (gridAbsorption : Proposition63RobustGridPruningAbsorptionData
      reentryNormalizationLoss epsilon₁)
    (hdeltaGridAbsorption : delta ≤ gridAbsorption.delta₀)
    (crossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        robustExponent outerLoss reentryNormalizationLoss weightLoss 4
        (proposition63CanonicalNearbyLevelCount outerNormalizationLoss))
    (hdeltaCrossAbsorption : delta ≤ crossAbsorption.delta₀)
    (hrobustScale : robustScale.1 = Real.rpow delta robustExponent)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : sqrtRequested.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (hsqrtSq : sqrtRequested.1 ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic : ∀ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) outerReentry.toNormalizationData
        first.state.shading,
      ∀ target : Proposition63RichTerminalStickyData
        (outputLoss := sqrtStickyLoss) reentry.normalization.croppedRefined
        (reentry.normalization.toPropStickyReentryData
          (by rw [hreentryLoss]; exact richSchedule.third.sourceLoss_pos)
          reentry.reentry_normalization_loss_pos) sqrtRequested,
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              reentry.reentryNormalizationLoss sqrtStickyLoss
              sqrtRequested.1 sqrtRequested.1 /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                sqrtRequested.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta sqrtRequested.1
              incidenceBound coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN
          (sqrtRequested.1 / delta) (1 - sigma))
    (hnormalizationSecond : reentryNormalizationLoss ≤ secondLoss)
    (hsecondLoss : 0 < secondLoss)
    (hrestore : ∀ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) outerReentry.toNormalizationData
        first.state.shading,
      ∀ target : Proposition63RichTerminalStickyData
        (outputLoss := sqrtStickyLoss) reentry.normalization.croppedRefined
        (reentry.normalization.toPropStickyReentryData
          (by rw [hreentryLoss]; exact richSchedule.third.sourceLoss_pos)
          reentry.reentry_normalization_loss_pos) sqrtRequested,
      proposition63Lemma43MassLoss
          ((81 / 400 : ENNReal) *
            (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
              ENNReal))⁻¹ *
            wz2PaperPureRefinementFraction delta 61) 1 *
            Kakeya.realRpowENN delta secondLoss ≤
          Kakeya.realRpowENN delta reentry.reentryNormalizationLoss) :
    Nonempty (Proposition63NestedPointCoverAnalyticData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (queryScale := delta) (tauScale := tauScale)
      (sqrtScale := sqrtRequested.1) outerReentry.toNormalizationData
      currentMap.planeMap tauConstant
      (C * Kakeya.realRpowENN
        (sqrtRequested.1 / delta) (1 - sigma))) := by
  have firstSubNormalized : PaperIsSubshading first.state.shading
      outerReentry.toNormalizationData.croppedRefined := by
    exact fun index point hpoint =>
      extendShading_subshading outer.data.selected outer.data.subshading index <|
        first.state.subshading index hpoint
  rcases first.nextReentryAndThirdRichOfAbsorption
      outerReentry.toNormalizationData firstSubNormalized absorption
      hdeltaAbsorption houterNormalizationLoss htwoNormalization
      hfirstReentry hfirstLoss hreentryNormalizationLoss hreentryHalf
      richSchedule hreentryLoss hthirdNormalization hdeltaThird sqrtRequested
      hsqrtLower hsqrtUpper with
    ⟨reentry, ⟨target⟩, hweight, hweightUpper, hlevel,
      hnormalization⟩
  let firstMap : PaperWZ1WeakPlaneMapData first.state.shading incidenceBound :=
    paperWeakPlaneMapRestrict currentMap first.state.subshading
  let normalizedMap : PaperWZ1WeakPlaneMapData
      reentry.normalization.croppedRefined incidenceBound :=
    reentry.normalizedPlaneMap firstMap
  let targetMap : PaperWZ1WeakPlaneMapData
      target.data.refined incidenceBound :=
    target.terminalPlaneMap normalizedMap
  have htargetReentryLoss : 0 < reentryLoss := by
    rw [hreentryLoss]
    exact richSchedule.third.sourceLoss_pos
  have receipts :=
    Proposition63RichTerminalStickyData.robustTauRuntimeReceipts_of_absorptions
      outer reentry htargetReentryLoss target hnormalization gridAbsorption
      crossAbsorption hdeltaGridAbsorption hdeltaCrossAbsorption hrobustScale
      hweight hweightUpper hlevel
      (reentry.reentry_extremal.delta_pos.trans_le
        sqrtRequested.2.1) hsqrtOne hrobustSmall
  rcases receipts with ⟨hgridError, hcrossCall⟩
  have htargetPos : 0 < sqrtRequested.1 :=
    reentry.reentry_extremal.delta_pos.trans_le sqrtRequested.2.1
  rcases proposition63_robust_tau_local_point_cover_data_of_cwa outer reentry
      first.state.subshading htargetReentryLoss target currentMap.planeMap
      incidenceBound targetMap.unit hplaneLipschitz targetMap.incidence
      sqrtRequested.2.1 hdeltaGrid htargetPos hsqrtOne hperiodic
      (hboundaryCWA reentry target) hgridError hrobustSmall hcrossCall hkappa
      htargetSmall hdeltaSmall (by linarith [htargetPos]) hsqrtSq hsigma
      hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale hdeltaLog hlog
      haxis C (harithmetic reentry target)
      (hdeltaSmall.trans_lt (by norm_num))
      (hnormalization.trans_le hnormalizationSecond) hsecondLoss
      (hrestore reentry target) with
    ⟨second, _hfactor, hsecondSubset⟩
  exact Proposition63NestedPointCoverAnalyticData.ofLiftedPointCovers
    outerReentry.toNormalizationData
    (extendShading outer.data.selected outer.data.refined) currentMap.planeMap
    tauConstant
    (C * Kakeya.realRpowENN (sqrtRequested.1 / delta) (1 - sigma))
    first reentry sqrtRequested rfl target.data second hsecondSubset

/-- Family-free scalar receipt for the sharp two-band Phase-1 restoration.
The fine and coarse multiplicity levels have already cancelled.  What
remains is one current-reentry regularization, its physical weight upper
bound, the rich terminal regularity, and the fixed 61-log refinement loss. -/
structure Proposition63FullGrainDensityAbsorptionData
    (weightLoss reentryNormalizationLoss criticalLoss : ℝ)
    (levelCount : ℕ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_tiny : delta₀ ≤ 1 / 100000
  absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
        (((8 : ENNReal) * proposition63OneScaleLogEnvelope delta ^
            (levelCount + 2)) *
          ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2) *
          ((4 : ENNReal) *
            proposition63OneScaleLogEnvelope delta ^ 10 *
            (wz2PaperPureRefinementFraction delta 61)⁻¹)) *
        Kakeya.realRpowENN delta criticalLoss ≤
      proposition63CanonicalReentryWeight delta weightLoss *
        Kakeya.realRpowENN delta reentryNormalizationLoss

/-- Choose the common-density threshold before the runtime family and rich
terminal.  The strict loss gap pays exactly the logarithmic residue left by
the two multiplicity-band cancellations. -/
theorem proposition63_full_grain_density_absorption
    (weightLoss reentryNormalizationLoss criticalLoss : ℝ)
    (levelCount : ℕ)
    (hgap : 0 < criticalLoss - reentryNormalizationLoss - weightLoss) :
    Nonempty (Proposition63FullGrainDensityAbsorptionData
      weightLoss reentryNormalizationLoss criticalLoss levelCount) := by
  let gap : ℝ := criticalLoss - reentryNormalizationLoss - weightLoss
  have gapPos : 0 < gap := by simpa only [gap] using hgap
  let geometry : ENNReal :=
    (55296 : ENNReal) * Kakeya.deltaTubeVolume 1
  let fixed : ENNReal := geometry * 8 * geometry * 4
  have geometryTop : geometry ≠ ⊤ := by
    dsimp only [geometry]
    exact ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top
  have fixedTop : fixed ≠ ⊤ := by
    dsimp only [fixed]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top geometryTop (by norm_num)) geometryTop)
      (by norm_num)
  let logExponent : ℕ := levelCount + 73
  have logExponentPos : 0 < logExponent := by
    dsimp only [logExponent]
    omega
  rcases exists_delta_C_pow_log_absorbed_ennreal
      fixed fixedTop proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg gapPos logExponentPos with
    ⟨logDelta, logDeltaPos, logDeltaOne, logAbsorb⟩
  let delta₀ : ℝ := min logDelta (min (1 / 100000) (Real.exp (-1)))
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := by dsimp only [delta₀]; positivity
    delta₀_le_one := (min_le_left _ _).trans logDeltaOne
    delta₀_le_tiny :=
      (min_le_right _ _).trans (min_le_left _ _)
    absorb := ?_
  }⟩
  intro delta deltaPos deltaLe
  have deltaLeLog : delta ≤ logDelta :=
    deltaLe.trans (min_le_left _ _)
  have deltaLeOne : delta ≤ 1 := deltaLeLog.trans logDeltaOne
  have deltaLtOne : delta < 1 := by
    exact deltaLe.trans_lt <|
      (min_le_right _ _).trans_lt <|
        (min_le_right _ _).trans_lt
          (Real.exp_lt_one_iff.mpr (by norm_num))
  let logTerm : ENNReal := ENNReal.ofReal (Real.log (1 / delta))
  have logTermLe :
      logTerm ≤ proposition63OneScaleLogEnvelope delta := by
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
  have powerIdentity :
      Kakeya.realRpowENN delta (-gap) *
          (Kakeya.realRpowENN delta 2 *
            Kakeya.realRpowENN delta criticalLoss) =
        proposition63CanonicalReentryWeight delta weightLoss *
          Kakeya.realRpowENN delta reentryNormalizationLoss := by
    unfold proposition63CanonicalReentryWeight
    rw [← realRpowENN_add deltaPos]
    rw [← realRpowENN_add deltaPos]
    rw [← realRpowENN_add deltaPos]
    congr 1
    dsimp only [gap]
    ring
  have logTermPos : 0 < logTerm := by
    exact ENNReal.ofReal_pos.mpr <|
      Real.log_pos (one_lt_one_div deltaPos deltaLtOne)
  have logTermTop : logTerm ≠ ⊤ := by simp [logTerm]
  have logPowerPos : 0 < logTerm ^ 61 := by positivity
  have logPowerTop : logTerm ^ 61 ≠ ⊤ :=
    ENNReal.pow_ne_top logTermTop
  have multiplied :
      (fixed * proposition63OneScaleLogEnvelope delta ^
          (levelCount + 12) *
        (Kakeya.realRpowENN delta 2 *
          Kakeya.realRpowENN delta criticalLoss)) * logTerm ^ 61 ≤
        proposition63CanonicalReentryWeight delta weightLoss *
          Kakeya.realRpowENN delta reentryNormalizationLoss := by
    calc
      (fixed * proposition63OneScaleLogEnvelope delta ^
            (levelCount + 12) *
          (Kakeya.realRpowENN delta 2 *
            Kakeya.realRpowENN delta criticalLoss)) * logTerm ^ 61 =
          (fixed *
            (proposition63OneScaleLogEnvelope delta ^
              (levelCount + 12) * logTerm ^ 61)) *
            (Kakeya.realRpowENN delta 2 *
              Kakeya.realRpowENN delta criticalLoss) := by ring
      _ ≤ (fixed * proposition63OneScaleLogEnvelope delta ^ logExponent) *
            (Kakeya.realRpowENN delta 2 *
              Kakeya.realRpowENN delta criticalLoss) := by gcongr
      _ ≤ Kakeya.realRpowENN delta (-gap) *
            (Kakeya.realRpowENN delta 2 *
              Kakeya.realRpowENN delta criticalLoss) := by gcongr
      _ = proposition63CanonicalReentryWeight delta weightLoss *
          Kakeya.realRpowENN delta reentryNormalizationLoss := powerIdentity
  rw [wz2PaperPureRefinementFraction, ← ENNReal.inv_pow, inv_inv]
  rw [show levelCount + 12 = (levelCount + 2) + 10 by omega, pow_add]
    at multiplied
  simpa only [fixed, geometry, logTerm, mul_assoc, mul_comm, mul_left_comm]
    using multiplied

/-- Apply the family-free density receipt to the actual dyadic re-entry and
rich terminal.  This is the precise point where the terminal regularity is
replaced by its fixed logarithmic envelope. -/
theorem Proposition63DyadicCurrentReentryData.commonDensityLift_of_absorption
    {delta sigma initialInputLoss normalizationLoss densityLoss incidence
      currentLoss dyadicLoss weightLoss reentryLoss reentryNormalizationLoss
      producerLoss criticalLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent levelCount : ℕ}
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
    (hreentrySourceLoss : 0 < reentryLoss)
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := producerLoss)
      dyadic.reentry.normalization.croppedRefined
      (dyadic.reentry.normalization.toPropStickyReentryData
        hreentrySourceLoss
        dyadic.reentry.reentry_normalization_loss_pos) rho)
    (absorption : Proposition63FullGrainDensityAbsorptionData
      weightLoss reentryNormalizationLoss criticalLoss levelCount)
    (hdeltaPos : 0 < delta) (hdeltaLe : delta ≤ absorption.delta₀)
    (hweight : dyadic.reentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta weightLoss)
    (hweightUpper : dyadic.reentry.weightUpper =
      (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2)
    (hlevelCount : dyadic.reentry.levelCount = levelCount)
    (hnormalizationLoss :
      dyadic.reentry.reentryNormalizationLoss = reentryNormalizationLoss) :
    ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
        (dyadic.reentry.regularized.regularizationLoss *
          dyadic.reentry.weightUpper *
            ((4 * (rich.terminal.regularity : ENNReal)) *
              (wz2PaperPureRefinementFraction delta 61)⁻¹)) *
        Kakeya.realRpowENN delta criticalLoss ≤
      dyadic.reentry.normalizationWeight *
        Kakeya.realRpowENN delta
          dyadic.reentry.reentryNormalizationLoss := by
  have deltaOne : delta ≤ 1 :=
    hdeltaLe.trans absorption.delta₀_le_one
  have regularizationBound :
      dyadic.reentry.regularized.regularizationLoss ≤
        (8 : ENNReal) * proposition63OneScaleLogEnvelope delta ^
          (levelCount + 2) := by
    exact (dyadic.reentry.regularizationLoss_le_oneScaleEnvelope
      hlevelCount).trans <|
        proposition63OneScaleReentryRegularizationEnvelope_le_logEnvelope
          (levelCount := levelCount) root.normalization
          (hdeltaLe.trans absorption.delta₀_le_tiny)
  have terminalBound : (rich.terminal.regularity : ENNReal) ≤
      proposition63OneScaleLogEnvelope delta ^ 10 := by
    exact rich.terminal_regularity_bound.trans <|
      pow_le_pow_left'
        (proposition63_logarithmicLoss_le_oneScaleEnvelope
          hdeltaPos deltaOne) 10
  have terminalFactorBound :
      (4 * (rich.terminal.regularity : ENNReal)) *
          (wz2PaperPureRefinementFraction delta 61)⁻¹ ≤
        ((4 : ENNReal) * proposition63OneScaleLogEnvelope delta ^ 10) *
          (wz2PaperPureRefinementFraction delta 61)⁻¹ := by
    apply mul_le_mul_left _
    exact mul_le_mul_right terminalBound 4
  have coreBound :
      dyadic.reentry.regularized.regularizationLoss *
          dyadic.reentry.weightUpper *
            ((4 * (rich.terminal.regularity : ENNReal)) *
              (wz2PaperPureRefinementFraction delta 61)⁻¹) ≤
        ((8 : ENNReal) * proposition63OneScaleLogEnvelope delta ^
            (levelCount + 2)) *
          ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2) *
          (((4 : ENNReal) * proposition63OneScaleLogEnvelope delta ^ 10) *
            (wz2PaperPureRefinementFraction delta 61)⁻¹) := by
    exact mul_le_mul
      (mul_le_mul regularizationBound hweightUpper.le bot_le bot_le)
      terminalFactorBound bot_le bot_le
  calc
    ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (dyadic.reentry.regularized.regularizationLoss *
            dyadic.reentry.weightUpper *
              ((4 * (rich.terminal.regularity : ENNReal)) *
                (wz2PaperPureRefinementFraction delta 61)⁻¹)) *
          Kakeya.realRpowENN delta criticalLoss ≤
        ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (((8 : ENNReal) * proposition63OneScaleLogEnvelope delta ^
              (levelCount + 2)) *
            ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2) *
            ((4 : ENNReal) *
              proposition63OneScaleLogEnvelope delta ^ 10 *
              (wz2PaperPureRefinementFraction delta 61)⁻¹)) *
          Kakeya.realRpowENN delta criticalLoss := by
            exact mul_le_mul_left (mul_le_mul_right coreBound _) _
    _ ≤ proposition63CanonicalReentryWeight delta weightLoss *
          Kakeya.realRpowENN delta reentryNormalizationLoss :=
      absorption.absorb hdeltaPos hdeltaLe
    _ = dyadic.reentry.normalizationWeight *
          Kakeya.realRpowENN delta
            dyadic.reentry.reentryNormalizationLoss := by
      rw [hweight, hnormalizationLoss]

/-- One logarithmic pigeonhole loss absorbed into a strict increase of the
extremality loss.  The receipt is independent of the runtime root family. -/
structure Proposition63FullGrainLogAbsorptionData
    (sourceLoss outputLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_tiny : delta₀ ≤ 1 / 100000
  absorbEnvelope : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    proposition63OneScaleLogEnvelope delta *
        Kakeya.realRpowENN delta outputLoss ≤
      Kakeya.realRpowENN delta sourceLoss

theorem proposition63_full_grain_log_absorption
    (sourceLoss outputLoss : ℝ) (hgap : sourceLoss < outputLoss) :
    Nonempty (Proposition63FullGrainLogAbsorptionData
      sourceLoss outputLoss) := by
  let gap : ℝ := outputLoss - sourceLoss
  have gapPos : 0 < gap := by dsimp only [gap]; linarith
  rcases exists_delta_C_pow_log_absorbed_ennreal
      (1 : ENNReal) (by norm_num) proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg gapPos
      (show 0 < (1 : ℕ) by norm_num) with
    ⟨logDelta, logDeltaPos, logDeltaOne, logAbsorb⟩
  let delta₀ : ℝ := min logDelta (1 / 100000)
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min logDeltaPos (by norm_num)
    delta₀_le_one := (min_le_left _ _).trans logDeltaOne
    delta₀_le_tiny := min_le_right _ _
    absorbEnvelope := ?_
  }⟩
  intro delta deltaPos deltaLe
  have envelopeAbsorb :
      proposition63OneScaleLogEnvelope delta ≤
        Kakeya.realRpowENN delta (-gap) := by
    simpa [proposition63OneScaleLogEnvelope] using
      logAbsorb delta deltaPos (deltaLe.trans (min_le_left _ _))
  calc
    proposition63OneScaleLogEnvelope delta *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta (-gap) *
          Kakeya.realRpowENN delta outputLoss :=
      mul_le_mul_left envelopeAbsorb _
    _ = Kakeya.realRpowENN delta sourceLoss := by
      rw [← realRpowENN_add deltaPos]
      congr 1
      dsimp only [gap]
      ring

/-- Specialize the family-free logarithmic receipt to the exact root-family
factor produced by constant-multiplicity refinement. -/
theorem Proposition63FullGrainLogAbsorptionData.absorbRootCardLog
    {sourceLoss outputLoss delta sigma inputLoss normalizationLoss
      densityLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (data : Proposition63FullGrainLogAbsorptionData sourceLoss outputLoss)
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss)
    (hdeltaPos : 0 < delta) (hdeltaLe : delta ≤ data.delta₀) :
    (((Nat.log 2 root.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal) * Kakeya.realRpowENN delta outputLoss) ≤
      Kakeya.realRpowENN delta sourceLoss := by
  have cardLogLe :
      ((Nat.log 2 root.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal) ≤ proposition63OneScaleLogEnvelope delta := by
    apply le_trans ?_
      (proposition63_cropped_cardLog_le_oneScaleEnvelope root.normalization
        (hdeltaLe.trans data.delta₀_le_tiny))
    exact_mod_cast Nat.add_le_add_right
      (Nat.log_mono_right (by omega :
        root.normalization.croppedFamily.card ≤
          2 * root.normalization.croppedFamily.card)) 1
  exact (mul_le_mul_left cardLogLe _).trans
    (data.absorbEnvelope hdeltaPos hdeltaLe)

/-- Family-free absorption of the fresh exact-balancing logarithm. -/
structure Proposition63FullGrainBalancingAbsorptionData
    (sourceLoss outputLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    proposition63FreshBalancingEnvelope delta *
        Kakeya.realRpowENN delta outputLoss ≤
      Kakeya.realRpowENN delta sourceLoss

theorem proposition63_full_grain_balancing_absorption
    (sourceLoss outputLoss : ℝ) (hgap : sourceLoss < outputLoss) :
    Nonempty (Proposition63FullGrainBalancingAbsorptionData
      sourceLoss outputLoss) := by
  let gap : ℝ := outputLoss - sourceLoss
  have gapPos : 0 < gap := by dsimp only [gap]; linarith
  rcases exists_delta_C_pow_log_absorbed_ennreal
      (8 : ENNReal) (by norm_num) wz2PaperBoundaryLogCoefficient
      (by dsimp only [wz2PaperBoundaryLogCoefficient]; positivity) gapPos
      (show 0 < (1 : ℕ) by norm_num) with
    ⟨delta₀, delta₀Pos, delta₀One, absorb⟩
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := delta₀Pos
    delta₀_le_one := delta₀One
    absorb := ?_
  }⟩
  intro delta deltaPos deltaLe
  have envelopeAbsorb :
      proposition63FreshBalancingEnvelope delta ≤
        Kakeya.realRpowENN delta (-gap) := by
    simpa [proposition63FreshBalancingEnvelope] using
      absorb delta deltaPos deltaLe
  calc
    proposition63FreshBalancingEnvelope delta *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta (-gap) *
          Kakeya.realRpowENN delta outputLoss :=
      mul_le_mul_left envelopeAbsorb _
    _ = Kakeya.realRpowENN delta sourceLoss := by
      rw [← realRpowENN_add deltaPos]
      congr 1
      dsimp only [gap]
      ring

/-- The fixed factor four paid by local full-grain restoration. -/
structure Proposition63FullGrainFixedRestoreAbsorptionData
    (sourceLoss outputLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    4 * Kakeya.realRpowENN delta outputLoss ≤
      Kakeya.realRpowENN delta sourceLoss

theorem proposition63_full_grain_fixed_restore_absorption
    (sourceLoss outputLoss : ℝ) (hgap : sourceLoss < outputLoss) :
    Nonempty (Proposition63FullGrainFixedRestoreAbsorptionData
      sourceLoss outputLoss) := by
  rcases exists_delta_realRpowENN_bound (4 : ENNReal) (by norm_num)
      (sub_pos.mpr hgap) with
    ⟨delta₀, delta₀Pos, delta₀One, absorb⟩
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := delta₀Pos
    delta₀_le_one := delta₀One
    absorb := ?_
  }⟩
  intro delta deltaPos deltaLe
  calc
    4 * Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta (-(outputLoss - sourceLoss)) *
          Kakeya.realRpowENN delta outputLoss := by
      exact mul_le_mul_left (absorb delta deltaPos deltaLe) _
    _ = Kakeya.realRpowENN delta sourceLoss := by
      rw [← realRpowENN_add deltaPos]
      congr 1
      ring

/-- The Phase-1 lower scale window supplies the physical gain needed by the
fixed-origin boundary deletion at the square-root query scale. -/
structure Proposition63FullGrainBoundaryAbsorptionData
    (stickyLoss middleLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorb : ∀ {delta queryScale : ℝ}, 0 < delta → delta ≤ delta₀ →
    0 < queryScale → 48 * delta ^ 2 ≤ queryScale →
    Real.rpow delta stickyLoss ≤ alignedCoarseScale delta queryScale →
    2 * 24000000 *
        (Kakeya.realRpowENN delta (-middleLoss) *
            wz2PaperBoundaryGeometryConstant + 1) *
        ENNReal.ofReal (Real.sqrt (delta / Real.sqrt queryScale)) <
      Kakeya.realRpowENN delta middleLoss

/-- The Phase-1 lower window is a genuine lower bound on the query scale.
In particular, it cannot be imposed on the whole central Lemma 4.12 power
grid when `stickyLoss` is small: every admitted query lies strictly above
`delta ^ (2 * stickyLoss)`. -/
lemma rpow_two_mul_lt_query_of_aligned_phase1_lower
    {delta queryScale stickyLoss : ℝ}
    (hdelta : 0 < delta) (hquery : 0 < queryScale)
    (hgrid : 48 * delta ^ 2 ≤ queryScale)
    (hphase : Real.rpow delta stickyLoss ≤
      alignedCoarseScale delta queryScale) :
    Real.rpow delta (2 * stickyLoss) < queryScale := by
  have halignedPos : 0 < alignedCoarseScale delta queryScale :=
    alignedCoarseScale_pos hdelta hquery
  have halignedSquare : alignedCoarseScale delta queryScale ^ 2 <
      queryScale := by
    have comparison := fortyEight_mul_alignedCoarseScale_sq_lt_four_mul_query
      hdelta hquery hgrid
    nlinarith [sq_nonneg (alignedCoarseScale delta queryScale)]
  have hpowerSquare : Real.rpow delta (2 * stickyLoss) =
      (Real.rpow delta stickyLoss) ^ 2 := by
    calc
      Real.rpow delta (2 * stickyLoss) =
          Real.rpow delta (stickyLoss + stickyLoss) := by ring_nf
      _ = Real.rpow delta stickyLoss * Real.rpow delta stickyLoss :=
        Real.rpow_add hdelta stickyLoss stickyLoss
      _ = (Real.rpow delta stickyLoss) ^ 2 := by ring
  rw [hpowerSquare]
  have hsourcePos : 0 < Real.rpow delta stickyLoss :=
    Real.rpow_pos_of_pos hdelta stickyLoss
  have hsquare : (Real.rpow delta stickyLoss) ^ 2 ≤
      alignedCoarseScale delta queryScale ^ 2 := by
    nlinarith
  exact hsquare.trans_lt halignedSquare

theorem proposition63_full_grain_boundary_absorption
    (stickyLoss middleLoss : ℝ) (hmiddleLoss : 0 < middleLoss)
    (hgap : 2 * middleLoss < (1 - stickyLoss) / 2) :
    Nonempty (Proposition63FullGrainBoundaryAbsorptionData
      stickyLoss middleLoss) := by
  let gain : ℝ := (1 - stickyLoss) / 2
  let gap : ℝ := gain - 2 * middleLoss
  have gapPos : 0 < gap := by
    dsimp only [gap, gain]
    linarith
  let fixed : ENNReal :=
    (2 : ENNReal) * 24000000 * (wz2PaperBoundaryGeometryConstant + 1)
  have fixedTop : fixed ≠ ⊤ := by
    dsimp only [fixed, wz2PaperBoundaryGeometryConstant]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (by norm_num))
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top,
          by norm_num⟩)
  rcases exists_delta_realRpowENN_bound fixed fixedTop
      (show 0 < gap / 2 by positivity) with
    ⟨constantDelta, constantDeltaPos, constantDeltaOne, constantAbsorb⟩
  let delta₀ : ℝ := min constantDelta (Real.exp (-1))
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min constantDeltaPos (by positivity)
    delta₀_le_one := (min_le_left _ _).trans constantDeltaOne
    absorb := ?_
  }⟩
  intro delta queryScale deltaPos deltaLe queryPos queryGridFloor phaseLower
  have deltaLeConstant : delta ≤ constantDelta :=
    deltaLe.trans (min_le_left _ _)
  have deltaOne : delta ≤ 1 := deltaLeConstant.trans constantDeltaOne
  have deltaLtOne : delta < 1 :=
    deltaLe.trans_lt <| (min_le_right _ _).trans_lt
      (Real.exp_lt_one_iff.mpr (by norm_num))
  have alignedPos : 0 < alignedCoarseScale delta queryScale :=
    alignedCoarseScale_pos deltaPos queryPos
  have alignedSquare : alignedCoarseScale delta queryScale ^ 2 < queryScale := by
    have comparison := fortyEight_mul_alignedCoarseScale_sq_lt_four_mul_query
      deltaPos queryPos queryGridFloor
    nlinarith [sq_nonneg (alignedCoarseScale delta queryScale)]
  have alignedLeSqrt :
      alignedCoarseScale delta queryScale ≤ Real.sqrt queryScale := by
    have sqrtSquare : (Real.sqrt queryScale) ^ 2 = queryScale :=
      Real.sq_sqrt queryPos.le
    have sqrtNonnegative : 0 ≤ Real.sqrt queryScale := Real.sqrt_nonneg _
    nlinarith
  have lowerSqrt :
      Real.rpow delta stickyLoss ≤ Real.sqrt queryScale :=
    phaseLower.trans alignedLeSqrt
  have ratioBound :
      delta / Real.sqrt queryScale ≤
        delta / Real.rpow delta stickyLoss :=
    div_le_div_of_nonneg_left deltaPos.le
      (Real.rpow_pos_of_pos deltaPos stickyLoss) lowerSqrt
  have ratioPower :
      delta / Real.rpow delta stickyLoss =
        Real.rpow delta (1 - stickyLoss) := by
    calc
      delta / Real.rpow delta stickyLoss =
          Real.rpow delta 1 / Real.rpow delta stickyLoss := by
        exact congrArg (fun value : ℝ =>
          value / Real.rpow delta stickyLoss) (Real.rpow_one delta).symm
      _ = Real.rpow delta (1 - stickyLoss) :=
        (Real.rpow_sub deltaPos 1 stickyLoss).symm
  have rootBoundReal :
      Real.sqrt (delta / Real.sqrt queryScale) ≤
        Real.rpow delta gain := by
    calc
      Real.sqrt (delta / Real.sqrt queryScale) ≤
          Real.sqrt (delta / Real.rpow delta stickyLoss) :=
        Real.sqrt_le_sqrt ratioBound
      _ = Real.sqrt (Real.rpow delta (1 - stickyLoss)) := by
        rw [ratioPower]
      _ = Real.rpow delta gain := by
        rw [Real.sqrt_eq_rpow]
        calc
          Real.rpow (Real.rpow delta (1 - stickyLoss)) (1 / 2) =
              Real.rpow delta ((1 - stickyLoss) * (1 / 2)) :=
            (Real.rpow_mul deltaPos.le (1 - stickyLoss) (1 / 2)).symm
          _ = Real.rpow delta gain := by
            congr 1
            dsimp only [gain]
            ring
  have rootBound :
      ENNReal.ofReal (Real.sqrt (delta / Real.sqrt queryScale)) ≤
        Kakeya.realRpowENN delta gain :=
    ENNReal.ofReal_mono rootBoundReal
  have oneLeNegative :
      (1 : ENNReal) ≤ Kakeya.realRpowENN delta (-middleLoss) := by
    rw [Kakeya.realRpowENN, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_mono
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      deltaPos deltaOne (by linarith)
  have bracketBound :
      Kakeya.realRpowENN delta (-middleLoss) *
            wz2PaperBoundaryGeometryConstant + 1 ≤
        Kakeya.realRpowENN delta (-middleLoss) *
          (wz2PaperBoundaryGeometryConstant + 1) := by
    calc
      Kakeya.realRpowENN delta (-middleLoss) *
            wz2PaperBoundaryGeometryConstant + 1 ≤
          Kakeya.realRpowENN delta (-middleLoss) *
              wz2PaperBoundaryGeometryConstant +
            Kakeya.realRpowENN delta (-middleLoss) := by gcongr
      _ = Kakeya.realRpowENN delta (-middleLoss) *
          (wz2PaperBoundaryGeometryConstant + 1) := by ring
  have fixedAbsorb :
      fixed ≤ Kakeya.realRpowENN delta (-(gap / 2)) :=
    constantAbsorb delta deltaPos deltaLeConstant
  have exponentIdentity :
      -(gap / 2) + (-middleLoss) + gain =
        middleLoss + gap / 2 := by
    dsimp only [gap]
    ring
  have powerStrict :
      Kakeya.realRpowENN delta (middleLoss + gap / 2) <
        Kakeya.realRpowENN delta middleLoss := by
    apply (ENNReal.ofReal_lt_ofReal_iff
      (Real.rpow_pos_of_pos deltaPos middleLoss)).2
    exact Real.rpow_lt_rpow_of_exponent_gt deltaPos deltaLtOne (by
      linarith [gapPos])
  calc
    2 * 24000000 *
          (Kakeya.realRpowENN delta (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (delta / Real.sqrt queryScale)) ≤
        fixed * Kakeya.realRpowENN delta (-middleLoss) *
          Kakeya.realRpowENN delta gain := by
      dsimp only [fixed]
      calc
        2 * 24000000 *
              (Kakeya.realRpowENN delta (-middleLoss) *
                  wz2PaperBoundaryGeometryConstant + 1) *
              ENNReal.ofReal (Real.sqrt (delta / Real.sqrt queryScale)) ≤
            2 * 24000000 *
              (Kakeya.realRpowENN delta (-middleLoss) *
                (wz2PaperBoundaryGeometryConstant + 1)) *
              Kakeya.realRpowENN delta gain := by
          exact mul_le_mul
            (mul_le_mul_right bracketBound _) rootBound bot_le bot_le
        _ = (2 * 24000000 *
              (wz2PaperBoundaryGeometryConstant + 1)) *
            Kakeya.realRpowENN delta (-middleLoss) *
              Kakeya.realRpowENN delta gain := by ring
    _ ≤ Kakeya.realRpowENN delta (-(gap / 2)) *
          Kakeya.realRpowENN delta (-middleLoss) *
            Kakeya.realRpowENN delta gain := by
      exact mul_le_mul_left (mul_le_mul_left fixedAbsorb _) _
    _ = Kakeya.realRpowENN delta (middleLoss + gap / 2) := by
      rw [← realRpowENN_add deltaPos, ← realRpowENN_add deltaPos]
      rw [exponentIdentity]
    _ < Kakeya.realRpowENN delta middleLoss := powerStrict

/-- Rewrite the refinement-retention receipt into the inverse-factor form
consumed by Phase 1. -/
theorem Proposition63RefinementRetentionAbsorptionData.inverse_mul_absorb
    {sourceLoss outputLoss delta : ℝ} {logExponent : ℕ}
    (data : Proposition63RefinementRetentionAbsorptionData
      sourceLoss outputLoss logExponent)
    (hdeltaPos : 0 < delta) (hdeltaLtOne : delta < 1)
    (hdeltaLe : delta ≤ data.delta₀) :
    (wz2PaperPureRefinementFraction delta logExponent)⁻¹ *
        Kakeya.realRpowENN delta outputLoss ≤
      Kakeya.realRpowENN delta sourceLoss := by
  let logTerm : ENNReal := ENNReal.ofReal (Real.log (1 / delta))
  have logTermPos : 0 < logTerm := by
    exact ENNReal.ofReal_pos.mpr <|
      Real.log_pos (one_lt_one_div hdeltaPos hdeltaLtOne)
  have logTermTop : logTerm ≠ ⊤ := by simp [logTerm]
  have fractionPos : 0 < wz2PaperPureRefinementFraction delta logExponent := by
    unfold wz2PaperPureRefinementFraction
    exact ENNReal.pow_pos (ENNReal.inv_pos.mpr logTermTop) _
  have fractionTop : wz2PaperPureRefinementFraction delta logExponent ≠ ⊤ := by
    unfold wz2PaperPureRefinementFraction
    exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr logTermPos.ne')
  apply (ENNReal.inv_mul_le_iff fractionPos.ne' fractionTop).2
  simpa only [mul_comm] using data.absorb hdeltaPos hdeltaLe

/-- Restore extremality from the final, ambient-family output of any genuine
one-scale full-grain construction.  This is the common endpoint for both the
direct current-reentry producer and the dependent coarse-to-fine pullback. -/
theorem proposition63_extremal_one_scale_full_grain_of_candidate
    {delta sigma incidence inputLoss outputLoss queryScale spatialScale
      variationScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {current next : WZ1PaperTubeShading family}
    (currentExtremal : WZ2PaperCroppedIsExtremal
      sigma inputLoss family current)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (hnextSub : PaperIsSubshading next current)
    (hnextCubical : WZ1PaperIsCubicalShading next)
    (hnextVariation : ∀ first ∈ next.union, ∀ second ∈ next.union,
      dist first second ≤ spatialScale →
        dist (currentMap.planeMap first) (currentMap.planeMap second) ≤
          variationScale)
    (hnextAD : ∀ point ∈ next.union,
      IsADSet1
        (scalarProjection (currentMap.planeMap point)
          (next.union ∩ Metric.closedBall point (Real.sqrt queryScale)))
        queryScale (1 - sigma)
        (Kakeya.realRpowENN delta (-outputLoss)))
    (leftFactor rightFactor : ENNReal)
    (hleftPos : 0 < leftFactor)
    (hleftTop : leftFactor ≠ ⊤)
    (hrightTop : rightFactor ≠ ⊤)
    (hmass : leftFactor * current.mass ≤ rightFactor * next.mass)
    (hinputOutput : inputLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss leftFactor rightFactor *
      Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta inputLoss) :
    Nonempty (Proposition63ExtremalOneScaleFullGrainData
      (sigma := sigma) current currentMap outputLoss queryScale spatialScale
        variationScale) := by
  let massLoss := proposition63Lemma43MassLoss leftFactor rightFactor
  have hmassRetention : massLoss⁻¹ * current.mass ≤ next.mass :=
    proposition63Lemma43MassLoss_inv_mul_le
      hleftPos hleftTop hrightTop hmass
  have hnextExtremal : WZ2PaperCroppedIsExtremal
      sigma outputLoss family next := by
    apply transfer_cropped_extremal_to_subshading massLoss
      (proposition63Lemma43MassLoss_pos _ _)
      (proposition63Lemma43MassLoss_ne_top hleftPos hrightTop)
      currentExtremal hnextSub hmassRetention hnextCubical hinputOutput
    · simpa only [massLoss] using hrestore
    · exact currentExtremal.delta_pos
    · exact currentExtremal.delta_le_one
    · exact houtputLoss
  let nextMap := paperWeakPlaneMapRestrict currentMap hnextSub
  exact ⟨{
    shading := next
    subshading := hnextSub
    cubical := hnextCubical
    planeMap := nextMap
    same_plane_map := rfl
    variation := by
      intro first hfirst second hsecond hdistance
      change dist (currentMap.planeMap first) (currentMap.planeMap second) ≤
        variationScale
      exact hnextVariation first hfirst second hsecond hdistance
    local_ad := by
      intro point hpoint
      change IsADSet1
        (scalarProjection (currentMap.planeMap point)
          (next.union ∩ Metric.closedBall point (Real.sqrt queryScale)))
        queryScale (1 - sigma)
        (Kakeya.realRpowENN delta (-outputLoss))
      exact hnextAD point hpoint
    massLoss := massLoss
    massLoss_pos := proposition63Lemma43MassLoss_pos _ _
    massLoss_ne_top := proposition63Lemma43MassLoss_ne_top hleftPos hrightTop
    mass_retention := hmassRetention
    extremal := hnextExtremal
  }⟩

/-- Compose the pre-Phase-1 dyadic selection with one already-restored
full-grain step on that band.  This exposes a single transition from the
actual incoming shading while keeping both losses local to the same scale. -/
noncomputable def Proposition63DyadicCurrentReentryData.liftExtremalOneScaleFullGrain
    {delta sigma initialInputLoss normalizationLoss densityLoss incidence
      currentLoss dyadicLoss weightLoss reentryLoss reentryNormalizationLoss
      outputLoss queryScale spatialScale variationScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
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
    (next : Proposition63ExtremalOneScaleFullGrainData
      (sigma := sigma) dyadic.shading dyadic.planeMap outputLoss queryScale
        spatialScale variationScale) :
    Proposition63ExtremalOneScaleFullGrainData
      (sigma := sigma) current currentMap outputLoss queryScale spatialScale
        variationScale := by
  let massLoss := dyadic.massLoss * next.massLoss
  have hmassLossPos : 0 < massLoss :=
    ENNReal.mul_pos dyadic.massLoss_pos.ne' next.massLoss_pos.ne'
  have hmassLossTop : massLoss ≠ ⊤ :=
    ENNReal.mul_ne_top dyadic.massLoss_ne_top next.massLoss_ne_top
  have hmassRetention : massLoss⁻¹ * current.mass ≤ next.shading.mass := by
    rw [ENNReal.mul_inv (Or.inl dyadic.massLoss_pos.ne')
      (Or.inl dyadic.massLoss_ne_top)]
    calc
      (dyadic.massLoss⁻¹ * next.massLoss⁻¹) * current.mass =
          next.massLoss⁻¹ * (dyadic.massLoss⁻¹ * current.mass) := by ring
      _ ≤ next.massLoss⁻¹ * dyadic.shading.mass := by
        exact mul_le_mul_right dyadic.mass_retention _
      _ ≤ next.shading.mass := next.mass_retention
  exact {
    shading := next.shading
    subshading := fun index point hpoint =>
      dyadic.subshading index (next.subshading index hpoint)
    cubical := next.cubical
    planeMap := next.planeMap
    same_plane_map := next.same_plane_map.trans dyadic.same_plane_map
    variation := next.variation
    local_ad := next.local_ad
    massLoss := massLoss
    massLoss_pos := hmassLossPos
    massLoss_ne_top := hmassLossTop
    mass_retention := hmassRetention
    extremal := next.extremal
  }

/-- Execute an already-prepared genuine full-grain step and restore
extremality before returning.  The Lipschitz hypothesis is required only on
the current shading, exactly as supplied by Lemma 4.7. -/
theorem proposition63_extremal_one_scale_full_grain_of_prepared
    {delta sigma initialInputLoss normalizationLoss reentryLoss incidence
      inputLoss firstLoss secondLoss outputLoss queryScale sqrtScale
      spatialScale variationScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (currentExtremal : WZ2PaperCroppedIsExtremal
      sigma inputLoss initialNormalized.croppedFamily current)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (coefficient : NNReal)
    (currentLipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ current.union} =>
        currentMap.planeMap point))
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (sourceLeftFactor sourceRightFactor uniformPreparationLoss : ENNReal)
    (uniformCoverBudget : ℕ)
    (step : Proposition63UniformFullGrainStepData
      (firstLoss := firstLoss) (secondLoss := secondLoss)
      (queryScale := queryScale) (sqrtScale := sqrtScale) reentry
      currentMap.planeMap sourceLeftFactor sourceRightFactor coefficient
      uniformPreparationLoss uniformCoverBudget)
    (hsourceLeftPos : 0 < sourceLeftFactor)
    (hsourceLeftTop : sourceLeftFactor ≠ ⊤)
    (hsourceRightTop : sourceRightFactor ≠ ⊤)
    (hpreparationTop : uniformPreparationLoss ≠ ⊤)
    (hcoverBudgetPos : 0 < uniformCoverBudget)
    (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hqueryPos : 0 < queryScale)
    (hquerySmall : queryScale ≤ 1 / 4)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (hsqrtPos : 0 < sqrtScale)
    (hspatialVariation : (coefficient : ℝ) * spatialScale ≤ variationScale)
    (hsecondOutput : secondLoss ≤ outputLoss)
    (hinputOutput : inputLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hrestore :
      proposition63Lemma43MassLoss
          (proposition63UniformLineFactor
              (Kakeya.realRpowENN delta (secondLoss + 2)) sqrtScale hsqrtPos *
            (((1 : ENNReal) / 2) /
              (2 * (uniformCoverBudget : ENNReal))) *
            sourceLeftFactor)
          (sourceRightFactor * (uniformPreparationLoss * 2)) *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta inputLoss) :
    Nonempty (Proposition63ExtremalOneScaleFullGrainData
      (sigma := sigma) current currentMap outputLoss queryScale spatialScale
        variationScale) := by
  let volumeFloor := Kakeya.realRpowENN delta (secondLoss + 2)
  let lineVolume := proposition63UniformLineVolume volumeFloor sqrtScale
    hsqrtPos
  let lineFactor := proposition63UniformLineFactor volumeFloor sqrtScale
    hsqrtPos
  let inverseCoverFactor : ENNReal :=
    ((1 : ENNReal) / 2) / (2 * (uniformCoverBudget : ENNReal))
  let leftFactor := lineFactor * inverseCoverFactor * sourceLeftFactor
  let rightFactor := sourceRightFactor * (uniformPreparationLoss * 2)
  let massLoss := proposition63Lemma43MassLoss leftFactor rightFactor
  have hdeltaPos : 0 < delta := currentExtremal.delta_pos
  have hdeltaOne : delta ≤ 1 := currentExtremal.delta_le_one
  have hlineFactorPos : 0 < lineFactor := by
    apply proposition63UniformLineFactor_pos
    · dsimp only [volumeFloor, Kakeya.realRpowENN]
      exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdeltaPos _)
    · dsimp only [volumeFloor, Kakeya.realRpowENN]
      exact ENNReal.ofReal_ne_top
  have hlineFactorTop : lineFactor ≠ ⊤ := by
    dsimp only [lineFactor, proposition63UniformLineFactor]
    exact ENNReal.ofReal_ne_top
  have hcoverCastPos : 0 < (uniformCoverBudget : ENNReal) := by
    exact_mod_cast hcoverBudgetPos
  have hcoverDenomPos : 0 < (2 * (uniformCoverBudget : ENNReal)) :=
    ENNReal.mul_pos (by norm_num) hcoverCastPos.ne'
  have hcoverDenomTop : (2 * (uniformCoverBudget : ENNReal)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) (by simp)
  have hinversePos : 0 < inverseCoverFactor := by
    dsimp only [inverseCoverFactor]
    exact ENNReal.div_pos (by norm_num) hcoverDenomTop
  have hinverseTop : inverseCoverFactor ≠ ⊤ := by
    dsimp only [inverseCoverFactor]
    exact ENNReal.div_ne_top (by norm_num) hcoverDenomPos.ne'
  have hleftPos : 0 < leftFactor := by
    dsimp only [leftFactor]
    exact ENNReal.mul_pos
      (ENNReal.mul_pos hlineFactorPos.ne' hinversePos.ne').ne'
      hsourceLeftPos.ne'
  have hleftTop : leftFactor ≠ ⊤ := by
    dsimp only [leftFactor]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hlineFactorTop hinverseTop) hsourceLeftTop
  have hrightTop : rightFactor ≠ ⊤ := by
    dsimp only [rightFactor]
    exact ENNReal.mul_ne_top hsourceRightTop
      (ENNReal.mul_ne_top hpreparationTop (by norm_num))
  have horiginalUnionCurrent : step.original.shading.union ⊆ current.union := by
    intro point hpoint
    have hextended : point ∈
        (reentry.extendCandidate step.original.shading).union := by
      rw [reentry.extendCandidate_union]
      exact hpoint
    rcases hextended with ⟨index, hindex⟩
    exact ⟨index, reentry.extendCandidate_subshading
      step.original.subshading index hindex⟩
  have horiginalLipschitz : ∀ first ∈ step.original.shading.union,
      ∀ second ∈ step.original.shading.union,
        dist (currentMap.planeMap first) (currentMap.planeMap second) ≤
          (coefficient : ℝ) * dist first second := by
    intro first hfirst second hsecond
    exact currentLipschitz.dist_le_mul
      ⟨first, horiginalUnionCurrent hfirst⟩
      ⟨second, horiginalUnionCurrent hsecond⟩
  let full := Classical.choice <|
    proposition63_oneScale_fullGrainCandidate_of_extremal
      currentMap.planeMap step.original step.prepared step.cells
      reentry.normalization.line_class hqueryPos
      (hquerySmall.trans (by norm_num)) hsqrtScale step.plane_unit
      hcoefficientOne horiginalLipschitz uniformCoverBudget hcoverBudgetPos
      step.cover_budget hdeltaSmall
  let candidate := full.lineHitCandidate hdeltaPos
  have hcandidateSub : PaperIsSubshading candidate
      reentry.normalization.croppedRefined :=
    full.lineHitCandidate_subshading_source hdeltaPos
  have hcandidateCubical : WZ1PaperIsCubicalShading candidate :=
    full.lineHitCandidate_cubical hdeltaPos
  have hcandidateUnionCurrent : candidate.union ⊆ current.union := by
    intro point hpoint
    have hextended : point ∈ (reentry.extendCandidate candidate).union := by
      rw [reentry.extendCandidate_union]
      exact hpoint
    rcases hextended with ⟨index, hindex⟩
    exact ⟨index, reentry.extendCandidate_subshading hcandidateSub index hindex⟩
  have hcandidateVariation : ∀ first ∈ candidate.union,
      ∀ second ∈ candidate.union, dist first second ≤ spatialScale →
        dist (currentMap.planeMap first) (currentMap.planeMap second) ≤
          variationScale := by
    intro first hfirst second hsecond hdistance
    exact (currentLipschitz.dist_le_mul
      ⟨first, hcandidateUnionCurrent hfirst⟩
      ⟨second, hcandidateUnionCurrent hsecond⟩).trans
        ((mul_le_mul_of_nonneg_left hdistance coefficient.coe_nonneg).trans
          hspatialVariation)
  have hconstant : Kakeya.realRpowENN delta (-secondLoss) ≤
      Kakeya.realRpowENN delta (-outputLoss) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hdeltaPos hdeltaOne (by linarith)
  have hcandidateAD : ∀ point ∈ candidate.union,
      IsADSet1
        (scalarProjection (currentMap.planeMap point)
          (candidate.union ∩ Metric.closedBall point
            (Real.sqrt queryScale)))
        queryScale (1 - sigma)
        (Kakeya.realRpowENN delta (-outputLoss)) := by
    intro point hpoint
    exact (full.lineHitCandidate_local_ad hdeltaPos point hpoint).mono_constant
      hconstant
  have hrawMass :
      (lineFactor * inverseCoverFactor * sourceLeftFactor) * current.mass ≤
        (sourceRightFactor * (uniformPreparationLoss * 2)) * candidate.mass := by
    have hcandidateMass :=
      full.lineHitCandidate_mass_from_current_cancel_cellMass
        (current := current) sourceLeftFactor sourceRightFactor
        step.incoming_mass hdeltaPos hqueryPos hsqrtPos
    have hqueryFactor : ENNReal.ofReal (4 * queryScale) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hright : sourceRightFactor *
          (step.prepared.preparationLoss *
            (2 * ENNReal.ofReal (4 * queryScale))) ≤
        sourceRightFactor * (uniformPreparationLoss * 2) := by
      apply mul_le_mul_right
      calc
        step.prepared.preparationLoss *
              (2 * ENNReal.ofReal (4 * queryScale)) ≤
            uniformPreparationLoss *
              (2 * ENNReal.ofReal (4 * queryScale)) := by
          gcongr
          exact step.preparation_budget
        _ ≤ uniformPreparationLoss * 2 := by
          gcongr
          simpa only [mul_one] using mul_le_mul_right hqueryFactor 2
    exact hcandidateMass.trans (mul_le_mul_left hright candidate.mass)
  rcases reentry.candidate_joint_one_scale candidate currentMap.planeMap
      (Kakeya.realRpowENN delta (-outputLoss)) leftFactor rightFactor
      hcandidateSub hcandidateCubical hcandidateVariation hcandidateAD
      (by simpa only [leftFactor, rightFactor] using hrawMass) with
    ⟨next, hnextSub, hnextCubical, _hnextMultiplicity, hnextVariation,
      hnextAD, hnextMass⟩
  apply proposition63_extremal_one_scale_full_grain_of_candidate
    currentExtremal currentMap hnextSub hnextCubical hnextVariation hnextAD
    leftFactor rightFactor hleftPos hleftTop hrightTop
    (by simpa only [leftFactor, rightFactor] using hnextMass) hinputOutput
    houtputLoss
  simpa only [leftFactor, rightFactor] using hrestore

/-- Canonical direct runtime chain for one Lemma 4.12 coordinate: construct
the aligned Phase-1 analytic output from the fresh current re-entry, perform
the canonical multiplicity/balancing preparation, and restore extremality
immediately after the line-hit full-grain refinement. -/
theorem Proposition63CurrentShadingReentryData.extremalOneScaleFullGrain_of_phase1
    {delta sigma initialInputLoss normalizationLoss reentryLoss incidence
      inputLoss stickyDataLoss phase1Loss sourceADLoss criticalLoss queryLoss
      middleLoss finalLoss outputLoss queryScale spatialScale variationScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent logExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (currentExtremal : WZ2PaperCroppedIsExtremal
      sigma inputLoss initialNormalized.croppedFamily current)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (coefficient : NNReal)
    (currentLipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ current.union} =>
        currentMap.planeMap point))
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    {rho : WZ2PaperRequestedScale delta}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyDataLoss)
      data.normalization.croppedRefined rho logExponent)
    (leftFactor rightFactor : ENNReal)
    (hleftPos : 0 < leftFactor)
    (hleftTop : leftFactor ≠ ⊤)
    (hrightTop : rightFactor ≠ ⊤)
    (hleft : leftFactor ≤
      (73 / 100 : ENNReal) * data.normalizationWeight)
    (hright : data.regularized.regularizationLoss *
        propertyThreeCommonHullMassLoss sticky ≤ rightFactor)
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
      (-1 / (queryLoss - criticalLoss)))
    (hqueryMiddle : queryLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (hmultiplicitySlack :
      (((Nat.log 2 data.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal) * Kakeya.realRpowENN delta middleLoss) ≤
        Kakeya.realRpowENN delta queryLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hperiodicScale : 50 * delta ≤ Real.sqrt queryScale)
    (hsqrtOne : Real.sqrt queryScale ≤ 1)
    (hboundaryScalar :
      2 * 24000000 *
          (Kakeya.realRpowENN delta (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (delta / Real.sqrt queryScale)) <
        Kakeya.realRpowENN delta middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss)
    (hfinalLoss : 0 < finalLoss)
    (hbalancingSlack : proposition63FreshBalancingEnvelope delta *
        Kakeya.realRpowENN delta finalLoss ≤
      Kakeya.realRpowENN delta middleLoss)
    (uniformCoverBudget : ℕ)
    (hcoverBudgetPos : 0 < uniformCoverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN delta (-finalLoss) *
              Kakeya.realRpowENN (1 / queryScale) (1 - sigma))) ≤
        (uniformCoverBudget : ENNReal))
    (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hvariationBudget :
      (coefficient : ℝ) * spatialScale ≤ variationScale)
    (hfinalOutput : finalLoss ≤ outputLoss)
    (hinputOutput : inputLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore :
      proposition63Lemma43MassLoss
          (proposition63UniformLineFactor
              (Kakeya.realRpowENN delta (finalLoss + 2))
                (Real.sqrt queryScale) (Real.sqrt_pos.mpr hqueryPos) *
            (((1 : ENNReal) / 2) /
              (2 * (uniformCoverBudget : ENNReal))) * leftFactor)
          (rightFactor *
            (proposition63UniformPreparationLoss
              data.normalization.croppedFamily * 2)) *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta inputLoss) :
    Nonempty (Proposition63ExtremalOneScaleFullGrainData
      (sigma := sigma) current currentMap outputLoss queryScale spatialScale
        variationScale) := by
  have hplaneUnit : ∀ point ∈ data.normalization.croppedRefined.union,
      ‖currentMap.planeMap point‖ = 1 := by
    intro point hpoint
    have pointCurrent : point ∈ current.union := by
      have extended : point ∈
          (data.extendCandidate data.normalization.croppedRefined).union := by
        rw [data.extendCandidate_union]
        exact hpoint
      rcases extended with ⟨index, indexMem⟩
      exact ⟨index, data.extendCandidate_subshading
        (fun _ => Set.Subset.rfl) index indexMem⟩
    exact currentMap.unit point pointCurrent
  rcases data.phase1AlignedCandidate_of_bounds sticky currentMap.planeMap
      leftFactor rightFactor hleft hright hplaneUnit hrhoAligned
      hphase1Loss hreentryPhase1 hphase1Slack hsigma hsigmaOne hreentryLoss
      hreentrySticky hstickySmall hrhoSmall hrhoPropertyP hhavg
      hreentryCritical hcommonSlack hdeltaOne hcriticalLoss hsourceADLoss
      hADGap hADSmall logScale hrhoLog hlog hrhoLower hrhoBound hstickyAD
      hqueryPos hquerySmall hqueryGridFloor hcriticalQuery hqueryAbsorb with
    ⟨original, incomingMass⟩
  let preparationLoss := proposition63UniformPreparationLoss
    data.normalization.croppedFamily
  have hplaneUnitOriginal : ∀ point ∈ original.shading.union,
      ‖currentMap.planeMap point‖ = 1 := by
    intro point hpoint
    exact hplaneUnit point <| by
      rcases hpoint with ⟨index, indexMem⟩
      exact ⟨index, original.subshading index indexMem⟩
  let step := Classical.choice <|
    proposition63_uniformFullGrainStep_of_freshBalancingCWA_uniform data
      currentMap.planeMap leftFactor rightFactor coefficient
      uniformCoverBudget original incomingMass hqueryMiddle hmiddleLoss
      hmultiplicitySlack hdeltaSmall hperiodicScale
      (Real.sqrt_pos.mpr hqueryPos) hsqrtOne hboundaryScalar hmiddleFinal
      hfinalLoss hbalancingSlack hplaneUnitOriginal hcoverBudget
  have preparationTop : preparationLoss ≠ ⊤ :=
    (proposition63UniformPreparationLoss_pos_ne_top
      data.normalization.croppedFamily currentExtremal.delta_pos
      currentExtremal.delta_le_one).2
  apply proposition63_extremal_one_scale_full_grain_of_prepared
    currentExtremal currentMap coefficient currentLipschitz data leftFactor
    rightFactor preparationLoss uniformCoverBudget step hleftPos hleftTop
    hrightTop preparationTop hcoverBudgetPos hcoefficientOne hqueryPos
    hquerySmall rfl (Real.sqrt_pos.mpr hqueryPos) hvariationBudget
    hfinalOutput hinputOutput houtputLoss (hdeltaSmall.trans (by norm_num))
  simpa only [preparationLoss] using hrestore

/-- Restore a source-generic full-grain candidate on the dyadic ambient
shading and then lift the restored state back to the actual incoming
shading. -/
theorem Proposition63DyadicCurrentReentryData.extremalOneScaleFullGrain_of_ambientPrepared
    {delta sigma initialInputLoss normalizationLoss densityLoss incidence
      currentLoss dyadicLoss weightLoss reentryLoss reentryNormalizationLoss
      firstLoss secondLoss outputLoss queryScale sqrtScale spatialScale
      variationScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
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
    (coefficient : NNReal)
    (dyadicLipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ dyadic.shading.union} =>
        dyadic.planeMap.planeMap point))
    (sourceLeftFactor sourceRightFactor uniformPreparationLoss : ENNReal)
    (uniformCoverBudget : ℕ)
    (step : Proposition63UniformAmbientFullGrainStepData
      (sigma := sigma) (firstLoss := firstLoss) (secondLoss := secondLoss)
      (queryScale := queryScale) dyadic.shading dyadic.planeMap.planeMap
      sourceLeftFactor sourceRightFactor coefficient uniformPreparationLoss
      uniformCoverBudget sqrtScale)
    (hsourceLeftPos : 0 < sourceLeftFactor)
    (hsourceLeftTop : sourceLeftFactor ≠ ⊤)
    (hsourceRightTop : sourceRightFactor ≠ ⊤)
    (hpreparationTop : uniformPreparationLoss ≠ ⊤)
    (hcoverBudgetPos : 0 < uniformCoverBudget)
    (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hqueryPos : 0 < queryScale)
    (hquerySmall : queryScale ≤ 1 / 4)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (hsqrtPos : 0 < sqrtScale)
    (hspatialVariation : (coefficient : ℝ) * spatialScale ≤ variationScale)
    (hsecondOutput : secondLoss ≤ outputLoss)
    (hdyadicOutput : dyadicLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hrestore :
      proposition63Lemma43MassLoss
          (proposition63UniformLineFactor
              (Kakeya.realRpowENN delta (secondLoss + 2)) sqrtScale hsqrtPos *
            (((1 : ENNReal) / 2) /
              (2 * (uniformCoverBudget : ENNReal))) * sourceLeftFactor)
          (sourceRightFactor * (uniformPreparationLoss * 2)) *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta dyadicLoss) :
    Nonempty (Proposition63ExtremalOneScaleFullGrainData
      (sigma := sigma) current currentMap outputLoss queryScale spatialScale
        variationScale) := by
  let volumeFloor := Kakeya.realRpowENN delta (secondLoss + 2)
  let lineVolume := proposition63UniformLineVolume volumeFloor sqrtScale
    hsqrtPos
  let lineFactor := proposition63UniformLineFactor volumeFloor sqrtScale
    hsqrtPos
  let inverseCoverFactor : ENNReal :=
    ((1 : ENNReal) / 2) / (2 * (uniformCoverBudget : ENNReal))
  let leftFactor := lineFactor * inverseCoverFactor * sourceLeftFactor
  let rightFactor := sourceRightFactor * (uniformPreparationLoss * 2)
  let full := Classical.choice <|
    proposition63_oneScale_fullGrainCandidate_of_extremal
      dyadic.planeMap.planeMap step.original step.prepared step.cells
      root.normalization.line_class hqueryPos
      (hquerySmall.trans (by norm_num)) hsqrtScale step.plane_unit
      hcoefficientOne
      (fun first hfirst second hsecond =>
        dyadicLipschitz.dist_le_mul
          ⟨first, paperSubshading_union step.original.subshading hfirst⟩
          ⟨second, paperSubshading_union step.original.subshading hsecond⟩)
      uniformCoverBudget hcoverBudgetPos step.cover_budget hdeltaSmall
  let candidate := full.lineHitCandidate dyadic.extremal.delta_pos
  have hcandidateSub : PaperIsSubshading candidate dyadic.shading :=
    full.lineHitCandidate_subshading_source dyadic.extremal.delta_pos
  have hcandidateCubical : WZ1PaperIsCubicalShading candidate :=
    full.lineHitCandidate_cubical dyadic.extremal.delta_pos
  have hcandidateVariation : ∀ first ∈ candidate.union,
      ∀ second ∈ candidate.union, dist first second ≤ spatialScale →
        dist (dyadic.planeMap.planeMap first)
          (dyadic.planeMap.planeMap second) ≤ variationScale := by
    intro first hfirst second hsecond hdistance
    exact (dyadicLipschitz.dist_le_mul
      ⟨first, paperSubshading_union hcandidateSub hfirst⟩
      ⟨second, paperSubshading_union hcandidateSub hsecond⟩).trans <|
        (mul_le_mul_of_nonneg_left hdistance coefficient.coe_nonneg).trans
          hspatialVariation
  have hconstant : Kakeya.realRpowENN delta (-secondLoss) ≤
      Kakeya.realRpowENN delta (-outputLoss) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge dyadic.extremal.delta_pos
      dyadic.extremal.delta_le_one (by linarith)
  have hcandidateAD : ∀ point ∈ candidate.union,
      IsADSet1
        (scalarProjection (dyadic.planeMap.planeMap point)
          (candidate.union ∩ Metric.closedBall point
            (Real.sqrt queryScale)))
        queryScale (1 - sigma)
        (Kakeya.realRpowENN delta (-outputLoss)) := by
    intro point hpoint
    exact (full.lineHitCandidate_local_ad dyadic.extremal.delta_pos point
      hpoint).mono_constant hconstant
  have hrawMass : leftFactor * dyadic.shading.mass ≤
      rightFactor * candidate.mass := by
    have hcandidateMass :=
      full.lineHitCandidate_mass_from_current_cancel_cellMass
        (current := dyadic.shading) sourceLeftFactor sourceRightFactor
        step.incoming_mass dyadic.extremal.delta_pos hqueryPos hsqrtPos
    have hqueryFactor : ENNReal.ofReal (4 * queryScale) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hright : sourceRightFactor *
          (step.prepared.preparationLoss *
            (2 * ENNReal.ofReal (4 * queryScale))) ≤
        sourceRightFactor * (uniformPreparationLoss * 2) := by
      apply mul_le_mul_right
      calc
        step.prepared.preparationLoss *
              (2 * ENNReal.ofReal (4 * queryScale)) ≤
            uniformPreparationLoss *
              (2 * ENNReal.ofReal (4 * queryScale)) := by
          gcongr
          exact step.preparation_budget
        _ ≤ uniformPreparationLoss * 2 := by
          gcongr
          simpa only [mul_one] using mul_le_mul_right hqueryFactor 2
    exact hcandidateMass.trans (mul_le_mul_left hright candidate.mass)
  have hlineFactorPos : 0 < lineFactor := by
    apply proposition63UniformLineFactor_pos
    · simp [volumeFloor, Kakeya.realRpowENN,
        Real.rpow_pos_of_pos dyadic.extremal.delta_pos]
    · simp [volumeFloor, Kakeya.realRpowENN]
  have hlineFactorTop : lineFactor ≠ ⊤ := by
    simp [lineFactor, proposition63UniformLineFactor]
  have hcoverCastPos : 0 < (uniformCoverBudget : ENNReal) := by
    exact_mod_cast hcoverBudgetPos
  have hcoverDenomPos : 0 < (2 * (uniformCoverBudget : ENNReal)) :=
    ENNReal.mul_pos (by norm_num) hcoverCastPos.ne'
  have hcoverDenomTop : (2 * (uniformCoverBudget : ENNReal)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (by simp)
  have hinversePos : 0 < inverseCoverFactor :=
    ENNReal.div_pos (by norm_num) hcoverDenomTop
  have hinverseTop : inverseCoverFactor ≠ ⊤ :=
    ENNReal.div_ne_top (by norm_num) hcoverDenomPos.ne'
  have hleftPos : 0 < leftFactor :=
    ENNReal.mul_pos
      (ENNReal.mul_pos hlineFactorPos.ne' hinversePos.ne').ne'
      hsourceLeftPos.ne'
  have hleftTop : leftFactor ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hlineFactorTop hinverseTop) hsourceLeftTop
  have hrightTop : rightFactor ≠ ⊤ :=
    ENNReal.mul_ne_top hsourceRightTop
      (ENNReal.mul_ne_top hpreparationTop (by norm_num))
  rcases proposition63_extremal_one_scale_full_grain_of_candidate
      dyadic.extremal dyadic.planeMap hcandidateSub hcandidateCubical
      hcandidateVariation hcandidateAD leftFactor rightFactor hleftPos
      hleftTop hrightTop hrawMass hdyadicOutput houtputLoss
      (by simpa only [leftFactor, rightFactor] using hrestore) with ⟨next⟩
  exact ⟨dyadic.liftExtremalOneScaleFullGrain next⟩

/-- Restore the next extremal state on the cubical hull of the cellwise good
regions, while retaining the genuine good-line/full-grain certificates inside
the construction.  The line-hit restriction is a geometric witness and is not
the state iterated at the next scale: forcing extremality on that thinner set
would charge the physical line-volume factor (and hence a non-absorbable
`delta ^ 2` loss).  Here the only restoration cost after the already-extremal
Phase-1 output is the logarithmic multiplicity/balancing preparation. -/
theorem Proposition63DyadicCurrentReentryData.extremalOneScaleFullGrain_of_ambientPrepared_localRestore
    {delta sigma initialInputLoss normalizationLoss densityLoss incidence
      currentLoss dyadicLoss weightLoss reentryLoss reentryNormalizationLoss
      firstLoss secondLoss outputLoss queryScale sqrtScale spatialScale
      variationScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
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
    (coefficient : NNReal)
    (dyadicLipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ dyadic.shading.union} =>
        dyadic.planeMap.planeMap point))
    (sourceLeftFactor sourceRightFactor uniformPreparationLoss : ENNReal)
    (uniformCoverBudget : ℕ)
    (step : Proposition63UniformAmbientFullGrainStepData
      (sigma := sigma) (firstLoss := firstLoss) (secondLoss := secondLoss)
      (queryScale := queryScale) dyadic.shading dyadic.planeMap.planeMap
      sourceLeftFactor sourceRightFactor coefficient uniformPreparationLoss
      uniformCoverBudget sqrtScale)
    (hsourceLeftPos : 0 < sourceLeftFactor)
    (hsourceLeftTop : sourceLeftFactor ≠ ⊤)
    (hsourceRightTop : sourceRightFactor ≠ ⊤)
    (hpreparationTop : uniformPreparationLoss ≠ ⊤)
    (hcoverBudgetPos : 0 < uniformCoverBudget)
    (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hqueryPos : 0 < queryScale)
    (hquerySmall : queryScale ≤ 1 / 4)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (hsqrtPos : 0 < sqrtScale)
    (hspatialVariation : (coefficient : ℝ) * spatialScale ≤ variationScale)
    (hsecondOutput : secondLoss ≤ outputLoss)
    (_hdyadicOutput : dyadicLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hfullGrainRestore :
      4 *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta secondLoss) :
    Nonempty (Proposition63ExtremalOneScaleFullGrainData
      (sigma := sigma) current currentMap outputLoss queryScale spatialScale
        variationScale) := by
  let volumeFloor := Kakeya.realRpowENN delta (secondLoss + 2)
  let lineVolume := proposition63UniformLineVolume volumeFloor sqrtScale
    hsqrtPos
  let full := Classical.choice <|
    proposition63_oneScale_fullGrainCandidate_of_extremal
      dyadic.planeMap.planeMap step.original step.prepared step.cells
      root.normalization.line_class hqueryPos
      (hquerySmall.trans (by norm_num)) hsqrtScale step.plane_unit
      hcoefficientOne
      (fun first hfirst second hsecond =>
        dyadicLipschitz.dist_le_mul
          ⟨first, paperSubshading_union step.original.subshading hfirst⟩
          ⟨second, paperSubshading_union step.original.subshading hsecond⟩)
      uniformCoverBudget hcoverBudgetPos step.cover_budget
      hdeltaSmall
  let candidate := full.candidate dyadic.extremal.delta_pos
  have hcandidateSub : PaperIsSubshading candidate dyadic.shading :=
    full.candidate_subshading_source dyadic.extremal.delta_pos
  have hcandidateCubical : WZ1PaperIsCubicalShading candidate :=
    full.candidate_cubical dyadic.extremal.delta_pos
  have hpreparedCandidate : step.prepared.refined.shading.mass ≤
      4 * candidate.mass :=
    full.cellCertificates.cubicalRetainedShading_quarter_mass
      dyadic.extremal.delta_pos hsqrtPos
      (2 ^ step.prepared.level : ENNReal) (by simp)
      step.prepared.multiplicity_lower step.prepared.multiplicity_upper
  have horiginalCandidate : step.original.shading.mass ≤
      (uniformPreparationLoss * 4) * candidate.mass := by
    calc
      step.original.shading.mass ≤
          step.prepared.preparationLoss *
            step.prepared.refined.shading.mass :=
        step.prepared.mass_retention
      _ ≤ uniformPreparationLoss * (4 * candidate.mass) :=
        mul_le_mul step.preparation_budget hpreparedCandidate bot_le bot_le
      _ = (uniformPreparationLoss * 4) * candidate.mass := by ring
  have hcombinedTop : uniformPreparationLoss * 4 ≠ ⊤ :=
    ENNReal.mul_ne_top hpreparationTop (by norm_num)
  have hcandidateMassFromPrepared : (4 : ENNReal)⁻¹ *
      step.prepared.refined.shading.mass ≤
        candidate.mass := by
    exact (ENNReal.inv_mul_le_iff (by norm_num) (by norm_num)).2 <| by
      simpa only [mul_assoc] using hpreparedCandidate
  have hcandidateExtremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      root.normalization.croppedFamily candidate := by
    apply transfer_cropped_extremal_to_subshading
      4 (by norm_num) (by norm_num) step.prepared.refined.extremal
      (full.cellCertificates.cubicalRetainedShading_subshading
        dyadic.extremal.delta_pos)
      hcandidateMassFromPrepared hcandidateCubical hsecondOutput
      hfullGrainRestore dyadic.extremal.delta_pos
      dyadic.extremal.delta_le_one houtputLoss
  have hcandidateVariation : ∀ first ∈ candidate.union,
      ∀ second ∈ candidate.union, dist first second ≤ spatialScale →
        dist (dyadic.planeMap.planeMap first)
          (dyadic.planeMap.planeMap second) ≤ variationScale :=
    by
      intro first hfirst second hsecond hdistance
      have firstDyadic : first ∈ dyadic.shading.union :=
        paperSubshading_union hcandidateSub hfirst
      have secondDyadic : second ∈ dyadic.shading.union :=
        paperSubshading_union hcandidateSub hsecond
      exact (dyadicLipschitz.dist_le_mul
        ⟨first, firstDyadic⟩ ⟨second, secondDyadic⟩).trans <|
          (mul_le_mul_of_nonneg_left hdistance coefficient.coe_nonneg).trans
            hspatialVariation
  have hconstant : Kakeya.realRpowENN delta (-secondLoss) ≤
      Kakeya.realRpowENN delta (-outputLoss) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge dyadic.extremal.delta_pos
      dyadic.extremal.delta_le_one (by linarith)
  have hcandidateAD : ∀ point ∈ candidate.union,
      IsADSet1
        (scalarProjection (dyadic.planeMap.planeMap point)
          (candidate.union ∩ Metric.closedBall point
            (Real.sqrt queryScale)))
        queryScale (1 - sigma)
        (Kakeya.realRpowENN delta (-outputLoss)) := by
    intro point hpoint
    exact (full.candidate_local_ad dyadic.extremal.delta_pos point hpoint).mono_constant
      hconstant
  let rightFactor := sourceRightFactor * (uniformPreparationLoss * 4)
  let massLoss := proposition63Lemma43MassLoss sourceLeftFactor rightFactor
  have hrightTop : rightFactor ≠ ⊤ :=
    ENNReal.mul_ne_top hsourceRightTop hcombinedTop
  have hmassComparison : sourceLeftFactor * dyadic.shading.mass ≤
      rightFactor * candidate.mass := by
    calc
      sourceLeftFactor * dyadic.shading.mass ≤
          sourceRightFactor * step.original.shading.mass :=
        step.incoming_mass
      _ ≤ sourceRightFactor *
          ((uniformPreparationLoss * 4) * candidate.mass) := by gcongr
      _ = rightFactor * candidate.mass := by
        dsimp only [rightFactor]
        ring
  have hmassRetention : massLoss⁻¹ * dyadic.shading.mass ≤ candidate.mass :=
    proposition63Lemma43MassLoss_inv_mul_le hsourceLeftPos hsourceLeftTop
      hrightTop hmassComparison
  let candidateMap := paperWeakPlaneMapRestrict dyadic.planeMap hcandidateSub
  let next : Proposition63ExtremalOneScaleFullGrainData
      (sigma := sigma) dyadic.shading dyadic.planeMap outputLoss queryScale
        spatialScale variationScale :=
    { shading := candidate
      subshading := hcandidateSub
      cubical := hcandidateCubical
      planeMap := candidateMap
      same_plane_map := rfl
      variation := hcandidateVariation
      local_ad := hcandidateAD
      massLoss := massLoss
      massLoss_pos := proposition63Lemma43MassLoss_pos _ _
      massLoss_ne_top := proposition63Lemma43MassLoss_ne_top
        hsourceLeftPos hrightTop
      mass_retention := hmassRetention
      extremal := hcandidateExtremal }
  exact ⟨dyadic.liftExtremalOneScaleFullGrain next⟩

/-- Complete the dyadic one-scale step while restoring the iterated state at
the cubical hull of all good projection grains.  The selected good lines are
still constructed and stored inside `full`; only the unnecessarily thinner
line-hit shading is omitted from the extremality ledger. -/
theorem Proposition63DyadicCurrentReentryData.extremalOneScaleFullGrain_of_phase1_localRestore
    {delta sigma initialInputLoss normalizationLoss densityLoss incidence
      currentLoss dyadicLoss weightLoss reentryLoss reentryNormalizationLoss
      stickyDataLoss phase1Loss sourceADLoss criticalLoss queryLoss middleLoss
      finalLoss outputLoss queryScale spatialScale variationScale : ℝ}
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
    (coefficient : NNReal)
    (currentLipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ current.union} =>
        currentMap.planeMap point))
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
    (hleftPos : 0 < leftFactor) (hleftTop : leftFactor ≠ ⊤)
    (hrightTop : rightFactor ≠ ⊤)
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
        Kakeya.realRpowENN delta dyadic.reentry.reentryNormalizationLoss)
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
    (hdeltaOne : delta < 1) (hcriticalLoss : 0 < criticalLoss)
    (hsourceADLoss : 0 < sourceADLoss)
    (hADGap : sourceADLoss < criticalLoss)
    (hADSmall : delta ≤ Real.rpow (10 : ℝ)
      (-1 / (criticalLoss - sourceADLoss)))
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : ∀ epsilon₁ : ℝ, epsilon₁ =
        (sigma - 2 * dyadic.reentry.reentryNormalizationLoss) / 20 →
      0 < epsilon₁ → ∀ scale : ℝ, 0 < scale → scale ≤ logScale →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hrhoLower : Real.rpow delta stickyDataLoss ≤ rho.1)
    (hrhoBound : rho.1 ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (hstickyAD : 3 * stickyDataLoss ≤ sourceADLoss)
    (hqueryPos : 0 < queryScale) (hquerySmall : queryScale ≤ 1 / 4)
    (hqueryGridFloor : 48 * delta ^ 2 ≤ queryScale)
    (hcriticalQuery : criticalLoss < queryLoss)
    (hqueryAbsorb : delta ≤ Real.rpow (40 : ℝ)
      (-1 / (queryLoss - criticalLoss)))
    (hqueryMiddle : queryLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (hmultiplicitySlack :
      (((Nat.log 2 root.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal) * Kakeya.realRpowENN delta middleLoss) ≤
        Kakeya.realRpowENN delta queryLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hperiodicScale : 50 * delta ≤ Real.sqrt queryScale)
    (hsqrtOne : Real.sqrt queryScale ≤ 1)
    (hboundaryScalar :
      2 * 24000000 *
          (Kakeya.realRpowENN delta (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (delta / Real.sqrt queryScale)) <
        Kakeya.realRpowENN delta middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss) (hfinalLoss : 0 < finalLoss)
    (hbalancingSlack : proposition63FreshBalancingEnvelope delta *
        Kakeya.realRpowENN delta finalLoss ≤
      Kakeya.realRpowENN delta middleLoss)
    (uniformCoverBudget : ℕ) (hcoverBudgetPos : 0 < uniformCoverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN delta (-finalLoss) *
              Kakeya.realRpowENN (1 / queryScale) (1 - sigma))) ≤
        (uniformCoverBudget : ENNReal))
    (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hvariationBudget :
      (coefficient : ℝ) * spatialScale ≤ variationScale)
    (hfinalOutput : finalLoss ≤ outputLoss)
    (hdyadicOutput : dyadicLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hfullGrainRestore :
      4 * Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta finalLoss) :
    Nonempty (Proposition63ExtremalOneScaleFullGrainData
      (sigma := sigma) current currentMap outputLoss queryScale spatialScale
        variationScale) := by
  rcases dyadic.phase1AlignedAmbientCandidate_of_bounds sticky
      coarseMultiplicity regularity hcoarseMultiplicityPos
      hcoarseMultiplicityTop hregularityPos hregularityTop hcoarseLower
      hcoarseUpper leftFactor rightFactor hleft hright hrhoAligned
      hphase1Loss hreentryPhase1
      hphase1Slack hsigma hsigmaOne hreentryLoss hreentrySticky hstickySmall
      hrhoSmall hrhoPropertyP hhavg hdyadicCritical hnormalizationCritical
      hcommonDensityLift hdeltaOne hcriticalLoss hsourceADLoss hADGap hADSmall
      logScale hrhoLog hlog hrhoLower hrhoBound hstickyAD hqueryPos
      hquerySmall hqueryGridFloor hcriticalQuery hqueryAbsorb with
    ⟨original, incomingMass⟩
  let preparationLoss := proposition63UniformPreparationLoss
    root.normalization.croppedFamily
  let step := Classical.choice <|
    proposition63_uniformAmbientFullGrainStep_of_freshBalancingCWA_uniform
      dyadic.planeMap.planeMap leftFactor rightFactor coefficient
      uniformCoverBudget original incomingMass hqueryMiddle hmiddleLoss
      hmultiplicitySlack root.normalization.line_class hdeltaSmall
      hperiodicScale (Real.sqrt_pos.mpr hqueryPos) hsqrtOne hboundaryScalar
      hmiddleFinal hfinalLoss hbalancingSlack
      (fun point hpoint => dyadic.planeMap.unit point <|
        paperSubshading_union original.subshading hpoint) hcoverBudget
  have preparationTop : preparationLoss ≠ ⊤ :=
    (proposition63UniformPreparationLoss_pos_ne_top
      root.normalization.croppedFamily dyadic.extremal.delta_pos
      dyadic.extremal.delta_le_one).2
  have dyadicLipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ dyadic.shading.union} =>
        dyadic.planeMap.planeMap point) := by
    intro first second
    have firstCurrent : (first : Point3) ∈ current.union :=
      paperSubshading_union dyadic.subshading first.prop
    have secondCurrent : (second : Point3) ∈ current.union :=
      paperSubshading_union dyadic.subshading second.prop
    change edist (dyadic.planeMap.planeMap first)
      (dyadic.planeMap.planeMap second) ≤ coefficient * edist first second
    rw [dyadic.same_plane_map]
    exact currentLipschitz ⟨first, firstCurrent⟩ ⟨second, secondCurrent⟩
  exact dyadic.extremalOneScaleFullGrain_of_ambientPrepared_localRestore
    coefficient dyadicLipschitz leftFactor rightFactor preparationLoss
    uniformCoverBudget step hleftPos hleftTop hrightTop preparationTop
    hcoverBudgetPos hcoefficientOne hqueryPos hquerySmall rfl
    (Real.sqrt_pos.mpr hqueryPos) hvariationBudget hfinalOutput
    hdyadicOutput houtputLoss (hdeltaSmall.trans (by norm_num))
    hfullGrainRestore

/-- Specialize the sharp full-grain transition to the coarse multiplicity
band carried by the genuine rich Node-3 terminal. -/
theorem Proposition63DyadicCurrentReentryData.extremalOneScaleFullGrain_of_rich_phase1_localRestore
    {delta sigma initialInputLoss normalizationLoss densityLoss incidence
      currentLoss dyadicLoss weightLoss reentryLoss reentryNormalizationLoss
      producerLoss stickyDataLoss phase1Loss sourceADLoss criticalLoss
      queryLoss middleLoss
      finalLoss outputLoss queryScale spatialScale variationScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
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
    (coefficient : NNReal)
    (currentLipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ current.union} =>
        currentMap.planeMap point))
    {rho : WZ2PaperRequestedScale delta}
    (hreentrySourceLoss : 0 < reentryLoss)
    (hreentryNormalizationLossPos :
      0 < dyadic.reentry.reentryNormalizationLoss)
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := producerLoss)
      dyadic.reentry.normalization.croppedRefined
      (dyadic.reentry.normalization.toPropStickyReentryData
        hreentrySourceLoss
        dyadic.reentry.reentry_normalization_loss_pos) rho)
    (hproducerSticky : producerLoss ≤ stickyDataLoss)
    (leftFactor rightFactor : ENNReal)
    (hleftPos : 0 < leftFactor) (hleftTop : leftFactor ≠ ⊤)
    (hrightTop : rightFactor ≠ ⊤)
    (hleft : leftFactor ≤
      (73 / 100 : ENNReal) * dyadic.reentry.normalizationWeight)
    (hright : dyadic.reentry.regularized.regularizationLoss *
        ((4 * (rich.terminal.regularity : ENNReal)) *
          (wz2PaperPureRefinementFraction delta 61)⁻¹) ≤ rightFactor)
    (hrhoAligned : rho.1 = alignedCoarseScale delta queryScale)
    (hphase1Loss : 0 < phase1Loss)
    (hreentryPhase1 : dyadic.reentry.reentryNormalizationLoss ≤ phase1Loss)
    (hphase1Slack :
      (wz2PaperPureRefinementFraction delta 61)⁻¹ *
          Kakeya.realRpowENN delta phase1Loss ≤
        Kakeya.realRpowENN delta
          dyadic.reentry.reentryNormalizationLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
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
              ((4 * (rich.terminal.regularity : ENNReal)) *
                (wz2PaperPureRefinementFraction delta 61)⁻¹)) *
          Kakeya.realRpowENN delta criticalLoss ≤
        dyadic.reentry.normalizationWeight *
          Kakeya.realRpowENN delta
            dyadic.reentry.reentryNormalizationLoss)
    (hdeltaOne : delta < 1) (hcriticalLoss : 0 < criticalLoss)
    (hsourceADLoss : 0 < sourceADLoss)
    (hADGap : sourceADLoss < criticalLoss)
    (hADSmall : delta ≤ Real.rpow (10 : ℝ)
      (-1 / (criticalLoss - sourceADLoss)))
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : ∀ epsilon₁ : ℝ, epsilon₁ =
        (sigma - 2 * dyadic.reentry.reentryNormalizationLoss) / 20 →
      0 < epsilon₁ → ∀ scale : ℝ, 0 < scale → scale ≤ logScale →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hrhoLower : Real.rpow delta stickyDataLoss ≤ rho.1)
    (hrhoBound : rho.1 ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (hstickyAD : 3 * stickyDataLoss ≤ sourceADLoss)
    (hqueryPos : 0 < queryScale) (hquerySmall : queryScale ≤ 1 / 4)
    (hqueryGridFloor : 48 * delta ^ 2 ≤ queryScale)
    (hcriticalQuery : criticalLoss < queryLoss)
    (hqueryAbsorb : delta ≤ Real.rpow (40 : ℝ)
      (-1 / (queryLoss - criticalLoss)))
    (hqueryMiddle : queryLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (hmultiplicitySlack :
      (((Nat.log 2 root.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal) * Kakeya.realRpowENN delta middleLoss) ≤
        Kakeya.realRpowENN delta queryLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hperiodicScale : 50 * delta ≤ Real.sqrt queryScale)
    (hsqrtOne : Real.sqrt queryScale ≤ 1)
    (hboundaryScalar :
      2 * 24000000 *
          (Kakeya.realRpowENN delta (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (delta / Real.sqrt queryScale)) <
        Kakeya.realRpowENN delta middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss) (hfinalLoss : 0 < finalLoss)
    (hbalancingSlack : proposition63FreshBalancingEnvelope delta *
        Kakeya.realRpowENN delta finalLoss ≤
      Kakeya.realRpowENN delta middleLoss)
    (uniformCoverBudget : ℕ) (hcoverBudgetPos : 0 < uniformCoverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN delta (-finalLoss) *
              Kakeya.realRpowENN (1 / queryScale) (1 - sigma))) ≤
        (uniformCoverBudget : ENNReal))
    (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hvariationBudget :
      (coefficient : ℝ) * spatialScale ≤ variationScale)
    (hfinalOutput : finalLoss ≤ outputLoss)
    (hdyadicOutput : dyadicLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hfullGrainRestore :
      4 * Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta finalLoss) :
    Nonempty (Proposition63ExtremalOneScaleFullGrainData
      (sigma := sigma) current currentMap outputLoss queryScale spatialScale
        variationScale) := by
  have hcoarsePos : (0 : ENNReal) < rich.terminal.muCoarse := by
    exact_mod_cast rich.terminal.muCoarse_pos
  have hregularityPos : (0 : ENNReal) < rich.terminal.regularity := by
    exact_mod_cast rich.terminal.regularity_pos
  exact dyadic.extremalOneScaleFullGrain_of_phase1_localRestore
    (coefficient := coefficient) (currentLipschitz := currentLipschitz)
    (sticky := rich.data.mono_loss hproducerSticky)
    (coarseMultiplicity := (rich.terminal.muCoarse : ENNReal))
    (regularity := (rich.terminal.regularity : ENNReal))
    (leftFactor := leftFactor) (rightFactor := rightFactor)
    (hcoarseMultiplicityPos := hcoarsePos)
    (hcoarseMultiplicityTop := ENNReal.natCast_ne_top _)
    (hregularityPos := hregularityPos)
    (hregularityTop := ENNReal.natCast_ne_top _)
    (hcoarseLower := fun point hpoint => by
      simpa only [PureWZ2PropStickyData.mono_loss] using
        (rich.terminal.coarse_pointMultiplicity_band hpoint).1)
    (hcoarseUpper := fun point hpoint => by
      simpa only [PureWZ2PropStickyData.mono_loss, Nat.cast_mul] using
        (rich.terminal.coarse_pointMultiplicity_band hpoint).2)
    (hleftPos := hleftPos) (hleftTop := hleftTop)
    (hrightTop := hrightTop) (hleft := hleft) (hright := hright)
    (hrhoAligned := hrhoAligned) (hphase1Loss := hphase1Loss)
    (hreentryPhase1 := hreentryPhase1) (hphase1Slack := hphase1Slack)
    (hsigma := hsigma) (hsigmaOne := hsigmaOne)
    (hreentryLoss := hreentryNormalizationLossPos)
    (hreentrySticky := hreentrySticky) (hstickySmall := hstickySmall)
    (hrhoSmall := hrhoSmall) (hrhoPropertyP := hrhoPropertyP)
    (hhavg := hhavg) (hdyadicCritical := hdyadicCritical)
    (hnormalizationCritical := hnormalizationCritical)
    (hcommonDensityLift := hcommonDensityLift) (hdeltaOne := hdeltaOne)
    (hcriticalLoss := hcriticalLoss) (hsourceADLoss := hsourceADLoss)
    (hADGap := hADGap) (hADSmall := hADSmall) (logScale := logScale)
    (hrhoLog := hrhoLog) (hlog := hlog) (hrhoLower := hrhoLower)
    (hrhoBound := hrhoBound) (hstickyAD := hstickyAD)
    (hqueryPos := hqueryPos) (hquerySmall := hquerySmall)
    (hqueryGridFloor := hqueryGridFloor) (hcriticalQuery := hcriticalQuery)
    (hqueryAbsorb := hqueryAbsorb) (hqueryMiddle := hqueryMiddle)
    (hmiddleLoss := hmiddleLoss) (hmultiplicitySlack := hmultiplicitySlack)
    (hdeltaSmall := hdeltaSmall) (hperiodicScale := hperiodicScale)
    (hsqrtOne := hsqrtOne) (hboundaryScalar := hboundaryScalar)
    (hmiddleFinal := hmiddleFinal) (hfinalLoss := hfinalLoss)
    (hbalancingSlack := hbalancingSlack)
    (uniformCoverBudget := uniformCoverBudget)
    (hcoverBudgetPos := hcoverBudgetPos) (hcoverBudget := hcoverBudget)
    (hcoefficientOne := hcoefficientOne)
    (hvariationBudget := hvariationBudget) (hfinalOutput := hfinalOutput)
    (hdyadicOutput := hdyadicOutput) (houtputLoss := houtputLoss)
    (hfullGrainRestore := hfullGrainRestore)

/-- Complete one paper-ordered Lemma 4.12 step: use the sharp ambient
Phase-1 cancellation, prepare its output on the dyadic ambient family,
restore the full-grain candidate, and expose the result over the original
current shading. -/
theorem Proposition63DyadicCurrentReentryData.extremalOneScaleFullGrain_of_phase1
    {delta sigma initialInputLoss normalizationLoss densityLoss incidence
      currentLoss dyadicLoss weightLoss reentryLoss reentryNormalizationLoss
      stickyDataLoss phase1Loss sourceADLoss criticalLoss queryLoss middleLoss
      finalLoss outputLoss queryScale spatialScale variationScale : ℝ}
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
    (coefficient : NNReal)
    (currentLipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ current.union} =>
        currentMap.planeMap point))
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
    (hleftPos : 0 < leftFactor) (hleftTop : leftFactor ≠ ⊤)
    (hrightTop : rightFactor ≠ ⊤)
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
        Kakeya.realRpowENN delta dyadic.reentry.reentryNormalizationLoss)
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
    (hdeltaOne : delta < 1) (hcriticalLoss : 0 < criticalLoss)
    (hsourceADLoss : 0 < sourceADLoss)
    (hADGap : sourceADLoss < criticalLoss)
    (hADSmall : delta ≤ Real.rpow (10 : ℝ)
      (-1 / (criticalLoss - sourceADLoss)))
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : ∀ epsilon₁ : ℝ, epsilon₁ =
        (sigma - 2 * dyadic.reentry.reentryNormalizationLoss) / 20 →
      0 < epsilon₁ → ∀ scale : ℝ, 0 < scale → scale ≤ logScale →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hrhoLower : Real.rpow delta stickyDataLoss ≤ rho.1)
    (hrhoBound : rho.1 ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (hstickyAD : 3 * stickyDataLoss ≤ sourceADLoss)
    (hqueryPos : 0 < queryScale) (hquerySmall : queryScale ≤ 1 / 4)
    (hqueryGridFloor : 48 * delta ^ 2 ≤ queryScale)
    (hcriticalQuery : criticalLoss < queryLoss)
    (hqueryAbsorb : delta ≤ Real.rpow (40 : ℝ)
      (-1 / (queryLoss - criticalLoss)))
    (hqueryMiddle : queryLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (hmultiplicitySlack :
      (((Nat.log 2 root.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal) * Kakeya.realRpowENN delta middleLoss) ≤
        Kakeya.realRpowENN delta queryLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hperiodicScale : 50 * delta ≤ Real.sqrt queryScale)
    (hsqrtOne : Real.sqrt queryScale ≤ 1)
    (hboundaryScalar :
      2 * 24000000 *
          (Kakeya.realRpowENN delta (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (delta / Real.sqrt queryScale)) <
        Kakeya.realRpowENN delta middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss) (hfinalLoss : 0 < finalLoss)
    (hbalancingSlack : proposition63FreshBalancingEnvelope delta *
        Kakeya.realRpowENN delta finalLoss ≤
      Kakeya.realRpowENN delta middleLoss)
    (uniformCoverBudget : ℕ) (hcoverBudgetPos : 0 < uniformCoverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN delta (-finalLoss) *
              Kakeya.realRpowENN (1 / queryScale) (1 - sigma))) ≤
        (uniformCoverBudget : ENNReal))
    (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hvariationBudget :
      (coefficient : ℝ) * spatialScale ≤ variationScale)
    (hfinalOutput : finalLoss ≤ outputLoss)
    (hdyadicOutput : dyadicLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hfullGrainRestore :
      4 * Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta finalLoss) :
    Nonempty (Proposition63ExtremalOneScaleFullGrainData
      (sigma := sigma) current currentMap outputLoss queryScale spatialScale
        variationScale) := by
  rcases dyadic.phase1AlignedAmbientCandidate_of_bounds sticky
      coarseMultiplicity regularity hcoarseMultiplicityPos
      hcoarseMultiplicityTop hregularityPos hregularityTop hcoarseLower
      hcoarseUpper leftFactor rightFactor hleft hright hrhoAligned
      hphase1Loss hreentryPhase1
      hphase1Slack hsigma hsigmaOne hreentryLoss hreentrySticky hstickySmall
      hrhoSmall hrhoPropertyP hhavg hdyadicCritical hnormalizationCritical
      hcommonDensityLift hdeltaOne hcriticalLoss hsourceADLoss hADGap hADSmall
      logScale hrhoLog hlog hrhoLower hrhoBound hstickyAD hqueryPos
      hquerySmall hqueryGridFloor hcriticalQuery hqueryAbsorb with
    ⟨original, incomingMass⟩
  let preparationLoss := proposition63UniformPreparationLoss
    root.normalization.croppedFamily
  let step := Classical.choice <|
    proposition63_uniformAmbientFullGrainStep_of_freshBalancingCWA_uniform
      dyadic.planeMap.planeMap leftFactor rightFactor coefficient
      uniformCoverBudget original incomingMass hqueryMiddle hmiddleLoss
      hmultiplicitySlack root.normalization.line_class hdeltaSmall
      hperiodicScale (Real.sqrt_pos.mpr hqueryPos) hsqrtOne hboundaryScalar
      hmiddleFinal hfinalLoss hbalancingSlack
      (fun point hpoint => dyadic.planeMap.unit point <|
        paperSubshading_union original.subshading hpoint) hcoverBudget
  have preparationTop : preparationLoss ≠ ⊤ :=
    (proposition63UniformPreparationLoss_pos_ne_top
      root.normalization.croppedFamily dyadic.extremal.delta_pos
      dyadic.extremal.delta_le_one).2
  have dyadicLipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ dyadic.shading.union} =>
        dyadic.planeMap.planeMap point) := by
    intro first second
    have firstCurrent : (first : Point3) ∈ current.union :=
      paperSubshading_union dyadic.subshading first.prop
    have secondCurrent : (second : Point3) ∈ current.union :=
      paperSubshading_union dyadic.subshading second.prop
    change edist (dyadic.planeMap.planeMap first)
      (dyadic.planeMap.planeMap second) ≤ coefficient * edist first second
    rw [dyadic.same_plane_map]
    exact currentLipschitz ⟨first, firstCurrent⟩ ⟨second, secondCurrent⟩
  exact dyadic.extremalOneScaleFullGrain_of_ambientPrepared_localRestore
    coefficient
    dyadicLipschitz leftFactor rightFactor preparationLoss uniformCoverBudget
    step hleftPos hleftTop hrightTop preparationTop hcoverBudgetPos
    hcoefficientOne hqueryPos hquerySmall rfl (Real.sqrt_pos.mpr hqueryPos)
    hvariationBudget hfinalOutput hdyadicOutput houtputLoss
    (hdeltaSmall.trans (by norm_num)) hfullGrainRestore

/-- Final state of a finite sequence of restored full-grain steps.  The
product of the individual `massLoss` fields is retained only as an audit
ledger; every runtime transition has already restored extremality before the
next step is invoked. -/
structure Proposition63ExtremalFiniteFullGrainData
    {delta sigma incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (current : WZ1PaperTubeShading family)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (loss : ℕ → ℝ) (N : ℕ)
    (queryScale spatialScale variationScale : ℕ → ℝ) where
  shading : WZ1PaperTubeShading family
  subshading : PaperIsSubshading shading current
  cubical : WZ1PaperIsCubicalShading shading
  planeMap : PaperWZ1WeakPlaneMapData shading incidence
  same_plane_map : planeMap.planeMap = currentMap.planeMap
  variation : ∀ index, index < N → ∀ first ∈ shading.union,
    ∀ second ∈ shading.union, dist first second ≤ spatialScale index →
      dist (planeMap.planeMap first) (planeMap.planeMap second) ≤
        variationScale index
  local_ad : ∀ index, index < N → ∀ point ∈ shading.union,
    IsADSet1
      (scalarProjection (planeMap.planeMap point)
        (shading.union ∩ Metric.closedBall point
          (Real.sqrt (queryScale index))))
      (queryScale index) (1 - sigma)
      (Kakeya.realRpowENN delta (-(loss N)))
  massLoss : ENNReal
  massLoss_pos : 0 < massLoss
  massLoss_ne_top : massLoss ≠ ⊤
  mass_retention : massLoss⁻¹ * current.mass ≤ shading.mass
  extremal : WZ2PaperCroppedIsExtremal sigma (loss N) family shading

/-- Forward dependent-family recursion for Lemma 4.12.  Step `index` starts
from the already-restored `loss index` extremal state and returns a
`loss (index + 1)` state.  Old AD estimates are restricted to the new
subshading and weakened only to the next loss. -/
theorem proposition63_extremal_finite_full_grain
    {delta sigma incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {current : WZ1PaperTubeShading family}
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (loss : ℕ → ℝ)
    (loss_mono : ∀ index, loss index ≤ loss (index + 1))
    (currentExtremal : WZ2PaperCroppedIsExtremal
      sigma (loss 0) family current)
    (N : ℕ)
    (queryScale spatialScale variationScale : ℕ → ℝ)
    (step : ∀ index, index < N →
      ∀ (active : WZ1PaperTubeShading family),
      ∀ (activeMap : PaperWZ1WeakPlaneMapData active incidence),
        activeMap.planeMap = currentMap.planeMap →
        WZ2PaperCroppedIsExtremal sigma (loss index) family active →
        Nonempty (Proposition63ExtremalOneScaleFullGrainData
          (sigma := sigma) active activeMap (loss (index + 1))
            (queryScale index) (spatialScale index)
              (variationScale index))) :
    Nonempty (Proposition63ExtremalFiniteFullGrainData
      (sigma := sigma) current currentMap loss N queryScale spatialScale
        variationScale) := by
  let P : ℕ → Prop := fun completed =>
    ∃ active : WZ1PaperTubeShading family,
      ∃ activeMap : PaperWZ1WeakPlaneMapData active incidence,
        PaperIsSubshading active current ∧
        WZ1PaperIsCubicalShading active ∧
        activeMap.planeMap = currentMap.planeMap ∧
        (∀ index, index < completed → ∀ first ∈ active.union,
          ∀ second ∈ active.union, dist first second ≤ spatialScale index →
            dist (activeMap.planeMap first) (activeMap.planeMap second) ≤
              variationScale index) ∧
        (∀ index, index < completed → ∀ point ∈ active.union,
          IsADSet1
            (scalarProjection (activeMap.planeMap point)
              (active.union ∩ Metric.closedBall point
                (Real.sqrt (queryScale index))))
            (queryScale index) (1 - sigma)
            (Kakeya.realRpowENN delta (-(loss completed)))) ∧
        (∃ massLoss : ENNReal, 0 < massLoss ∧ massLoss ≠ ⊤ ∧
          massLoss⁻¹ * current.mass ≤ active.mass) ∧
        WZ2PaperCroppedIsExtremal sigma (loss completed) family active
  have base : P 0 := by
    exact ⟨current, currentMap, fun _ => Set.Subset.rfl,
      currentExtremal.cubical, rfl, (by intro index index_lt; omega),
      (by intro index index_lt; omega), ⟨1, by norm_num, by norm_num, by simp⟩,
      currentExtremal⟩
  have advance : ∀ completed, completed < N → P completed →
      P (completed + 1) := by
    intro completed completed_lt state
    rcases state with ⟨active, activeMap, activeSub, activeCubical, activeSame,
      activeVariation, activeAD, activeMassLoss, activeExtremal⟩
    rcases activeMassLoss with
      ⟨activeLoss, activeLossPos, activeLossTop, activeRetention⟩
    rcases step completed completed_lt active activeMap activeSame
        activeExtremal with ⟨next⟩
    let massLoss := activeLoss * next.massLoss
    have massLossPos : 0 < massLoss := ENNReal.mul_pos
      activeLossPos.ne' next.massLoss_pos.ne'
    have massLossTop : massLoss ≠ ⊤ := ENNReal.mul_ne_top
      activeLossTop next.massLoss_ne_top
    have massRetention : massLoss⁻¹ * current.mass ≤ next.shading.mass := by
      rw [ENNReal.mul_inv (Or.inl activeLossPos.ne')
        (Or.inl activeLossTop)]
      calc
        (activeLoss⁻¹ * next.massLoss⁻¹) * current.mass =
            next.massLoss⁻¹ * (activeLoss⁻¹ * current.mass) := by ring
        _ ≤ next.massLoss⁻¹ * active.mass := by
          exact mul_le_mul_right activeRetention _
        _ ≤ next.shading.mass := next.mass_retention
    have nextSubCurrent : PaperIsSubshading next.shading current :=
      fun tube point pointMem => activeSub tube (next.subshading tube pointMem)
    have lossStep : loss completed ≤ loss (completed + 1) :=
      loss_mono completed
    have constantStep : Kakeya.realRpowENN delta (-(loss completed)) ≤
        Kakeya.realRpowENN delta (-(loss (completed + 1))) := by
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge activeExtremal.delta_pos
        activeExtremal.delta_le_one (by linarith)
    refine ⟨next.shading, next.planeMap, nextSubCurrent, next.cubical,
      next.same_plane_map.trans activeSame, ?_, ?_,
      ⟨massLoss, massLossPos, massLossTop, massRetention⟩, next.extremal⟩
    · intro index index_lt first firstMem second secondMem distanceBound
      by_cases isNew : index = completed
      · subst index
        exact next.variation first firstMem second secondMem distanceBound
      · have indexOld : index < completed := by omega
        have firstActive : first ∈ active.union := by
          rcases firstMem with ⟨tube, tubeMem⟩
          exact ⟨tube, next.subshading tube tubeMem⟩
        have secondActive : second ∈ active.union := by
          rcases secondMem with ⟨tube, tubeMem⟩
          exact ⟨tube, next.subshading tube tubeMem⟩
        rw [next.same_plane_map]
        exact activeVariation index indexOld first firstActive second
          secondActive distanceBound
    · intro index index_lt point pointMem
      by_cases isNew : index = completed
      · subst index
        exact next.local_ad point pointMem
      · have indexOld : index < completed := by omega
        have pointActive : point ∈ active.union := by
          rcases pointMem with ⟨tube, tubeMem⟩
          exact ⟨tube, next.subshading tube tubeMem⟩
        rw [next.same_plane_map]
        have hset :
            scalarProjection (activeMap.planeMap point)
                (next.shading.union ∩ Metric.closedBall point
                  (Real.sqrt (queryScale index))) ⊆
              scalarProjection (activeMap.planeMap point)
                (active.union ∩ Metric.closedBall point
                  (Real.sqrt (queryScale index))) := by
          rintro value ⟨other, hother, rfl⟩
          have otherActive : other ∈ active.union := by
            rcases hother.1 with ⟨tube, tubeMem⟩
            exact ⟨tube, next.subshading tube tubeMem⟩
          exact ⟨other, ⟨otherActive, hother.2⟩, rfl⟩
        exact ((activeAD index indexOld point pointActive).mono hset).mono_constant
          constantStep
  have all : ∀ completed, completed ≤ N → P completed := by
    intro completed completed_le
    induction completed with
    | zero => exact base
    | succ completed inductionHypothesis =>
        exact advance completed (by omega)
          (inductionHypothesis (by omega))
  rcases all N le_rfl with ⟨final, finalMap, finalSub, finalCubical,
    finalSame, finalVariation, finalAD, finalMassLoss, finalExtremal⟩
  rcases finalMassLoss with
    ⟨finalLoss, finalLossPos, finalLossTop, finalRetention⟩
  exact ⟨{
    shading := final
    subshading := finalSub
    cubical := finalCubical
    planeMap := finalMap
    same_plane_map := finalSame
    variation := finalVariation
    local_ad := finalAD
    massLoss := finalLoss
    massLoss_pos := finalLossPos
    massLoss_ne_top := finalLossTop
    mass_retention := finalRetention
    extremal := finalExtremal
  }⟩

/-- Execute one concrete paper-order full-grain step from preselected losses
and family-free scalar receipts.  Runtime choices are limited to the exact
dyadic bands, rich terminal, and a finite natural cover budget. -/
theorem proposition63_extremal_one_scale_full_grain_of_receipts
    {sigma outputLoss : ℝ}
    (losses : Proposition63FullGrainOneScaleLossData sigma outputLoss)
    (reentryAbsorption : Proposition63CurrentReentryAbsorptionData
      losses.rootSourceLoss losses.rootNormalizationLoss losses.densityLoss
      losses.dyadicLoss losses.weightLoss losses.producer.sourceLoss
      (proposition63CanonicalNearbyLevelCount losses.rootNormalizationLoss))
    (dyadicAbsorption : Proposition63FullGrainLogAbsorptionData
      losses.inputLoss losses.dyadicLoss)
    (phase1Retention : Proposition63RefinementRetentionAbsorptionData
      losses.producer.normalizationLoss losses.phase1Loss 61)
    (densityAbsorption : Proposition63FullGrainDensityAbsorptionData
      losses.weightLoss losses.producer.normalizationLoss
      losses.criticalLoss
      (proposition63CanonicalNearbyLevelCount losses.rootNormalizationLoss))
    (phase1Threshold : Proposition63FullGrainPhase1ThresholdData sigma
      losses.producerWindowLoss losses.phase1StickyLoss
      losses.producer.normalizationLoss)
    (multiplicityAbsorption : Proposition63FullGrainLogAbsorptionData
      losses.queryLoss losses.middleLoss)
    (boundaryAbsorption : Proposition63FullGrainBoundaryAbsorptionData
      losses.phase1StickyLoss losses.middleLoss)
    (balancingAbsorption : Proposition63FullGrainBalancingAbsorptionData
      losses.middleLoss losses.finalLoss)
    (restoreAbsorption : Proposition63FullGrainFixedRestoreAbsorptionData
      losses.finalLoss outputLoss)
    {delta : ℝ} (hdeltaPos : 0 < delta) (hdeltaLtOne : delta < 1)
    (hdeltaProducer : delta ≤ losses.producer.delta₀)
    (hdeltaReentry : delta ≤ reentryAbsorption.delta₀)
    (hdeltaDyadic : delta ≤ dyadicAbsorption.delta₀)
    (hdeltaPhase1Retention : delta ≤ phase1Retention.delta₀)
    (hdeltaDensity : delta ≤ densityAbsorption.delta₀)
    (hdeltaPhase1 : delta ≤ phase1Threshold.delta₀)
    (hdeltaMultiplicity : delta ≤ multiplicityAbsorption.delta₀)
    (hdeltaBoundary : delta ≤ boundaryAbsorption.delta₀)
    (hdeltaBalancing : delta ≤ balancingAbsorption.delta₀)
    (hdeltaRestore : delta ≤ restoreAbsorption.delta₀)
    (hADSmall : delta ≤ Real.rpow (10 : ℝ)
      (-1 / (losses.criticalLoss - losses.sourceADLoss)))
    (hqueryAbsorb : delta ≤ Real.rpow (40 : ℝ)
      (-1 / (losses.queryLoss - losses.criticalLoss)))
    {ambientSourceLoss ambientNormalizationLoss : ℝ}
    {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {normalizationExponent : ℕ}
    (ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) ambientShading normalizationExponent ambientSourceLoss
        ambientNormalizationLoss)
    (ambientSource_le : ambientSourceLoss ≤ losses.rootSourceLoss)
    (ambientNormalization_le :
      ambientNormalizationLoss ≤ losses.rootNormalizationLoss)
    (current : WZ1PaperTubeShading ambientFamily)
    (currentExtremal : WZ2PaperCroppedIsExtremal
      sigma losses.inputLoss ambientFamily current)
    (currentSub : PaperIsSubshading current ambientShading)
    {incidence : ℝ}
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (coefficient : NNReal)
    (currentLipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ current.union} =>
        currentMap.planeMap point))
    (queryScale spatialScale variationScale : ℝ)
    (hqueryPos : 0 < queryScale)
    (hquerySmall : queryScale ≤ 1 / 4)
    (hqueryGridFloor : 48 * delta ^ 2 ≤ queryScale)
    (halignedLower : Real.rpow delta
      (1 - losses.producerWindowLoss) ≤
        alignedCoarseScale delta queryScale)
    (hphase1Lower : Real.rpow delta losses.phase1StickyLoss ≤
      alignedCoarseScale delta queryScale)
    (halignedUpper : alignedCoarseScale delta queryScale ≤
      Real.rpow delta losses.producerWindowLoss)
    (hperiodicScale : 50 * delta ≤ Real.sqrt queryScale)
    (hsqrtOne : Real.sqrt queryScale ≤ 1)
    (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hvariationBudget :
      (coefficient : ℝ) * spatialScale ≤ variationScale) :
    Nonempty (Proposition63ExtremalOneScaleFullGrainData
      (sigma := sigma) current currentMap outputLoss queryScale spatialScale
        variationScale) := by
  let scheduledReentry := ambientReentry.mono_losses ambientSource_le
    ambientNormalization_le losses.rootSourceLoss_pos
      losses.rootNormalizationLoss_pos losses.rootSourceLoss_le_half
  let root : Proposition63RootNormalizationData
      (outputLoss := losses.rootNormalizationLoss)
      scheduledReentry.ordinarySource normalizationExponent losses.densityLoss :=
    Proposition63RootNormalizationData.ofPropStickyReentry scheduledReentry
      (reentryAbsorption.density_absorb hdeltaPos hdeltaReentry)
  have ambientTwo :=
    reentryAbsorption.ambient_two hdeltaPos hdeltaReentry
  rcases root.finiteNearbySchedule losses.rootNormalizationLoss_pos
      ambientTwo losses.two_rootNormalization_le_reentry with
    ⟨nearbySchedule⟩
  have regularizationAbsorb :=
    reentryAbsorption.regularization_absorb root.normalization rfl
      nearbySchedule rfl rfl hdeltaPos hdeltaReentry
  have currentSubRoot : PaperIsSubshading current
      root.normalization.croppedRefined := by
    simpa only [root, scheduledReentry,
      Proposition63RootNormalizationData.ofPropStickyReentry,
      Proposition63RootNormalizationData.ofNormalization,
      PureWZ2PropStickyReentryData.toNormalizationData,
      PureWZ2PropStickyReentryData.mono_losses] using currentSub
  rcases root.currentDyadicShadingReentry current currentMap currentExtremal
      currentSubRoot nearbySchedule ambientTwo losses.input_le_dyadic
      losses.dyadic_pos
      (dyadicAbsorption.absorbRootCardLog root hdeltaPos hdeltaDyadic)
      losses.dyadic_le_reentry losses.producer.normalizationLoss_pos
      losses.producer.sourceLoss_le_half
      (reentryAbsorption.canonical_weight_absorb hdeltaPos hdeltaReentry)
      (reentryAbsorption.trace_fixed_absorb hdeltaPos hdeltaReentry)
      (reentryAbsorption.paper_fixed_absorb hdeltaPos hdeltaReentry)
      regularizationAbsorb
      (hdeltaReentry.trans reentryAbsorption.delta₀_le_tiny |>.trans
        (by norm_num)) with
    ⟨dyadic⟩
  let rho : WZ2PaperRequestedScale delta :=
    ⟨alignedCoarseScale delta queryScale,
      delta_le_alignedCoarseScale hdeltaPos hqueryPos,
      halignedUpper.trans <|
        Real.rpow_le_one hdeltaPos.le hdeltaLtOne.le
          losses.producerWindowLoss_pos.le⟩
  rcases proposition63CurrentShadingReentry_richTerminalSticky
      dyadic.reentry losses.producer rfl dyadic.reentry_normalization_loss
      hdeltaProducer rho halignedLower halignedUpper with
    ⟨rich⟩
  have phase1Data := phase1Threshold.run hdeltaPos hdeltaPhase1 rho
    halignedUpper
  have commonDensity := dyadic.commonDensityLift_of_absorption
    losses.producer.sourceLoss_pos rich densityAbsorption hdeltaPos
    hdeltaDensity dyadic.reentry_normalization_weight
    dyadic.reentry_weight_upper dyadic.reentry_level_count
    dyadic.reentry_normalization_loss
  let leftFactor : ENNReal :=
    (73 / 100 : ENNReal) * dyadic.reentry.normalizationWeight
  let rightFactor : ENNReal :=
    dyadic.reentry.regularized.regularizationLoss *
      ((4 * (rich.terminal.regularity : ENNReal)) *
        (wz2PaperPureRefinementFraction delta 61)⁻¹)
  have leftPos : 0 < leftFactor := by
    dsimp only [leftFactor]
    exact ENNReal.mul_pos (by norm_num)
      dyadic.reentry.normalization_weight_ne_zero
  have leftTop : leftFactor ≠ ⊤ := by
    dsimp only [leftFactor]
    exact ENNReal.mul_ne_top
      (ENNReal.div_ne_top (by norm_num) (by norm_num))
      dyadic.reentry.normalization_weight_ne_top
  have refinementFractionNeZero :
      wz2PaperPureRefinementFraction delta 61 ≠ 0 := by
    unfold wz2PaperPureRefinementFraction
    exact pow_ne_zero 61 (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
  have rightTop : rightFactor ≠ ⊤ := by
    dsimp only [rightFactor]
    exact ENNReal.mul_ne_top
      (by
        rw [dyadic.reentry.regularized.regularizationLoss_eq]
        exact ENNReal.mul_ne_top (by norm_num) (by simp))
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _))
        (ENNReal.inv_ne_top.mpr refinementFractionNeZero))
  have phase1Slack :
      (wz2PaperPureRefinementFraction delta 61)⁻¹ *
          Kakeya.realRpowENN delta losses.phase1Loss ≤
        Kakeya.realRpowENN delta
          dyadic.reentry.reentryNormalizationLoss := by
    rw [dyadic.reentry_normalization_loss]
    exact phase1Retention.inverse_mul_absorb hdeltaPos hdeltaLtOne
      hdeltaPhase1Retention
  have multiplicitySlack :
      (((Nat.log 2 root.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal) * Kakeya.realRpowENN delta losses.middleLoss) ≤
        Kakeya.realRpowENN delta losses.queryLoss :=
    multiplicityAbsorption.absorbRootCardLog root hdeltaPos
      hdeltaMultiplicity
  have boundaryScalar := boundaryAbsorption.absorb hdeltaPos hdeltaBoundary
    hqueryPos hqueryGridFloor hphase1Lower
  let coverRequirement : ENNReal :=
    512 *
      ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
        (9 * Kakeya.realRpowENN delta (-losses.finalLoss) *
          Kakeya.realRpowENN (1 / queryScale) (1 - sigma)))
  have coverRequirementTop : coverRequirement ≠ ⊤ := by
    dsimp only [coverRequirement]
    exact ENNReal.mul_ne_top
      (by norm_num) <| ENNReal.mul_ne_top
        (ENNReal.add_ne_top.mpr
          ⟨ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _),
            by norm_num⟩) <| ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
          ENNReal.ofReal_ne_top
  rcases proposition63_exists_positive_nat_cover_budget coverRequirement
      coverRequirementTop with
    ⟨coverBudget, coverBudgetPos, coverBudgetBound⟩
  exact dyadic.extremalOneScaleFullGrain_of_rich_phase1_localRestore
    (coefficient := coefficient) (currentLipschitz := currentLipschitz)
    (hreentrySourceLoss := losses.producer.sourceLoss_pos)
    (hreentryNormalizationLossPos :=
      dyadic.reentry.reentry_normalization_loss_pos)
    (rich := rich)
    (hproducerSticky := losses.producerWindowLoss_le_sticky)
    (leftFactor := leftFactor) (rightFactor := rightFactor)
    (hleftPos := leftPos) (hleftTop := leftTop) (hrightTop := rightTop)
    (hleft := le_rfl) (hright := le_rfl) (hrhoAligned := rfl)
    (hphase1Loss := losses.phase1Loss_pos)
    (hreentryPhase1 := by
      rw [dyadic.reentry_normalization_loss]
      exact losses.reentryNormalization_le_phase1)
    (hphase1Slack := phase1Slack) (hsigma := losses.sigma_pos)
    (hsigmaOne := losses.sigma_lt_one)
    (hreentrySticky := by
      rw [dyadic.reentry_normalization_loss]
      exact losses.reentryNormalization_le_sticky)
    (hstickySmall := by
      rw [dyadic.reentry_normalization_loss]
      exact losses.sticky_small)
    (hrhoSmall := phase1Data.1) (hrhoPropertyP := phase1Data.2.1)
    (hhavg := by
      rw [dyadic.reentry_normalization_loss]
      exact phase1Data.2.2.1)
    (hdyadicCritical := losses.dyadic_le_critical)
    (hnormalizationCritical := losses.rootNormalization_le_critical)
    (hcommonDensityLift := commonDensity) (hdeltaOne := hdeltaLtOne)
    (hcriticalLoss := losses.criticalLoss_pos)
    (hsourceADLoss := losses.sourceADLoss_pos)
    (hADGap := losses.sourceAD_lt_critical) (hADSmall := hADSmall)
    (logScale := phase1Threshold.logScale)
    (hrhoLog := phase1Data.2.2.2.1)
    (hlog := by
      rw [dyadic.reentry_normalization_loss]
      exact phase1Data.2.2.2.2.1)
    (hrhoLower := hphase1Lower)
    (hrhoBound := phase1Data.2.2.2.2.2)
    (hstickyAD := losses.sticky_le_sourceAD)
    (hqueryPos := hqueryPos) (hquerySmall := hquerySmall)
    (hqueryGridFloor := hqueryGridFloor)
    (hcriticalQuery := losses.critical_lt_query)
    (hqueryAbsorb := hqueryAbsorb)
    (hqueryMiddle := losses.query_le_middle)
    (hmiddleLoss := losses.middle_pos)
    (hmultiplicitySlack := multiplicitySlack)
    (hdeltaSmall := hdeltaReentry.trans
      reentryAbsorption.delta₀_le_tiny |>.trans (by norm_num))
    (hperiodicScale := hperiodicScale) (hsqrtOne := hsqrtOne)
    (hboundaryScalar := boundaryScalar)
    (hmiddleFinal := losses.middle_lt_final.le)
    (hfinalLoss := losses.final_pos)
    (hbalancingSlack :=
      balancingAbsorption.absorb hdeltaPos hdeltaBalancing)
    (uniformCoverBudget := coverBudget)
    (hcoverBudgetPos := coverBudgetPos)
    (hcoverBudget := coverBudgetBound)
    (hcoefficientOne := hcoefficientOne)
    (hvariationBudget := hvariationBudget)
    (hfinalOutput := losses.final_lt_output.le)
    (hdyadicOutput := losses.dyadic_le_critical.trans
      (losses.critical_lt_query.le.trans <| losses.query_le_middle.trans <|
        losses.middle_lt_final.le.trans losses.final_lt_output.le))
    (houtputLoss := losses.final_pos.trans losses.final_lt_output)
    (hfullGrainRestore :=
      restoreAbsorption.absorb hdeltaPos hdeltaRestore)

/-- Canonical concrete one-scale producer.  Every loss and analytic threshold
is chosen before the runtime extremizer; `run` only selects genuine dyadic
bands, the Node-3 rich terminal, and a finite cover cardinality. -/
theorem proposition63_extremal_one_scale_full_grain_schedule
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ) (houtputLoss : 0 < outputLoss) :
    Nonempty (Proposition63ExtremalOneScaleFullGrainScheduleData
      sigma outputLoss) := by
  rcases proposition63_full_grain_one_scale_losses sigma critical outputLoss
      houtputLoss with ⟨losses⟩
  let levelCount :=
    proposition63CanonicalNearbyLevelCount losses.rootNormalizationLoss
  have levelCountPos : 0 < levelCount :=
    proposition63CanonicalNearbyLevelCount_pos
      losses.rootNormalizationLoss_pos
  rcases proposition63_current_reentry_absorption losses.rootSourceLoss
      losses.rootNormalizationLoss losses.densityLoss losses.dyadicLoss
      losses.weightLoss losses.producer.sourceLoss levelCount
      losses.rootSource_lt_density losses.rootNormalizationLoss_pos
      losses.density_add_dyadic_lt_weight losses.weight_lt_reentry
      levelCountPos losses.producer.sourceLoss_pos
      losses.reentry_regularization_gap with
    ⟨reentryAbsorption⟩
  rcases proposition63_full_grain_log_absorption losses.inputLoss
      losses.dyadicLoss losses.inputLoss_lt_dyadic with
    ⟨dyadicAbsorption⟩
  rcases proposition63_refinement_retention_absorption
      losses.producer.normalizationLoss losses.phase1Loss 61
      losses.reentryNormalization_lt_phase1 (by norm_num) with
    ⟨phase1Retention⟩
  rcases proposition63_full_grain_density_absorption losses.weightLoss
      losses.producer.normalizationLoss losses.criticalLoss levelCount
      losses.density_gap with ⟨densityAbsorption⟩
  rcases proposition63_full_grain_phase1_threshold sigma
      losses.producerWindowLoss losses.phase1StickyLoss
      losses.producer.normalizationLoss losses.sigma_pos losses.sigma_lt_one
      losses.producerWindowLoss_pos losses.producer.normalizationLoss_pos
      losses.reentryNormalization_lt_half_sigma
      (losses.producerWindowLoss_pos.le.trans
        losses.producerWindowLoss_le_sticky) losses.sticky_small with
    ⟨phase1Threshold⟩
  rcases proposition63_full_grain_log_absorption losses.queryLoss
      losses.middleLoss losses.query_lt_middle with
    ⟨multiplicityAbsorption⟩
  rcases proposition63_full_grain_boundary_absorption
      losses.phase1StickyLoss losses.middleLoss losses.middle_pos
      losses.boundary_gap with ⟨boundaryAbsorption⟩
  rcases proposition63_full_grain_balancing_absorption losses.middleLoss
      losses.finalLoss losses.middle_lt_final with
    ⟨balancingAbsorption⟩
  rcases proposition63_full_grain_fixed_restore_absorption losses.finalLoss
      outputLoss losses.final_lt_output with ⟨restoreAbsorption⟩
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := Real.rpow (10 : ℝ)
        (-1 / (losses.criticalLoss - losses.sourceADLoss)))
      (s := (1 : ℝ))
      (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num) with
    ⟨adDelta, adDeltaPos, adDeltaOne, adBound⟩
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := Real.rpow (40 : ℝ)
        (-1 / (losses.queryLoss - losses.criticalLoss)))
      (s := (1 : ℝ))
      (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num) with
    ⟨queryDelta, queryDeltaPos, queryDeltaOne, queryBound⟩
  let delta₀ := min losses.producer.delta₀ <|
    min reentryAbsorption.delta₀ <|
    min dyadicAbsorption.delta₀ <|
    min phase1Retention.delta₀ <|
    min densityAbsorption.delta₀ <|
    min phase1Threshold.delta₀ <|
    min multiplicityAbsorption.delta₀ <|
    min boundaryAbsorption.delta₀ <|
    min balancingAbsorption.delta₀ <|
    min restoreAbsorption.delta₀ <|
    min adDelta <| min queryDelta (Real.exp (-1))
  have delta₀Pos : 0 < delta₀ := by
    dsimp only [delta₀]
    exact lt_min losses.producer.delta₀_pos <|
      lt_min reentryAbsorption.delta₀_pos <|
      lt_min dyadicAbsorption.delta₀_pos <|
      lt_min phase1Retention.delta₀_pos <|
      lt_min densityAbsorption.delta₀_pos <|
      lt_min phase1Threshold.delta₀_pos <|
      lt_min multiplicityAbsorption.delta₀_pos <|
      lt_min boundaryAbsorption.delta₀_pos <|
      lt_min balancingAbsorption.delta₀_pos <|
      lt_min restoreAbsorption.delta₀_pos <|
      lt_min adDeltaPos <| lt_min queryDeltaPos (by positivity)
  refine ⟨{
    rootSourceLoss := losses.rootSourceLoss
    rootNormalizationLoss := losses.rootNormalizationLoss
    producerWindowLoss := losses.producerWindowLoss
    phase1StickyLoss := losses.phase1StickyLoss
    inputLoss := losses.inputLoss
    delta₀ := delta₀
    rootSourceLoss_pos := losses.rootSourceLoss_pos
    rootNormalizationLoss_pos := losses.rootNormalizationLoss_pos
    rootSourceLoss_le_half := losses.rootSourceLoss_le_half
    producerWindowLoss_pos := losses.producerWindowLoss_pos
    producerWindowLoss_le_sticky := losses.producerWindowLoss_le_sticky
    phase1StickyLoss_le_output := losses.phase1StickyLoss_le_output
    inputLoss_pos := losses.inputLoss_pos
    inputLoss_le_output := losses.inputLoss_le_output
    delta₀_pos := delta₀Pos
    delta₀_le_one := (min_le_left _ _).trans
      losses.producer.delta₀_le_one
    run := ?_
  }⟩
  intro delta deltaPos deltaLe ambientSourceLoss ambientNormalizationLoss
    ambientFamily ambientShading normalizationExponent ambientReentry ambientSourceLe
    ambientNormalizationLe current currentExtremal currentSub incidence
    currentMap coefficient currentLipschitz queryScale spatialScale
    variationScale queryPos querySmall queryGridFloor alignedLower phase1Lower
    alignedUpper periodicScale sqrtOne coefficientOne variationBudget
  have deltaProducer : delta ≤ losses.producer.delta₀ :=
    deltaLe.trans (min_le_left _ _)
  have deltaReentry : delta ≤ reentryAbsorption.delta₀ :=
    deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have deltaDyadic : delta ≤ dyadicAbsorption.delta₀ :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have deltaPhase1Retention : delta ≤ phase1Retention.delta₀ :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have deltaDensity : delta ≤ densityAbsorption.delta₀ :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have deltaPhase1 : delta ≤ phase1Threshold.delta₀ :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
  have deltaMultiplicity : delta ≤ multiplicityAbsorption.delta₀ :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
  have deltaBoundary : delta ≤ boundaryAbsorption.delta₀ :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_left _ _)
  have deltaBalancing : delta ≤ balancingAbsorption.delta₀ :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_left _ _)
  have deltaRestore : delta ≤ restoreAbsorption.delta₀ :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans <|
            (min_le_right _ _).trans <|
              (min_le_right _ _).trans (min_le_left _ _)
  have deltaAD : delta ≤ adDelta :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans <|
            (min_le_right _ _).trans <| (min_le_right _ _).trans <|
              (min_le_right _ _).trans (min_le_left _ _)
  have deltaQuery : delta ≤ queryDelta :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans <|
            (min_le_right _ _).trans <| (min_le_right _ _).trans <|
              (min_le_right _ _).trans <|
                (min_le_right _ _).trans (min_le_left _ _)
  have deltaStrict : delta < 1 :=
    deltaLe.trans_lt <| (min_le_right _ _).trans_lt <|
      (min_le_right _ _).trans_lt <| (min_le_right _ _).trans_lt <|
        (min_le_right _ _).trans_lt <| (min_le_right _ _).trans_lt <|
          (min_le_right _ _).trans_lt <| (min_le_right _ _).trans_lt <|
            (min_le_right _ _).trans_lt <| (min_le_right _ _).trans_lt <|
              (min_le_right _ _).trans_lt <|
                (min_le_right _ _).trans_lt <|
                  (min_le_right _ _).trans_lt
                    (Real.exp_lt_one_iff.mpr (by norm_num))
  exact proposition63_extremal_one_scale_full_grain_of_receipts losses
    reentryAbsorption dyadicAbsorption phase1Retention densityAbsorption
    phase1Threshold multiplicityAbsorption boundaryAbsorption
    balancingAbsorption restoreAbsorption deltaPos deltaStrict deltaProducer
    deltaReentry deltaDyadic deltaPhase1Retention deltaDensity deltaPhase1
    deltaMultiplicity deltaBoundary deltaBalancing deltaRestore
    (by simpa using adBound delta deltaPos deltaAD)
    (by simpa using queryBound delta deltaPos deltaQuery) ambientReentry
    ambientSourceLe ambientNormalizationLe current currentExtremal currentSub
    currentMap coefficient currentLipschitz queryScale spatialScale
    variationScale queryPos querySmall queryGridFloor alignedLower phase1Lower
    alignedUpper periodicScale sqrtOne coefficientOne variationBudget

/-- A finite schedule selected backwards from the requested final loss.
Runtime execution is forward: each coordinate consumes the actual family,
shading, map, and extremality returned by its predecessor. -/
structure Proposition63ExtremalFiniteFullGrainScheduleData
    (sigma outputLoss : ℝ) (N : ℕ) where
  rootSourceLoss : ℝ
  rootNormalizationLoss : ℝ
  inputLoss : ℝ
  loss : ℕ → ℝ
  producerWindowLoss : ℕ → ℝ
  phase1StickyLoss : ℕ → ℝ
  delta₀ : ℝ
  rootSourceLoss_pos : 0 < rootSourceLoss
  rootNormalizationLoss_pos : 0 < rootNormalizationLoss
  rootSourceLoss_le_half : rootSourceLoss ≤ rootNormalizationLoss / 2
  rootNormalizationLoss_le_output : rootNormalizationLoss ≤ outputLoss
  inputLoss_eq : inputLoss = loss 0
  finalLoss_eq : loss N = outputLoss
  inputLoss_pos : 0 < inputLoss
  inputLoss_le_output : inputLoss ≤ outputLoss
  loss_mono : ∀ index, loss index ≤ loss (index + 1)
  producerWindowLoss_pos : ∀ index, index < N → 0 < producerWindowLoss index
  producerWindowLoss_le_sticky : ∀ index, index < N →
    producerWindowLoss index ≤ phase1StickyLoss index
  phase1StickyLoss_le_output : ∀ index, index < N →
    phase1StickyLoss index ≤ loss (index + 1)
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  run : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    ∀ {ambientSourceLoss ambientNormalizationLoss : ℝ}
      {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
      {ambientShading : WZ1PaperTubeShading ambientFamily}
      {normalizationExponent : ℕ},
      ∀ (_ambientReentry : PureWZ2PropStickyReentryData
          (sigma := sigma) ambientShading normalizationExponent ambientSourceLoss
            ambientNormalizationLoss)
        (_ambientSource_le : ambientSourceLoss ≤ rootSourceLoss)
        (_ambientNormalization_le :
          ambientNormalizationLoss ≤ rootNormalizationLoss)
        (current : WZ1PaperTubeShading ambientFamily)
        (_currentExtremal : WZ2PaperCroppedIsExtremal
          sigma inputLoss ambientFamily current)
        (_currentSub : PaperIsSubshading current ambientShading)
        {incidence : ℝ}
        (currentMap : PaperWZ1WeakPlaneMapData current incidence)
        (coefficient : NNReal)
        (_currentLipschitz : LipschitzWith coefficient
          (fun point : {point : Point3 // point ∈ current.union} =>
            currentMap.planeMap point))
        (queryScale spatialScale variationScale : ℕ → ℝ),
        (query_pos : ∀ index, index < N → 0 < queryScale index) →
        (query_small : ∀ index, index < N → queryScale index ≤ 1 / 4) →
        (query_grid_floor : ∀ index, index < N →
          48 * delta ^ 2 ≤ queryScale index) →
        (aligned_lower : ∀ index, index < N →
          Real.rpow delta (1 - producerWindowLoss index) ≤
            alignedCoarseScale delta (queryScale index)) →
        (phase1_lower : ∀ index, index < N →
          Real.rpow delta (phase1StickyLoss index) ≤
            alignedCoarseScale delta (queryScale index)) →
        (aligned_upper : ∀ index, index < N →
          alignedCoarseScale delta (queryScale index) ≤
            Real.rpow delta (producerWindowLoss index)) →
        (periodic_scale : ∀ index, index < N →
          50 * delta ≤ Real.sqrt (queryScale index)) →
        (sqrt_one : ∀ index, index < N →
          Real.sqrt (queryScale index) ≤ 1) →
        1 ≤ (coefficient : ℝ) →
        (variation_budget : ∀ index, index < N →
          (coefficient : ℝ) * spatialScale index ≤ variationScale index) →
        Nonempty (Proposition63ExtremalFiniteFullGrainData
          (sigma := sigma) current currentMap loss N queryScale spatialScale
            variationScale)

private theorem proposition63_extremal_finite_full_grain_schedule_zero
    (sigma outputLoss : ℝ) (houtputLoss : 0 < outputLoss) :
    Nonempty (Proposition63ExtremalFiniteFullGrainScheduleData
      sigma outputLoss 0) := by
  let rootNormalizationLoss := outputLoss / 2
  let rootSourceLoss := rootNormalizationLoss / 4
  refine ⟨{
    rootSourceLoss := rootSourceLoss
    rootNormalizationLoss := rootNormalizationLoss
    inputLoss := outputLoss
    loss := fun _ => outputLoss
    producerWindowLoss := fun _ => outputLoss
    phase1StickyLoss := fun _ => outputLoss
    delta₀ := 1
    rootSourceLoss_pos := by
      dsimp only [rootSourceLoss, rootNormalizationLoss]
      positivity
    rootNormalizationLoss_pos := by
      dsimp only [rootNormalizationLoss]
      positivity
    rootSourceLoss_le_half := by
      dsimp only [rootSourceLoss, rootNormalizationLoss]
      linarith
    rootNormalizationLoss_le_output := by
      dsimp only [rootNormalizationLoss]
      linarith
    inputLoss_eq := rfl
    finalLoss_eq := rfl
    inputLoss_pos := houtputLoss
    inputLoss_le_output := le_rfl
    loss_mono := fun _ => le_rfl
    producerWindowLoss_pos := by intro index indexLt; omega
    producerWindowLoss_le_sticky := by intro index indexLt; omega
    phase1StickyLoss_le_output := by intro index indexLt; omega
    delta₀_pos := by norm_num
    delta₀_le_one := le_rfl
    run := ?_
  }⟩
  intro delta deltaPos deltaLe ambientSourceLoss ambientNormalizationLoss
    ambientFamily ambientShading normalizationExponent ambientReentry ambientSourceLe
    ambientNormalizationLe current currentExtremal currentSub incidence
    currentMap coefficient currentLipschitz queryScale spatialScale
    variationScale queryPos querySmall queryGridFloor alignedLower phase1Lower
    alignedUpper periodicScale sqrtOne coefficientOne variationBudget
  exact proposition63_extremal_finite_full_grain currentMap
    (fun _ => outputLoss) (fun _ => le_rfl) currentExtremal 0 queryScale
    spatialScale variationScale (by intro index indexLt; omega)

/-- Fold any canonical one-scale producer backwards through a finite number
of coordinates.  The resulting input loss and common `delta₀` precede all
runtime objects, while execution calls each chosen one-scale schedule only on
the actual restored output of the previous coordinate. -/
theorem proposition63_extremal_finite_full_grain_schedule
    (sigma : ℝ)
    (oneScale : ∀ outputLoss : ℝ, 0 < outputLoss →
      Nonempty (Proposition63ExtremalOneScaleFullGrainScheduleData
        sigma outputLoss))
    (outputLoss : ℝ) (houtputLoss : 0 < outputLoss) :
    ∀ N : ℕ, Nonempty (Proposition63ExtremalFiniteFullGrainScheduleData
      sigma outputLoss N) := by
  intro N
  induction N with
  | zero =>
      exact proposition63_extremal_finite_full_grain_schedule_zero
        sigma outputLoss houtputLoss
  | succ N inductionHypothesis =>
      rcases inductionHypothesis with ⟨tail⟩
      rcases oneScale tail.inputLoss tail.inputLoss_pos with ⟨head⟩
      let common : ℝ := min head.rootSourceLoss <|
        min head.rootNormalizationLoss <|
          min tail.rootSourceLoss tail.rootNormalizationLoss
      let rootNormalizationLoss : ℝ := common
      let rootSourceLoss : ℝ := common / 4
      let loss : ℕ → ℝ := fun index =>
        if index = 0 then head.inputLoss else tail.loss (index - 1)
      let producerWindowLoss : ℕ → ℝ := fun index =>
        if index = 0 then head.producerWindowLoss
        else tail.producerWindowLoss (index - 1)
      let phase1StickyLoss : ℕ → ℝ := fun index =>
        if index = 0 then head.phase1StickyLoss
        else tail.phase1StickyLoss (index - 1)
      let delta₀ := min head.delta₀ tail.delta₀
      have commonPos : 0 < common := by
        dsimp only [common]
        exact lt_min head.rootSourceLoss_pos <|
          lt_min head.rootNormalizationLoss_pos <|
            lt_min tail.rootSourceLoss_pos tail.rootNormalizationLoss_pos
      have lossZero : loss 0 = head.inputLoss := by simp [loss]
      have lossSucc : ∀ index, loss (index + 1) = tail.loss index := by
        intro index
        simp [loss]
      have producerWindowZero :
          producerWindowLoss 0 = head.producerWindowLoss := by
        simp [producerWindowLoss]
      have producerWindowSucc : ∀ index,
          producerWindowLoss (index + 1) = tail.producerWindowLoss index := by
        intro index
        simp [producerWindowLoss]
      have phase1StickyZero :
          phase1StickyLoss 0 = head.phase1StickyLoss := by
        simp [phase1StickyLoss]
      have phase1StickySucc : ∀ index,
          phase1StickyLoss (index + 1) = tail.phase1StickyLoss index := by
        intro index
        simp [phase1StickyLoss]
      refine ⟨{
        rootSourceLoss := rootSourceLoss
        rootNormalizationLoss := rootNormalizationLoss
        inputLoss := head.inputLoss
        loss := loss
        producerWindowLoss := producerWindowLoss
        phase1StickyLoss := phase1StickyLoss
        delta₀ := delta₀
        rootSourceLoss_pos := by
          dsimp only [rootSourceLoss]
          positivity
        rootNormalizationLoss_pos := by
          dsimp only [rootNormalizationLoss]
          exact commonPos
        rootSourceLoss_le_half := by
          dsimp only [rootSourceLoss, rootNormalizationLoss]
          linarith [commonPos]
        rootNormalizationLoss_le_output := by
          dsimp only [rootNormalizationLoss, common]
          exact (((min_le_right _ _).trans <|
            (min_le_right _ _)).trans <|
              (min_le_right _ _)).trans
                tail.rootNormalizationLoss_le_output
        inputLoss_eq := lossZero.symm
        finalLoss_eq := by
          rw [lossSucc]
          exact tail.finalLoss_eq
        inputLoss_pos := head.inputLoss_pos
        inputLoss_le_output :=
          head.inputLoss_le_output.trans tail.inputLoss_le_output
        loss_mono := ?_
        producerWindowLoss_pos := ?_
        producerWindowLoss_le_sticky := ?_
        phase1StickyLoss_le_output := ?_
        delta₀_pos := lt_min head.delta₀_pos tail.delta₀_pos
        delta₀_le_one := (min_le_left _ _).trans head.delta₀_le_one
        run := ?_
      }⟩
      · intro index
        by_cases indexZero : index = 0
        · subst index
          rw [lossZero, lossSucc]
          rw [← tail.inputLoss_eq]
          exact head.inputLoss_le_output
        · have lossIndex : loss index = tail.loss (index - 1) := by
            simp [loss, indexZero]
          have lossNext : loss (index + 1) = tail.loss index := by
            exact lossSucc index
          rw [lossIndex, lossNext]
          simpa only [show (index - 1) + 1 = index by omega] using
            tail.loss_mono (index - 1)
      · intro index indexLt
        by_cases indexZero : index = 0
        · subst index
          rw [producerWindowZero]
          exact head.producerWindowLoss_pos
        · rw [show index = (index - 1) + 1 by omega, producerWindowSucc]
          exact tail.producerWindowLoss_pos (index - 1) (by omega)
      · intro index indexLt
        by_cases indexZero : index = 0
        · subst index
          rw [producerWindowZero, phase1StickyZero]
          exact head.producerWindowLoss_le_sticky
        · rw [show index = (index - 1) + 1 by omega, producerWindowSucc,
            phase1StickySucc]
          exact tail.producerWindowLoss_le_sticky (index - 1) (by omega)
      · intro index indexLt
        by_cases indexZero : index = 0
        · subst index
          rw [phase1StickyZero, lossSucc, ← tail.inputLoss_eq]
          exact head.phase1StickyLoss_le_output
        · rw [show index = (index - 1) + 1 by omega, phase1StickySucc,
            lossSucc]
          simpa only [show index - 1 + 1 = index by omega] using
            tail.phase1StickyLoss_le_output (index - 1) (by omega)
      · intro delta deltaPos deltaLe ambientSourceLoss
          ambientNormalizationLoss ambientFamily ambientShading
          normalizationExponent ambientReentry
          ambientSourceLe ambientNormalizationLe current currentExtremal
          currentSub incidence currentMap coefficient currentLipschitz
          queryScale spatialScale
          variationScale queryPos querySmall queryGridFloor alignedLower
          phase1Lower alignedUpper periodicScale sqrtOne coefficientOne
          variationBudget
        have deltaHead : delta ≤ head.delta₀ :=
          deltaLe.trans (min_le_left _ _)
        have deltaTail : delta ≤ tail.delta₀ :=
          deltaLe.trans (min_le_right _ _)
        have sourceLeHead : ambientSourceLoss ≤ head.rootSourceLoss :=
          ambientSourceLe.trans <| by
            dsimp only [rootSourceLoss, rootNormalizationLoss, common]
            exact (div_le_self commonPos.le (by norm_num)).trans <|
              min_le_left _ _
        have normalizationLeHead :
            ambientNormalizationLoss ≤ head.rootNormalizationLoss :=
          ambientNormalizationLe.trans <| by
            dsimp only [rootNormalizationLoss, common]
            exact (min_le_right _ _).trans (min_le_left _ _)
        have sourceLeTail : ambientSourceLoss ≤ tail.rootSourceLoss :=
          ambientSourceLe.trans <| by
            dsimp only [rootSourceLoss, rootNormalizationLoss, common]
            apply (div_le_self commonPos.le (by norm_num)).trans
            exact (min_le_right _ _).trans <|
              (min_le_right _ _).trans (min_le_left _ _)
        have normalizationLeTail :
            ambientNormalizationLoss ≤ tail.rootNormalizationLoss :=
          ambientNormalizationLe.trans <| by
            dsimp only [rootNormalizationLoss, common]
            exact (min_le_right _ _).trans <|
              (min_le_right _ _).trans (min_le_right _ _)
        have currentAtHead : WZ2PaperCroppedIsExtremal
            sigma head.inputLoss ambientFamily current := by
          simpa only [← lossZero] using currentExtremal
        rcases head.run deltaPos deltaHead ambientReentry sourceLeHead
            normalizationLeHead current currentAtHead currentSub currentMap
            coefficient
            currentLipschitz (queryScale 0) (spatialScale 0)
            (variationScale 0) (queryPos 0 (by omega))
            (querySmall 0 (by omega)) (queryGridFloor 0 (by omega))
            (by simpa only [producerWindowZero] using
              alignedLower 0 (by omega))
            (by simpa only [phase1StickyZero] using
              phase1Lower 0 (by omega))
            (by simpa only [producerWindowZero] using
              alignedUpper 0 (by omega))
            (periodicScale 0 (by omega)) (sqrtOne 0 (by omega))
            coefficientOne (variationBudget 0 (by omega)) with ⟨first⟩
        have firstAtTail : WZ2PaperCroppedIsExtremal
            sigma tail.inputLoss ambientFamily first.shading := by
          simpa only [lossSucc] using first.extremal
        have firstSubAmbient : PaperIsSubshading first.shading
            ambientShading := fun tube point pointMem =>
          currentSub tube (first.subshading tube pointMem)
        have firstLipschitz : LipschitzWith coefficient
            (fun point : {point : Point3 // point ∈ first.shading.union} =>
              first.planeMap.planeMap point) := by
          intro firstPoint secondPoint
          have firstCurrent : (firstPoint : Point3) ∈ current.union := by
            rcases firstPoint.prop with ⟨tube, tubeMem⟩
            exact ⟨tube, first.subshading tube tubeMem⟩
          have secondCurrent : (secondPoint : Point3) ∈ current.union := by
            rcases secondPoint.prop with ⟨tube, tubeMem⟩
            exact ⟨tube, first.subshading tube tubeMem⟩
          change edist (first.planeMap.planeMap firstPoint)
            (first.planeMap.planeMap secondPoint) ≤
              coefficient * edist firstPoint secondPoint
          rw [first.same_plane_map]
          exact currentLipschitz
            ⟨firstPoint, firstCurrent⟩ ⟨secondPoint, secondCurrent⟩
        let tailQuery : ℕ → ℝ := fun index => queryScale (index + 1)
        let tailSpatial : ℕ → ℝ := fun index => spatialScale (index + 1)
        let tailVariation : ℕ → ℝ := fun index => variationScale (index + 1)
        rcases tail.run deltaPos deltaTail ambientReentry sourceLeTail
            normalizationLeTail first.shading firstAtTail firstSubAmbient
            first.planeMap coefficient firstLipschitz tailQuery tailSpatial
            tailVariation
            (fun index indexLt => queryPos (index + 1) (by omega))
            (fun index indexLt => querySmall (index + 1) (by omega))
            (fun index indexLt => queryGridFloor (index + 1) (by omega))
            (fun index indexLt => by
              have raw := alignedLower (index + 1) (by omega)
              change Real.rpow delta
                  (1 - tail.producerWindowLoss index) ≤
                alignedCoarseScale delta (queryScale (index + 1))
              simpa only [producerWindowSucc] using raw)
            (fun index indexLt => by
              have raw := phase1Lower (index + 1) (by omega)
              change Real.rpow delta
                  (tail.phase1StickyLoss index) ≤
                alignedCoarseScale delta (queryScale (index + 1))
              simpa only [phase1StickySucc] using raw)
            (fun index indexLt => by
              have raw := alignedUpper (index + 1) (by omega)
              change alignedCoarseScale delta (queryScale (index + 1)) ≤
                Real.rpow delta (tail.producerWindowLoss index)
              simpa only [producerWindowSucc] using raw)
            (fun index indexLt => periodicScale (index + 1) (by omega))
            (fun index indexLt => sqrtOne (index + 1) (by omega))
            coefficientOne
            (fun index indexLt => variationBudget (index + 1) (by omega)) with
          ⟨final⟩
        -- Reassemble the head and already-run tail.  This avoids replaying
        -- any runtime choice while preserving the exact loss chain.
        let massLoss := first.massLoss * final.massLoss
        have massLossPos : 0 < massLoss :=
          ENNReal.mul_pos first.massLoss_pos.ne' final.massLoss_pos.ne'
        have massLossTop : massLoss ≠ ⊤ :=
          ENNReal.mul_ne_top first.massLoss_ne_top final.massLoss_ne_top
        have massRetention : massLoss⁻¹ * current.mass ≤ final.shading.mass := by
          rw [ENNReal.mul_inv (Or.inl first.massLoss_pos.ne')
            (Or.inl first.massLoss_ne_top)]
          calc
            (first.massLoss⁻¹ * final.massLoss⁻¹) * current.mass =
                final.massLoss⁻¹ * (first.massLoss⁻¹ * current.mass) := by ring
            _ ≤ final.massLoss⁻¹ * first.shading.mass := by
              exact mul_le_mul_right first.mass_retention _
            _ ≤ final.shading.mass := final.mass_retention
        refine ⟨{
          shading := final.shading
          subshading := fun tube point pointMem =>
            first.subshading tube (final.subshading tube pointMem)
          cubical := final.cubical
          planeMap := final.planeMap
          same_plane_map := final.same_plane_map.trans first.same_plane_map
          variation := ?_
          local_ad := ?_
          massLoss := massLoss
          massLoss_pos := massLossPos
          massLoss_ne_top := massLossTop
          mass_retention := massRetention
          extremal := by simpa only [tail.finalLoss_eq, lossSucc] using
            final.extremal
        }⟩
        · intro index indexLt firstPoint firstMem secondPoint secondMem distance
          by_cases indexZero : index = 0
          · subst index
            have firstInHead : firstPoint ∈ first.shading.union := by
              rcases firstMem with ⟨tube, tubeMem⟩
              exact ⟨tube, final.subshading tube tubeMem⟩
            have secondInHead : secondPoint ∈ first.shading.union := by
              rcases secondMem with ⟨tube, tubeMem⟩
              exact ⟨tube, final.subshading tube tubeMem⟩
            rw [final.same_plane_map]
            exact first.variation firstPoint firstInHead secondPoint
              secondInHead distance
          · have indexPos : 0 < index := Nat.pos_of_ne_zero indexZero
            let tailIndex := index - 1
            have tailIndexLt : tailIndex < N := by omega
            have indexEq : index = tailIndex + 1 := by omega
            have distanceTail : dist firstPoint secondPoint ≤
                tailSpatial tailIndex := by
              dsimp only [tailSpatial]
              rwa [← indexEq]
            have result := final.variation tailIndex tailIndexLt firstPoint
              firstMem secondPoint secondMem distanceTail
            dsimp only [tailVariation] at result
            rwa [← indexEq] at result
        · intro index indexLt point pointMem
          by_cases indexZero : index = 0
          · subst index
            have pointInHead : point ∈ first.shading.union := by
              rcases pointMem with ⟨tube, tubeMem⟩
              exact ⟨tube, final.subshading tube tubeMem⟩
            rw [final.same_plane_map]
            have hset :
                scalarProjection (first.planeMap.planeMap point)
                    (final.shading.union ∩ Metric.closedBall point
                      (Real.sqrt (queryScale 0))) ⊆
                  scalarProjection (first.planeMap.planeMap point)
                    (first.shading.union ∩ Metric.closedBall point
                      (Real.sqrt (queryScale 0))) := by
              rintro value ⟨other, hother, rfl⟩
              have otherInHead : other ∈ first.shading.union := by
                rcases hother.1 with ⟨tube, tubeMem⟩
                exact ⟨tube, final.subshading tube tubeMem⟩
              exact ⟨other, ⟨otherInHead, hother.2⟩, rfl⟩
            have firstAD := (first.local_ad point pointInHead).mono hset
            have headFinalConstant : Kakeya.realRpowENN delta
                (-tail.inputLoss) ≤
                Kakeya.realRpowENN delta (-outputLoss) := by
              apply ENNReal.ofReal_mono
              exact Real.rpow_le_rpow_of_exponent_ge deltaPos
                (deltaTail.trans tail.delta₀_le_one)
                (by linarith [tail.inputLoss_le_output])
            have firstADFinal := firstAD.mono_constant headFinalConstant
            have lossFinal : loss (N + 1) = outputLoss :=
              (lossSucc N).trans tail.finalLoss_eq
            simpa only [lossFinal] using firstADFinal
          · have indexPos : 0 < index := Nat.pos_of_ne_zero indexZero
            let tailIndex := index - 1
            have tailIndexLt : tailIndex < N := by omega
            simpa only [tailQuery, show index = tailIndex + 1 by omega,
              lossSucc] using final.local_ad tailIndex tailIndexLt point pointMem

/-- Concrete finite Lemma 4.12 schedule obtained by selecting the full
one-scale hierarchy backwards and executing its restored outputs forwards. -/
theorem proposition63_extremal_finite_full_grain_concrete_schedule
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ) (houtputLoss : 0 < outputLoss) :
    ∀ N : ℕ, Nonempty (Proposition63ExtremalFiniteFullGrainScheduleData
      sigma outputLoss N) := by
  exact proposition63_extremal_finite_full_grain_schedule sigma
    (fun oneScaleOutput oneScaleOutputPos =>
      proposition63_extremal_one_scale_full_grain_schedule sigma critical
        oneScaleOutput oneScaleOutputPos) outputLoss houtputLoss

end Kakeya.Assouad.PureWZ2

end
