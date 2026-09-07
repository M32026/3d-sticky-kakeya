import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperFinalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PaperLineHitCandidate
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperCoarseAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PaperTerminalPullbackAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PaperCoarseToFineLift
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63StagedCandidateHull
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63StagedPullbackCandidate
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallOrderedPair

/-!
# One paper-ordered Proposition 6.3 pair

This is the M5 consumer for the paper-ordered four-call runtime.  The final
candidate is restored locally on the fourth-call family and then lifted
through the two existing re-entries, the call-one terminal whole-cell
pullback, and the final current re-entry.  The raw M4 ancestry ledger remains
available for the iterator mass inequality, but it is not used to restore
extremality.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

attribute [local instance] Classical.propDecidable

/-- The paper all-line ledger differs from the separated-line ledger by the
same finite positive scalar on both sides. -/
noncomputable def proposition63FourCallPaperMassScale (rho : ℝ) : ENNReal :=
  32 * ENNReal.ofReal rho

private theorem proposition63_four_call_paper_scaled_line_factor
    {rho floor : ℝ} (rho_pos : 0 < rho) :
    proposition63FourCallPaperMassScale rho *
        ENNReal.ofReal ((floor / 2) / (4 * (2 * Real.sqrt rho) ^ 2)) =
      ENNReal.ofReal floor := by
  unfold proposition63FourCallPaperMassScale
  rw [show (2 * Real.sqrt rho) ^ 2 = 4 * rho by
    rw [mul_pow, Real.sq_sqrt rho_pos.le]
    ring]
  rw [← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (32 : ℝ) * rho)]
  apply congrArg ENNReal.ofReal
  field_simp
  ring

private theorem proposition63_four_call_paper_scaled_line_cover_le
    {rho floor : ℝ} {coverBudget : ℕ} {cellMass : ENNReal}
    (rho_pos : 0 < rho)
    (cell_lower : ENNReal.ofReal floor ≤ cellMass) :
    proposition63FourCallPaperMassScale rho *
        (ENNReal.ofReal ((floor / 2) / (4 * (2 * Real.sqrt rho) ^ 2)) *
          (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal)))) ≤
      (cellMass / 2) / (2 * (coverBudget : ENNReal)) := by
  calc
    proposition63FourCallPaperMassScale rho *
          (ENNReal.ofReal ((floor / 2) /
              (4 * (2 * Real.sqrt rho) ^ 2)) *
            (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal)))) =
        (proposition63FourCallPaperMassScale rho *
          ENNReal.ofReal ((floor / 2) /
            (4 * (2 * Real.sqrt rho) ^ 2))) *
          (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) := by ring
    _ = ENNReal.ofReal floor *
          (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) := by
      rw [proposition63_four_call_paper_scaled_line_factor rho_pos]
    _ ≤ cellMass *
          (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) :=
      mul_le_mul_right' cell_lower _
    _ = (cellMass / 2) / (2 * (coverBudget : ENNReal)) := by
      simp only [div_eq_mul_inv]
      ac_rfl

private theorem proposition63_four_call_paper_scaled_chain_le
    {scale oldBase newBase first second third fourth : ENNReal}
    (scaled_base : scale * oldBase ≤ newBase) :
    scale * (oldBase * first * second * third * fourth) ≤
      newBase * first * second * third * fourth := by
  calc
    scale * (oldBase * first * second * third * fourth) =
        (scale * oldBase) * (first * second * third * fourth) := by ring
    _ ≤ newBase * (first * second * third * fourth) :=
      mul_le_mul_right' scaled_base _
    _ = newBase * first * second * third * fourth := by ring

private theorem proposition63_four_call_paper_scaled_geometric
    {rho : ℝ} (rho_pos : 0 < rho) :
    4 * (ENNReal.ofReal (4 * (2 * Real.sqrt rho) ^ 2) *
        ENNReal.ofReal (4 * rho)) =
      proposition63FourCallPaperMassScale rho *
        (2 * ENNReal.ofReal (4 * rho)) := by
  unfold proposition63FourCallPaperMassScale
  rw [show 4 * (2 * Real.sqrt rho) ^ 2 = 16 * rho by
    rw [mul_pow, Real.sq_sqrt rho_pos.le]
    ring]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num
  ring

private theorem proposition63_four_call_paper_scaled_right_product
    {scale loss oldGeometric newGeometric fineLoss : ENNReal}
    (geometric_eq : newGeometric = scale * oldGeometric) :
    (loss * newGeometric) * fineLoss =
      scale * ((loss * oldGeometric) * fineLoss) := by
  rw [geometric_eq]
  ring

/-- Recover the first point-cover constant from a nested runtime without
unfolding its frozen scale choices. -/
def proposition63PaperTauConstant
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    (_data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant) : ENNReal :=
  tauConstant

namespace Proposition63NestedPointCoverData.FullGrainCells

variable
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

/-- The all-good-line region uses the same literal grid as the historical
finite selection, hence the same fixed local cell count. -/
theorem paperRelevantCells_card_le_fixed
    (full : data.FullGrainCells lineVolume coverBudget)
    (hquery : 0 < queryScale)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale) :
    ∀ center,
      (full.paperRelevantCells center (2 * Real.sqrt queryScale)).card ≤
        13 ^ 3 := by
  intro center
  have hsqrtPos : 0 < sqrtScale := by
    rw [hsqrtScale]
    exact Real.sqrt_pos.mpr hquery
  have hbound := gridCellsIntersecting_ball_bound
    (mul_pos hsqrtPos (Real.sqrt_pos.mpr (by norm_num))) center
    (show 2 * Real.sqrt queryScale ≤
        3 * (sqrtScale * Real.sqrt 3) by
      rw [hsqrtScale]
      have hsqrtThree : 1 ≤ Real.sqrt 3 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
          Real.sqrt_nonneg 3]
      nlinarith [Real.sqrt_nonneg queryScale])
  have hsubset :
      (↑(full.paperRelevantCells center (2 * Real.sqrt queryScale)) :
          Set (ℤ × ℤ × ℤ)) ⊆
        gridCellsIntersecting (sqrtScale * Real.sqrt 3)
          (Metric.closedBall center (2 * Real.sqrt queryScale)) := by
    intro cell hcell
    rcases Finset.mem_filter.mp hcell with ⟨hactive, hnonempty⟩
    simp only [hactive, dite_true] at hnonempty
    rcases hnonempty with ⟨point, hpointRegion, hpointBall⟩
    refine ⟨point, ?_, hpointBall⟩
    rw [gridCell_sqrtThree_eq_paperGridCube]
    exact full.paperCellRegion_subset_cell ⟨cell, hactive⟩ hpointRegion
  have hncard := Set.ncard_le_ncard hsubset hbound.1
  simpa using hncard.trans hbound.2

/-- Centered normal variation for an arbitrary point in an all-good-line
cell.  No runtime or schedule data enters this estimate. -/
theorem paperCandidate_centered_error
    (full : data.FullGrainCells lineVolume coverBudget)
    (hquery : 0 < queryScale)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (coefficient : NNReal)
    (hplaneLipschitz : LipschitzWith coefficient planeMap) :
    ∀ center cell, ∀ hcellRelevant :
      cell ∈ full.paperRelevantCells center (2 * Real.sqrt queryScale),
      ∀ point ∈ full.paperCellRegion
          ⟨cell, (Finset.mem_filter.mp hcellRelevant).1⟩ ∩
          Metric.closedBall center (2 * Real.sqrt queryScale),
        dist (inner ℝ (point - center) (planeMap center))
          (inner ℝ (point - center)
            (planeMap (data.cells.cellRep cell
              ((Finset.mem_filter.mp hcellRelevant).1)))) ≤
          8 * (coefficient : ℝ) * queryScale := by
  intro center cell hcellRelevant point hpoint
  have hactive := (Finset.mem_filter.mp hcellRelevant).1
  have hsqrtPos : 0 < sqrtScale := by
    rw [hsqrtScale]
    exact Real.sqrt_pos.mpr hquery
  have hpointCell : point ∈ wz1PaperGridCube sqrtScale cell :=
    full.paperCellRegion_subset_cell ⟨cell, hactive⟩ hpoint.1
  have hpointRep : dist point (data.cells.cellRep cell hactive) ≤
      sqrtScale * Real.sqrt 3 :=
    wz1PaperGridCube_diameter hsqrtPos cell hpointCell
      (data.cells.cellRep_in_cell cell hactive)
  have hpointCenter := Metric.mem_closedBall.mp hpoint.2
  have hsqrtThree : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg 3]
  have hcenterRep : dist center (data.cells.cellRep cell hactive) ≤
      4 * Real.sqrt queryScale := by
    calc
      dist center (data.cells.cellRep cell hactive) ≤
          dist center point + dist point (data.cells.cellRep cell hactive) :=
        dist_triangle _ _ _
      _ ≤ 2 * Real.sqrt queryScale + sqrtScale * Real.sqrt 3 := by
        gcongr
        simpa [dist_comm] using hpointCenter
      _ ≤ 4 * Real.sqrt queryScale := by
        rw [hsqrtScale]
        have hsqrtNonneg := Real.sqrt_nonneg queryScale
        nlinarith
  have hnormalDistance :
      dist (planeMap center) (planeMap (data.cells.cellRep cell hactive)) ≤
        4 * (coefficient : ℝ) * Real.sqrt queryScale :=
    (hplaneLipschitz.dist_le_mul center _).trans (by
      calc
        (coefficient : ℝ) * dist center (data.cells.cellRep cell hactive) ≤
            (coefficient : ℝ) * (4 * Real.sqrt queryScale) :=
          mul_le_mul_of_nonneg_left hcenterRep coefficient.coe_nonneg
        _ = 4 * (coefficient : ℝ) * Real.sqrt queryScale := by ring)
  rw [Real.dist_eq]
  have hidentity :
      inner ℝ (point - center) (planeMap center) -
          inner ℝ (point - center) (planeMap (data.cells.cellRep cell hactive)) =
        inner ℝ (point - center)
          (planeMap center - planeMap (data.cells.cellRep cell hactive)) := by
    rw [inner_sub_right]
  rw [hidentity]
  calc
    |inner ℝ (point - center)
        (planeMap center - planeMap (data.cells.cellRep cell hactive))| ≤
      ‖point - center‖ *
        ‖planeMap center - planeMap (data.cells.cellRep cell hactive)‖ :=
      abs_real_inner_le_norm _ _
    _ = dist point center *
        dist (planeMap center) (planeMap (data.cells.cellRep cell hactive)) := by
      rw [dist_eq_norm, dist_eq_norm]
    _ ≤ (2 * Real.sqrt queryScale) *
        (4 * (coefficient : ℝ) * Real.sqrt queryScale) := by
      exact mul_le_mul hpointCenter hnormalDistance dist_nonneg (by positivity)
    _ = 8 * (coefficient : ℝ) * queryScale := by
      calc
        (2 * Real.sqrt queryScale) *
            (4 * (coefficient : ℝ) * Real.sqrt queryScale) =
          8 * (coefficient : ℝ) *
            (Real.sqrt queryScale * Real.sqrt queryScale) := by ring
        _ = 8 * (coefficient : ℝ) * queryScale := by
          rw [Real.mul_self_sqrt hquery.le]

end Proposition63NestedPointCoverData.FullGrainCells

/-- Runtime-specialized coarse-A restoration.  This wrapper keeps the large
paper-runtime abbreviation out of the final ordered-pair elaboration. -/
theorem proposition63_four_call_runtime_paperCandidate_extremal
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    {K : ℝ}
    {backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length}
    {root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {leftFactor rightFactor : ℕ → ENNReal}
    {sourceCoefficient : NNReal}
    {global : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient}
    {index : ℕ}
    (hindex : index < (finiteIntervalOrderedPairs gridN).length)
    {scales : Proposition63FourCallOrderedPairIndexScales grid index}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading family}
    {fineReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) fineShading normalizationExponent
      (backward.seed index hindex).schedule.first.sourceLoss
      (backward.seed index hindex).schedule.first.normalizationLoss}
    {rootAxialWindow : ∀ sourceIndex point,
      point ∈ fineReentry.geometry.frame ''
          fineReentry.geometry.ordinaryRefined.carrier sourceIndex →
        |point (2 : Fin 3)| ≤ 1 / 8}
    {sourceMap : PaperWZ1WeakPlaneMapData fineShading incidence}
    {extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient}
    (runtime : Proposition63FourCallPaperRuntimeAssemblyData
      (fineShading := fineShading) (fineReentry := fineReentry)
      (rootAxialWindow := rootAxialWindow) (extension := extension) K backward
      root grid leftFactor rightFactor sourceCoefficient global index hindex
      scales)
    (paperCutoff : Proposition63FourCallPaperSeedCutoffData
      (backward.seed index hindex)
      ((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)))
    (hrhoCutoff : scales.rhoHat.1 ≤ paperCutoff.rhoCutoff)
    {lineVolume : ℝ} {coverBudget : ℕ}
    (full : runtime.paperNested.nested.FullGrainCells lineVolume coverBudget)
    (rho_pos : 0 < scales.rhoHat.1)
    (rho_le_one : scales.rhoHat.1 ≤ 1)
    (coverBudget_pos : 0 < coverBudget)
    (hincidenceRho : incidence ≤ scales.rhoHat.1)
    (hcoverUpper : (coverBudget : ENNReal) ≤
      (1605264998400 : ENNReal) *
        (((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ENNReal) ^ 3 *
        Kakeya.realRpowENN scales.rhoHat.1
          (-(proposition63FourCallPaperFinalExponent sigma
            (backward.seed index hindex).schedule.fourth.normalizationLoss
            (backward.seed index hindex).fourthKernel.internalLoss
            (backward.seed index hindex).epsilon₁
            (backward.seed index hindex).paperAngularExponent)) + 2)
    {constant : ENNReal}
    (covering : PureWZ2IntervalCoveringAt (full.paperCandidate rho_pos)
      runtime.currentResult.currentMap.planeMap scales.rhoHat.1
      (Real.toNNReal scales.rhoHat.1) (Real.toNNReal scales.tau) constant) :
    WZ2PaperCroppedIsExtremal sigma
      (backward.seed index hindex).paperCandidateLoss
      runtime.paperNested.nested.reentry.normalization.croppedFamily
      (full.paperCandidate rho_pos) := by
  let seed := backward.seed index hindex
  change WZ2PaperCroppedIsExtremal sigma seed.paperCandidateLoss
    runtime.paperNested.nested.reentry.normalization.croppedFamily
    (full.paperCandidate rho_pos)
  apply Proposition63NestedPointCoverData.FullGrainCells.paperCandidate_extremal_of_exact_choices
      (outputLoss := backward.loss (index + 1))
      (discreteLoss := discreteLoss)
      (seed := seed)
      (coefficient := (4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient))
      (coverBudget := coverBudget) (data := runtime.paperNested.nested)
      (full := full)
      (absorption := paperCutoff.coarseAbsorption)
      (rho_le_absorption :=
        hrhoCutoff.trans paperCutoff.rhoCutoff_le_coarseAbsorption)
      (critical := seed.critical)
      (rho_le_critical :=
        hrhoCutoff.trans <| paperCutoff.rhoCutoff_le_legacy.trans
          paperCutoff.legacy.rhoCutoff_le_critical)
      (final_le_structural := seed.finalLoss_le_structural)
      (traceAbsorption := seed.traceAbsorption.absorb scales.rhoHat.1
        rho_pos <|
          hrhoCutoff.trans <| paperCutoff.rhoCutoff_le_legacy.trans
            paperCutoff.legacy.rhoCutoff_le_traceAbsorption)
      (floor_nonneg := seed.floorLoss_pos.le)
      (coverBudget_pos := coverBudget_pos)
      (cover_upper := by
        rw [ENNReal.coe_mul, ENNReal.coe_mul]
        simpa only [seed] using hcoverUpper)
      (candidate_pos := by
        rw [seed.paperCandidateLoss_eq]
        have hout := backward.loss_pos (index + 1) (by omega)
        positivity)
      (rho_pos := rho_pos) (rho_le_one := rho_le_one)
      (constant := constant)
      (covering := by exact covering)


/-- Convert one paper runtime into the exact callback result for its ordered
pair.  The mass receipt keeps the preselected separated-line factors used by
the finite iterator.  Inside the proof both sides are multiplied by the same
positive factor `32 * rho`; the critical cell-mass lower bound then embeds the
separated-line ledger into the all-good-line paper ledger without changing the
one-step mass-loss ratio. -/
theorem proposition63_four_call_paper_ordered_pair
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale fineInputLoss fineNormalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    {K : ℝ}
    {backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length}
    {root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {leftFactor rightFactor : ℕ → ENNReal}
    {paperLeftFactor paperRightFactor : ℕ → ENNReal}
    {sourceCoefficient : NNReal}
    {global : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient}
    {index : ℕ}
    (hindex : index < (finiteIntervalOrderedPairs gridN).length)
    {scales : Proposition63FourCallOrderedPairIndexScales grid index}
    {fineSource : PureWZ2ExtremalConfiguration sigma fineInputLoss delta}
    {fineNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := fineNormalizationLoss) fineSource normalizationExponent}
    {fineCurrent : WZ1PaperTubeShading fineNormalized.croppedFamily}
    (fineCurrentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := (backward.seed index hindex).schedule.first.sourceLoss)
      fineNormalized fineCurrent)
    (hfineWeight : fineCurrentReentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta
        (backward.currentWeightLoss index hindex))
    (hfineWeightUpper : fineCurrentReentry.weightUpper =
      (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2)
    (hfineLevel : fineCurrentReentry.levelCount =
      proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss)
    (hnormalization : fineCurrentReentry.reentryNormalizationLoss =
      (backward.seed index hindex).schedule.first.normalizationLoss)
    {rootAxialWindow : ∀ sourceIndex point,
      point ∈ (fineCurrentReentry.paperPropStickyReentry
          (backward.seed index hindex).schedule.first.sourceLoss_pos
          hnormalization).geometry.frame ''
          (fineCurrentReentry.paperPropStickyReentry
            (backward.seed index hindex).schedule.first.sourceLoss_pos
            hnormalization).geometry.ordinaryRefined.carrier sourceIndex →
        |point (2 : Fin 3)| ≤ 1 / 8}
    {sourceMap : PaperWZ1WeakPlaneMapData
      fineCurrentReentry.normalization.croppedRefined incidence}
    {extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient}
    (runtime : Proposition63FourCallPaperRuntimeAssemblyData
      (fineShading := fineCurrentReentry.normalization.croppedRefined)
      (fineReentry := fineCurrentReentry.paperPropStickyReentry
        (backward.seed index hindex).schedule.first.sourceLoss_pos
        hnormalization)
      (rootAxialWindow := rootAxialWindow) (extension := extension) K backward
      root grid leftFactor rightFactor sourceCoefficient global index hindex
      scales)
    (paperCutoff : Proposition63FourCallPaperSeedCutoffData
      (backward.seed index hindex)
      ((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)))
    (hrhoCutoff : scales.rhoHat.1 ≤ paperCutoff.rhoCutoff)
    (finalCurrentLiftAbsorption :
      Proposition63ReentryDensityLiftAbsorptionData
        (backward.currentWeightLoss index hindex)
        (backward.seed index hindex).goodCellCandidateLoss
        (backward.loss (index + 1))
        (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss))
    (hdeltaFinalCurrentLift :
      delta ≤ finalCurrentLiftAbsorption.delta₀)
    (assembly : Proposition63FourCallPaperFinalAssemblyData
      runtime.paperNested.nested.current runtime.rich1.data.croppedCoarseShading
      (proposition63FourCallPaperPullbackCoefficient scales.rhoHat.1
        runtime.paperNested.restoredFirst.retainedFactor
        runtime.firstPullback.retentionFactor))
    (criticalInputs : Proposition63FourCallPaperCriticalTailReceipt
      (backward.seed index hindex) scales.rhoHat.1
      (Real.sqrt scales.rhoHat.1))
    (planeInputs : Proposition63FourCallPaperPlaneCoverReceipt
      runtime.paperNested.nested scales.rhoHat.1 scales.tau
      ((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)))
    (currentInputs : Proposition63FourCallCurrentReceipt
      (sigma := sigma) fineCurrent scales.rhoHat.1)
    (massInputs : Proposition63FourCallPaperMassReceipt
      (Proposition63NestedPointCoverData.FullGrainCells.nestedCandidateIntervalBound
        scales.rhoHat.1 scales.rhoHat.1
        (8 * (((4 : NNReal) * (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ) * scales.rhoHat.1)
        (((4 : NNReal) * (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ) (13 ^ 3)
        (proposition63PaperTauConstant runtime.paperNested.nested))
      (proposition63DependentFinePullbackLeft fineCurrentReentry
        runtime.rich1.data assembly.pullback.retentionFactor
        (ENNReal.ofReal ((criticalInputs.cellVolumeFloor / 2) /
            (4 * (2 * Real.sqrt scales.rhoHat.1) ^ 2)) *
          (((1 : ENNReal) / 2) /
            (2 * (planeInputs.coverBudget : ENNReal))) *
          (runtime.paperNested.nested.secondRetainedFactor *
            ((73 / 100 : ENNReal) *
              runtime.paperNested.nested.reentry.normalizationWeight) *
            runtime.paperNested.nested.firstRetainedFactor)))
      (proposition63DependentFinePullbackRight fineCurrentReentry
        ((runtime.paperNested.nested.reentry.regularized.regularizationLoss *
            runtime.paperNested.nested.prepared.preparationLoss) *
          (2 * ENNReal.ofReal (4 * scales.rhoHat.1))))
      delta criticalInputs.outputCandidateLoss currentInputs.fineCurrentLoss
      ((4 : NNReal) * (lipschitzExtensionConstant Point3 * sourceCoefficient)) criticalInputs.spatialScale
      criticalInputs.variationScale)
    (hincidenceRho : incidence ≤ scales.rhoHat.1)
    (hcoverUpper : (planeInputs.coverBudget : ENNReal) ≤
      (1605264998400 : ENNReal) *
        (((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ENNReal) ^ 3 *
        Kakeya.realRpowENN scales.rhoHat.1
          (-(proposition63FourCallPaperFinalExponent sigma
            (backward.seed index hindex).schedule.fourth.normalizationLoss
            (backward.seed index hindex).fourthKernel.internalLoss
            (backward.seed index hindex).epsilon₁
            (backward.seed index hindex).paperAngularExponent)) + 2)
    (hnextLoss : criticalInputs.outputCandidateLoss =
      backward.loss (index + 1))
    (hconstant : 2 * massInputs.targetConstant ≤
      proposition63FourCallOrderedPairConstant grid index)
    (hleft : massInputs.targetLeft = paperLeftFactor index)
    (hright : massInputs.targetRight = paperRightFactor index) :
    ∃ next : WZ1PaperTubeShading fineNormalized.croppedFamily,
      PaperIsSubshading next fineCurrent ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union, next.pointMultiplicity point =
        fineCurrent.pointMultiplicity point) ∧
      WZ2PaperCroppedIsExtremal sigma (backward.loss (index + 1))
        fineNormalized.croppedFamily next ∧
      WZ2PaperConvexWolffBound fineNormalized.croppedFamily
        (Kakeya.realRpowENN delta (-(backward.loss (index + 1)))) ∧
      PureWZ2IntervalCoveringAt next runtime.currentResult.currentMap.planeMap
        (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
        (grid.scale (finiteIntervalOrderedPair gridN index).1)
        (grid.scale (finiteIntervalOrderedPair gridN index).2)
        (proposition63FourCallOrderedPairConstant grid index) ∧
      paperLeftFactor index * fineCurrent.mass ≤
        paperRightFactor index * next.mass := by
  let seed := backward.seed index hindex
  let coefficient : NNReal :=
    (4 : NNReal) *
      (lipschitzExtensionConstant Point3 * sourceCoefficient)
  let full := Classical.choice
    (runtime.paperNested.nested.fullGrainCells_of_pure_critical_trace
      seed.critical criticalInputs.coarseCritical
      criticalInputs.finalStructural criticalInputs.traceAbsorption
      criticalInputs.cellVolumeFloor_pos criticalInputs.cellBudget
      criticalInputs.query_pos criticalInputs.query_le_one rfl
      planeInputs.plane_unit coefficient planeInputs.coefficient_one
      planeInputs.plane_lipschitz
      planeInputs.coverBudget planeInputs.coverBudget_pos
      planeInputs.cover_budget planeInputs.sqrtConstant_finite)
  let exactConstant :=
    Proposition63NestedPointCoverData.FullGrainCells.nestedCandidateIntervalBound
      scales.rhoHat.1 scales.rhoHat.1
      (8 * (((4 : NNReal) * (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ) * scales.rhoHat.1)
      (((4 : NNReal) * (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ) (13 ^ 3)
      (proposition63PaperTauConstant runtime.paperNested.nested)
  have _hincidenceRho := hincidenceRho
  have hneighbor : ∀ center,
      (full.paperRelevantCells center (2 * Real.sqrt scales.rhoHat.1)).card ≤
        13 ^ 3 :=
    full.paperRelevantCells_card_le_fixed criticalInputs.query_pos rfl
  have hcentered : ∀ center cell, ∀ hcellRelevant :
      cell ∈ full.paperRelevantCells center
        (2 * Real.sqrt scales.rhoHat.1),
      ∀ point ∈ full.paperCellRegion
          ⟨cell, (Finset.mem_filter.mp hcellRelevant).1⟩ ∩
          Metric.closedBall center (2 * Real.sqrt scales.rhoHat.1),
        dist
          (inner ℝ (point - center)
            (runtime.currentResult.currentMap.planeMap center))
          (inner ℝ (point - center)
            (runtime.currentResult.currentMap.planeMap
              (runtime.paperNested.nested.cells.cellRep cell
                ((Finset.mem_filter.mp hcellRelevant).1)))) ≤
          8 * (coefficient : ℝ) * scales.rhoHat.1 :=
    full.paperCandidate_centered_error criticalInputs.query_pos rfl
      coefficient planeInputs.plane_lipschitz
  have hpaperCover : PureWZ2IntervalCoveringAt
      (full.paperCandidate criticalInputs.query_pos)
      runtime.currentResult.currentMap.planeMap scales.rhoHat.1
      (Real.toNNReal scales.rhoHat.1) (Real.toNNReal scales.tau)
      exactConstant := by
    simpa [exactConstant, coefficient, proposition63PaperTauConstant] using
      full.paperCandidate_interval_covering_of_nested_cover
        criticalInputs.query_pos criticalInputs.query_pos scales.tau_pos
        scales.rhoHat_le_tau
        (scales.tau_le_sqrt_logicalR.trans
          (Real.sqrt_le_sqrt scales.logicalR_le_rhoHat)) rfl
        (coefficient : ℝ) planeInputs.coefficient_one
        (fun first _ second _ =>
          planeInputs.plane_lipschitz.dist_le_mul first second)
        planeInputs.plane_unit (2 * Real.sqrt scales.rhoHat.1)
        (8 * (((4 : NNReal) * (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ) * scales.rhoHat.1)
        (by
          have hhullSqrt := planeInputs.hullTau.trans
            (scales.tau_le_sqrt_logicalR.trans
              (Real.sqrt_le_sqrt scales.logicalR_le_rhoHat))
          linarith) (by
          have hc : 0 < (coefficient : ℝ) :=
            lt_of_lt_of_le zero_lt_one planeInputs.coefficient_one
          exact mul_pos (mul_pos (by norm_num) hc)
            criticalInputs.query_pos)
        planeInputs.normalErrorTau planeInputs.hullTau (13 ^ 3)
        hneighbor hcentered
  have hpaperCandidateExtremal : WZ2PaperCroppedIsExtremal sigma
      seed.paperCandidateLoss
      runtime.paperNested.nested.reentry.normalization.croppedFamily
      (full.paperCandidate criticalInputs.query_pos) := by
    exact proposition63_four_call_runtime_paperCandidate_extremal
      hindex runtime paperCutoff hrhoCutoff full
      criticalInputs.query_pos criticalInputs.query_le_one
      planeInputs.coverBudget_pos hincidenceRho hcoverUpper hpaperCover
  have hpaperCandidateSubNormalized : PaperIsSubshading
      (full.paperCandidate criticalInputs.query_pos)
      runtime.paperNested.nested.reentry.normalization.croppedRefined :=
    fun tube point hpoint =>
      runtime.paperNested.nested.second.subshading tube <|
        runtime.paperNested.nested.prepared.subshading_original tube <|
          full.paperCandidate_subshading criticalInputs.query_pos tube hpoint
  let nestedCandidate := runtime.paperNested.nested.reentry.extendCandidate
    (full.paperCandidate criticalInputs.query_pos)
  have hnestedCandidateSub : PaperIsSubshading nestedCandidate
      runtime.paperNested.nested.first.shading :=
    runtime.paperNested.nested.reentry.extendCandidate_subshading
      hpaperCandidateSubNormalized
  have hnestedCandidateCubical : WZ1PaperIsCubicalShading nestedCandidate :=
    extendShading_cubical runtime.paperNested.nested.reentry.regularized.selected
      (full.paperCandidate_cubical criticalInputs.query_pos)
  have hnestedDensityLift :=
    runtime.paperNested.nested.reentry.densityLift_of_absorption
      seed.nestedCandidateLiftAbsorption
      (hrhoCutoff.trans
        paperCutoff.rhoCutoff_le_nestedCandidateLiftAbsorption)
      runtime.paperNested.nestedCanonicalWeight
      runtime.paperNested.nestedCanonicalWeightUpper
      (by simpa only [runtime.currentResult.currentNormalization] using
        runtime.paperNested.nestedCanonicalLevel)
  have hnestedCandidateExtremal : WZ2PaperCroppedIsExtremal sigma
      seed.nestedCandidateLoss
      runtime.currentResult.currentReentry.normalization.croppedFamily
      nestedCandidate := by
    exact runtime.paperNested.nested.reentry.extendCandidate_extremal
      runtime.paperNested.nested.first.extremal
      hpaperCandidateSubNormalized
      (full.paperCandidate_cubical criticalInputs.query_pos)
      hpaperCandidateExtremal
      (by
        rw [seed.ancestorRestoredLoss_eq, seed.nestedCandidateLoss_eq]
        have hsource := seed.schedule.fourth.sourceLoss_le_half
        have hnormalization :=
          seed.schedule.fourth.normalizationLoss_lt_output
        have hout := backward.loss_pos (index + 1) (by omega)
        linarith)
      (by
        rw [seed.nestedCandidateLoss_eq]
        have hout := backward.loss_pos (index + 1) (by omega)
        linarith)
      hnestedDensityLift
  have hnestedCandidateSubCurrentNormalized : PaperIsSubshading
      nestedCandidate
      runtime.currentResult.currentReentry.normalization.croppedRefined := by
    intro tube point hpoint
    apply extendShading_subshading
      runtime.paperNested.outer.data.selected
      runtime.paperNested.outer.data.subshading tube
    apply runtime.paperNested.restoredFirst.state.subshading tube
    rw [← runtime.paperNested.nested_eq]
    exact runtime.paperNested.nested.first.subshading tube
      (hnestedCandidateSub tube hpoint)
  let sourceWitnessCandidate :=
    runtime.currentResult.currentReentry.extendCandidate nestedCandidate
  have hsourceWitnessCandidateSub : PaperIsSubshading
      sourceWitnessCandidate runtime.rich1.terminal.sourceWitness.shading :=
    runtime.currentResult.currentReentry.extendCandidate_subshading
      hnestedCandidateSubCurrentNormalized
  have hsourceWitnessCandidateCubical :
      WZ1PaperIsCubicalShading sourceWitnessCandidate :=
    extendShading_cubical
      runtime.currentResult.currentReentry.regularized.selected
      hnestedCandidateCubical
  have hsourceWitnessDensityLift :=
    runtime.currentResult.currentReentry.densityLift_of_absorption
      seed.sourceWitnessCandidateLiftAbsorption
      (hrhoCutoff.trans
        paperCutoff.rhoCutoff_le_sourceWitnessCandidateLiftAbsorption)
      runtime.currentResult.currentCanonicalWeight
      runtime.currentResult.currentCanonicalWeightUpper
      runtime.currentResult.currentCanonicalLevel
  have hsourceWitnessCandidateExtremal : WZ2PaperCroppedIsExtremal sigma
      seed.sourceWitnessCandidateLoss runtime.rich1.data.coarse
      sourceWitnessCandidate := by
    exact runtime.currentResult.currentReentry.extendCandidate_extremal
      runtime.currentResult.currentReentry.reentry_extremal
      hnestedCandidateSubCurrentNormalized hnestedCandidateCubical
      hnestedCandidateExtremal
      seed.sourceWitnessCurrentLoss_le_candidate
      (by
        rw [seed.sourceWitnessCandidateLoss_eq]
        have hout := backward.loss_pos (index + 1) (by omega)
        positivity)
      hsourceWitnessDensityLift
  have hsourceWitnessCandidateSubCoarse : PaperIsSubshading
      sourceWitnessCandidate runtime.rich1.data.croppedCoarseShading :=
    fun tube point hpoint =>
      runtime.rich1.terminal.sourceWitness.subshading tube
        (hsourceWitnessCandidateSub tube hpoint)
  have hsourceWitnessPullbackCubical : WZ1PaperIsCubicalShading
      (propertyThreeFinePullbackShading runtime.rich1.data.cover
        runtime.rich1.data.refined sourceWitnessCandidate) :=
    propertyThreeFinePullbackShading_cubical runtime.rich1.data.cover
      runtime.rich1.data.refined sourceWitnessCandidate
      runtime.rich1.data.refined_cubical scales.scaleFactor
      scales.scaleFactor_pos scales.rhoHat_aligned
  let terminalCandidate := ambientPropertyThreeCommonHull
    runtime.rich1.data sourceWitnessCandidate
  have hterminalCandidateSub : PaperIsSubshading terminalCandidate
      fineCurrentReentry.normalization.croppedRefined :=
    ambientPropertyThreeCommonHull_subshading runtime.rich1.data
      sourceWitnessCandidate
  have hterminalCandidateCubical :
      WZ1PaperIsCubicalShading terminalCandidate :=
    ambientPropertyThreeCommonHull_cubical runtime.rich1.data
      sourceWitnessCandidate fineCurrentReentry.normalization.cropped_cubical
      hsourceWitnessPullbackCubical
  have hterminalScalar :=
    runtime.rich1.terminal_pullback_scalar_of_absorption
      paperCutoff.terminalAbsorption
      (scales.rhoHat.property.1.trans <|
        hrhoCutoff.trans paperCutoff.rhoCutoff_le_terminalAbsorption)
      (scales.output_rpow_le_rhoHat
        seed.schedule.firstOutputLoss_pos
        (global.firstOutputLoss_le_discrete index hindex))
  have hterminalDensity :=
    runtime.rich1.terminal_commonHull_candidateExtremal_densityLift
      sourceWitnessCandidate hsourceWitnessCandidateExtremal
      hsourceWitnessCandidateSubCoarse hsourceWitnessCandidateCubical
      (fineCurrentReentry.delta_small.trans (by norm_num))
      ((global.rho_small index hindex scales).trans (by norm_num))
      hterminalScalar
  have hterminalCandidateExtremal : WZ2PaperCroppedIsExtremal sigma
      seed.goodCellCandidateLoss
      fineCurrentReentry.normalization.croppedFamily terminalCandidate :=
    proposition63_paper_coarseToFine_pulledCandidate_extremal
      fineCurrentReentry.normalization.final_extremal
      fineCurrentReentry.normalization.line_class
      fineCurrentReentry.delta_small hterminalCandidateSub
      hterminalCandidateCubical
      (by
        rw [hnormalization]
        exact seed.schedule.first.normalizationLoss_lt_output.le.trans <|
          seed.schedule.firstOutputLoss_lt_secondSource.le.trans <|
            seed.sourceWitnessCurrentLoss_le_candidate.trans
              seed.terminalCandidateGap.le)
      hterminalDensity
  let liftedFinalCandidate :=
    fineCurrentReentry.extendCandidate terminalCandidate
  have hliftedFinalCandidateSub :
      PaperIsSubshading liftedFinalCandidate fineCurrent :=
    fineCurrentReentry.extendCandidate_subshading hterminalCandidateSub
  have hliftedFinalCandidateCubical :
      WZ1PaperIsCubicalShading liftedFinalCandidate :=
    extendShading_cubical fineCurrentReentry.regularized.selected
      hterminalCandidateCubical
  have hfinalDensityLift :=
    fineCurrentReentry.densityLift_of_absorption
      finalCurrentLiftAbsorption hdeltaFinalCurrentLift hfineWeight
      hfineWeightUpper hfineLevel
  have hliftedFinalCandidateExtremal : WZ2PaperCroppedIsExtremal sigma
      (backward.loss (index + 1)) fineNormalized.croppedFamily
      liftedFinalCandidate := by
    exact fineCurrentReentry.extendCandidate_extremal
      currentInputs.current_extremal hterminalCandidateSub
      hterminalCandidateCubical hterminalCandidateExtremal
      (massInputs.currentOutput.trans <| by rw [hnextLoss])
      (backward.loss_pos (index + 1) (by omega)) hfinalDensityLift
  let finalCandidate :=
    paperCommonSpatialHull fineCurrent liftedFinalCandidate
  have hfinalCandidateSub : PaperIsSubshading finalCandidate fineCurrent :=
    paperCommonSpatialHull_subshading fineCurrent liftedFinalCandidate
  have hfinalCandidateCubical : WZ1PaperIsCubicalShading finalCandidate :=
    paperCommonSpatialHull_cubical fineCurrentReentry.current_cubical
      hliftedFinalCandidateCubical
  have hfinalCandidateExtremal : WZ2PaperCroppedIsExtremal sigma
      (backward.loss (index + 1)) fineNormalized.croppedFamily
      finalCandidate :=
    paperCommonSpatialHull_extremal hliftedFinalCandidateSub
      fineCurrentReentry.current_cubical hliftedFinalCandidateCubical
      hliftedFinalCandidateExtremal
  have houterCover : PureWZ2IntervalCoveringAt
      (full.paperOuterCandidate criticalInputs.query_pos)
      runtime.currentResult.currentMap.planeMap scales.rhoHat.1
      (Real.toNNReal scales.rhoHat.1) (Real.toNNReal scales.tau)
      exactConstant := by
    intro point intervalCenter
    have hp : (point : Point3) ∈
        (full.paperCandidate criticalInputs.query_pos).union := by
      rw [← full.paperOuterCandidate_union criticalInputs.query_pos]
      exact point.property
    simpa only [full.paperOuterCandidate_union criticalInputs.query_pos] using
      hpaperCover ⟨point, hp⟩ intervalCenter
  have hcoarseVariation : ∀ first ∈
      (full.paperOuterCandidate criticalInputs.query_pos).union,
      ∀ second ∈ (full.paperOuterCandidate criticalInputs.query_pos).union,
      dist first second ≤ criticalInputs.spatialScale →
        dist (runtime.currentResult.currentMap.planeMap first)
          (runtime.currentResult.currentMap.planeMap second) ≤
            criticalInputs.variationScale := by
    intro first _ second _ hdist
    exact (planeInputs.plane_lipschitz.dist_le_mul first second).trans
      (massInputs.variation.trans'
        (mul_le_mul_of_nonneg_left hdist coefficient.coe_nonneg))
  have hcoarseMass :
      (((runtime.paperNested.nested.cells.cellMass / 2) /
          (2 * (planeInputs.coverBudget : ENNReal))) *
        (runtime.paperNested.nested.secondRetainedFactor *
          ((73 / 100 : ENNReal) *
            runtime.paperNested.nested.reentry.normalizationWeight) *
          runtime.paperNested.nested.firstRetainedFactor)) *
          runtime.paperNested.nested.current.mass ≤
        ((runtime.paperNested.nested.reentry.regularized.regularizationLoss *
            runtime.paperNested.nested.prepared.preparationLoss) *
          (4 * (ENNReal.ofReal
              (4 * (2 * Real.sqrt scales.rhoHat.1) ^ 2) *
            ENNReal.ofReal (4 * scales.rhoHat.1)))) *
          (full.paperOuterCandidate criticalInputs.query_pos).mass := by
    simpa only using full.paperOuterCandidate_mass_ledger
      criticalInputs.query_pos criticalInputs.query_pos
  let massScale : ENNReal :=
    proposition63FourCallPaperMassScale scales.rhoHat.1
  have hmassScalePos : 0 < massScale := by
    dsimp only [massScale]
    exact ENNReal.mul_pos (by norm_num)
      (ENNReal.ofReal_pos.mpr criticalInputs.query_pos).ne'
  have hmassScaleFinite : massScale ≠ ⊤ := by
    dsimp only [massScale]
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hcellLower : ENNReal.ofReal criticalInputs.cellVolumeFloor ≤
      runtime.paperNested.nested.cells.cellMass :=
    runtime.paperNested.nested.critical_cellMass_lower_of_pure_critical_trace
      seed.critical criticalInputs.coarseCritical
      criticalInputs.finalStructural criticalInputs.traceAbsorption
      criticalInputs.cellVolumeFloor_pos.le criticalInputs.cellBudget
  have hscaledLineCover :
      massScale *
          (ENNReal.ofReal ((criticalInputs.cellVolumeFloor / 2) /
              (4 * (2 * Real.sqrt scales.rhoHat.1) ^ 2)) *
            (((1 : ENNReal) / 2) /
              (2 * (planeInputs.coverBudget : ENNReal)))) ≤
        (runtime.paperNested.nested.cells.cellMass / 2) /
          (2 * (planeInputs.coverBudget : ENNReal)) := by
    exact proposition63_four_call_paper_scaled_line_cover_le
      criticalInputs.query_pos hcellLower
  have hscaledCoarseLeft :
      massScale *
          (ENNReal.ofReal ((criticalInputs.cellVolumeFloor / 2) /
              (4 * (2 * Real.sqrt scales.rhoHat.1) ^ 2)) *
            (((1 : ENNReal) / 2) /
              (2 * (planeInputs.coverBudget : ENNReal))) *
            (runtime.paperNested.nested.secondRetainedFactor *
              ((73 / 100 : ENNReal) *
                runtime.paperNested.nested.reentry.normalizationWeight) *
              runtime.paperNested.nested.firstRetainedFactor)) ≤
        ((runtime.paperNested.nested.cells.cellMass / 2) /
            (2 * (planeInputs.coverBudget : ENNReal))) *
          (runtime.paperNested.nested.secondRetainedFactor *
            ((73 / 100 : ENNReal) *
              runtime.paperNested.nested.reentry.normalizationWeight) *
              runtime.paperNested.nested.firstRetainedFactor) := by
    simpa only [mul_assoc] using mul_le_mul_right' hscaledLineCover
      (runtime.paperNested.nested.secondRetainedFactor *
        ((73 / 100 : ENNReal) *
          runtime.paperNested.nested.reentry.normalizationWeight) *
        runtime.paperNested.nested.firstRetainedFactor)
  have hscaledLeft :
      massScale *
          proposition63DependentFinePullbackLeft fineCurrentReentry
            runtime.rich1.data assembly.pullback.retentionFactor
            (ENNReal.ofReal ((criticalInputs.cellVolumeFloor / 2) /
                (4 * (2 * Real.sqrt scales.rhoHat.1) ^ 2)) *
              (((1 : ENNReal) / 2) /
                (2 * (planeInputs.coverBudget : ENNReal))) *
              (runtime.paperNested.nested.secondRetainedFactor *
                ((73 / 100 : ENNReal) *
                  runtime.paperNested.nested.reentry.normalizationWeight) *
                runtime.paperNested.nested.firstRetainedFactor)) ≤
        proposition63DependentFinePullbackLeft fineCurrentReentry
          runtime.rich1.data assembly.pullback.retentionFactor
          (((runtime.paperNested.nested.cells.cellMass / 2) /
              (2 * (planeInputs.coverBudget : ENNReal))) *
            (runtime.paperNested.nested.secondRetainedFactor *
              ((73 / 100 : ENNReal) *
                runtime.paperNested.nested.reentry.normalizationWeight) *
              runtime.paperNested.nested.firstRetainedFactor)) := by
    simpa only [proposition63DependentFinePullbackLeft, mul_assoc] using
      proposition63_four_call_paper_scaled_chain_le
      (first := assembly.pullback.retentionFactor⁻¹)
      (second :=
        (proposition63OuterCoarsePullbackCost runtime.rich1.data)⁻¹)
      (third := wz2PaperPureRefinementFraction delta 61)
      (fourth := (73 / 100 : ENNReal) *
        fineCurrentReentry.normalizationWeight) hscaledCoarseLeft
  have hscaledRight :
      proposition63DependentFinePullbackRight fineCurrentReentry
          ((runtime.paperNested.nested.reentry.regularized.regularizationLoss *
              runtime.paperNested.nested.prepared.preparationLoss) *
            (4 * (ENNReal.ofReal
                (4 * (2 * Real.sqrt scales.rhoHat.1) ^ 2) *
              ENNReal.ofReal (4 * scales.rhoHat.1)))) =
        massScale * proposition63DependentFinePullbackRight fineCurrentReentry
          ((runtime.paperNested.nested.reentry.regularized.regularizationLoss *
              runtime.paperNested.nested.prepared.preparationLoss) *
            (2 * ENNReal.ofReal (4 * scales.rhoHat.1))) := by
    exact proposition63_four_call_paper_scaled_right_product
      (loss := runtime.paperNested.nested.reentry.regularized.regularizationLoss *
        runtime.paperNested.nested.prepared.preparationLoss)
      (fineLoss := fineCurrentReentry.regularized.regularizationLoss)
      (proposition63_four_call_paper_scaled_geometric
        criticalInputs.query_pos)
  let stagedCandidate := proposition63FinalPaperCommonSpatialHull
    fineCurrentReentry runtime.rich1.data
    runtime.currentResult.currentReentry.normalization
    (full.paperOuterCandidate criticalInputs.query_pos)
    assembly.pullback.embedding assembly.pullback.tube_eq
  have hsourceWitnessCandidateUnion : sourceWitnessCandidate.union =
      (full.paperOuterCandidate criticalInputs.query_pos).union := by
    calc
      sourceWitnessCandidate.union = nestedCandidate.union :=
        runtime.currentResult.currentReentry.extendCandidate_union
          nestedCandidate
      _ = (full.paperCandidate criticalInputs.query_pos).union :=
        runtime.paperNested.nested.reentry.extendCandidate_union _
      _ = (full.paperOuterCandidate criticalInputs.query_pos).union :=
        (full.paperOuterCandidate_union criticalInputs.query_pos).symm
  let coarseZeroCandidate := proposition63CoarseZeroExtension
    runtime.rich1.data runtime.currentResult.currentReentry.normalization
    (full.paperOuterCandidate criticalInputs.query_pos)
    assembly.pullback.embedding assembly.pullback.tube_eq
  have hcoarseZeroCandidateUnion : coarseZeroCandidate.union =
      (full.paperOuterCandidate criticalInputs.query_pos).union := by
    simpa only [coarseZeroCandidate, proposition63CoarseZeroExtension] using
      extendShading_union
        { family := runtime.currentResult.currentReentry.normalization.croppedFamily
          embedding := assembly.pullback.embedding
          tube_eq := assembly.pullback.tube_eq }
        (full.paperOuterCandidate criticalInputs.query_pos)
  have hterminalCandidateEq : terminalCandidate =
      proposition63NormalizedAmbientPropertyThreeCommonHull
        fineCurrentReentry runtime.rich1.data
        runtime.currentResult.currentReentry.normalization
        (full.paperOuterCandidate criticalInputs.query_pos)
        assembly.pullback.embedding assembly.pullback.tube_eq := by
    change ambientPropertyThreeCommonHull runtime.rich1.data
        sourceWitnessCandidate =
      ambientPropertyThreeCommonHull runtime.rich1.data coarseZeroCandidate
    exact ambientPropertyThreeCommonHull_eq_of_union_eq runtime.rich1.data <|
      hsourceWitnessCandidateUnion.trans hcoarseZeroCandidateUnion.symm
  have hstagedCandidateEq : stagedCandidate = finalCandidate := by
    change paperCommonSpatialHull fineCurrent
        (fineCurrentReentry.extendCandidate
          (proposition63NormalizedAmbientPropertyThreeCommonHull
            fineCurrentReentry runtime.rich1.data
            runtime.currentResult.currentReentry.normalization
            (full.paperOuterCandidate criticalInputs.query_pos)
            assembly.pullback.embedding assembly.pullback.tube_eq)) =
      paperCommonSpatialHull fineCurrent
        (fineCurrentReentry.extendCandidate terminalCandidate)
    rw [hterminalCandidateEq]
  rcases fineCurrentReentry.explicit_staged_pullback_candidate
      (outer := runtime.rich1.data)
      (coarseNormalized := runtime.currentResult.currentReentry.normalization)
      (coarseCurrent := runtime.paperNested.nested.current)
      (coarseCandidate := full.paperOuterCandidate criticalInputs.query_pos)
      (ancestorEmbedding := assembly.pullback.embedding)
      (ancestor_tube_eq := assembly.pullback.tube_eq)
      (current_sub_outer := assembly.pullback.subshading)
      (ancestorRetentionFactor := assembly.pullback.retentionFactor)
      (current_retained_mass := assembly.pullback.retained_mass)
      (planeMap := runtime.currentResult.currentMap.planeMap)
      (resolutionScale := Real.toNNReal scales.rhoHat.1)
      (windowScale := Real.toNNReal scales.tau) (constant := exactConstant)
      (coarseLeft := ((runtime.paperNested.nested.cells.cellMass / 2) /
        (2 * (planeInputs.coverBudget : ENNReal))) *
        (runtime.paperNested.nested.secondRetainedFactor *
          ((73 / 100 : ENNReal) *
            runtime.paperNested.nested.reentry.normalizationWeight) *
          runtime.paperNested.nested.firstRetainedFactor))
      (coarseRight :=
        (runtime.paperNested.nested.reentry.regularized.regularizationLoss *
          runtime.paperNested.nested.prepared.preparationLoss) *
        (4 * (ENNReal.ofReal (4 * (2 * Real.sqrt scales.rhoHat.1) ^ 2) *
          ENNReal.ofReal (4 * scales.rhoHat.1))))
      (hcoarseSub := full.paperOuterCandidate_subshading
        criticalInputs.query_pos)
      (hcoarseCubical := full.paperOuterCandidate_cubical
        criticalInputs.query_pos)
      (hcoarseVariation := hcoarseVariation)
      (hcoarseInterval := houterCover) (hcoarseMass := hcoarseMass)
      (scaleFactor := scales.scaleFactor)
      (hscaleFactor := scales.scaleFactor_pos)
      (hrhoAligned := scales.rhoHat_aligned) with
    ⟨hpulledSub, hpulledCubical, hpulledMultiplicity, _hvariation,
      hpulledCover, hpulledMass⟩
  have hpulledEq : stagedCandidate = finalCandidate := hstagedCandidateEq
  have htargetLeftScaled : massScale * massInputs.targetLeft ≤
      massScale *
        proposition63DependentFinePullbackLeft fineCurrentReentry
          runtime.rich1.data assembly.pullback.retentionFactor
          (ENNReal.ofReal ((criticalInputs.cellVolumeFloor / 2) /
              (4 * (2 * Real.sqrt scales.rhoHat.1) ^ 2)) *
            (((1 : ENNReal) / 2) /
              (2 * (planeInputs.coverBudget : ENNReal))) *
            (runtime.paperNested.nested.secondRetainedFactor *
              ((73 / 100 : ENNReal) *
                runtime.paperNested.nested.reentry.normalizationWeight) *
              runtime.paperNested.nested.firstRetainedFactor)) :=
    by simpa only [mul_comm] using
      mul_le_mul_right' massInputs.left_bound massScale
  have htargetRightScaled :
      massScale *
        proposition63DependentFinePullbackRight fineCurrentReentry
          ((runtime.paperNested.nested.reentry.regularized.regularizationLoss *
              runtime.paperNested.nested.prepared.preparationLoss) *
            (2 * ENNReal.ofReal (4 * scales.rhoHat.1))) ≤
      massScale * massInputs.targetRight :=
    by simpa only [mul_comm] using
      mul_le_mul_right' massInputs.right_bound massScale
  have hscaledTargetMass :
      massScale * (massInputs.targetLeft * fineCurrent.mass) ≤
        massScale * (massInputs.targetRight * finalCandidate.mass) := by
    calc
      massScale * (massInputs.targetLeft * fineCurrent.mass) =
          (massScale * massInputs.targetLeft) * fineCurrent.mass := by ring
      _ ≤ (massScale *
            proposition63DependentFinePullbackLeft fineCurrentReentry
              runtime.rich1.data assembly.pullback.retentionFactor
              (ENNReal.ofReal ((criticalInputs.cellVolumeFloor / 2) /
                  (4 * (2 * Real.sqrt scales.rhoHat.1) ^ 2)) *
                (((1 : ENNReal) / 2) /
                  (2 * (planeInputs.coverBudget : ENNReal))) *
                (runtime.paperNested.nested.secondRetainedFactor *
                  ((73 / 100 : ENNReal) *
                    runtime.paperNested.nested.reentry.normalizationWeight) *
                  runtime.paperNested.nested.firstRetainedFactor))) *
            fineCurrent.mass := mul_le_mul_right' htargetLeftScaled _
      _ ≤ proposition63DependentFinePullbackLeft fineCurrentReentry
              runtime.rich1.data assembly.pullback.retentionFactor
              (((runtime.paperNested.nested.cells.cellMass / 2) /
                  (2 * (planeInputs.coverBudget : ENNReal))) *
                (runtime.paperNested.nested.secondRetainedFactor *
                  ((73 / 100 : ENNReal) *
                    runtime.paperNested.nested.reentry.normalizationWeight) *
                  runtime.paperNested.nested.firstRetainedFactor)) *
            fineCurrent.mass := mul_le_mul_left hscaledLeft _
      _ ≤ proposition63DependentFinePullbackRight fineCurrentReentry
              ((runtime.paperNested.nested.reentry.regularized.regularizationLoss *
                  runtime.paperNested.nested.prepared.preparationLoss) *
                (4 * (ENNReal.ofReal
                    (4 * (2 * Real.sqrt scales.rhoHat.1) ^ 2) *
                  ENNReal.ofReal (4 * scales.rhoHat.1)))) *
                finalCandidate.mass := by
        rw [← hpulledEq]
        exact hpulledMass
      _ = (massScale *
            proposition63DependentFinePullbackRight fineCurrentReentry
              ((runtime.paperNested.nested.reentry.regularized.regularizationLoss *
                  runtime.paperNested.nested.prepared.preparationLoss) *
                (2 * ENNReal.ofReal (4 * scales.rhoHat.1)))) *
              finalCandidate.mass := by
        exact congrArg (fun factor : ENNReal => factor * finalCandidate.mass)
          hscaledRight
      _ ≤ (massScale * massInputs.targetRight) * finalCandidate.mass :=
        mul_le_mul_right' htargetRightScaled _
      _ = massScale * (massInputs.targetRight * finalCandidate.mass) := by ring
  have htargetMass : massInputs.targetLeft * fineCurrent.mass ≤
      massInputs.targetRight * finalCandidate.mass :=
    (ENNReal.mul_le_mul_iff_right hmassScalePos.ne' hmassScaleFinite).mp
      hscaledTargetMass
  have hpair := finiteIntervalOrderedPair_valid hindex
  have hkPos := grid.scale_pos _ (hpair.1.le.trans hpair.2)
  have hlogicalNN : grid.scale (finiteIntervalOrderedPair gridN index).1 ≤
      Real.toNNReal scales.rhoHat.1 := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ criticalInputs.query_pos.le]
    exact scales.logicalR_le_rhoHat
  have hrhoNNTwo : Real.toNNReal scales.rhoHat.1 ≤
      2 * grid.scale (finiteIntervalOrderedPair gridN index).1 := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ criticalInputs.query_pos.le]
    exact scales.rhoHat_le_two_logicalR
  have hcoverAligned := pureWZ2IntervalCoveringAt_mono_query_refine_resolution_two
    scales.logicalR_le_rhoHat hkPos hlogicalNN hrhoNNTwo
    (pureWZ2IntervalCoveringAt_mono_constant massInputs.constant_bound <|
      show PureWZ2IntervalCoveringAt finalCandidate
          runtime.currentResult.currentMap.planeMap scales.rhoHat.1
          (Real.toNNReal scales.rhoHat.1) (Real.toNNReal scales.tau)
          exactConstant from by
        rw [← hpulledEq]
        exact hpulledCover)
  refine ⟨finalCandidate, hfinalCandidateSub, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact hfinalCandidateCubical
  · intro point hpoint
    exact paperCommonSpatialHull_pointMultiplicity_eq fineCurrent
      liftedFinalCandidate point hpoint
  · exact hfinalCandidateExtremal
  · exact transfer_cwa_to_subshading
      (family := fineNormalized.croppedFamily)
      (_shading1 := fineCurrent) (_shading2 := finalCandidate)
      currentInputs.current_cwa
      (massInputs.currentOutput.trans <| by rw [hnextLoss])
      currentInputs.current_extremal.delta_pos
      currentInputs.current_extremal.delta_le_one
  · have hcoverFinal := pureWZ2IntervalCoveringAt_mono_constant
      hconstant hcoverAligned
    have hjPos := grid.scale_pos _ hpair.2
    have hjNN : Real.toNNReal
        (grid.scale (finiteIntervalOrderedPair gridN index).2 : ℝ) =
          grid.scale (finiteIntervalOrderedPair gridN index).2 := by
      ext
      exact Real.coe_toNNReal _ hjPos.le
    simpa only [scales.tau_eq, hjNN, proposition63FourCallOrderedPairConstant]
      using hcoverFinal
  · calc
      paperLeftFactor index * fineCurrent.mass =
          massInputs.targetLeft * fineCurrent.mass := by
        rw [hleft]
      _ ≤ massInputs.targetRight * finalCandidate.mass := htargetMass
      _ = paperRightFactor index * finalCandidate.mass := by
        rw [hright]

end Kakeya.Assouad.PureWZ2
