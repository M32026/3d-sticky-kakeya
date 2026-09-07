import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightProduction

/-!
# Return the final affine approximation to the exact source restriction

The production assignment is the identity, so every retained source point
lies in a graph-height slab selected by the same Theorem-5.2 output.  The
sharp graph-center estimate, the source-slope Lipschitz bound, and the affine
slope bound give the paper-scale `5 * graphScale` approximation.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2Node05V4RichJointTheorem52Data

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta finalLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {B₀ threshold : ENNReal}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {prepared : PureWZ2Node05V4RichJointPreparedData
      (eta := eta) pullback heightIndex B₀ threshold hbridge}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (data : PureWZ2Node05V4RichJointTheorem52Data prepared projection)

theorem sourceMass_assignedHeights_eq :
    data.sourceMass.assignedHeights = data.output.richHeightIndices := by
  rw [data.sourceMass.assignedHeights_eq, data.assignment_exact]
  simp

theorem sourceMass_slope_approximation
    (point : Point3) (hpoint : point ∈ data.sourceMass.shading.union) :
    |current.grain.globalGrains.slope (point (2 : Fin 3)) -
        data.output.lineData.L_S (point (2 : Fin 3))| ≤
      (9 / 2 : ℝ) * prepared.separated.graphScale := by
  have hsourceHeight :
      point (2 : Fin 3) ∈
        prepared.volumePopular.continuous.popularHeights :=
    data.sourceMass.source_height_mem_ZS point hpoint
  have hheightRange :
      point (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 :=
    pullback.sourcePopularHeight_mem_paperRange heightIndex.1.2
      (by
        rw [← prepared.volumePopular.continuous.popularHeights_eq]
        exact hsourceHeight)
  have hregion := hpoint
  rw [data.sourceMass.union_eq] at hregion
  have hassignedRegion := hregion.2
  rw [data.sourceMass.assignedRegion_eq] at hassignedRegion
  rcases Set.mem_iUnion₂.mp hassignedRegion with
    ⟨selectedHeight, hselectedHeight, hpointSlab⟩
  have hrichHeight :
      selectedHeight ∈ data.output.richHeightIndices := by
    rw [data.sourceMass_assignedHeights_eq] at hselectedHeight
    exact hselectedHeight
  rw [PureWZ2AnchoredTheorem52Output.richHeightIndices] at hrichHeight
  rcases Finset.mem_image.mp hrichHeight with
    ⟨richPoint, hrichPoint, hrichHeightEq⟩
  have hcellHeight :
      (data.output.lineData.graphCell richPoint).2.2 = selectedHeight := by
    simpa [PureWZ2AnchoredTheorem52Output.richHeightIndex] using hrichHeightEq
  have hsourceHeightEq :
      data.output.lineData.sourceHeight richPoint =
        wz1Lemma23SnappedBaseHeight
          prepared.separated.graphScale selectedHeight := by
    rw [data.output.lineData.sourceHeight_eq]
    simp [wz1Lemma23SnappedPoint, wz1Lemma23CellCenter,
      wz1Lemma23SnappedBaseHeight, point3, hcellHeight]
  have hpointClose :
      |point (2 : Fin 3) -
          data.output.lineData.sourceHeight richPoint| ≤
        prepared.separated.graphScale / 2 := by
    rw [hsourceHeightEq]
    change point (2 : Fin 3) ∈
      wz1Lemma23HeightInterval
        prepared.separated.graphScale selectedHeight at hpointSlab
    have hside :
        gridSide (prepared.separated.graphScale / 2) =
          prepared.separated.graphScale / Real.sqrt 3 := by
      simp [gridSide]
      ring
    rw [wz1Lemma23HeightInterval, hside] at hpointSlab
    rw [wz1Lemma23SnappedBaseHeight, hside, abs_le]
    constructor
    · have hhalf :
          prepared.separated.graphScale / (2 * Real.sqrt 3) ≤
            prepared.separated.graphScale / 2 := by
        have hden : (2 : ℝ) ≤ 2 * Real.sqrt 3 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
            Real.sqrt_nonneg (3 : ℝ)]
        exact div_le_div_of_nonneg_left
          prepared.separated.graphScale_pos.le (by norm_num) hden
      have hcenter :
          ((selectedHeight : ℝ) + 1 / 2) *
              (prepared.separated.graphScale / Real.sqrt 3) -
            (selectedHeight : ℝ) *
              (prepared.separated.graphScale / Real.sqrt 3) =
            prepared.separated.graphScale / (2 * Real.sqrt 3) := by ring
      linarith [hpointSlab.1, hhalf, hcenter]
    · have hhalf :
          prepared.separated.graphScale / (2 * Real.sqrt 3) ≤
            prepared.separated.graphScale / 2 := by
        have hden : (2 : ℝ) ≤ 2 * Real.sqrt 3 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
            Real.sqrt_nonneg (3 : ℝ)]
        exact div_le_div_of_nonneg_left
          prepared.separated.graphScale_pos.le (by norm_num) hden
      have hcenterUpper :
          ((selectedHeight : ℝ) + 1) *
              (prepared.separated.graphScale / Real.sqrt 3) -
            ((selectedHeight : ℝ) + 1 / 2) *
              (prepared.separated.graphScale / Real.sqrt 3) =
            prepared.separated.graphScale / (2 * Real.sqrt 3) := by ring
      linarith [hpointSlab.2, hhalf, hcenterUpper]
  have hextendedAtPoint :
      prepared.finite.prep.windowed.global.extendedSlope
          (point (2 : Fin 3)) =
        current.grain.globalGrains.slope (point (2 : Fin 3)) := by
    rw [prepared.finite.prep.windowed.global.extendedSlope_eq
      (point (2 : Fin 3)) hheightRange]
    rw [prepared.finite.prep.sourceSlope_eq]
    rfl
  have hslopeLip :
      |prepared.finite.prep.windowed.global.extendedSlope
            (point (2 : Fin 3)) -
          prepared.finite.prep.windowed.global.extendedSlope
            (data.output.lineData.sourceHeight richPoint)| ≤
        prepared.separated.graphScale / 2 := by
    have hlip :=
      prepared.finite.prep.windowed.global.extendedSlope_lipschitz.dist_le_mul
        (point (2 : Fin 3)) (by simp)
        (data.output.lineData.sourceHeight richPoint) (by simp)
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
    exact hlip.trans hpointClose
  have hlineLip :
      |data.output.lineData.L_S
            (data.output.lineData.sourceHeight richPoint) -
          data.output.lineData.L_S (point (2 : Fin 3))| ≤
        prepared.separated.graphScale := by
    rw [data.output.lineData.L_S_eq]
    have hslope := data.output.lineData.L_S_slope_bound
    calc
      |(data.output.lineData.L_S_slope *
            data.output.lineData.sourceHeight richPoint +
          data.output.lineData.L_S_intercept) -
        (data.output.lineData.L_S_slope * point (2 : Fin 3) +
          data.output.lineData.L_S_intercept)| =
          |data.output.lineData.L_S_slope| *
            |data.output.lineData.sourceHeight richPoint -
              point (2 : Fin 3)| := by
        rw [show
          (data.output.lineData.L_S_slope *
                data.output.lineData.sourceHeight richPoint +
              data.output.lineData.L_S_intercept) -
            (data.output.lineData.L_S_slope * point (2 : Fin 3) +
              data.output.lineData.L_S_intercept) =
            data.output.lineData.L_S_slope *
              (data.output.lineData.sourceHeight richPoint -
                point (2 : Fin 3)) by ring, abs_mul]
      _ ≤ 2 * (prepared.separated.graphScale / 2) := by
        gcongr
        simpa [abs_sub_comm] using hpointClose
      _ = prepared.separated.graphScale := by ring
  have hcenterApprox :=
    data.output.lineData.L_S_approximation_sharp richPoint hrichPoint
  rw [← hextendedAtPoint]
  calc
    _ ≤
        |prepared.finite.prep.windowed.global.extendedSlope
              (point (2 : Fin 3)) -
            prepared.finite.prep.windowed.global.extendedSlope
              (data.output.lineData.sourceHeight richPoint)| +
          |prepared.finite.prep.windowed.global.extendedSlope
              (data.output.lineData.sourceHeight richPoint) -
            data.output.lineData.L_S
              (data.output.lineData.sourceHeight richPoint)| +
          |data.output.lineData.L_S
              (data.output.lineData.sourceHeight richPoint) -
            data.output.lineData.L_S (point (2 : Fin 3))| := by
      have hone := abs_sub_le
        (prepared.finite.prep.windowed.global.extendedSlope
          (point (2 : Fin 3)))
        (prepared.finite.prep.windowed.global.extendedSlope
          (data.output.lineData.sourceHeight richPoint))
        (data.output.lineData.L_S (point (2 : Fin 3)))
      have htwo := abs_sub_le
        (prepared.finite.prep.windowed.global.extendedSlope
          (data.output.lineData.sourceHeight richPoint))
        (data.output.lineData.L_S
          (data.output.lineData.sourceHeight richPoint))
        (data.output.lineData.L_S (point (2 : Fin 3)))
      linarith
    _ ≤ prepared.separated.graphScale / 2 +
          3 * prepared.separated.graphScale +
          prepared.separated.graphScale := by
      gcongr
    _ = (9 / 2 : ℝ) * prepared.separated.graphScale := by ring

/-- Per-block weighted mass return from the whole heavy source slab to the
identity `Z_lin` source restriction.  The cost is only the two popularity
halves, the dyadic bin count, the number of popular graph-height layers, and
the fixed factor three in the generic mass interface. -/
theorem sourceSlab_weighted_mass_return :
    (((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
          twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
      Kakeya.realRpowENN data.output.ready.ready.deltaGraph (finalLoss - 1)) *
      (volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) /
        2 / 2) ≤
    (6 * (prepared.volumePopular.popular.bins : ENNReal) *
      (prepared.volumePopular.popular.heightIndices.card : ENNReal)) *
        data.sourceMass.shading.mass := by
  have hhalf :
      volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) / 2 / 2 ≤
        (prepared.volumePopular.popular.bins : ENNReal) *
          volume prepared.volumePopular.jointSourceSet := by
    calc
      volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) / 2 / 2 ≤
          volume prepared.volumePopular.continuous.popularRegion / 2 := by
        gcongr
        exact prepared.volumePopular.continuous.popularRegion_half_volume
      _ = volume prepared.volumePopular.sourcePopularShading.union / 2 := by
        rw [prepared.volumePopular.sourcePopularShading_union]
      _ ≤ (prepared.volumePopular.popular.bins : ENNReal) *
          volume prepared.volumePopular.jointSourceSet := by
        simpa only [
          PureWZ2Node05V4RichSourceVolumePopularHeightData.jointSourceSet]
          using prepared.volumePopular.popular.retained_volume
  have hpopularVolume :
      volume prepared.volumePopular.jointSourceSet ≤
        2 * (prepared.volumePopular.popular.heightIndices.card : ENNReal) *
          prepared.volumePopular.popular.layerMass := by
    rw [PureWZ2Node05V4RichSourceVolumePopularHeightData.jointSourceSet,
      prepared.volumePopular.popular.volume_eq_sum]
    calc
      (∑ selectedHeight ∈
          prepared.volumePopular.popular.heightIndices,
        volume (prepared.volumePopular.sourcePopularShading.union ∩
          wz1Lemma23HeightSlab (256 * rho) selectedHeight)) ≤
        ∑ _selectedHeight ∈
          prepared.volumePopular.popular.heightIndices,
            2 * prepared.volumePopular.popular.layerMass := by
          exact Finset.sum_le_sum fun selectedHeight hselectedHeight =>
            (prepared.volumePopular.popular.layer_volume_band
              selectedHeight hselectedHeight).2
      _ = 2 * (prepared.volumePopular.popular.heightIndices.card : ENNReal) *
          prepared.volumePopular.popular.layerMass := by
        simp [Finset.sum_const]
        ring
  have hrich :
      Kakeya.realRpowENN data.output.ready.ready.deltaGraph (finalLoss - 1) ≤
        (data.output.richHeightIndices.card : ENNReal) := by
    rw [data.output.richHeightIndices_card]
    exact data.output.lineData.richF_card
  let floor : ENNReal :=
    (twoScale.first.fourDegreeReceipts.fineDegreeFloor *
      twoScale.first.fourDegreeReceipts.muFine : ℕ)
  let richFloor : ENNReal :=
    Kakeya.realRpowENN data.output.ready.ready.deltaGraph (finalLoss - 1)
  let popularCount : ENNReal :=
    prepared.volumePopular.popular.heightIndices.card
  let bins : ENNReal := prepared.volumePopular.popular.bins
  calc
    (floor * richFloor) *
          (volume (pullback.standardSqrtSlabSourceRegion
            heightIndex.1.1) / 2 / 2) ≤
        (floor * richFloor) *
          (bins * volume prepared.volumePopular.jointSourceSet) := by
      gcongr
    _ ≤ (floor * richFloor) *
          (bins * (2 * popularCount *
            prepared.volumePopular.popular.layerMass)) := by
      gcongr
    _ ≤ (floor * (data.output.richHeightIndices.card : ENNReal)) *
          (bins * (2 * popularCount *
            prepared.volumePopular.popular.layerMass)) := by
      gcongr
    _ = (2 * bins * popularCount) *
          (floor * ((data.output.richHeightIndices.card : ENNReal) *
            prepared.volumePopular.popular.layerMass)) := by ring
    _ ≤ (2 * bins * popularCount) *
          (3 * data.sourceMass.shading.mass) := by
      exact mul_le_mul_right
        (by simpa [floor, Nat.cast_mul] using
          data.sourceMass.rich_mass_lower)
        (2 * bins * popularCount)
    _ = (6 * bins * popularCount) * data.sourceMass.shading.mass := by ring

/-- Division-free form used by the all-slab mass aggregation. -/
theorem sourceSlab_weighted_mass_return_whole :
    (((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
          twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
      Kakeya.realRpowENN data.output.ready.ready.deltaGraph (finalLoss - 1)) *
      volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) ≤
    (24 * (prepared.volumePopular.popular.bins : ENNReal) *
      (prepared.volumePopular.popular.heightIndices.card : ENNReal)) *
        data.sourceMass.shading.mass := by
  have hsourceToContinuous :
      volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) ≤
        2 * volume prepared.volumePopular.continuous.popularRegion := by
    calc
      volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) =
          volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) / 2 +
            volume (pullback.standardSqrtSlabSourceRegion
              heightIndex.1.1) / 2 :=
        (ENNReal.add_halves _).symm
      _ ≤ volume prepared.volumePopular.continuous.popularRegion +
          volume prepared.volumePopular.continuous.popularRegion := by
        gcongr
        · exact prepared.volumePopular.continuous.popularRegion_half_volume
        · exact prepared.volumePopular.continuous.popularRegion_half_volume
      _ = 2 * volume prepared.volumePopular.continuous.popularRegion := by ring
  have hcontinuousToJoint :
      volume prepared.volumePopular.continuous.popularRegion ≤
        2 * (prepared.volumePopular.popular.bins : ENNReal) *
          volume prepared.volumePopular.jointSourceSet := by
    rw [← prepared.volumePopular.sourcePopularShading_union]
    calc
      volume prepared.volumePopular.sourcePopularShading.union =
          volume prepared.volumePopular.sourcePopularShading.union / 2 +
            volume prepared.volumePopular.sourcePopularShading.union / 2 :=
        (ENNReal.add_halves _).symm
      _ ≤ ((prepared.volumePopular.popular.bins : ENNReal) *
            volume prepared.volumePopular.jointSourceSet) +
          ((prepared.volumePopular.popular.bins : ENNReal) *
            volume prepared.volumePopular.jointSourceSet) := by
        gcongr
        · simpa only [
            PureWZ2Node05V4RichSourceVolumePopularHeightData.jointSourceSet]
            using prepared.volumePopular.popular.retained_volume
        · simpa only [
            PureWZ2Node05V4RichSourceVolumePopularHeightData.jointSourceSet]
            using prepared.volumePopular.popular.retained_volume
      _ = 2 * (prepared.volumePopular.popular.bins : ENNReal) *
          volume prepared.volumePopular.jointSourceSet := by ring
  have hpopularVolume :
      volume prepared.volumePopular.jointSourceSet ≤
        2 * (prepared.volumePopular.popular.heightIndices.card : ENNReal) *
          prepared.volumePopular.popular.layerMass := by
    rw [PureWZ2Node05V4RichSourceVolumePopularHeightData.jointSourceSet,
      prepared.volumePopular.popular.volume_eq_sum]
    calc
      (∑ selectedHeight ∈
          prepared.volumePopular.popular.heightIndices,
        volume (prepared.volumePopular.sourcePopularShading.union ∩
          wz1Lemma23HeightSlab (256 * rho) selectedHeight)) ≤
        ∑ _selectedHeight ∈
          prepared.volumePopular.popular.heightIndices,
            2 * prepared.volumePopular.popular.layerMass := by
          exact Finset.sum_le_sum fun selectedHeight hselectedHeight =>
            (prepared.volumePopular.popular.layer_volume_band
              selectedHeight hselectedHeight).2
      _ = 2 * (prepared.volumePopular.popular.heightIndices.card : ENNReal) *
          prepared.volumePopular.popular.layerMass := by
        simp [Finset.sum_const]
        ring
  have hrich :
      Kakeya.realRpowENN data.output.ready.ready.deltaGraph (finalLoss - 1) ≤
        (data.output.richHeightIndices.card : ENNReal) := by
    rw [data.output.richHeightIndices_card]
    exact data.output.lineData.richF_card
  let floor : ENNReal :=
    (twoScale.first.fourDegreeReceipts.fineDegreeFloor *
      twoScale.first.fourDegreeReceipts.muFine : ℕ)
  let richFloor : ENNReal :=
    Kakeya.realRpowENN data.output.ready.ready.deltaGraph (finalLoss - 1)
  let popularCount : ENNReal :=
    prepared.volumePopular.popular.heightIndices.card
  let bins : ENNReal := prepared.volumePopular.popular.bins
  calc
    (floor * richFloor) *
          volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) ≤
        (floor * richFloor) *
          (2 * volume prepared.volumePopular.continuous.popularRegion) := by
      gcongr
    _ ≤ (floor * richFloor) *
          (2 * (2 * bins *
            volume prepared.volumePopular.jointSourceSet)) := by
      gcongr
    _ = (floor * richFloor) *
          (4 * bins *
            volume prepared.volumePopular.jointSourceSet) := by ring
    _ ≤ (floor * richFloor) *
          (4 * bins * (2 * popularCount *
            prepared.volumePopular.popular.layerMass)) := by
      gcongr
    _ ≤ (floor * (data.output.richHeightIndices.card : ENNReal)) *
          (4 * bins * (2 * popularCount *
            prepared.volumePopular.popular.layerMass)) := by
      gcongr
    _ = (8 * bins * popularCount) *
          (floor * ((data.output.richHeightIndices.card : ENNReal) *
            prepared.volumePopular.popular.layerMass)) := by ring
    _ ≤ (8 * bins * popularCount) *
          (3 * data.sourceMass.shading.mass) := by
      exact mul_le_mul_right
        (by simpa [floor, Nat.cast_mul] using
          data.sourceMass.rich_mass_lower)
        (8 * bins * popularCount)
    _ = (24 * bins * popularCount) *
          data.sourceMass.shading.mass := by ring

end PureWZ2Node05V4RichJointTheorem52Data

structure PureWZ2Node05V4RichJointWholeCellLiftData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta finalLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {B₀ threshold : ENNReal}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {prepared : PureWZ2Node05V4RichJointPreparedData
      (eta := eta) pullback heightIndex B₀ threshold hbridge}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (data : PureWZ2Node05V4RichJointTheorem52Data prepared projection) where
  cells : Finset WZ2PaperCellIndex :=
    (wz1PaperActiveCells current.grain.shading
      current.grain.extremal.delta_pos).filter fun cell =>
        (wz1PaperGridCube delta cell ∩ data.sourceMass.shading.union).Nonempty
  cells_eq :
    cells = (wz1PaperActiveCells current.grain.shading
      current.grain.extremal.delta_pos).filter fun cell =>
        (wz1PaperGridCube delta cell ∩ data.sourceMass.shading.union).Nonempty
  region : Set Point3 :=
    ⋃ cell ∈ cells, wz1PaperGridCube delta cell
  region_eq :
    region = ⋃ cell ∈ cells, wz1PaperGridCube delta cell
  region_measurable : MeasurableSet region
  shading : WZ1PaperTubeShading current.grain.family
  carrier_eq : ∀ index,
    shading.carrier index = current.grain.shading.carrier index ∩ region
  subshading_current :
    PureWZ2PaperIsSubshading shading current.grain.shading
  union_eq : shading.union = current.grain.shading.union ∩ region
  whole_cells : WZ1PaperIsCubicalShading shading
  sourceCore_subshading :
    PureWZ2PaperIsSubshading data.sourceMass.shading shading
  sourceCore_mass_le : data.sourceMass.shading.mass ≤ shading.mass
  point_near_sourceCore :
    ∀ point ∈ shading.union,
      ∃ anchor ∈ data.sourceMass.shading.union,
        dist point anchor < 2 * delta
  slope_approximation :
    ∀ point ∈ shading.union,
      |current.grain.globalGrains.slope (point (2 : Fin 3)) -
          data.output.lineData.L_S (point (2 : Fin 3))| ≤
        5 * prepared.separated.graphScale

namespace PureWZ2Node05V4RichJointTheorem52Data

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta finalLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {B₀ threshold : ENNReal}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {prepared : PureWZ2Node05V4RichJointPreparedData
      (eta := eta) pullback heightIndex B₀ threshold hbridge}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (data : PureWZ2Node05V4RichJointTheorem52Data prepared projection)

theorem wholeCellLift :
    Nonempty (PureWZ2Node05V4RichJointWholeCellLiftData data) := by
  let cells :=
    (wz1PaperActiveCells current.grain.shading
      current.grain.extremal.delta_pos).filter fun cell =>
        (wz1PaperGridCube delta cell ∩ data.sourceMass.shading.union).Nonempty
  let region : Set Point3 :=
    ⋃ cell ∈ cells, wz1PaperGridCube delta cell
  have hregionMeas : MeasurableSet region :=
    MeasurableSet.biUnion cells.finite_toSet.countable
      (fun cell _ => wz1PaperGridCube_measurable cell)
  let shading : WZ1PaperTubeShading current.grain.family :=
    { carrier := fun index => current.grain.shading.carrier index ∩ region
      measurable_carrier := fun index =>
        (current.grain.shading.measurable_carrier index).inter hregionMeas
      subset_body := fun index => Set.inter_subset_left.trans
        (current.grain.shading.subset_body index) }
  have hunion :
      shading.union = current.grain.shading.union ∩ region := by
    ext point
    constructor
    · rintro ⟨index, hsource, hregion⟩
      exact ⟨⟨index, hsource⟩, hregion⟩
    · rintro ⟨⟨index, hsource⟩, hregion⟩
      exact ⟨index, hsource, hregion⟩
  have hcoreCarrier :
      PureWZ2PaperIsSubshading data.sourceMass.shading shading := by
    intro index point hpoint
    have hcurrent := data.sourceMass.subshading_current index hpoint
    have hsourceUnion : point ∈ data.sourceMass.shading.union :=
      ⟨index, hpoint⟩
    have hcurrentUnion : point ∈ current.grain.shading.union :=
      ⟨index, hcurrent⟩
    have hactive :
        wz1PaperGridIndex delta point ∈
          wz1PaperActiveCells current.grain.shading
            current.grain.extremal.delta_pos := by
      rw [current.grain.cubical.union_eq_activeCells
        current.grain.extremal.delta_pos] at hcurrentUnion
      rcases Set.mem_iUnion₂.mp hcurrentUnion with
        ⟨cell, hcell, hpointCell⟩
      have hcellEq : cell = wz1PaperGridIndex delta point :=
        (mem_wz1PaperGridCube delta cell point).mp hpointCell |>.symm
      rwa [← hcellEq]
    have hcell :
        wz1PaperGridIndex delta point ∈ cells := by
      change wz1PaperGridIndex delta point ∈
        (wz1PaperActiveCells current.grain.shading
          current.grain.extremal.delta_pos).filter _
      rw [Finset.mem_filter]
      exact ⟨hactive, point,
        (mem_wz1PaperGridCube delta _ point).mpr rfl, hsourceUnion⟩
    exact ⟨hcurrent, Set.mem_iUnion₂.mpr
      ⟨wz1PaperGridIndex delta point, hcell,
        (mem_wz1PaperGridCube delta _ point).mpr rfl⟩⟩
  have hwhole : WZ1PaperIsCubicalShading shading := by
    intro index point hpoint other hother
    have hsourceOther :=
      current.grain.cubical index point hpoint.1 hother
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨cell, hcell, hpointCell⟩
    have hcellEq : cell = wz1PaperGridIndex delta point :=
      (mem_wz1PaperGridCube delta cell point).mp hpointCell |>.symm
    exact ⟨hsourceOther, Set.mem_iUnion₂.mpr
      ⟨cell, hcell, by simpa [hcellEq] using hother⟩⟩
  have hnear :
      ∀ point ∈ shading.union,
        ∃ anchor ∈ data.sourceMass.shading.union,
          dist point anchor < 2 * delta := by
    intro point hpoint
    rw [hunion] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨cell, hcell, hpointCell⟩
    change cell ∈
      (wz1PaperActiveCells current.grain.shading
        current.grain.extremal.delta_pos).filter _ at hcell
    rcases (Finset.mem_filter.mp hcell).2 with
      ⟨anchor, hanchorCell, hanchorCore⟩
    exact ⟨anchor, hanchorCore,
      wz1_paper_grid_cube_diameter_lt_two_rho
        current.grain.extremal.delta_pos hpointCell hanchorCell⟩
  have hslope :
      ∀ point ∈ shading.union,
        |current.grain.globalGrains.slope (point (2 : Fin 3)) -
            data.output.lineData.L_S (point (2 : Fin 3))| ≤
          5 * prepared.separated.graphScale := by
    intro point hpoint
    rcases hnear point hpoint with ⟨anchor, hanchor, hdist⟩
    have hpointCurrent : point ∈ current.grain.shading.union := by
      rw [hunion] at hpoint
      exact hpoint.1
    have hanchorCurrent :
        anchor ∈ current.grain.shading.union :=
      data.sourceMass.subshading_current.union_subset hanchor
    have hpointRange : point (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 := by
      have hbox := shading_union_subset_axisBox hpointCurrent
      simpa [Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2
    have hanchorRange : anchor (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 := by
      have hbox := shading_union_subset_axisBox hanchorCurrent
      simpa [Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2
    have hcoordinateLe := PiLp.dist_apply_le point anchor (2 : Fin 3)
    have hcoordinate :
        |point (2 : Fin 3) - anchor (2 : Fin 3)| ≤ 2 * delta := by
      have hcoordinate' :
          |point (2 : Fin 3) - anchor (2 : Fin 3)| ≤ dist point anchor := by
        simpa [Real.dist_eq] using hcoordinateLe
      exact hcoordinate'.trans hdist.le
    have hslopeDiff :
        |current.grain.globalGrains.slope (point (2 : Fin 3)) -
            current.grain.globalGrains.slope (anchor (2 : Fin 3))| ≤
          2 * delta := by
      have hlip :=
        current.grain.globalGrains.slope_lipschitz.dist_le_mul
          (point (2 : Fin 3)) hpointRange
          (anchor (2 : Fin 3)) hanchorRange
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
      exact hlip.trans hcoordinate
    have hlineDiff :
        |data.output.lineData.L_S (anchor (2 : Fin 3)) -
            data.output.lineData.L_S (point (2 : Fin 3))| ≤
          4 * delta := by
      rw [data.output.lineData.L_S_eq]
      have hslopeBound := data.output.lineData.L_S_slope_bound
      calc
        |(data.output.lineData.L_S_slope * anchor (2 : Fin 3) +
              data.output.lineData.L_S_intercept) -
            (data.output.lineData.L_S_slope * point (2 : Fin 3) +
              data.output.lineData.L_S_intercept)| =
            |data.output.lineData.L_S_slope| *
              |anchor (2 : Fin 3) - point (2 : Fin 3)| := by
          rw [show
            (data.output.lineData.L_S_slope * anchor (2 : Fin 3) +
                data.output.lineData.L_S_intercept) -
              (data.output.lineData.L_S_slope * point (2 : Fin 3) +
                data.output.lineData.L_S_intercept) =
              data.output.lineData.L_S_slope *
                (anchor (2 : Fin 3) - point (2 : Fin 3)) by ring, abs_mul]
        _ ≤ 2 * (2 * delta) := by
          gcongr
          simpa [abs_sub_comm] using hcoordinate
        _ = 4 * delta := by ring
    have hanchorApprox :=
      data.sourceMass_slope_approximation anchor hanchor
    calc
      _ ≤
          |current.grain.globalGrains.slope (point (2 : Fin 3)) -
            current.grain.globalGrains.slope (anchor (2 : Fin 3))| +
          |current.grain.globalGrains.slope (anchor (2 : Fin 3)) -
            data.output.lineData.L_S (anchor (2 : Fin 3))| +
          |data.output.lineData.L_S (anchor (2 : Fin 3)) -
            data.output.lineData.L_S (point (2 : Fin 3))| := by
        have hone := abs_sub_le
          (current.grain.globalGrains.slope (point (2 : Fin 3)))
          (current.grain.globalGrains.slope (anchor (2 : Fin 3)))
          (data.output.lineData.L_S (point (2 : Fin 3)))
        have htwo := abs_sub_le
          (current.grain.globalGrains.slope (anchor (2 : Fin 3)))
          (data.output.lineData.L_S (anchor (2 : Fin 3)))
          (data.output.lineData.L_S (point (2 : Fin 3)))
        linarith
      _ ≤ 2 * delta +
          (9 / 2 : ℝ) * prepared.separated.graphScale +
          4 * delta := by
        gcongr
      _ ≤ 5 * prepared.separated.graphScale := by
        have hdeltaRho : delta ≤ rho := by
          rw [← pullback.rhoRequested_eq]
          exact rhoRequested.property.1
        have hscale :
            prepared.separated.graphScale = 256 * rho :=
          prepared.graphScale_eq
        rw [hscale]
        nlinarith [current.grain.extremal.delta_pos]
  exact ⟨{
    cells := cells
    cells_eq := rfl
    region := region
    region_eq := rfl
    region_measurable := hregionMeas
    shading := shading
    carrier_eq := fun _ => rfl
    subshading_current := fun _ => Set.inter_subset_left
    union_eq := hunion
    whole_cells := hwhole
    sourceCore_subshading := hcoreCarrier
    sourceCore_mass_le := by
      apply Finset.sum_le_sum
      intro index _
      exact measure_mono (hcoreCarrier index)
    point_near_sourceCore := hnear
    slope_approximation := hslope
  }⟩

end PureWZ2Node05V4RichJointTheorem52Data

structure PureWZ2Node05V4RichJointBlockTrapezoid
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta finalLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {B₀ threshold : ENNReal}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {prepared : PureWZ2Node05V4RichJointPreparedData
      (eta := eta) pullback heightIndex B₀ threshold hbridge}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    {data : PureWZ2Node05V4RichJointTheorem52Data prepared projection}
    (lift : PureWZ2Node05V4RichJointWholeCellLiftData data) where
  scale : ℝ := 5 * prepared.separated.graphScale
  scale_eq : scale = 5 * prepared.separated.graphScale
  scale_le_one : scale ≤ 1
  trapezoid : WZ1VerticalTrapezoid
  height_eq : trapezoid.height = scale
  slope_bound : |trapezoid.slope| ≤ 2
  core_eq : trapezoid.core = Set.Icc
    ((heightIndex.1.1 : ℝ) * Real.sqrt rho - 2 * delta)
    ((heightIndex.1.1 : ℝ) * Real.sqrt rho + Real.sqrt rho + 2 * delta)
  length_eq :
    trapezoid.length = Real.sqrt rho + 4 * delta
  length_bounds :
    Real.rpow scale (1 / 2 + finalLoss) ≤ trapezoid.length ∧
      trapezoid.length ≤ Real.sqrt scale
  active_height_coverage :
    ∀ z, horizontalSlice lift.shading.union z ≠ ∅ →
      z ∈ trapezoid.core
  slope_approximation :
    ∀ z ∈ trapezoid.core,
      horizontalSlice lift.shading.union z ≠ ∅ →
        |current.grain.globalGrains.slope z - trapezoid.affine z| ≤ scale

namespace PureWZ2Node05V4RichJointWholeCellLiftData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta finalLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {B₀ threshold : ENNReal}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {prepared : PureWZ2Node05V4RichJointPreparedData
      (eta := eta) pullback heightIndex B₀ threshold hbridge}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    {data : PureWZ2Node05V4RichJointTheorem52Data prepared projection}
    (lift : PureWZ2Node05V4RichJointWholeCellLiftData data)

theorem blockTrapezoid
    (hscaleOne : 5 * prepared.separated.graphScale ≤ 1)
    (hlengthLower :
      Real.rpow (5 * prepared.separated.graphScale)
          (1 / 2 + finalLoss) ≤ Real.sqrt rho + 4 * delta) :
    Nonempty (PureWZ2Node05V4RichJointBlockTrapezoid lift) := by
  let left := (heightIndex.1.1 : ℝ) * Real.sqrt rho - 2 * delta
  let right :=
    (heightIndex.1.1 : ℝ) * Real.sqrt rho + Real.sqrt rho + 2 * delta
  let scale := 5 * prepared.separated.graphScale
  let trapezoid : WZ1VerticalTrapezoid := {
    left := left
    right := right
    left_lt_right := by
      dsimp only [left, right]
      have hrho : 0 < rho := by
        rw [← pullback.rhoRequested_eq]
        exact twoScale.first.publicSticky.coarse_extremal.delta_pos
      have hdelta := current.grain.extremal.delta_pos
      nlinarith [Real.sqrt_pos.mpr hrho]
    slope := data.output.lineData.L_S_slope
    intercept := data.output.lineData.L_S_intercept
    height := scale
    height_pos := by
      dsimp only [scale]
      exact mul_pos (by norm_num) prepared.separated.graphScale_pos
  }
  have hlength :
      trapezoid.length = Real.sqrt rho + 4 * delta := by
    dsimp only [trapezoid, WZ1VerticalTrapezoid.length, right, left]
    ring
  have hlengthUpper :
      Real.sqrt rho + 4 * delta ≤ Real.sqrt scale := by
    have hrho : 0 < rho := by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos
    have hdeltaRho : delta ≤ rho := by
      rw [← pullback.rhoRequested_eq]
      exact rhoRequested.property.1
    have hrhoOne : rho ≤ 1 := by
      rw [← pullback.rhoRequested_eq]
      exact rhoRequested.property.2
    have hrhoRoot : rho ≤ Real.sqrt rho := by
      nlinarith [Real.sq_sqrt hrho.le, Real.sqrt_nonneg rho]
    have hscale :
        scale = 1280 * rho := by
      dsimp only [scale]
      rw [prepared.graphScale_eq]
      ring
    rw [hscale, Real.sqrt_mul (by norm_num),
      show Real.sqrt (1280 : ℝ) = 16 * Real.sqrt 5 by
        rw [show (1280 : ℝ) = 256 * 5 by norm_num, Real.sqrt_mul (by norm_num)]
        norm_num]
    have hsqrtFive : 1 ≤ Real.sqrt 5 := Real.one_le_sqrt.mpr (by norm_num)
    nlinarith [Real.sqrt_nonneg rho]
  exact ⟨{
    scale := scale
    scale_eq := rfl
    scale_le_one := hscaleOne
    trapezoid := trapezoid
    height_eq := rfl
    slope_bound := data.output.lineData.L_S_slope_bound
    core_eq := rfl
    length_eq := hlength
    length_bounds := by
      rw [hlength]
      exact ⟨hlengthLower, hlengthUpper⟩
    active_height_coverage := by
      intro z hslice
      rcases Set.nonempty_iff_ne_empty.mpr hslice with
        ⟨point, hpoint, hpointHeight⟩
      rcases lift.point_near_sourceCore point hpoint with
        ⟨anchor, hanchor, hdist⟩
      have hanchorSlab :
          anchor ∈ pullback.standardSqrtSlabSourceRegion heightIndex.1.1 := by
        have hslab :=
          data.sourceMass.subshading_slab.union_subset hanchor
        rwa [pullback.standardSqrtSlabSourceShading_union] at hslab
      have hanchorHeight :=
        pullback.standardSqrtSlabSourceRegion_height hanchorSlab
      have hcoordinateLe := PiLp.dist_apply_le point anchor (2 : Fin 3)
      have hcoordinate :
          |point (2 : Fin 3) - anchor (2 : Fin 3)| < 2 * delta := by
        have hcoordinate' :
            |point (2 : Fin 3) - anchor (2 : Fin 3)| ≤ dist point anchor := by
          simpa [Real.dist_eq] using hcoordinateLe
        exact hcoordinate'.trans_lt hdist
      change z ∈ Set.Icc left right
      rw [← hpointHeight]
      rw [abs_lt] at hcoordinate
      exact ⟨by
        dsimp only [left]
        linarith [hanchorHeight.1, hcoordinate.1],
        by
          dsimp only [right]
          linarith [hanchorHeight.2, hcoordinate.2]⟩
    slope_approximation := by
      intro z _hz hslice
      rcases Set.nonempty_iff_ne_empty.mpr hslice with
        ⟨point, hpoint, hpointHeight⟩
      have happ := lift.slope_approximation point hpoint
      rw [hpointHeight] at happ
      rw [show trapezoid.affine z = data.output.lineData.L_S z by
        rw [data.output.lineData.L_S_eq]
        rfl]
      exact happ
  }⟩

end PureWZ2Node05V4RichJointWholeCellLiftData

end Kakeya.Assouad

end
