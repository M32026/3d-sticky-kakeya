import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9SameExtremizerAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PopularShiftedGridCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureFiniteRegularizedRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingFinal

/-!
# Proposition 6.3 M9 genuine mild-rescaling assembly

This module starts the final paper-ordered stage after Lemma 4.12.  Its first
dependent package performs the popular-core restriction and the whole-tube
finite regularization before raw isotropic rediscretization.  Consequently
every source tube used by the raw construction really meets the one common
core, while the same selected family retains pure nearby-scale CWA and the
exact pre-grain maps.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Source-side output of the final mild rescaling.  All later target objects
are definitionally indexed by `regularized.regularized.selected.family`. -/
structure Proposition63M9MildRescalingSourceData
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading)
    (sourceLine : WZ1PaperIsLineClass sourceFamily)
    (sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily)
    (sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3)
    (preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1)
    (hscale : 1 ≤ scale)
    (hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000)
    (levelCount : ℕ)
    (sourceOutputConstant : ENNReal) where
  center : Point3
  boxed : WZ1PaperTubeShading sourceFamily
  center_grid : ∀ coordinate : Fin 3,
    ∃ index : ℤ, center coordinate = (index : ℝ) * sourceDelta
  center_window : center ∈ pureWZ2SourceWindow
  boxed_subshading : PaperIsSubshading boxed sourceShading
  boxed_cubical : WZ1PaperIsCubicalShading boxed
  box_mass :
    ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3) *
        sourceShading.mass ≤ boxed.mass
  boxed_carrier_eq : ∀ index, boxed.carrier index =
    sourceShading.carrier index ∩
      pureWZ2ShiftedOriginGridCore sourceDelta scale center
  sourceDensity : ENNReal
  sourceDensity_eq : sourceDensity =
    ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3) *
      Kakeya.realRpowENN sourceDelta sourceLoss
  selected : Kakeya.Streamlined.TubeSubfamily sourceFamily
  refined : WZ1PaperTubeShading selected.family
  refined_cubical : WZ1PaperIsCubicalShading refined
  refined_sub_boxed : ∀ index, refined.carrier index ⊆
    boxed.carrier (selected.embedding index)
  refined_per_tube : ∀ index,
    (1 / 2 : ENNReal) * sourceDensity *
        Kakeya.realRpowENN sourceDelta 2 ≤
      volume (refined.carrier index)
  selected_nonempty : selected.family.Nonempty
  pure_cwa_nearby : WZ2PaperPureCWAAtNearbyScales
    selected.family sourceOutputConstant
  preGrainSelected : PureWZ2GeneralPreGrainData
    refined sigma sourceLoss Lplane Lslope 1
  preGrainSelected_planeMap_source :
    ∀ point, ∃ sourcePoint,
      preGrainSelected.planeMap point = preGrain.planeMap sourcePoint
  preGrainSelected_slope_eq :
    preGrainSelected.slope = preGrain.slope
  source_meets_core : ∀ index,
    (refined.carrier index ∩
      pureWZ2ShiftedOriginGridCore sourceDelta scale center).Nonempty
  raw : WZ1IsotropicTubeRediscretizationData
    (scale := scale) selected.family
      (proposition63MildRescalingRawSourceShading sourceExtremal.delta_pos
        refined) center
  raw_line_class : WZ1PaperIsLineClass raw.family
  targetShading : WZ1PaperTubeShading
    (proposition63MildRescalingFamily hscale raw)
  targetShading_eq : targetShading =
    proposition63MildRescalingShading hscale raw
      refined
      (pureWZ2ShiftedOriginGridCore sourceDelta scale center)
      sourceExtremal.delta_pos
      (hscaleDeltaSmall.trans_lt (by norm_num))
      (1 / (9 * scale) - 6 * sourceDelta) rfl
      (measurableSet_pureWZ2ShiftedOriginGridCore
        sourceDelta scale center)
      (fun point point_mem coordinate =>
        point_mem ((mem_wz1PaperGridCube sourceDelta _ point).mpr rfl)
          coordinate)
  target_cubical : WZ1PaperIsCubicalShading targetShading

/-- Execute the source-side popular-core and finite regularization stages.
The numerical hypotheses are exactly the finite-CWA and density absorptions
which the final M9 cutoff must provide. -/
theorem proposition63_m9_mild_rescaling_source
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading)
    (sourceLine : WZ1PaperIsLineClass sourceFamily)
    (sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily)
    (sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3)
    (preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1)
    (hscale : 1 ≤ scale)
    (hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000)
    (levelCount : ℕ)
    (hambientTwo : (2 : ENNReal) <
      Kakeya.realRpowENN sourceDelta (-sourceLoss))
    (hlevels : ENNReal.ofReal (1 / sourceDelta) ≤
      Kakeya.realRpowENN sourceDelta (-sourceLoss) ^ levelCount)
    (sourceOutputConstant : ENNReal)
    (houtputTop : sourceOutputConstant ≠ ⊤)
    (hwindow :
      Kakeya.realRpowENN sourceDelta (-sourceLoss) *
          Kakeya.realRpowENN sourceDelta (-sourceLoss) ≤
        sourceOutputConstant)
    (hregularizationAbsorb :
      let density :=
        ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3) *
          Kakeya.realRpowENN sourceDelta sourceLoss
      let degreeConstant :=
        16 * ((levelCount + 1 : ℕ) : ENNReal) *
          (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
            (levelCount + 1)
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
            (levelCount + 2)
      let weight := (1 / 2 : ENNReal) * density
      let cardinalityLoss :=
        (2 * regularizationLoss) *
          (55296 * Kakeya.deltaTubeVolume 1)
      max degreeConstant
          ((weight⁻¹ *
              (Kakeya.realRpowENN sourceDelta (-sourceLoss) *
                cardinalityLoss * degreeConstant)) *
            Kakeya.realRpowENN sourceDelta (-sourceLoss)) ≤
        sourceOutputConstant) :
    Nonempty (Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant) := by
  have sourceDeltaSmallTwelve : sourceDelta ≤ 1 / 12 := by
    have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
    have hsourceLe : sourceDelta ≤ scale * sourceDelta := by
      exact le_mul_of_one_le_left sourceExtremal.delta_pos.le hscale
    exact hsourceLe.trans (hscaleDeltaSmall.trans (by norm_num))
  have sourceDeltaSmallTwentyFour : sourceDelta ≤ 1 / 24 := by
    have hsourceLe : sourceDelta ≤ scale * sourceDelta := by
      exact le_mul_of_one_le_left sourceExtremal.delta_pos.le hscale
    exact hsourceLe.trans (hscaleDeltaSmall.trans (by norm_num))
  rcases popular_shifted_grid_core_shading sourceShading
      sourceExtremal.delta_pos sourceExtremal.cubical scale hscale
      hscaleDeltaSmall with
    ⟨center, boxed, centerGrid, centerWindow, boxedSub, boxedCubical,
      boxMass, boxedCarrier⟩
  let boxWeight : ENNReal :=
    ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3)
  let sourceDensity : ENNReal :=
    boxWeight * Kakeya.realRpowENN sourceDelta sourceLoss
  have boxWeightPos : 0 < boxWeight := by
    dsimp only [boxWeight]
    apply ENNReal.ofReal_pos.mpr
    have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
    positivity
  have densityZero : sourceDensity ≠ 0 := by
    apply mul_ne_zero
    · exact boxWeightPos.ne'
    · simp [Kakeya.realRpowENN,
        Real.rpow_pos_of_pos sourceExtremal.delta_pos]
  have densityTop : sourceDensity ≠ ⊤ := by
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    simp [Kakeya.realRpowENN]
  have boxedDense :
      sourceDensity * sourceFamily.enncard *
          Kakeya.realRpowENN sourceDelta 2 ≤ boxed.mass := by
    calc
      sourceDensity * sourceFamily.enncard *
            Kakeya.realRpowENN sourceDelta 2 =
          boxWeight *
            (Kakeya.realRpowENN sourceDelta sourceLoss *
              (Kakeya.realRpowENN sourceDelta 2 *
                sourceFamily.enncard)) := by ring
      _ ≤ boxWeight *
          (Kakeya.realRpowENN sourceDelta sourceLoss *
            (wz1PaperBodyFamily sourceFamily).mass) := by
        gcongr
        exact paperBodyFamily_mass_lower_rpow_two sourceExtremal.delta_pos
          sourceDeltaSmallTwelve sourceLine
      _ ≤ boxWeight * sourceShading.mass := by
        gcongr
        exact sourceExtremal.dense
      _ ≤ boxed.mass := by simpa only [boxWeight] using boxMass
  rcases paper_pure_finite_regularized_refinement boxed
      sourceExtremal.delta_pos sourceDeltaSmallTwentyFour
      sourceExtremal.nonempty
      densityZero densityTop sourceLine boxedCubical boxedDense levelCount
      hambientTwo hlevels hwindow houtputTop
      sourceExtremal.cwa_nearby_scales hregularizationAbsorb with
    ⟨regularized⟩
  letI : ∀ coordinate, Fintype (regularized.Parent coordinate) :=
    regularized.parent_fintype
  letI : ∀ coordinate, DecidableEq (regularized.Parent coordinate) :=
    regularized.parent_decidableEq
  let boxedPreGrain := preGrain.restrict boxedSub
  let selectedPreGrain :=
    boxedPreGrain.restrictSubfamily regularized.regularized.selected
  have refinedSub : PaperIsSubshading regularized.regularized.refined
      (restrictPaperShading regularized.regularized.selected boxed) :=
    regularized.regularized.subshading
  let preGrainSelected := selectedPreGrain.restrict refinedSub
  have sourceMeetsCore : ∀ index,
      (regularized.regularized.refined.carrier index ∩
        pureWZ2ShiftedOriginGridCore sourceDelta scale center).Nonempty := by
    intro index
    have lowerPositive : 0 <
        (1 / 2 : ENNReal) * sourceDensity *
          Kakeya.realRpowENN sourceDelta 2 := by
      apply ENNReal.mul_pos
      · exact (ENNReal.mul_pos (by norm_num) densityZero).ne'
      · simp only [Kakeya.realRpowENN]
        exact (ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos sourceExtremal.delta_pos 2)).ne'
    have carrierPositive : 0 < volume
        (regularized.regularized.refined.carrier index) :=
      lowerPositive.trans_le (regularized.regularized.per_tube index)
    rcases nonempty_of_measure_ne_zero carrierPositive.ne' with
      ⟨point, pointMem⟩
    have pointBoxed : point ∈
        boxed.carrier (regularized.regularized.selected.embedding index) :=
      regularized.regularized.subshading index pointMem
    have pointCore : point ∈
        pureWZ2ShiftedOriginGridCore sourceDelta scale center := by
      rw [boxedCarrier] at pointBoxed
      exact pointBoxed.2
    exact ⟨point, pointMem, pointCore⟩
  have hscaleDeltaOne : scale * sourceDelta ≤ 1 :=
    hscaleDeltaSmall.trans (by norm_num)
  rcases proposition63_mild_rescaling_raw sourceExtremal.delta_pos hscale
      hscaleDeltaOne regularized.selected_nonempty
      regularized.regularized.refined center with ⟨raw⟩
  have hscaleDeltaStrict : scale * sourceDelta < 1 / 54 :=
    hscaleDeltaSmall.trans_lt (by norm_num)
  have rawLine := proposition63_mild_rescaling_raw_line_class
    sourceExtremal.delta_pos hscale hscaleDeltaStrict
    regularized.regularized.refined
    (sourceLine.subfamily regularized.regularized.selected) center
    sourceMeetsCore raw
  let core := pureWZ2ShiftedOriginGridCore sourceDelta scale center
  let width : ℝ := 1 / (9 * scale) - 6 * sourceDelta
  have coreBox : ∀ point ∈ core, ∀ coordinate : Fin 3,
      |point coordinate - center coordinate| ≤ width := by
    intro point pointMem coordinate
    exact pointMem
      ((mem_wz1PaperGridCube sourceDelta _ point).mpr rfl) coordinate
  let targetShading := proposition63MildRescalingShading hscale raw
    regularized.regularized.refined core sourceExtremal.delta_pos
    hscaleDeltaStrict width rfl
    (measurableSet_pureWZ2ShiftedOriginGridCore
      sourceDelta scale center) coreBox
  have targetCubical : WZ1PaperIsCubicalShading targetShading :=
    proposition63MildRescalingShading_cubical hscale raw
      regularized.regularized.refined core sourceExtremal.delta_pos
      hscaleDeltaStrict width rfl
      (measurableSet_pureWZ2ShiftedOriginGridCore
        sourceDelta scale center) coreBox centerGrid
      regularized.regularized.refined_cubical
      (pureWZ2ShiftedOriginGridCore_whole_cell
        sourceDelta scale center)
  exact ⟨{
    center := center
    boxed := boxed
    center_grid := centerGrid
    center_window := centerWindow
    boxed_subshading := boxedSub
    boxed_cubical := boxedCubical
    box_mass := boxMass
    boxed_carrier_eq := boxedCarrier
    sourceDensity := sourceDensity
    sourceDensity_eq := rfl
    selected := regularized.regularized.selected
    refined := regularized.regularized.refined
    refined_cubical := regularized.regularized.refined_cubical
    refined_sub_boxed := regularized.regularized.subshading
    refined_per_tube := regularized.regularized.per_tube
    selected_nonempty := regularized.selected_nonempty
    pure_cwa_nearby := regularized.pure_cwa_nearby
    preGrainSelected := preGrainSelected
    preGrainSelected_planeMap_source := by
      intro point
      refine ⟨⟨point, ?_⟩, rfl⟩
      rcases point.property with ⟨index, pointMem⟩
      exact ⟨regularized.regularized.selected.embedding index,
        boxedSub _ (regularized.regularized.subshading index pointMem)⟩
    preGrainSelected_slope_eq := rfl
    source_meets_core := sourceMeetsCore
    raw := raw
    raw_line_class := rawLine
    targetShading := targetShading
    targetShading_eq := rfl
    target_cubical := targetCubical
  }⟩

namespace Proposition63M9MildRescalingSourceData

/-- Build all target parent families from one finite nearby schedule on the
selected source family.  Each target radius is the exact geometric budget,
and all line, distinctness, midpoint, and center hypotheses are inherited
from the one dependent source package. -/
noncomputable def parentSchedule
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    (data : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant)
    {scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    (sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := data.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount) :
    Proposition63MildRescalingFiniteParentScheduleData
      hscale data.raw sourceSchedule :=
  proposition63_mild_rescaling_finite_parent_schedule hscale data.raw
    sourceSchedule
    (fun coordinate => proposition63MildRescalingTargetRho
      sourceDelta (sourceSchedule.witness coordinate).rho scale)
    (fun coordinate =>
      Proposition63MildRescalingParentCoverData.ofSource
        (sourceSchedule.witness coordinate).scaleData hscale data.raw
        data.selected_nonempty (sourceLine.subfamily data.selected)
        (sourceDistinct.subfamily data.selected)
        (fun source => by
          rw [data.selected.tube_eq]
          exact sourceMidpoint (data.selected.embedding source))
        data.raw_line_class (data.center_window 2))

end Proposition63M9MildRescalingSourceData

/-- The purely combinatorial target-side output after constructing the
source-scale parents, deleting ordinary containment conflicts, selecting one
common strongly separated family, and regularizing every target full fiber. -/
structure Proposition63M9MildRescalingTargetData
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    (sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant)
    {scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    (sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount) where
  parentSchedule : Proposition63MildRescalingFiniteParentScheduleData
    hscale sourceData.raw sourceSchedule
  cleanup : Proposition63MildRescalingCleanupData hscale sourceData.raw
    sourceData.targetShading
  weight : Fin sourceData.selected.family.card → ENNReal
  weight_eq : weight = fun index =>
    if index ∈ cleanup.selectedIndices then
      volume (sourceData.targetShading.carrier index) else 0
  selection : Proposition63FiniteStrongParentSelectionData
    weight sourceSchedule.scaleCount
    (fun coordinate => Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card)
    parentSchedule.parent parentSchedule.conflict parentSchedule.degree
  selection_subset_cleanup : selection.selected ⊆ cleanup.selectedIndices
  selection_mass :
    (∑ index ∈ cleanup.selectedIndices,
        volume (sourceData.targetShading.carrier index)) ≤
      (parentSchedule.degree : ENNReal) ^ sourceSchedule.scaleCount *
        ∑ index ∈ selection.selected,
          volume (sourceData.targetShading.carrier index)
  fiberRegularized : WZ2PaperFiniteParentRegularizationData
    (parentSchedule.selectedTargetShading selection
      sourceData.targetShading)
    sourceSchedule.scaleCount
    (fun coordinate => Fin
      (parentSchedule.selectedParents selection coordinate).family.card)
    (parentSchedule.selectedFiberParent selection)

namespace Proposition63M9MildRescalingTargetData

/-- Ordinary essential distinctness of the final family is inherited through
the cleanup selection and the later fiber regularization. -/
theorem finalDistinct
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (targetData : Proposition63M9MildRescalingTargetData
      sourceData sourceSchedule) :
    WZ2PaperOrdinaryIsEssentiallyDistinct
      (targetData.parentSchedule.fiberRegularizedSubfamily
        targetData.fiberRegularized).family :=
  (targetData.parentSchedule.selectedTarget_ordinaryDistinct_of_cleanup
      targetData.selection targetData.cleanup
      targetData.selection_subset_cleanup).subfamily
    (targetData.parentSchedule.fiberRegularizedSubfamily
      targetData.fiberRegularized)

/-- The final family remains in the target paper line class. -/
theorem finalLineClass
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (targetData : Proposition63M9MildRescalingTargetData
      sourceData sourceSchedule) :
    WZ1PaperIsLineClass
      (targetData.parentSchedule.fiberRegularizedSubfamily
        targetData.fiberRegularized).family :=
  targetData.parentSchedule.finalFamily_lineClass
    targetData.fiberRegularized sourceData.raw_line_class

/-- Exact source index of a tube surviving both target selections. -/
def finalSourceIndex
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (targetData : Proposition63M9MildRescalingTargetData
      sourceData sourceSchedule) :
    Fin (targetData.parentSchedule.fiberRegularizedSubfamily
      targetData.fiberRegularized).family.card →
      Fin sourceData.selected.family.card :=
  targetData.parentSchedule.fiberRegularizedSourceIndex
    targetData.fiberRegularized

/-- Direction provenance from the final target family back to its exact
source line. -/
theorem finalDirection
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (targetData : Proposition63M9MildRescalingTargetData
      sourceData sourceSchedule)
    (index : Fin (targetData.parentSchedule.fiberRegularizedSubfamily
      targetData.fiberRegularized).family.card) :
    ((targetData.parentSchedule.fiberRegularizedSubfamily
      targetData.fiberRegularized).family.tube index).direction =
      wz1PaperDirection
        (sourceData.selected.family.tube
          (targetData.finalSourceIndex index)) := by
  rw [(targetData.parentSchedule.fiberRegularizedSubfamily
    targetData.fiberRegularized).tube_eq,
    (targetData.parentSchedule.selectedTarget targetData.selection).tube_eq]
  exact proposition63MildRescalingFamily_direction_provenance
    hscale sourceData.raw _

/-- Every final shaded carrier is contained in the isotropic image of its
exact source carrier. -/
theorem finalCarrierSubsetImage
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (targetData : Proposition63M9MildRescalingTargetData
      sourceData sourceSchedule)
    (index : Fin (targetData.parentSchedule.fiberRegularizedSubfamily
      targetData.fiberRegularized).family.card) :
    (targetData.parentSchedule.finalShading
      targetData.fiberRegularized).carrier index ⊆
      wz1IsotropicRescalingMap sourceData.center scale ''
        sourceData.refined.carrier (targetData.finalSourceIndex index) := by
  intro point pointMem
  let ambientIndex := (targetData.parentSchedule.selectedTarget
    targetData.selection).embedding
      ((targetData.parentSchedule.fiberRegularizedSubfamily
        targetData.fiberRegularized).embedding index)
  have targetMem : point ∈
      sourceData.targetShading.carrier ambientIndex := pointMem
  rw [sourceData.targetShading_eq] at targetMem
  rcases targetMem with ⟨sourcePoint, sourcePointMem, hpoint⟩
  exact ⟨sourcePoint, sourcePointMem.1, hpoint⟩

/-- The final shading union lies in the isotropic image of the exact selected
source shading. -/
theorem finalUnionSubsetImage
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (targetData : Proposition63M9MildRescalingTargetData
      sourceData sourceSchedule) :
    (targetData.parentSchedule.finalShading
      targetData.fiberRegularized).union ⊆
      wz1IsotropicRescalingMap sourceData.center scale ''
        sourceData.refined.union :=
  targetData.parentSchedule.finalShading_union_subset_image
    sourceData.targetShading_eq targetData.fiberRegularized

/-- Both finite target restrictions preserve cubicality. -/
theorem finalCubical
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (targetData : Proposition63M9MildRescalingTargetData
      sourceData sourceSchedule) :
    WZ1PaperIsCubicalShading (targetData.parentSchedule.finalShading
      targetData.fiberRegularized) :=
  targetData.parentSchedule.finalShading_cubical
    targetData.fiberRegularized sourceData.target_cubical

/-- Final assembly once the remaining scalar CWA, density, volume, and AD
absorptions have been paid.  All geometric and index-provenance inputs are
discharged from the dependent source/target records. -/
theorem finalGrainConfiguration
    {sourceDelta sigma sourceLoss outputLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (targetData : Proposition63M9MildRescalingTargetData
      sourceData sourceSchedule)
    (targetConstant : ENNReal)
    (hconstantBudget :
      max (targetData.parentSchedule.fiberRegularizationConstant
          targetData.selection)
        (targetData.parentSchedule.actualJohnScheduleConstant
          targetData.fiberRegularized) ≤ targetConstant)
    (htargetFinite : WZ2PaperFiniteErrorConstant targetConstant)
    (htargetWindow : ∀ target :
      WZ2PaperRequestedScale (scale * sourceDelta),
      ENNReal.ofReal
          (targetData.parentSchedule.targetRho
            (sourceSchedule.representative
              (proposition63MildRescalingSourceRequest
                sourceExtremal.delta_pos hscale target))) <
        targetConstant * ENNReal.ofReal target.1)
    (hfinalCWAAbsorb : (4 : ENNReal) * targetConstant ≤
      Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss))
    (hdensityAbsorb :
      (((proposition63MildRescalingConflictDegree sourceDelta scale + 1 :
          ℕ) : ENNReal) *
        (targetData.parentSchedule.degree : ENNReal) ^
          sourceSchedule.scaleCount *
        ((8 : ENNReal) *
          (Nat.log 2
            (2 * (targetData.parentSchedule.selectedTarget
              targetData.selection).family.card) + 1 : ENNReal) ^
            (sourceSchedule.scaleCount + 1))) *
          Kakeya.realRpowENN (scale * sourceDelta) outputLoss ≤
        ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
          ENNReal.ofReal scale *
          ((1 / 2 : ENNReal) * sourceData.sourceDensity)))
    (hvolumeAbsorb : ENNReal.ofReal (scale ^ 3) *
        Kakeya.realRpowENN sourceDelta (sigma - sourceLoss) ≤
      Kakeya.realRpowENN (scale * sourceDelta) (sigma - outputLoss))
    (hsourceLoss : 0 < sourceLoss)
    (hsourceOutput : sourceLoss < outputLoss)
    (hADAbsorb : Real.rpow sourceDelta (outputLoss - sourceLoss) ≤
      Real.rpow scale (-outputLoss))
    (hplaneScale :
      (Lplane : ℝ) ≤ scale)
    (hslopeScale :
      (Lslope : ℝ) ≤ scale)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    Nonempty (PureWZ2GrainConfiguration sigma outputLoss
      (scale * sourceDelta)) := by
  rcases
      Proposition63MildRescalingFiniteParentScheduleData.Proposition63MildRescalingFiniteParentScheduleData.toFiniteCWAData
        targetData.parentSchedule targetData.fiberRegularized
        targetConstant hconstantBudget with
    ⟨cwa⟩
  have targetRho : ∀ coordinate,
      scale * (sourceSchedule.witness coordinate).rho ≤
        targetData.parentSchedule.targetRho coordinate := by
    intro coordinate
    have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
    have hrhoPos :=
      (sourceSchedule.witness coordinate).scaleData.rho_pos
    exact le_trans
      (show scale * (sourceSchedule.witness coordinate).rho ≤
          proposition63MildRescalingTargetRho sourceDelta
            (sourceSchedule.witness coordinate).rho scale by
        unfold proposition63MildRescalingTargetRho
        nlinarith [sourceExtremal.delta_pos])
      (targetData.parentSchedule.parentCover coordinate).target_rho_budget
  have targetSmall : scale * sourceDelta ≤ 1 / 24 :=
    hscaleDeltaSmall.trans (by norm_num)
  have targetSupport := targetData.parentSchedule.finalFamily_isInUnitBall
    targetData.fiberRegularized sourceExtremal.delta_pos
    (hscaleDeltaSmall.trans (by norm_num)) sourceData.raw_line_class
  have targetNearby := cwa.toNearbyScales targetData.finalDistinct
    targetRho htargetFinite htargetWindow
  have targetNearbyFinal : WZ2PaperPureCWAAtNearbyScales
      (targetData.parentSchedule.fiberRegularizedSubfamily
        targetData.fiberRegularized).family
      (Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss)) :=
    targetNearby.mono
      (calc
        targetConstant = 1 * targetConstant := (one_mul _).symm
        _ ≤ 4 * targetConstant := by gcongr; norm_num
        _ ≤ Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss) :=
          hfinalCWAAbsorb)
      (by simp [Kakeya.realRpowENN])
  have targetTop := targetData.parentSchedule.finalTopLevelCWA cwa
    targetData.finalDistinct targetRho htargetFinite htargetWindow
    targetSmall targetSupport hfinalCWAAbsorb
  have targetCubical := targetData.finalCubical
  have targetDenseBeforeSelections :
      sourceData.targetShading.IsLambdaDense
        ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
          ENNReal.ofReal scale *
          ((1 / 2 : ENNReal) * sourceData.sourceDensity)) := by
    rw [sourceData.targetShading_eq]
    apply proposition63MildRescalingShading_dense hscale sourceData.raw
      sourceData.refined
      (pureWZ2ShiftedOriginGridCore sourceDelta scale sourceData.center)
      sourceExtremal.delta_pos
      (hscaleDeltaSmall.trans_lt (by norm_num))
      (1 / (9 * scale) - 6 * sourceDelta) rfl
      (measurableSet_pureWZ2ShiftedOriginGridCore
        sourceDelta scale sourceData.center)
      (fun point pointMem coordinate =>
        pointMem
          ((mem_wz1PaperGridCube sourceDelta _ point).mpr rfl) coordinate)
      (fun index point pointMem => by
        have pointBoxed := sourceData.refined_sub_boxed index pointMem
        rw [sourceData.boxed_carrier_eq] at pointBoxed
        exact pointBoxed.2) sourceData.raw_line_class
      ((1 / 2 : ENNReal) * sourceData.sourceDensity)
      sourceData.refined_per_tube
  have parentDegreePos : 0 < targetData.parentSchedule.degree := by
    let coordinate : Fin sourceSchedule.scaleCount :=
      ⟨0, sourceSchedule.scaleCount_pos⟩
    have degreeLower := targetData.parentSchedule.parent_degree coordinate
    have localDegreePos : 0 <
        (targetData.parentSchedule.parentCover coordinate).parentConflictDegree := by
      unfold Proposition63MildRescalingParentCoverData.parentConflictDegree
      positivity
    omega
  have selectionLossPos : 0 <
      ((proposition63MildRescalingConflictDegree sourceDelta scale + 1 :
          ℕ) : ENNReal) *
        (targetData.parentSchedule.degree : ENNReal) ^
          sourceSchedule.scaleCount *
        ((8 : ENNReal) *
          (Nat.log 2
            (2 * (targetData.parentSchedule.selectedTarget
              targetData.selection).family.card) + 1 : ENNReal) ^
            (sourceSchedule.scaleCount + 1)) := by
    positivity
  have targetDense := targetData.parentSchedule.finalShading_dense_after_cleanup
    targetData.cleanup targetData.selection_mass targetData.fiberRegularized
    ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
      ENNReal.ofReal scale *
      ((1 / 2 : ENNReal) * sourceData.sourceDensity))
    (Kakeya.realRpowENN (scale * sourceDelta) outputLoss)
    targetDenseBeforeSelections selectionLossPos hdensityAbsorb
  have targetFamilyNonempty :
      (proposition63MildRescalingFamily hscale sourceData.raw).Nonempty := by
    change 0 < sourceData.selected.family.card
    exact sourceData.selected_nonempty
  have sourceDensityPos : 0 < sourceData.sourceDensity := by
    rw [sourceData.sourceDensity_eq]
    apply ENNReal.mul_pos
    · apply (ENNReal.ofReal_pos.mpr ?_).ne'
      have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
      positivity
    · simp only [Kakeya.realRpowENN]
      exact (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos sourceExtremal.delta_pos sourceLoss)).ne'
  have targetDensityPos : 0 <
      ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
        ENNReal.ofReal scale *
        ((1 / 2 : ENNReal) * sourceData.sourceDensity)) := by
    have geometryTop :
        (55296 * Kakeya.deltaTubeVolume 1 : ENNReal) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top
    apply ENNReal.mul_pos
    · exact (ENNReal.mul_pos
        (ENNReal.inv_pos.mpr geometryTop).ne'
        (ENNReal.ofReal_pos.mpr
          (lt_of_lt_of_le zero_lt_one hscale)).ne').ne'
    · exact (ENNReal.mul_pos (by norm_num) sourceDensityPos.ne').ne'
  have targetBodyMassPos : 0 <
      (wz1PaperBodyFamily
        (proposition63MildRescalingFamily hscale sourceData.raw)).mass :=
    paper_body_family_mass_positive
      (mul_pos (lt_of_lt_of_le zero_lt_one hscale)
        sourceExtremal.delta_pos)
      (hscaleDeltaSmall.trans (by norm_num))
      (proposition63MildRescalingFamily_lineClass hscale sourceData.raw
        sourceData.raw_line_class)
      targetFamilyNonempty
  have targetMassPos : 0 < sourceData.targetShading.mass := by
    exact (ENNReal.mul_pos targetDensityPos.ne' targetBodyMassPos.ne').trans_le
      targetDenseBeforeSelections
  have finalRetention :=
    targetData.parentSchedule.finalShading_mass_retention_after_cleanup
      targetData.cleanup targetData.selection_mass
      targetData.fiberRegularized
  have finalMassPos : 0 < (targetData.parentSchedule.finalShading
      targetData.fiberRegularized).mass := by
    by_contra hnot
    have hzero : (targetData.parentSchedule.finalShading
        targetData.fiberRegularized).mass = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    rw [hzero, mul_zero] at finalRetention
    exact (not_le_of_gt targetMassPos) finalRetention
  have refinedUnionSubset : sourceData.refined.union ⊆ sourceShading.union := by
    rintro point ⟨index, pointMem⟩
    exact ⟨sourceData.selected.embedding index,
      sourceData.boxed_subshading _
        (sourceData.refined_sub_boxed index pointMem)⟩
  have finalUnionSubsetOriginal :
      (targetData.parentSchedule.finalShading
        targetData.fiberRegularized).union ⊆
      wz1IsotropicRescalingMap sourceData.center scale ''
        sourceShading.union :=
    targetData.finalUnionSubsetImage.trans
      (Set.image_mono refinedUnionSubset)
  have targetVolume :=
    Proposition63MildRescalingFiniteParentScheduleData.isotropicSubshading_volume_upper
      sourceExtremal sourceData.center
      (lt_of_lt_of_le zero_lt_one hscale) finalUnionSubsetOriginal
      hvolumeAbsorb
  have targetExtremal := targetData.parentSchedule.finalCroppedExtremal
    targetData.fiberRegularized sourceExtremal.delta_pos
    (hscaleDeltaSmall.trans (by norm_num)) finalMassPos targetNearbyFinal
    targetCubical targetDense targetVolume
  exact
    Proposition63MildRescalingFiniteParentScheduleData.finalGrainConfiguration
    sourceData.preGrainSelected targetData.finalSourceIndex
    targetData.finalDirection sourceData.center
    targetData.finalCarrierSubsetImage targetData.finalUnionSubsetImage
    hscale hplaneScale hslopeScale sourceExtremal.delta_pos
    (hscaleDeltaSmall.trans (by norm_num)) hsigma hsigmaOne hsourceLoss
    hsourceOutput hADAbsorb targetData.finalLineClass targetCubical
    targetExtremal targetTop

end Proposition63M9MildRescalingTargetData

/-- Execute every finite target-side selection.  No CWA or extremality is
postulated here; those are assembled in the next layer from the exact source
schedule and the explicit numerical budgets. -/
theorem Proposition63M9MildRescalingSourceData.buildTarget
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    (sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant)
    (sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount) :
    Nonempty (Proposition63M9MildRescalingTargetData
      sourceData sourceSchedule) := by
  let parentSchedule := sourceData.parentSchedule sourceSchedule
  rcases proposition63_mild_rescaling_cleanup sourceExtremal.delta_pos hscale
      (sourceLine.subfamily sourceData.selected)
      (sourceDistinct.subfamily sourceData.selected)
      (sourceData.center_window 2) sourceData.raw sourceData.raw_line_class
      sourceData.targetShading sourceData.target_cubical with
    ⟨cleanup⟩
  rcases parentSchedule.finiteStrongSelectionAfterCleanup cleanup with
    ⟨selection, selectionSubset, selectionMass⟩
  rcases parentSchedule.finiteFiberRegularization selection
      sourceData.targetShading with ⟨fiberRegularized⟩
  exact ⟨{
    parentSchedule := parentSchedule
    cleanup := cleanup
    weight := fun index =>
      if index ∈ cleanup.selectedIndices then
        volume (sourceData.targetShading.carrier index) else 0
    weight_eq := rfl
    selection := selection
    selection_subset_cleanup := selectionSubset
    selection_mass := selectionMass
    fiberRegularized := fiberRegularized
  }⟩

end Kakeya.Assouad.PureWZ2

end
