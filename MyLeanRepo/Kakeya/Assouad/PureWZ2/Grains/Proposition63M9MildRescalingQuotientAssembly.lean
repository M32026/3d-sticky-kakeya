import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9MildRescalingAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingQuotientCWA
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCardinalityRetention

/-!
# Quotient-based M9 mild-rescaling assembly

This module replaces the raw-source-parent schedule in the final Proposition
6.3 tail by the target-line quotient schedule.  The same joint finite
regularization controls both public quotient fibers and the source actual
packets used by the packetwise John-body transfer.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure Proposition63M9MildRescalingQuotientTargetData
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
  quotientSchedule : Proposition63MildRescalingQuotientScheduleData
    hscale sourceData.raw sourceSchedule
  cleanup : Proposition63MildRescalingCleanupData hscale sourceData.raw
    sourceData.targetShading
  weight : Fin sourceData.selected.family.card → ENNReal
  weight_eq : weight = fun index =>
    if index ∈ cleanup.selectedIndices then
      volume (sourceData.targetShading.carrier index) else 0
  selection : Proposition63FiniteStrongParentSelectionData
    weight sourceSchedule.scaleCount quotientSchedule.Parent
    quotientSchedule.parent quotientSchedule.conflict
    proposition63MildRescalingQuotientConflictDegree
  selection_subset_cleanup : selection.selected ⊆ cleanup.selectedIndices
  selection_mass :
    (∑ index ∈ cleanup.selectedIndices,
        volume (sourceData.targetShading.carrier index)) ≤
      (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
          sourceSchedule.scaleCount *
        ∑ index ∈ selection.selected,
          volume (sourceData.targetShading.carrier index)
  jointRegularized : WZ2PaperFiniteParentRegularizationData
    (restrictPaperShading
      (quotientSchedule.selectedTarget selection).toTubeSubfamily
        sourceData.targetShading)
    (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
    (fun _ => quotientSchedule.JointParent selection)
    (quotientSchedule.jointParent selection)

namespace Proposition63M9MildRescalingQuotientTargetData

private theorem paperBodyFamily_mass_subfamily_le
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family) :
    (wz1PaperBodyFamily selected.family).mass ≤
      (wz1PaperBodyFamily family).mass := by
  let selectedIndices : Finset (Fin family.card) :=
    Finset.univ.map selected.embedding
  have selectedMass :
      (wz1PaperBodyFamily selected.family).mass =
        ∑ index ∈ selectedIndices,
          volume (wz1PaperTubeCarrier (family.tube index)) := by
    change (∑ index : Fin selected.family.card,
        volume (wz1PaperTubeCarrier (selected.family.tube index))) = _
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro index _
    rw [selected.tube_eq]
  rw [selectedMass]
  change (∑ index ∈ selectedIndices,
      volume (wz1PaperTubeCarrier (family.tube index))) ≤
    ∑ index : Fin family.card,
      volume (wz1PaperTubeCarrier (family.tube index))
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ selectedIndices) (fun _ _ _ => bot_le)

/-- The final target shading after quotient selection and joint
regularization. -/
def finalShading
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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    WZ1PaperTubeShading
      (data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).family :=
  restrictPaperShading
    (Kakeya.Streamlined.TubeSubfamily.fromFinset
      (data.quotientSchedule.selectedTarget data.selection).family
      data.jointRegularized.selected)
    (restrictPaperShading
      (data.quotientSchedule.selectedTarget data.selection).toTubeSubfamily
      sourceData.targetShading)

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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    WZ2PaperOrdinaryIsEssentiallyDistinct
      (data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).family :=
  (data.quotientSchedule.selectedTarget_ordinaryDistinct_of_cleanup
    data.cleanup data.selection data.selection_subset_cleanup).subfamily
      (data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized)

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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    WZ1PaperIsLineClass
      (data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).family :=
  ((proposition63MildRescalingFamily_lineClass hscale sourceData.raw
    sourceData.raw_line_class).subfamily
      (data.quotientSchedule.selectedTarget data.selection).toTubeSubfamily)
    |>.subfamily
      (data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).toTubeSubfamily

/-- Exact final-to-source index through both finite restrictions. -/
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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    Fin (data.quotientSchedule.jointRegularizedTarget
      data.jointRegularized).family.card ↪ Fin sourceData.selected.family.card :=
  data.quotientSchedule.jointRegularizedSourceIndex data.jointRegularized

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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule)
    (index : Fin (data.quotientSchedule.jointRegularizedTarget
      data.jointRegularized).family.card) :
    ((data.quotientSchedule.jointRegularizedTarget
      data.jointRegularized).family.tube index).direction =
      wz1PaperDirection
        (sourceData.selected.family.tube (data.finalSourceIndex index)) := by
  rw [(data.quotientSchedule.jointRegularizedTarget
      data.jointRegularized).tube_eq,
    (data.quotientSchedule.selectedTarget data.selection).tube_eq]
  exact proposition63MildRescalingFamily_direction_provenance
    hscale sourceData.raw _

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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule)
    (index : Fin (data.quotientSchedule.jointRegularizedTarget
      data.jointRegularized).family.card) :
    data.finalShading.carrier index ⊆
      wz1IsotropicRescalingMap sourceData.center scale ''
        sourceData.refined.carrier (data.finalSourceIndex index) := by
  intro point pointMem
  let ambientIndex := (data.quotientSchedule.selectedTarget
    data.selection).embedding
      ((data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).embedding index)
  have targetMem : point ∈ sourceData.targetShading.carrier ambientIndex :=
    pointMem
  rw [sourceData.targetShading_eq] at targetMem
  rcases targetMem with ⟨sourcePoint, sourcePointMem, pointEq⟩
  exact ⟨sourcePoint, sourcePointMem.1, pointEq⟩

/-- The two target-side selections only discard tube indices.  On every
surviving index, the final carrier is therefore the exact isotropic image of
the corresponding source carrier.  The apparent intersection in the raw
target shading is redundant because the source regularization was performed
inside the common shifted-grid core. -/
theorem finalCarrier_eq_image
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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule)
    (index : Fin (data.quotientSchedule.jointRegularizedTarget
      data.jointRegularized).family.card) :
    data.finalShading.carrier index =
      wz1IsotropicRescalingMap sourceData.center scale ''
        sourceData.refined.carrier (data.finalSourceIndex index) := by
  apply Set.Subset.antisymm
  · exact data.finalCarrierSubsetImage index
  · rintro point ⟨sourcePoint, sourcePointMem, rfl⟩
    let ambientIndex := (data.quotientSchedule.selectedTarget
      data.selection).embedding
        ((data.quotientSchedule.jointRegularizedTarget
          data.jointRegularized).embedding index)
    have pointBoxed := sourceData.refined_sub_boxed
      (data.finalSourceIndex index) sourcePointMem
    have pointCore : sourcePoint ∈
        pureWZ2ShiftedOriginGridCore sourceDelta scale sourceData.center := by
      rw [sourceData.boxed_carrier_eq] at pointBoxed
      exact pointBoxed.2
    change wz1IsotropicRescalingMap sourceData.center scale sourcePoint ∈
      sourceData.targetShading.carrier ambientIndex
    rw [sourceData.targetShading_eq]
    exact ⟨sourcePoint, ⟨sourcePointMem, pointCore⟩, rfl⟩

/-- Each final target tube retains positive shaded mass.  This is an indexed
fact: it follows from the exact source index and the exact isotropic image,
not from positivity of the aggregate final mass. -/
theorem finalCarrier_volume_pos
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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule)
    (index : Fin (data.quotientSchedule.jointRegularizedTarget
      data.jointRegularized).family.card) :
    0 < volume (data.finalShading.carrier index) := by
  rw [data.finalCarrier_eq_image index,
    volume_image_wz1IsotropicRescalingMap
      (lt_of_lt_of_le zero_lt_one hscale) sourceData.center
      (sourceData.refined.measurable_carrier
        (data.finalSourceIndex index))]
  apply ENNReal.mul_pos
  · exact (ENNReal.ofReal_pos.mpr (by
      have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
      positivity)).ne'
  · have sourceDensityPos : 0 < sourceData.sourceDensity := by
      rw [sourceData.sourceDensity_eq]
      apply ENNReal.mul_pos
      · exact (ENNReal.ofReal_pos.mpr (by
          have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
          positivity)).ne'
      · exact (show 0 < Kakeya.realRpowENN sourceDelta sourceLoss by
          simp only [Kakeya.realRpowENN]
          exact ENNReal.ofReal_pos.mpr
            (Real.rpow_pos_of_pos sourceExtremal.delta_pos sourceLoss)).ne'
    have sourceScalePos : 0 < Kakeya.realRpowENN sourceDelta 2 := by
      simp only [Kakeya.realRpowENN]
      exact ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos sourceExtremal.delta_pos 2)
    exact ((ENNReal.mul_pos
      (ENNReal.mul_pos (by norm_num) sourceDensityPos.ne').ne'
      sourceScalePos.ne').trans_le
        (sourceData.refined_per_tube (data.finalSourceIndex index))).ne'

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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    data.finalShading.union ⊆
      wz1IsotropicRescalingMap sourceData.center scale ''
        sourceData.refined.union := by
  rintro point ⟨index, pointMem⟩
  rcases data.finalCarrierSubsetImage index pointMem with
    ⟨sourcePoint, sourcePointMem, pointEq⟩
  exact ⟨sourcePoint, ⟨data.finalSourceIndex index, sourcePointMem⟩,
    pointEq⟩

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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    WZ1PaperIsCubicalShading data.finalShading :=
  restrictPaperShading_cubical
    (data.quotientSchedule.jointRegularizedTarget
      data.jointRegularized).toTubeSubfamily
    (restrictPaperShading_cubical
      (data.quotientSchedule.selectedTarget data.selection).toTubeSubfamily
      sourceData.target_cubical)

theorem finalFamily_isInUnitBall
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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    (data.quotientSchedule.jointRegularizedTarget
      data.jointRegularized).family.IsInUnitBall := by
  intro index
  rw [(data.quotientSchedule.jointRegularizedTarget
      data.jointRegularized).tube_eq,
    (data.quotientSchedule.selectedTarget data.selection).tube_eq]
  exact proposition63MildRescalingFamily_isInUnitBall
    sourceExtremal.delta_pos hscale
    (hscaleDeltaSmall.trans (by norm_num)) sourceData.raw
    sourceData.raw_line_class _

/-- Total mass/cardinality loss from cleanup, absolute-degree quotient
selection, and the final joint degree regularization. -/
noncomputable def selectionLoss
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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) : ENNReal :=
  ((proposition63MildRescalingConflictDegree sourceDelta scale + 1 : ℕ) :
      ENNReal) *
    (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
      sourceSchedule.scaleCount *
    ((8 : ENNReal) *
      (Nat.log 2
        (2 * (data.quotientSchedule.selectedTarget
          data.selection).family.card) + 1 : ENNReal) ^
        (sourceSchedule.scaleCount + sourceSchedule.scaleCount + 1))

/-- All three finite restrictions retain the target shaded mass with the
explicit quotient loss. -/
theorem finalShading_mass_retention
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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    sourceData.targetShading.mass ≤
      data.selectionLoss * data.finalShading.mass := by
  let cleanupSelected := proposition63MildRescalingSelectedSubfamily
    (proposition63MildRescalingFamily hscale sourceData.raw)
    data.cleanup.selectedIndices
  let selected := data.quotientSchedule.selectedTarget data.selection
  let joint := data.quotientSchedule.jointRegularizedTarget
    data.jointRegularized
  let cleanupLoss : ENNReal :=
    (proposition63MildRescalingConflictDegree sourceDelta scale + 1 : ℕ)
  let quotientLoss : ENNReal :=
    (proposition63MildRescalingQuotientConflictDegree : ℕ) ^
      sourceSchedule.scaleCount
  let jointLoss : ENNReal :=
    8 *
      (Nat.log 2 (2 * selected.family.card) + 1 : ENNReal) ^
        (sourceSchedule.scaleCount + sourceSchedule.scaleCount + 1)
  have cleanupMass :
      (restrictPaperShading cleanupSelected sourceData.targetShading).mass =
        ∑ index ∈ data.cleanup.selectedIndices,
          volume (sourceData.targetShading.carrier index) := by
    change (∑ index : Fin data.cleanup.selectedIndices.card,
        volume (sourceData.targetShading.carrier
          (data.cleanup.selectedIndices.equivFin.symm index).1)) = _
    calc
      _ = ∑ index : data.cleanup.selectedIndices,
          volume (sourceData.targetShading.carrier index.1) := by
        exact Equiv.sum_comp (M := ENNReal)
          data.cleanup.selectedIndices.equivFin.symm
          (fun index : data.cleanup.selectedIndices =>
            volume (sourceData.targetShading.carrier index.1))
      _ = _ := by
        exact Finset.sum_coe_sort data.cleanup.selectedIndices
          (fun index => volume (sourceData.targetShading.carrier index))
  have selectedMass :
      (restrictPaperShading selected.toTubeSubfamily
        sourceData.targetShading).mass =
      ∑ index ∈ data.selection.selected,
        volume (sourceData.targetShading.carrier index) := by
    change (∑ index : Fin data.selection.selected.card,
        volume (sourceData.targetShading.carrier
          (data.selection.selected.orderEmbOfFin rfl index))) = _
    let equivalence : Fin data.selection.selected.card ≃
        data.selection.selected :=
      (data.selection.selected.orderIsoOfFin rfl).toEquiv
    calc
      _ = ∑ index : data.selection.selected,
          volume (sourceData.targetShading.carrier index.1) := by
        exact Fintype.sum_equiv equivalence _ _ (fun _ => rfl)
      _ = _ := by
        exact Finset.sum_coe_sort data.selection.selected
          (fun index => volume (sourceData.targetShading.carrier index))
  have cleanupRetention : sourceData.targetShading.mass ≤
      cleanupLoss *
        (restrictPaperShading cleanupSelected
          sourceData.targetShading).mass := by
    simpa only [cleanupLoss, cleanupSelected] using data.cleanup.mass_retention
  have selectionRetention :
      (∑ index ∈ data.cleanup.selectedIndices,
        volume (sourceData.targetShading.carrier index)) ≤
      quotientLoss *
        ∑ index ∈ data.selection.selected,
          volume (sourceData.targetShading.carrier index) := by
    simpa only [quotientLoss] using data.selection_mass
  have jointRetention :
      (restrictPaperShading selected.toTubeSubfamily
        sourceData.targetShading).mass ≤
      jointLoss * data.finalShading.mass := by
    have retained := data.jointRegularized.retained_mass
    change (restrictPaperShading selected.toTubeSubfamily
        sourceData.targetShading).mass ≤
      jointLoss *
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset selected.family
            data.jointRegularized.selected)
          (restrictPaperShading selected.toTubeSubfamily
            sourceData.targetShading)).mass at retained
    change (restrictPaperShading selected.toTubeSubfamily
        sourceData.targetShading).mass ≤
      jointLoss *
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset selected.family
            data.jointRegularized.selected)
          (restrictPaperShading selected.toTubeSubfamily
            sourceData.targetShading)).mass
    exact retained
  calc
    sourceData.targetShading.mass ≤ cleanupLoss *
        (restrictPaperShading cleanupSelected sourceData.targetShading).mass :=
      cleanupRetention
    _ = cleanupLoss *
          ∑ index ∈ data.cleanup.selectedIndices,
            volume (sourceData.targetShading.carrier index) := by
      rw [cleanupMass]
    _ ≤ cleanupLoss *
        (quotientLoss * ∑ index ∈ data.selection.selected,
          volume (sourceData.targetShading.carrier index)) := by
      gcongr
    _ = (cleanupLoss * quotientLoss) *
        (restrictPaperShading selected.toTubeSubfamily
          sourceData.targetShading).mass := by
      rw [selectedMass]
      ring
    _ ≤ (cleanupLoss * quotientLoss) *
        (jointLoss * data.finalShading.mass) := by
      gcongr
    _ = data.selectionLoss * data.finalShading.mass := by
      simp only [selectionLoss, cleanupLoss, quotientLoss, jointLoss, selected]
      ring

theorem selectionLoss_pos
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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) : 0 < data.selectionLoss := by
  unfold selectionLoss proposition63MildRescalingQuotientConflictDegree
  positivity

/-- A density lower bound and the three-stage mass ledger give the global
cardinality retention needed by packetwise actual-John transport. -/
theorem globalCardinalityRetention
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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule)
    (targetDensity : ENNReal)
    (targetDense : sourceData.targetShading.IsLambdaDense targetDensity) :
    targetDensity * sourceData.selected.family.enncard ≤
      data.selectionLoss * (55296 * Kakeya.deltaTubeVolume 1) *
        (data.quotientSchedule.jointRegularizedTarget
          data.jointRegularized).family.enncard := by
  let finalSelected : Kakeya.Streamlined.TubeSubfamily
      (proposition63MildRescalingFamily hscale sourceData.raw) :=
    (data.quotientSchedule.selectedTarget data.selection).toTubeSubfamily.comp
      (data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).toTubeSubfamily
  have ambientMass : targetDensity *
      (proposition63MildRescalingFamily hscale sourceData.raw).enncard *
        Kakeya.realRpowENN (scale * sourceDelta) 2 ≤
      sourceData.targetShading.mass := by
    calc
      targetDensity *
          (proposition63MildRescalingFamily hscale sourceData.raw).enncard *
            Kakeya.realRpowENN (scale * sourceDelta) 2 =
          targetDensity *
            (Kakeya.realRpowENN (scale * sourceDelta) 2 *
              (proposition63MildRescalingFamily hscale
                sourceData.raw).enncard) := by ring
      _ ≤ targetDensity *
          (wz1PaperBodyFamily
            (proposition63MildRescalingFamily hscale sourceData.raw)).mass := by
        gcongr
        exact paperBodyFamily_mass_lower_rpow_two
          (mul_pos (lt_of_lt_of_le zero_lt_one hscale)
            sourceExtremal.delta_pos)
          (hscaleDeltaSmall.trans (by norm_num))
          (proposition63MildRescalingFamily_lineClass hscale sourceData.raw
            sourceData.raw_line_class)
      _ ≤ sourceData.targetShading.mass := targetDense
  have retained : sourceData.targetShading.mass ≤
      data.selectionLoss *
        (restrictPaperShading finalSelected sourceData.targetShading).mass := by
    calc
      sourceData.targetShading.mass ≤
          data.selectionLoss * data.finalShading.mass :=
        data.finalShading_mass_retention
      _ = data.selectionLoss *
          (restrictPaperShading finalSelected
            sourceData.targetShading).mass := by
        congr 1
  have result := wz2PaperWeightedCardinality_retained_from_subfamily_mass
    (mul_pos (lt_of_lt_of_le zero_lt_one hscale)
      sourceExtremal.delta_pos)
    (hscaleDeltaSmall.trans (by norm_num))
    (proposition63MildRescalingFamily_lineClass hscale sourceData.raw
      sourceData.raw_line_class) sourceData.targetShading finalSelected
    targetDensity data.selectionLoss ambientMass retained
  change targetDensity * sourceData.selected.family.enncard ≤
      data.selectionLoss * (55296 * Kakeya.deltaTubeVolume 1) *
        (data.quotientSchedule.jointRegularizedTarget
          data.jointRegularized).family.enncard at result
  exact result

theorem finalShading_dense
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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule)
    (sourceDensity finalDensity : ENNReal)
    (targetDense : sourceData.targetShading.IsLambdaDense sourceDensity)
    (densityAbsorb : data.selectionLoss * finalDensity ≤ sourceDensity) :
    data.finalShading.IsLambdaDense finalDensity := by
  let finalSelected : Kakeya.Streamlined.TubeSubfamily
      (proposition63MildRescalingFamily hscale sourceData.raw) :=
    (data.quotientSchedule.selectedTarget data.selection).toTubeSubfamily.comp
      (data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).toTubeSubfamily
  have bodyMass := paperBodyFamily_mass_subfamily_le finalSelected
  change (wz1PaperBodyFamily
      (data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).family).mass ≤
    (wz1PaperBodyFamily
      (proposition63MildRescalingFamily hscale sourceData.raw)).mass
    at bodyMass
  have retained := data.finalShading_mass_retention
  let loss := data.selectionLoss
  have scaled : loss *
      (finalDensity *
        (wz1PaperBodyFamily
          (data.quotientSchedule.jointRegularizedTarget
            data.jointRegularized).family).mass) ≤
      loss * data.finalShading.mass := by
    calc
      loss * (finalDensity *
          (wz1PaperBodyFamily
            (data.quotientSchedule.jointRegularizedTarget
              data.jointRegularized).family).mass) =
          (loss * finalDensity) *
            (wz1PaperBodyFamily
              (data.quotientSchedule.jointRegularizedTarget
                data.jointRegularized).family).mass := by ring
      _ ≤ sourceDensity *
          (wz1PaperBodyFamily
            (data.quotientSchedule.jointRegularizedTarget
              data.jointRegularized).family).mass := by gcongr
      _ ≤ sourceDensity *
          (wz1PaperBodyFamily
            (proposition63MildRescalingFamily hscale sourceData.raw)).mass := by
        gcongr
      _ ≤ sourceData.targetShading.mass := targetDense
      _ ≤ loss * data.finalShading.mass := by simpa only [loss] using retained
  have lossZero : loss ≠ 0 := data.selectionLoss_pos.ne'
  have lossTop : loss ≠ ⊤ := by
    unfold loss selectionLoss proposition63MildRescalingQuotientConflictDegree
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.natCast_ne_top _
      · exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
    · apply ENNReal.mul_ne_top
      · norm_num
      · exact ENNReal.pow_ne_top
          (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, by norm_num⟩)
  calc
    finalDensity *
        (wz1PaperBodyFamily
          (data.quotientSchedule.jointRegularizedTarget
            data.jointRegularized).family).mass =
      loss⁻¹ * (loss *
        (finalDensity *
          (wz1PaperBodyFamily
            (data.quotientSchedule.jointRegularizedTarget
              data.jointRegularized).family).mass)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel lossZero lossTop, one_mul]
    _ ≤ loss⁻¹ * (loss * data.finalShading.mass) := by gcongr
    _ = data.finalShading.mass := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel lossZero lossTop, one_mul]

theorem finalFamily_nonempty_of_mass_pos
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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule)
    (massPositive : 0 < data.finalShading.mass) :
    (data.quotientSchedule.jointRegularizedTarget
      data.jointRegularized).family.Nonempty := by
  by_contra familyEmpty
  have cardZero : (data.quotientSchedule.jointRegularizedTarget
      data.jointRegularized).family.card = 0 := by
    simpa [Kakeya.Streamlined.TubeFamily.Nonempty, not_lt] using familyEmpty
  have massZero : data.finalShading.mass = 0 := by
    change (∑ _index : Fin
      (data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).family.card, _) = 0
    apply Finset.sum_eq_zero
    intro index _
    exact Fin.elim0 (Fin.cast cardZero index)
  rw [massZero] at massPositive
  exact lt_irrefl 0 massPositive

/-- Complete quotient-based terminal assembly.  All source-to-packet
cardinality control is derived from the same target density and mass ledger
used to restore final extremality. -/
theorem finalGrainConfigurationWithBounds
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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule)
    (targetConstant : ENNReal)
    (targetFinite : WZ2PaperFiniteErrorConstant targetConstant)
    (scaleBudget :
      Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
        scheduleWindowConstant ≤ targetConstant)
    (constantBudget : ∀ coordinate : Fin sourceSchedule.scaleCount,
      max (data.quotientSchedule.quotientFiberRegularizationConstant
          data.selection)
        (data.quotientSchedule.quotientScheduleBodyConstant
          data.jointRegularized
          (((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
            ENNReal.ofReal scale) *
            ((1 / 2 : ENNReal) * sourceData.sourceDensity))
          (data.selectionLoss *
            (55296 * Kakeya.deltaTubeVolume 1))) ≤ targetConstant)
    (finalCWAAbsorb : (4 : ENNReal) * targetConstant ≤
      Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss))
    (densityAbsorb : data.selectionLoss *
        Kakeya.realRpowENN (scale * sourceDelta) outputLoss ≤
      ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
        ENNReal.ofReal scale) *
        ((1 / 2 : ENNReal) * sourceData.sourceDensity))
    (volumeAbsorb : ENNReal.ofReal (scale ^ 3) *
        Kakeya.realRpowENN sourceDelta (sigma - sourceLoss) ≤
      Kakeya.realRpowENN (scale * sourceDelta) (sigma - outputLoss))
    (sourceLoss_pos : 0 < sourceLoss)
    (sourceLoss_lt : sourceLoss < outputLoss)
    (adAbsorb : Real.rpow sourceDelta (outputLoss - sourceLoss) ≤
      Real.rpow scale (-outputLoss))
    (planeScale : (Lplane : ℝ) ≤ scale)
    (slopeScale : (Lslope : ℝ) ≤ scale)
    (sigma_pos : 0 < sigma) (sigma_lt_one : sigma < 1) :
    Nonempty (Proposition63MildRescalingFiniteParentScheduleData.Proposition63MildRescalingFinalGrainData
      (outputLoss := outputLoss) sourceData.refined
      sourceData.preGrainSelected
      (data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).family data.finalShading) := by
  let targetDensity : ENNReal :=
    ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
      ENNReal.ofReal scale) *
      ((1 / 2 : ENNReal) * sourceData.sourceDensity)
  have targetDenseBeforeSelections :
      sourceData.targetShading.IsLambdaDense targetDensity := by
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
        pointMem ((mem_wz1PaperGridCube sourceDelta _ point).mpr rfl)
          coordinate)
      (fun index point pointMem => by
        have pointBoxed := sourceData.refined_sub_boxed index pointMem
        rw [sourceData.boxed_carrier_eq] at pointBoxed
        exact pointBoxed.2) sourceData.raw_line_class
      ((1 / 2 : ENNReal) * sourceData.sourceDensity)
      sourceData.refined_per_tube
  have targetDensityZero : targetDensity ≠ 0 := by
    dsimp only [targetDensity]
    have geometryTop :
        (55296 * Kakeya.deltaTubeVolume 1 : ENNReal) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top
    apply mul_ne_zero
    · exact ENNReal.mul_pos
        (ENNReal.inv_pos.mpr geometryTop).ne'
        (ENNReal.ofReal_pos.mpr
          (lt_of_lt_of_le zero_lt_one hscale)).ne' |>.ne'
    · apply mul_ne_zero (by norm_num)
      rw [sourceData.sourceDensity_eq]
      apply mul_ne_zero
      · exact (ENNReal.ofReal_pos.mpr (by
        have scalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
        positivity)).ne'
      · exact (show 0 < Kakeya.realRpowENN sourceDelta sourceLoss by
          simp only [Kakeya.realRpowENN]
          exact ENNReal.ofReal_pos.mpr
            (Real.rpow_pos_of_pos sourceExtremal.delta_pos sourceLoss)).ne'
  have targetDensityTop : targetDensity ≠ ⊤ := by
    dsimp only [targetDensity]
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by
        exact mul_ne_zero (by norm_num)
          (zero_lt_one.trans_le one_le_deltaTubeVolume_one).ne'))
        ENNReal.ofReal_ne_top
    · apply ENNReal.mul_ne_top (by norm_num)
      rw [sourceData.sourceDensity_eq]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
        simp [Kakeya.realRpowENN])
  have cardinalityRetention := data.globalCardinalityRetention
    targetDensity targetDenseBeforeSelections
  have targetNearby := data.quotientSchedule.quotientNearbyScales
    sourceSchedule data.jointRegularized targetDensity
      (data.selectionLoss * (55296 * Kakeya.deltaTubeVolume 1))
    targetDensityZero targetDensityTop cardinalityRetention data.finalDistinct
    targetFinite scaleBudget constantBudget
  have targetNearbyFinal : WZ2PaperPureCWAAtNearbyScales
      (data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).family
      (Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss)) :=
    targetNearby.mono
      (calc
        targetConstant = 1 * targetConstant := (one_mul _).symm
        _ ≤ 4 * targetConstant := by gcongr; norm_num
        _ ≤ Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss) :=
          finalCWAAbsorb)
      (by simp [Kakeya.realRpowENN])
  have targetTopRaw := pure_nearby_to_top_level
    (mul_pos (lt_of_lt_of_le zero_lt_one hscale)
      sourceExtremal.delta_pos)
    (hscaleDeltaSmall.trans (by norm_num)) data.finalFamily_isInUnitBall
    targetNearby
  have targetTop : WZ2PaperConvexWolffBound
      (data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).family
      (Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss)) := by
    intro convexSet convexSetConvex
    exact (targetTopRaw convexSet convexSetConvex).trans <| by
      gcongr
  have targetDense := data.finalShading_dense targetDensity
    (Kakeya.realRpowENN (scale * sourceDelta) outputLoss)
    targetDenseBeforeSelections (by simpa only [targetDensity] using
      densityAbsorb)
  have targetFamilyNonempty :
      (proposition63MildRescalingFamily hscale sourceData.raw).Nonempty := by
    change 0 < sourceData.selected.family.card
    exact sourceData.selected_nonempty
  have targetDensityPos : 0 < targetDensity := targetDensityZero.bot_lt
  have targetBodyMassPos : 0 <
      (wz1PaperBodyFamily
        (proposition63MildRescalingFamily hscale sourceData.raw)).mass :=
    paper_body_family_mass_positive
      (mul_pos (lt_of_lt_of_le zero_lt_one hscale)
        sourceExtremal.delta_pos)
      (hscaleDeltaSmall.trans (by norm_num))
      (proposition63MildRescalingFamily_lineClass hscale sourceData.raw
        sourceData.raw_line_class) targetFamilyNonempty
  have targetMassPos : 0 < sourceData.targetShading.mass :=
    (ENNReal.mul_pos targetDensityPos.ne' targetBodyMassPos.ne').trans_le
      targetDenseBeforeSelections
  have finalMassPos : 0 < data.finalShading.mass := by
    by_contra notPositive
    have massZero : data.finalShading.mass = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp notPositive)
    have retained := data.finalShading_mass_retention
    rw [massZero, mul_zero] at retained
    exact (not_le_of_gt targetMassPos) retained
  have targetVolume :=
    Proposition63MildRescalingFiniteParentScheduleData.isotropicSubshading_volume_upper
      sourceExtremal sourceData.center
      (lt_of_lt_of_le zero_lt_one hscale)
      (data.finalUnionSubsetImage.trans (Set.image_mono (by
        rintro point ⟨index, pointMem⟩
        exact ⟨sourceData.selected.embedding index,
          sourceData.boxed_subshading _
            (sourceData.refined_sub_boxed index pointMem)⟩)))
      volumeAbsorb
  let targetExtremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      (data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).family data.finalShading := {
    delta_pos := mul_pos (lt_of_lt_of_le zero_lt_one hscale)
      sourceExtremal.delta_pos
    delta_le_one := hscaleDeltaSmall.trans (by norm_num)
    nonempty := data.finalFamily_nonempty_of_mass_pos finalMassPos
    cwa_nearby_scales := targetNearbyFinal
    cubical := data.finalCubical
    dense := targetDense
    volume_upper := targetVolume
    }
  exact Proposition63MildRescalingFiniteParentScheduleData.finalGrainConfigurationWithBounds
    sourceData.preGrainSelected data.finalSourceIndex data.finalDirection
    sourceData.center data.finalCarrierSubsetImage data.finalUnionSubsetImage
    hscale planeScale slopeScale sourceExtremal.delta_pos
    (hscaleDeltaSmall.trans (by norm_num)) sigma_pos sigma_lt_one
    sourceLoss_pos sourceLoss_lt adAbsorb data.finalLineClass
    data.finalCubical targetExtremal targetTop

/-- Paper-facing compatibility projection of the construction-aware quotient
tail. -/
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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule)
    (targetConstant : ENNReal)
    (targetFinite : WZ2PaperFiniteErrorConstant targetConstant)
    (scaleBudget :
      Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
        scheduleWindowConstant ≤ targetConstant)
    (constantBudget : ∀ coordinate : Fin sourceSchedule.scaleCount,
      max (data.quotientSchedule.quotientFiberRegularizationConstant
          data.selection)
        (data.quotientSchedule.quotientScheduleBodyConstant
          data.jointRegularized
          (((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
            ENNReal.ofReal scale) *
            ((1 / 2 : ENNReal) * sourceData.sourceDensity))
          (data.selectionLoss *
            (55296 * Kakeya.deltaTubeVolume 1))) ≤ targetConstant)
    (finalCWAAbsorb : (4 : ENNReal) * targetConstant ≤
      Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss))
    (densityAbsorb : data.selectionLoss *
        Kakeya.realRpowENN (scale * sourceDelta) outputLoss ≤
      ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
        ENNReal.ofReal scale) *
        ((1 / 2 : ENNReal) * sourceData.sourceDensity))
    (volumeAbsorb : ENNReal.ofReal (scale ^ 3) *
        Kakeya.realRpowENN sourceDelta (sigma - sourceLoss) ≤
      Kakeya.realRpowENN (scale * sourceDelta) (sigma - outputLoss))
    (sourceLoss_pos : 0 < sourceLoss)
    (sourceLoss_lt : sourceLoss < outputLoss)
    (adAbsorb : Real.rpow sourceDelta (outputLoss - sourceLoss) ≤
      Real.rpow scale (-outputLoss))
    (planeScale : (Lplane : ℝ) ≤ scale)
    (slopeScale : (Lslope : ℝ) ≤ scale)
    (sigma_pos : 0 < sigma) (sigma_lt_one : sigma < 1) :
    Nonempty (PureWZ2GrainConfiguration sigma outputLoss
      (scale * sourceDelta)) := by
  rcases data.finalGrainConfigurationWithBounds targetConstant targetFinite
      scaleBudget constantBudget finalCWAAbsorb densityAbsorb volumeAbsorb
      sourceLoss_pos sourceLoss_lt adAbsorb planeScale slopeScale sigma_pos
      sigma_lt_one with ⟨result⟩
  exact ⟨result.toGrainConfiguration⟩


end Proposition63M9MildRescalingQuotientTargetData

/-- Execute cleanup, quotient selection, and the joint quotient/source packet
regularization. -/
theorem Proposition63M9MildRescalingSourceData.buildQuotientTarget
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
    Nonempty (Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) := by
  let quotientSchedule := proposition63_mild_rescaling_quotient_schedule
    hscale sourceData.raw sourceSchedule sourceData.selected_nonempty
    (sourceLine.subfamily sourceData.selected)
    (sourceDistinct.subfamily sourceData.selected)
    (fun source => by
      rw [sourceData.selected.tube_eq]
      exact sourceMidpoint (sourceData.selected.embedding source))
    sourceData.raw_line_class (sourceData.center_window 2)
  rcases proposition63_mild_rescaling_cleanup sourceExtremal.delta_pos hscale
      (sourceLine.subfamily sourceData.selected)
      (sourceDistinct.subfamily sourceData.selected)
      (sourceData.center_window 2) sourceData.raw sourceData.raw_line_class
      sourceData.targetShading sourceData.target_cubical with
    ⟨cleanup⟩
  rcases quotientSchedule.simultaneouslySeparateAfterCleanup cleanup with
    ⟨selection, selectionSubset, selectionMass⟩
  rcases quotientSchedule.jointFiberRegularization selection
      sourceData.targetShading with ⟨jointRegularized⟩
  exact ⟨{
    quotientSchedule := quotientSchedule
    cleanup := cleanup
    weight := fun index => if index ∈ cleanup.selectedIndices then
      volume (sourceData.targetShading.carrier index) else 0
    weight_eq := rfl
    selection := selection
    selection_subset_cleanup := selectionSubset
    selection_mass := selectionMass
    jointRegularized := jointRegularized
    }⟩

end Kakeya.Assouad.PureWZ2

end
