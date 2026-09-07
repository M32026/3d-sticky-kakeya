import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingFiniteSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingParentCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureFiniteNearbySchedule
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureHitParentRestriction

/-!
# Finite strict-parent schedule for Proposition 6.3 mild rescaling

The source Definition 2.12 data are first reduced to the finite nearby-scale
schedule used in the paper.  At every representative scale, the canonical
centered isotropic target tubes are assigned to enlarged image-line parents.
One weighted complete-parent selection is then performed simultaneously at
all representative scales.  The selected target family consequently has a
literal strict partitioning cover at every representative scale.

This file is deliberately only the strict-cover layer.  Full-fiber degree
regularization and the actual-John transport are performed after this common
selection, so no parent fiber is replaced by a singleton here.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Geometric parent data at every representative source scale, with one
common packing degree large enough for the simultaneous selection. -/
structure Proposition63MildRescalingFiniteParentScheduleData
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center)
    (sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount) where
  targetRho : Fin sourceSchedule.scaleCount → ℝ
  parentCover : ∀ coordinate,
    Proposition63MildRescalingParentCoverData
      (sourceSchedule.witness coordinate).scaleData hscale raw
      (targetRho coordinate)
  degree : ℕ
  parent_degree : ∀ coordinate,
    (parentCover coordinate).parentConflictDegree ≤ degree

/-- Build the finite target-parent schedule from the actual source nearby
schedule.  The caller supplies only the geometric parent record at each
coordinate; the common degree is the finite supremum of the already-proved
packing degrees. -/
noncomputable def proposition63_mild_rescaling_finite_parent_schedule
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center)
    (sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount)
    (targetRho : Fin sourceSchedule.scaleCount → ℝ)
    (parentCover : ∀ coordinate,
      Proposition63MildRescalingParentCoverData
        (sourceSchedule.witness coordinate).scaleData hscale raw
        (targetRho coordinate)) :
    Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule where
  targetRho := targetRho
  parentCover := parentCover
  degree := Finset.univ.sup fun coordinate =>
    (parentCover coordinate).parentConflictDegree
  parent_degree coordinate := by
    exact Finset.le_sup
      (f := fun coordinate =>
        (parentCover coordinate).parentConflictDegree)
      (Finset.mem_univ coordinate)

namespace Proposition63MildRescalingFiniteParentScheduleData

/-- The source parent selected at one representative coordinate. -/
def parent
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    (data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule)
    (coordinate : Fin sourceSchedule.scaleCount) :
    Fin sourceFine.card →
      Fin (sourceSchedule.witness coordinate).scaleData.coarse.card :=
  (sourceSchedule.witness coordinate).scaleData.cover.parent

/-- Conflict means failure of the quantitative parent separation needed by
the literal doubled-fiber cover. -/
def conflict
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    (data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule)
    (coordinate : Fin sourceSchedule.scaleCount)
    (first second :
      Fin (sourceSchedule.witness coordinate).scaleData.coarse.card) : Prop :=
  wz1PaperLineDistance
      ((data.parentCover coordinate).parentFamily.tube first)
      ((data.parentCover coordinate).parentFamily.tube second) ≤
    2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
      data.targetRho coordinate

theorem conflict_refl
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    (data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule)
    (coordinate : Fin sourceSchedule.scaleCount)
    (parent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card) :
    data.conflict coordinate parent parent := by
  unfold conflict
  have hnonnegative :
      0 ≤ 2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
        data.targetRho coordinate := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (by
        simp only [wz2PaperLocalizedDoubledFiberLineDistanceConstant]
        norm_num))
      (data.parentCover coordinate).target_rho_pos.le
  have hdirection : wz1PaperDirection
      ((data.parentCover coordinate).parentFamily.tube parent) ≠ 0 := by
    intro hzero
    have hnorm := wz1PaperDirection_norm
      ((data.parentCover coordinate).parentFamily.tube parent)
    rw [hzero] at hnorm
    norm_num at hnorm
  have hself : wz1PaperLineDistance
      ((data.parentCover coordinate).parentFamily.tube parent)
      ((data.parentCover coordinate).parentFamily.tube parent) = 0 := by
    simp [wz1PaperLineDistance, dist_self]
      <;> rw [InnerProductGeometry.angle_self hdirection] <;> simp
  rw [hself]
  exact hnonnegative

theorem conflict_symm
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    (data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule)
    (coordinate : Fin sourceSchedule.scaleCount)
    (first second :
      Fin (sourceSchedule.witness coordinate).scaleData.coarse.card) :
    data.conflict coordinate first second →
      data.conflict coordinate second first := by
  unfold conflict
  intro h
  rw [wz1PaperLineDistance_symm]
  exact h

theorem conflict_degree
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    (data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule)
    (coordinate : Fin sourceSchedule.scaleCount)
    (parent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card) :
    ((Finset.univ : Finset (Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)).filter
      (data.conflict coordinate parent)).card ≤ data.degree := by
  exact ((data.parentCover coordinate).parentConflict_degree parent).trans
    (data.parent_degree coordinate)

/-- The common complete-parent selection over all source schedule
coordinates.  The weight is arbitrary here; the final Proposition 6.3
assembly instantiates it with the actual rescaled shaded mass. -/
theorem finiteStrongSelection
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    (data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule)
    (weight : Fin sourceFine.card → ENNReal) :
    Nonempty (Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree) := by
  apply proposition63_finite_strong_parent_selection
  · exact data.conflict_refl
  · exact data.conflict_symm
  · exact data.conflict_degree

/-- Run the simultaneous parent separation only after the ordinary target
cleanup.  The resulting common index set is therefore a subset of the
ordinary-distinct family, while the retained-weight estimate starts from
the entire cleanup output. -/
theorem finiteStrongSelectionAfterCleanup
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    (data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule)
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (cleanup : Proposition63MildRescalingCleanupData
      hscale raw targetShading) :
    let weight : Fin sourceFine.card → ENNReal := fun index =>
      if index ∈ cleanup.selectedIndices then
        volume (targetShading.carrier index) else 0
    ∃ selection : Proposition63FiniteStrongParentSelectionData
        weight sourceSchedule.scaleCount
        (fun coordinate => Fin
          (sourceSchedule.witness coordinate).scaleData.coarse.card)
        data.parent data.conflict data.degree,
      selection.selected ⊆ cleanup.selectedIndices ∧
      (∑ index ∈ cleanup.selectedIndices,
          volume (targetShading.carrier index)) ≤
        (data.degree : ENNReal) ^ sourceSchedule.scaleCount *
          ∑ index ∈ selection.selected,
            volume (targetShading.carrier index) := by
  dsimp only
  exact proposition63_finite_strong_parent_selection_from
    (fun index => volume (targetShading.carrier index))
    cleanup.selectedIndices sourceSchedule.scaleCount
    (fun coordinate => Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card)
    data.parent data.conflict data.degree
    data.conflict_refl data.conflict_symm data.conflict_degree

/-- The common target tube subfamily retained by the finite parent
selection. -/
def selectedTarget
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree) :
    WZ2PaperPureTubeSubfamily
      (proposition63MildRescalingFamily hscale raw) :=
  WZ2PaperPureTubeSubfamily.fromFinset
    (proposition63MildRescalingFamily hscale raw) selection.selected

/-- The same selected indices, viewed in the source family. -/
def selectedSource
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree) :
    WZ2PaperPureTubeSubfamily sourceFine :=
  WZ2PaperPureTubeSubfamily.fromFinset sourceFine selection.selected

/-- The first selection uses the same finite set on source and target
indices. -/
def selectedTargetSourceIndexEquiv
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree) :
    Fin (selectedTarget selection).family.card ≃
      Fin (selectedSource selection).family.card :=
  Equiv.cast (by rfl)

/-- A parent-schedule selection contained in the ordinary cleanup remains
ordinary essentially distinct. -/
theorem selectedTarget_ordinaryDistinct_of_cleanup
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree)
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (cleanup : Proposition63MildRescalingCleanupData
      hscale raw targetShading)
    (hsubset : selection.selected ⊆ cleanup.selectedIndices) :
    WZ2PaperOrdinaryIsEssentiallyDistinct
      (selectedTarget selection).family := by
  intro first second hne
  let ambientFirst : Fin sourceFine.card :=
    selection.selected.orderEmbOfFin rfl first
  let ambientSecond : Fin sourceFine.card :=
    selection.selected.orderEmbOfFin rfl second
  have hfirstMem : ambientFirst ∈ cleanup.selectedIndices :=
    hsubset (Finset.orderEmbOfFin_mem selection.selected rfl first)
  have hsecondMem : ambientSecond ∈ cleanup.selectedIndices :=
    hsubset (Finset.orderEmbOfFin_mem selection.selected rfl second)
  let cleanupFirst : Fin cleanup.selectedIndices.card :=
    cleanup.selectedIndices.equivFin ⟨ambientFirst, hfirstMem⟩
  let cleanupSecond : Fin cleanup.selectedIndices.card :=
    cleanup.selectedIndices.equivFin ⟨ambientSecond, hsecondMem⟩
  have hambientFirst :
      (cleanup.selectedIndices.equivFin.symm cleanupFirst).1 = ambientFirst :=
    congrArg Subtype.val <|
      cleanup.selectedIndices.equivFin.symm_apply_apply
        ⟨ambientFirst, hfirstMem⟩
  have hambientSecond :
      (cleanup.selectedIndices.equivFin.symm cleanupSecond).1 = ambientSecond :=
    congrArg Subtype.val <|
      cleanup.selectedIndices.equivFin.symm_apply_apply
        ⟨ambientSecond, hsecondMem⟩
  have hcleanupNe : cleanupFirst ≠ cleanupSecond := by
    intro heq
    apply hne
    have hambient : ambientFirst = ambientSecond := by
      rw [← hambientFirst, ← hambientSecond, heq]
    exact (selection.selected.orderEmbOfFin rfl).injective hambient
  have hdistinct := cleanup.ordinary_distinct
    cleanupFirst cleanupSecond hcleanupNe
  change
    ¬((proposition63MildRescalingFamily hscale raw).tube ambientFirst).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2
          ((proposition63MildRescalingFamily hscale raw).tube ambientSecond) ∧
      ¬((proposition63MildRescalingFamily hscale raw).tube ambientSecond).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2
          ((proposition63MildRescalingFamily hscale raw).tube ambientFirst)
  simpa only [proposition63MildRescalingSelectedSubfamily,
    selectedTubeFamily_tube, hambientFirst, hambientSecond] using hdistinct

@[simp] theorem selectedTargetSourceIndexEquiv_embedding
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree)
    (index : Fin (selectedTarget selection).family.card) :
    (selectedSource selection).embedding
        (selectedTargetSourceIndexEquiv selection index) =
      (selectedTarget selection).embedding index := by
  rfl

/-- The enlarged target parents hit by the common selected family at one
representative scale. -/
def selectedParents
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree)
    (coordinate : Fin sourceSchedule.scaleCount) :
    WZ2PaperPureTubeSubfamily (data.parentCover coordinate).parentFamily :=
  WZ2PaperPureTubeSubfamily.fromFinset
    (data.parentCover coordinate).parentFamily
    ((sourceSchedule.witness coordinate).scaleData.cover.hitParentIndices
      (selectedSource selection))

/-- Target parent labels and the corresponding source hit-parent labels use
the same selected ambient parent indices. -/
def selectedParentSourceIndexEquiv
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree)
    (coordinate : Fin sourceSchedule.scaleCount) :
    Fin (selectedParents selection coordinate).family.card ≃
      Fin ((sourceSchedule.witness coordinate).scaleData.cover
        |>.hitParentSubfamily (selectedSource selection)).family.card :=
  Equiv.cast (by rfl)

@[simp] theorem selectedParentSourceIndexEquiv_embedding
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree)
    (coordinate : Fin sourceSchedule.scaleCount)
    (parent : Fin (selectedParents selection coordinate).family.card) :
    ((sourceSchedule.witness coordinate).scaleData.cover
      |>.hitParentSubfamily (selectedSource selection)).embedding
        (selectedParentSourceIndexEquiv selection coordinate parent) =
      (selectedParents selection coordinate).embedding parent := by
  rfl

/-- At every representative scale, simultaneous parent separation produces
a genuine literal Definition 2.12 partitioning cover of the same selected
target family. -/
noncomputable def selectedPartitioningCover
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree)
    (coordinate : Fin sourceSchedule.scaleCount) :
    WZ2PaperPurePartitioningCover
      (selectedTarget selection).family
      (selectedParents selection coordinate).family := by
  let sourceScale := (sourceSchedule.witness coordinate).scaleData
  let sourceSelected := selectedSource selection
  let assigned := sourceScale.cover.hitParent sourceSelected
  apply (data.parentCover coordinate).toPartitioningCoverOfSeparated
    (selectedTarget selection) (selectedParents selection coordinate) assigned
  · exact sourceScale.cover.hitParent_surjective sourceSelected
  · intro source
    exact sourceScale.cover.hitParent_ambient sourceSelected source
  · intro first second hne
    have hambientNe :
        (selectedParents selection coordinate).embedding first ≠
          (selectedParents selection coordinate).embedding second :=
      (selectedParents selection coordinate).embedding.injective.ne hne
    rcases sourceScale.cover.hitParent_surjective sourceSelected first with
      ⟨firstSource, hfirstSource⟩
    rcases sourceScale.cover.hitParent_surjective sourceSelected second with
      ⟨secondSource, hsecondSource⟩
    have hfirstParent := sourceScale.cover.hitParent_ambient
      sourceSelected firstSource
    have hsecondParent := sourceScale.cover.hitParent_ambient
      sourceSelected secondSource
    rw [hfirstSource] at hfirstParent
    rw [hsecondSource] at hsecondParent
    have hfirstParent' :
        data.parent coordinate
            ((selectedSource selection).embedding firstSource) =
          (selectedParents selection coordinate).embedding first := by
      change sourceScale.cover.parent
          (sourceSelected.embedding firstSource) =
        (sourceScale.cover.hitParentSubfamily sourceSelected).embedding first
      exact hfirstParent.symm
    have hsecondParent' :
        data.parent coordinate
            ((selectedSource selection).embedding secondSource) =
          (selectedParents selection coordinate).embedding second := by
      change sourceScale.cover.parent
          (sourceSelected.embedding secondSource) =
        (sourceScale.cover.hitParentSubfamily sourceSelected).embedding second
      exact hsecondParent.symm
    have hnotConflict := selection.hit_parent_separated coordinate
      ((selectedParents selection coordinate).embedding first)
      ((selectedParents selection coordinate).embedding second)
      hambientNe
      ⟨(selectedSource selection).embedding firstSource,
        Finset.orderEmbOfFin_mem _ rfl firstSource, by
          exact hfirstParent'⟩
      ⟨(selectedSource selection).embedding secondSource,
        Finset.orderEmbOfFin_mem _ rfl secondSource, by
          exact hsecondParent'⟩
    exact lt_of_not_ge hnotConflict

/-- The parent derived from the target strict cover is exactly the source
hit parent, transported across the two definitional index equivalences. -/
theorem selectedPartitioningCover_parent
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree)
    (coordinate : Fin sourceSchedule.scaleCount)
    (source : Fin (selectedTarget selection).family.card) :
    (selectedPartitioningCover selection coordinate).parent source =
      (selectedParentSourceIndexEquiv selection coordinate).symm
        ((sourceSchedule.witness coordinate).scaleData.cover.hitParent
          (selectedSource selection)
          (selectedTargetSourceIndexEquiv selection source)) := by
  let cover := selectedPartitioningCover selection coordinate
  let sourceScale := (sourceSchedule.witness coordinate).scaleData
  let sourceIndex := selectedTargetSourceIndexEquiv selection source
  let parentEquiv := selectedParentSourceIndexEquiv selection coordinate
  let sourceParent := sourceScale.cover.hitParent
    (selectedSource selection) sourceIndex
  apply cover.fullFiber_parent_unique
    (data.parentCover coordinate).target_rho_pos.le
  · exact cover.parent_mem_fullFiber source
  · rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    rw [(selectedTarget selection).tube_eq,
      (selectedParents selection coordinate).tube_eq]
    have hparentAmbient :
        (selectedParents selection coordinate).embedding
            (parentEquiv.symm sourceParent) =
          sourceScale.cover.parent
            ((selectedSource selection).embedding sourceIndex) := by
      calc
        _ = (sourceScale.cover.hitParentSubfamily
              (selectedSource selection)).embedding
              (parentEquiv (parentEquiv.symm sourceParent)) := by
            rw [selectedParentSourceIndexEquiv_embedding]
        _ = (sourceScale.cover.hitParentSubfamily
              (selectedSource selection)).embedding sourceParent := by
            rw [parentEquiv.apply_symm_apply]
        _ = sourceScale.cover.parent
              ((selectedSource selection).embedding sourceIndex) :=
            sourceScale.cover.hitParent_ambient
              (selectedSource selection) sourceIndex
    rw [hparentAmbient]
    rw [← selectedTargetSourceIndexEquiv_embedding selection source]
    exact (data.parentCover coordinate).assigned_containment
      ((selectedSource selection).embedding sourceIndex)

end Proposition63MildRescalingFiniteParentScheduleData

end Kakeya.Assouad.PureWZ2

end
