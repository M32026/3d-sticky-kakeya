import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingQuotientParent
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingFiniteSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureFiniteNearbySchedule
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteParentRegularization
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteRegularizedRefinement
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureHitParentRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricFiberRequestedRoute

/-!
# Finite quotient-parent schedule for Proposition 6.3 mild rescaling

Each source nearby witness is first quotiented by a maximal target-line net.
A single weighted complete-fiber selection then makes the hit quotient
parents strongly separated at every scheduled coordinate.  Its loss base is
the absolute quotient-center packing constant, not a power of
`sourceRho / sourceDelta`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

attribute [local instance] Classical.propDecidable

structure Proposition63MildRescalingQuotientScheduleData
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
  representative : ∀ coordinate,
    Proposition63MildRescalingParentCoverData
      (sourceSchedule.witness coordinate).scaleData hscale raw
      (proposition63MildRescalingTargetRho sourceDelta
        (sourceSchedule.witness coordinate).rho scale)
  quotient : ∀ coordinate,
    Proposition63MildRescalingQuotientParentData
      (representative coordinate)
      (proposition63MildRescalingQuotientRho sourceDelta
        (sourceSchedule.witness coordinate).rho scale)

namespace Proposition63MildRescalingQuotientScheduleData

abbrev Parent
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
    (data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule)
    (coordinate : Fin sourceSchedule.scaleCount) : Type :=
  Fin (data.quotient coordinate).parentFamily.card

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
    (data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule)
    (coordinate : Fin sourceSchedule.scaleCount)
    (target : Fin sourceFine.card) : data.Parent coordinate :=
  (data.quotient coordinate).assignedParent target

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
    (data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule)
    (coordinate : Fin sourceSchedule.scaleCount)
    (first second : data.Parent coordinate) : Prop :=
  wz1PaperLineDistance
      ((data.quotient coordinate).parentFamily.tube first)
      ((data.quotient coordinate).parentFamily.tube second) ≤
    2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
      proposition63MildRescalingQuotientRho sourceDelta
        (sourceSchedule.witness coordinate).rho scale

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
    (data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule)
    (coordinate : Fin sourceSchedule.scaleCount)
    (parent : data.Parent coordinate) :
    data.conflict coordinate parent parent := by
  unfold conflict
  have hzero :
      wz1PaperLineDistance
          ((data.quotient coordinate).parentFamily.tube parent)
          ((data.quotient coordinate).parentFamily.tube parent) = 0 := by
    have hdirection :
        wz1PaperDirection
            ((data.quotient coordinate).parentFamily.tube parent) ≠ 0 := by
      intro hzero
      have hnorm := wz1PaperDirection_norm
        ((data.quotient coordinate).parentFamily.tube parent)
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
    simp [wz1PaperLineDistance,
      InnerProductGeometry.angle_self hdirection]
  rw [hzero]
  have hrho := (data.quotient coordinate).caller_rho_pos
  unfold wz2PaperLocalizedDoubledFiberLineDistanceConstant
  positivity

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
    (data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule)
    (coordinate : Fin sourceSchedule.scaleCount)
    (first second : data.Parent coordinate) :
    data.conflict coordinate first second →
      data.conflict coordinate second first := by
  unfold conflict
  intro h
  rwa [wz1PaperLineDistance_symm]

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
    (data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule)
    (coordinate : Fin sourceSchedule.scaleCount)
    (parent : data.Parent coordinate) :
    ((Finset.univ : Finset (data.Parent coordinate)).filter
      (data.conflict coordinate parent)).card ≤
        proposition63MildRescalingQuotientConflictDegree :=
  (data.quotient coordinate).parentConflict_degree parent

/-- One simultaneous selection across the quotient schedules, with an
absolute per-coordinate loss base. -/
theorem simultaneouslySeparate
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
    (data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule)
    (weight : Fin sourceFine.card → ENNReal) :
    Nonempty (Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree) := by
  apply proposition63_finite_strong_parent_selection
  · exact data.conflict_refl
  · exact data.conflict_symm
  · exact data.conflict_degree

/-- Run the quotient-center selection from the already cleaned ordinary
target indices. -/
theorem simultaneouslySeparateAfterCleanup
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
    (data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule)
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (cleanup : Proposition63MildRescalingCleanupData
      hscale raw targetShading) :
    let weight : Fin sourceFine.card → ENNReal := fun index =>
      if index ∈ cleanup.selectedIndices then
        MeasureTheory.volume (targetShading.carrier index) else 0
    ∃ selection : Proposition63FiniteStrongParentSelectionData
        weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
        proposition63MildRescalingQuotientConflictDegree,
      selection.selected ⊆ cleanup.selectedIndices ∧
      (∑ index ∈ cleanup.selectedIndices,
          MeasureTheory.volume (targetShading.carrier index)) ≤
        (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
            sourceSchedule.scaleCount *
          ∑ index ∈ selection.selected,
            MeasureTheory.volume (targetShading.carrier index) := by
  dsimp only
  exact proposition63_finite_strong_parent_selection_from
    (fun index => MeasureTheory.volume (targetShading.carrier index))
    cleanup.selectedIndices sourceSchedule.scaleCount data.Parent
    data.parent data.conflict
    proposition63MildRescalingQuotientConflictDegree
    data.conflict_refl data.conflict_symm data.conflict_degree

/-- Target family retained by the one common quotient-center selection. -/
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree) :
    WZ2PaperPureTubeSubfamily
      (proposition63MildRescalingFamily hscale raw) :=
  WZ2PaperPureTubeSubfamily.fromFinset
    (proposition63MildRescalingFamily hscale raw) selection.selected

/-- A quotient-selected target family remains ordinary essentially
distinct because selection starts inside the earlier ordinary cleanup. -/
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (cleanup : Proposition63MildRescalingCleanupData
      hscale raw targetShading)
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree)
    (hsubset : selection.selected ⊆ cleanup.selectedIndices) :
    WZ2PaperOrdinaryIsEssentiallyDistinct
      (data.selectedTarget selection).family := by
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
    apply (selection.selected.orderEmbOfFin rfl).injective
    change ambientFirst = ambientSecond
    rw [← hambientFirst, ← hambientSecond, heq]
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

/-- At one coordinate, restrict to the quotient parents hit by the common
selected target family. -/
theorem selectedCover
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree)
    (coordinate : Fin sourceSchedule.scaleCount) :
    Nonempty
      (Proposition63MildRescalingQuotientParentData.Proposition63MildRescalingSelectedQuotientCoverData
        (data.quotient coordinate) (data.selectedTarget selection)) := by
  apply (data.quotient coordinate).restrictToSeparatedHitParents
    (data.selectedTarget selection)
  intro first second hne hfirst hsecond
  apply lt_of_not_ge
  intro hconflict
  apply selection.hit_parent_separated coordinate first second hne
  · rcases hfirst with ⟨target, htarget⟩
    exact ⟨(data.selectedTarget selection).embedding target,
      Finset.orderEmbOfFin_mem selection.selected rfl target, htarget⟩
  · rcases hsecond with ⟨target, htarget⟩
    exact ⟨(data.selectedTarget selection).embedding target,
      Finset.orderEmbOfFin_mem selection.selected rfl target, htarget⟩
  · exact hconflict

/-- Choose the hit quotient-parent cover at one selected coordinate. -/
noncomputable def selectedCoverData
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree)
    (coordinate : Fin sourceSchedule.scaleCount) :
    Proposition63MildRescalingQuotientParentData.Proposition63MildRescalingSelectedQuotientCoverData
      (data.quotient coordinate) (data.selectedTarget selection) :=
  Classical.choice (data.selectedCover selection coordinate)

/-- Chosen quotient-parent family at one selected coordinate. -/
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree)
    (coordinate : Fin sourceSchedule.scaleCount) :
    WZ2PaperPureTubeSubfamily (data.quotient coordinate).parentFamily :=
  (data.selectedCoverData selection coordinate).selectedParents

/-- Literal target cover supplied by the selected quotient parents. -/
theorem selectedPartitioningCover
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree)
    (coordinate : Fin sourceSchedule.scaleCount) :
    WZ2PaperPurePartitioningCover
      (data.selectedTarget selection).family
      (data.selectedParents selection coordinate).family :=
  (data.selectedCoverData selection coordinate).cover

/-- Strict quotient-parent map at one representative scale. -/
noncomputable def selectedFiberParent
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree)
    (coordinate : Fin sourceSchedule.scaleCount) :
    Fin (data.selectedTarget selection).toTubeSubfamily.family.card →
      Fin (data.selectedParents selection coordinate).family.card :=
  (data.selectedPartitioningCover selection coordinate).parent

/-- The source actual-parent map on the same selected target indices. -/
def selectedSourceFiberParent
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree)
    (coordinate : Fin sourceSchedule.scaleCount) :
    Fin (data.selectedTarget selection).toTubeSubfamily.family.card →
      Fin (sourceSchedule.witness coordinate).scaleData.coarse.card :=
  fun target => (sourceSchedule.witness coordinate).scaleData.cover.parent
    ((data.selectedTarget selection).embedding target)

/-- Tagged quotient and source parents for the joint regularization. -/
abbrev JointParent
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree) : Type :=
  (Σ coordinate : Fin sourceSchedule.scaleCount,
      Fin (data.selectedParents selection coordinate).family.card) ⊕
    (Σ coordinate : Fin sourceSchedule.scaleCount,
      Fin (sourceSchedule.witness coordinate).scaleData.coarse.card)

/-- Parent map combining public quotient fibers and source actual packets. -/
def jointParent
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree)
    (joint : Fin (sourceSchedule.scaleCount + sourceSchedule.scaleCount)) :
    Fin (data.selectedTarget selection).toTubeSubfamily.family.card →
      data.JointParent selection :=
  Fin.addCases
    (fun coordinate target => Sum.inl
      ⟨coordinate, data.selectedFiberParent selection coordinate target⟩)
    (fun coordinate target => Sum.inr
      ⟨coordinate, data.selectedSourceFiberParent selection coordinate target⟩)
    joint

/-- One joint regularization of quotient strict fibers and source actual
packets.  This is the finite combinatorial datum needed by packetwise
actual-John transport. -/
theorem jointFiberRegularization
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
    (data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule)
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree)
    (targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)) :
    Nonempty (WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection)
      (data.jointParent selection)) := by
  exact wz2_prop_sticky_finite_parent_regularization
    (restrictPaperShading
      (data.selectedTarget selection).toTubeSubfamily targetShading)
    (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
    (fun _ => data.JointParent selection) (data.jointParent selection)

/-- Final target subfamily after the joint quotient/source packet
regularization. -/
def jointRegularizedTarget
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection)) :
    WZ2PaperPureTubeSubfamily (data.selectedTarget selection).family :=
  WZ2PaperPureTubeSubfamily.fromFinset
    (data.selectedTarget selection).family regularized.selected

/-- Exact ambient source index of a jointly regularized target tube. -/
def jointRegularizedSourceIndex
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection)) :
    Fin (data.jointRegularizedTarget regularized).family.card ↪
      Fin sourceFine.card :=
  (data.jointRegularizedTarget regularized).embedding.trans
    (data.selectedTarget selection).embedding

/-- Source actual-parent packet in the final target family. -/
def jointRegularizedSourcePacket
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card) :
    Finset (Fin (data.jointRegularizedTarget regularized).family.card) :=
  Finset.univ.filter fun target =>
    (sourceSchedule.witness coordinate).scaleData.cover.parent
      (data.jointRegularizedSourceIndex regularized target) = sourceParent

/-- Quotient parents hit by the joint-regularized target family. -/
def jointRegularizedParents
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount) :
    WZ2PaperPureTubeSubfamily
      (data.selectedParents selection coordinate).family :=
  (data.selectedPartitioningCover selection coordinate).hitParentSubfamily
    (data.jointRegularizedTarget regularized)

/-- Final literal quotient cover after the joint regularization. -/
theorem jointRegularizedCover
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount) :
    WZ2PaperPurePartitioningCover
      (data.jointRegularizedTarget regularized).family
      (data.jointRegularizedParents regularized coordinate).family :=
  (data.selectedPartitioningCover selection coordinate).restrictToHitParents
    (data.jointRegularizedTarget regularized)

/-- Exact selected quotient parent is determined by the ambient quotient
assignment. -/
theorem jointRegularizedCover_parent_ambient
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (target : Fin (data.jointRegularizedTarget regularized).family.card) :
    (data.jointRegularizedParents regularized coordinate).embedding
        ((data.jointRegularizedCover regularized coordinate).parent target) =
      data.selectedFiberParent selection coordinate
        ((data.jointRegularizedTarget regularized).embedding target) := by
  change
    ((data.selectedPartitioningCover selection coordinate).hitParentSubfamily
      (data.jointRegularizedTarget regularized)).embedding
        (((data.selectedPartitioningCover selection coordinate)
          |>.restrictToHitParents
            (data.jointRegularizedTarget regularized)).parent target) = _
  rw [(data.selectedPartitioningCover selection coordinate)
    |>.restrictToHitParents_parent_eq
      (data.quotient coordinate).caller_rho_pos.le
      (data.jointRegularizedTarget regularized) target]
  exact (data.selectedPartitioningCover selection coordinate).hitParent_ambient
    (data.jointRegularizedTarget regularized) target

/-- Tubes sharing a source actual parent also share their quotient parent. -/
theorem jointRegularizedCover_parent_eq_of_sourceParent_eq
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (first second : Fin
      (data.jointRegularizedTarget regularized).family.card)
    (hsource :
      (sourceSchedule.witness coordinate).scaleData.cover.parent
          (data.jointRegularizedSourceIndex regularized first) =
        (sourceSchedule.witness coordinate).scaleData.cover.parent
          (data.jointRegularizedSourceIndex regularized second)) :
    (data.jointRegularizedCover regularized coordinate).parent first =
      (data.jointRegularizedCover regularized coordinate).parent second := by
  apply (data.jointRegularizedParents regularized coordinate).embedding.injective
  rw [data.jointRegularizedCover_parent_ambient regularized coordinate first,
    data.jointRegularizedCover_parent_ambient regularized coordinate second]
  change (data.selectedPartitioningCover selection coordinate).parent
      ((data.jointRegularizedTarget regularized).embedding first) =
    (data.selectedPartitioningCover selection coordinate).parent
      ((data.jointRegularizedTarget regularized).embedding second)
  apply (data.selectedParents selection coordinate).embedding.injective
  change (data.selectedCoverData selection coordinate).selectedParents.embedding
      ((data.selectedCoverData selection coordinate).cover.parent
        ((data.jointRegularizedTarget regularized).embedding first)) =
    (data.selectedCoverData selection coordinate).selectedParents.embedding
      ((data.selectedCoverData selection coordinate).cover.parent
        ((data.jointRegularizedTarget regularized).embedding second))
  rw [(data.selectedCoverData selection coordinate).parent_ambient,
    (data.selectedCoverData selection coordinate).parent_ambient]
  unfold Proposition63MildRescalingQuotientParentData.assignedParent
  change (data.quotient coordinate).net.center
      ((sourceSchedule.witness coordinate).scaleData.cover.parent
        (data.jointRegularizedSourceIndex regularized first)) =
    (data.quotient coordinate).net.center
      ((sourceSchedule.witness coordinate).scaleData.cover.parent
        (data.jointRegularizedSourceIndex regularized second))
  rw [hsource]

/-- The joint regularizer's left coordinates are exactly the public quotient
fiber maps. -/
theorem jointRegularized_fullFiber_uniform
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount) :
    WZ2PaperPureFullFibersAreCUniform
      (data.jointRegularizedTarget regularized).family
      (data.jointRegularizedParents regularized coordinate).family
      (16 * ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
          ENNReal) *
        (Nat.log 2
          (2 * (data.selectedTarget selection).family.card) + 1 : ENNReal) ^
            (sourceSchedule.scaleCount + sourceSchedule.scaleCount)) := by
  apply (data.selectedPartitioningCover selection coordinate)
    |>.restrictToHitParents_fullFiber_uniform_of_subfamily
      (data.quotient coordinate).caller_rho_pos.le
      (data.jointRegularizedTarget regularized)
  intro first second hfirst hsecond
  let jointCoordinate : Fin
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount) :=
    Fin.castAdd sourceSchedule.scaleCount coordinate
  let firstJoint : data.JointParent selection := Sum.inl ⟨coordinate, first⟩
  let secondJoint : data.JointParent selection := Sum.inl ⟨coordinate, second⟩
  let finalFirst :=
    (Finset.univ : Finset (Fin regularized.selected.card)).filter fun source =>
      data.selectedFiberParent selection coordinate
        (regularized.selected.orderEmbOfFin rfl source) = first
  let finalSecond :=
    (Finset.univ : Finset (Fin regularized.selected.card)).filter fun source =>
      data.selectedFiberParent selection coordinate
        (regularized.selected.orderEmbOfFin rfl source) = second
  have ambientFirstEq :
      (regularized.selected.filter fun index =>
        data.jointParent selection jointCoordinate index = firstJoint) =
      (regularized.selected.filter fun index =>
        data.selectedFiberParent selection coordinate index = first) := by
    ext index
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor <;> rintro ⟨hindex, heq⟩
    · exact ⟨hindex, by
        simpa [firstJoint, jointCoordinate, jointParent] using heq⟩
    · exact ⟨hindex, by
        simpa [firstJoint, jointCoordinate, jointParent] using heq⟩
  have ambientSecondEq :
      (regularized.selected.filter fun index =>
        data.jointParent selection jointCoordinate index = secondJoint) =
      (regularized.selected.filter fun index =>
        data.selectedFiberParent selection coordinate index = second) := by
    ext index
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor <;> rintro ⟨hindex, heq⟩
    · exact ⟨hindex, by
        simpa [secondJoint, jointCoordinate, jointParent] using heq⟩
    · exact ⟨hindex, by
        simpa [secondJoint, jointCoordinate, jointParent] using heq⟩
  have finalFirstPos : 0 < finalFirst.card := by
    change 0 < (((Finset.univ : Finset (Fin regularized.selected.card)).filter
      (fun source => data.selectedFiberParent selection coordinate
        (regularized.selected.orderEmbOfFin rfl source) = first))).card
    exact hfirst
  have finalSecondPos : 0 < finalSecond.card := by
    change 0 < (((Finset.univ : Finset (Fin regularized.selected.card)).filter
      (fun source => data.selectedFiberParent selection coordinate
        (regularized.selected.orderEmbOfFin rfl source) = second))).card
    exact hsecond
  have firstCardEq : finalFirst.card =
      (regularized.selected.filter fun index =>
        data.selectedFiberParent selection coordinate index = first).card :=
    fromFinset_filter_card regularized.selected
      (data.selectedFiberParent selection coordinate) first
  have secondCardEq : finalSecond.card =
      (regularized.selected.filter fun index =>
        data.selectedFiberParent selection coordinate index = second).card :=
    fromFinset_filter_card regularized.selected
      (data.selectedFiberParent selection coordinate) second
  have ambientFirstPos : 0 <
      (regularized.selected.filter fun index =>
        data.selectedFiberParent selection coordinate index = first).card :=
    firstCardEq ▸ finalFirstPos
  have ambientSecondPos : 0 <
      (regularized.selected.filter fun index =>
        data.selectedFiberParent selection coordinate index = second).card :=
    secondCardEq ▸ finalSecondPos
  have hfirstForDegree : 0 <
      (regularized.selected.filter fun index =>
        data.jointParent selection jointCoordinate index = firstJoint).card := by
    have heq :
        (regularized.selected.filter fun index =>
          data.jointParent selection jointCoordinate index = firstJoint) =
        (regularized.selected.filter fun index =>
          data.selectedFiberParent selection coordinate index = first) :=
      ambientFirstEq
    rw [heq]
    exact ambientFirstPos
  have hsecondForDegree : 0 <
      (regularized.selected.filter fun index =>
        data.jointParent selection jointCoordinate index = secondJoint).card := by
    have heq :
        (regularized.selected.filter fun index =>
          data.jointParent selection jointCoordinate index = secondJoint) =
        (regularized.selected.filter fun index =>
          data.selectedFiberParent selection coordinate index = second) :=
      ambientSecondEq
    rw [heq]
    exact ambientSecondPos
  have hdegree := regularized.degree_uniform jointCoordinate
    firstJoint secondJoint
    hfirstForDegree hsecondForDegree
  change (finalFirst.card : ENNReal) ≤ _ * (finalSecond.card : ENNReal)
  rw [firstCardEq, secondCardEq]
  rw [ambientFirstEq, ambientSecondEq] at hdegree
  exact hdegree

/-- The joint regularizer's right coordinates are exactly the original
source actual-parent packets. -/
theorem jointRegularized_sourcePacket_uniform
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (first second :
      Fin (sourceSchedule.witness coordinate).scaleData.coarse.card)
    (hfirst : 0 < ((Finset.univ : Finset
        (Fin (data.jointRegularizedTarget regularized).family.card)).filter
      fun target => data.selectedSourceFiberParent selection coordinate
        ((data.jointRegularizedTarget regularized).embedding target) =
          first).card)
    (hsecond : 0 < ((Finset.univ : Finset
        (Fin (data.jointRegularizedTarget regularized).family.card)).filter
      fun target => data.selectedSourceFiberParent selection coordinate
        ((data.jointRegularizedTarget regularized).embedding target) =
          second).card) :
    (((Finset.univ : Finset
        (Fin (data.jointRegularizedTarget regularized).family.card)).filter
      fun target => data.selectedSourceFiberParent selection coordinate
        ((data.jointRegularizedTarget regularized).embedding target) =
          first).card : ENNReal) ≤
      (16 * ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
          ENNReal) *
        (Nat.log 2
          (2 * (data.selectedTarget selection).family.card) + 1 : ENNReal) ^
            (sourceSchedule.scaleCount + sourceSchedule.scaleCount)) *
      (((Finset.univ : Finset
          (Fin (data.jointRegularizedTarget regularized).family.card)).filter
        fun target => data.selectedSourceFiberParent selection coordinate
          ((data.jointRegularizedTarget regularized).embedding target) =
            second).card : ENNReal) := by
  let jointCoordinate : Fin
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount) :=
    Fin.natAdd sourceSchedule.scaleCount coordinate
  let firstJoint : data.JointParent selection := Sum.inr ⟨coordinate, first⟩
  let secondJoint : data.JointParent selection := Sum.inr ⟨coordinate, second⟩
  let ambientFirst := regularized.selected.filter fun index =>
    data.jointParent selection jointCoordinate index = firstJoint
  let ambientSecond := regularized.selected.filter fun index =>
    data.jointParent selection jointCoordinate index = secondJoint
  let finalFirst :=
    (Finset.univ : Finset (Fin regularized.selected.card)).filter fun source =>
      data.selectedSourceFiberParent selection coordinate
        (regularized.selected.orderEmbOfFin rfl source) = first
  let finalSecond :=
    (Finset.univ : Finset (Fin regularized.selected.card)).filter fun source =>
      data.selectedSourceFiberParent selection coordinate
        (regularized.selected.orderEmbOfFin rfl source) = second
  have finalFirstPos : 0 < finalFirst.card := by
    change 0 < (((Finset.univ : Finset (Fin regularized.selected.card)).filter
      (fun source => data.selectedSourceFiberParent selection coordinate
        (regularized.selected.orderEmbOfFin rfl source) = first))).card
    exact hfirst
  have finalSecondPos : 0 < finalSecond.card := by
    change 0 < (((Finset.univ : Finset (Fin regularized.selected.card)).filter
      (fun source => data.selectedSourceFiberParent selection coordinate
        (regularized.selected.orderEmbOfFin rfl source) = second))).card
    exact hsecond
  have firstCardEq : finalFirst.card = ambientFirst.card := by
    apply Finset.card_bij
      (fun source _ => regularized.selected.orderEmbOfFin rfl source)
    · intro source hsource
      apply Finset.mem_filter.mpr
      refine ⟨Finset.orderEmbOfFin_mem regularized.selected rfl source, ?_⟩
      have hparent := (Finset.mem_filter.mp hsource).2
      change data.jointParent selection jointCoordinate
          (regularized.selected.orderEmbOfFin rfl source) = firstJoint
      simp only [jointCoordinate, jointParent, Fin.addCases_right, firstJoint]
      exact congrArg Sum.inr (Sigma.eq rfl hparent)
    · intro firstIndex _ secondIndex _ heq
      exact (regularized.selected.orderEmbOfFin rfl).injective heq
    · intro ambient hambient
      rcases Finset.mem_filter.mp hambient with ⟨hselected, hparent⟩
      let source : Fin regularized.selected.card :=
        (regularized.selected.orderIsoOfFin rfl).symm ⟨ambient, hselected⟩
      have hembedding :
          regularized.selected.orderEmbOfFin rfl source = ambient :=
        congrArg Subtype.val
          (regularized.selected.orderIsoOfFin rfl
            |>.apply_symm_apply ⟨ambient, hselected⟩)
      refine ⟨source, ?_, hembedding⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ source, ?_⟩
      have hparent' := hparent
      rw [← hembedding] at hparent'
      simp only [jointCoordinate, jointParent, Fin.addCases_right, firstJoint]
        at hparent'
      change (Sum.inr
          (Sigma.mk coordinate
            (data.selectedSourceFiberParent selection coordinate
              (regularized.selected.orderEmbOfFin rfl source))) :
            data.JointParent selection) =
        Sum.inr (Sigma.mk coordinate first) at hparent'
      have hsigma := Sum.inr.inj hparent'
      exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
  have secondCardEq : finalSecond.card = ambientSecond.card := by
    apply Finset.card_bij
      (fun source _ => regularized.selected.orderEmbOfFin rfl source)
    · intro source hsource
      apply Finset.mem_filter.mpr
      refine ⟨Finset.orderEmbOfFin_mem regularized.selected rfl source, ?_⟩
      have hparent := (Finset.mem_filter.mp hsource).2
      change data.jointParent selection jointCoordinate
          (regularized.selected.orderEmbOfFin rfl source) = secondJoint
      simp only [jointCoordinate, jointParent, Fin.addCases_right, secondJoint]
      exact congrArg Sum.inr (Sigma.eq rfl hparent)
    · intro firstIndex _ secondIndex _ heq
      exact (regularized.selected.orderEmbOfFin rfl).injective heq
    · intro ambient hambient
      rcases Finset.mem_filter.mp hambient with ⟨hselected, hparent⟩
      let source : Fin regularized.selected.card :=
        (regularized.selected.orderIsoOfFin rfl).symm ⟨ambient, hselected⟩
      have hembedding :
          regularized.selected.orderEmbOfFin rfl source = ambient :=
        congrArg Subtype.val
          (regularized.selected.orderIsoOfFin rfl
            |>.apply_symm_apply ⟨ambient, hselected⟩)
      refine ⟨source, ?_, hembedding⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ source, ?_⟩
      have hparent' := hparent
      rw [← hembedding] at hparent'
      simp only [jointCoordinate, jointParent, Fin.addCases_right, secondJoint]
        at hparent'
      change (Sum.inr
          (Sigma.mk coordinate
            (data.selectedSourceFiberParent selection coordinate
              (regularized.selected.orderEmbOfFin rfl source))) :
            data.JointParent selection) =
        Sum.inr (Sigma.mk coordinate second) at hparent'
      have hsigma := Sum.inr.inj hparent'
      exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
  have hfirstPositive : 0 < ambientFirst.card :=
    firstCardEq ▸ finalFirstPos
  have hsecondPositive : 0 < ambientSecond.card :=
    secondCardEq ▸ finalSecondPos
  have hdegree := regularized.degree_uniform jointCoordinate
    firstJoint secondJoint
    (by simpa [ambientFirst] using hfirstPositive)
    (by simpa [ambientSecond] using hsecondPositive)
  change (finalFirst.card : ENNReal) ≤ _ * (finalSecond.card : ENNReal)
  rw [firstCardEq, secondCardEq]
  simpa [ambientFirst, ambientSecond, WZ2PaperPureTubeSubfamily.toTubeSubfamily]
    using hdegree

/-- The source-parent packets partition the joint-regularized target family. -/
theorem sum_jointRegularizedSourcePacket_card
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount) :
    (∑ sourceParent,
        ((data.jointRegularizedSourcePacket regularized coordinate
          sourceParent).card : ENNReal)) =
      (data.jointRegularizedTarget regularized).family.enncard := by
  change (∑ sourceParent,
      (((Finset.univ : Finset (Fin regularized.selected.card)).filter
        (fun target =>
          data.selectedSourceFiberParent selection coordinate
            (regularized.selected.orderEmbOfFin rfl target) =
              sourceParent)).card : ENNReal)) =
    (regularized.selected.card : ENNReal)
  have partition :
      (∑ sourceParent : Fin
          (sourceSchedule.witness coordinate).scaleData.coarse.card,
        ((Finset.univ : Finset (Fin regularized.selected.card)).filter
          (fun target =>
            data.selectedSourceFiberParent selection coordinate
              (regularized.selected.orderEmbOfFin rfl target) =
                sourceParent)).card) =
        regularized.selected.card :=
    (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin regularized.selected.card))
      (Finset.univ : Finset (Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card))
      (fun target => data.selectedSourceFiberParent selection coordinate
        (regularized.selected.orderEmbOfFin rfl target))).trans (by simp)
  rw [← Nat.cast_sum]
  exact_mod_cast partition

/-- The complete actual source fibers partition the source family. -/
theorem sum_sourceFullFiber_card
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
    (_data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule)
    (coordinate : Fin sourceSchedule.scaleCount) :
    (∑ sourceParent,
        ((wz2PaperOrdinaryFullFiberIndices sourceFine
          (sourceSchedule.witness coordinate).scaleData.coarse
          sourceParent).card : ENNReal)) = sourceFine.enncard :=
  (sourceSchedule.witness coordinate).scaleData.cover.sum_fullFiberCount
    (sourceSchedule.witness coordinate).scaleData.rho_pos.le

/-- Pointwise ambient-to-selected ratio for one nonempty source packet. -/
private theorem weightedFiberRatioAtPositiveSelected
    {Parent : Type*} [Fintype Parent] [Nonempty Parent]
    (ambient selected : Parent → ENNReal)
    (normalizationWeight ambientConstant selectedConstant
      retentionConstant : ENNReal)
    (ambientUniform : ∀ first second,
      ambient first ≤ ambientConstant * ambient second)
    (selectedUniform : ∀ first second,
      0 < selected first → 0 < selected second →
      selected first ≤ selectedConstant * selected second)
    (retained :
      normalizationWeight * (∑ parent, ambient parent) ≤
        retentionConstant * ∑ parent, selected parent)
    (parent : Parent) (parentPositive : 0 < selected parent) :
    normalizationWeight * ambient parent ≤
      ambientConstant * retentionConstant * selectedConstant *
        selected parent := by
  let parentCount : ENNReal := Fintype.card Parent
  have parentCountPos : 0 < parentCount := by
    simpa [parentCount] using
      (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card Parent) :
        (0 : ENNReal) < Fintype.card Parent)
  have parentCountTop : parentCount ≠ ⊤ := by simp [parentCount]
  have ambientSum :
      parentCount * ambient parent ≤
        ambientConstant * ∑ other, ambient other := by
    calc
      parentCount * ambient parent = ∑ _other : Parent, ambient parent := by
        simp [parentCount]
      _ ≤ ∑ other : Parent, ambientConstant * ambient other := by
        exact Finset.sum_le_sum fun other _ => ambientUniform parent other
      _ = ambientConstant * ∑ other, ambient other := by
        rw [Finset.mul_sum]
  have selectedTo : ∀ other,
      selected other ≤ selectedConstant * selected parent := by
    intro other
    by_cases otherPositive : 0 < selected other
    · exact selectedUniform other parent otherPositive parentPositive
    · have otherZero : selected other = 0 := by
        simpa [not_lt] using otherPositive
      rw [otherZero]
      exact bot_le
  have selectedSum :
      (∑ other, selected other) ≤
        parentCount * (selectedConstant * selected parent) := by
    calc
      (∑ other, selected other) ≤
          ∑ _other : Parent, selectedConstant * selected parent := by
        exact Finset.sum_le_sum fun other _ => selectedTo other
      _ = parentCount * (selectedConstant * selected parent) := by
        simp [parentCount]
  have withCount :
      parentCount * (normalizationWeight * ambient parent) ≤
        parentCount *
          (ambientConstant * retentionConstant * selectedConstant *
            selected parent) := by
    calc
      parentCount * (normalizationWeight * ambient parent) =
          normalizationWeight * (parentCount * ambient parent) := by ring
      _ ≤ normalizationWeight *
          (ambientConstant * ∑ other, ambient other) := by gcongr
      _ = ambientConstant *
          (normalizationWeight * ∑ other, ambient other) := by ring
      _ ≤ ambientConstant *
          (retentionConstant * ∑ other, selected other) := by gcongr
      _ ≤ ambientConstant *
          (retentionConstant *
            (parentCount * (selectedConstant * selected parent))) := by
        gcongr
      _ = parentCount *
          (ambientConstant * retentionConstant * selectedConstant *
            selected parent) := by ring
  have withCount' :
      (normalizationWeight * ambient parent) * parentCount ≤
        (ambientConstant * retentionConstant * selectedConstant *
          selected parent) * parentCount := by
    simpa [mul_comm] using withCount
  exact (ENNReal.mul_le_mul_iff_left
    parentCountPos.ne' parentCountTop).mp withCount'

/-- A nonempty selected source packet controls its complete source fiber. -/
theorem sourceFullFiber_weighted_card_le_packet
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
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (normalizationWeight retentionConstant : ENNReal)
    (globalRetention : normalizationWeight * sourceFine.enncard ≤
      retentionConstant *
        (data.jointRegularizedTarget regularized).family.enncard)
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card)
    (packetPositive : 0 <
      (data.jointRegularizedSourcePacket regularized coordinate
        sourceParent).card) :
    normalizationWeight *
        ((wz2PaperOrdinaryFullFiberIndices sourceFine
          (sourceSchedule.witness coordinate).scaleData.coarse
          sourceParent).card : ENNReal) ≤
      sourceConstant * retentionConstant *
          (16 * ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
              ENNReal) *
            (Nat.log 2
              (2 * (data.selectedTarget selection).family.card) + 1 :
                ENNReal) ^
              (sourceSchedule.scaleCount + sourceSchedule.scaleCount)) *
        ((data.jointRegularizedSourcePacket regularized coordinate
          sourceParent).card : ENNReal) := by
  let ambient : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card →
      ENNReal := fun parent =>
    (wz2PaperOrdinaryFullFiberIndices sourceFine
      (sourceSchedule.witness coordinate).scaleData.coarse parent).card
  let selectedPacket : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card →
      ENNReal := fun parent =>
    (data.jointRegularizedSourcePacket regularized coordinate parent).card
  have ambientUniform : ∀ first second,
      ambient first ≤ sourceConstant * ambient second :=
    (sourceSchedule.witness coordinate).scaleData.full_fiber_uniform
  have selectedUniform : ∀ first second,
      0 < selectedPacket first → 0 < selectedPacket second →
      selectedPacket first ≤
        (16 * ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
            ENNReal) *
          (Nat.log 2
            (2 * (data.selectedTarget selection).family.card) + 1 :
              ENNReal) ^
            (sourceSchedule.scaleCount + sourceSchedule.scaleCount)) *
          selectedPacket second := by
    intro first second firstPositive secondPositive
    apply data.jointRegularized_sourcePacket_uniform regularized coordinate
    · change 0 <
        (data.jointRegularizedSourcePacket regularized coordinate first).card
      exact (Nat.cast_pos (α := ENNReal)).mp
        (by simpa only [selectedPacket] using firstPositive)
    · change 0 <
        (data.jointRegularizedSourcePacket regularized coordinate second).card
      exact (Nat.cast_pos (α := ENNReal)).mp
        (by simpa only [selectedPacket] using secondPositive)
  have sumRetention :
      normalizationWeight * (∑ parent, ambient parent) ≤
        retentionConstant * ∑ parent, selectedPacket parent := by
    rw [show (∑ parent, ambient parent) = sourceFine.enncard by
      simpa [ambient] using data.sum_sourceFullFiber_card coordinate]
    rw [show (∑ parent, selectedPacket parent) =
        (data.jointRegularizedTarget regularized).family.enncard by
      simpa [selectedPacket] using
        data.sum_jointRegularizedSourcePacket_card regularized coordinate]
    exact globalRetention
  letI : Nonempty
      (Fin (sourceSchedule.witness coordinate).scaleData.coarse.card) :=
    ⟨sourceParent⟩
  have ratio := weightedFiberRatioAtPositiveSelected ambient selectedPacket
    normalizationWeight sourceConstant
      (16 * ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
          ENNReal) *
        (Nat.log 2
          (2 * (data.selectedTarget selection).family.card) + 1 : ENNReal) ^
          (sourceSchedule.scaleCount + sourceSchedule.scaleCount))
      retentionConstant ambientUniform selectedUniform sumRetention
      sourceParent (by
        change (0 : ENNReal) <
          ((data.jointRegularizedSourcePacket regularized coordinate
            sourceParent).card : ENNReal)
        exact Nat.cast_pos.mpr packetPositive)
  simpa only [ambient, selectedPacket] using ratio

end Proposition63MildRescalingQuotientScheduleData

/-- Build all one-scale quotients from the existing finite source schedule. -/
noncomputable def proposition63_mild_rescaling_quotient_schedule
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
    (sourceNonempty : sourceFine.Nonempty)
    (sourceLine : WZ1PaperIsLineClass sourceFine)
    (sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFine)
    (sourceMidpoint : ∀ source,
      ‖wz2PaperTubeMidpoint (sourceFine.tube source)‖ ≤ 3)
    (rawLine : WZ1PaperIsLineClass raw.family)
    (centerHeight : |center 2| ≤ 2) :
    Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule := by
  let representative : ∀ coordinate,
      Proposition63MildRescalingParentCoverData
        (sourceSchedule.witness coordinate).scaleData hscale raw
        (proposition63MildRescalingTargetRho sourceDelta
          (sourceSchedule.witness coordinate).rho scale) :=
    fun coordinate => Proposition63MildRescalingParentCoverData.ofSource
      (sourceSchedule.witness coordinate).scaleData hscale raw
      sourceNonempty sourceLine sourceDistinct sourceMidpoint rawLine
      centerHeight
  exact {
    representative := representative
    quotient := fun coordinate => Classical.choice
      (proposition63_mild_rescaling_quotient_parent
        (representative coordinate))
  }

end Kakeya.Assouad.PureWZ2

end
