import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingFiniteParentSchedule
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteParentRegularization
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteRegularizedRefinement
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureHitParentRestriction

/-!
# Simultaneous target-fiber regularization for Proposition 6.3

After the common strong-parent selection has made the enlarged target
parents into literal strict covers, the paper performs a second finite
pigeonholing.  It regularizes the cardinalities of the actual strict target
fibers at every representative nearby scale.  This module implements exactly
that step and exposes the resulting strict covers and fiber uniformity.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

attribute [local instance] Classical.propDecidable

namespace Proposition63MildRescalingFiniteParentScheduleData

/-- The target shading after the common strong-parent selection. -/
def selectedTargetShading
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
    (targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)) :
    WZ1PaperTubeShading (selectedTarget selection).family :=
  restrictPaperShading (selectedTarget selection).toTubeSubfamily
    targetShading

/-- Strict target-parent map at one representative scale, after the first
common selection. -/
def selectedFiberParent
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
    Fin (selectedTarget selection).family.card →
      Fin (selectedParents selection coordinate).family.card :=
  (selectedPartitioningCover selection coordinate).parent

/-- Simultaneously regularize the genuine strict target fibers at all
representative scales. -/
theorem finiteFiberRegularization
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
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree)
    (targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)) :
    Nonempty (WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection)) := by
  exact wz2_prop_sticky_finite_parent_regularization
    (selectedTargetShading selection targetShading)
    sourceSchedule.scaleCount
    (fun coordinate =>
      Fin (selectedParents selection coordinate).family.card)
    (selectedFiberParent selection)

/-- The final target family after both finite selections, viewed as a pure
subfamily of the first selected target. -/
def fiberRegularizedSubfamily
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
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection)) :
    WZ2PaperPureTubeSubfamily (selectedTarget selection).family :=
  WZ2PaperPureTubeSubfamily.fromFinset
    (selectedTarget selection).family regularized.selected

/-- Original source index carried by one tube surviving both target
selections. -/
def fiberRegularizedSourceIndex
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
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection)) :
    Fin (fiberRegularizedSubfamily regularized).family.card ↪
      Fin sourceFine.card :=
  (fiberRegularizedSubfamily regularized).embedding.trans
    (selectedTarget selection).embedding

@[simp] theorem fiberRegularizedSourceIndex_eq_target_embedding
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
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection))
    (index : Fin (fiberRegularizedSubfamily regularized).family.card) :
    fiberRegularizedSourceIndex regularized index =
      (selectedTarget selection).embedding
        ((fiberRegularizedSubfamily regularized).embedding index) := by
  rfl

/-- The target parents hit after the second selection. -/
def fiberRegularizedParents
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
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection))
    (coordinate : Fin sourceSchedule.scaleCount) :
    WZ2PaperPureTubeSubfamily
      (selectedParents selection coordinate).family :=
  (selectedPartitioningCover selection coordinate).hitParentSubfamily
    (fiberRegularizedSubfamily regularized)

/-- The final literal strict cover at a representative scale. -/
def fiberRegularizedCover
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
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection))
    (coordinate : Fin sourceSchedule.scaleCount) :
    WZ2PaperPurePartitioningCover
      (fiberRegularizedSubfamily regularized).family
      (fiberRegularizedParents regularized coordinate).family :=
  (selectedPartitioningCover selection coordinate).restrictToHitParents
    (fiberRegularizedSubfamily regularized)

/-- The ambient source parent corresponding to a parent surviving both
finite selections. -/
def fiberRegularizedSourceParent
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
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection))
    (coordinate : Fin sourceSchedule.scaleCount) :
    Fin (fiberRegularizedParents regularized coordinate).family.card →
      Fin (sourceSchedule.witness coordinate).scaleData.coarse.card :=
  fun parent =>
    (selectedParents selection coordinate).embedding
      ((fiberRegularizedParents regularized coordinate).embedding parent)

/-- The final target cover still records the exact source-cover parent. -/
theorem fiberRegularizedCover_parent_source
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
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (source : Fin (fiberRegularizedSubfamily regularized).family.card) :
    fiberRegularizedSourceParent regularized coordinate
        ((fiberRegularizedCover regularized coordinate).parent source) =
      (sourceSchedule.witness coordinate).scaleData.cover.parent
        ((selectedSource selection).embedding
          (selectedTargetSourceIndexEquiv selection
            ((fiberRegularizedSubfamily regularized).embedding source))) := by
  have hparent :=
    (selectedPartitioningCover selection coordinate).hitParent_ambient
      (fiberRegularizedSubfamily regularized) source
  have hfirstMem :
      (fiberRegularizedSubfamily regularized).embedding source ∈
        wz2PaperOrdinaryFullFiberIndices
          (selectedTarget selection).family
          (selectedParents selection coordinate).family
          ((fiberRegularizedParents regularized coordinate).embedding
            ((fiberRegularizedCover regularized coordinate).parent source)) := by
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    have hfinal :=
      (mem_wz2PaperOrdinaryFullFiberIndices_iff
        ((fiberRegularizedCover regularized coordinate).parent source)
        source).mp
          ((fiberRegularizedCover regularized coordinate).parent_mem_fullFiber
            source)
    rw [(fiberRegularizedSubfamily regularized).tube_eq,
      (fiberRegularizedParents regularized coordinate).tube_eq] at hfinal
    exact hfinal
  have hfirstParent :
      (selectedPartitioningCover selection coordinate).parent
          ((fiberRegularizedSubfamily regularized).embedding source) =
        (fiberRegularizedParents regularized coordinate).embedding
          ((fiberRegularizedCover regularized coordinate).parent source) :=
    ((selectedPartitioningCover selection coordinate).mem_fullFiber_iff_parent_eq
      (data.parentCover coordinate).target_rho_pos.le _ _).mp hfirstMem
  change
    (selectedParents selection coordinate).embedding
        ((fiberRegularizedParents regularized coordinate).embedding
          ((fiberRegularizedCover regularized coordinate).parent source)) = _
  rw [← hfirstParent]
  rw [selectedPartitioningCover_parent selection coordinate]
  let sourceHitParent :=
    (sourceSchedule.witness coordinate).scaleData.cover.hitParent
      (selectedSource selection)
      (selectedTargetSourceIndexEquiv selection
        ((fiberRegularizedSubfamily regularized).embedding source))
  have hselectedParent :
      (selectedParents selection coordinate).embedding
          ((selectedParentSourceIndexEquiv selection coordinate).symm
            sourceHitParent) =
        ((sourceSchedule.witness coordinate).scaleData.cover
          |>.hitParentSubfamily (selectedSource selection)).embedding
            sourceHitParent := by
    rw [← selectedParentSourceIndexEquiv_embedding selection coordinate]
    simp
  rw [hselectedParent]
  exact (sourceSchedule.witness coordinate).scaleData.cover
    |>.hitParent_ambient (selectedSource selection) _

/-- The regularizer's degree statement is exactly public strict-full-fiber
uniformity for the final literal target cover. -/
theorem fiberRegularized_fullFiber_uniform
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
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection))
    (coordinate : Fin sourceSchedule.scaleCount) :
    WZ2PaperPureFullFibersAreCUniform
      (fiberRegularizedSubfamily regularized).family
      (fiberRegularizedParents regularized coordinate).family
      (16 * (sourceSchedule.scaleCount : ENNReal) *
        (Nat.log 2 (2 * (selectedTarget selection).family.card) + 1 :
          ENNReal) ^ sourceSchedule.scaleCount) := by
  apply (selectedPartitioningCover selection coordinate)
    |>.restrictToHitParents_fullFiber_uniform_of_subfamily
      (data.parentCover coordinate).target_rho_pos.le
      (fiberRegularizedSubfamily regularized)
  intro first second hfirst hsecond
  have hfirstCard := fromFinset_filter_card regularized.selected
    (selectedFiberParent selection coordinate) first
  have hsecondCard := fromFinset_filter_card regularized.selected
    (selectedFiberParent selection coordinate) second
  change 0 < ((Finset.univ : Finset (Fin regularized.selected.card)).filter
      fun index => selectedFiberParent selection coordinate
        (regularized.selected.orderEmbOfFin rfl index) = first).card at hfirst
  change 0 < ((Finset.univ : Finset (Fin regularized.selected.card)).filter
      fun index => selectedFiberParent selection coordinate
        (regularized.selected.orderEmbOfFin rfl index) = second).card at hsecond
  have hfirstPositive : 0 <
      (regularized.selected.filter fun index =>
        selectedFiberParent selection coordinate index = first).card := by
    rw [← hfirstCard]
    exact hfirst
  have hsecondPositive : 0 <
      (regularized.selected.filter fun index =>
        selectedFiberParent selection coordinate index = second).card := by
    rw [← hsecondCard]
    exact hsecond
  have hdegree := regularized.degree_uniform coordinate first second
    hfirstPositive hsecondPositive
  rw [← hfirstCard, ← hsecondCard] at hdegree
  change ((Finset.univ : Finset (Fin regularized.selected.card)).filter
      fun index => selectedFiberParent selection coordinate
        (regularized.selected.orderEmbOfFin rfl index) = first).card ≤
    (16 * (sourceSchedule.scaleCount : ENNReal) *
        (Nat.log 2 (2 * (selectedTarget selection).family.card) + 1 :
          ENNReal) ^ sourceSchedule.scaleCount) *
      ((Finset.univ : Finset (Fin regularized.selected.card)).filter
        fun index => selectedFiberParent selection coordinate
          (regularized.selected.orderEmbOfFin rfl index) = second).card
  exact hdegree

end Proposition63MildRescalingFiniteParentScheduleData

end Kakeya.Assouad.PureWZ2

end
