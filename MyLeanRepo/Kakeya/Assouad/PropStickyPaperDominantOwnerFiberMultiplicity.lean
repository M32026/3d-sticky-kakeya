import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCompleteFiberReindex
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoarseSelectionPullbackStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantOwnerExactificationStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentOwnerPreparationStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalMultiplicityComparison
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGlobalMultiplicityHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume

/-!
# Fine multiplicity through dominant-owner exactification

The WZ2 proof sketch first fixes one common `mu_fine`, then repeatedly
restricts later shadings while preserving that property.  Dominant-owner
exactification keeps complete parent fibers and, inside one fixed fiber,
intersects every carrier with the same union of selected whole cells.
Consequently the point multiplicity on the surviving fiber is unchanged.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem
    WZ2PaperDominantOwnerExactificationData.full_fiber_pointMultiplicity_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {active :
      WZ2PaperBalancedActiveParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData hdelta hrho}
    {multiplicityLevel : ℕ}
    {degree :
      WZ2PaperBalancedParentDegreeData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel}
    {dominant :
      WZ2PaperDominantParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree}
    {owned :
      WZ2PaperDominantParentFineCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree dominant}
    (exactified :
      WZ2PaperDominantOwnerExactificationData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree
        dominant owned)
    (parent :
      Fin
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          coarse exactified.retainedParents).family.card)
    (point : Point3)
    (hpoint :
      point ∈
        (restrictPaperShading
          (exactified.restrictedCover.fullFiberSubfamily parent)
          exactified.refined).union) :
    (restrictPaperShading
        (exactified.restrictedCover.fullFiberSubfamily parent)
        exactified.refined).pointMultiplicity point =
      (restrictPaperShading
        (cover.fullFiberSubfamily
          ((Kakeya.Streamlined.TubeSubfamily.fromFinset
            coarse exactified.retainedParents).embedding parent))
        balancing.refined).pointMultiplicity point := by
  let packedCoarse :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      coarse exactified.retainedParents
  let localFiber :=
    exactified.restrictedCover.fullFiberSubfamily parent
  let selectedBase :=
    restrictPaperShading exactified.selected balancing.refined
  let localExact :=
    restrictPaperShading localFiber exactified.refined
  let localBase :=
    restrictPaperShading localFiber selectedBase
  let ownerRegion : Set Point3 :=
    ⋃ cell ∈ exactified.retainedCells,
      if packedCoarse.embedding parent =
          dominant.dominantParent cell then
        ⋃ fineCell ∈ exactified.selectedOwnerFineCells cell,
          wz1PaperGridCube delta fineCell
      else ∅
  have hAmbientParent :
      ∀ index : Fin localFiber.family.card,
        cover.parent
            (exactified.selected.embedding
              (localFiber.embedding index)) =
          packedCoarse.embedding parent := by
    intro index
    have hLocal :
        localFiber.embedding index ∈
          wz2PaperFullFiberIndices
            exactified.selected.family packedCoarse.family parent :=
      exactified.restrictedCover.fullFiberSubfamily_mem parent index
    have hImage :
        exactified.selected.embedding (localFiber.embedding index) ∈
          Finset.image exactified.selected.embedding
            (wz2PaperFullFiberIndices
              exactified.selected.family packedCoarse.family parent) :=
      Finset.mem_image.mpr
        ⟨localFiber.embedding index, hLocal, rfl⟩
    rw [exactified.full_fiber_complete parent] at hImage
    exact
      (cover.mem_fullFiber_iff_parent
        (packedCoarse.embedding parent)
        (exactified.selected.embedding
          (localFiber.embedding index))).mp hImage
  have hCarrier :
      ∀ index : Fin localFiber.family.card,
        localExact.carrier index =
          localBase.carrier index ∩ ownerRegion := by
    intro index
    change
      exactified.refined.carrier (localFiber.embedding index) =
        balancing.refined.carrier
            (exactified.selected.embedding
              (localFiber.embedding index)) ∩
          ownerRegion
    rw [exactified.refined_carrier_eq]
    rw [hAmbientParent index]
  have hWholeCell :
      localExact.pointMultiplicity point =
        localBase.pointMultiplicity point :=
    wholeCellRestriction_pointMultiplicity_eq
      (fine := localFiber.family)
      (S := localBase) (T := localExact) (U := ownerRegion)
      hCarrier (by simpa [localExact, localFiber] using hpoint)
  have hComplete :
      localBase.pointMultiplicity point =
        (restrictPaperShading
          (cover.fullFiberSubfamily (packedCoarse.embedding parent))
          balancing.refined).pointMultiplicity point := by
    simpa [localBase, selectedBase, localFiber] using
      wz2_paper_complete_fiber_restrict_pointMultiplicity_eq
        cover exactified.selected exactified.restrictedCover
        parent (packedCoarse.embedding parent)
        (exactified.full_fiber_complete parent)
        balancing.refined point
  simpa [localExact, localBase, selectedBase, localFiber,
    packedCoarse] using hWholeCell.trans hComplete

theorem
    WZ2PaperCoarseSelectionPullbackData.full_fiber_pointMultiplicity_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {active :
      WZ2PaperBalancedActiveParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData hdelta hrho}
    {multiplicityLevel : ℕ}
    {degree :
      WZ2PaperBalancedParentDegreeData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel}
    {dominant :
      WZ2PaperDominantParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree}
    {owned :
      WZ2PaperDominantParentFineCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree dominant}
    {exactified :
      WZ2PaperDominantOwnerExactificationData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree
        dominant owned}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    {regularization :
      WZ2PaperCoarseOwnerRegularizationData
        exactified ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount}
    (pullback :
      WZ2PaperCoarseSelectionPullbackData exactified regularization)
    (parent : Fin regularization.regularized.selected.family.card)
    (point : Point3) :
    (restrictPaperShading
        (pullback.restrictedCover.fullFiberSubfamily parent)
        pullback.selectedFineShading).pointMultiplicity point =
      (restrictPaperShading
        (exactified.restrictedCover.fullFiberSubfamily
          (regularization.support.packedIndex parent))
        exactified.refined).pointMultiplicity point := by
  let packedCoarse :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      coarse exactified.retainedParents
  simpa [pullback.selectedFineShading_eq] using
    wz2_paper_complete_fiber_restrict_pointMultiplicity_eq
      exactified.restrictedCover pullback.selectedFine
      pullback.restrictedCover parent
      (regularization.support.packedIndex parent)
      (pullback.full_fiber_complete_in_exactified parent)
      exactified.refined point

theorem WZ2PaperFinalParentOwnerPreparationData.refined_pointMultiplicity_le_fiberCap
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover sourceShading coarseCells availableFineCells
        balancing coarseData}
    {referenceFiberMass : Fin coarse.card → ENNReal}
    {threshold : ENNReal}
    {finalDeletion :
      WZ2PaperFinalParentDeletionData
        producer referenceFiberMass threshold}
    {ambient :
      WZ2PaperFinalParentDeletionAmbientExactData finalDeletion}
    (owner :
      WZ2PaperFinalParentOwnerPreparationData ambient) :
    ∀ point,
      (owner.exactified.refined.pointMultiplicity point : ENNReal) ≤
        (2 ^ (producer.finalFine.fineLevel + 1) : ENNReal) := by
  intro point
  have hOwnerSelected :
      owner.exactified.refined.pointMultiplicity point ≤
        (restrictPaperShading
          owner.exactified.selected ambient.exact.refined).pointMultiplicity
            point :=
    paperSubshading_pointMultiplicity_le
      owner.exactified.refined
      (restrictPaperShading
        owner.exactified.selected ambient.exact.refined)
      owner.exactified_subshading point
  have hSelectedAmbient :
      (restrictPaperShading
          owner.exactified.selected ambient.exact.refined).pointMultiplicity
            point ≤
        ambient.exact.refined.pointMultiplicity point :=
    restrictPaperShading_pointMultiplicity_le
      owner.exactified.selected ambient.exact.refined point
  have hAmbientDeletion :
      ambient.exact.refined.pointMultiplicity point =
        finalDeletion.deletion.refined.pointMultiplicity point := by
    rw [ambient.exact_refined_eq]
  have hDeletionExact :
      finalDeletion.deletion.refined.pointMultiplicity point ≤
        finalDeletion.exactAdapter.exact.refined.pointMultiplicity point :=
    paperSubshading_pointMultiplicity_le
      finalDeletion.deletion.refined
      finalDeletion.exactAdapter.exact.refined
      finalDeletion.deletion.refined_subshading point
  have hExactCap :
      (finalDeletion.exactAdapter.exact.refined.pointMultiplicity point :
          ENNReal) ≤
        (2 ^ (producer.finalFine.fineLevel + 1) : ENNReal) := by
    by_cases hpoint :
        point ∈ finalDeletion.exactAdapter.exact.refined.union
    · exact
        (finalDeletion.exactAdapter.fine_multiplicity_band
          point hpoint).2.le
    · have hzero :
          finalDeletion.exactAdapter.exact.refined.pointMultiplicity point =
            0 := by
        simp [Kakeya.Streamlined.Shading.pointMultiplicity,
          show ∀ index, point ∉
              finalDeletion.exactAdapter.exact.refined.carrier index by
            intro index hindex
            exact hpoint ⟨index, hindex⟩]
      rw [hzero]
      simp
  calc
    (owner.exactified.refined.pointMultiplicity point : ENNReal) ≤
        ((restrictPaperShading
          owner.exactified.selected ambient.exact.refined).pointMultiplicity
            point : ENNReal) := by
      exact_mod_cast hOwnerSelected
    _ ≤ (ambient.exact.refined.pointMultiplicity point : ENNReal) := by
      exact_mod_cast hSelectedAmbient
    _ =
        (finalDeletion.deletion.refined.pointMultiplicity point :
          ENNReal) := by
      exact_mod_cast hAmbientDeletion
    _ ≤
        (finalDeletion.exactAdapter.exact.refined.pointMultiplicity point :
          ENNReal) := by
      exact_mod_cast hDeletionExact
    _ ≤ (2 ^ (producer.finalFine.fineLevel + 1) : ENNReal) :=
      hExactCap

theorem WZ2PaperFinalParentOwnerPreparationData.refined_mass_le_fiberCap_union
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover sourceShading coarseCells availableFineCells
        balancing coarseData}
    {referenceFiberMass : Fin coarse.card → ENNReal}
    {threshold : ENNReal}
    {finalDeletion :
      WZ2PaperFinalParentDeletionData
        producer referenceFiberMass threshold}
    {ambient :
      WZ2PaperFinalParentDeletionAmbientExactData finalDeletion}
    (owner :
      WZ2PaperFinalParentOwnerPreparationData ambient) :
    owner.exactified.refined.mass ≤
      (2 ^ (producer.finalFine.fineLevel + 1) : ENNReal) *
        MeasureTheory.volume owner.exactified.refined.union :=
  mass_le_of_pointMultiplicity_le
    (fun point _ =>
      owner.refined_pointMultiplicity_le_fiberCap point)

theorem
    WZ2PaperFinalParentOwnerPreparationData.refined_mass_le_fiberCap_mul_coarse_mass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover sourceShading coarseCells availableFineCells
        balancing coarseData}
    {referenceFiberMass : Fin coarse.card → ENNReal}
    {threshold : ENNReal}
    {finalDeletion :
      WZ2PaperFinalParentDeletionData
        producer referenceFiberMass threshold}
    {ambient :
      WZ2PaperFinalParentDeletionAmbientExactData finalDeletion}
    (owner :
      WZ2PaperFinalParentOwnerPreparationData ambient) :
    owner.exactified.refined.mass ≤
      (2 ^ (producer.finalFine.fineLevel + 1) : ENNReal) *
        owner.exactified.coarseShading.mass := by
  apply
    owner.exactified.restrictedCover.toWZ1PaperTubeCover
      |>.fine_mass_le_fiberCap_mul_coarse_mass
        owner.exactified.refined
        owner.exactified.coarseShading
        owner.exactified.balanced.point_compatibility
  intro parent point
  have hFiberEq :=
    owner.exactified.restrictedCover
      |>.restrict_fullFiber_pointMultiplicity_eq
        owner.exactified.refined parent point
  rw [← hFiberEq]
  exact
    (show
      ((restrictPaperShading
        (owner.exactified.restrictedCover.fullFiberSubfamily parent)
        owner.exactified.refined).pointMultiplicity point : ENNReal) ≤
        (owner.exactified.refined.pointMultiplicity point : ENNReal) by
      exact_mod_cast
        restrictPaperShading_pointMultiplicity_le
          (owner.exactified.restrictedCover.fullFiberSubfamily parent)
          owner.exactified.refined point).trans
      (owner.refined_pointMultiplicity_le_fiberCap point)

end Kakeya.Assouad

end
