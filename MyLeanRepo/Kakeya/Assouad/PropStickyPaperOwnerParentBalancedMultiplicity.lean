import MyLeanRepo.Kakeya.Assouad.PropStickyPaperOwnerCellMultiplicity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperOwnerParentBalancedPullback

/-!
# Multiplicity of an owner-parent balanced pullback

Every retained coarse cell has one dominant owner.  Restricting to any
subfamily of owner parents therefore leaves a coarse shading with point
multiplicity at most one.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem WZ2PaperOwnerParentBalancedPullbackData.coarse_pointMultiplicity_le_one
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) fineShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover fineShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover fineShading coarseCells availableFineCells
        balancing coarseData}
    {owner : WZ2PaperDirectOwnerPreparationData producer}
    {selectedPacked :
      Kakeya.Streamlined.TubeSubfamily
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          coarse owner.exactified.retainedParents).family}
    (data :
      WZ2PaperOwnerParentBalancedPullbackData
        owner selectedPacked) :
    ∀ point,
      (data.pullback.selectedCoarseShading.pointMultiplicity point :
        ENNReal) ≤ 1 := by
  let packed :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      coarse owner.exactified.retainedParents
  let parentEmbedding :
      Fin selectedPacked.family.card ↪ Fin coarse.card :=
    selectedPacked.embedding.trans packed.embedding
  apply
    wz2_paper_owner_cell_pointMultiplicity_le_one
      data.pullback.selectedCoarseShading data.selectedCells
      parentEmbedding owner.dominant.dominantParent
  intro parent point
  change
    point ∈ data.pullback.selectedCoarseShading.carrier parent ↔
      ∃ cell ∈ data.selectedCells,
        packed.embedding (selectedPacked.embedding parent) =
            owner.dominant.dominantParent cell ∧
          point ∈ wz1PaperGridCube rho cell
  rw [data.selected_coarse_carrier_eq parent]
  constructor
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨cell, hcell, hif⟩
    by_cases howner :
        packed.embedding (selectedPacked.embedding parent) =
          owner.dominant.dominantParent cell
    · exact
        ⟨cell, hcell, howner, by
          rwa [if_pos howner] at hif⟩
    · rw [if_neg howner] at hif
      exact False.elim hif
  · rintro ⟨cell, hcell, howner, hpoint⟩
    exact
      Set.mem_iUnion₂.mpr
        ⟨cell, hcell, by
          rw [if_pos howner]
          exact hpoint⟩

end Kakeya.Assouad

end
