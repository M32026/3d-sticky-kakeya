import MyLeanRepo.Kakeya.Assouad.PropStickyPaperExactBalancingMassRetentionStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRelativeMultiplicityHelpers

/-! # Shaded-mass retention through exact whole-cell balancing -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_exact_balancing_mass_retention :
    WZ2PaperExactBalancingMassRetentionStatement := by
  intro delta rho hdelta fine shading multiplicityLevel hband
    multiplicityCap pruning balancing
  classical
  have hPrunedMultiplicity :
      ∀ point ∈ pruning.pruned.union,
        pruning.pruned.pointMultiplicity point =
          shading.pointMultiplicity point := by
    intro point hpoint
    rcases hpoint with ⟨witness, hwitness⟩
    have hSafe :
        point ∈
          ⋃ fineCell ∈ pruning.safeFineCells,
            wz1PaperGridCube delta fineCell := by
      rw [pruning.pruned_carrier_eq witness] at hwitness
      exact hwitness.2
    simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
    congr 1
    apply Finset.filter_congr
    intro index _
    rw [pruning.pruned_carrier_eq index]
    exact and_iff_left hSafe
  have hRefinedPrunedMultiplicity :
      ∀ point ∈ balancing.refined.union,
        balancing.refined.pointMultiplicity point =
          pruning.pruned.pointMultiplicity point := by
    intro point hpoint
    rcases hpoint with ⟨witness, hwitness⟩
    have hRetained :
        point ∈
          ⋃ fineCell ∈ balancing.retainedFineCells,
            wz1PaperGridCube delta fineCell := by
      rw [balancing.refined_carrier_eq witness] at hwitness
      exact hwitness.2
    simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
    congr 1
    apply Finset.filter_congr
    intro index _
    rw [balancing.refined_carrier_eq index]
    exact and_iff_left hRetained
  have hRefinedMultiplicity :
      ∀ point ∈ balancing.refined.union,
        balancing.refined.pointMultiplicity point =
          shading.pointMultiplicity point := by
    intro point hpoint
    have hpointPruned : point ∈ pruning.pruned.union := by
      rcases hpoint with ⟨index, hindex⟩
      refine ⟨index, ?_⟩
      rw [balancing.refined_carrier_eq index] at hindex
      exact hindex.1
    exact
      (hRefinedPrunedMultiplicity point hpoint).trans
        (hPrunedMultiplicity point hpointPruned)
  have hPrunedConstant :
      pruning.pruned.HasConstantMultiplicity
        (2 ^ multiplicityLevel)
        (2 * (2 ^ multiplicityLevel)) := by
    intro point hpoint
    have hpointShading : point ∈ shading.union := by
      rcases hpoint with ⟨index, hindex⟩
      refine ⟨index, pruning.pruned_subshading index hindex⟩
    have h := hband point hpointShading
    have hEq := hPrunedMultiplicity point hpoint
    constructor
    · exact_mod_cast hEq.symm ▸ h.1
    · have hUpper :
          pruning.pruned.pointMultiplicity point <
            2 ^ (multiplicityLevel + 1) := by
        exact_mod_cast hEq.symm ▸ h.2
      simpa [pow_succ, mul_comm] using hUpper.le
  have hRefinedConstant :
      balancing.refined.HasConstantMultiplicity
        (2 ^ multiplicityLevel)
        (2 * (2 ^ multiplicityLevel)) := by
    intro point hpoint
    have hpointShading : point ∈ shading.union := by
      rcases hpoint with ⟨index, hindex⟩
      rw [balancing.refined_carrier_eq index] at hindex
      exact ⟨index, pruning.pruned_subshading index hindex.1⟩
    have h := hband point hpointShading
    have hEq := hRefinedMultiplicity point hpoint
    constructor
    · exact_mod_cast hEq.symm ▸ h.1
    · have hUpper :
          balancing.refined.pointMultiplicity point <
            2 ^ (multiplicityLevel + 1) := by
        exact_mod_cast hEq.symm ▸ h.2
      simpa [pow_succ, mul_comm] using hUpper.le
  have hAvailableCount :
      (∑ coarseCell ∈ pruning.coarseCells,
          (pruning.availableFineCells coarseCell).card) =
        pruning.safeFineCells.card := by
    simp_rw [pruning.availableFineCells_eq]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    apply congrArg Finset.card
    ext fineCell
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      rw [pruning.coarseCells_eq]
      exact Finset.mem_image.mpr
        ⟨fineCell, h, rfl⟩
  have hPrunedVolume :
      MeasureTheory.volume pruning.pruned.union =
        (pruning.safeFineCells.card : ENNReal) *
          MeasureTheory.volume
            (wz1PaperGridCube delta (0, 0, 0)) := by
    rw [pruning.pruned_union_eq]
    exact
      wz1PaperGridCube_volume_biUnion
        hdelta pruning.safeFineCells
  have hRefinedVolume :
      MeasureTheory.volume balancing.refined.union =
        (balancing.retainedFineCells.card : ENNReal) *
          MeasureTheory.volume
            (wz1PaperGridCube delta (0, 0, 0)) := by
    rw [balancing.refined_union_eq]
    exact
      wz1PaperGridCube_volume_biUnion
        hdelta balancing.retainedFineCells
  let availableCellCount :=
    ∑ coarseCell ∈ pruning.coarseCells,
      (pruning.availableFineCells coarseCell).card
  let logarithmicLoss := Nat.log 2 availableCellCount + 1
  have hCount :
      availableCellCount ≤
        2 * logarithmicLoss *
          balancing.retainedFineCells.card := by
    dsimp only [availableCellCount, logarithmicLoss]
    exact balancing.retainedFineCells_count
  have hCountENN :
      (availableCellCount : ENNReal) ≤
        (2 : ENNReal) * (logarithmicLoss : ENNReal) *
          (balancing.retainedFineCells.card : ENNReal) := by
    exact_mod_cast hCount
  have hPrunedMass :=
    (constant_multiplicity_mass_volume_generic
      hPrunedConstant).2
  have hRefinedMass :=
    (constant_multiplicity_mass_volume_generic
      hRefinedConstant).1
  have hSafeCount :
      (pruning.safeFineCells.card : ENNReal) =
        (availableCellCount : ENNReal) := by
    exact_mod_cast hAvailableCount.symm
  refine ⟨hRefinedMultiplicity, ?_, ?_⟩
  · intro point hpoint
    have hpointShading : point ∈ shading.union := by
      rcases hpoint with ⟨index, hindex⟩
      rw [balancing.refined_carrier_eq index] at hindex
      exact ⟨index, pruning.pruned_subshading index hindex.1⟩
    simpa [hRefinedMultiplicity point hpoint] using
      hband point hpointShading
  · dsimp only
    calc
      pruning.pruned.mass ≤
          (2 : ENNReal) * (2 ^ multiplicityLevel : ENNReal) *
            MeasureTheory.volume pruning.pruned.union :=
        by simpa [Nat.cast_pow] using hPrunedMass
      _ =
          (2 : ENNReal) * (2 ^ multiplicityLevel : ENNReal) *
            ((availableCellCount : ENNReal) *
              MeasureTheory.volume
                (wz1PaperGridCube delta (0, 0, 0))) := by
        rw [hPrunedVolume, hSafeCount]
      _ ≤
          (2 : ENNReal) * (2 ^ multiplicityLevel : ENNReal) *
            (((2 : ENNReal) * (logarithmicLoss : ENNReal) *
                (balancing.retainedFineCells.card : ENNReal)) *
              MeasureTheory.volume
                (wz1PaperGridCube delta (0, 0, 0))) := by
        gcongr
      _ =
          ((4 : ENNReal) * (logarithmicLoss : ENNReal)) *
            ((2 ^ multiplicityLevel : ENNReal) *
              ((balancing.retainedFineCells.card : ENNReal) *
                MeasureTheory.volume
                  (wz1PaperGridCube delta (0, 0, 0)))) := by
        ring
      _ ≤
          ((4 : ENNReal) * (logarithmicLoss : ENNReal)) *
            balancing.refined.mass := by
        gcongr
        rw [← hRefinedVolume]
        simpa using hRefinedMass

end Kakeya.Assouad

end
