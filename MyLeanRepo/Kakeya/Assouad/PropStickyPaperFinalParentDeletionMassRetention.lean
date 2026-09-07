import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentDeletionMassRetentionStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedVolumeIdentities
import MyLeanRepo.Kakeya.Assouad.WZ1.ShadingPruningMass

/-! # Retain shaded mass through final whole-cell parent deletion -/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem wz2_paper_final_parent_deletion_mass_retention :
    WZ2PaperFinalParentDeletionMassRetentionStatement := by
  intro delta rho fine coarse cover sourceShading coarseCells
    availableFineCells balancing coarseData hdelta hrho producer
    threshold referenceFiberMass finalDeletion
  dsimp only
  intro hBudget deletionExponent hFraction
  let source := finalDeletion.exactAdapter.exact.refined
  let retained := finalDeletion.restriction.selectedFineShading
  let retainedAmbient := finalDeletion.deletion.refined
  let fineCap : ENNReal :=
    (2 ^ (producer.finalFine.fineLevel + 1) : ENNReal)
  let degreeCap : ENNReal :=
    wz2PaperBalancedParentDegreeCap
      finalDeletion.exactAdapter.exact
      producer.finalFine.fineLevel
  have hMultiplicity :
      ∀ point,
        (source.pointMultiplicity point : ENNReal) ≤ fineCap := by
    intro point
    by_cases hpoint : point ∈ source.union
    · exact
        (finalDeletion.exactAdapter.fine_multiplicity_band
          point hpoint).2.le
    · have hzero : source.pointMultiplicity point = 0 := by
        simp [Kakeya.Streamlined.Shading.pointMultiplicity,
          show ∀ index, point ∉ source.carrier index by
            intro index hindex
            exact hpoint ⟨index, hindex⟩]
      rw [hzero]
      simp
  have hDeletedVolume :
      volume (source.union \ retainedAmbient.union) ≤
        ((finalDeletion.exactAdapter.exact.retainedCoarseCells.card :
            ENNReal) -
          (finalDeletion.deletion.goodCells.card : ENNReal)) *
          finalDeletion.exactAdapter.exact.cellMass := by
    let deletedCells :=
      finalDeletion.exactAdapter.exact.retainedCoarseCells \
        finalDeletion.deletion.goodCells
    have hSubset :
        source.union \ retainedAmbient.union ⊆
          ⋃ cell ∈ deletedCells,
            source.union ∩ wz1PaperGridCube rho cell := by
      intro point hpoint
      have hpointSource := hpoint.1
      rw [finalDeletion.exactAdapter.exact.refined_union_eq]
        at hpointSource
      rcases Set.mem_iUnion₂.mp hpointSource with
        ⟨fineCell, hfineRetained, hpointFine⟩
      rw [finalDeletion.exactAdapter.exact.retainedFineCells_eq]
        at hfineRetained
      rcases Finset.mem_biUnion.mp hfineRetained with
        ⟨cell, hcell, hfineCell⟩
      have hpointCell :
          point ∈ wz1PaperGridCube rho cell :=
        finalDeletion.exactAdapter.exact.fine_cell_containment
          cell hcell fineCell hfineCell hpointFine
      have hcellDeleted : cell ∈ deletedCells := by
        apply Finset.mem_sdiff.mpr
        refine ⟨hcell, ?_⟩
        intro hgood
        have hretainedPoint :
            point ∈ retainedAmbient.union := by
          rw [finalDeletion.deletion.refined_union_eq]
          exact Set.mem_iUnion₂.mpr
            ⟨fineCell,
              by
                rw [finalDeletion.deletion.retainedFineCells_eq]
                exact Finset.mem_biUnion.mpr
                  ⟨cell, hgood, hfineCell⟩,
              hpointFine⟩
        exact hpoint.2 hretainedPoint
      exact Set.mem_iUnion₂.mpr
        ⟨cell, hcellDeleted, hpoint.1, hpointCell⟩
    calc
      volume (source.union \ retainedAmbient.union) ≤
          volume
            (⋃ cell ∈ deletedCells,
              source.union ∩ wz1PaperGridCube rho cell) :=
        measure_mono hSubset
      _ =
          ∑ cell ∈ deletedCells,
            volume
              (source.union ∩ wz1PaperGridCube rho cell) := by
        rw [MeasureTheory.measure_biUnion_finset]
        · intro first _ second _ hne
          exact
            (wz1PaperGridCube_disjoint hne).mono
              Set.inter_subset_right Set.inter_subset_right
        · intro cell _
          exact
            (measurableSet_shading_union source).inter
              (wz1PaperGridCube_measurable cell)
      _ =
          ∑ _cell ∈ deletedCells,
            finalDeletion.exactAdapter.exact.cellMass := by
        apply Finset.sum_congr rfl
        intro cell hcell
        exact
          finalDeletion.exactAdapter.exact.fine_cell_mass
            cell (Finset.mem_sdiff.mp hcell).1
      _ =
          (deletedCells.card : ENNReal) *
            finalDeletion.exactAdapter.exact.cellMass := by
        simp [Finset.sum_const]
      _ =
          ((finalDeletion.exactAdapter.exact.retainedCoarseCells.card :
              ENNReal) -
            (finalDeletion.deletion.goodCells.card : ENNReal)) *
            finalDeletion.exactAdapter.exact.cellMass := by
        have hcard :
            deletedCells.card =
              finalDeletion.exactAdapter.exact.retainedCoarseCells.card -
                finalDeletion.deletion.goodCells.card :=
          Finset.card_sdiff_of_subset
            finalDeletion.deletion.goodCells_subset
        have hcast :
            ((finalDeletion.exactAdapter.exact.retainedCoarseCells.card -
                finalDeletion.deletion.goodCells.card : ℕ) : ENNReal) =
              (finalDeletion.exactAdapter.exact.retainedCoarseCells.card :
                ENNReal) -
                (finalDeletion.deletion.goodCells.card : ENNReal) :=
          ENNReal.natCast_sub _ _
        rw [hcard]
        exact congrArg
          (fun value : ENNReal =>
            value * finalDeletion.exactAdapter.exact.cellMass)
          hcast
  have hMassSplit :
      source.mass ≤
        retainedAmbient.mass +
          fineCap *
            volume (source.union \ retainedAmbient.union) := by
    have hDeletedMassUpper :=
      setLIntegral_mono' (μ := volume)
        ((measurableSet_shading_union source).diff
          (measurableSet_shading_union retainedAmbient))
        (fun point _ => hMultiplicity point)
    rw [setLIntegral_const] at hDeletedMassUpper
    have hCarrierSplit :
        ∀ index,
          volume (source.carrier index) ≤
            volume (retainedAmbient.carrier index) +
              volume
                (source.carrier index ∩
                  (source.union \ retainedAmbient.union)) := by
      intro index
      have hUnion :
          source.carrier index ⊆
            retainedAmbient.carrier index ∪
              (source.carrier index ∩
                (source.union \ retainedAmbient.union)) := by
        intro point hpoint
        by_cases hretained :
            point ∈ retainedAmbient.carrier index
        · exact Or.inl hretained
        · refine Or.inr ⟨hpoint, ⟨⟨index, hpoint⟩, ?_⟩⟩
          intro hretainedUnion
          rcases hretainedUnion with ⟨witness, hwitness⟩
          have hmask :
              point ∈ wz2RetainedCellsUnion
                delta finalDeletion.deletion.retainedFineCells := by
            change point ∈
              finalDeletion.deletion.refined.carrier witness at hwitness
            rw [finalDeletion.deletion.refined_eq] at hwitness
            exact hwitness.2
          apply hretained
          change point ∈
            finalDeletion.deletion.refined.carrier index
          rw [finalDeletion.deletion.refined_eq]
          exact ⟨hpoint, hmask⟩
      calc
        volume (source.carrier index) ≤
            volume
              (retainedAmbient.carrier index ∪
                (source.carrier index ∩
                  (source.union \ retainedAmbient.union))) :=
          measure_mono hUnion
        _ ≤
            volume (retainedAmbient.carrier index) +
              volume
                (source.carrier index ∩
                  (source.union \ retainedAmbient.union)) :=
          MeasureTheory.measure_union_le _ _
    calc
      source.mass ≤
          retainedAmbient.mass +
            ∑ index : Fin (wz1PaperBodyFamily fine).card,
              volume
                (source.carrier index ∩
                  (source.union \ retainedAmbient.union)) := by
        change
          (∑ index : Fin (wz1PaperBodyFamily fine).card,
              volume (source.carrier index)) ≤
            (∑ index : Fin (wz1PaperBodyFamily fine).card,
              volume (retainedAmbient.carrier index)) +
            ∑ index : Fin (wz1PaperBodyFamily fine).card,
              volume
                (source.carrier index ∩
                  (source.union \ retainedAmbient.union))
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum
          (fun index (_ : index ∈
            (Finset.univ :
              Finset (Fin (wz1PaperBodyFamily fine).card))) =>
              hCarrierSplit index)
      _ =
          retainedAmbient.mass +
            ∫⁻ point in source.union \ retainedAmbient.union,
              (source.pointMultiplicity point : ENNReal) := by
        have hFubini :=
          sum_volume_inter_eq_setLIntegral_pointMultiplicity
            source
            ((measurableSet_shading_union source).diff
              (measurableSet_shading_union retainedAmbient))
        exact congrArg (fun value => retainedAmbient.mass + value)
          hFubini
      _ ≤
          retainedAmbient.mass +
            fineCap *
              volume (source.union \ retainedAmbient.union) := by
        gcongr
  have hError :
      fineCap *
          volume (source.union \ retainedAmbient.union) ≤
        (1 / 2 : ENNReal) * source.mass := by
    calc
      fineCap *
            volume (source.union \ retainedAmbient.union) ≤
          fineCap *
            (((finalDeletion.exactAdapter.exact.retainedCoarseCells.card :
                ENNReal) -
              (finalDeletion.deletion.goodCells.card : ENNReal)) *
              finalDeletion.exactAdapter.exact.cellMass) := by
        gcongr
      _ ≤
          fineCap *
            (2 * degreeCap * threshold *
              ∑ parent : Fin coarse.card,
                referenceFiberMass parent) := by
        apply mul_le_mul_left'
        simpa [degreeCap] using
          finalDeletion.deletion.deleted_cell_mass
      _ =
          fineCap *
            (2 * degreeCap * threshold *
              ∑ parent : Fin coarse.card,
                referenceFiberMass parent) := rfl
      _ ≤ (1 / 2 : ENNReal) * source.mass := by
        simpa [source] using hBudget
  have hSourceFinite : source.mass ≠ ⊤ := by
    change
      (∑ index : Fin (wz1PaperBodyFamily fine).card,
        volume (source.carrier index)) ≠ ⊤
    apply ENNReal.sum_ne_top.2
    intro index _
    have hle :
        volume (source.carrier index) ≤
          volume (Kakeya.Streamlined.axisBox 2 2 2) :=
      measure_mono <|
        (source.subset_body index).trans Set.inter_subset_right
    have hbox :
        volume (Kakeya.Streamlined.axisBox 2 2 2) ≠ ⊤ := by
      rw [Kakeya.Streamlined.volume_axisBox
        2 2 2 (by norm_num) (by norm_num) (by norm_num)]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hbox hle
  have hHalf :
      (1 / 2 : ENNReal) * source.mass ≤ retainedAmbient.mass :=
    retained_mass_of_error_le_fraction
      hSourceFinite (by norm_num)
      (by simpa using ENNReal.add_halves (1 : ENNReal))
      hMassSplit hError
  have hRetainedMassEq :
      retained.mass = retainedAmbient.mass :=
    finalDeletion.restriction.selectedFine_mass_eq
  have hSourceMass :
      source.mass ≤ 2 * retained.mass := by
    have hcancel :
        (2 : ENNReal) * (1 / 2 : ENNReal) = 1 :=
      by
        simpa [one_div] using
          ENNReal.mul_inv_cancel
            (show (2 : ENNReal) ≠ 0 by norm_num)
            (show (2 : ENNReal) ≠ ⊤ by norm_num)
    calc
      source.mass = 1 * source.mass := by simp
      _ =
          (2 * (1 / 2 : ENNReal)) * source.mass := by
        rw [hcancel]
      _ =
          2 * ((1 / 2 : ENNReal) * source.mass) := by
        rw [mul_assoc]
      _ ≤ 2 * retainedAmbient.mass := by
        gcongr
      _ = 2 * retained.mass := by rw [hRetainedMassEq]
  let refinement :
      WZ1PaperRefinement source deletionExponent :=
    { selected := finalDeletion.restriction.selected
      refined := retained
      subshading := by
        intro index
        exact finalDeletion.restriction.selectedFine_subshading index
      retained_mass := by
        calc
          wz1PaperRefinementFraction delta deletionExponent *
                source.mass ≤
              (1 / 2 : ENNReal) * source.mass := by
            gcongr
          _ ≤ retainedAmbient.mass := hHalf
          _ = retained.mass := hRetainedMassEq.symm }
  exact
    ⟨{
      source_mass_le := hSourceMass
      refinement := refinement
      refinement_selected_eq := rfl
      refinement_refined_heq := HEq.rfl
      refinement_refined_mass_eq := rfl
      retained_mass_to_selected := by
        simpa [source, retained] using refinement.retained_mass
    }⟩

end Kakeya.Assouad

end
