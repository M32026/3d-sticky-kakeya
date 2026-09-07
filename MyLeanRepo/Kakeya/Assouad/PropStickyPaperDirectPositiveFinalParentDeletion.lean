import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedVolumeIdentities
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDirectFinalParentDeletion
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume

/-!
# Positive final parent-deletion threshold on the direct route

The final balanced realization determines one positive deletion threshold.
It is the final fine union volume divided by a fixed numerical constant, the
canonical balanced parent-degree cap, and one plus the total geometric
reference fiber mass.  The extra one avoids any nonzero assumption on the
reference mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem WZ2PaperFinalBalancedCoverExactAdapterData.level_le
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
    (adapter :
      WZ2PaperFinalBalancedCoverExactAdapterData producer) :
    adapter.exact.level ≤ producer.finalFine.exact.level := by
  rcases adapter.exact.retainedCoarseCells_nonempty with ⟨cell, hcell⟩
  have hAdapter :=
    adapter.exact.selectedFineCells_card cell hcell
  have hProducer :=
    producer.finalFine.exact.selectedFineCells_card
      cell
        (producer.coarseBand.selectedCells_subset
          (adapter.exact.retainedCoarseCells_subset hcell))
  apply (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp
  rw [← hAdapter, ← hProducer]
  exact
    Finset.card_le_card
      (adapter.exact.selectedFineCells_subset cell hcell)

theorem WZ2PaperFinalBalancedCoverExactAdapterData.degreeCap_le
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
    (adapter :
      WZ2PaperFinalBalancedCoverExactAdapterData producer) :
    wz2PaperBalancedParentDegreeCap
        adapter.exact producer.finalFine.fineLevel ≤
      wz2PaperBalancedParentDegreeCap
        producer.finalFine.exact producer.finalFine.fineLevel := by
  simp only [wz2PaperBalancedParentDegreeCap]
  exact Nat.mul_le_mul_right _ <|
    Nat.pow_le_pow_right (n := 2) (by norm_num) adapter.level_le

theorem WZ2PaperCoarseShadingData.coarse_union_eq_retainedCoarseCells
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
    (data :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing) :
    data.coarseShading.union =
      ⋃ cell ∈ balancing.retainedCoarseCells,
        wz1PaperGridCube rho cell := by
  ext point
  constructor
  · rintro ⟨parent, hpoint⟩
    rw [data.coarseShading_carrier_eq] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨cell, hcell, hpointCell⟩
    exact
      Set.mem_iUnion₂.mpr
        ⟨cell, data.parentCells_subset parent hcell, hpointCell⟩
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨cell, hcell, hpointCell⟩
    rcases data.retained_cell_owned cell hcell with
      ⟨parent, hparent⟩
    refine ⟨parent, ?_⟩
    rw [data.coarseShading_carrier_eq]
    exact Set.mem_iUnion₂.mpr ⟨cell, hparent, hpointCell⟩

noncomputable def WZ2PaperCoarseShadingData.toExactBalancedCover
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
    (data :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing) :
    WZ1PaperBalancedCoverData
      cover.toWZ1PaperTubeCover
      balancing.refined data.coarseShading where
  point_compatibility :=
    data.balancedCover.point_compatibility
  coarse_cubical :=
    data.balancedCover.coarse_cubical
  activeCells :=
    balancing.retainedCoarseCells
  coarse_union_eq :=
    data.coarse_union_eq_retainedCoarseCells
  cellMass :=
    balancing.cellMass
  cellMass_pos :=
    balancing.cellMass_pos
  cellMass_ne_top :=
    balancing.cellMass_ne_top
  fine_cell_mass :=
    balancing.fine_cell_mass

theorem WZ2PaperFinalBalancedCoverExactAdapterData.fine_union_volume
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
    (adapter :
      WZ2PaperFinalBalancedCoverExactAdapterData producer) :
    volume adapter.exact.refined.union =
      (adapter.exact.retainedCoarseCells.card : ENNReal) *
        adapter.exact.cellMass :=
  adapter.coarseData.toExactBalancedCover.fine_union_volume

def wz2PaperDirectFinalParentDeletionThreshold
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (balanced :
      WZ2PaperDirectBalancedData cover shading hdelta hrho 14) :
    ENNReal :=
  let producer := balanced.finalData.producer
  let degreeCap : ENNReal :=
    wz2PaperBalancedParentDegreeCap
      producer.finalFine.exact producer.finalFine.fineLevel
  let referenceMass : ENNReal :=
    ∑ parent : Fin coarse.card,
      wz2PaperGeometricReferenceFiberMass cover parent
  (1 / 8 : ENNReal) *
    degreeCap⁻¹ *
    (1 + referenceMass)⁻¹ *
    volume producer.coarseBand.selectedFineShading.union

theorem wz2_paper_direct_final_parent_deletion_threshold_pos
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (balanced :
      WZ2PaperDirectBalancedData cover shading hdelta hrho 14) :
    0 < wz2PaperDirectFinalParentDeletionThreshold balanced := by
  let producer := balanced.finalData.producer
  let degreeCap : ENNReal :=
    wz2PaperBalancedParentDegreeCap
      producer.finalFine.exact producer.finalFine.fineLevel
  let referenceMass : ENNReal :=
    ∑ parent : Fin coarse.card,
      wz2PaperGeometricReferenceFiberMass cover parent
  have hDegreeTop : degreeCap ≠ ⊤ := by
    dsimp only [degreeCap]
    simp
  have hReferenceTop : referenceMass ≠ ⊤ := by
    dsimp only [referenceMass]
    apply ENNReal.sum_ne_top.2
    intro parent _
    exact
      ENNReal.mul_ne_top
        (by
          simp [
            Kakeya.Streamlined.TubeFamily.enncard,
            Kakeya.Streamlined.BodyFamily.enncard
          ])
        (by simp [Kakeya.realRpowENN])
  have hVolumePos :
      0 < volume producer.coarseBand.selectedFineShading.union := by
    rw [producer.finalCover.balanced.fine_union_volume]
    rw [producer.finalCover.activeCells_eq,
      producer.finalCover.cellMass_eq]
    exact ENNReal.mul_pos
      (by
        exact_mod_cast
          producer.coarseBand.selectedCells_nonempty.card_pos.ne')
      producer.finalFine.exact.cellMass_pos.ne'
  dsimp only [wz2PaperDirectFinalParentDeletionThreshold]
  exact ENNReal.mul_pos
    (ENNReal.mul_pos
      (ENNReal.mul_pos (by norm_num)
        (ENNReal.inv_ne_zero.mpr hDegreeTop)).ne'
      (ENNReal.inv_ne_zero.mpr
        (ENNReal.add_ne_top.mpr ⟨by norm_num, hReferenceTop⟩))).ne'
    hVolumePos.ne'

theorem wz2_paper_direct_final_parent_deletion_volume_budget
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (balanced :
      WZ2PaperDirectBalancedData cover shading hdelta hrho 14)
    (adapter :
      WZ2PaperFinalBalancedCoverExactAdapterData
        balanced.finalData.producer) :
    2 *
          (wz2PaperBalancedParentDegreeCap
            adapter.exact
            balanced.finalData.producer.finalFine.fineLevel :
            ENNReal) *
          wz2PaperDirectFinalParentDeletionThreshold balanced *
          (∑ parent : Fin coarse.card,
            wz2PaperGeometricReferenceFiberMass cover parent) ≤
      (1 / 4 : ENNReal) *
        volume
          (balanced.finalData.producer.coarseBand.selectedFineShading.union) := by
  let producer := balanced.finalData.producer
  let degreeCap : ENNReal :=
    wz2PaperBalancedParentDegreeCap
      producer.finalFine.exact producer.finalFine.fineLevel
  let adapterDegreeCap : ENNReal :=
    wz2PaperBalancedParentDegreeCap
      adapter.exact producer.finalFine.fineLevel
  let referenceMass : ENNReal :=
    ∑ parent : Fin coarse.card,
      wz2PaperGeometricReferenceFiberMass cover parent
  let finalVolume : ENNReal :=
    volume producer.coarseBand.selectedFineShading.union
  have hDegree :
      adapterDegreeCap ≤ degreeCap := by
    dsimp only [adapterDegreeCap, degreeCap]
    exact_mod_cast adapter.degreeCap_le
  have hDegreeZero : degreeCap ≠ 0 := by
    dsimp only [degreeCap, wz2PaperBalancedParentDegreeCap]
    positivity
  have hDegreeTop : degreeCap ≠ ⊤ := by
    dsimp only [degreeCap]
    exact ENNReal.natCast_ne_top _
  have hReferenceTop : referenceMass ≠ ⊤ := by
    dsimp only [referenceMass]
    apply ENNReal.sum_ne_top.2
    intro parent _
    exact
      ENNReal.mul_ne_top
        (by
          simp [
            Kakeya.Streamlined.TubeFamily.enncard,
            Kakeya.Streamlined.BodyFamily.enncard
          ])
        (by simp [Kakeya.realRpowENN])
  have hReferencePlusZero : 1 + referenceMass ≠ 0 := by
    positivity
  have hReferencePlusTop : 1 + referenceMass ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨by norm_num, hReferenceTop⟩
  have hReferenceRatio :
      (1 + referenceMass)⁻¹ * referenceMass ≤ 1 := by
    calc
      (1 + referenceMass)⁻¹ * referenceMass ≤
          (1 + referenceMass)⁻¹ * (1 + referenceMass) := by
        gcongr
        exact le_add_left le_rfl
      _ = 1 :=
        ENNReal.inv_mul_cancel
          hReferencePlusZero hReferencePlusTop
  have hCanonical :
      2 * degreeCap *
            ((1 / 8 : ENNReal) * degreeCap⁻¹ *
              (1 + referenceMass)⁻¹ * finalVolume) *
            referenceMass ≤
        (1 / 4 : ENNReal) * finalVolume := by
    have hQuarterConstant :
        (2 : ENNReal) * (1 / 8) = 1 / 4 := by
      have hLeftTop : (2 : ENNReal) * (1 / 8) ≠ ⊤ :=
        ENNReal.mul_ne_top (by norm_num) (by simp)
      have hRightTop : (1 / 4 : ENNReal) ≠ ⊤ := by simp
      apply
        (ENNReal.toReal_eq_toReal_iff'
          hLeftTop hRightTop).mp
      simp [ENNReal.toReal_mul, ENNReal.toReal_inv]
      norm_num
    calc
      2 * degreeCap *
            ((1 / 8 : ENNReal) * degreeCap⁻¹ *
              (1 + referenceMass)⁻¹ * finalVolume) *
            referenceMass =
          (2 * (1 / 8 : ENNReal)) *
            (degreeCap * degreeCap⁻¹) *
            ((1 + referenceMass)⁻¹ * referenceMass) *
            finalVolume := by ring
      _ =
          (1 / 4 : ENNReal) *
            (degreeCap * degreeCap⁻¹) *
            ((1 + referenceMass)⁻¹ * referenceMass) *
            finalVolume := by rw [hQuarterConstant]
      _ =
          (1 / 4 : ENNReal) *
            ((1 + referenceMass)⁻¹ * referenceMass) *
            finalVolume := by
        rw [ENNReal.mul_inv_cancel hDegreeZero hDegreeTop]
        simp
      _ ≤ (1 / 4 : ENNReal) * 1 * finalVolume := by
        gcongr
      _ = (1 / 4 : ENNReal) * finalVolume := by simp
  calc
    2 * adapterDegreeCap *
          wz2PaperDirectFinalParentDeletionThreshold balanced *
          referenceMass ≤
        2 * degreeCap *
          wz2PaperDirectFinalParentDeletionThreshold balanced *
          referenceMass := by
      gcongr
    _ ≤ (1 / 4 : ENNReal) * finalVolume := by
      simpa only [
        wz2PaperDirectFinalParentDeletionThreshold,
        producer, degreeCap, referenceMass, finalVolume
      ] using hCanonical

theorem wz2_paper_direct_final_parent_deletion_nonempty_budget
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (balanced :
      WZ2PaperDirectBalancedData cover shading hdelta hrho 14) :
    ∀ adapter :
        WZ2PaperFinalBalancedCoverExactAdapterData
          balanced.finalData.producer,
      2 *
            (wz2PaperBalancedParentDegreeCap
              adapter.exact
              balanced.finalData.producer.finalFine.fineLevel :
              ENNReal) *
            wz2PaperDirectFinalParentDeletionThreshold balanced *
            (∑ parent : Fin coarse.card,
              wz2PaperGeometricReferenceFiberMass cover parent) <
        adapter.exact.cellMass *
          adapter.exact.retainedCoarseCells.card := by
  intro adapter
  let finalVolume : ENNReal :=
    volume balanced.finalData.producer.coarseBand.selectedFineShading.union
  have hVolumeEq :
      finalVolume =
        (adapter.exact.retainedCoarseCells.card : ENNReal) *
          adapter.exact.cellMass := by
    simpa only [finalVolume, adapter.exact_refined_eq] using
      adapter.fine_union_volume
  have hVolumeZero : finalVolume ≠ 0 := by
    rw [hVolumeEq]
    exact
      (ENNReal.mul_pos
        (by
          exact_mod_cast
            adapter.exact.retainedCoarseCells_nonempty.card_pos.ne')
        adapter.exact.cellMass_pos.ne').ne'
  have hVolumeTop : finalVolume ≠ ⊤ := by
    rw [hVolumeEq]
    exact ENNReal.mul_ne_top (by simp) adapter.exact.cellMass_ne_top
  have hQuarter :
      (1 / 4 : ENNReal) * finalVolume < finalVolume := by
    calc
      (1 / 4 : ENNReal) * finalVolume <
          1 * finalVolume :=
        ENNReal.mul_lt_mul_left hVolumeZero hVolumeTop
          (by norm_num)
      _ = finalVolume := by simp
  calc
    2 *
          (wz2PaperBalancedParentDegreeCap
            adapter.exact
            balanced.finalData.producer.finalFine.fineLevel :
            ENNReal) *
          wz2PaperDirectFinalParentDeletionThreshold balanced *
          (∑ parent : Fin coarse.card,
            wz2PaperGeometricReferenceFiberMass cover parent) ≤
        (1 / 4 : ENNReal) * finalVolume :=
      wz2_paper_direct_final_parent_deletion_volume_budget
        balanced adapter
    _ < finalVolume := hQuarter
    _ =
        adapter.exact.cellMass *
          adapter.exact.retainedCoarseCells.card := by
      rw [hVolumeEq]
      ring

theorem wz2_paper_direct_final_parent_deletion_mass_budget
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (balanced :
      WZ2PaperDirectBalancedData cover shading hdelta hrho 14) :
    ∀ deletion :
        WZ2PaperFinalParentDeletionData
          balanced.finalData.producer
          (wz2PaperGeometricReferenceFiberMass cover)
          (wz2PaperDirectFinalParentDeletionThreshold balanced),
      let fineCap : ENNReal :=
        (2 ^
          (balanced.finalData.producer.finalFine.fineLevel + 1) :
          ENNReal)
      let degreeCap : ENNReal :=
        wz2PaperBalancedParentDegreeCap
          deletion.exactAdapter.exact
          balanced.finalData.producer.finalFine.fineLevel
      fineCap *
            (2 * degreeCap *
              wz2PaperDirectFinalParentDeletionThreshold balanced *
              ∑ parent : Fin coarse.card,
                wz2PaperGeometricReferenceFiberMass cover parent) ≤
          (1 / 2 : ENNReal) *
            deletion.exactAdapter.exact.refined.mass := by
  intro deletion
  let producer := balanced.finalData.producer
  let adapter := deletion.exactAdapter
  let level := producer.finalFine.fineLevel
  let fineFloor : ENNReal := (2 ^ level : ENNReal)
  let fineCap : ENNReal := (2 ^ (level + 1) : ENNReal)
  let deletedVolume : ENNReal :=
    2 *
        (wz2PaperBalancedParentDegreeCap
          adapter.exact level : ENNReal) *
        wz2PaperDirectFinalParentDeletionThreshold balanced *
        ∑ parent : Fin coarse.card,
          wz2PaperGeometricReferenceFiberMass cover parent
  let finalVolume : ENNReal :=
    volume adapter.exact.refined.union
  have hVolumeBudget :
      deletedVolume ≤ (1 / 4 : ENNReal) * finalVolume := by
    simpa only [
      deletedVolume, finalVolume, adapter.exact_refined_eq
    ] using
      wz2_paper_direct_final_parent_deletion_volume_budget
        balanced adapter
  have hMassFloor :
      fineFloor * finalVolume ≤ adapter.exact.refined.mass := by
    apply multiplicity_floor_le_mass
    intro point hpoint
    exact (adapter.fine_multiplicity_band point hpoint).1
  have hFineCap :
      fineCap = 2 * fineFloor := by
    dsimp only [fineCap, fineFloor, level]
    rw [pow_succ]
    ring
  have hHalfConstant :
      (2 : ENNReal) * (1 / 4) = 1 / 2 := by
    have hLeftTop : (2 : ENNReal) * (1 / 4) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) (by simp)
    have hRightTop : (1 / 2 : ENNReal) ≠ ⊤ := by simp
    apply
      (ENNReal.toReal_eq_toReal_iff'
        hLeftTop hRightTop).mp
    simp [ENNReal.toReal_mul, ENNReal.toReal_inv]
    norm_num
  dsimp only
  calc
    fineCap * deletedVolume ≤
        fineCap * ((1 / 4 : ENNReal) * finalVolume) := by
      gcongr
    _ =
        (1 / 2 : ENNReal) * (fineFloor * finalVolume) := by
      rw [hFineCap]
      calc
        (2 * fineFloor) * ((1 / 4 : ENNReal) * finalVolume) =
            (2 * (1 / 4 : ENNReal)) *
              (fineFloor * finalVolume) := by ring
        _ =
            (1 / 2 : ENNReal) *
              (fineFloor * finalVolume) := by
          rw [hHalfConstant]
    _ ≤ (1 / 2 : ENNReal) * adapter.exact.refined.mass := by
      gcongr

theorem wz2_paper_direct_positive_final_parent_deletion
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (balanced :
      WZ2PaperDirectBalancedData cover shading hdelta hrho 14)
    (deletionExponent : ℕ)
    (hFraction :
      wz1PaperRefinementFraction delta deletionExponent ≤
        (1 / 2 : ENNReal)) :
    Nonempty
      (WZ2PaperDirectFinalParentDeletionData
        balanced
        (wz2PaperDirectFinalParentDeletionThreshold balanced)
        deletionExponent) :=
  wz2_paper_direct_final_parent_deletion
    balanced
    (wz2PaperDirectFinalParentDeletionThreshold balanced)
    (wz2_paper_direct_final_parent_deletion_nonempty_budget balanced)
    (wz2_paper_direct_final_parent_deletion_mass_budget balanced)
    deletionExponent hFraction

end Kakeya.Assouad

end
