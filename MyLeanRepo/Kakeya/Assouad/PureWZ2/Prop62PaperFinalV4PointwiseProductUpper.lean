import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperAudit.StatementsV4
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGlobalMultiplicityHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralGlobalOutputV2

/-!
# Proposition 6.2 V4 record-level multiplicity upper bounds

The paper-facing four-degree record already contains the exact fine
packet-cell multiplicity and the coarse active-cell multiplicity band.
Cubicality turns these cellwise statements into pointwise bounds, and the
finite parent-fiber decomposition gives the product bound.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PaperFourDegreePacketCoreData

variable
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {eta : ℝ}
    {packetDensityExponent : ℕ}
    {hdelta : 0 < delta}
    {metric :
      PaperMetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
          parentConstant fiberConstant}
    {outputParentConstant outputFiberConstant : ENNReal}
    (output :
      PaperFourDegreePacketCoreData
        (eta := eta)
        (packetDensityExponent := packetDensityExponent)
        hdelta metric outputParentConstant outputFiberConstant)

include output

/-- The coarse active-cell band gives a uniform pointwise coarse cap. -/
theorem coarse_pointMultiplicity_le
    (point : Point3) :
    (output.coarseShading.pointMultiplicity point : ENNReal) ≤
      (output.regularity * output.muCoarse : ℕ) := by
  by_cases pointMem : point ∈ output.coarseShading.union
  · rcases Set.mem_iUnion₂.mp
        (show point ∈
            ⋃ cell ∈ output.balanced.activeCells,
              wz1PaperGridCube rho.1 cell by
          simpa only [← output.balanced.coarse_union_eq] using pointMem) with
      ⟨cell, cellMem, pointCell⟩
    have activeCell : cell ∈ output.activeCoarseCells := by
      simpa only [output.active_coarse_cells_eq] using cellMem
    have countEq :
        output.coarseShading.pointMultiplicity point =
          (Finset.univ.filter fun parent =>
            wz1PaperGridCube rho.1 cell ⊆
              output.coarseShading.carrier parent).card := by
      change
        (Finset.univ.filter fun parent =>
          point ∈ output.coarseShading.carrier parent).card =
        (Finset.univ.filter fun parent =>
          wz1PaperGridCube rho.1 cell ⊆
            output.coarseShading.carrier parent).card
      congr 1
      ext parent
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro parentPoint
        have pointIndex :
            wz1PaperGridIndex rho.1 point = cell :=
          (mem_wz1PaperGridCube rho.1 cell point).mp pointCell
        simpa only [pointIndex] using
          output.balanced.coarse_cubical parent point parentPoint
      · intro wholeCell
        exact wholeCell pointCell
    rw [countEq]
    exact_mod_cast (output.coarse_multiplicity cell activeCell).2
  · have pointMultiplicityZero :
        output.coarseShading.pointMultiplicity point = 0 := by
      simp [
        Kakeya.Streamlined.Shading.pointMultiplicity,
        show ∀ parent, point ∉ output.coarseShading.carrier parent by
          intro parent pointCarrier
          exact pointMem ⟨parent, pointCarrier⟩
      ]
    rw [pointMultiplicityZero]
    simp

/-- The lower half of the coarse active-cell multiplicity band. -/
theorem coarse_pointMultiplicity_lower
    {point : Point3}
    (pointMem : point ∈ output.coarseShading.union) :
    (output.muCoarse : ENNReal) ≤
      output.coarseShading.pointMultiplicity point := by
  rcases Set.mem_iUnion₂.mp
      (show point ∈
          ⋃ cell ∈ output.balanced.activeCells,
            wz1PaperGridCube rho.1 cell by
        simpa only [← output.balanced.coarse_union_eq] using pointMem) with
    ⟨cell, cellMem, pointCell⟩
  have activeCell : cell ∈ output.activeCoarseCells := by
    simpa only [output.active_coarse_cells_eq] using cellMem
  have countEq :
      output.coarseShading.pointMultiplicity point =
        (Finset.univ.filter fun parent =>
          wz1PaperGridCube rho.1 cell ⊆
            output.coarseShading.carrier parent).card := by
    change
      (Finset.univ.filter fun parent =>
        point ∈ output.coarseShading.carrier parent).card =
      (Finset.univ.filter fun parent =>
        wz1PaperGridCube rho.1 cell ⊆
          output.coarseShading.carrier parent).card
    congr 1
    ext parent
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro parentPoint
      have pointIndex :
          wz1PaperGridIndex rho.1 point = cell :=
        (mem_wz1PaperGridCube rho.1 cell point).mp pointCell
      simpa only [pointIndex] using
        output.balanced.coarse_cubical parent point parentPoint
    · intro wholeCell
      exact wholeCell pointCell
  rw [countEq]
  exact_mod_cast (output.coarse_multiplicity cell activeCell).1

/-- A positive fiber multiplicity is exactly the packet multiplicity `muFine`. -/
theorem fiber_pointMultiplicity_eq_muFine_of_pos
    (parent : Fin output.coarse.family.card)
    (point : Point3)
    (positive :
      0 <
        output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
          output.refinement.refined parent point) :
    output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
        output.refinement.refined parent point =
      output.muFine := by
  let cell := wz1PaperGridIndex delta point
  let fiberSources :=
    (output.cover.toWZ1PaperTubeCover.fiberIndices parent).filter
      fun sourceIndex =>
        point ∈ output.refinement.refined.carrier sourceIndex
  have fiberNonempty : fiberSources.Nonempty := by
    change 0 < fiberSources.card at positive
    exact Finset.card_pos.mp positive
  rcases fiberNonempty with ⟨sourceIndex, sourceMem⟩
  have sourceData := Finset.mem_filter.mp sourceMem
  have sourceFiber :
      sourceIndex ∈
        wz2PaperFullFiberIndices
          output.refinement.selected.family output.coarse.family parent := by
    rw [output.cover.fullFiberIndices_eq parent]
    exact sourceData.1
  have wholeCell :
      wz1PaperGridCube delta cell ⊆
        output.refinement.refined.carrier sourceIndex := by
    exact
      output.refined_cubical sourceIndex point sourceData.2
  have cellActive :
      cell ∈ wz1PaperActiveCells output.refinement.refined hdelta := by
    rw [mem_wz1PaperActiveCells]
    refine ⟨?_, ⟨point, ⟨sourceIndex, sourceData.2⟩, ?_⟩⟩
    · exact
        paper_point_gridIndex_in_window hdelta
          (output.refinement.refined.subset_body sourceIndex sourceData.2).2
    · exact (mem_wz1PaperGridCube delta cell point).mpr rfl
  have packetMem : (parent, cell) ∈ output.packetCells := by
    rw [output.packetCells_eq]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ parent, cellActive⟩, ?_⟩
    exact
      ⟨sourceIndex,
        Finset.mem_filter.mpr ⟨sourceFiber, wholeCell⟩⟩
  have activeFiberEq :
      fiberSources =
        (wz2PaperFullFiberIndices
            output.refinement.selected.family output.coarse.family parent).filter
          fun candidate =>
            wz1PaperGridCube delta cell ⊆
              output.refinement.refined.carrier candidate := by
    dsimp only [fiberSources]
    rw [← output.cover.fullFiberIndices_eq parent]
    apply Finset.filter_congr
    intro candidate _candidateFiber
    constructor
    · intro candidatePoint
      exact output.refined_cubical candidate point candidatePoint
    · intro candidateCell
      exact candidateCell
        ((mem_wz1PaperGridCube delta cell point).mpr rfl)
  change fiberSources.card = output.muFine
  rw [activeFiberEq]
  exact output.exact_fine_multiplicity (parent, cell) packetMem

/-- The exact packet multiplicity gives a uniform pointwise fiber cap. -/
theorem fiber_pointMultiplicity_le
    (parent : Fin output.coarse.family.card)
    (point : Point3) :
    (output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
        output.refinement.refined parent point : ENNReal) ≤
      output.muFine := by
  by_cases positive :
      0 <
        output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
          output.refinement.refined parent point
  · rw [output.fiber_pointMultiplicity_eq_muFine_of_pos
      parent point positive]
  · have zero :
        output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
            output.refinement.refined parent point =
          0 :=
      Nat.eq_zero_of_not_pos positive
    rw [zero]
    simp

/-- On the union of one complete fiber, its restricted shading has exact
point multiplicity `muFine`. -/
theorem fullFiberShading_pointMultiplicity_eq_muFine
    (parent : Fin output.coarse.family.card)
    {point : Point3}
    (pointMem :
      point ∈
        (restrictPaperShading
          (output.cover.fullFiberSubfamily parent)
          output.refinement.refined).union) :
    (restrictPaperShading
      (output.cover.fullFiberSubfamily parent)
      output.refinement.refined).pointMultiplicity point =
        output.muFine := by
  have positiveLocal :
      0 <
        (restrictPaperShading
          (output.cover.fullFiberSubfamily parent)
          output.refinement.refined).pointMultiplicity point := by
    rcases pointMem with ⟨index, indexMem⟩
    rw [Kakeya.Streamlined.Shading.pointMultiplicity]
    exact Finset.card_pos.mpr
      ⟨index, Finset.mem_filter.mpr ⟨Finset.mem_univ index, indexMem⟩⟩
  rw [output.cover.fullFiberShading_pointMultiplicity
    output.refinement.refined parent point] at positiveLocal ⊢
  unfold wz2PaperFullFiberPointMultiplicity at positiveLocal ⊢
  rw [output.cover.fullFiberIndices_eq parent] at positiveLocal ⊢
  exact output.fiber_pointMultiplicity_eq_muFine_of_pos
    parent point positiveLocal

/-- The corresponding pointwise multiplicity floor on a complete fiber. -/
theorem fullFiberShading_pointMultiplicity_lower
    (parent : Fin output.coarse.family.card)
    (point : Point3)
    (pointMem :
      point ∈
        (restrictPaperShading
          (output.cover.fullFiberSubfamily parent)
          output.refinement.refined).union) :
    (output.muFine : ENNReal) ≤
      (restrictPaperShading
        (output.cover.fullFiberSubfamily parent)
        output.refinement.refined).pointMultiplicity point := by
  rw [output.fullFiberShading_pointMultiplicity_eq_muFine
    parent pointMem]

/-- The exact packet multiplicity also gives the all-point upper bound on the
canonical restricted full-fiber shading. -/
theorem fullFiberShading_pointMultiplicity_le
    (parent : Fin output.coarse.family.card)
    (point : Point3) :
    ((restrictPaperShading
      (output.cover.fullFiberSubfamily parent)
      output.refinement.refined).pointMultiplicity point : ENNReal) ≤
        output.muFine := by
  rw [output.cover.fullFiberShading_pointMultiplicity
    output.refinement.refined parent point]
  unfold wz2PaperFullFiberPointMultiplicity
  rw [output.cover.fullFiberIndices_eq parent]
  exact output.fiber_pointMultiplicity_le parent point

/-- The record-level pointwise product multiplicity upper bound. -/
theorem pointwise_product_multiplicity_upper
    (point : Point3) :
    (output.refinement.refined.pointMultiplicity point : ENNReal) ≤
      (output.regularity * output.muCoarse : ENNReal) *
        output.muFine := by
  simpa only [Nat.cast_mul] using
    output.cover.toWZ1PaperTubeCover
      |>.pointMultiplicity_le_coarse_mul_fiber
        output.refinement.refined output.coarseShading
        output.balanced.point_compatibility
        output.coarse_pointMultiplicity_le
        output.fiber_pointMultiplicity_le
        point

end PaperFourDegreePacketCoreData

end Kakeya.Assouad.Prop62PaperAudit.V4

end
