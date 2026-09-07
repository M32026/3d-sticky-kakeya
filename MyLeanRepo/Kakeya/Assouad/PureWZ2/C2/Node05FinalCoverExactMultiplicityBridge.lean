import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDirectPositiveFinalParentDeletion
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ExactMultiplicityTruncation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Section6CoverAdapter

/-!
# Final-cover bridge to Node-5 exact multiplicity

The paper final-cover adapter already carries a global fine multiplicity band and an
exact balanced cover.  This module converts its paper partitioning cover to
the pure Section-6 interface, truncates every active fine cell to exactly the
lower dyadic multiplicity, and packages the result as Node-5 balanced data.
The fine-cell nesting certificate is derived from the adapter's own retained
cell decomposition and containment fields.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- The exact adapter already records the containing coarse cell of every
retained literal fine cell.  Cubicality identifies the fine cell containing a
point with that retained cell, so no external ancestry certificate is needed. -/
theorem WZ2PaperFinalBalancedCoverExactAdapterData.fineCellNested
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
        (hdelta := hdelta) (hrho := hrho) cover sourceShading coarseCells
        availableFineCells balancing coarseData}
    (adapter : WZ2PaperFinalBalancedCoverExactAdapterData producer) :
    ∀ source point, point ∈ adapter.exact.refined.carrier source →
      ∃ cell ∈ adapter.exact.retainedCoarseCells,
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          wz1PaperGridCube rho cell := by
  intro source point hpoint
  have hpointUnion : point ∈ adapter.exact.refined.union :=
    ⟨source, hpoint⟩
  rw [adapter.exact.refined_union_eq] at hpointUnion
  rcases Set.mem_iUnion₂.mp hpointUnion with
    ⟨fineCell, hfineRetained, hpointFine⟩
  rw [adapter.exact.retainedFineCells_eq] at hfineRetained
  rcases Finset.mem_biUnion.mp hfineRetained with
    ⟨coarseCell, hcoarse, hfine⟩
  have hindex : wz1PaperGridIndex delta point = fineCell :=
    (mem_wz1PaperGridCube delta fineCell point).mp hpointFine
  refine ⟨coarseCell, hcoarse, ?_⟩
  rw [hindex]
  exact adapter.exact.fine_cell_containment
    coarseCell hcoarse fineCell hfine

/-- Convert the final V4 multiplicity band and exact balanced-cover adapter
into a same-family exact-multiplicity Node-5 balanced cover. -/
theorem WZ2PaperFinalBalancedCoverExactAdapterData.toNode5ExactMultiplicity
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
        (hdelta := hdelta) (hrho := hrho) cover sourceShading coarseCells
        availableFineCells balancing coarseData}
    (adapter : WZ2PaperFinalBalancedCoverExactAdapterData producer)
    (fineLine : WZ1PaperIsLineClass fine)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (coarseDistinct : WZ1PaperIsEssentiallyDistinct coarse) :
    ∃ section6Cover : PureWZ2Section6Cover fine coarse,
      ∃ base : PureWZ2BalancedCoverData section6Cover
          adapter.exact.refined adapter.coarseData.coarseShading,
        let m : ℕ := 2 ^ producer.finalFine.fineLevel
        let truncation := pureWZ2Node05_exactMultiplicityTruncation
          adapter.exact.refined hdelta adapter.exact.refined_cubical m
            (by positivity) (by
              intro point hpoint
              have hband := adapter.fine_multiplicity_band point hpoint
              constructor
              · exact_mod_cast hband.1
              · have hupper := hband.2.le
                have hpow :
                    (2 ^ (producer.finalFine.fineLevel + 1) : ENNReal) =
                      (2 * m : ℕ) := by
                  simp [m, pow_succ, mul_comm]
                rw [hpow] at hupper
                exact_mod_cast hupper)
        Nonempty
          (PureWZ2Node5BalancedCoverData (truncation.toBalancedBase base)) := by
  let section6Cover : PureWZ2Section6Cover fine coarse :=
    { fine_line_class := fineLine
      coarse_line_class := coarseLine
      covers := fun source =>
        ⟨cover.parent source, cover.parent_covers source⟩
      parent_hit := by
        intro parent
        rcases cover.parent_surjective parent with ⟨source, hsource⟩
        refine ⟨source, ?_⟩
        rw [← hsource]
        exact cover.parent_covers source
      coarse_essentially_distinct := coarseDistinct }
  let base : PureWZ2BalancedCoverData section6Cover
      adapter.exact.refined adapter.coarseData.coarseShading :=
    { point_compatibility := by
        intro source parent hcovers point hpoint
        have hparentCandidate : parent = cover.parent source :=
          cover.parent_unique source parent hcovers
        rw [hparentCandidate]
        exact adapter.coarseData.balancedCover.point_compatibility
          source point hpoint
      coarse_cubical := adapter.coarseData.balancedCover.coarse_cubical
      activeCells := adapter.exact.retainedCoarseCells
      coarse_union_eq := adapter.coarseData.coarse_union_eq_retainedCoarseCells
      cellMass := adapter.exact.cellMass
      cellMass_pos := adapter.exact.cellMass_pos
      cellMass_ne_top := adapter.exact.cellMass_ne_top
      fine_cell_mass := adapter.exact.fine_cell_mass }
  let m : ℕ := 2 ^ producer.finalFine.fineLevel
  have hm : 0 < m := by positivity
  have hconstant : adapter.exact.refined.HasConstantMultiplicity m (2 * m) := by
    intro point hpoint
    have hband := adapter.fine_multiplicity_band point hpoint
    constructor
    · exact_mod_cast hband.1
    · have hupper := hband.2.le
      have hpow :
          (2 ^ (producer.finalFine.fineLevel + 1) : ENNReal) =
            (2 * m : ℕ) := by
        simp [m, pow_succ, mul_comm]
      rw [hpow] at hupper
      exact_mod_cast hupper
  let truncation := pureWZ2Node05_exactMultiplicityTruncation
    adapter.exact.refined hdelta adapter.exact.refined_cubical m hm hconstant
  refine ⟨section6Cover, base, ?_⟩
  exact ⟨truncation.toNode5Balanced base hm adapter.fineCellNested⟩

end Kakeya.Assouad

end
