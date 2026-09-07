import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSecondCall

/-!
# Genuine source witnesses for the direct-rich first coarse cells

WZ Lemma 5.4 uses the first Proposition 6.2 coarse `rho`-carrier for the
volume and global-grain bookkeeping, while the local plane normal remains the
one supplied on the original fine source.  This module records that
heterogeneous interface directly on the two dependent rich V4 calls.

Every active first balanced cell supplies a point of the exact first refined
shading in that cell.  Its selected-family index embeds literally into the
current source, so the normal, vertical bound, Lipschitz comparison, and local
AD receipt all come from the same P1 source witness.  No owner or reconstructed
sticky wrapper is used.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The paper-faithful coarse/fine witness interface attached to the first
balanced cover of two dependent direct-rich Proposition 6.2 calls. -/
structure PureWZ2Node05V4RichCoarseCellWitnessData
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    (twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested) where
  activeCells : Finset WZ2PaperCellIndex
  activeCells_eq :
    activeCells = twoScale.firstBalancedCover.activeCells
  witness : WZ2PaperCellIndex → Point3
  witness_mem_refined :
    ∀ cell ∈ activeCells,
      witness cell ∈ twoScale.first.refinedFineShading.union
  witness_mem_cell :
    ∀ cell ∈ activeCells,
      witness cell ∈ wz1PaperGridCube rhoRequested.1 cell
  sourceIndex : WZ2PaperCellIndex → Fin current.grain.family.card
  witness_mem_source :
    ∀ cell ∈ activeCells,
      witness cell ∈ current.grain.shading.carrier (sourceIndex cell)
  normal : WZ2PaperCellIndex → Point3
  normal_eq :
    ∀ cell (hcell : cell ∈ activeCells),
      normal cell = current.grain.localGrains.planeMap
        ⟨witness cell,
          ⟨sourceIndex cell, witness_mem_source cell hcell⟩⟩
  normal_unit :
    ∀ cell ∈ activeCells, ‖normal cell‖ = 1
  normal_vertical :
    ∀ cell ∈ activeCells, |normal cell (2 : Fin 3)| ≤ 1 / 2
  normal_dist :
    ∀ first ∈ activeCells, ∀ second ∈ activeCells,
      dist (normal first) (normal second) ≤
        dist (witness first) (witness second)
  fine_local_ad :
    ∀ cell ∈ activeCells,
      PureWZ2PaperADSet1
        (scalarProjection (normal cell)
          (current.grain.shading.union ∩
            Metric.closedBall (witness cell) (Real.sqrt rhoRequested.1)))
        rhoRequested.1 (1 - sigma)
        (Kakeya.realRpowENN delta (-inputLoss))

namespace PureWZ2Node05V4RichSecondCallData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}

/-- Select one genuine current-source point in every active first balanced
cell.  All normal and AD fields are literal projections of the supplied P1
grain source. -/
theorem coarseCellWitnesses
    (twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested) :
    Nonempty (PureWZ2Node05V4RichCoarseCellWitnessData twoScale) := by
  let activeCells := twoScale.firstBalancedCover.activeCells
  have hcellWitness :
      ∀ cell ∈ activeCells,
        (twoScale.first.refinedFineShading.union ∩
          wz1PaperGridCube rhoRequested.1 cell).Nonempty := by
    intro cell hcell
    exact twoScale.firstBalancedCover.cellIntersection_nonempty cell hcell
  let witness : WZ2PaperCellIndex → Point3 := fun cell =>
    if hcell : cell ∈ activeCells then
      Classical.choose (hcellWitness cell hcell)
    else 0
  have hwitness :
      ∀ cell (hcell : cell ∈ activeCells),
        witness cell ∈ twoScale.first.refinedFineShading.union ∩
          wz1PaperGridCube rhoRequested.1 cell := by
    intro cell hcell
    simp only [witness, dif_pos hcell]
    exact Classical.choose_spec (hcellWitness cell hcell)
  let selectedIndex : WZ2PaperCellIndex →
      Fin twoScale.first.finalFineFamily.card := fun cell =>
    if hcell : cell ∈ activeCells then
      Classical.choose (hwitness cell hcell).1
    else
      ⟨0, twoScale.first.publicSticky.selected_nonempty⟩
  have hwitnessSelected :
      ∀ cell (hcell : cell ∈ activeCells),
        witness cell ∈
          twoScale.first.refinedFineShading.carrier (selectedIndex cell) := by
    intro cell hcell
    simp only [selectedIndex, dif_pos hcell]
    exact Classical.choose_spec (hwitness cell hcell).1
  let sourceIndex : WZ2PaperCellIndex → Fin current.grain.family.card :=
    fun cell =>
      twoScale.first.publicSticky.selected.embedding (selectedIndex cell)
  have hwitnessSource :
      ∀ cell (hcell : cell ∈ activeCells),
        witness cell ∈ current.grain.shading.carrier (sourceIndex cell) := by
    intro cell hcell
    exact twoScale.first.publicSticky.subshading (selectedIndex cell)
      (hwitnessSelected cell hcell)
  let normal : WZ2PaperCellIndex → Point3 := fun cell =>
    if hcell : cell ∈ activeCells then
      current.grain.localGrains.planeMap
        ⟨witness cell,
          ⟨sourceIndex cell, hwitnessSource cell hcell⟩⟩
    else 0
  have hnormalEq :
      ∀ cell (hcell : cell ∈ activeCells),
        normal cell = current.grain.localGrains.planeMap
          ⟨witness cell,
            ⟨sourceIndex cell, hwitnessSource cell hcell⟩⟩ := by
    intro cell hcell
    simp [normal, hcell]
  refine
    ⟨{ activeCells := activeCells
       activeCells_eq := rfl
       witness := witness
       witness_mem_refined := fun cell hcell => (hwitness cell hcell).1
       witness_mem_cell := fun cell hcell => (hwitness cell hcell).2
       sourceIndex := sourceIndex
       witness_mem_source := hwitnessSource
       normal := normal
       normal_eq := hnormalEq
       normal_unit := ?_
       normal_vertical := ?_
       normal_dist := ?_
       fine_local_ad := ?_ }⟩
  · intro cell hcell
    rw [hnormalEq cell hcell]
    exact current.grain.localGrains.planeMap_unit _
  · intro cell hcell
    rw [hnormalEq cell hcell]
    exact current.grain.planeMap_vertical_bound _
  · intro first hfirst second hsecond
    rw [hnormalEq first hfirst, hnormalEq second hsecond]
    have h := current.grain.localGrains.planeMap_lipschitz.dist_le_mul
      ⟨witness first,
        ⟨sourceIndex first, hwitnessSource first hfirst⟩⟩
      ⟨witness second,
        ⟨sourceIndex second, hwitnessSource second hsecond⟩⟩
    have hsubtype :
        dist
            (⟨witness first,
              ⟨sourceIndex first, hwitnessSource first hfirst⟩⟩ :
              {point : Point3 // point ∈ current.grain.shading.union})
            (⟨witness second,
              ⟨sourceIndex second, hwitnessSource second hsecond⟩⟩ :
              {point : Point3 // point ∈ current.grain.shading.union}) =
          dist (witness first) (witness second) := rfl
    simpa [hsubtype] using h
  · intro cell hcell
    rw [hnormalEq cell hcell]
    exact current.grain.localGrains.local_ad rhoRequested.1
      rhoRequested.property.1 rhoRequested.property.2 _

end PureWZ2Node05V4RichSecondCallData

end Kakeya.Assouad

end
