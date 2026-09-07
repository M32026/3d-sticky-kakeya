import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ParentTreeCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeIncidence

/-!
# Proposition 6.2: exact packet-cell incidences after tree cleanup

This is the first point at which packet-cell incidences are made exact.
Only pairs whose metric parent survived the weighted reference-tree cleanup
are retained.  Every such pair keeps exactly `muFine` of its original
fine-tube incidences, while the fine and coarse tube families themselves
remain unchanged.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62PacketCellInput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput cover shading)
    (multiplicity : input.FineMultiplicityClassData)
    (parentClass : input.ParentClassData multiplicity)
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        coarse ambientConstant scaleWindow}
    (treeCleanup :
      input.ParentTreeCleanupData
        multiplicity parentClass schedule)

/-- Multiplicity-class pairs whose parent survived the weighted tree cleanup. -/
def referencePairs :
    Finset (Fin coarse.card × WZ2PaperCellIndex) :=
  multiplicity.selectedPairs.filter fun pair =>
    pair.1 ∈ treeCleanup.referenceParents

theorem referencePairs_nonempty :
    (input.referencePairs multiplicity parentClass treeCleanup).Nonempty := by
  rcases treeCleanup.referenceParents_nonempty with
    ⟨parent, parentMem⟩
  rcases
      ParentTreeCleanupData.reference_parent_has_selected_pair
        input multiplicity parentClass schedule
        treeCleanup parentMem
    with ⟨pair, pairMem⟩
  have pairParent :
      pair.1 = parent :=
    (Finset.mem_filter.mp pairMem).2
  exact
    ⟨pair,
      Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp pairMem).1,
          by simpa [pairParent] using parentMem⟩⟩

@[simp]
theorem mem_referencePairs_iff
    (pair : Fin coarse.card × WZ2PaperCellIndex) :
    pair ∈ input.referencePairs multiplicity parentClass treeCleanup ↔
      pair ∈ multiplicity.selectedPairs ∧
        pair.1 ∈ treeCleanup.referenceParents := by
  simp [referencePairs]

structure PacketCellExactificationData where
  selectedSources :
    (pair :
      {pair //
        pair ∈ input.referencePairs multiplicity parentClass treeCleanup}) →
      Finset (Fin fine.card)
  selectedSources_subset :
    ∀ pair,
      selectedSources pair ⊆
        input.packetCellSources pair.1.1 pair.1.2
  selectedSources_card :
    ∀ pair,
      (selectedSources pair).card = multiplicity.muFine
  incidence :
    PureWZ2Prop62FourDegreeIncidenceData
      (Fin coarse.card) WZ2PaperCellIndex WZ2PaperCellIndex
  incidence_coarseCellOf_eq :
    incidence.coarseCellOf = input.coarseCellOf
  incidence_edgePool_eq :
    incidence.edgePool =
      input.referencePairs multiplicity parentClass treeCleanup
  edgePool_nonempty : incidence.edgePool.Nonempty
  selected_incidence_count :
    (∑ pair, (selectedSources pair).card) =
      multiplicity.muFine * incidence.edgePool.card
  reference_multiplicity_sum_le_exact :
    (∑ pair ∈ input.referencePairs multiplicity parentClass treeCleanup,
        input.packetCellMultiplicity pair) ≤
      2 *
        (∑ pair, (selectedSources pair).card)
  active_parent_iff :
    ∀ parent,
      parent ∈
          incidence.activeParents incidence.allEdges ↔
        parent ∈ treeCleanup.referenceParents

namespace PacketCellExactificationData

variable
    (exactification :
      input.PacketCellExactificationData
        multiplicity parentClass treeCleanup)

theorem selectedSource_mem_fullFiber
    (pair :
      {pair //
        pair ∈ input.referencePairs multiplicity parentClass treeCleanup})
    {source : Fin fine.card}
    (sourceMem :
      source ∈ exactification.selectedSources pair) :
    source ∈
      wz2PaperFullFiberIndices fine coarse pair.1.1 := by
  exact
    FineMultiplicityClassData.source_mem_fullFiber
      input multiplicity
      ⟨pair.1,
        (input.mem_referencePairs_iff
          multiplicity parentClass treeCleanup pair.1).mp pair.2 |>.1⟩
      (exactification.selectedSources_subset pair sourceMem)

theorem selectedCell_subset_carrier
    (pair :
      {pair //
        pair ∈ input.referencePairs multiplicity parentClass treeCleanup})
    {source : Fin fine.card}
    (sourceMem :
      source ∈ exactification.selectedSources pair) :
    wz1PaperGridCube delta pair.1.2 ⊆
      shading.carrier source := by
  exact
    FineMultiplicityClassData.cell_subset_carrier
      input multiplicity
      ⟨pair.1,
        (input.mem_referencePairs_iff
          multiplicity parentClass treeCleanup pair.1).mp pair.2 |>.1⟩
      (exactification.selectedSources_subset pair sourceMem)

theorem selectedCoarseCell_subset_parentCarrier
    (pair :
      {pair //
        pair ∈ input.referencePairs multiplicity parentClass treeCleanup})
    {source : Fin fine.card}
    (sourceMem :
      source ∈ exactification.selectedSources pair) :
    wz1PaperGridCube rho (input.coarseCellOf pair.1.2) ⊆
      wz1PaperTubeCarrier (coarse.tube pair.1.1) := by
  exact
    FineMultiplicityClassData.coarseCell_subset_parentCarrier
      input multiplicity
      ⟨pair.1,
        (input.mem_referencePairs_iff
          multiplicity parentClass treeCleanup pair.1).mp pair.2 |>.1⟩
      (exactification.selectedSources_subset pair sourceMem)

end PacketCellExactificationData

theorem pureWZ2_prop62_packet_cell_exactification :
    Nonempty
      (input.PacketCellExactificationData
        multiplicity parentClass treeCleanup) := by
  let referencePairs :=
    input.referencePairs multiplicity parentClass treeCleanup
  have exactSourcesExist :
      ∀ pair : {pair // pair ∈ referencePairs},
        ∃ sources : Finset (Fin fine.card),
          sources ⊆
              input.packetCellSources pair.1.1 pair.1.2 ∧
            sources.card = multiplicity.muFine := by
    intro pair
    have pairSelected :
        pair.1 ∈ multiplicity.selectedPairs :=
      (input.mem_referencePairs_iff
          multiplicity parentClass treeCleanup pair.1).mp pair.2 |>.1
    have lower :
        multiplicity.muFine ≤
          (input.packetCellSources
            pair.1.1 pair.1.2).card := by
      exact
        (multiplicity.multiplicity_band
          pair.1 pairSelected).1
    rcases Finset.exists_subset_card_eq lower with
      ⟨sources, sourcesSubset, sourcesCard⟩
    exact ⟨sources, sourcesSubset, sourcesCard⟩
  choose selectedSources selectedSourcesSubset
    selectedSourcesCard using exactSourcesExist
  let incidence :
      PureWZ2Prop62FourDegreeIncidenceData
        (Fin coarse.card) WZ2PaperCellIndex WZ2PaperCellIndex :=
    {
      coarseCellOf := input.coarseCellOf
      edgePool := referencePairs
    }
  have incidenceCount :
      (∑ pair, (selectedSources pair).card) =
        multiplicity.muFine * incidence.edgePool.card := by
    calc
      (∑ pair, (selectedSources pair).card) =
          ∑ _pair : {pair // pair ∈ referencePairs},
            multiplicity.muFine := by
        apply Finset.sum_congr rfl
        intro pair _
        exact selectedSourcesCard pair
      _ =
          Fintype.card {pair // pair ∈ referencePairs} *
            multiplicity.muFine := by
        simp
      _ =
          multiplicity.muFine * incidence.edgePool.card := by
        simp [incidence, Fintype.card_coe]
        ring
  have referenceSumUpper :
      (∑ pair ∈ referencePairs,
          input.packetCellMultiplicity pair) ≤
        2 * multiplicity.muFine * referencePairs.card := by
    calc
      (∑ pair ∈ referencePairs,
          input.packetCellMultiplicity pair) ≤
          ∑ _pair ∈ referencePairs,
            2 * multiplicity.muFine := by
        apply Finset.sum_le_sum
        intro pair pairMem
        have pairSelected :
            pair ∈ multiplicity.selectedPairs :=
          (input.mem_referencePairs_iff
          multiplicity parentClass treeCleanup pair).mp pairMem |>.1
        exact
          (multiplicity.multiplicity_band
            pair pairSelected).2.le
      _ = 2 * multiplicity.muFine * referencePairs.card := by
        simp
        ring
  have exactRetention :
      (∑ pair ∈ referencePairs,
          input.packetCellMultiplicity pair) ≤
        2 * (∑ pair, (selectedSources pair).card) := by
    calc
      (∑ pair ∈ referencePairs,
          input.packetCellMultiplicity pair) ≤
          2 * multiplicity.muFine * referencePairs.card :=
        referenceSumUpper
      _ = 2 * (∑ pair, (selectedSources pair).card) := by
        rw [incidenceCount]
        simp [incidence]
        ring
  have activeParentIff :
      ∀ parent,
        parent ∈ incidence.activeParents incidence.allEdges ↔
          parent ∈ treeCleanup.referenceParents := by
    intro parent
    rw [incidence.mem_activeParents_iff]
    constructor
    · intro degreePos
      rcases Finset.card_pos.mp degreePos with
        ⟨edge, edgeMem⟩
      have edgeAll :=
        (Finset.mem_filter.mp edgeMem).1
      have edgeReference :
          edge.1 ∈ referencePairs := edge.2
      have edgeParentEq :
          edge.1.1 = parent :=
        (Finset.mem_filter.mp edgeMem).2
      have parentMem :
          edge.1.1 ∈ treeCleanup.referenceParents :=
        (input.mem_referencePairs_iff
          multiplicity parentClass treeCleanup edge.1).mp edgeReference |>.2
      simpa [edgeParentEq] using parentMem
    · intro parentMem
      rcases
          ParentTreeCleanupData.reference_parent_has_selected_pair
            input multiplicity parentClass schedule
            treeCleanup parentMem
        with ⟨pair, pairMem⟩
      have pairParent :
          pair.1 = parent :=
        (Finset.mem_filter.mp pairMem).2
      have pairReference :
          pair ∈ referencePairs := by
        exact
          (input.mem_referencePairs_iff
          multiplicity parentClass treeCleanup pair).mpr
              ⟨(Finset.mem_filter.mp pairMem).1,
                by simpa [pairParent] using parentMem⟩
      let edge : incidence.Edge :=
        ⟨pair, pairReference⟩
      exact
        Finset.card_pos.mpr
          ⟨edge,
            Finset.mem_filter.mpr
              ⟨Finset.mem_univ edge, by
                simpa [incidence,
                  PureWZ2Prop62FourDegreeIncidenceData.edgeParent,
                  pairParent]⟩⟩
  exact
    ⟨{
      selectedSources := selectedSources
      selectedSources_subset := selectedSourcesSubset
      selectedSources_card := selectedSourcesCard
      incidence := incidence
      incidence_coarseCellOf_eq := rfl
      incidence_edgePool_eq := rfl
      edgePool_nonempty := by
        simpa [incidence, referencePairs] using
          input.referencePairs_nonempty
            multiplicity parentClass treeCleanup
      selected_incidence_count := incidenceCount
      reference_multiplicity_sum_le_exact := exactRetention
      active_parent_iff := activeParentIff
    }⟩

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
