import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TerminalMassRetention

/-!
# Proposition 6.2: four-degree lemma output

This is the thin assembly record for the paper's
`Four-degree packet core and exact balancing` lemma.

Every field refers to the same terminal complete fine family, terminal metric
parent family, exact final fine shading, and frozen coarse shading.  The
constructor performs no further selection.

The only inputs not produced by the deterministic finite construction are:

* one good fixed-cardinality balancing sample;
* ambient complete-fiber pure CWA, transported here by exact reindexing;
* the packet-density scalar absorption;
* the logarithmic mass-retention scalar absorption.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62PacketCellInput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput cover sourceShading)
    (multiplicity : input.FineMultiplicityClassData)
    (parentClass : input.ParentClassData multiplicity)
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        coarse ambientConstant scaleWindow}
    (treeCleanup :
      input.ParentTreeCleanupData
        multiplicity parentClass schedule)
    (exactification :
      input.PacketCellExactificationData
        multiplicity parentClass treeCleanup)
    (parentDegree :
      input.ReferenceParentDegreeData
        multiplicity parentClass treeCleanup exactification)
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}
    {A0 : ℕ}
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup
        exactification parentDegree bins A0)
    {degreeLoss : ℕ}
    (good : core.ranges.GoodBalancingSampleData degreeLoss)
    (families :
      input.TerminalCompleteFamiliesData
        multiplicity parentClass treeCleanup exactification
          core.ranges)

theorem selectedEdge_terminalParent
    {edge : exactification.incidence.Edge}
    (edgeSelected :
      edge ∈ core.ranges.selectedEdges good.sample) :
    ∃ parent :
        Fin families.restriction.coarseSelected.family.card,
      exactification.incidence.edgeParent edge =
        families.restriction.coarseSelected.embedding parent := by
  have edgeTerminal :
      edge ∈ core.ranges.terminalEdges :=
    good.selectedEdges_subset edgeSelected
  have parentTerminal :
      exactification.incidence.edgeParent edge ∈
        families.terminalParents := by
    rw [families.terminalParents_eq]
    exact
      Finset.mem_image.mpr
        ⟨edge, edgeTerminal, rfl⟩
  have parentImage :
      exactification.incidence.edgeParent edge ∈
        Finset.image
          families.restriction.coarseSelected.embedding
            Finset.univ := by
    rw [families.coarse_image_univ]
    exact parentTerminal
  rcases Finset.mem_image.mp parentImage with
    ⟨parent, _parentUniv, parentEq⟩
  exact ⟨parent, parentEq.symm⟩

/-- The paper-facing output of the fourth preparatory lemma. -/
structure FourDegreeLemmaOutputData
    (fiberConstant densityConstant : ENNReal)
    (logExponent : ℕ) where
  fineShading :
    WZ1PaperTubeShading
      families.restriction.fineSelected.family
  fineShading_eq :
    fineShading =
      input.terminalFineShading
        multiplicity parentClass treeCleanup exactification
          core.ranges good families
  coarseShading :
    WZ1PaperTubeShading
      families.restriction.coarseSelected.family
  coarseShading_eq :
    coarseShading =
      input.terminalCoarseShading
        multiplicity parentClass treeCleanup exactification
          core.ranges families
  balanced :
    PureWZ2BalancedCoverData
      families.restriction.section6Cover
      fineShading coarseShading
  muFine : ℕ
  muFine_eq : muFine = multiplicity.muFine
  muFine_pos : 0 < muFine
  exact_fine :
    ∀ edge ∈ core.ranges.selectedEdges good.sample,
      ∃ parent :
          Fin families.restriction.coarseSelected.family.card,
        exactification.incidence.edgeParent edge =
            families.restriction.coarseSelected.embedding parent ∧
          (TerminalFineShading.terminalPacketCellSources
            input multiplicity parentClass treeCleanup exactification
              parentDegree core good families parent edge).card =
            muFine
  W : ℕ
  W_eq : W = core.ranges.commonFineCellCount
  W_pos : 0 < W
  exact_balance :
    ∀ coarseCell ∈
        exactification.incidence.activeCoarseCells
          core.ranges.terminalEdges,
      volume
          (fineShading.union ∩
            wz1PaperGridCube rho coarseCell) =
        (W : ENNReal) *
          volume (wz1PaperGridCube delta (0, 0, 0))
  muCoarse : ℕ
  muCoarse_eq :
    muCoarse =
      core.terminalCoarseMultiplicity
        input multiplicity parentClass treeCleanup
          exactification parentDegree
  muCoarse_pos : 0 < muCoarse
  coarseLoss : ℕ
  coarseLoss_eq :
    coarseLoss =
      core.terminalCoarseMultiplicityLoss
        input multiplicity parentClass treeCleanup
          exactification parentDegree
  coarse_multiplicity :
    ∀ coarseCell : core.ranges.ActiveCoarseCell,
      muCoarse ≤
          (FrozenCoarseShading.terminalParentsAtCoarseCell
            input multiplicity parentClass treeCleanup exactification
              parentDegree core families coarseCell.1).card ∧
        (FrozenCoarseShading.terminalParentsAtCoarseCell
            input multiplicity parentClass treeCleanup exactification
              parentDegree core families coarseCell.1).card ≤
          coarseLoss * muCoarse
  fiberFloor : ℕ
  fiberFloor_eq : fiberFloor = parentClass.fiberFloor
  fiberFloor_pos : 0 < fiberFloor
  fiber_cardinality :
    ∀ parent :
        Fin families.restriction.coarseSelected.family.card,
      fiberFloor ≤
          (wz2PaperFullFiberIndices
            families.restriction.fineSelected.family
            families.restriction.coarseSelected.family parent).card ∧
        (wz2PaperFullFiberIndices
            families.restriction.fineSelected.family
            families.restriction.coarseSelected.family parent).card <
          2 * fiberFloor
  packet_density :
    ∀ parent :
        Fin families.restriction.coarseSelected.family.card,
      densityConstant * (fiberFloor : ENNReal) *
          Kakeya.realRpowENN delta 2 ≤
        TerminalFineShading.terminalFiberMass
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families parent
  parentConstant : ENNReal
  parentConstant_eq :
    parentConstant =
      input.terminalParentOutputConstant
        multiplicity parentClass treeCleanup exactification
          parentDegree core
  parent_cwa :
    WZ2PaperPureCWAAtNearbyScales
      families.restriction.coarseSelected.family
      parentConstant
  retained_mass :
    wz2PaperPureRefinementFraction delta logExponent *
        sourceShading.mass ≤
      fineShading.mass

theorem pureWZ2_prop62_four_degree_lemma_output
    {fiberConstant densityConstant : ENNReal}
    {logExponent : ℕ}
    (packetAbsorption :
      TerminalFineShading.PacketDensityAbsorptionData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good densityConstant)
    (massAbsorption :
      input.MassRetentionAbsorptionData
        multiplicity parentClass treeCleanup exactification
          parentDegree core good logExponent) :
    Nonempty
      (input.FourDegreeLemmaOutputData
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          fiberConstant densityConstant logExponent) := by
  let finalFine :=
    input.terminalFineShading
      multiplicity parentClass treeCleanup exactification
        core.ranges good families
  let finalCoarse :=
    input.terminalCoarseShading
      multiplicity parentClass treeCleanup exactification
        core.ranges families
  refine
    ⟨{
      fineShading := finalFine
      fineShading_eq := rfl
      coarseShading := finalCoarse
      coarseShading_eq := rfl
      balanced := ?_
      muFine := multiplicity.muFine
      muFine_eq := rfl
      muFine_pos := multiplicity.muFine_pos
      exact_fine := ?_
      W := core.ranges.commonFineCellCount
      W_eq := rfl
      W_pos := core.ranges.commonFineCellCount_pos
      exact_balance := ?_
      muCoarse :=
        core.terminalCoarseMultiplicity
          input multiplicity parentClass treeCleanup
            exactification parentDegree
      muCoarse_eq := rfl
      muCoarse_pos :=
        core.terminalCoarseMultiplicity_pos
          input multiplicity parentClass treeCleanup
            exactification parentDegree
      coarseLoss :=
        core.terminalCoarseMultiplicityLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree
      coarseLoss_eq := rfl
      coarse_multiplicity := ?_
      fiberFloor := parentClass.fiberFloor
      fiberFloor_eq := rfl
      fiberFloor_pos := parentClass.fiberFloor_pos
      fiber_cardinality := ?_
      packet_density := ?_
      parentConstant :=
        input.terminalParentOutputConstant
          multiplicity parentClass treeCleanup exactification
            parentDegree core
      parentConstant_eq := rfl
      parent_cwa :=
        input.terminalParentCWA
          multiplicity parentClass treeCleanup exactification
            parentDegree core families
      retained_mass := ?_
    }⟩
  · exact
      FrozenCoarseShading.balancedCoverData
        input multiplicity parentClass treeCleanup exactification
          core.ranges good families
  · intro edge edgeSelected
    rcases input.selectedEdge_terminalParent
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families edgeSelected
      with ⟨parent, edgeParent⟩
    exact
      ⟨parent, edgeParent,
        TerminalFineShading.terminal_exact_fine_multiplicity
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families edgeSelected edgeParent⟩
  · intro coarseCell coarseCellMem
    let activeCell : core.ranges.ActiveCoarseCell :=
      ⟨coarseCell, coarseCellMem⟩
    rw [TerminalFineShading.union_eq_ambient
      input multiplicity parentClass treeCleanup exactification
        core.ranges good families]
    exact
      ExactFineShading.ambient_union_inter_coarseCube_volume
        input multiplicity parentClass treeCleanup exactification
          core.ranges good activeCell
  · intro coarseCell
    exact
      FrozenCoarseShading.terminal_coarse_multiplicity_band
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families coarseCell
  · intro parent
    exact
      TerminalFineShading.terminalFiberCard_band
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families parent
  · intro parent
    exact
      TerminalFineShading.terminal_packet_density
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families packetAbsorption parent
  · exact
      input.terminal_mass_retention_fraction
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families massAbsorption

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
