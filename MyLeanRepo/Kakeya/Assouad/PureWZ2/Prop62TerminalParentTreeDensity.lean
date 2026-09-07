import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeCoreAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TerminalCompleteFamilies

/-!
# Proposition 6.2: terminal density in the parent schedule tree

The first weighted tree cleanup produces a locally dense reference parent
subtree.  During the later simultaneous four-degree peeling, a reference
node is deleted whenever its current terminal parent count drops below the
`A0⁻¹` fraction of the reference count.

This module identifies those current counts with the terminal parent
projection of the final edge core and combines the two density statements.
The result is the exact node-density bridge needed to restrict every
scheduled pure scale witness to the terminal parent family.
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

def terminalParentsAtNode
    (level : ℕ)
    (node : Finset (Fin coarse.card)) :
    Finset (Fin coarse.card) :=
  input.terminalParentIndices
      multiplicity parentClass treeCleanup exactification
      core.ranges ∩
    schedule.tree.fiber level node

theorem currentParents_eq_terminalParentsAtNode
    (level : ℕ)
    (node : Finset (Fin coarse.card)) :
    input.currentParents
        multiplicity parentClass treeCleanup exactification
        core.peeling.core (level, node) =
      input.terminalParentsAtNode
        multiplicity parentClass treeCleanup exactification
        parentDegree core level node := by
  ext parent
  constructor
  · intro parentMem
    rcases Finset.mem_image.mp parentMem with
      ⟨edge, edgeMem, edgeParent⟩
    have edgeCurrent :
        edge ∈
          input.currentTreeBlock
            multiplicity parentClass treeCleanup exactification
            core.peeling.core (level, node) :=
      edgeMem
    have edgeData := Finset.mem_inter.mp edgeCurrent
    have edgeBlock := Finset.mem_filter.mp edgeData.2
    have parentTerminal :
        parent ∈
          input.terminalParentIndices
            multiplicity parentClass treeCleanup exactification
            core.ranges := by
      have edgeTerminal :
          edge ∈ core.ranges.terminalEdges := by
        change edge ∈ core.ranges.peeling.core
        rw [core.ranges_peeling_eq]
        exact edgeData.1
      exact
        Finset.mem_image.mpr
          ⟨edge, edgeTerminal, edgeParent⟩
    have parentNode :
        parent ∈ schedule.tree.fiber level node := by
      rw [← edgeParent]
      exact edgeBlock.2
    exact Finset.mem_inter.mpr ⟨parentTerminal, parentNode⟩
  · intro parentMem
    have parentData := Finset.mem_inter.mp parentMem
    rcases Finset.mem_image.mp parentData.1 with
      ⟨edge, edgeCore, edgeParent⟩
    have edgePeeling :
        edge ∈ core.peeling.core := by
      change edge ∈ core.ranges.peeling.core at edgeCore
      rw [core.ranges_peeling_eq] at edgeCore
      exact edgeCore
    have edgeBlock :
        edge ∈
          input.referenceTreeBlock
            multiplicity parentClass treeCleanup exactification
            (level, node) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ edge, ?_⟩
      rw [edgeParent]
      exact parentData.2
    have edgeCurrent :
        edge ∈
          input.currentTreeBlock
            multiplicity parentClass treeCleanup exactification
            core.peeling.core (level, node) :=
      Finset.mem_inter.mpr ⟨edgePeeling, edgeBlock⟩
    exact
      Finset.mem_image.mpr
        ⟨edge, edgeCurrent, edgeParent⟩

theorem terminalParent_mem_reference
    {parent : Fin coarse.card}
    (parentMem :
      parent ∈
        input.terminalParentIndices
          multiplicity parentClass treeCleanup exactification
          core.ranges) :
    parent ∈ treeCleanup.referenceParents := by
  rcases Finset.mem_image.mp parentMem with
    ⟨edge, edgeCore, edgeParent⟩
  have edgeAll :
      edge ∈ exactification.incidence.allEdges := by
    exact Finset.mem_univ edge
  have parentActive :
      parent ∈
        exactification.incidence.activeParents
          exactification.incidence.allEdges := by
    rw [exactification.incidence.mem_activeParents_iff]
    apply Finset.card_pos.mpr
    exact
      ⟨edge,
        Finset.mem_filter.mpr
          ⟨edgeAll, edgeParent⟩⟩
  exact (exactification.active_parent_iff parent).mp parentActive

theorem terminalNode_label_mem
    {level : ℕ}
    (level_le : level ≤ schedule.levelCount)
    {node : Finset (Fin coarse.card)}
    (terminalNonempty :
      (input.terminalParentsAtNode
        multiplicity parentClass treeCleanup exactification
        parentDegree core level node).Nonempty) :
    (level, node) ∈
      input.referenceTreeLabels
        multiplicity parentClass treeCleanup := by
  rcases terminalNonempty with ⟨parent, parentMem⟩
  have parentData := Finset.mem_inter.mp parentMem
  have parentReference :=
    input.terminalParent_mem_reference
      multiplicity parentClass treeCleanup exactification
      parentDegree core parentData.1
  have parentNodeEq :
      schedule.nodeAt level parent = node :=
    (Finset.mem_filter.mp parentData.2).2
  apply Finset.mem_biUnion.mpr
  refine
    ⟨level,
      Finset.mem_range.mpr (by omega),
      ?_⟩
  exact
    Finset.mem_image.mpr
      ⟨parent, parentReference, by
        rw [parentNodeEq]⟩

theorem referenceCount_le_A0_mul_terminalCount
    {level : ℕ}
    (level_le : level ≤ schedule.levelCount)
    (node : Finset (Fin coarse.card))
    (terminalNonempty :
      (input.terminalParentsAtNode
        multiplicity parentClass treeCleanup exactification
        parentDegree core level node).Nonempty) :
    input.referenceCount
        multiplicity parentClass treeCleanup (level, node) ≤
      A0 *
        (input.terminalParentsAtNode
          multiplicity parentClass treeCleanup exactification
          parentDegree core level node).card := by
  have labelMem :=
    input.terminalNode_label_mem
      multiplicity parentClass treeCleanup exactification
      parentDegree core level_le terminalNonempty
  have stable :=
    core.peeling.tree_stable (level, node) labelMem
  have currentCountPos :
      0 <
        input.currentParentCount
          multiplicity parentClass treeCleanup exactification
          core.peeling.core (level, node) := by
    unfold currentParentCount
    rw [input.currentParents_eq_terminalParentsAtNode
      multiplicity parentClass treeCleanup exactification
      parentDegree core level node]
    exact terminalNonempty.card_pos
  change
    ¬(0 <
        input.currentParentCount
          multiplicity parentClass treeCleanup exactification
          core.peeling.core (level, node) ∧
      A0 *
          input.currentParentCount
            multiplicity parentClass treeCleanup exactification
            core.peeling.core (level, node) <
        input.referenceCount
          multiplicity parentClass treeCleanup (level, node)) at stable
  have notStrict :
      ¬ A0 *
          input.currentParentCount
            multiplicity parentClass treeCleanup exactification
            core.peeling.core (level, node) <
        input.referenceCount
          multiplicity parentClass treeCleanup (level, node) := by
    intro strict
    exact stable ⟨currentCountPos, strict⟩
  have referenceLe :
      input.referenceCount
          multiplicity parentClass treeCleanup (level, node) ≤
        A0 *
          input.currentParentCount
            multiplicity parentClass treeCleanup exactification
            core.peeling.core (level, node) := by
    omega
  unfold currentParentCount at referenceLe
  rw [input.currentParents_eq_terminalParentsAtNode
    multiplicity parentClass treeCleanup exactification
    parentDegree core level node] at referenceLe
  exact referenceLe

theorem terminal_node_density
    {level : ℕ}
    (level_le : level ≤ schedule.levelCount)
    (node : Finset (Fin coarse.card))
    (terminalNonempty :
      (input.terminalParentsAtNode
        multiplicity parentClass treeCleanup exactification
        parentDegree core level node).Nonempty) :
    parentClass.selectedParents.card *
        (schedule.tree.fiber level node).card ≤
      (2 ^ schedule.levelCount * A0) *
        (input.terminalParentsAtNode
          multiplicity parentClass treeCleanup exactification
          parentDegree core level node).card *
        coarse.card := by
  have referenceNonempty :
      (treeCleanup.referenceParents ∩
        schedule.tree.fiber level node).Nonempty := by
    rcases terminalNonempty with ⟨parent, parentMem⟩
    have parentData := Finset.mem_inter.mp parentMem
    exact
      ⟨parent,
        Finset.mem_inter.mpr
          ⟨input.terminalParent_mem_reference
              multiplicity parentClass treeCleanup exactification
              parentDegree core parentData.1,
            parentData.2⟩⟩
  have referenceDensity :=
    treeCleanup.node_density level level_le node referenceNonempty
  have referenceLe :=
    input.referenceCount_le_A0_mul_terminalCount
      multiplicity parentClass treeCleanup exactification
      parentDegree core level_le node terminalNonempty
  have multiplied :
      2 ^ schedule.levelCount *
          (treeCleanup.referenceParents ∩
            schedule.tree.fiber level node).card *
          coarse.card ≤
        (2 ^ schedule.levelCount * A0) *
          (input.terminalParentsAtNode
            multiplicity parentClass treeCleanup exactification
            parentDegree core level node).card *
          coarse.card := by
    change
      2 ^ schedule.levelCount *
          input.referenceCount
            multiplicity parentClass treeCleanup (level, node) *
          coarse.card ≤ _
    calc
      2 ^ schedule.levelCount *
            input.referenceCount
              multiplicity parentClass treeCleanup (level, node) *
            coarse.card ≤
          2 ^ schedule.levelCount *
            (A0 *
              (input.terminalParentsAtNode
                multiplicity parentClass treeCleanup exactification
                parentDegree core level node).card) *
            coarse.card := by
        gcongr
      _ = _ := by ring
  exact referenceDensity.trans multiplied

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
