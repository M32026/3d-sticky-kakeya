import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ReferenceParentDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeBinning
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4CleanupReceiptAdapter

/-!
# Proposition 6.2: deterministic four-degree prefix

Once the genuine metric cover, its fixed-grid shading, and a finite nested
schedule on the metric-parent family are fixed, every selection before the
simultaneous peeling is deterministic up to finite choice:

1. the global packet-cell multiplicity class;
2. the weighted parent and complete-fiber cardinality class;
3. the one-pass parent-tree core;
4. exact `muFine` packet-cell incidences;
5. the reference parent-degree scale and three ordered degree bins.

This module packages those choices without assuming the later peeling charge
bound or the probabilistic balancing estimate.
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
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        coarse ambientConstant scaleWindow)

/--
All finite choices in the four-degree lemma before the simultaneous peeling
charge estimate.
-/
structure FourDegreePrefixData where
  multiplicity : input.FineMultiplicityClassData
  parentClass : input.ParentClassData multiplicity
  treeCleanup :
    input.ParentTreeCleanupData
      multiplicity parentClass schedule
  exactification :
    input.PacketCellExactificationData
      multiplicity parentClass treeCleanup
  parentDegree :
    input.ReferenceParentDegreeData
      multiplicity parentClass treeCleanup exactification
  bins :
    exactification.incidence.ThreeDegreeBinningData
      exactification.incidence.allEdges

theorem pureWZ2_prop62_four_degree_prefix :
    Nonempty (input.FourDegreePrefixData schedule) := by
  rcases input.pureWZ2_prop62_packet_cell_fine_multiplicity_class with
    ⟨multiplicity⟩
  rcases input.pureWZ2_prop62_parent_class_selection multiplicity with
    ⟨parentClass⟩
  rcases
      input.pureWZ2_prop62_parent_tree_cleanup
        multiplicity parentClass schedule
    with ⟨treeCleanup⟩
  rcases
      input.pureWZ2_prop62_packet_cell_exactification
        multiplicity parentClass treeCleanup
    with ⟨exactification⟩
  rcases
      input.pureWZ2_prop62_reference_parent_degree
        multiplicity parentClass treeCleanup exactification
    with ⟨parentDegree⟩
  have allEdgesNonempty :
      exactification.incidence.allEdges.Nonempty := by
    rcases exactification.edgePool_nonempty with ⟨pair, pairMem⟩
    exact ⟨⟨pair, pairMem⟩, Finset.mem_univ _⟩
  rcases
      exactification.incidence.pureWZ2_prop62_three_degree_binning
        exactification.incidence.allEdges allEdgesNonempty
    with ⟨bins⟩
  exact
    ⟨{
      multiplicity := multiplicity
      parentClass := parentClass
      treeCleanup := treeCleanup
      exactification := exactification
      parentDegree := parentDegree
      bins := bins
    }⟩

/--
The deterministic four-degree prefix using the externally supplied one-pass
cleanup theorem.  Every later construction uses this single receipt.
-/
theorem pureWZ2_prop62_four_degree_prefix_of_cleanupOracle
    (cleanupOracle : PureWZ2Prop62CleanupOracle) :
    Nonempty (input.FourDegreePrefixData schedule) := by
  rcases input.pureWZ2_prop62_packet_cell_fine_multiplicity_class with
    ⟨multiplicity⟩
  rcases input.pureWZ2_prop62_parent_class_selection multiplicity with
    ⟨parentClass⟩
  rcases
      cleanupOracle
        (Fin coarse.card) (Finset (Fin coarse.card))
        schedule.levelCount schedule.tree parentClass.selectedParents
        parentClass.selectedParents_nonempty
    with ⟨receipt⟩
  rcases
      input.pureWZ2_prop62_parent_tree_cleanup_of_receipt
        multiplicity parentClass schedule receipt
    with ⟨treeCleanup⟩
  rcases
      input.pureWZ2_prop62_packet_cell_exactification
        multiplicity parentClass treeCleanup
    with ⟨exactification⟩
  rcases
      input.pureWZ2_prop62_reference_parent_degree
        multiplicity parentClass treeCleanup exactification
    with ⟨parentDegree⟩
  have allEdgesNonempty :
      exactification.incidence.allEdges.Nonempty := by
    rcases exactification.edgePool_nonempty with ⟨pair, pairMem⟩
    exact ⟨⟨pair, pairMem⟩, Finset.mem_univ _⟩
  rcases
      exactification.incidence.pureWZ2_prop62_three_degree_binning
        exactification.incidence.allEdges allEdgesNonempty
    with ⟨bins⟩
  exact
    ⟨{
      multiplicity := multiplicity
      parentClass := parentClass
      treeCleanup := treeCleanup
      exactification := exactification
      parentDegree := parentDegree
      bins := bins
    }⟩

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
