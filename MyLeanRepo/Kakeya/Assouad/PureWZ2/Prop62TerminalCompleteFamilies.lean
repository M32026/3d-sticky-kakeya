import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ExactFineShading
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricCoreRestriction

/-!
# Proposition 6.2: terminal complete metric families

The terminal edge core selects metric parent vertices, not individual fine
tubes.  The final fine family is the union of the complete genuine Section 6
metric fibers over those parents.  This choice is frozen before the random
whole-cell balancing; the random sample only changes the shading.
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
    {TreeLabel : Type*} [DecidableEq TreeLabel]
    {initialEdges : Finset exactification.incidence.Edge}
    {bins :
      exactification.incidence.ThreeDegreeBinningData initialEdges}
    {parentLower fineLower parentCoarseLower coarseLower : ℕ}
    {treeLabels : Finset TreeLabel}
    {treeBad :
      Finset exactification.incidence.Edge → TreeLabel → Prop}
    {treeCharge : TreeLabel → ℕ}
    (ranges :
      exactification.incidence.FourDegreeRangeData
        bins parentLower fineLower parentCoarseLower coarseLower
        treeLabels treeBad treeCharge)

/-- Ambient metric parent indices occurring in the terminal edge core. -/
def terminalParentIndices : Finset (Fin coarse.card) :=
  exactification.incidence.activeParents ranges.terminalEdges

theorem terminalParentIndices_nonempty :
    ranges.terminalEdges.Nonempty →
      (input.terminalParentIndices
        multiplicity parentClass treeCleanup exactification
        ranges).Nonempty := by
  intro terminalEdgesNonempty
  rcases terminalEdgesNonempty with ⟨edge, edgeMem⟩
  exact
    ⟨exactification.incidence.edgeParent edge,
      Finset.mem_image.mpr ⟨edge, edgeMem, rfl⟩⟩

/-- Ambient fine indices in complete metric fibers of terminal parents. -/
def terminalFineIndices : Finset (Fin fine.card) :=
  Finset.univ.filter fun source =>
    cover.toWZ1PaperTubeCover.parent source ∈
      input.terminalParentIndices
        multiplicity parentClass treeCleanup exactification ranges

theorem terminalFineIndices_nonempty :
    ranges.terminalEdges.Nonempty →
      (input.terminalFineIndices
        multiplicity parentClass treeCleanup exactification
        ranges).Nonempty := by
  intro terminalEdgesNonempty
  rcases input.terminalParentIndices_nonempty
      multiplicity parentClass treeCleanup exactification ranges
      terminalEdgesNonempty with
    ⟨parent, parentMem⟩
  rcases cover.toWZ1PaperTubeCover.parent_surjective parent with
    ⟨source, sourceParent⟩
  exact
    ⟨source,
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ source,
          by simpa [sourceParent] using parentMem⟩⟩

structure TerminalCompleteFamiliesData where
  terminalParents : Finset (Fin coarse.card)
  terminalParents_eq :
    terminalParents =
      input.terminalParentIndices
        multiplicity parentClass treeCleanup exactification ranges
  terminalFine : Finset (Fin fine.card)
  terminalFine_eq :
    terminalFine =
      input.terminalFineIndices
        multiplicity parentClass treeCleanup exactification ranges
  terminalFine_nonempty : terminalFine.Nonempty
  restriction :
    PureWZ2Prop62MetricCoreRestrictionData
      cover terminalFine
  coarse_image_univ :
    Finset.image restriction.coarseSelected.embedding Finset.univ =
      terminalParents
  fine_complete :
    ∀ parent : Fin restriction.coarseSelected.family.card,
      Finset.image restriction.fineSelected.embedding
          (wz2PaperFullFiberIndices
            restriction.fineSelected.family
            restriction.coarseSelected.family parent) =
        wz2PaperFullFiberIndices
          fine coarse (restriction.coarseSelected.embedding parent)

theorem pureWZ2_prop62_terminal_complete_families :
    ranges.terminalEdges.Nonempty →
    Nonempty
      (input.TerminalCompleteFamiliesData
        multiplicity parentClass treeCleanup exactification ranges) := by
  intro terminalEdgesNonempty
  let terminalParents :=
    input.terminalParentIndices
      multiplicity parentClass treeCleanup exactification ranges
  let terminalFine :=
    input.terminalFineIndices
      multiplicity parentClass treeCleanup exactification ranges
  have terminalFineNonempty : terminalFine.Nonempty :=
    input.terminalFineIndices_nonempty
      multiplicity parentClass treeCleanup exactification ranges
      terminalEdgesNonempty
  rcases
      pureWZ2_prop62_metric_core_restriction
        cover terminalFine terminalFineNonempty
    with ⟨restriction⟩
  have coarseImage :
      Finset.image restriction.coarseSelected.embedding Finset.univ =
        terminalParents := by
    let ambientLine := cover.toWZ1PaperTubeCover
    ext parent
    constructor
    · intro parentImage
      rcases Finset.mem_image.mp parentImage with
        ⟨selectedParent, _selectedUniv, parentEq⟩
      rcases restriction.lineCover.parent_surjective selectedParent with
        ⟨selectedSource, selectedParentEq⟩
      have sourceImage :
          restriction.fineSelected.embedding selectedSource ∈
            Finset.image restriction.fineSelected.embedding
              Finset.univ :=
        Finset.mem_image.mpr
          ⟨selectedSource, Finset.mem_univ _, rfl⟩
      have sourceMem :
          restriction.fineSelected.embedding selectedSource ∈
            terminalFine := by
        have imageEq := restriction.fine_image_univ
        rw [imageEq] at sourceImage
        exact sourceImage
      have ambientParentMem :
          ambientLine.parent
              (restriction.fineSelected.embedding selectedSource) ∈
            terminalParents :=
        (Finset.mem_filter.mp sourceMem).2
      have ambientParentEq :
          ambientLine.parent
              (restriction.fineSelected.embedding selectedSource) =
            restriction.coarseSelected.embedding selectedParent := by
        symm
        apply ambientLine.parent_unique
        rw [← selectedParentEq]
        simpa only [
          restriction.fineSelected.tube_eq,
          restriction.coarseSelected.tube_eq
        ] using restriction.lineCover.parent_covers selectedSource
      rw [← parentEq, ← ambientParentEq]
      exact ambientParentMem
    · intro parentMem
      rcases ambientLine.parent_surjective parent with
        ⟨ambientSource, ambientParent⟩
      have sourceFine :
          ambientSource ∈ terminalFine := by
        have canonicalParentMem :
            ambientLine.parent ambientSource ∈ terminalParents := by
          rw [ambientParent]
          exact parentMem
        exact
          Finset.mem_filter.mpr
            ⟨Finset.mem_univ ambientSource,
              by simpa [terminalFineIndices] using
                canonicalParentMem⟩
      have sourceImage :
          ambientSource ∈
            Finset.image restriction.fineSelected.embedding Finset.univ := by
        rw [restriction.fine_image_univ]
        exact sourceFine
      rcases Finset.mem_image.mp sourceImage with
        ⟨selectedSource, _sourceUniv, sourceEq⟩
      let selectedParent :=
        restriction.lineCover.parent selectedSource
      refine
        Finset.mem_image.mpr
          ⟨selectedParent, Finset.mem_univ _, ?_⟩
      have selectedParentAmbient :
          restriction.coarseSelected.embedding selectedParent =
              ambientLine.parent
                (restriction.fineSelected.embedding selectedSource) := by
        apply ambientLine.parent_unique
        simpa only [
          restriction.fineSelected.tube_eq,
          restriction.coarseSelected.tube_eq
        ] using restriction.lineCover.parent_covers selectedSource
      rw [selectedParentAmbient, sourceEq, ambientParent]
  have fineComplete :
      ∀ parent : Fin restriction.coarseSelected.family.card,
        Finset.image restriction.fineSelected.embedding
            (wz2PaperFullFiberIndices
              restriction.fineSelected.family
              restriction.coarseSelected.family parent) =
          wz2PaperFullFiberIndices
            fine coarse (restriction.coarseSelected.embedding parent) := by
    intro parent
    rw [restriction.fiber_image_eq]
    apply Finset.inter_eq_right.mpr
    intro source sourceFiber
    have sourceParent :
        cover.toWZ1PaperTubeCover.parent source =
          restriction.coarseSelected.embedding parent := by
      exact
        (cover.toWZ1PaperTubeCover.parent_unique
          source (restriction.coarseSelected.embedding parent)
          ((mem_wz2PaperFullFiberIndices_iff
            (restriction.coarseSelected.embedding parent)
            source).mp sourceFiber)).symm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ source, ?_⟩
    rw [sourceParent]
    have parentImage :
        restriction.coarseSelected.embedding parent ∈
          terminalParents := by
      rw [← coarseImage]
      exact
        Finset.mem_image.mpr
          ⟨parent, Finset.mem_univ _, rfl⟩
    simpa [terminalParents] using parentImage
  exact
    ⟨{
      terminalParents := terminalParents
      terminalParents_eq := rfl
      terminalFine := terminalFine
      terminalFine_eq := rfl
      terminalFine_nonempty := terminalFineNonempty
      restriction := restriction
      coarse_image_univ := coarseImage
      fine_complete := fineComplete
    }⟩

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
