import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TerminalCompleteFamilies

/-!
# Proposition 6.2: exact shading on the terminal complete fine family

The ambient exact shading is already supported on terminal packet-cell
edges.  Every source used by such an edge belongs to the complete metric
fiber of a terminal parent.  Consequently every ambient source outside the
terminal complete fine family has empty exact carrier.

Restricting the exact shading to the frozen terminal fine family is therefore
lossless: the mass and union are unchanged, while cubicality and source
subshading provenance are preserved.
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
    {degreeLoss : ℕ}
    (good : ranges.GoodBalancingSampleData degreeLoss)
    (families :
      input.TerminalCompleteFamiliesData
        multiplicity parentClass treeCleanup exactification ranges)

abbrev ambientExactShading : WZ1PaperTubeShading fine :=
  input.exactFineShading
    multiplicity parentClass treeCleanup exactification ranges good

theorem ambientExact_source_mem_terminalFine
    {source : Fin fine.card}
    (carrier_nonempty :
      (input.ambientExactShading
        multiplicity parentClass treeCleanup exactification
        ranges good).carrier source |>.Nonempty) :
    source ∈ families.terminalFine := by
  rcases carrier_nonempty with ⟨point, pointMem⟩
  rcases Set.mem_iUnion₂.mp pointMem with
    ⟨cell, cellMem, _pointCell⟩
  rcases Finset.mem_image.mp cellMem with
    ⟨edge, edgeMem, _edgeCell⟩
  have edgeSelected :
      edge ∈ ranges.selectedEdges good.sample :=
    (Finset.mem_filter.mp edgeMem).1
  have edgeTerminal :
      edge ∈ ranges.terminalEdges :=
    good.selectedEdges_subset edgeSelected
  have sourceSelected :
      input.sourceSelectedOnEdge
        multiplicity parentClass treeCleanup exactification
        source edge :=
    (Finset.mem_filter.mp edgeMem).2
  have sourceFiber :
      source ∈
        wz2PaperFullFiberIndices fine coarse
          (exactification.incidence.edgeParent edge) :=
    ExactFineShading.sourceSelectedOnEdge_fullFiber
      input multiplicity parentClass treeCleanup exactification
      sourceSelected
  have canonicalParent :
      cover.toWZ1PaperTubeCover.parent source =
        exactification.incidence.edgeParent edge := by
    exact
      (cover.toWZ1PaperTubeCover.parent_unique
        source (exactification.incidence.edgeParent edge)
        ((mem_wz2PaperFullFiberIndices_iff
          (exactification.incidence.edgeParent edge) source).mp
            sourceFiber)).symm
  have parentTerminal :
      exactification.incidence.edgeParent edge ∈
        input.terminalParentIndices
          multiplicity parentClass treeCleanup exactification ranges := by
    exact
      Finset.mem_image.mpr
        ⟨edge, edgeTerminal, rfl⟩
  rw [families.terminalFine_eq]
  apply Finset.mem_filter.mpr
  exact
    ⟨Finset.mem_univ source,
      by simpa [canonicalParent] using parentTerminal⟩

theorem ambientExact_carrier_eq_empty_of_not_mem
    {source : Fin fine.card}
    (source_not_mem : source ∉ families.terminalFine) :
    (input.ambientExactShading
      multiplicity parentClass treeCleanup exactification
      ranges good).carrier source = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  intro carrierNonempty
  exact source_not_mem <|
    input.ambientExact_source_mem_terminalFine
      multiplicity parentClass treeCleanup exactification
      ranges good families carrierNonempty

/-- The final shading on the frozen terminal complete fine family. -/
def terminalFineShading :
    WZ1PaperTubeShading families.restriction.fineSelected.family :=
  restrictPaperShading
    families.restriction.fineSelected
    (input.ambientExactShading
      multiplicity parentClass treeCleanup exactification
      ranges good)

namespace TerminalFineShading

theorem carrier_eq
    (source :
      Fin families.restriction.fineSelected.family.card) :
    (input.terminalFineShading
      multiplicity parentClass treeCleanup exactification
      ranges good families).carrier source =
      (input.ambientExactShading
        multiplicity parentClass treeCleanup exactification
        ranges good).carrier
          (families.restriction.fineSelected.embedding source) := by
  rfl

theorem cubical :
    WZ1PaperIsCubicalShading
      (input.terminalFineShading
        multiplicity parentClass treeCleanup exactification
        ranges good families) := by
  exact
    restrictPaperShading_cubical
      families.restriction.fineSelected
      (ExactFineShading.cubical
        input multiplicity parentClass treeCleanup exactification
        ranges good)

theorem subshading
    (source :
      Fin families.restriction.fineSelected.family.card) :
    (input.terminalFineShading
      multiplicity parentClass treeCleanup exactification
      ranges good families).carrier source ⊆
        sourceShading.carrier
          (families.restriction.fineSelected.embedding source) := by
  exact
    ExactFineShading.subshading
      input multiplicity parentClass treeCleanup exactification
      ranges good
      (families.restriction.fineSelected.embedding source)

theorem ambient_source_reindex
    {source : Fin fine.card}
    (sourceMem : source ∈ families.terminalFine) :
    ∃ selectedSource :
        Fin families.restriction.fineSelected.family.card,
      families.restriction.fineSelected.embedding selectedSource =
        source := by
  have sourceImage :
      source ∈
        Finset.image
          families.restriction.fineSelected.embedding Finset.univ := by
    rw [families.restriction.fine_image_univ]
    exact sourceMem
  rcases Finset.mem_image.mp sourceImage with
    ⟨selectedSource, _selectedUniv, selectedEq⟩
  exact ⟨selectedSource, selectedEq⟩

theorem union_eq_ambient :
    (input.terminalFineShading
      multiplicity parentClass treeCleanup exactification
      ranges good families).union =
      (input.ambientExactShading
        multiplicity parentClass treeCleanup exactification
        ranges good).union := by
  apply Set.Subset.antisymm
  · intro point pointMem
    rcases pointMem with ⟨source, sourceMem⟩
    exact
      ⟨families.restriction.fineSelected.embedding source,
        sourceMem⟩
  · intro point pointMem
    rcases pointMem with ⟨ambientSource, ambientMem⟩
    have sourceTerminal :
        ambientSource ∈ families.terminalFine :=
      input.ambientExact_source_mem_terminalFine
        multiplicity parentClass treeCleanup exactification
        ranges good families ⟨point, ambientMem⟩
    rcases
        TerminalFineShading.ambient_source_reindex
          input
          multiplicity parentClass treeCleanup exactification
          ranges families sourceTerminal
      with ⟨selectedSource, selectedEq⟩
    refine ⟨selectedSource, ?_⟩
    change
      point ∈
        (input.ambientExactShading
          multiplicity parentClass treeCleanup exactification
          ranges good).carrier
            (families.restriction.fineSelected.embedding
              selectedSource)
    rw [selectedEq]
    exact ambientMem

theorem mass_eq_ambient :
    (input.terminalFineShading
      multiplicity parentClass treeCleanup exactification
      ranges good families).mass =
      (input.ambientExactShading
        multiplicity parentClass treeCleanup exactification
        ranges good).mass := by
  have restrictedMass :
      (input.terminalFineShading
        multiplicity parentClass treeCleanup exactification
        ranges good families).mass =
        ∑ source ∈ families.terminalFine,
          volume
            ((input.ambientExactShading
              multiplicity parentClass treeCleanup exactification
              ranges good).carrier source) := by
    unfold terminalFineShading
    rw [families.restriction.fineSelected_eq]
    exact
      restrictPaperShading_fromFinset_mass
        (input.ambientExactShading
          multiplicity parentClass treeCleanup exactification
          ranges good)
        families.terminalFine
  rw [restrictedMass]
  change
    (∑ source ∈ families.terminalFine,
        volume
          ((input.ambientExactShading
            multiplicity parentClass treeCleanup exactification
            ranges good).carrier source)) =
      ∑ source : Fin fine.card,
        volume
          ((input.ambientExactShading
            multiplicity parentClass treeCleanup exactification
            ranges good).carrier source)
  rw [Finset.sum_subset (Finset.subset_univ families.terminalFine)]
  intro source _sourceUniv sourceNotMem
  rw [input.ambientExact_carrier_eq_empty_of_not_mem
    multiplicity parentClass treeCleanup exactification
    ranges good families sourceNotMem]
  simp

end TerminalFineShading

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
