import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TerminalCoarseMultiplicity

/-!
# Proposition 6.2: exact terminal packet mass and density gate

The final fine tube family is the union of complete metric fibers and the
balancing sample deletes whole packet-cells only.  Consequently the mass of
one final complete fiber has the exact double-counted form

`muFine * K_new(P) * |q|`.

This module proves that identity on the same final family and shading used by
the balanced cover.  It also transports the frozen factor-two fiber
cardinality band and combines the parent lower-tail certificate with the
terminal parent-degree lower bound.

The current packet-cell input does not contain the original density
hypothesis.  Therefore the final conversion of this exact lower bound into
`delta^(B0 * eta) * N_f * delta^2` is exposed as a scalar premise rather than
silently asserted.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

private theorem card_relation_eq_sum_left
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (left : Finset α) (right : Finset β)
    (relation : α → β → Prop) [DecidableRel relation] :
    ((left ×ˢ right).filter fun pair =>
        relation pair.1 pair.2).card =
      ∑ first ∈ left,
        (right.filter fun second =>
          relation first second).card := by
  rw [Finset.card_filter, Finset.sum_product]
  simp_rw [Finset.card_filter]

private theorem card_relation_eq_sum_right
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (left : Finset α) (right : Finset β)
    (relation : α → β → Prop) [DecidableRel relation] :
    ((left ×ˢ right).filter fun pair =>
        relation pair.1 pair.2).card =
      ∑ second ∈ right,
        (left.filter fun first =>
          relation first second).card := by
  rw [Finset.card_filter, Finset.sum_product]
  rw [Finset.sum_comm]
  simp_rw [Finset.card_filter]

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

namespace ExactFineShading

/-- Selected terminal packet-cell edges incident to one ambient parent. -/
def selectedEdgesAtParent
    (parent : Fin coarse.card) :
    Finset exactification.incidence.Edge :=
  (core.ranges.selectedEdges good.sample).filter fun edge =>
    exactification.incidence.edgeParent edge = parent

theorem selectedEdgesAtParent_card
    (parent : Fin coarse.card) :
    (ExactFineShading.selectedEdgesAtParent
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good parent).card =
      core.ranges.selectedParentDegree good.sample parent := by
  rfl

theorem sourceSelectedOnEdge_parent_eq
    {parent : Fin coarse.card}
    {source : Fin fine.card}
    {edge : exactification.incidence.Edge}
    (sourceFiber :
      source ∈ wz2PaperFullFiberIndices fine coarse parent)
    (sourceSelected :
      input.sourceSelectedOnEdge
        multiplicity parentClass treeCleanup exactification
          source edge) :
    exactification.incidence.edgeParent edge = parent := by
  have edgeFiber :
      source ∈
        wz2PaperFullFiberIndices fine coarse
          (exactification.incidence.edgeParent edge) :=
    ExactFineShading.sourceSelectedOnEdge_fullFiber
      input multiplicity parentClass treeCleanup exactification
        sourceSelected
  have edgeCover :=
    (mem_wz2PaperFullFiberIndices_iff
      (exactification.incidence.edgeParent edge) source).mp edgeFiber
  have parentCover :=
    (mem_wz2PaperFullFiberIndices_iff parent source).mp sourceFiber
  exact
    (cover.toWZ1PaperTubeCover.parent_unique
      source (exactification.incidence.edgeParent edge)
        edgeCover).trans
      (cover.toWZ1PaperTubeCover.parent_unique
        source parent parentCover).symm

theorem edgeFineCell_injective_on_selectedEdgesAtParent
    (parent : Fin coarse.card) :
    Set.InjOn exactification.incidence.edgeFineCell
      (ExactFineShading.selectedEdgesAtParent
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good parent) := by
  intro first firstMem second secondMem fineEq
  have firstParent :
      exactification.incidence.edgeParent first = parent :=
    (Finset.mem_filter.mp firstMem).2
  have secondParent :
      exactification.incidence.edgeParent second = parent :=
    (Finset.mem_filter.mp secondMem).2
  apply Subtype.ext
  apply Prod.ext
  · exact firstParent.trans secondParent.symm
  · exact fineEq

theorem retainedCellsForSource_eq_parent_image
    {parent : Fin coarse.card}
    {source : Fin fine.card}
    (sourceFiber :
      source ∈ wz2PaperFullFiberIndices fine coarse parent) :
    input.retainedCellsForSource
        multiplicity parentClass treeCleanup exactification
          core.ranges good source =
      ((ExactFineShading.selectedEdgesAtParent
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good parent).filter fun edge =>
        input.sourceSelectedOnEdge
          multiplicity parentClass treeCleanup exactification
            source edge).image
        exactification.incidence.edgeFineCell := by
  ext fineCell
  constructor
  · intro fineCellMem
    rcases Finset.mem_image.mp fineCellMem with
      ⟨edge, edgeMem, edgeFine⟩
    have edgeSelected :
        edge ∈ core.ranges.selectedEdges good.sample :=
      (Finset.mem_filter.mp edgeMem).1
    have sourceSelected :
        input.sourceSelectedOnEdge
          multiplicity parentClass treeCleanup exactification
            source edge :=
      (Finset.mem_filter.mp edgeMem).2
    have edgeParent :
        exactification.incidence.edgeParent edge = parent :=
      ExactFineShading.sourceSelectedOnEdge_parent_eq
        input multiplicity parentClass treeCleanup exactification
          sourceFiber sourceSelected
    exact
      Finset.mem_image.mpr
        ⟨edge,
          Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr
                ⟨edgeSelected, edgeParent⟩,
              sourceSelected⟩,
          edgeFine⟩
  · intro fineCellMem
    rcases Finset.mem_image.mp fineCellMem with
      ⟨edge, edgeMem, edgeFine⟩
    have parentEdgeData := Finset.mem_filter.mp edgeMem
    have edgeSelected :
        edge ∈ core.ranges.selectedEdges good.sample :=
      (Finset.mem_filter.mp parentEdgeData.1).1
    exact
      Finset.mem_image.mpr
        ⟨edge,
          Finset.mem_filter.mpr
            ⟨edgeSelected, parentEdgeData.2⟩,
          edgeFine⟩

theorem retainedCellsForSource_card
    {parent : Fin coarse.card}
    {source : Fin fine.card}
    (sourceFiber :
      source ∈ wz2PaperFullFiberIndices fine coarse parent) :
    (input.retainedCellsForSource
      multiplicity parentClass treeCleanup exactification
        core.ranges good source).card =
      ((ExactFineShading.selectedEdgesAtParent
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good parent).filter fun edge =>
        input.sourceSelectedOnEdge
          multiplicity parentClass treeCleanup exactification
            source edge).card := by
  rw [
    ExactFineShading.retainedCellsForSource_eq_parent_image
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good sourceFiber
  ]
  exact
    Finset.card_image_iff.mpr
      ((ExactFineShading.edgeFineCell_injective_on_selectedEdgesAtParent
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good parent).mono
        (Finset.filter_subset _ _))

theorem selectedSources_filter_eq
    {parent : Fin coarse.card}
    {edge : exactification.incidence.Edge}
    (edgeMem :
      edge ∈
        ExactFineShading.selectedEdgesAtParent
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good parent) :
    ((wz2PaperFullFiberIndices fine coarse parent).filter fun source =>
        input.sourceSelectedOnEdge
          multiplicity parentClass treeCleanup exactification
            source edge) =
      exactification.selectedSources
        (input.referencePairOfEdge
          multiplicity parentClass treeCleanup exactification edge) := by
  have edgeParent :
      exactification.incidence.edgeParent edge = parent :=
    (Finset.mem_filter.mp edgeMem).2
  ext source
  constructor
  · intro sourceMem
    exact (Finset.mem_filter.mp sourceMem).2
  · intro sourceMem
    apply Finset.mem_filter.mpr
    refine ⟨?_, sourceMem⟩
    have sourceFiber :=
      ExactFineShading.sourceSelectedOnEdge_fullFiber
        input multiplicity parentClass treeCleanup exactification
          sourceMem
    simpa [edgeParent] using sourceFiber

theorem sum_retainedCellsForSource_card
    (parent : Fin coarse.card) :
    (∑ source ∈ wz2PaperFullFiberIndices fine coarse parent,
        (input.retainedCellsForSource
          multiplicity parentClass treeCleanup exactification
            core.ranges good source).card) =
      multiplicity.muFine *
        core.ranges.selectedParentDegree good.sample parent := by
  let parentEdges :=
    ExactFineShading.selectedEdgesAtParent
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good parent
  let fiber :=
    wz2PaperFullFiberIndices fine coarse parent
  let relation :
      exactification.incidence.Edge → Fin fine.card → Prop :=
    fun edge source =>
      input.sourceSelectedOnEdge
        multiplicity parentClass treeCleanup exactification
          source edge
  have sourceCount :
      (∑ source ∈ fiber,
          (parentEdges.filter fun edge =>
            relation edge source).card) =
        ((parentEdges ×ˢ fiber).filter fun pair =>
          relation pair.1 pair.2).card := by
    exact (card_relation_eq_sum_right parentEdges fiber relation).symm
  have edgeCount :
      ((parentEdges ×ˢ fiber).filter fun pair =>
          relation pair.1 pair.2).card =
        ∑ edge ∈ parentEdges,
          (fiber.filter fun source =>
            relation edge source).card :=
    card_relation_eq_sum_left parentEdges fiber relation
  calc
    (∑ source ∈ wz2PaperFullFiberIndices fine coarse parent,
        (input.retainedCellsForSource
          multiplicity parentClass treeCleanup exactification
            core.ranges good source).card) =
        ∑ source ∈ fiber,
          (parentEdges.filter fun edge =>
            relation edge source).card := by
      apply Finset.sum_congr rfl
      intro source sourceMem
      exact
        ExactFineShading.retainedCellsForSource_card
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good sourceMem
    _ =
        ((parentEdges ×ˢ fiber).filter fun pair =>
          relation pair.1 pair.2).card :=
      sourceCount
    _ =
        ∑ edge ∈ parentEdges,
          (fiber.filter fun source =>
            relation edge source).card :=
      edgeCount
    _ =
        ∑ _edge ∈ parentEdges, multiplicity.muFine := by
      apply Finset.sum_congr rfl
      intro edge edgeMem
      rw [
        ExactFineShading.selectedSources_filter_eq
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good edgeMem,
        exactification.selectedSources_card
      ]
    _ = parentEdges.card * multiplicity.muFine := by
      simp
    _ =
        multiplicity.muFine *
          core.ranges.selectedParentDegree good.sample parent := by
      rw [ExactFineShading.selectedEdgesAtParent_card
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good parent]
      ring

/-- Mass of the ambient exact shading inside one complete metric fiber. -/
def ambientTerminalFiberMass
    (parent : Fin coarse.card) : ENNReal :=
  ∑ source ∈ wz2PaperFullFiberIndices fine coarse parent,
    volume
      ((input.exactFineShading
        multiplicity parentClass treeCleanup exactification
          core.ranges good).carrier source)

theorem ambientTerminalFiberMass_eq
    (parent : Fin coarse.card) :
    ExactFineShading.ambientTerminalFiberMass
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good parent =
      (multiplicity.muFine *
        core.ranges.selectedParentDegree good.sample parent : ℕ) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  calc
    ExactFineShading.ambientTerminalFiberMass
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good parent =
        ∑ source ∈ wz2PaperFullFiberIndices fine coarse parent,
          ((input.retainedCellsForSource
            multiplicity parentClass treeCleanup exactification
              core.ranges good source).card : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
      apply Finset.sum_congr rfl
      intro source _sourceMem
      rw [ExactFineShading.carrier_eq
        input multiplicity parentClass treeCleanup exactification
          core.ranges good source]
      exact
        wz1PaperGridCube_volume_biUnion input.delta_pos
          (input.retainedCellsForSource
            multiplicity parentClass treeCleanup exactification
              core.ranges good source)
    _ =
        (∑ source ∈ wz2PaperFullFiberIndices fine coarse parent,
          ((input.retainedCellsForSource
            multiplicity parentClass treeCleanup exactification
              core.ranges good source).card : ENNReal)) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
      rw [Finset.sum_mul]
    _ =
        ((∑ source ∈ wz2PaperFullFiberIndices fine coarse parent,
          (input.retainedCellsForSource
            multiplicity parentClass treeCleanup exactification
              core.ranges good source).card : ℕ) : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
      rw [Nat.cast_sum]
    _ =
        (multiplicity.muFine *
          core.ranges.selectedParentDegree good.sample parent : ℕ) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
      rw [ExactFineShading.sum_retainedCellsForSource_card
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good parent]

end ExactFineShading

namespace TerminalFineShading

/-- Fine sources in one final complete fiber whose final shading contains the
selected whole packet-cell. -/
def terminalPacketCellSources
    (parent :
      Fin families.restriction.coarseSelected.family.card)
    (edge : exactification.incidence.Edge) :
    Finset
      (Fin families.restriction.fineSelected.family.card) :=
  (wz2PaperFullFiberIndices
      families.restriction.fineSelected.family
      families.restriction.coarseSelected.family parent).filter fun source =>
    wz1PaperGridCube delta
        (exactification.incidence.edgeFineCell edge) ⊆
      (input.terminalFineShading
        multiplicity parentClass treeCleanup exactification
          core.ranges good families).carrier source

theorem terminalPacketCellSources_image
    {parent :
      Fin families.restriction.coarseSelected.family.card}
    {edge : exactification.incidence.Edge}
    (edgeSelected :
      edge ∈ core.ranges.selectedEdges good.sample)
    (edgeParent :
      exactification.incidence.edgeParent edge =
        families.restriction.coarseSelected.embedding parent) :
    Finset.image
        families.restriction.fineSelected.embedding
        (TerminalFineShading.terminalPacketCellSources
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families parent edge) =
      ExactFineShading.finalPacketCellSources
        input multiplicity parentClass treeCleanup exactification
          core.ranges good edge := by
  ext ambientSource
  constructor
  · intro sourceImage
    rcases Finset.mem_image.mp sourceImage with
      ⟨source, sourceMem, sourceEq⟩
    have sourceData := Finset.mem_filter.mp sourceMem
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · have ambientFiber :
          families.restriction.fineSelected.embedding source ∈
            wz2PaperFullFiberIndices fine coarse
              (families.restriction.coarseSelected.embedding parent) := by
        have sourceInImage :
            families.restriction.fineSelected.embedding source ∈
              Finset.image
                families.restriction.fineSelected.embedding
                (wz2PaperFullFiberIndices
                  families.restriction.fineSelected.family
                  families.restriction.coarseSelected.family parent) :=
          Finset.mem_image.mpr
            ⟨source, sourceData.1, rfl⟩
        rw [families.fine_complete parent] at sourceInImage
        exact sourceInImage
      rw [← sourceEq, edgeParent]
      exact ambientFiber
    · rw [← sourceEq]
      exact sourceData.2
  · intro ambientMem
    have ambientData := Finset.mem_filter.mp ambientMem
    have ambientFiber :
        ambientSource ∈
          wz2PaperFullFiberIndices fine coarse
            (families.restriction.coarseSelected.embedding parent) := by
      simpa [edgeParent] using ambientData.1
    have sourceImage :
        ambientSource ∈
          Finset.image
            families.restriction.fineSelected.embedding
            (wz2PaperFullFiberIndices
              families.restriction.fineSelected.family
              families.restriction.coarseSelected.family parent) := by
      rw [families.fine_complete parent]
      exact ambientFiber
    rcases Finset.mem_image.mp sourceImage with
      ⟨source, sourceFiber, sourceEq⟩
    apply Finset.mem_image.mpr
    refine ⟨source, Finset.mem_filter.mpr ⟨sourceFiber, ?_⟩, sourceEq⟩
    rw [TerminalFineShading.carrier_eq
      input multiplicity parentClass treeCleanup exactification
        core.ranges good families source]
    rw [sourceEq]
    exact ambientData.2

theorem terminal_exact_fine_multiplicity
    {parent :
      Fin families.restriction.coarseSelected.family.card}
    {edge : exactification.incidence.Edge}
    (edgeSelected :
      edge ∈ core.ranges.selectedEdges good.sample)
    (edgeParent :
      exactification.incidence.edgeParent edge =
        families.restriction.coarseSelected.embedding parent) :
    (TerminalFineShading.terminalPacketCellSources
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent edge).card =
      multiplicity.muFine := by
  have imageCard :
      (Finset.image
        families.restriction.fineSelected.embedding
        (TerminalFineShading.terminalPacketCellSources
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families parent edge)).card =
        (TerminalFineShading.terminalPacketCellSources
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families parent edge).card :=
    Finset.card_image_of_injective _
      families.restriction.fineSelected.embedding.injective
  rw [TerminalFineShading.terminalPacketCellSources_image
    input multiplicity parentClass treeCleanup exactification
      parentDegree core good families edgeSelected edgeParent] at imageCard
  rw [← imageCard]
  exact
    ExactFineShading.exact_fine_multiplicity
      input multiplicity parentClass treeCleanup exactification
        core.ranges good edgeSelected

/-- Mass of the final shading inside one final complete metric fiber. -/
def terminalFiberMass
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    ENNReal :=
  ∑ source ∈
      wz2PaperFullFiberIndices
        families.restriction.fineSelected.family
        families.restriction.coarseSelected.family parent,
    volume
      ((input.terminalFineShading
        multiplicity parentClass treeCleanup exactification
          core.ranges good families).carrier source)

theorem terminalFiberMass_eq_ambient
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    TerminalFineShading.terminalFiberMass
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent =
      ExactFineShading.ambientTerminalFiberMass
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good
          (families.restriction.coarseSelected.embedding parent) := by
  let finalFiber :=
    wz2PaperFullFiberIndices
      families.restriction.fineSelected.family
      families.restriction.coarseSelected.family parent
  let ambientFiber :=
    wz2PaperFullFiberIndices fine coarse
      (families.restriction.coarseSelected.embedding parent)
  rw [TerminalFineShading.terminalFiberMass]
  rw [ExactFineShading.ambientTerminalFiberMass]
  rw [← families.fine_complete parent]
  rw [Finset.sum_image
    families.restriction.fineSelected.embedding.injective.injOn]
  rfl

theorem terminalFiberMass_eq
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    TerminalFineShading.terminalFiberMass
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent =
      (multiplicity.muFine *
        core.ranges.selectedParentDegree good.sample
          (families.restriction.coarseSelected.embedding parent) : ℕ) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  rw [TerminalFineShading.terminalFiberMass_eq_ambient
    input multiplicity parentClass treeCleanup exactification
      parentDegree core good families parent]
  exact
    ExactFineShading.ambientTerminalFiberMass_eq
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good
        (families.restriction.coarseSelected.embedding parent)

theorem terminalFiberCard_eq_ambient
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    (wz2PaperFullFiberIndices
      families.restriction.fineSelected.family
      families.restriction.coarseSelected.family parent).card =
      input.parentFiberCard
        (families.restriction.coarseSelected.embedding parent) := by
  have imageCard :
      (Finset.image families.restriction.fineSelected.embedding
        (wz2PaperFullFiberIndices
          families.restriction.fineSelected.family
          families.restriction.coarseSelected.family parent)).card =
        (wz2PaperFullFiberIndices
          families.restriction.fineSelected.family
          families.restriction.coarseSelected.family parent).card :=
    Finset.card_image_of_injective _
      families.restriction.fineSelected.embedding.injective
  rw [families.fine_complete parent] at imageCard
  simpa [parentFiberCard] using imageCard.symm

theorem terminalFiberCard_band
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    parentClass.fiberFloor ≤
        (wz2PaperFullFiberIndices
          families.restriction.fineSelected.family
          families.restriction.coarseSelected.family parent).card ∧
      (wz2PaperFullFiberIndices
          families.restriction.fineSelected.family
          families.restriction.coarseSelected.family parent).card <
        2 * parentClass.fiberFloor := by
  have ambientTerminal :
      families.restriction.coarseSelected.embedding parent ∈
        input.terminalParentIndices
          multiplicity parentClass treeCleanup exactification
            core.ranges := by
    rw [← families.terminalParents_eq]
    rw [← families.coarse_image_univ]
    exact
      Finset.mem_image.mpr
        ⟨parent, Finset.mem_univ _, rfl⟩
  have ambientReference :
      families.restriction.coarseSelected.embedding parent ∈
        treeCleanup.referenceParents :=
    input.terminalParent_mem_reference
      multiplicity parentClass treeCleanup exactification
        parentDegree core ambientTerminal
  rw [TerminalFineShading.terminalFiberCard_eq_ambient
    input multiplicity parentClass treeCleanup exactification
      parentDegree core families parent]
  exact treeCleanup.reference_fiber_card_band
    (families.restriction.coarseSelected.embedding parent)
      ambientReference

theorem terminal_packet_density_scaled
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    ((multiplicity.muFine *
        input.parentThreshold
          multiplicity parentClass treeCleanup
            exactification parentDegree A0 : ℕ) : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0)) ≤
      (degreeLoss : ENNReal) *
        TerminalFineShading.terminalFiberMass
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families parent := by
  let ambientParent :=
    families.restriction.coarseSelected.embedding parent
  have ambientTerminal :
      ambientParent ∈ core.ranges.terminalParents := by
    rw [
      PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.terminalParents
    ]
    change
      ambientParent ∈
        input.terminalParentIndices
          multiplicity parentClass treeCleanup exactification
            core.ranges
    rw [← families.terminalParents_eq]
    rw [← families.coarse_image_univ]
    exact
      Finset.mem_image.mpr
        ⟨parent, Finset.mem_univ _, rfl⟩
  have terminalDegreePos :
      0 <
        exactification.incidence.parentDegree
          core.ranges.terminalEdges ambientParent :=
    core.ranges.terminalParent_degree_pos ambientTerminal
  have thresholdLeTerminal :
      input.parentThreshold
          multiplicity parentClass treeCleanup
            exactification parentDegree A0 ≤
        exactification.incidence.parentDegree
          core.ranges.terminalEdges ambientParent := by
    have peelingDegreePos :
        0 <
          exactification.incidence.parentDegree
            core.peeling.core ambientParent := by
      rw [← core.ranges_peeling_eq]
      exact terminalDegreePos
    have range :=
      core.parent_range
        input multiplicity parentClass treeCleanup
          exactification parentDegree ambientParent peelingDegreePos
    rw [
      PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.terminalEdges,
      core.ranges_peeling_eq
    ]
    exact range.1
  have terminalLeSelected :
      exactification.incidence.parentDegree
          core.ranges.terminalEdges ambientParent ≤
        degreeLoss *
          core.ranges.selectedParentDegree good.sample ambientParent :=
    good.parent_degree_retention ambientParent ambientTerminal
  have countLower :
      multiplicity.muFine *
          input.parentThreshold
            multiplicity parentClass treeCleanup
              exactification parentDegree A0 ≤
        degreeLoss *
          (multiplicity.muFine *
            core.ranges.selectedParentDegree good.sample ambientParent) := by
    calc
      multiplicity.muFine *
          input.parentThreshold
            multiplicity parentClass treeCleanup
              exactification parentDegree A0 ≤
        multiplicity.muFine *
          exactification.incidence.parentDegree
            core.ranges.terminalEdges ambientParent :=
        Nat.mul_le_mul_left multiplicity.muFine thresholdLeTerminal
      _ ≤
        multiplicity.muFine *
          (degreeLoss *
            core.ranges.selectedParentDegree good.sample ambientParent) :=
        Nat.mul_le_mul_left multiplicity.muFine terminalLeSelected
      _ =
        degreeLoss *
          (multiplicity.muFine *
            core.ranges.selectedParentDegree good.sample ambientParent) := by
        ring
  rw [TerminalFineShading.terminalFiberMass_eq
    input multiplicity parentClass treeCleanup exactification
      parentDegree core good families parent]
  have countLowerENN :
      ((multiplicity.muFine *
        input.parentThreshold
          multiplicity parentClass treeCleanup
            exactification parentDegree A0 : ℕ) : ENNReal) ≤
        (degreeLoss : ENNReal) *
          (multiplicity.muFine *
            core.ranges.selectedParentDegree good.sample ambientParent : ℕ) := by
    exact_mod_cast countLower
  calc
    ((multiplicity.muFine *
        input.parentThreshold
          multiplicity parentClass treeCleanup
            exactification parentDegree A0 : ℕ) : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0)) ≤
      ((degreeLoss : ENNReal) *
        (multiplicity.muFine *
          core.ranges.selectedParentDegree good.sample ambientParent : ℕ)) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
      gcongr
    _ =
      (degreeLoss : ENNReal) *
        ((multiplicity.muFine *
          core.ranges.selectedParentDegree good.sample ambientParent : ℕ) *
        volume (wz1PaperGridCube delta (0, 0, 0))) := by
      ring

theorem degreeLoss_pos
    (good : core.ranges.GoodBalancingSampleData degreeLoss)
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    0 < degreeLoss := by
  let ambientParent :=
    families.restriction.coarseSelected.embedding parent
  have ambientTerminal :
      ambientParent ∈ core.ranges.terminalParents := by
    rw [
      PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.terminalParents
    ]
    change
      ambientParent ∈
        input.terminalParentIndices
          multiplicity parentClass treeCleanup exactification
            core.ranges
    rw [← families.terminalParents_eq]
    rw [← families.coarse_image_univ]
    exact
      Finset.mem_image.mpr
        ⟨parent, Finset.mem_univ _, rfl⟩
  have terminalDegreePos :
      0 <
        exactification.incidence.parentDegree
          core.ranges.terminalEdges ambientParent :=
    core.ranges.terminalParent_degree_pos ambientTerminal
  have retained :=
    good.parent_degree_retention ambientParent ambientTerminal
  by_contra degreeLossNotPos
  have degreeLossZero : degreeLoss = 0 := by omega
  have retainedRightZero :
      degreeLoss *
          core.ranges.selectedParentDegree good.sample ambientParent =
        0 := by
    simp [degreeLossZero]
  have degreeLeZero :
      exactification.incidence.parentDegree
          core.ranges.terminalEdges ambientParent ≤
        0 :=
    retained.trans_eq retainedRightZero
  omega

/--
The only quantitative input still needed to turn the exact terminal packet
mass into the paper's power-form packet density.
-/
structure PacketDensityAbsorptionData
    (_core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup
        exactification parentDegree bins A0)
    (_good : _core.ranges.GoodBalancingSampleData degreeLoss)
    (densityConstant : ENNReal) : Prop where
  scalar :
    (degreeLoss : ENNReal) *
        densityConstant *
        (parentClass.fiberFloor : ENNReal) *
        Kakeya.realRpowENN delta 2 ≤
      ((multiplicity.muFine *
        input.parentThreshold
          multiplicity parentClass treeCleanup
            exactification parentDegree A0 : ℕ) : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0))

theorem terminal_packet_density
    {densityConstant : ENNReal}
    (absorption :
      TerminalFineShading.PacketDensityAbsorptionData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good densityConstant)
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    densityConstant *
        (parentClass.fiberFloor : ENNReal) *
        Kakeya.realRpowENN delta 2 ≤
      TerminalFineShading.terminalFiberMass
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent := by
  have scaled :=
    absorption.scalar.trans <|
      TerminalFineShading.terminal_packet_density_scaled
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent
  have degreeLossPositive :
      0 < (degreeLoss : ENNReal) := by
    exact_mod_cast
      TerminalFineShading.degreeLoss_pos
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families good parent
  apply
    (ENNReal.mul_le_mul_iff_right
      degreeLossPositive.ne'
      (ENNReal.natCast_ne_top degreeLoss)).mp
  simpa [mul_assoc] using scaled

end TerminalFineShading

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
